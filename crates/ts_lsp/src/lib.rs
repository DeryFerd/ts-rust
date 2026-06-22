//! Core Language Server Protocol types and a synchronous TypeScript session.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt, io,
};

use serde::{Deserialize, Serialize, de::DeserializeOwned};
use serde_json::Value;
use ts_ast::{NodeData, NodeId, SymbolId};
use ts_binder::{ScopeId, SymbolFlags};
use ts_compiler::{Program, SourceFile};
use ts_jsonrpc::{
    CODE_INVALID_PARAMS, CODE_INVALID_REQUEST, CODE_METHOD_NOT_FOUND, FramedReader, FramedWriter,
    Id, Message, MessageKind, Notification, ProtocolError, Response, ResponseError,
};
use ts_module::{ResolutionOptions, Resolver};
use ts_options::CompilerOptions;
use ts_vfs::{FileSystem, MemoryFileSystem};

/// LSP error code used when a request arrives before `initialize`.
pub const CODE_SERVER_NOT_INITIALIZED: i32 = -32_002;

/// A URI identifying an LSP document.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Deserialize, Serialize)]
#[serde(transparent)]
pub struct DocumentUri(pub String);

/// A zero-based UTF-16 position in a text document.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Deserialize, Serialize)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}

/// A half-open range in a text document.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Deserialize, Serialize)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}

/// A parser diagnostic represented in LSP coordinates.
#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct Diagnostic {
    pub range: Range,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub severity: Option<u8>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
    pub message: String,
}

/// Parameters sent by an LSP client when starting a session.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InitializeParams {
    #[serde(default)]
    pub process_id: Option<i64>,
    #[serde(default)]
    pub client_info: Option<ClientInfo>,
    #[serde(default)]
    pub root_uri: Option<DocumentUri>,
    #[serde(default)]
    pub capabilities: Value,
}

/// Parameters for the post-initialize `initialized` notification.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Deserialize, Serialize)]
pub struct InitializedParams {}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct ClientInfo {
    pub name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InitializeResult {
    pub capabilities: ServerCapabilities,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub server_info: Option<ServerInfo>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ServerInfo {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
#[allow(clippy::struct_excessive_bools)] // LSP capabilities are independent feature switches.
pub struct ServerCapabilities {
    pub text_document_sync: TextDocumentSyncOptions,
    pub hover_provider: bool,
    pub definition_provider: bool,
    pub references_provider: bool,
    pub rename_provider: bool,
    pub document_symbol_provider: bool,
    pub workspace_symbol_provider: bool,
    pub call_hierarchy_provider: bool,
    pub signature_help_provider: SignatureHelpOptions,
    pub semantic_tokens_provider: SemanticTokensOptions,
    pub folding_range_provider: bool,
    pub selection_range_provider: bool,
    pub document_highlight_provider: bool,
    pub linked_editing_range_provider: bool,
    pub code_action_provider: bool,
    pub completion_provider: CompletionOptions,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticTokensOptions {
    pub legend: SemanticTokensLegend,
    pub full: bool,
    pub range: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticTokensLegend {
    pub token_types: Vec<String>,
    pub token_modifiers: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SignatureHelpOptions {
    pub trigger_characters: Vec<String>,
    pub retrigger_characters: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CompletionOptions {
    pub resolve_provider: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TextDocumentSyncOptions {
    pub open_close: bool,
    /// `2` is LSP's incremental synchronization mode.
    pub change: u8,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TextDocumentItem {
    pub uri: DocumentUri,
    pub language_id: String,
    pub version: i32,
    pub text: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DidOpenTextDocumentParams {
    pub text_document: TextDocumentItem,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct VersionedTextDocumentIdentifier {
    pub uri: DocumentUri,
    pub version: i32,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct TextDocumentIdentifier {
    pub uri: DocumentUri,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TextDocumentPositionParams {
    pub text_document: TextDocumentIdentifier,
    pub position: Position,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct Location {
    pub uri: DocumentUri,
    pub range: Range,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct MarkupContent {
    pub kind: String,
    pub value: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct Hover {
    pub contents: MarkupContent,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub range: Option<Range>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ReferenceContext {
    pub include_declaration: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ReferenceParams {
    pub text_document: TextDocumentIdentifier,
    pub position: Position,
    pub context: ReferenceContext,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RenameParams {
    pub text_document: TextDocumentIdentifier,
    pub position: Position,
    pub new_name: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TextEdit {
    pub range: Range,
    pub new_text: String,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Deserialize, Serialize)]
pub struct WorkspaceEdit {
    pub changes: BTreeMap<DocumentUri, Vec<TextEdit>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DocumentSymbolParams {
    pub text_document: TextDocumentIdentifier,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DocumentSymbol {
    pub name: String,
    pub kind: u8,
    pub range: Range,
    pub selection_range: Range,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub children: Option<Vec<DocumentSymbol>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct CompletionItem {
    pub label: String,
    pub kind: u8,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SignatureHelpParams {
    pub text_document: TextDocumentIdentifier,
    pub position: Position,
    #[serde(default)]
    pub context: Option<Value>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SignatureHelp {
    pub signatures: Vec<SignatureInformation>,
    pub active_signature: u32,
    pub active_parameter: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SignatureInformation {
    pub label: String,
    pub parameters: Vec<ParameterInformation>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct ParameterInformation {
    pub label: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CallHierarchyItem {
    pub name: String,
    pub kind: u8,
    pub uri: DocumentUri,
    pub range: Range,
    pub selection_range: Range,
    pub data: Value,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct CallHierarchyCallsParams {
    pub item: CallHierarchyItem,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CallHierarchyIncomingCall {
    pub from: CallHierarchyItem,
    pub from_ranges: Vec<Range>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CallHierarchyOutgoingCall {
    pub to: CallHierarchyItem,
    pub from_ranges: Vec<Range>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct WorkspaceSymbolParams {
    pub query: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SymbolInformation {
    pub name: String,
    pub kind: u8,
    pub location: Location,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub container_name: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticTokens {
    pub data: Vec<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FoldingRangeParams {
    pub text_document: TextDocumentIdentifier,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FoldingRange {
    pub start_line: u32,
    pub start_character: u32,
    pub end_line: u32,
    pub end_character: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SelectionRangeParams {
    pub text_document: TextDocumentIdentifier,
    pub positions: Vec<Position>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct SelectionRange {
    pub range: Range,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent: Option<Box<SelectionRange>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct DocumentHighlight {
    pub range: Range,
    /// `1` text, `2` read, `3` write.
    pub kind: u8,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LinkedEditingRanges {
    pub ranges: Vec<Range>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub word_pattern: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CodeActionParams {
    pub text_document: TextDocumentIdentifier,
    pub range: Range,
    pub context: CodeActionContext,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CodeActionContext {
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CodeAction {
    pub title: String,
    pub kind: String,
    pub diagnostics: Vec<Diagnostic>,
    pub edit: WorkspaceEdit,
    pub is_preferred: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
struct CallHierarchyData {
    file_name: String,
    declaration_start: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TextDocumentContentChangeEvent {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub range: Option<Range>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub range_length: Option<u32>,
    pub text: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DidChangeTextDocumentParams {
    pub text_document: VersionedTextDocumentIdentifier,
    pub content_changes: Vec<TextDocumentContentChangeEvent>,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DidCloseTextDocumentParams {
    pub text_document: TextDocumentIdentifier,
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct PublishDiagnosticsParams {
    pub uri: DocumentUri,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub version: Option<i32>,
    pub diagnostics: Vec<Diagnostic>,
}

/// A server-originated JSON-RPC message.
#[derive(Clone, Debug, Serialize)]
#[serde(untagged)]
pub enum OutgoingMessage {
    Response(Response<Value>),
    Notification(Notification<Value>),
}

/// Current state of the LSP lifecycle.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum LifecycleState {
    #[default]
    Uninitialized,
    AwaitingInitialized,
    Running,
    Shutdown,
    Exited,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OpenDocument {
    pub language_id: String,
    pub version: i32,
    pub text: String,
    pub file_name: String,
}

/// Result requested by the LSP `exit` notification.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExitStatus {
    Success,
    Failure,
}

impl ExitStatus {
    #[must_use]
    pub const fn code(self) -> i32 {
        match self {
            Self::Success => 0,
            Self::Failure => 1,
        }
    }
}

/// Stateful, synchronous LSP message handler.
#[derive(Debug, Default)]
pub struct Server {
    state: LifecycleState,
    documents: BTreeMap<DocumentUri, OpenDocument>,
    workspace: MemoryFileSystem,
    exit_status: Option<ExitStatus>,
}

impl Server {
    #[must_use]
    pub const fn state(&self) -> LifecycleState {
        self.state
    }

    #[must_use]
    pub fn documents(&self) -> &BTreeMap<DocumentUri, OpenDocument> {
        &self.documents
    }

    #[must_use]
    pub const fn exit_status(&self) -> Option<ExitStatus> {
        self.exit_status
    }

    /// Handles one client message and returns zero or more messages to send.
    #[must_use]
    pub fn handle_message(&mut self, message: Message) -> Vec<OutgoingMessage> {
        match message.kind() {
            MessageKind::Request => self.handle_request(message),
            MessageKind::Notification => self.handle_notification(message),
            MessageKind::Response | MessageKind::Invalid => Vec::new(),
        }
    }

    fn handle_request(&mut self, message: Message) -> Vec<OutgoingMessage> {
        let Some(id) = message.id else {
            return Vec::new();
        };
        let Some(method) = message.method else {
            return Vec::new();
        };

        if method == "initialize" {
            return self.initialize(id, message.params);
        }
        if self.state == LifecycleState::Uninitialized {
            return vec![failure(
                id,
                CODE_SERVER_NOT_INITIALIZED,
                "server not initialized",
            )];
        }
        if self.state == LifecycleState::Shutdown || self.state == LifecycleState::Exited {
            return vec![failure(
                id,
                CODE_INVALID_REQUEST,
                "request received after shutdown",
            )];
        }
        if method == "shutdown" {
            self.state = LifecycleState::Shutdown;
            return vec![OutgoingMessage::Response(Response::success(
                id,
                Value::Null,
            ))];
        }
        if method == "textDocument/hover" {
            return vec![self.hover(id, message.params)];
        }
        if method == "textDocument/definition" {
            return vec![self.definition(id, message.params)];
        }
        if method == "textDocument/references" {
            return vec![self.references(id, message.params)];
        }
        if method == "textDocument/rename" {
            return vec![self.rename(id, message.params)];
        }
        if method == "textDocument/documentSymbol" {
            return vec![self.document_symbol(id, message.params)];
        }
        if method == "textDocument/completion" {
            return vec![self.completion(id, message.params)];
        }
        if method == "textDocument/signatureHelp" {
            return vec![self.signature_help(id, message.params)];
        }
        if method == "textDocument/prepareCallHierarchy" {
            return vec![self.prepare_call_hierarchy(id, message.params)];
        }
        if method == "callHierarchy/incomingCalls" {
            return vec![self.incoming_calls(id, message.params)];
        }
        if method == "callHierarchy/outgoingCalls" {
            return vec![self.outgoing_calls(id, message.params)];
        }
        if method == "workspace/symbol" {
            return vec![self.workspace_symbol(id, message.params)];
        }
        if method == "textDocument/semanticTokens/full" {
            return vec![self.semantic_tokens_full(id, message.params)];
        }
        if method == "textDocument/foldingRange" {
            return vec![self.folding_range(id, message.params)];
        }
        if method == "textDocument/selectionRange" {
            return vec![self.selection_range(id, message.params)];
        }
        if method == "textDocument/documentHighlight" {
            return vec![self.document_highlight(id, message.params)];
        }
        if method == "textDocument/linkedEditingRange" {
            return vec![self.linked_editing_range(id, message.params)];
        }
        if method == "textDocument/codeAction" {
            return vec![self.code_action(id, message.params)];
        }
        vec![failure(id, CODE_METHOD_NOT_FOUND, "method not found")]
    }

    fn initialize(&mut self, id: Id, params: Option<Value>) -> Vec<OutgoingMessage> {
        if self.state != LifecycleState::Uninitialized {
            return vec![failure(
                id,
                CODE_INVALID_REQUEST,
                "initialize may only be sent once",
            )];
        }
        if let Err(error) = deserialize_params::<InitializeParams>(params) {
            return vec![failure(id, CODE_INVALID_PARAMS, error)];
        }
        self.state = LifecycleState::AwaitingInitialized;
        let result = InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: TextDocumentSyncOptions {
                    open_close: true,
                    change: 2,
                },
                hover_provider: true,
                definition_provider: true,
                references_provider: true,
                rename_provider: true,
                document_symbol_provider: true,
                workspace_symbol_provider: true,
                call_hierarchy_provider: true,
                signature_help_provider: SignatureHelpOptions {
                    trigger_characters: vec!["(".to_owned(), ",".to_owned()],
                    retrigger_characters: vec![")".to_owned()],
                },
                semantic_tokens_provider: SemanticTokensOptions {
                    legend: SemanticTokensLegend {
                        token_types: semantic_token_types()
                            .iter()
                            .map(|token| (*token).to_owned())
                            .collect(),
                        token_modifiers: Vec::new(),
                    },
                    full: true,
                    range: false,
                },
                folding_range_provider: true,
                selection_range_provider: true,
                document_highlight_provider: true,
                linked_editing_range_provider: true,
                code_action_provider: true,
                completion_provider: CompletionOptions {
                    resolve_provider: false,
                },
            },
            server_info: Some(ServerInfo {
                name: "ts-rust".to_owned(),
                version: Some(env!("CARGO_PKG_VERSION").to_owned()),
            }),
        };
        vec![OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))]
    }

    fn handle_notification(&mut self, message: Message) -> Vec<OutgoingMessage> {
        let Some(method) = message.method.as_deref() else {
            return Vec::new();
        };
        if method == "exit" {
            self.exit_status = Some(if self.state == LifecycleState::Shutdown {
                ExitStatus::Success
            } else {
                ExitStatus::Failure
            });
            self.state = LifecycleState::Exited;
            return Vec::new();
        }
        if self.state == LifecycleState::AwaitingInitialized && method == "initialized" {
            if message.params.is_none()
                || deserialize_params::<InitializedParams>(message.params).is_ok()
            {
                self.state = LifecycleState::Running;
            }
            return Vec::new();
        }
        if self.state != LifecycleState::Running {
            return Vec::new();
        }
        match method {
            "textDocument/didOpen" => self.did_open(message.params),
            "textDocument/didChange" => self.did_change(message.params),
            "textDocument/didClose" => self.did_close(message.params),
            _ => Vec::new(),
        }
    }

    fn did_open(&mut self, params: Option<Value>) -> Vec<OutgoingMessage> {
        let Ok(params) = deserialize_params::<DidOpenTextDocumentParams>(params) else {
            return Vec::new();
        };
        let document = params.text_document;
        let uri = document.uri.clone();
        let open = OpenDocument {
            language_id: document.language_id,
            version: document.version,
            text: document.text,
            file_name: file_name_from_uri(&uri),
        };
        if self
            .workspace
            .write_file(&open.file_name, &open.text)
            .is_err()
        {
            return Vec::new();
        }
        self.documents.insert(uri, open);
        self.diagnostic_notifications()
    }

    fn did_change(&mut self, params: Option<Value>) -> Vec<OutgoingMessage> {
        let Ok(params) = deserialize_params::<DidChangeTextDocumentParams>(params) else {
            return Vec::new();
        };
        let uri = params.text_document.uri;
        let Some(document) = self.documents.get_mut(&uri) else {
            return Vec::new();
        };
        let mut next_text = document.text.clone();
        for change in params.content_changes {
            if apply_change(&mut next_text, &change).is_err() {
                return Vec::new();
            }
        }
        document.text = next_text;
        document.version = params.text_document.version;
        if self
            .workspace
            .write_file(&document.file_name, &document.text)
            .is_err()
        {
            return Vec::new();
        }
        self.diagnostic_notifications()
    }

    fn did_close(&mut self, params: Option<Value>) -> Vec<OutgoingMessage> {
        let Ok(params) = deserialize_params::<DidCloseTextDocumentParams>(params) else {
            return Vec::new();
        };
        let uri = params.text_document.uri;
        if self.documents.remove(&uri).is_none() {
            return Vec::new();
        }
        if self.rebuild_workspace().is_err() {
            return Vec::new();
        }
        let mut notifications = vec![publish_diagnostics(uri, None, Vec::new())];
        notifications.extend(self.diagnostic_notifications());
        notifications
    }

    fn rebuild_workspace(&mut self) -> io::Result<()> {
        let workspace = MemoryFileSystem::new(true);
        for document in self.documents.values() {
            workspace.write_file(&document.file_name, &document.text)?;
        }
        self.workspace = workspace;
        Ok(())
    }

    fn diagnostic_notifications(&self) -> Vec<OutgoingMessage> {
        if self.documents.is_empty() {
            return Vec::new();
        }
        let program = self.build_program();
        self.documents
            .iter()
            .map(|(uri, document)| {
                let diagnostics = diagnostics_for_document(&program, document);
                publish_diagnostics(uri.clone(), Some(document.version), diagnostics)
            })
            .collect()
    }

    fn hover(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<TextDocumentPositionParams>(params) else {
            return failure(id, CODE_INVALID_PARAMS, "invalid hover parameters");
        };
        let result = self.hover_at(&params);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn hover_at(&self, params: &TextDocumentPositionParams) -> Option<Hover> {
        let document = self.documents.get(&params.text_document.uri)?;
        let offset = u32::try_from(byte_offset(&document.text, params.position).ok()?).ok()?;
        let program = self.build_program();
        let source = program.source_file(&document.file_name)?;
        let node = identifier_at(source, offset)?;
        let name = identifier_text(source, node)?;
        let (target_source, symbol) =
            semantic_target(&program, &self.workspace, source, node, name)?;
        let type_id = target_source.checking.type_of_symbol(symbol)?;
        let value = format!("{name}: {}", target_source.checking.types.display(type_id));
        Some(Hover {
            contents: MarkupContent {
                kind: "plaintext".to_owned(),
                value,
            },
            range: Some(node_range(source, node)?),
        })
    }

    fn definition(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<TextDocumentPositionParams>(params) else {
            return failure(id, CODE_INVALID_PARAMS, "invalid definition parameters");
        };
        let result = self.definition_at(&params);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn definition_at(&self, params: &TextDocumentPositionParams) -> Option<Location> {
        let document = self.documents.get(&params.text_document.uri)?;
        let offset = u32::try_from(byte_offset(&document.text, params.position).ok()?).ok()?;
        let program = self.build_program();
        let source = program.source_file(&document.file_name)?;
        let node = identifier_at(source, offset)?;
        let name = identifier_text(source, node)?;
        let (target_source, symbol) =
            semantic_target(&program, &self.workspace, source, node, name)?;
        let declaration = declaration_name_node(target_source, symbol)?;
        let uri = self.documents.iter().find_map(|(uri, document)| {
            (document.file_name == target_source.file_name).then(|| uri.clone())
        })?;
        Some(Location {
            uri,
            range: node_range(target_source, declaration)?,
        })
    }

    fn references(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<ReferenceParams>(params) else {
            return failure(id, CODE_INVALID_PARAMS, "invalid references parameters");
        };
        let result = self.references_at(&params);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn references_at(&self, params: &ReferenceParams) -> Vec<Location> {
        let Some(document) = self.documents.get(&params.text_document.uri) else {
            return Vec::new();
        };
        let Ok(offset) = byte_offset(&document.text, params.position) else {
            return Vec::new();
        };
        let Ok(offset) = u32::try_from(offset) else {
            return Vec::new();
        };
        let program = self.build_program();
        let Some(source) = program.source_file(&document.file_name) else {
            return Vec::new();
        };
        let Some(node) = identifier_at(source, offset) else {
            return Vec::new();
        };
        let Some(name) = identifier_text(source, node) else {
            return Vec::new();
        };
        let Some((target_source, target_symbol)) =
            semantic_target(&program, &self.workspace, source, node, name)
        else {
            return Vec::new();
        };
        let declaration = declaration_name_node(target_source, target_symbol);
        semantic_occurrences(
            &program,
            &self.workspace,
            &target_source.file_name,
            target_symbol,
        )
        .into_iter()
        .filter(|(source, node)| {
            params.context.include_declaration
                || declaration.is_none_or(|declaration| {
                    source.file_name != target_source.file_name || *node != declaration
                })
        })
        .filter_map(|(source, node)| {
            Some(Location {
                uri: self.uri_for_file(&source.file_name)?,
                range: node_range(source, node)?,
            })
        })
        .collect()
    }

    fn rename(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<RenameParams>(params) else {
            return failure(id, CODE_INVALID_PARAMS, "invalid rename parameters");
        };
        if !is_identifier_name(&params.new_name) {
            return failure(
                id,
                CODE_INVALID_PARAMS,
                "new name is not a valid identifier",
            );
        }
        let Some(edit) = self.rename_at(&params) else {
            return failure(id, CODE_INVALID_PARAMS, "no rename target at position");
        };
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(edit).unwrap_or(Value::Null),
        ))
    }

    fn rename_at(&self, params: &RenameParams) -> Option<WorkspaceEdit> {
        let document = self.documents.get(&params.text_document.uri)?;
        let offset = u32::try_from(byte_offset(&document.text, params.position).ok()?).ok()?;
        let program = self.build_program();
        let source = program.source_file(&document.file_name)?;
        let node = identifier_at(source, offset)?;
        let name = identifier_text(source, node)?;
        let (target_source, target_symbol) =
            semantic_target(&program, &self.workspace, source, node, name)?;
        let mut changes = BTreeMap::<DocumentUri, Vec<TextEdit>>::new();
        for (source, node) in semantic_occurrences(
            &program,
            &self.workspace,
            &target_source.file_name,
            target_symbol,
        ) {
            changes
                .entry(self.uri_for_file(&source.file_name)?)
                .or_default()
                .push(TextEdit {
                    range: node_range(source, node)?,
                    new_text: params.new_name.clone(),
                });
        }
        (!changes.is_empty()).then_some(WorkspaceEdit { changes })
    }

    fn uri_for_file(&self, file_name: &str) -> Option<DocumentUri> {
        self.documents
            .iter()
            .find_map(|(uri, document)| (document.file_name == file_name).then(|| uri.clone()))
    }

    fn document_symbol(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<DocumentSymbolParams>(params) else {
            return failure(
                id,
                CODE_INVALID_PARAMS,
                "invalid document symbol parameters",
            );
        };
        let symbols = self.document_symbols(&params.text_document.uri);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(symbols).unwrap_or(Value::Null),
        ))
    }

    fn document_symbols(&self, uri: &DocumentUri) -> Vec<DocumentSymbol> {
        let Some(document) = self.documents.get(uri) else {
            return Vec::new();
        };
        let program = self.build_program();
        let Some(source) = program.source_file(&document.file_name) else {
            return Vec::new();
        };
        source
            .parse
            .arena
            .get(source.parse.source_file)
            .and_then(|node| match &node.data {
                NodeData::SourceFile(file) => Some(
                    file.statements
                        .nodes
                        .iter()
                        .flat_map(|statement| document_symbols_for_node(source, *statement))
                        .collect(),
                ),
                _ => None,
            })
            .unwrap_or_default()
    }

    fn completion(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<TextDocumentPositionParams>(params) else {
            return failure(id, CODE_INVALID_PARAMS, "invalid completion parameters");
        };
        let items = self.completion_at(&params);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(items).unwrap_or(Value::Null),
        ))
    }

    fn completion_at(&self, params: &TextDocumentPositionParams) -> Vec<CompletionItem> {
        let Some(document) = self.documents.get(&params.text_document.uri) else {
            return Vec::new();
        };
        let Ok(offset) = byte_offset(&document.text, params.position) else {
            return Vec::new();
        };
        let Ok(offset) = u32::try_from(offset) else {
            return Vec::new();
        };
        let program = self.build_program();
        let Some(source) = program.source_file(&document.file_name) else {
            return Vec::new();
        };
        completion_items(&program, source, offset)
    }

    fn signature_help(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<SignatureHelpParams>(params) else {
            return failure(id, CODE_INVALID_PARAMS, "invalid signature help parameters");
        };
        let result = self.signature_help_at(&params);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn signature_help_at(&self, params: &SignatureHelpParams) -> Option<SignatureHelp> {
        let document = self.documents.get(&params.text_document.uri)?;
        let offset = u32::try_from(byte_offset(&document.text, params.position).ok()?).ok()?;
        let program = self.build_program();
        let source = program.source_file(&document.file_name)?;
        signature_help_at(&program, &self.workspace, source, offset)
    }

    fn prepare_call_hierarchy(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<TextDocumentPositionParams>(params) else {
            return failure(id, CODE_INVALID_PARAMS, "invalid call hierarchy parameters");
        };
        let result = self.prepare_call_hierarchy_at(&params);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn prepare_call_hierarchy_at(
        &self,
        params: &TextDocumentPositionParams,
    ) -> Option<Vec<CallHierarchyItem>> {
        let document = self.documents.get(&params.text_document.uri)?;
        let offset = u32::try_from(byte_offset(&document.text, params.position).ok()?).ok()?;
        let program = self.build_program();
        let source = program.source_file(&document.file_name)?;
        let node = identifier_at(source, offset)?;
        let name = identifier_text(source, node)?;
        let (target_source, symbol) =
            semantic_target(&program, &self.workspace, source, node, name)?;
        Some(vec![
            self.call_hierarchy_item_for_symbol(target_source, symbol)?,
        ])
    }

    fn incoming_calls(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<CallHierarchyCallsParams>(params) else {
            return failure(id, CODE_INVALID_PARAMS, "invalid incoming calls parameters");
        };
        let result = self.incoming_calls_for(&params.item);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn incoming_calls_for(&self, item: &CallHierarchyItem) -> Vec<CallHierarchyIncomingCall> {
        let Ok(data) = serde_json::from_value::<CallHierarchyData>(item.data.clone()) else {
            return Vec::new();
        };
        let program = self.build_program();
        let Some(source) = program.source_file(&data.file_name) else {
            return Vec::new();
        };
        let Some(declaration) = call_hierarchy_declaration_at(source, data.declaration_start)
        else {
            return Vec::new();
        };
        let Some(symbol) = symbol_for_declaration(source, declaration) else {
            return Vec::new();
        };
        let mut grouped = BTreeMap::<(String, u32), CallHierarchyIncomingCall>::new();
        for (caller_source, node) in
            semantic_occurrences(&program, &self.workspace, &data.file_name, symbol)
        {
            if call_expression_for_target(caller_source, node).is_none() {
                continue;
            }
            let caller = enclosing_call_hierarchy(caller_source, node);
            let Some(caller_item) = self.call_hierarchy_item_for_declaration(caller_source, caller)
            else {
                continue;
            };
            let start = caller_source
                .parse
                .arena
                .get(caller)
                .map(|node| node.range.start.get())
                .unwrap_or_default();
            let Some(range) = node_range(caller_source, node) else {
                continue;
            };
            grouped
                .entry((caller_source.file_name.clone(), start))
                .and_modify(|call| call.from_ranges.push(range))
                .or_insert(CallHierarchyIncomingCall {
                    from: caller_item,
                    from_ranges: vec![range],
                });
        }
        grouped.into_values().collect()
    }

    fn outgoing_calls(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<CallHierarchyCallsParams>(params) else {
            return failure(id, CODE_INVALID_PARAMS, "invalid outgoing calls parameters");
        };
        let result = self.outgoing_calls_for(&params.item);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn outgoing_calls_for(&self, item: &CallHierarchyItem) -> Vec<CallHierarchyOutgoingCall> {
        let Ok(data) = serde_json::from_value::<CallHierarchyData>(item.data.clone()) else {
            return Vec::new();
        };
        let program = self.build_program();
        let Some(source) = program.source_file(&data.file_name) else {
            return Vec::new();
        };
        let Some(declaration) = call_hierarchy_declaration_at(source, data.declaration_start)
        else {
            return Vec::new();
        };
        let mut grouped = BTreeMap::<(String, u32), CallHierarchyOutgoingCall>::new();
        for (_, target) in calls_in_declaration(source, declaration) {
            let Some(name) = identifier_text(source, target) else {
                continue;
            };
            let Some((target_source, symbol)) =
                semantic_target(&program, &self.workspace, source, target, name)
            else {
                continue;
            };
            let Some(target_item) = self.call_hierarchy_item_for_symbol(target_source, symbol)
            else {
                continue;
            };
            let Some(target_declaration) = declaration_for_symbol(target_source, symbol) else {
                continue;
            };
            let target_start = target_source
                .parse
                .arena
                .get(target_declaration)
                .map(|node| node.range.start.get())
                .unwrap_or_default();
            let Some(range) = node_range(source, target) else {
                continue;
            };
            grouped
                .entry((target_source.file_name.clone(), target_start))
                .and_modify(|entry| entry.from_ranges.push(range))
                .or_insert(CallHierarchyOutgoingCall {
                    to: target_item,
                    from_ranges: vec![range],
                });
        }
        grouped.into_values().collect()
    }

    fn workspace_symbol(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<WorkspaceSymbolParams>(params) else {
            return failure(
                id,
                CODE_INVALID_PARAMS,
                "invalid workspace symbol parameters",
            );
        };
        let result = self.workspace_symbols(&params.query);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn workspace_symbols(&self, query: &str) -> Vec<SymbolInformation> {
        let mut symbols = self
            .documents
            .iter()
            .flat_map(|(uri, _)| {
                self.document_symbols(uri)
                    .into_iter()
                    .flat_map(|symbol| workspace_symbols_for_document(uri, symbol, None))
            })
            .filter(|symbol| workspace_symbol_matches(&symbol.name, query))
            .collect::<Vec<_>>();
        symbols.truncate(256);
        symbols
    }

    fn semantic_tokens_full(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<FoldingRangeParams>(params) else {
            return failure(
                id,
                CODE_INVALID_PARAMS,
                "invalid semantic tokens parameters",
            );
        };
        let program = self.build_program();
        let result = self
            .documents
            .get(&params.text_document.uri)
            .and_then(|document| program.source_file(&document.file_name))
            .map_or_else(|| SemanticTokens { data: Vec::new() }, semantic_tokens);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn folding_range(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<FoldingRangeParams>(params) else {
            return failure(id, CODE_INVALID_PARAMS, "invalid folding range parameters");
        };
        let program = self.build_program();
        let result = self
            .documents
            .get(&params.text_document.uri)
            .and_then(|document| program.source_file(&document.file_name))
            .map_or_else(Vec::new, folding_ranges);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn selection_range(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<SelectionRangeParams>(params) else {
            return failure(
                id,
                CODE_INVALID_PARAMS,
                "invalid selection range parameters",
            );
        };
        let program = self.build_program();
        let result = self
            .documents
            .get(&params.text_document.uri)
            .and_then(|document| program.source_file(&document.file_name))
            .map_or_else(Vec::new, |source| {
                params
                    .positions
                    .iter()
                    .filter_map(|position| selection_range_at(source, *position))
                    .collect()
            });
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn document_highlight(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<TextDocumentPositionParams>(params) else {
            return failure(
                id,
                CODE_INVALID_PARAMS,
                "invalid document highlight parameters",
            );
        };
        let result = self.document_highlights_at(&params);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn document_highlights_at(
        &self,
        params: &TextDocumentPositionParams,
    ) -> Vec<DocumentHighlight> {
        let Some(document) = self.documents.get(&params.text_document.uri) else {
            return Vec::new();
        };
        let Ok(offset) = byte_offset(&document.text, params.position) else {
            return Vec::new();
        };
        let Ok(offset) = u32::try_from(offset) else {
            return Vec::new();
        };
        let program = self.build_program();
        let Some(source) = program.source_file(&document.file_name) else {
            return Vec::new();
        };
        let Some(node) = identifier_at(source, offset) else {
            return Vec::new();
        };
        let Some(name) = identifier_text(source, node) else {
            return Vec::new();
        };
        let Some((target_source, symbol)) =
            semantic_target(&program, &self.workspace, source, node, name)
        else {
            return Vec::new();
        };
        semantic_occurrences(&program, &self.workspace, &target_source.file_name, symbol)
            .into_iter()
            .filter(|(occurrence_source, _)| occurrence_source.file_name == source.file_name)
            .filter_map(|(occurrence_source, occurrence)| {
                Some(DocumentHighlight {
                    range: node_range(occurrence_source, occurrence)?,
                    kind: if is_write_occurrence(occurrence_source, occurrence) {
                        3
                    } else {
                        2
                    },
                })
            })
            .collect()
    }

    fn linked_editing_range(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<TextDocumentPositionParams>(params) else {
            return failure(id, CODE_INVALID_PARAMS, "invalid linked editing parameters");
        };
        let result = self
            .documents
            .get(&params.text_document.uri)
            .and_then(|document| {
                let offset =
                    u32::try_from(byte_offset(&document.text, params.position).ok()?).ok()?;
                let program = self.build_program();
                let source = program.source_file(&document.file_name)?;
                linked_editing_ranges_at(source, offset)
            });
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(result).unwrap_or(Value::Null),
        ))
    }

    fn code_action(&self, id: Id, params: Option<Value>) -> OutgoingMessage {
        let Ok(params) = deserialize_params::<CodeActionParams>(params) else {
            return failure(id, CODE_INVALID_PARAMS, "invalid code action parameters");
        };
        let actions = self.code_actions(&params);
        OutgoingMessage::Response(Response::success(
            id,
            serde_json::to_value(actions).unwrap_or(Value::Null),
        ))
    }

    fn code_actions(&self, params: &CodeActionParams) -> Vec<CodeAction> {
        let Some(document) = self.documents.get(&params.text_document.uri) else {
            return Vec::new();
        };
        let program = self.build_program();
        let Some(source) = program.source_file(&document.file_name) else {
            return Vec::new();
        };
        let mut actions = Vec::new();
        for diagnostic in &params.context.diagnostics {
            let action = match diagnostic.code {
                Some(2304 | 2552) => Self::missing_import_action(
                    &program,
                    source,
                    &params.text_document.uri,
                    diagnostic,
                ),
                Some(6133 | 6138 | 6192 | 6196 | 6198) => {
                    unused_declaration_action(source, &params.text_document.uri, diagnostic)
                }
                _ => None,
            };
            actions.extend(action);
        }
        actions
    }

    fn missing_import_action(
        program: &Program,
        source: &SourceFile,
        uri: &DocumentUri,
        diagnostic: &Diagnostic,
    ) -> Option<CodeAction> {
        let offset =
            u32::try_from(byte_offset(&source.source_text, diagnostic.range.start).ok()?).ok()?;
        let node = identifier_at(source, offset)?;
        let name = identifier_text(source, node)?;
        let target = program.source_files().iter().find(|candidate| {
            candidate.file_name != source.file_name && candidate.binding.exports.get(name).is_some()
        })?;
        let module = relative_module_specifier(&source.file_name, &target.file_name)?;
        let edit = TextEdit {
            range: Range::default(),
            new_text: format!("import {{ {name} }} from \"{module}\";\n"),
        };
        Some(quick_fix(
            format!("Add import from '{module}'"),
            uri,
            diagnostic,
            edit,
        ))
    }

    fn call_hierarchy_item_for_symbol(
        &self,
        source: &SourceFile,
        symbol: SymbolId,
    ) -> Option<CallHierarchyItem> {
        self.call_hierarchy_item_for_declaration(source, declaration_for_symbol(source, symbol)?)
    }

    fn call_hierarchy_item_for_declaration(
        &self,
        source: &SourceFile,
        declaration: NodeId,
    ) -> Option<CallHierarchyItem> {
        let (name, name_node, kind) = call_hierarchy_name(source, declaration)?;
        let declaration_start = source.parse.arena.get(declaration)?.range.start.get();
        Some(CallHierarchyItem {
            name,
            kind,
            uri: self.uri_for_file(&source.file_name)?,
            range: node_range(source, declaration)?,
            selection_range: node_range(source, name_node)?,
            data: serde_json::to_value(CallHierarchyData {
                file_name: source.file_name.clone(),
                declaration_start,
            })
            .ok()?,
        })
    }

    fn build_program(&self) -> Program {
        let roots = self
            .documents
            .values()
            .map(|document| document.file_name.clone())
            .collect::<Vec<_>>();
        Program::new_with_options(&self.workspace, "/", &roots, lightweight_options())
    }
}

fn lightweight_options() -> CompilerOptions {
    CompilerOptions {
        no_emit: true,
        no_lib: true,
        ..CompilerOptions::default()
    }
}

const fn semantic_token_types() -> &'static [&'static str] {
    &[
        "namespace",
        "type",
        "class",
        "enum",
        "interface",
        "struct",
        "typeParameter",
        "parameter",
        "variable",
        "property",
        "enumMember",
        "event",
        "function",
        "method",
        "macro",
        "keyword",
        "modifier",
        "comment",
        "string",
        "number",
        "regexp",
        "operator",
        "decorator",
    ]
}

fn semantic_tokens(source: &SourceFile) -> SemanticTokens {
    let mut tokens = source
        .parse
        .arena
        .iter()
        .filter_map(|(node, value)| {
            let token_type = semantic_token_type(source, node, &value.data, value.kind)?;
            let start = position_at(&source.source_text, value.range.start.get());
            let end = position_at(&source.source_text, value.range.end.get());
            (start.line == end.line && end.character > start.character).then_some((
                start.line,
                start.character,
                end.character - start.character,
                token_type,
            ))
        })
        .collect::<Vec<_>>();
    tokens.sort_unstable();
    tokens.dedup_by_key(|token| (token.0, token.1, token.2));
    let mut data = Vec::with_capacity(tokens.len() * 5);
    let mut previous_line = 0;
    let mut previous_start = 0;
    for (line, start, length, token_type) in tokens {
        let delta_line = line - previous_line;
        let delta_start = if delta_line == 0 {
            start - previous_start
        } else {
            start
        };
        data.extend([delta_line, delta_start, length, token_type, 0]);
        previous_line = line;
        previous_start = start;
    }
    SemanticTokens { data }
}

fn semantic_token_type(
    source: &SourceFile,
    node: NodeId,
    data: &NodeData,
    kind: ts_ast::SyntaxKind,
) -> Option<u32> {
    match data {
        NodeData::Identifier(identifier) => {
            if is_parameter_name(source, node) {
                return Some(7);
            }
            let symbol = resolve_symbol(source, node, &identifier.text)
                .and_then(|symbol| source.binding.symbols.get(symbol));
            Some(symbol.map_or(8, |symbol| semantic_symbol_type(symbol.flags)))
        }
        NodeData::StringLiteral(_) | NodeData::NoSubstitutionTemplateLiteral(_) => Some(18),
        NodeData::NumericLiteral(_) | NodeData::BigIntLiteral(_) => Some(19),
        NodeData::RegularExpressionLiteral(_) => Some(20),
        _ if kind.is_keyword() => Some(15),
        _ => None,
    }
}

fn semantic_symbol_type(flags: SymbolFlags) -> u32 {
    if flags.intersects(SymbolFlags::CLASS) {
        2
    } else if flags.intersects(SymbolFlags::ENUM) {
        3
    } else if flags.intersects(SymbolFlags::INTERFACE) {
        4
    } else if flags.intersects(SymbolFlags::TYPE_PARAMETER) {
        6
    } else if flags.intersects(SymbolFlags::PROPERTY) {
        9
    } else if flags.intersects(SymbolFlags::ENUM_MEMBER) {
        10
    } else if flags.intersects(SymbolFlags::FUNCTION) {
        12
    } else if flags.intersects(SymbolFlags::METHOD) {
        13
    } else if flags.intersects(SymbolFlags::MODULE) {
        0
    } else if flags.intersects(SymbolFlags::TYPE_ALIAS) {
        1
    } else {
        8
    }
}

fn is_parameter_name(source: &SourceFile, node: NodeId) -> bool {
    let Some(parent) = source.parse.arena.get(node).and_then(|node| node.parent) else {
        return false;
    };
    matches!(
        source.parse.arena.get(parent).map(|node| &node.data),
        Some(NodeData::ParameterDeclaration(parameter)) if parameter.name == node
    )
}

fn folding_ranges(source: &SourceFile) -> Vec<FoldingRange> {
    let mut ranges = BTreeSet::new();
    for (_, node) in source.parse.arena.iter() {
        if !is_foldable_node(&node.data) {
            continue;
        }
        let start = position_at(&source.source_text, node.range.start.get());
        let end = position_at(&source.source_text, node.range.end.get());
        if end.line > start.line {
            ranges.insert((start.line, start.character, end.line, end.character));
        }
    }
    ranges
        .into_iter()
        .map(
            |(start_line, start_character, end_line, end_character)| FoldingRange {
                start_line,
                start_character,
                end_line,
                end_character,
            },
        )
        .collect()
}

fn is_foldable_node(data: &NodeData) -> bool {
    matches!(
        data,
        NodeData::Block(_)
            | NodeData::ClassDeclaration(_)
            | NodeData::InterfaceDeclaration(_)
            | NodeData::EnumDeclaration(_)
            | NodeData::ModuleBlock(_)
            | NodeData::ObjectLiteralExpression(_)
            | NodeData::ArrayLiteralExpression(_)
            | NodeData::SwitchStatement(_)
            | NodeData::JsxElement(_)
    )
}

fn selection_range_at(source: &SourceFile, position: Position) -> Option<SelectionRange> {
    let offset = u32::try_from(byte_offset(&source.source_text, position).ok()?).ok()?;
    let mut node = source
        .parse
        .arena
        .iter()
        .filter(|(_, node)| node.range.start.get() <= offset && offset <= node.range.end.get())
        .min_by_key(|(_, node)| node.range.len())
        .map(|(node, _)| node)?;
    let mut ranges = Vec::new();
    loop {
        let current = source.parse.arena.get(node)?;
        let range = node_range(source, node)?;
        if ranges.last() != Some(&range) {
            ranges.push(range);
        }
        let Some(parent) = current.parent else {
            break;
        };
        node = parent;
    }
    let mut result = None;
    for range in ranges.into_iter().rev() {
        result = Some(SelectionRange {
            range,
            parent: result.map(Box::new),
        });
    }
    result
}

fn is_write_occurrence(source: &SourceFile, node: NodeId) -> bool {
    let Some(parent) = source.parse.arena.get(node).and_then(|node| node.parent) else {
        return false;
    };
    match &source.parse.arena.get(parent).map(|node| &node.data) {
        Some(NodeData::VariableDeclaration(declaration)) => declaration.name == node,
        Some(NodeData::ParameterDeclaration(parameter)) => parameter.name == node,
        Some(NodeData::FunctionDeclaration(function)) => function.name == Some(node),
        Some(NodeData::ClassDeclaration(class)) => class.name == Some(node),
        Some(NodeData::InterfaceDeclaration(interface)) => interface.name == node,
        Some(NodeData::TypeAliasDeclaration(alias)) => alias.name == node,
        Some(NodeData::EnumDeclaration(enumeration)) => enumeration.name == node,
        Some(NodeData::MethodDeclaration(method)) => method.name == node,
        Some(NodeData::PropertyDeclaration(property)) => property.name == node,
        Some(NodeData::BinaryExpression(binary)) => {
            binary.left == node
                && source
                    .parse
                    .arena
                    .get(binary.operator_token)
                    .is_some_and(|op| {
                        matches!(
                            op.kind,
                            ts_ast::SyntaxKind::EqualsToken
                                | ts_ast::SyntaxKind::PlusEqualsToken
                                | ts_ast::SyntaxKind::MinusEqualsToken
                                | ts_ast::SyntaxKind::AsteriskEqualsToken
                                | ts_ast::SyntaxKind::SlashEqualsToken
                        )
                    })
        }
        _ => false,
    }
}

fn linked_editing_ranges_at(source: &SourceFile, offset: u32) -> Option<LinkedEditingRanges> {
    let identifier = identifier_at(source, offset)?;
    let tag = ancestor_of_kind(source, identifier, |data| {
        matches!(
            data,
            NodeData::JsxOpeningElement(_) | NodeData::JsxClosingElement(_)
        )
    })?;
    let element = ancestor_of_kind(source, tag, |data| matches!(data, NodeData::JsxElement(_)))?;
    let NodeData::JsxElement(element) = &source.parse.arena.get(element)?.data else {
        return None;
    };
    let NodeData::JsxOpeningElement(opening) =
        &source.parse.arena.get(element.opening_element)?.data
    else {
        return None;
    };
    let NodeData::JsxClosingElement(closing) =
        &source.parse.arena.get(element.closing_element)?.data
    else {
        return None;
    };
    (node_text(source, opening.tag_name)? == node_text(source, closing.tag_name)?).then(|| {
        Some(LinkedEditingRanges {
            ranges: vec![
                node_range(source, opening.tag_name)?,
                node_range(source, closing.tag_name)?,
            ],
            word_pattern: Some("[-._$a-zA-Z0-9]+".to_owned()),
        })
    })?
}

fn unused_declaration_action(
    source: &SourceFile,
    uri: &DocumentUri,
    diagnostic: &Diagnostic,
) -> Option<CodeAction> {
    let offset =
        u32::try_from(byte_offset(&source.source_text, diagnostic.range.start).ok()?).ok()?;
    let identifier = identifier_at(source, offset)?;
    let name = identifier_text(source, identifier)?;
    if let Some(parent) = source.parse.arena.get(identifier)?.parent
        && matches!(
            source.parse.arena.get(parent).map(|node| &node.data),
            Some(NodeData::ParameterDeclaration(parameter)) if parameter.name == identifier
        )
    {
        return (!name.starts_with('_')).then(|| {
            quick_fix(
                format!("Rename unused parameter to '_{name}'"),
                uri,
                diagnostic,
                TextEdit {
                    range: node_range(source, identifier).unwrap_or(diagnostic.range),
                    new_text: format!("_{name}"),
                },
            )
        });
    }
    let removal = removable_declaration(source, identifier, diagnostic.code?)?;
    Some(quick_fix(
        format!("Remove unused declaration '{name}'"),
        uri,
        diagnostic,
        TextEdit {
            range: removal_range(source, removal)?,
            new_text: String::new(),
        },
    ))
}

fn removable_declaration(source: &SourceFile, mut node: NodeId, code: u32) -> Option<NodeId> {
    loop {
        let current = source.parse.arena.get(node)?;
        match &current.data {
            NodeData::VariableDeclaration(_) => {
                let list = current.parent?;
                let NodeData::VariableDeclarationList(list_data) =
                    &source.parse.arena.get(list)?.data
                else {
                    return None;
                };
                if list_data.declarations.nodes.len() != 1 {
                    return None;
                }
                return source.parse.arena.get(list)?.parent;
            }
            NodeData::FunctionDeclaration(_)
            | NodeData::ClassDeclaration(_)
            | NodeData::InterfaceDeclaration(_)
            | NodeData::TypeAliasDeclaration(_)
            | NodeData::EnumDeclaration(_)
            | NodeData::PropertyDeclaration(_) => return Some(node),
            NodeData::ImportDeclaration(_) if code == 6192 => return Some(node),
            NodeData::SourceFile(_) => return None,
            _ => node = current.parent?,
        }
    }
}

fn removal_range(source: &SourceFile, node: NodeId) -> Option<Range> {
    let range = source.parse.arena.get(node)?.range;
    let mut end = usize::try_from(range.end.get()).ok()?;
    if source.source_text.as_bytes().get(end) == Some(&b'\r') {
        end += 1;
    }
    if source.source_text.as_bytes().get(end) == Some(&b'\n') {
        end += 1;
    }
    Some(Range {
        start: position_at(&source.source_text, range.start.get()),
        end: position_at(&source.source_text, u32::try_from(end).ok()?),
    })
}

fn quick_fix(
    title: String,
    uri: &DocumentUri,
    diagnostic: &Diagnostic,
    edit: TextEdit,
) -> CodeAction {
    CodeAction {
        title,
        kind: "quickfix".to_owned(),
        diagnostics: vec![diagnostic.clone()],
        edit: WorkspaceEdit {
            changes: BTreeMap::from([(uri.clone(), vec![edit])]),
        },
        is_preferred: true,
    }
}

fn relative_module_specifier(from: &str, to: &str) -> Option<String> {
    let from = from.rsplit_once('/').map_or("", |(directory, _)| directory);
    let mut target = to.to_owned();
    for extension in [".d.ts", ".tsx", ".ts", ".jsx", ".js"] {
        if target.ends_with(extension) {
            target.truncate(target.len() - extension.len());
            break;
        }
    }
    if target.ends_with("/index") {
        target.truncate(target.len() - "/index".len());
    }
    let from = from
        .split('/')
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>();
    let to = target
        .split('/')
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>();
    let common = from
        .iter()
        .zip(&to)
        .take_while(|(left, right)| left == right)
        .count();
    let mut parts = vec![".."; from.len().saturating_sub(common)];
    parts.extend(to[common..].iter().copied());
    let path = parts.join("/");
    (!path.is_empty()).then(|| {
        if path.starts_with('.') {
            path
        } else {
            format!("./{path}")
        }
    })
}

fn document_symbols_for_node(source: &SourceFile, node: NodeId) -> Vec<DocumentSymbol> {
    let Some(value) = source.parse.arena.get(node) else {
        return Vec::new();
    };
    match &value.data {
        NodeData::VariableStatement(statement) => source
            .parse
            .arena
            .get(statement.declaration_list)
            .and_then(|list| match &list.data {
                NodeData::VariableDeclarationList(list) => Some(
                    list.declarations
                        .nodes
                        .iter()
                        .filter_map(|declaration| {
                            let NodeData::VariableDeclaration(variable) =
                                &source.parse.arena.get(*declaration)?.data
                            else {
                                return None;
                            };
                            make_document_symbol(source, *declaration, variable.name, 13, None)
                        })
                        .collect(),
                ),
                _ => None,
            })
            .unwrap_or_default(),
        NodeData::FunctionDeclaration(function) => function
            .name
            .and_then(|name| make_document_symbol(source, node, name, 12, None))
            .into_iter()
            .collect(),
        NodeData::ClassDeclaration(class) => class
            .name
            .and_then(|name| {
                make_document_symbol(
                    source,
                    node,
                    name,
                    5,
                    Some(member_symbols(source, &class.members.nodes)),
                )
            })
            .into_iter()
            .collect(),
        NodeData::InterfaceDeclaration(interface) => make_document_symbol(
            source,
            node,
            interface.name,
            11,
            Some(member_symbols(source, &interface.members.nodes)),
        )
        .into_iter()
        .collect(),
        NodeData::TypeAliasDeclaration(alias) => {
            make_document_symbol(source, node, alias.name, 23, None)
                .into_iter()
                .collect()
        }
        NodeData::EnumDeclaration(enumeration) => make_document_symbol(
            source,
            node,
            enumeration.name,
            10,
            Some(member_symbols(source, &enumeration.members.nodes)),
        )
        .into_iter()
        .collect(),
        NodeData::ModuleDeclaration(module) => make_document_symbol(
            source,
            node,
            module.name,
            3,
            module.body.map(|body| namespace_symbols(source, body)),
        )
        .into_iter()
        .collect(),
        _ => Vec::new(),
    }
}

fn member_symbols(source: &SourceFile, members: &[NodeId]) -> Vec<DocumentSymbol> {
    members
        .iter()
        .filter_map(|member| {
            let value = source.parse.arena.get(*member)?;
            let (name, kind) = match &value.data {
                NodeData::MethodDeclaration(method) => (method.name, 6),
                NodeData::MethodSignatureDeclaration(method) => (method.name, 6),
                NodeData::PropertyDeclaration(property) => (property.name, 8),
                NodeData::PropertySignatureDeclaration(property) => (property.name, 7),
                NodeData::GetAccessorDeclaration(accessor) => (accessor.name, 7),
                NodeData::SetAccessorDeclaration(accessor) => (accessor.name, 7),
                NodeData::EnumMember(member) => (member.name, 22),
                NodeData::ConstructorDeclaration(_) => {
                    let range = node_range(source, *member)?;
                    return Some(DocumentSymbol {
                        name: "constructor".to_owned(),
                        kind: 9,
                        range,
                        selection_range: range,
                        children: None,
                    });
                }
                _ => return None,
            };
            make_document_symbol(source, *member, name, kind, None)
        })
        .collect()
}

fn namespace_symbols(source: &SourceFile, body: NodeId) -> Vec<DocumentSymbol> {
    match &source.parse.arena.get(body).map(|node| &node.data) {
        Some(NodeData::ModuleBlock(block)) => block
            .statements
            .nodes
            .iter()
            .flat_map(|statement| document_symbols_for_node(source, *statement))
            .collect(),
        Some(NodeData::ModuleDeclaration(_)) => document_symbols_for_node(source, body),
        _ => Vec::new(),
    }
}

fn make_document_symbol(
    source: &SourceFile,
    node: NodeId,
    name_node: NodeId,
    kind: u8,
    children: Option<Vec<DocumentSymbol>>,
) -> Option<DocumentSymbol> {
    let name = declaration_name_text(source, name_node)?.to_owned();
    Some(DocumentSymbol {
        name,
        kind,
        range: node_range(source, node)?,
        selection_range: node_range(source, name_node)?,
        children: children.filter(|children| !children.is_empty()),
    })
}

fn workspace_symbols_for_document(
    uri: &DocumentUri,
    symbol: DocumentSymbol,
    container_name: Option<&str>,
) -> Vec<SymbolInformation> {
    let mut result = vec![SymbolInformation {
        name: symbol.name.clone(),
        kind: symbol.kind,
        location: Location {
            uri: uri.clone(),
            range: symbol.selection_range,
        },
        container_name: container_name.map(str::to_owned),
    }];
    if let Some(children) = symbol.children {
        for child in children {
            result.extend(workspace_symbols_for_document(
                uri,
                child,
                Some(&symbol.name),
            ));
        }
    }
    result
}

fn workspace_symbol_matches(name: &str, query: &str) -> bool {
    let name = name.to_lowercase();
    let query = query.to_lowercase();
    if name.contains(&query) {
        return true;
    }
    let mut characters = name.chars();
    query
        .chars()
        .all(|expected| characters.by_ref().any(|actual| actual == expected))
}

fn signature_help_at(
    program: &Program,
    workspace: &MemoryFileSystem,
    source: &SourceFile,
    offset: u32,
) -> Option<SignatureHelp> {
    let (expression, arguments) = source
        .parse
        .arena
        .iter()
        .filter_map(|(_, value)| match &value.data {
            NodeData::CallExpression(call)
                if value.range.start.get() <= offset && offset <= value.range.end.get() =>
            {
                Some((
                    call.expression,
                    call.arguments.nodes.as_slice(),
                    value.range.len(),
                ))
            }
            NodeData::NewExpression(call)
                if value.range.start.get() <= offset && offset <= value.range.end.get() =>
            {
                Some((
                    call.expression,
                    call.arguments
                        .as_ref()
                        .map_or(&[] as &[NodeId], |args| args.nodes.as_slice()),
                    value.range.len(),
                ))
            }
            _ => None,
        })
        .min_by_key(|(_, _, length)| *length)
        .map(|(expression, arguments, _)| (expression, arguments))?;
    let target = rightmost_identifier(source, expression)?;
    let name = identifier_text(source, target)?;
    let (target_source, symbol) = semantic_target(program, workspace, source, target, name)?;
    let symbol = target_source.binding.symbols.get(symbol)?;
    let mut signatures = symbol
        .declarations
        .iter()
        .filter_map(|declaration| signature_information(target_source, *declaration, &symbol.name))
        .collect::<Vec<_>>();
    if signatures.is_empty() {
        let declaration = declaration_for_symbol(target_source, symbol.id)?;
        signatures.push(signature_information(
            target_source,
            declaration,
            &symbol.name,
        )?);
    }
    let active_parameter = arguments
        .iter()
        .filter(|argument| {
            source
                .parse
                .arena
                .get(**argument)
                .is_some_and(|argument| argument.range.end.get() < offset)
        })
        .count();
    let active_signature = signatures
        .iter()
        .position(|signature| active_parameter < signature.parameters.len())
        .unwrap_or(0);
    Some(SignatureHelp {
        signatures,
        active_signature: u32::try_from(active_signature).unwrap_or_default(),
        active_parameter: u32::try_from(active_parameter).unwrap_or(u32::MAX),
    })
}

fn signature_information(
    source: &SourceFile,
    declaration: NodeId,
    name: &str,
) -> Option<SignatureInformation> {
    let value = source.parse.arena.get(declaration)?;
    if let NodeData::VariableDeclaration(variable) = &value.data
        && let Some(initializer) = variable.initializer
    {
        return signature_information(source, initializer, name);
    }
    if let NodeData::ClassDeclaration(class) = &value.data {
        return class.members.nodes.iter().find_map(|member| {
            matches!(
                source.parse.arena.get(*member).map(|node| &node.data),
                Some(NodeData::ConstructorDeclaration(_))
            )
            .then(|| signature_information(source, *member, name))
            .flatten()
        });
    }
    let (parameters, return_type) = match &value.data {
        NodeData::FunctionDeclaration(function) => (&function.parameters.nodes, function.type_),
        NodeData::FunctionExpression(function) => (&function.parameters.nodes, function.type_),
        NodeData::ArrowFunction(function) => (&function.parameters.nodes, function.type_),
        NodeData::MethodDeclaration(method) => (&method.parameters.nodes, method.type_),
        NodeData::MethodSignatureDeclaration(method) => (&method.parameters.nodes, method.type_),
        NodeData::CallSignatureDeclaration(signature) => {
            (&signature.parameters.nodes, signature.type_)
        }
        NodeData::ConstructorDeclaration(constructor) => (&constructor.parameters.nodes, None),
        _ => return None,
    };
    let parameters = parameters
        .iter()
        .filter_map(|parameter| {
            Some(ParameterInformation {
                label: node_text(source, *parameter)?.trim().to_owned(),
            })
        })
        .collect::<Vec<_>>();
    let mut label = format!(
        "{name}({})",
        parameters
            .iter()
            .map(|parameter| parameter.label.as_str())
            .collect::<Vec<_>>()
            .join(", ")
    );
    if let Some(return_type) = return_type {
        label.push_str(": ");
        label.push_str(node_text(source, return_type)?.trim());
    }
    Some(SignatureInformation { label, parameters })
}

fn node_text(source: &SourceFile, node: NodeId) -> Option<&str> {
    let range = source.parse.arena.get(node)?.range;
    source
        .source_text
        .get(usize::try_from(range.start.get()).ok()?..usize::try_from(range.end.get()).ok()?)
}

fn rightmost_identifier(source: &SourceFile, node: NodeId) -> Option<NodeId> {
    match &source.parse.arena.get(node)?.data {
        NodeData::Identifier(_) => Some(node),
        NodeData::PropertyAccessExpression(access) => rightmost_identifier(source, access.name),
        NodeData::ParenthesizedExpression(expression) => {
            rightmost_identifier(source, expression.expression)
        }
        NodeData::NonNullExpression(expression) => {
            rightmost_identifier(source, expression.expression)
        }
        _ => None,
    }
}

fn declaration_for_symbol(source: &SourceFile, symbol: SymbolId) -> Option<NodeId> {
    let symbol = source.binding.symbols.get(symbol)?;
    symbol
        .declarations
        .iter()
        .copied()
        .find_map(|declaration| callable_from_declaration(source, declaration))
        .or_else(|| {
            symbol
                .declarations
                .iter()
                .find_map(|declaration| enclosing_callable(source, *declaration))
        })
}

fn callable_from_declaration(source: &SourceFile, declaration: NodeId) -> Option<NodeId> {
    if is_callable_declaration(source, declaration) {
        return Some(declaration);
    }
    let NodeData::VariableDeclaration(variable) = &source.parse.arena.get(declaration)?.data else {
        return None;
    };
    variable
        .initializer
        .filter(|initializer| is_callable_declaration(source, *initializer))
}

fn symbol_for_declaration(source: &SourceFile, declaration: NodeId) -> Option<SymbolId> {
    let binding_declaration = match source.parse.arena.get(declaration)?.data {
        NodeData::ArrowFunction(_) | NodeData::FunctionExpression(_) => source
            .parse
            .arena
            .get(declaration)?
            .parent
            .filter(|parent| {
                matches!(
                    source.parse.arena.get(*parent).map(|node| &node.data),
                    Some(NodeData::VariableDeclaration(_))
                )
            })
            .unwrap_or(declaration),
        _ => declaration,
    };
    source
        .binding
        .symbols
        .iter()
        .find(|symbol| symbol.declarations.contains(&binding_declaration))
        .map(|symbol| symbol.target.unwrap_or(symbol.id))
}

fn is_callable_declaration(source: &SourceFile, declaration: NodeId) -> bool {
    matches!(
        source.parse.arena.get(declaration).map(|node| &node.data),
        Some(
            NodeData::FunctionDeclaration(_)
                | NodeData::FunctionExpression(_)
                | NodeData::ArrowFunction(_)
                | NodeData::MethodDeclaration(_)
                | NodeData::ConstructorDeclaration(_)
        )
    )
}

fn call_hierarchy_declaration_at(source: &SourceFile, start: u32) -> Option<NodeId> {
    source
        .parse
        .arena
        .iter()
        .find(|(node, value)| {
            value.range.start.get() == start
                && (is_callable_declaration(source, *node) || *node == source.parse.source_file)
        })
        .map(|(node, _)| node)
}

fn enclosing_callable(source: &SourceFile, mut node: NodeId) -> Option<NodeId> {
    while let Some(parent) = source.parse.arena.get(node)?.parent {
        if is_callable_declaration(source, parent) {
            return Some(parent);
        }
        node = parent;
    }
    None
}

fn enclosing_call_hierarchy(source: &SourceFile, node: NodeId) -> NodeId {
    enclosing_callable(source, node).unwrap_or(source.parse.source_file)
}

fn call_hierarchy_name(source: &SourceFile, declaration: NodeId) -> Option<(String, NodeId, u8)> {
    match &source.parse.arena.get(declaration)?.data {
        NodeData::FunctionDeclaration(function) => {
            let name = function.name?;
            Some((identifier_text(source, name)?.to_owned(), name, 12))
        }
        NodeData::FunctionExpression(function) => {
            let name = function.name?;
            Some((identifier_text(source, name)?.to_owned(), name, 12))
        }
        NodeData::MethodDeclaration(method) => Some((
            declaration_name_text(source, method.name)?.to_owned(),
            method.name,
            6,
        )),
        NodeData::ConstructorDeclaration(_) => Some(("constructor".to_owned(), declaration, 9)),
        NodeData::ArrowFunction(_) => {
            let parent = source.parse.arena.get(declaration)?.parent?;
            let NodeData::VariableDeclaration(variable) = &source.parse.arena.get(parent)?.data
            else {
                return None;
            };
            Some((
                declaration_name_text(source, variable.name)?.to_owned(),
                variable.name,
                12,
            ))
        }
        NodeData::SourceFile(_) => Some((
            source
                .file_name
                .rsplit('/')
                .next()
                .unwrap_or(&source.file_name)
                .to_owned(),
            declaration,
            1,
        )),
        _ => None,
    }
}

fn call_expression_for_target(source: &SourceFile, node: NodeId) -> Option<NodeId> {
    let parent = source.parse.arena.get(node)?.parent?;
    match &source.parse.arena.get(parent)?.data {
        NodeData::CallExpression(call) if call.expression == node => Some(parent),
        NodeData::NewExpression(call) if call.expression == node => Some(parent),
        NodeData::PropertyAccessExpression(access) if access.name == node => {
            let call = source.parse.arena.get(parent)?.parent?;
            match &source.parse.arena.get(call)?.data {
                NodeData::CallExpression(expression) if expression.expression == parent => {
                    Some(call)
                }
                NodeData::NewExpression(expression) if expression.expression == parent => {
                    Some(call)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn calls_in_declaration(source: &SourceFile, declaration: NodeId) -> Vec<(NodeId, NodeId)> {
    source
        .parse
        .arena
        .iter()
        .filter_map(|(node, value)| {
            let expression = match &value.data {
                NodeData::CallExpression(call) => call.expression,
                NodeData::NewExpression(call) => call.expression,
                _ => return None,
            };
            (enclosing_call_hierarchy(source, node) == declaration)
                .then(|| rightmost_identifier(source, expression).map(|target| (node, target)))
                .flatten()
        })
        .collect()
}

fn declaration_name_text(source: &SourceFile, node: NodeId) -> Option<&str> {
    match &source.parse.arena.get(node)?.data {
        NodeData::Identifier(name) => Some(&name.text),
        NodeData::StringLiteral(name) => Some(&name.text),
        NodeData::NumericLiteral(name) => Some(&name.text),
        _ => None,
    }
}

fn completion_items(program: &Program, source: &SourceFile, offset: u32) -> Vec<CompletionItem> {
    let mut names = BTreeMap::<String, u8>::new();
    if let Some(mut scope) = scope_at(source, offset) {
        loop {
            let Some(current) = source.binding.scope(scope) else {
                break;
            };
            for (name, symbol) in current.symbols.iter() {
                if let Some(symbol) = source.binding.symbols.get(symbol) {
                    names
                        .entry(name.to_owned())
                        .or_insert_with(|| completion_kind(symbol.flags));
                }
            }
            let Some(parent) = current.parent else {
                break;
            };
            scope = parent;
        }
    }
    for global_source in program.source_files() {
        if global_source.file_name == source.file_name || is_external_module(global_source) {
            continue;
        }
        let Some(root) = global_source.binding.root_scope() else {
            continue;
        };
        for (name, symbol) in root.symbols.iter() {
            if let Some(symbol) = global_source.binding.symbols.get(symbol) {
                names
                    .entry(name.to_owned())
                    .or_insert_with(|| completion_kind(symbol.flags));
            }
        }
    }
    names
        .into_iter()
        .map(|(label, kind)| CompletionItem { label, kind })
        .collect()
}

fn scope_at(source: &SourceFile, offset: u32) -> Option<ScopeId> {
    let containing = source
        .parse
        .arena
        .iter()
        .filter(|(_, node)| node.range.start.get() <= offset && offset <= node.range.end.get())
        .min_by_key(|(_, node)| node.range.len())
        .map(|(node, _)| node);
    containing
        .and_then(|node| {
            source.binding.node_scopes.get(&node).copied().or_else(|| {
                let container = source.binding.containers.get(&node)?;
                source
                    .binding
                    .node_scopes
                    .get(container)
                    .copied()
                    .or_else(|| {
                        source
                            .binding
                            .scopes
                            .iter()
                            .find(|scope| scope.owner == *container)
                            .map(|scope| scope.id)
                    })
            })
        })
        .or_else(|| source.binding.root_scope().map(|scope| scope.id))
}

fn completion_kind(flags: SymbolFlags) -> u8 {
    if flags.intersects(SymbolFlags::ALIAS) {
        18
    } else if flags.intersects(SymbolFlags::FUNCTION) {
        3
    } else if flags.intersects(SymbolFlags::METHOD) {
        2
    } else if flags.intersects(SymbolFlags::CLASS) {
        7
    } else if flags.intersects(SymbolFlags::INTERFACE) {
        8
    } else if flags.intersects(SymbolFlags::ENUM) {
        13
    } else if flags.intersects(SymbolFlags::MODULE) {
        9
    } else if flags.intersects(SymbolFlags::PROPERTY) {
        10
    } else if flags.intersects(SymbolFlags::ENUM_MEMBER) {
        20
    } else if flags.intersects(SymbolFlags::TYPE_ALIAS) {
        22
    } else if flags.intersects(SymbolFlags::TYPE_PARAMETER) {
        25
    } else if flags.intersects(SymbolFlags::VARIABLE) {
        6
    } else {
        12
    }
}

fn is_external_module(source: &SourceFile) -> bool {
    if !source.binding.exports.is_empty() {
        return true;
    }
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return false;
    };
    file.statements.nodes.iter().any(|statement| {
        matches!(
            source.parse.arena.get(*statement).map(|node| &node.data),
            Some(
                NodeData::ImportDeclaration(_)
                    | NodeData::ImportEqualsDeclaration(_)
                    | NodeData::ExportDeclaration(_)
                    | NodeData::ExportAssignment(_)
            )
        )
    })
}

fn identifier_at(source: &SourceFile, offset: u32) -> Option<NodeId> {
    source
        .parse
        .arena
        .iter()
        .filter(|(_, node)| {
            matches!(node.data, NodeData::Identifier(_))
                && node.range.start.get() <= offset
                && offset < node.range.end.get()
        })
        .min_by_key(|(_, node)| node.range.len())
        .map(|(id, _)| id)
}

fn identifier_text(source: &SourceFile, node: NodeId) -> Option<&str> {
    match &source.parse.arena.get(node)?.data {
        NodeData::Identifier(identifier) => Some(&identifier.text),
        _ => None,
    }
}

fn resolve_symbol(source: &SourceFile, node: NodeId, name: &str) -> Option<SymbolId> {
    if let Some(symbol) = source.binding.node_symbols.get(&node) {
        return Some(*symbol);
    }
    if let Some(container) = source.binding.containers.get(&node)
        && let Some(mut scope) = source
            .binding
            .node_scopes
            .get(container)
            .copied()
            .or_else(|| {
                source
                    .binding
                    .scopes
                    .iter()
                    .find(|scope| scope.owner == *container)
                    .map(|scope| scope.id)
            })
    {
        loop {
            let current = source.binding.scope(scope)?;
            if let Some(symbol) = current.symbols.get(name) {
                return Some(symbol);
            }
            let Some(parent) = current.parent else {
                break;
            };
            scope = parent;
        }
    }
    source
        .binding
        .scopes
        .iter()
        .find_map(|scope| scope.symbols.get(name))
}

fn semantic_target<'a>(
    program: &'a Program,
    workspace: &MemoryFileSystem,
    source: &'a SourceFile,
    node: NodeId,
    name: &str,
) -> Option<(&'a SourceFile, SymbolId)> {
    if let Some(binding) = import_binding_ancestor(source, node)
        && let Some(target) = imported_target(program, workspace, source, binding)
    {
        return Some(target);
    }
    let symbol_id = resolve_symbol(source, node, name)?;
    let symbol = source.binding.symbols.get(symbol_id)?;
    if let Some(binding) = symbol
        .declarations
        .iter()
        .copied()
        .find(|declaration| import_binding_kind(source, *declaration))
        && let Some(target) = imported_target(program, workspace, source, binding)
    {
        return Some(target);
    }
    Some((source, symbol.target.unwrap_or(symbol_id)))
}

fn semantic_occurrences<'a>(
    program: &'a Program,
    workspace: &MemoryFileSystem,
    target_file: &str,
    target_symbol: SymbolId,
) -> Vec<(&'a SourceFile, NodeId)> {
    let mut occurrences = Vec::new();
    for source in program.source_files() {
        for (node, value) in source.parse.arena.iter() {
            let NodeData::Identifier(identifier) = &value.data else {
                continue;
            };
            let Some((candidate_source, candidate_symbol)) =
                semantic_target(program, workspace, source, node, &identifier.text)
            else {
                continue;
            };
            if candidate_source.file_name == target_file && candidate_symbol == target_symbol {
                occurrences.push((source, node));
            }
        }
    }
    occurrences.sort_by(|(left_source, left_node), (right_source, right_node)| {
        left_source
            .file_name
            .cmp(&right_source.file_name)
            .then_with(|| {
                let left = left_source.parse.arena.get(*left_node);
                let right = right_source.parse.arena.get(*right_node);
                left.map(|node| node.range.start)
                    .cmp(&right.map(|node| node.range.start))
            })
    });
    occurrences
}

fn is_identifier_name(name: &str) -> bool {
    let mut characters = name.chars();
    let Some(first) = characters.next() else {
        return false;
    };
    (first == '_' || first == '$' || first.is_alphabetic())
        && characters
            .all(|character| character == '_' || character == '$' || character.is_alphanumeric())
}

fn import_binding_ancestor(source: &SourceFile, mut node: NodeId) -> Option<NodeId> {
    loop {
        if import_binding_kind(source, node) {
            return Some(node);
        }
        node = source.parse.arena.get(node)?.parent?;
    }
}

fn import_binding_kind(source: &SourceFile, node: NodeId) -> bool {
    matches!(
        source.parse.arena.get(node).map(|node| &node.data),
        Some(NodeData::ImportClause(_) | NodeData::ImportSpecifier(_))
    )
}

fn imported_target<'a>(
    program: &'a Program,
    workspace: &MemoryFileSystem,
    source: &SourceFile,
    binding: NodeId,
) -> Option<(&'a SourceFile, SymbolId)> {
    let imported_name = match &source.parse.arena.get(binding)?.data {
        NodeData::ImportClause(_) => "default",
        NodeData::ImportSpecifier(specifier) => {
            identifier_text(source, specifier.property_name.unwrap_or(specifier.name))?
        }
        _ => return None,
    };
    let declaration = ancestor_of_kind(source, binding, |data| {
        matches!(data, NodeData::ImportDeclaration(_))
    })?;
    let NodeData::ImportDeclaration(import) = &source.parse.arena.get(declaration)?.data else {
        return None;
    };
    let NodeData::StringLiteral(module) = &source.parse.arena.get(import.module_specifier)?.data
    else {
        return None;
    };
    let resolved = Resolver::new(workspace, ResolutionOptions::default())
        .resolve(&module.text, &source.file_name)
        .resolved?;
    let target_source = program.source_file(&resolved.resolved_file_name)?;
    let exported = target_source.binding.exports.get(imported_name)?;
    let symbol = target_source.binding.symbols.get(exported)?;
    Some((target_source, symbol.target.unwrap_or(exported)))
}

fn ancestor_of_kind(
    source: &SourceFile,
    mut node: NodeId,
    predicate: impl Fn(&NodeData) -> bool,
) -> Option<NodeId> {
    loop {
        let current = source.parse.arena.get(node)?;
        if predicate(&current.data) {
            return Some(node);
        }
        node = current.parent?;
    }
}

fn declaration_name_node(source: &SourceFile, symbol: SymbolId) -> Option<NodeId> {
    let symbol = source.binding.symbols.get(symbol)?;
    let target = symbol.target.unwrap_or(symbol.id);
    source
        .binding
        .node_symbols
        .iter()
        .filter(|(_, candidate)| **candidate == target)
        .filter_map(|(node, _)| {
            let value = source.parse.arena.get(*node)?;
            matches!(value.data, NodeData::Identifier(_)).then_some((*node, value.range.start))
        })
        .min_by_key(|(_, start)| *start)
        .map(|(node, _)| node)
}

fn node_range(source: &SourceFile, node: NodeId) -> Option<Range> {
    let range = source.parse.arena.get(node)?.range;
    Some(Range {
        start: position_at(&source.source_text, range.start.get()),
        end: position_at(&source.source_text, range.end.get()),
    })
}

fn deserialize_params<T: DeserializeOwned>(params: Option<Value>) -> Result<T, String> {
    serde_json::from_value(params.unwrap_or(Value::Null)).map_err(|error| error.to_string())
}

fn failure(id: Id, code: i32, message: impl Into<String>) -> OutgoingMessage {
    OutgoingMessage::Response(Response::failure(
        Some(id),
        ResponseError::new(code, message, None),
    ))
}

fn diagnostics_for_document(program: &Program, document: &OpenDocument) -> Vec<Diagnostic> {
    program
        .diagnostics()
        .iter()
        .filter(|diagnostic| diagnostic.file_name.as_deref() == Some(&document.file_name))
        .map(|diagnostic| {
            let range = diagnostic.range.unwrap_or_default();
            Diagnostic {
                range: Range {
                    start: position_at(&document.text, range.start.get()),
                    end: position_at(&document.text, range.end.get()),
                },
                severity: Some(1),
                code: diagnostic.code,
                source: Some("ts-rust".to_owned()),
                message: diagnostic.message.clone(),
            }
        })
        .collect()
}

fn file_name_from_uri(uri: &DocumentUri) -> String {
    let Some(encoded_path) = uri.0.strip_prefix("file://") else {
        return format!("/__lsp/{}.ts", stable_hash(uri.0.as_bytes()));
    };
    let path = percent_decode(encoded_path).unwrap_or_else(|| encoded_path.to_owned());
    if path.as_bytes().get(2) == Some(&b':') && path.starts_with('/') {
        path[1..].to_owned()
    } else {
        path
    }
}

fn percent_decode(value: &str) -> Option<String> {
    let mut bytes = Vec::with_capacity(value.len());
    let mut index = 0;
    while index < value.len() {
        let byte = value.as_bytes()[index];
        if byte == b'%' {
            let high = hex(value.as_bytes().get(index + 1).copied()?)?;
            let low = hex(value.as_bytes().get(index + 2).copied()?)?;
            bytes.push(high * 16 + low);
            index += 3;
        } else {
            bytes.push(byte);
            index += 1;
        }
    }
    String::from_utf8(bytes).ok()
}

const fn hex(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn stable_hash(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

fn publish_diagnostics(
    uri: DocumentUri,
    version: Option<i32>,
    diagnostics: Vec<Diagnostic>,
) -> OutgoingMessage {
    let params = PublishDiagnosticsParams {
        uri,
        version,
        diagnostics,
    };
    OutgoingMessage::Notification(Notification::new(
        "textDocument/publishDiagnostics",
        Some(serde_json::to_value(params).unwrap_or(Value::Null)),
    ))
}

fn apply_change(
    text: &mut String,
    change: &TextDocumentContentChangeEvent,
) -> Result<(), PositionError> {
    let Some(range) = change.range else {
        text.clone_from(&change.text);
        return Ok(());
    };
    let start = byte_offset(text, range.start)?;
    let end = byte_offset(text, range.end)?;
    if start > end {
        return Err(PositionError);
    }
    if let Some(expected_length) = change.range_length {
        let actual_length = text[start..end].encode_utf16().count();
        if usize::try_from(expected_length).ok() != Some(actual_length) {
            return Err(PositionError);
        }
    }
    text.replace_range(start..end, &change.text);
    Ok(())
}

#[derive(Clone, Copy, Debug)]
struct PositionError;

fn byte_offset(text: &str, position: Position) -> Result<usize, PositionError> {
    let mut line = 0_u32;
    let mut line_start = 0;
    for (offset, byte) in text.bytes().enumerate() {
        if line == position.line {
            break;
        }
        if byte == b'\n' {
            line += 1;
            line_start = offset + 1;
        }
    }
    if line != position.line {
        return Err(PositionError);
    }
    let mut line_end = text[line_start..]
        .find('\n')
        .map_or(text.len(), |offset| line_start + offset);
    if line_end > line_start && text.as_bytes()[line_end - 1] == b'\r' {
        line_end -= 1;
    }
    let mut utf16_offset = 0_u32;
    for (relative_offset, character) in text[line_start..line_end].char_indices() {
        if utf16_offset == position.character {
            return Ok(line_start + relative_offset);
        }
        utf16_offset += u32::try_from(character.len_utf16()).map_err(|_| PositionError)?;
        if utf16_offset > position.character {
            return Err(PositionError);
        }
    }
    (utf16_offset == position.character)
        .then_some(line_end)
        .ok_or(PositionError)
}

/// Converts a UTF-8 byte offset to a zero-based LSP UTF-16 position.
#[must_use]
pub fn position_at(text: &str, byte_offset: u32) -> Position {
    let requested = usize::try_from(byte_offset)
        .unwrap_or(usize::MAX)
        .min(text.len());
    let mut position = Position::default();
    for (offset, character) in text.char_indices() {
        if offset >= requested {
            break;
        }
        if character == '\n' {
            position.line += 1;
            position.character = 0;
        } else {
            position.character += u32::try_from(character.len_utf16()).unwrap_or(2);
        }
    }
    position
}

/// Successful result of running a framed LSP session to `exit`.
#[derive(Debug)]
pub struct SessionResult<W> {
    pub server: Server,
    pub writer: W,
    pub exit_status: ExitStatus,
}

/// Failure while running a framed session.
#[derive(Debug)]
pub enum SessionError {
    Protocol(ProtocolError),
    UnexpectedEof,
}

impl fmt::Display for SessionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Protocol(error) => error.fmt(formatter),
            Self::UnexpectedEof => formatter.write_str("LSP input ended before exit"),
        }
    }
}

impl Error for SessionError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Protocol(error) => Some(error),
            Self::UnexpectedEof => None,
        }
    }
}

impl From<ProtocolError> for SessionError {
    fn from(error: ProtocolError) -> Self {
        Self::Protocol(error)
    }
}

/// Runs a synchronous framed session until the client sends `exit`.
///
/// # Errors
///
/// Returns framing/JSON errors, or [`SessionError::UnexpectedEof`] if the input
/// closes without an `exit` notification.
pub fn run_framed_session<R: io::Read, W: io::Write>(
    reader: R,
    writer: W,
) -> Result<SessionResult<W>, SessionError> {
    let mut reader = FramedReader::new(reader);
    let mut writer = FramedWriter::new(writer);
    let mut server = Server::default();
    loop {
        let Some(message) = reader.read_message::<Message>()? else {
            return Err(SessionError::UnexpectedEof);
        };
        for outgoing in server.handle_message(message) {
            writer.write_message(&outgoing)?;
        }
        if let Some(exit_status) = server.exit_status() {
            return Ok(SessionResult {
                server,
                writer: writer.into_inner()?,
                exit_status,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use serde_json::json;
    use ts_jsonrpc::{FramedReader, FramedWriter, Request};

    use super::*;

    fn write<T: Serialize>(writer: &mut FramedWriter<Vec<u8>>, message: &T) {
        writer.write_message(message).unwrap();
    }

    fn write_open(writer: &mut FramedWriter<Vec<u8>>, uri: DocumentUri, text: impl Into<String>) {
        write(
            writer,
            &Notification::new(
                "textDocument/didOpen",
                Some(DidOpenTextDocumentParams {
                    text_document: TextDocumentItem {
                        uri,
                        language_id: "typescript".to_owned(),
                        version: 1,
                        text: text.into(),
                    },
                }),
            ),
        );
    }

    fn write_position_request(
        writer: &mut FramedWriter<Vec<u8>>,
        id: i64,
        method: &str,
        uri: DocumentUri,
        position: Position,
    ) {
        write(
            writer,
            &Request::new(
                id,
                method,
                Some(TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri },
                    position,
                }),
            ),
        );
    }

    fn write_reference_request(
        writer: &mut FramedWriter<Vec<u8>>,
        id: i64,
        uri: DocumentUri,
        position: Position,
        include_declaration: bool,
    ) {
        write(
            writer,
            &Request::new(
                id,
                "textDocument/references",
                Some(ReferenceParams {
                    text_document: TextDocumentIdentifier { uri },
                    position,
                    context: ReferenceContext {
                        include_declaration,
                    },
                }),
            ),
        );
    }

    fn write_rename_request(
        writer: &mut FramedWriter<Vec<u8>>,
        id: i64,
        uri: DocumentUri,
        position: Position,
        new_name: &str,
    ) {
        write(
            writer,
            &Request::new(
                id,
                "textDocument/rename",
                Some(RenameParams {
                    text_document: TextDocumentIdentifier { uri },
                    position,
                    new_name: new_name.to_owned(),
                }),
            ),
        );
    }

    fn edit_count(response: &Value, uri: &DocumentUri) -> usize {
        response["result"]["changes"][uri.0.as_str()]
            .as_array()
            .unwrap()
            .len()
    }

    fn begin_framed_session() -> FramedWriter<Vec<u8>> {
        let mut input = FramedWriter::new(Vec::new());
        write(
            &mut input,
            &Request::new(1_i64, "initialize", Some(json!({"capabilities": {}}))),
        );
        write(
            &mut input,
            &Notification::new("initialized", Some(InitializedParams {})),
        );
        input
    }

    fn finish_framed_session(mut input: FramedWriter<Vec<u8>>) -> Vec<Value> {
        write(&mut input, &Request::new(2_i64, "shutdown", None::<Value>));
        write(&mut input, &Notification::new("exit", None::<Value>));
        let result =
            run_framed_session(Cursor::new(input.into_inner().unwrap()), Vec::new()).unwrap();
        let mut reader = FramedReader::new(Cursor::new(result.writer));
        let mut output = Vec::new();
        while let Some(message) = reader.read_message::<Value>().unwrap() {
            output.push(message);
        }
        output
    }

    fn incoming<T: Serialize>(message: &T) -> Message {
        serde_json::from_value(serde_json::to_value(message).unwrap()).unwrap()
    }

    fn ready_server() -> Server {
        let mut server = Server::default();
        let _ = server.handle_message(incoming(&Request::new(
            1_i64,
            "initialize",
            Some(json!({"capabilities": {}})),
        )));
        let _ = server.handle_message(incoming(&Notification::new(
            "initialized",
            Some(InitializedParams {}),
        )));
        assert_eq!(server.state(), LifecycleState::Running);
        server
    }

    fn published_for(messages: &[OutgoingMessage], uri: &str) -> Value {
        messages
            .iter()
            .map(|message| serde_json::to_value(message).unwrap())
            .find(|message| message["params"]["uri"] == uri)
            .unwrap()
    }

    #[test]
    fn positions_and_incremental_changes_use_utf16_code_units() {
        let mut text = "a😀b\nnext".to_owned();
        assert_eq!(
            position_at(&text, 5),
            Position {
                line: 0,
                character: 3
            }
        );
        apply_change(
            &mut text,
            &TextDocumentContentChangeEvent {
                range: Some(Range {
                    start: Position {
                        line: 0,
                        character: 1,
                    },
                    end: Position {
                        line: 0,
                        character: 3,
                    },
                }),
                range_length: Some(2),
                text: "x".to_owned(),
            },
        )
        .unwrap();
        assert_eq!(text, "axb\nnext");
    }

    #[test]
    fn republishes_cross_file_semantic_diagnostics_when_the_graph_changes() {
        let dependency_uri = DocumentUri("file:///workspace/dep.ts".to_owned());
        let main_uri = DocumentUri("file:///workspace/main.ts".to_owned());
        let mut server = ready_server();

        let _ = server.handle_message(incoming(&Notification::new(
            "textDocument/didOpen",
            Some(DidOpenTextDocumentParams {
                text_document: TextDocumentItem {
                    uri: dependency_uri.clone(),
                    language_id: "typescript".to_owned(),
                    version: 1,
                    text: "export const count: number = 1;".to_owned(),
                },
            }),
        )));
        let opened = server.handle_message(incoming(&Notification::new(
            "textDocument/didOpen",
            Some(DidOpenTextDocumentParams {
                text_document: TextDocumentItem {
                    uri: main_uri.clone(),
                    language_id: "typescript".to_owned(),
                    version: 1,
                    text: "import { count } from './dep'; const value: string = count;".to_owned(),
                },
            }),
        )));
        let main = published_for(&opened, &main_uri.0);
        assert!(
            main["params"]["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| diagnostic["code"] == 2322)
        );

        let changed = server.handle_message(incoming(&Notification::new(
            "textDocument/didChange",
            Some(DidChangeTextDocumentParams {
                text_document: VersionedTextDocumentIdentifier {
                    uri: dependency_uri.clone(),
                    version: 2,
                },
                content_changes: vec![TextDocumentContentChangeEvent {
                    range: None,
                    range_length: None,
                    text: "export const count: string = 'fixed';".to_owned(),
                }],
            }),
        )));
        assert_eq!(
            published_for(&changed, &main_uri.0)["params"]["diagnostics"],
            json!([])
        );

        let closed = server.handle_message(incoming(&Notification::new(
            "textDocument/didClose",
            Some(DidCloseTextDocumentParams {
                text_document: TextDocumentIdentifier {
                    uri: dependency_uri.clone(),
                },
            }),
        )));
        assert_eq!(
            published_for(&closed, &dependency_uri.0)["params"]["diagnostics"],
            json!([])
        );
        let main = published_for(&closed, &main_uri.0);
        assert!(
            main["params"]["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| diagnostic["code"] == 2307)
        );
    }

    #[test]
    fn runs_an_in_memory_lifecycle_and_document_session() {
        let uri = DocumentUri("file:///workspace/main.ts".to_owned());
        let mut input = FramedWriter::new(Vec::new());
        write(
            &mut input,
            &Request::new(1_i64, "initialize", Some(json!({"capabilities": {}}))),
        );
        write(
            &mut input,
            &Notification::new("initialized", Some(json!({}))),
        );
        write(
            &mut input,
            &Notification::new(
                "textDocument/didOpen",
                Some(DidOpenTextDocumentParams {
                    text_document: TextDocumentItem {
                        uri: uri.clone(),
                        language_id: "typescript".to_owned(),
                        version: 1,
                        text: "const smile = '😀'; const broken: = 1;".to_owned(),
                    },
                }),
            ),
        );
        write(
            &mut input,
            &Notification::new(
                "textDocument/didChange",
                Some(DidChangeTextDocumentParams {
                    text_document: VersionedTextDocumentIdentifier {
                        uri: uri.clone(),
                        version: 2,
                    },
                    content_changes: vec![TextDocumentContentChangeEvent {
                        range: None,
                        range_length: None,
                        text: "const smile = '😀'; const fixed = 1;".to_owned(),
                    }],
                }),
            ),
        );
        write(
            &mut input,
            &Notification::new(
                "textDocument/didClose",
                Some(DidCloseTextDocumentParams {
                    text_document: TextDocumentIdentifier { uri: uri.clone() },
                }),
            ),
        );
        write(&mut input, &Request::new(2_i64, "shutdown", None::<Value>));
        write(&mut input, &Notification::new("exit", None::<Value>));
        let input = input.into_inner().unwrap();

        let result = run_framed_session(Cursor::new(input), Vec::new()).unwrap();
        assert_eq!(result.exit_status, ExitStatus::Success);
        assert_eq!(result.server.state(), LifecycleState::Exited);
        assert!(result.server.documents().is_empty());

        let mut reader = FramedReader::new(Cursor::new(result.writer));
        let initialize = reader.read_message::<Value>().unwrap().unwrap();
        assert_eq!(initialize["id"], 1);
        assert_eq!(
            initialize["result"]["capabilities"]["textDocumentSync"]["change"],
            2
        );
        let capabilities = &initialize["result"]["capabilities"];
        assert_eq!(capabilities["semanticTokensProvider"]["full"], true);
        assert_eq!(capabilities["foldingRangeProvider"], true);
        assert_eq!(capabilities["selectionRangeProvider"], true);
        assert_eq!(capabilities["documentHighlightProvider"], true);
        assert_eq!(capabilities["linkedEditingRangeProvider"], true);
        assert_eq!(capabilities["codeActionProvider"], true);

        let opened = reader.read_message::<Value>().unwrap().unwrap();
        assert_eq!(opened["method"], "textDocument/publishDiagnostics");
        let diagnostics = opened["params"]["diagnostics"].as_array().unwrap();
        assert!(!diagnostics.is_empty());
        let diagnostic_start = diagnostics[0]["range"]["start"]["character"]
            .as_u64()
            .unwrap();
        let byte_start = ts_parser::parse_source_file("const smile = '😀'; const broken: = 1;")
            .diagnostics[0]
            .range
            .start
            .get();
        assert!(diagnostic_start < u64::from(byte_start));

        let changed = reader.read_message::<Value>().unwrap().unwrap();
        assert_eq!(changed["params"]["version"], 2);
        assert_eq!(changed["params"]["diagnostics"], json!([]));

        let closed = reader.read_message::<Value>().unwrap().unwrap();
        assert_eq!(closed["params"]["uri"], uri.0);
        assert_eq!(closed["params"]["diagnostics"], json!([]));

        let shutdown = reader.read_message::<Value>().unwrap().unwrap();
        assert_eq!(shutdown["id"], 2);
        assert!(shutdown["result"].is_null());
        assert!(reader.read_message::<Value>().unwrap().is_none());
    }

    #[test]
    fn framed_session_serves_hover_and_cross_file_definitions() {
        let dependency_uri = DocumentUri("file:///workspace/dep.ts".to_owned());
        let main_uri = DocumentUri("file:///workspace/main.ts".to_owned());
        let dependency_source = concat!(
            "export const count: number = 1;\n",
            "export default function label(value: number): number { return value; }"
        );
        let main_source = concat!(
            "import label, { count as total } from './dep';\n",
            "const emoji = '😀'; const result: number = label(total);\n",
            "result;"
        );
        let request_position = |needle: &str| {
            let offset = main_source.rfind(needle).unwrap();
            position_at(main_source, u32::try_from(offset).unwrap())
        };
        let mut input = FramedWriter::new(Vec::new());
        write(
            &mut input,
            &Request::new(1_i64, "initialize", Some(json!({"capabilities": {}}))),
        );
        write(
            &mut input,
            &Notification::new("initialized", Some(InitializedParams {})),
        );
        write_open(&mut input, dependency_uri.clone(), dependency_source);
        write_open(&mut input, main_uri.clone(), main_source);
        write_position_request(
            &mut input,
            10,
            "textDocument/hover",
            main_uri.clone(),
            request_position("total"),
        );
        write_position_request(
            &mut input,
            11,
            "textDocument/definition",
            main_uri.clone(),
            request_position("total"),
        );
        write_position_request(
            &mut input,
            12,
            "textDocument/definition",
            main_uri.clone(),
            request_position("label"),
        );
        write_position_request(
            &mut input,
            13,
            "textDocument/definition",
            main_uri.clone(),
            request_position("result"),
        );
        write_position_request(
            &mut input,
            14,
            "textDocument/hover",
            main_uri.clone(),
            Position {
                line: 1,
                character: 5,
            },
        );
        write(&mut input, &Request::new(2_i64, "shutdown", None::<Value>));
        write(&mut input, &Notification::new("exit", None::<Value>));

        let result =
            run_framed_session(Cursor::new(input.into_inner().unwrap()), Vec::new()).unwrap();
        let mut reader = FramedReader::new(Cursor::new(result.writer));
        let mut output = Vec::new();
        while let Some(message) = reader.read_message::<Value>().unwrap() {
            output.push(message);
        }
        let response = |id| output.iter().find(|message| message["id"] == id).unwrap();

        assert_eq!(response(10)["result"]["contents"]["value"], "total: number");
        assert_eq!(response(11)["result"]["uri"], dependency_uri.0);
        assert_eq!(response(11)["result"]["range"]["start"]["line"], 0);
        assert_eq!(response(12)["result"]["uri"], dependency_uri.0);
        assert_eq!(response(12)["result"]["range"]["start"]["line"], 1);
        assert_eq!(response(13)["result"]["uri"], main_uri.0);
        assert_eq!(response(13)["result"]["range"]["start"]["line"], 1);
        assert!(response(14)["result"].is_null());
    }

    #[test]
    fn framed_session_finds_references_and_builds_cross_file_renames() {
        let dependency_uri = DocumentUri("file:///workspace/dep.ts".to_owned());
        let main_uri = DocumentUri("file:///workspace/main.ts".to_owned());
        let dependency_source = concat!(
            "export const count: number = 1;\n",
            "export default function label(value: number): number { return value; }"
        );
        let main_source = concat!(
            "import label, { count as total } from './dep';\n",
            "const result: number = label(total);\n",
            "result;"
        );
        let position = |needle: &str| {
            position_at(
                main_source,
                u32::try_from(main_source.rfind(needle).unwrap()).unwrap(),
            )
        };
        let mut input = begin_framed_session();
        write_open(&mut input, dependency_uri.clone(), dependency_source);
        write_open(&mut input, main_uri.clone(), main_source);
        for (id, name, include_declaration) in [
            (20, "total", true),
            (21, "label", true),
            (22, "result", false),
        ] {
            write_reference_request(
                &mut input,
                id,
                main_uri.clone(),
                position(name),
                include_declaration,
            );
        }
        for (id, name, new_name) in [
            (23, "total", "amount"),
            (24, "label", "describe"),
            (25, "result", "output"),
        ] {
            write_rename_request(&mut input, id, main_uri.clone(), position(name), new_name);
        }
        write_rename_request(
            &mut input,
            26,
            main_uri.clone(),
            Position {
                line: 1,
                character: 5,
            },
            "renamed",
        );

        let output = finish_framed_session(input);
        let response = |id| output.iter().find(|message| message["id"] == id).unwrap();
        assert_eq!(response(20)["result"].as_array().unwrap().len(), 4);
        assert_eq!(response(21)["result"].as_array().unwrap().len(), 3);
        assert_eq!(response(22)["result"].as_array().unwrap().len(), 1);
        assert_eq!(edit_count(response(23), &dependency_uri), 1);
        assert_eq!(edit_count(response(23), &main_uri), 3);
        assert_eq!(edit_count(response(24), &dependency_uri), 1);
        assert_eq!(edit_count(response(24), &main_uri), 2);
        assert_eq!(edit_count(response(25), &main_uri), 2);
        assert_eq!(response(26)["error"]["code"], CODE_INVALID_PARAMS);
    }

    #[test]
    fn framed_session_returns_document_symbols_and_visible_completions() {
        let symbols_uri = DocumentUri("file:///workspace/symbols.ts".to_owned());
        let dependency_uri = DocumentUri("file:///workspace/dep.ts".to_owned());
        let globals_uri = DocumentUri("file:///workspace/globals.ts".to_owned());
        let main_uri = DocumentUri("file:///workspace/main.ts".to_owned());
        let symbols_source = concat!(
            "const value = 1;\n",
            "function run() {}\n",
            "class Box { field: number; method(): number { return this.field; } }\n",
            "interface Shape { size: number; area(): number; }\n",
            "type Name = string;\n",
            "enum Color { Red, Blue }\n",
            "namespace Tools { export const version = 1; }"
        );
        let main_source = concat!(
            "import { count } from './dep';\n",
            "function test(param: string) { const local = count; return local; }"
        );
        let completion_position = position_at(
            main_source,
            u32::try_from(main_source.rfind("local").unwrap()).unwrap(),
        );

        let mut input = begin_framed_session();
        write_open(&mut input, symbols_uri.clone(), symbols_source);
        write_open(&mut input, dependency_uri, "export const count = 1;");
        write_open(&mut input, globals_uri, "const shared = 1;");
        write_open(&mut input, main_uri.clone(), main_source);
        write(
            &mut input,
            &Request::new(
                30_i64,
                "textDocument/documentSymbol",
                Some(DocumentSymbolParams {
                    text_document: TextDocumentIdentifier { uri: symbols_uri },
                }),
            ),
        );
        write_position_request(
            &mut input,
            31,
            "textDocument/completion",
            main_uri,
            completion_position,
        );

        let output = finish_framed_session(input);
        let response = |id| output.iter().find(|message| message["id"] == id).unwrap();
        let symbols = response(30)["result"].as_array().unwrap();
        let names = symbols
            .iter()
            .map(|symbol| symbol["name"].as_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            names,
            ["value", "run", "Box", "Shape", "Name", "Color", "Tools"]
        );
        let children = |name| {
            symbols
                .iter()
                .find(|symbol| symbol["name"] == name)
                .unwrap()["children"]
                .as_array()
                .unwrap()
                .iter()
                .map(|symbol| symbol["name"].as_str().unwrap())
                .collect::<Vec<_>>()
        };
        assert_eq!(children("Box"), ["field", "method"]);
        assert_eq!(children("Shape"), ["size", "area"]);
        assert_eq!(children("Color"), ["Red", "Blue"]);
        assert_eq!(children("Tools"), ["version"]);

        let completions = response(31)["result"].as_array().unwrap();
        let labels = completions
            .iter()
            .map(|item| item["label"].as_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            labels,
            [
                "Box", "Color", "Name", "Shape", "Tools", "count", "local", "param", "run",
                "shared", "test", "value"
            ]
        );
        let completion = |name| {
            completions
                .iter()
                .find(|item| item["label"] == name)
                .unwrap()
        };
        assert_eq!(completion("count")["kind"], 18);
        assert_eq!(completion("test")["kind"], 3);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn framed_session_serves_signature_help_call_hierarchy_and_workspace_symbols() {
        let uri = DocumentUri("file:///workspace/calls.ts".to_owned());
        let source = concat!(
            "function leaf(value: number): number { return value; }\n",
            "function middle(input: number): number { return leaf(input); }\n",
            "function top(): number { return middle(1) + leaf(2); }\n",
            "top();"
        );
        let position = |needle: &str, adjustment: usize| {
            position_at(
                source,
                u32::try_from(source.find(needle).unwrap() + adjustment).unwrap(),
            )
        };
        let hierarchy_item = |name: &str, declaration_start: usize| CallHierarchyItem {
            name: name.to_owned(),
            kind: 12,
            uri: uri.clone(),
            range: Range::default(),
            selection_range: Range::default(),
            data: serde_json::to_value(CallHierarchyData {
                file_name: "/workspace/calls.ts".to_owned(),
                declaration_start: u32::try_from(declaration_start).unwrap(),
            })
            .unwrap(),
        };

        let mut input = begin_framed_session();
        write_open(&mut input, uri.clone(), source);
        write(
            &mut input,
            &Request::new(
                40_i64,
                "textDocument/signatureHelp",
                Some(SignatureHelpParams {
                    text_document: TextDocumentIdentifier { uri: uri.clone() },
                    position: position("leaf(input)", 8),
                    context: None,
                }),
            ),
        );
        write_position_request(
            &mut input,
            41,
            "textDocument/prepareCallHierarchy",
            uri.clone(),
            position("middle(input", 1),
        );
        write(
            &mut input,
            &Request::new(
                42_i64,
                "callHierarchy/incomingCalls",
                Some(CallHierarchyCallsParams {
                    item: hierarchy_item("leaf", 0),
                }),
            ),
        );
        write(
            &mut input,
            &Request::new(
                43_i64,
                "callHierarchy/outgoingCalls",
                Some(CallHierarchyCallsParams {
                    item: hierarchy_item("top", source.find("function top").unwrap()),
                }),
            ),
        );
        write(
            &mut input,
            &Request::new(
                44_i64,
                "workspace/symbol",
                Some(WorkspaceSymbolParams {
                    query: "lea".to_owned(),
                }),
            ),
        );

        let output = finish_framed_session(input);
        let response = |id| output.iter().find(|message| message["id"] == id).unwrap();
        assert_eq!(
            response(40)["result"]["signatures"][0]["label"],
            "leaf(value: number): number"
        );
        assert_eq!(response(40)["result"]["activeParameter"], 0);
        assert_eq!(response(41)["result"][0]["name"], "middle");

        let incoming = response(42)["result"].as_array().unwrap();
        assert_eq!(incoming.len(), 2);
        assert_eq!(
            incoming
                .iter()
                .map(|call| call["from"]["name"].as_str().unwrap())
                .collect::<Vec<_>>(),
            ["middle", "top"]
        );
        let outgoing = response(43)["result"].as_array().unwrap();
        assert_eq!(outgoing.len(), 2);
        assert_eq!(
            outgoing
                .iter()
                .map(|call| call["to"]["name"].as_str().unwrap())
                .collect::<Vec<_>>(),
            ["leaf", "middle"]
        );
        assert_eq!(response(44)["result"][0]["name"], "leaf");
        assert_eq!(response(44)["result"][0]["location"]["uri"], uri.0);
    }

    #[test]
    fn framed_session_serves_semantic_folding_and_selection_ranges() {
        let uri = DocumentUri("file:///workspace/ranges.ts".to_owned());
        let source = concat!(
            "function outer(name: string) {\n",
            "  const emoji = \"😀\"; const after = emoji;\n",
            "  if (name) {\n",
            "    return after;\n",
            "  }\n",
            "}\n"
        );
        let after_offset = source.find("after").unwrap();
        let reference_offset = source.rfind("after").unwrap();
        let mut input = begin_framed_session();
        write_open(&mut input, uri.clone(), source);
        for (id, method) in [
            (50_i64, "textDocument/semanticTokens/full"),
            (51_i64, "textDocument/foldingRange"),
        ] {
            write(
                &mut input,
                &Request::new(
                    id,
                    method,
                    Some(FoldingRangeParams {
                        text_document: TextDocumentIdentifier { uri: uri.clone() },
                    }),
                ),
            );
        }
        write(
            &mut input,
            &Request::new(
                52_i64,
                "textDocument/selectionRange",
                Some(SelectionRangeParams {
                    text_document: TextDocumentIdentifier { uri: uri.clone() },
                    positions: vec![position_at(
                        source,
                        u32::try_from(reference_offset + 2).unwrap(),
                    )],
                }),
            ),
        );

        let output = finish_framed_session(input);
        let response = |id| output.iter().find(|message| message["id"] == id).unwrap();
        let data = response(50)["result"]["data"]
            .as_array()
            .unwrap()
            .iter()
            .map(|value| u32::try_from(value.as_u64().unwrap()).unwrap())
            .collect::<Vec<_>>();
        let mut line = 0;
        let mut start = 0;
        let mut tokens = Vec::new();
        for token in data.chunks_exact(5) {
            line += token[0];
            start = if token[0] == 0 {
                start + token[1]
            } else {
                token[1]
            };
            tokens.push((line, start, token[2], token[3]));
        }
        let after = position_at(source, u32::try_from(after_offset).unwrap());
        assert!(tokens.contains(&(after.line, after.character, 5, 8)));
        assert!(tokens.iter().any(|token| token.2 == 4 && token.3 == 18));

        let folds = response(51)["result"].as_array().unwrap();
        assert!(
            folds
                .iter()
                .any(|range| range["startLine"] == 0 && range["endLine"] == 5)
        );
        assert!(
            folds
                .iter()
                .any(|range| range["startLine"] == 2 && range["endLine"] == 4)
        );

        let selection = &response(52)["result"][0];
        assert_eq!(selection["range"]["start"]["line"], 3);
        assert_eq!(selection["range"]["start"]["character"], 11);
        assert!(selection["parent"]["parent"].is_object());
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn framed_session_serves_highlights_linked_editing_and_quick_fixes() {
        let dependency_uri = DocumentUri("file:///workspace/dep.ts".to_owned());
        let main_uri = DocumentUri("file:///workspace/main.tsx".to_owned());
        let source = concat!(
            "const unused = 1;\n",
            "function greet(unusedParam: string) {\n",
            "  const face = \"😀\"; return face + missing;\n",
            "}\n",
            "const icon = \"😀\"; const view = <UI.Panel>{missing}</UI.Panel>;"
        );
        let position = |offset: usize| position_at(source, u32::try_from(offset).unwrap());
        let diagnostic = |code, needle: &str, offset: usize| Diagnostic {
            range: Range {
                start: position(offset),
                end: position(offset + needle.len()),
            },
            severity: Some(1),
            code: Some(code),
            source: Some("ts-rust".to_owned()),
            message: format!("diagnostic for {needle}"),
        };
        let face_reference = source.find("return face").unwrap() + "return ".len();
        let panel = source.find("<UI.Panel>").unwrap() + 4;
        let missing = source.find("missing").unwrap();
        let unused = source.find("unused").unwrap();
        let unused_parameter = source.find("unusedParam").unwrap();

        let mut input = begin_framed_session();
        write_open(&mut input, dependency_uri, "export const missing = 1;");
        write_open(&mut input, main_uri.clone(), source);
        write_position_request(
            &mut input,
            60,
            "textDocument/documentHighlight",
            main_uri.clone(),
            position(face_reference),
        );
        write_position_request(
            &mut input,
            61,
            "textDocument/linkedEditingRange",
            main_uri.clone(),
            position(panel),
        );
        write(
            &mut input,
            &Request::new(
                62_i64,
                "textDocument/codeAction",
                Some(CodeActionParams {
                    text_document: TextDocumentIdentifier {
                        uri: main_uri.clone(),
                    },
                    range: Range::default(),
                    context: CodeActionContext {
                        diagnostics: vec![
                            diagnostic(2304, "missing", missing),
                            diagnostic(6133, "unused", unused),
                            diagnostic(6133, "unusedParam", unused_parameter),
                        ],
                    },
                }),
            ),
        );

        let output = finish_framed_session(input);
        let response = |id| output.iter().find(|message| message["id"] == id).unwrap();
        let highlights = response(60)["result"].as_array().unwrap();
        assert_eq!(highlights.len(), 2);
        assert_eq!(highlights[0]["kind"], 3);
        assert_eq!(highlights[1]["kind"], 2);

        let linked = response(61)["result"]["ranges"].as_array().unwrap();
        assert_eq!(linked.len(), 2);
        let opening = position(source.find("UI.Panel").unwrap());
        assert_eq!(linked[0]["start"]["character"], opening.character);
        assert_eq!(linked[0]["end"]["character"], opening.character + 8);

        let actions = response(62)["result"].as_array().unwrap();
        assert_eq!(actions.len(), 3);
        assert_eq!(actions[0]["title"], "Add import from './dep'");
        assert_eq!(
            actions[0]["edit"]["changes"][main_uri.0.as_str()][0]["newText"],
            "import { missing } from \"./dep\";\n"
        );
        assert_eq!(actions[1]["title"], "Remove unused declaration 'unused'");
        assert_eq!(
            actions[2]["title"],
            "Rename unused parameter to '_unusedParam'"
        );
        assert_eq!(
            actions[2]["edit"]["changes"][main_uri.0.as_str()][0]["newText"],
            "_unusedParam"
        );
    }
}
