//! Program-owned canonical binder traversal and AST side data.
//!
//! TypeScript-Go writes binder results directly onto mutable AST nodes. Rust
//! keeps the parse tree immutable, so [`BoundFile`] is the provenance-bearing
//! equivalent of those node slots. This slice freezes the traversal, container,
//! locals, and flow contracts and provides complete TypeScript-family
//! declaration dispatch. Callers can observe the traversal/declaration boundary
//! through [`BindingPhase`]. Ordinary JavaScript declarations share the same
//! dispatch. `CommonJS`, JavaScript expandos, and JSON remain separate.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use ts_ast::{
    FileId, FlowRef, ModifierList, NodeArena, NodeArenaId, NodeArenaRevision, NodeData, NodeFlags,
    NodeId, NodeRef, SyntaxKind,
};
use ts_diagnostics::{Diagnostic, message_by_code};

use crate::{
    AstScope, BoundFlowGraph, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolData,
    SymbolFlags, SymbolStore, SymbolTableId,
    flow_builder::{FlowTraversalHooks, build_flow_graph_with_hooks},
    should_replace_value_declaration,
};

/// The last completed phase of the canonical binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BindingPhase {
    /// Exact declaration-order traversal and side-data allocation are complete.
    /// Symbol declaration and merge behavior has not run yet.
    Traversal,
    /// Declaration symbols and merge diagnostics are complete.
    /// Produced by successful TypeScript or ordinary JavaScript dispatch.
    Declarations,
}

/// Why canonical bindings cannot yet be separated for checker adoption.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalExtractionError {
    /// At least one bound file has not completed declaration binding.
    DeclarationsIncomplete,
}

impl std::fmt::Display for CanonicalExtractionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DeclarationsIncomplete => {
                formatter.write_str("canonical declarations are incomplete")
            }
        }
    }
}

impl std::error::Error for CanonicalExtractionError {}

/// A structural failure that prevents canonical binding from starting.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalBindError {
    /// The requested root is absent or is not a source-file node.
    InvalidSourceFile(NodeRef),
    /// A Program file slot may be bound exactly once.
    DuplicateFile(FileId),
    /// The file/arena pair conflicts with an AST scope already owned by the
    /// Program's symbol store.
    AstScopeConflict { file: FileId, arena: NodeArenaId },
    /// An AST child reference points outside its arena snapshot.
    MissingChild { parent: NodeRef, child: NodeId },
    /// A reachable AST node occurs twice in the generated child graph. Binder
    /// state is path-dependent, so accepting a DAG here would be ambiguous.
    RepeatedNode(NodeRef),
    /// A node's generated payload cannot represent its advertised syntax kind.
    MismatchedNodeKind {
        node: NodeRef,
        kind: SyntaxKind,
        data: &'static str,
    },
    /// A reachable node's parent backlink disagrees with the generated child
    /// edge used to reach it. Source-file roots must have no parent.
    InvalidParent {
        node: NodeRef,
        expected: Option<NodeId>,
        actual: Option<NodeId>,
    },
}

impl std::fmt::Display for CanonicalBindError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSourceFile(node) => {
                write!(
                    formatter,
                    "canonical binder root {:?} is not a source file",
                    node.node
                )
            }
            Self::DuplicateFile(file) => {
                write!(
                    formatter,
                    "Program file slot {} was already bound",
                    file.index()
                )
            }
            Self::AstScopeConflict { file, .. } => write!(
                formatter,
                "Program file slot {} conflicts with a registered AST arena",
                file.index()
            ),
            Self::MissingChild { parent, child } => write!(
                formatter,
                "AST node {:?} references missing child {child:?}",
                parent.node
            ),
            Self::RepeatedNode(node) => {
                write!(
                    formatter,
                    "AST node {:?} is reachable more than once",
                    node.node
                )
            }
            Self::MismatchedNodeKind { node, kind, data } => write!(
                formatter,
                "AST node {:?} advertises {kind:?} but stores {data}",
                node.node
            ),
            Self::InvalidParent {
                node,
                expected,
                actual,
            } => write!(
                formatter,
                "AST node {:?} has parent {actual:?}, expected {expected:?}",
                node.node
            ),
        }
    }
}

impl std::error::Error for CanonicalBindError {}

/// An invariant or provenance failure rejected before declaration state is
/// changed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalDeclarationError {
    /// The declaration's file has not completed canonical traversal.
    UnboundFile(FileId),
    /// The supplied arena is not the snapshot registered for this file.
    WrongArena {
        file: FileId,
        expected: NodeArenaId,
        actual: NodeArenaId,
    },
    /// The arena changed after this file's canonical traversal completed.
    ArenaRevisionMismatch {
        file: FileId,
        expected: NodeArenaRevision,
        actual: NodeArenaRevision,
    },
    /// The declaration is not reachable from the registered source file.
    UnboundNode(NodeRef),
    /// The table belongs to another store or was never allocated.
    InvalidSymbolTable(SymbolTableId),
    /// The parent belongs to another store or was never allocated.
    InvalidParent(SemanticSymbolId),
    /// A local-symbol write references a symbol outside this store.
    InvalidLocalSymbol(SemanticSymbolId),
    /// An exported-symbol link references a symbol outside this store.
    InvalidExportSymbol(SemanticSymbolId),
    /// The supplied export is not the declaration's canonical symbol slot.
    ExportSymbolMismatch {
        node: NodeRef,
        actual: Option<SemanticSymbolId>,
        export: SemanticSymbolId,
    },
    /// A dynamic computed name must take the explicit computed-name path.
    DynamicNameRequiresComputed(NodeRef),
    /// Declaration naming depends on the not-yet-canonicalized JS file-kind
    /// fact, so the TypeScript-only primitive cannot choose a table key.
    JavaScriptFileKindRequired(NodeRef),
    /// A private declaration was reached before its containing class symbol.
    MissingContainingClassSymbol(NodeRef),
    /// Declaration dispatch requires parser/Program source-file facts.
    MissingSourceFileFacts(FileId),
    /// JavaScript/JSX and `allowJs` declaration dispatch is deferred.
    JavaScriptDeclarationsDeferred(FileId),
    /// `CommonJS` declaration dispatch is deferred.
    CommonJsDeclarationsDeferred(FileId),
    /// The dependency-closed declaration slice may run only once per file.
    DuplicateDeclarationDispatch(FileId),
    /// This declaration family is outside the currently installed exact
    /// dependency closure. The whole file is rejected before symbol writes.
    UnsupportedDeclarationFamily(NodeRef),
}

impl std::fmt::Display for CanonicalDeclarationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnboundFile(file) => write!(
                formatter,
                "Program file slot {} has not been canonically traversed",
                file.index()
            ),
            Self::WrongArena { file, .. } => write!(
                formatter,
                "declaration arena does not match Program file slot {}",
                file.index()
            ),
            Self::ArenaRevisionMismatch { file, .. } => write!(
                formatter,
                "declaration arena changed after traversal for Program file slot {}",
                file.index()
            ),
            Self::UnboundNode(node) => {
                write!(formatter, "AST node {:?} is not bound", node.node)
            }
            Self::InvalidSymbolTable(_) => formatter.write_str("invalid canonical symbol table"),
            Self::InvalidParent(_) => formatter.write_str("invalid canonical parent symbol"),
            Self::InvalidLocalSymbol(_) => formatter.write_str("invalid canonical local symbol"),
            Self::InvalidExportSymbol(_) => formatter.write_str("invalid canonical export symbol"),
            Self::ExportSymbolMismatch { node, .. } => write!(
                formatter,
                "AST node {:?} does not contain the supplied export symbol",
                node.node
            ),
            Self::DynamicNameRequiresComputed(node) => write!(
                formatter,
                "dynamic name on AST node {:?} requires the computed-name declaration path",
                node.node
            ),
            Self::JavaScriptFileKindRequired(node) => write!(
                formatter,
                "AST node {:?} requires a canonical JavaScript file-kind fact",
                node.node
            ),
            Self::MissingContainingClassSymbol(node) => write!(
                formatter,
                "private declaration {:?} has no bound containing class symbol",
                node.node
            ),
            Self::MissingSourceFileFacts(file) => write!(
                formatter,
                "Program file slot {} has no canonical source-file facts",
                file.index()
            ),
            Self::JavaScriptDeclarationsDeferred(file) => write!(
                formatter,
                "JavaScript declaration dispatch is deferred for Program file slot {}",
                file.index()
            ),
            Self::CommonJsDeclarationsDeferred(file) => write!(
                formatter,
                "CommonJS declaration dispatch is deferred for Program file slot {}",
                file.index()
            ),
            Self::DuplicateDeclarationDispatch(file) => write!(
                formatter,
                "Program file slot {} already ran canonical declaration dispatch",
                file.index()
            ),
            Self::UnsupportedDeclarationFamily(node) => write!(
                formatter,
                "AST node {:?} is outside the installed canonical declaration closure",
                node.node
            ),
        }
    }
}

impl std::error::Error for CanonicalDeclarationError {}

/// Related information attached to one canonical binder diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalRelatedInformation {
    pub node: NodeRef,
    pub diagnostic: Diagnostic,
}

/// A canonical binder diagnostic with exact related-information order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalBindDiagnostic {
    pub node: NodeRef,
    pub diagnostic: Diagnostic,
    pub related_information: Vec<CanonicalRelatedInformation>,
}

/// Parser/Program-owned source-file facts consumed by canonical declaration
/// binding.
///
/// These facts are deliberately supplied by the caller. The immutable Rust
/// AST does not retain TypeScript-Go's `SourceFile` file-kind and module slots,
/// and the binder must not reconstruct them from a file name or syntax.
/// Caller-supplied text source family. JSON is intentionally not representable
/// until its distinct pinned source-file binding path is ported.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalSourceLanguage {
    /// TypeScript-family inputs, including TS, TSX, declaration files, MTS,
    /// and CTS when the caller's module facts do not classify them as
    /// `CommonJS`.
    TypeScript,
    /// JavaScript/JSX inputs, including `allowJs` Program files.
    JavaScript,
}

/// Exact parser/Program module indicators for one source file.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalModuleState {
    Script,
    External,
    CommonJs,
    ExternalAndCommonJs,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalSourceFileFacts {
    source_file_symbol_name: EscapedName,
    language: CanonicalSourceLanguage,
    is_declaration_file: bool,
    is_default_library: bool,
    module_state: CanonicalModuleState,
}

/// One wildcard ambient-module entry recorded by declaration binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalPatternAmbientModule {
    pattern: String,
    star_index: usize,
    symbol: SemanticSymbolId,
}

/// One parser-collected module augmentation plus the ambientness of its
/// containing context used by checker module-name diagnostics.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CanonicalModuleAugmentation {
    name: NodeRef,
    in_ambient_context: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ModuleInstanceState {
    Unknown,
    NonInstantiated,
    Instantiated,
    ConstEnumOnly,
}

impl CanonicalPatternAmbientModule {
    #[must_use]
    pub fn pattern(&self) -> &str {
        &self.pattern
    }

    #[must_use]
    pub const fn star_index(&self) -> usize {
        self.star_index
    }

    #[must_use]
    pub const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }
}

impl CanonicalModuleAugmentation {
    #[must_use]
    pub const fn name(self) -> NodeRef {
        self.name
    }

    #[must_use]
    pub const fn in_ambient_context(self) -> bool {
        self.in_ambient_context
    }
}

impl CanonicalSourceFileFacts {
    #[must_use]
    pub const fn new(
        source_file_symbol_name: EscapedName,
        language: CanonicalSourceLanguage,
        is_declaration_file: bool,
        module_state: CanonicalModuleState,
    ) -> Self {
        Self::new_with_default_library(
            source_file_symbol_name,
            language,
            is_declaration_file,
            false,
            module_state,
        )
    }

    /// Retains the Program-owned default-library classification explicitly.
    ///
    /// Default-library identity cannot be reconstructed from a declaration-file
    /// bit or filename: callers must supply the exact Program fact.
    #[must_use]
    pub const fn new_with_default_library(
        source_file_symbol_name: EscapedName,
        language: CanonicalSourceLanguage,
        is_declaration_file: bool,
        is_default_library: bool,
        module_state: CanonicalModuleState,
    ) -> Self {
        Self {
            source_file_symbol_name,
            language,
            is_declaration_file,
            is_default_library,
            module_state,
        }
    }

    #[must_use]
    pub const fn source_file_symbol_name(&self) -> crate::EscapedNameRef<'_> {
        self.source_file_symbol_name.as_ref()
    }

    #[must_use]
    pub const fn is_javascript_file(&self) -> bool {
        matches!(self.language, CanonicalSourceLanguage::JavaScript)
    }

    #[must_use]
    pub const fn is_declaration_file(&self) -> bool {
        self.is_declaration_file
    }

    /// Whether the Program classified this source as one of its lib files.
    #[must_use]
    pub const fn is_default_library(&self) -> bool {
        self.is_default_library
    }

    #[must_use]
    pub const fn is_external_module(&self) -> bool {
        matches!(
            self.module_state,
            CanonicalModuleState::External | CanonicalModuleState::ExternalAndCommonJs
        )
    }

    #[must_use]
    pub const fn is_common_js_module(&self) -> bool {
        matches!(
            self.module_state,
            CanonicalModuleState::CommonJs | CanonicalModuleState::ExternalAndCommonJs
        )
    }

    #[must_use]
    pub const fn is_external_or_common_js_module(&self) -> bool {
        !matches!(self.module_state, CanonicalModuleState::Script)
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct NodeBinding {
    visited: bool,
    contains_this: bool,
    symbol: Option<SemanticSymbolId>,
    local_symbol: Option<SemanticSymbolId>,
    locals: Option<SymbolTableId>,
    container: Option<NodeId>,
    block_scope_container: Option<NodeId>,
    this_container: Option<NodeId>,
    next_container: Option<NodeId>,
}

/// Immutable-AST equivalent of TypeScript-Go's binder-populated node fields.
///
/// Every query requires the full [`NodeRef`] provenance. Dense `NodeId`s from
/// another file or arena therefore cannot alias this file's semantic slots.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoundFile {
    file: FileId,
    arena: NodeArenaId,
    arena_revision: NodeArenaRevision,
    source_file: NodeId,
    source_facts: Option<CanonicalSourceFileFacts>,
    node_count: usize,
    phase: BindingPhase,
    declaration_slice_bound: bool,
    nodes: Vec<NodeBinding>,
    traversal_order: Vec<NodeId>,
    container_chain: Vec<NodeId>,
    diagnostics: Vec<CanonicalBindDiagnostic>,
    pattern_ambient_modules: Vec<CanonicalPatternAmbientModule>,
    module_augmentations: Vec<CanonicalModuleAugmentation>,
    global_exports: Option<SymbolTableId>,
    classifiable_names: BTreeSet<EscapedName>,
    not_const_enum_only_modules: BTreeSet<SemanticSymbolId>,
    symbol_count: u32,
    flow: BoundFlowGraph,
}

impl BoundFile {
    #[must_use]
    pub const fn file_id(&self) -> FileId {
        self.file
    }

    #[must_use]
    pub const fn node_arena_id(&self) -> NodeArenaId {
        self.arena
    }

    /// The exact arena mutation revision captured after traversal.
    #[must_use]
    pub const fn node_arena_revision(&self) -> NodeArenaRevision {
        self.arena_revision
    }

    #[must_use]
    pub const fn phase(&self) -> BindingPhase {
        self.phase
    }

    #[must_use]
    pub fn declarations_complete(&self) -> bool {
        self.phase == BindingPhase::Declarations
    }

    /// Whether the complete TypeScript-family declaration dispatch ran.
    /// Rejected JavaScript, `CommonJS`, and structurally unsupported files remain
    /// in traversal phase with this bit clear.
    #[must_use]
    pub const fn declaration_slice_bound(&self) -> bool {
        self.declaration_slice_bound
    }

    #[must_use]
    pub const fn source_file(&self) -> NodeRef {
        NodeRef::new(self.arena, self.file, self.source_file)
    }

    /// Exact source facts supplied by the parser/Program host. Traversal-only
    /// callers may omit them; declaration dispatch never infers replacements.
    #[must_use]
    pub const fn source_facts(&self) -> Option<&CanonicalSourceFileFacts> {
        self.source_facts.as_ref()
    }

    /// Whether `node` was reached from this exact source-file root.
    #[must_use]
    pub fn contains(&self, node: NodeRef) -> bool {
        self.node_binding(node)
            .is_some_and(|binding| binding.visited)
    }

    /// Pinned binder-owned `NodeFlagsContainsThis` for this node.
    ///
    /// The parsed AST remains immutable, so this side fact is authoritative.
    /// `Some(false)` is a bound negative; `None` means the node provenance is
    /// invalid or the node was not reached by canonical traversal.
    #[must_use]
    pub fn contains_this(&self, node: NodeRef) -> Option<bool> {
        let binding = self.node_binding(node)?;
        binding.visited.then_some(binding.contains_this)
    }

    /// Canonical declaration symbol written by declaration binding. A focused
    /// declaration primitive may populate this while the file remains in the
    /// traversal phase; only full dispatch advances [`Self::phase`].
    #[must_use]
    pub fn symbol(&self, node: NodeRef) -> Option<SemanticSymbolId> {
        self.node_binding(node)?.symbol
    }

    /// Canonical local half of an exported declaration pair.
    #[must_use]
    pub fn local_symbol(&self, node: NodeRef) -> Option<SemanticSymbolId> {
        self.node_binding(node)?.local_symbol
    }

    /// Binder diagnostics in append order, including exact related-info order.
    #[must_use]
    pub fn diagnostics(&self) -> &[CanonicalBindDiagnostic] {
        &self.diagnostics
    }

    /// Wildcard ambient modules in declaration order.
    #[must_use]
    pub fn pattern_ambient_modules(&self) -> &[CanonicalPatternAmbientModule] {
        &self.pattern_ambient_modules
    }

    /// Parser-equivalent module augmentations in declaration order.
    ///
    /// Each entry retains the exact `ModuleDeclaration.name` node consumed by
    /// `initializeChecker` and whether its containing context was ambient.
    /// Global-scope augmentations are included. Relative nested ambient-module
    /// names are excluded exactly as in the pinned parser's
    /// `collectExternalModuleReferences` pass.
    #[must_use]
    pub fn module_augmentations(&self) -> &[CanonicalModuleAugmentation] {
        &self.module_augmentations
    }

    /// `export as namespace` aliases. Absence remains distinct from an
    /// allocated empty table.
    #[must_use]
    pub const fn global_exports(&self) -> Option<SymbolTableId> {
        self.global_exports
    }

    /// Names observed with a classifiable declaration meaning.
    #[must_use]
    pub fn classifiable_names(&self) -> impl ExactSizeIterator<Item = crate::EscapedNameRef<'_>> {
        self.classifiable_names.iter().map(EscapedName::as_ref)
    }

    /// Symbols whose const-enum-only marker was permanently cleared.
    #[must_use]
    pub fn is_not_const_enum_only_module(&self, symbol: SemanticSymbolId) -> bool {
        self.not_const_enum_only_modules.contains(&symbol)
    }

    /// Symbols allocated while binding this file, including detached and
    /// missing-name symbols.
    #[must_use]
    pub const fn symbol_count(&self) -> u32 {
        self.symbol_count
    }

    /// The node's locals table. Absence and an allocated empty table remain
    /// observably different, matching TypeScript-Go's nil-map behavior.
    #[must_use]
    pub fn locals(&self, node: NodeRef) -> Option<SymbolTableId> {
        self.node_binding(node)?.locals
    }

    /// Semantic declaration container active when `node` is entered.
    ///
    /// The source-file root has no containing container. Its direct children
    /// name the source file, and a function's children name that function.
    #[must_use]
    pub fn container(&self, node: NodeRef) -> Option<NodeRef> {
        self.node_ref(self.node_binding(node)?.container?)
    }

    /// Block-scoped declaration container active when `node` is entered.
    #[must_use]
    pub fn block_scope_container(&self, node: NodeRef) -> Option<NodeRef> {
        self.node_ref(self.node_binding(node)?.block_scope_container?)
    }

    /// `this` container active when `node` is entered.
    #[must_use]
    pub fn this_container(&self, node: NodeRef) -> Option<NodeRef> {
        self.node_ref(self.node_binding(node)?.this_container?)
    }

    /// Next entry in TypeScript-Go's declaration-order locals-container chain.
    #[must_use]
    pub fn next_container(&self, node: NodeRef) -> Option<NodeRef> {
        self.node_ref(self.node_binding(node)?.next_container?)
    }

    /// Nodes in exact binder visitation order. Source-file, block, and module-
    /// block statement lists visit function declarations first.
    #[must_use]
    pub fn traversal_order(&self) -> impl ExactSizeIterator<Item = NodeRef> + '_ {
        self.traversal_order
            .iter()
            .copied()
            .map(|node| NodeRef::new(self.arena, self.file, node))
    }

    /// Locals containers in the order used by `getLocalNameOfContainer`.
    #[must_use]
    pub fn container_chain(&self) -> impl ExactSizeIterator<Item = NodeRef> + '_ {
        self.container_chain
            .iter()
            .copied()
            .map(|node| NodeRef::new(self.arena, self.file, node))
    }

    /// The sole control-flow graph built for this canonical file.
    #[must_use]
    pub const fn flow_graph(&self) -> &BoundFlowGraph {
        &self.flow
    }

    #[must_use]
    pub fn flow_at(&self, node: NodeRef) -> Option<FlowRef> {
        self.contains(node)
            .then(|| self.flow.flow_at(node))
            .flatten()
    }

    #[must_use]
    pub fn flow_container(&self, node: NodeRef) -> Option<NodeRef> {
        self.contains(node)
            .then(|| self.flow.flow_container(node))
            .flatten()
    }

    fn node_binding(&self, node: NodeRef) -> Option<&NodeBinding> {
        (node.is_for(self.arena, self.file) && node.node.index() < self.node_count)
            .then(|| self.nodes.get(node.node.index()))
            .flatten()
    }

    fn node_binding_mut(&mut self, node: NodeRef) -> Option<&mut NodeBinding> {
        (node.is_for(self.arena, self.file) && node.node.index() < self.node_count)
            .then(|| self.nodes.get_mut(node.node.index()))
            .flatten()
    }

    fn node_ref(&self, node: NodeId) -> Option<NodeRef> {
        (node.index() < self.node_count).then(|| NodeRef::new(self.arena, self.file, node))
    }
}

/// Completed canonical traversal for all files plus the sole pre-checker
/// symbol owner.
///
/// Consume this value and pass the returned [`SymbolStore`] to
/// `SemanticStore::from_symbol_store` only after all Program files have been
/// declaration-bound.
#[derive(Debug)]
pub struct CanonicalProgramBindings {
    symbols: SymbolStore,
    files: BTreeMap<FileId, BoundFile>,
}

impl CanonicalProgramBindings {
    #[must_use]
    pub const fn symbol_store(&self) -> &SymbolStore {
        &self.symbols
    }

    #[must_use]
    pub fn file(&self, file: FileId) -> Option<&BoundFile> {
        self.files.get(&file)
    }

    #[must_use]
    pub fn files(&self) -> impl ExactSizeIterator<Item = &BoundFile> {
        self.files.values()
    }

    #[must_use]
    pub fn declarations_complete(&self) -> bool {
        self.files.values().all(BoundFile::declarations_complete)
    }

    /// Separates immutable AST side data from the symbol owner consumed by the
    /// checker, but only once declaration binding is complete.
    ///
    /// On failure, the traversal-only symbol owner is not exposed as a checker
    /// store.
    ///
    /// # Errors
    ///
    /// Returns [`CanonicalExtractionError::DeclarationsIncomplete`] while any
    /// file remains in the traversal-only phase.
    pub fn try_into_parts(
        self,
    ) -> Result<(SymbolStore, BTreeMap<FileId, BoundFile>), CanonicalExtractionError> {
        if self.declarations_complete() {
            Ok((self.symbols, self.files))
        } else {
            Err(CanonicalExtractionError::DeclarationsIncomplete)
        }
    }
}

/// Owns the one canonical symbol store while Program files are bound.
///
/// There is intentionally no mutable `SymbolStore` escape hatch. Declaration
/// operations validate identities through this owner before changing state.
#[derive(Clone, Debug)]
struct DeclarationFacts {
    kind: SyntaxKind,
    diagnostic_node: NodeRef,
    display_name: String,
}

struct PreparedDeclaration {
    name: EscapedName,
    facts: DeclarationFacts,
    is_default_export: bool,
    is_export_assignment_default: bool,
    export_type_suggestion: Option<CanonicalRelatedInformation>,
}

#[derive(Clone, Copy, Debug)]
struct ExpandoAssignmentInfo {
    node: NodeId,
    container: Option<NodeId>,
    block_scope_container: Option<NodeId>,
    this_container: Option<NodeId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum JavaScriptAssignmentKind {
    ModuleExports,
    ExportsProperty,
    ExpandoProperty,
    ThisProperty,
}

#[derive(Debug, Default)]
pub struct CanonicalBinder {
    symbols: SymbolStore,
    files: BTreeMap<FileId, BoundFile>,
    declaration_facts: HashMap<NodeRef, DeclarationFacts>,
}

impl CanonicalBinder {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub const fn symbol_store(&self) -> &SymbolStore {
        &self.symbols
    }

    #[must_use]
    pub fn file(&self, file: FileId) -> Option<&BoundFile> {
        self.files.get(&file)
    }

    /// Allocates one observable empty symbol table without exposing mutable
    /// access to the Program's symbol store.
    #[must_use]
    pub fn create_symbol_table(&mut self) -> SymbolTableId {
        self.symbols.alloc_symbol_table()
    }

    /// Pinned `declareSymbol`: derives the declaration name, then performs the
    /// exact table insert/merge/conflict operation.
    ///
    /// # Errors
    ///
    /// Foreign arenas, nodes, tables, and parent symbols are rejected before
    /// any declaration state changes.
    ///
    /// # Panics
    ///
    /// Like the pinned binder, a parent mismatch is checked after
    /// `addDeclarationToSymbol` and therefore panics after those mutations.
    #[allow(clippy::too_many_arguments)]
    pub fn declare_symbol(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        symbol_table: SymbolTableId,
        parent: Option<SemanticSymbolId>,
        node: NodeId,
        includes: SymbolFlags,
        excludes: SymbolFlags,
    ) -> Result<SemanticSymbolId, CanonicalDeclarationError> {
        self.declare_symbol_ex(
            arena,
            file,
            symbol_table,
            parent,
            node,
            includes,
            excludes,
            false,
            false,
        )
    }

    /// Pinned `declareSymbolEx`, including replaceable-property and explicit
    /// computed-name behavior.
    ///
    /// # Errors
    ///
    /// Foreign arenas, nodes, tables, and parent symbols are rejected before
    /// any declaration state changes. A dynamic computed name must use
    /// `is_computed_name`.
    ///
    /// # Panics
    ///
    /// Like the pinned binder, a parent mismatch is checked after
    /// `addDeclarationToSymbol` and therefore panics after those mutations.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn declare_symbol_ex(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        symbol_table: SymbolTableId,
        parent: Option<SemanticSymbolId>,
        node: NodeId,
        includes: SymbolFlags,
        excludes: SymbolFlags,
        is_replaceable_by_method: bool,
        is_computed_name: bool,
    ) -> Result<SemanticSymbolId, CanonicalDeclarationError> {
        self.declare_symbol_ex_worker(
            arena,
            file,
            symbol_table,
            parent,
            node,
            includes,
            excludes,
            is_replaceable_by_method,
            is_computed_name,
            false,
        )
    }

    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn declare_symbol_ex_worker(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        symbol_table: SymbolTableId,
        parent: Option<SemanticSymbolId>,
        node: NodeId,
        includes: SymbolFlags,
        excludes: SymbolFlags,
        is_replaceable_by_method: bool,
        is_computed_name: bool,
        has_known_typescript_file_kind: bool,
    ) -> Result<SemanticSymbolId, CanonicalDeclarationError> {
        let node_ref = self.preflight_declaration(arena, file, symbol_table, parent, node)?;
        let prepared = self.prepare_declaration(
            arena,
            node_ref,
            parent,
            is_computed_name,
            has_known_typescript_file_kind,
        )?;
        let is_missing = prepared.name.as_ref() == InternalSymbolName::Missing.as_ref();

        let symbol = if is_missing {
            self.new_symbol(file, prepared.name.clone())
        } else {
            if includes.intersects(SymbolFlags::CLASSIFIABLE) {
                self.files
                    .get_mut(&file)
                    .expect("declaration file was preflighted")
                    .classifiable_names
                    .insert(prepared.name.clone());
            }

            let existing = self
                .symbols
                .symbol_table(symbol_table)
                .expect("declaration table was preflighted")
                .get(prepared.name.as_ref());
            match existing {
                None => {
                    let symbol = self.new_symbol(file, prepared.name.clone());
                    let replaced = self
                        .symbols
                        .insert_symbol(symbol_table, prepared.name.clone(), symbol)
                        .expect("declaration table and symbol were preflighted");
                    assert_eq!(
                        replaced, None,
                        "new declaration must not replace a table entry"
                    );
                    if is_replaceable_by_method {
                        self.or_symbol_flags(symbol, SymbolFlags::REPLACEABLE_BY_METHOD);
                    }
                    symbol
                }
                Some(existing)
                    if is_replaceable_by_method
                        && !self
                            .symbols
                            .symbol(existing)
                            .expect("table entries are store-owned")
                            .flags()
                            .intersects(SymbolFlags::REPLACEABLE_BY_METHOD) =>
                {
                    // Pinned early return: no node symbol, declaration, parent,
                    // or value-declaration write.
                    return Ok(existing);
                }
                Some(existing) => {
                    let existing_flags = self
                        .symbols
                        .symbol(existing)
                        .expect("table entries are store-owned")
                        .flags();
                    if !existing_flags.intersects(excludes) {
                        existing
                    } else if existing_flags.intersects(SymbolFlags::REPLACEABLE_BY_METHOD) {
                        let replacement = self.new_symbol(file, prepared.name.clone());
                        assert_eq!(
                            self.symbols.insert_symbol(
                                symbol_table,
                                prepared.name.clone(),
                                replacement,
                            ),
                            Some(Some(existing)),
                            "only replaceable-by-method displacement replaces a table entry",
                        );
                        replacement
                    } else if assignment_variable_merge(includes, existing_flags) {
                        existing
                    } else {
                        self.report_declaration_conflict(
                            file, arena, existing, node_ref, includes, &prepared,
                        );
                        let existing_accessor = existing_flags & SymbolFlags::ACCESSOR;
                        let incoming_accessor = includes & SymbolFlags::ACCESSOR;
                        if existing_accessor != SymbolFlags::NONE
                            && existing_accessor != incoming_accessor
                        {
                            self.or_symbol_flags(existing, SymbolFlags::ACCESSOR);
                        }
                        // Ordinary conflicts are detached: the table keeps the
                        // first symbol and the current node receives a fresh one.
                        self.new_symbol(file, prepared.name.clone())
                    }
                }
            }
        };

        self.add_declaration_to_symbol(symbol, node_ref, includes, prepared.facts);

        let record = self
            .symbols
            .symbol(symbol)
            .expect("declared symbol is store-owned");
        if record.parent().is_none() {
            let (members, exports, export_symbol) =
                (record.members(), record.exports(), record.export_symbol());
            assert!(self.symbols.set_symbol_relationships(
                symbol,
                members,
                exports,
                parent,
                export_symbol,
            ));
        } else if record.parent() != parent {
            panic!("Existing symbol parent should match new one");
        }
        Ok(symbol)
    }

    /// Links the two symbols created for an exported declaration and writes
    /// the dedicated AST `LocalSymbol` side slot.
    ///
    /// # Errors
    ///
    /// Returns [`CanonicalDeclarationError`] if the node or either symbol has
    /// foreign or otherwise invalid provenance.
    ///
    /// # Panics
    ///
    /// Panics only if store ownership changes after the complete provenance
    /// preflight, which would violate `CanonicalBinder`'s sealed ownership.
    pub fn link_exported_declaration(
        &mut self,
        node: NodeRef,
        local: SemanticSymbolId,
        export: SemanticSymbolId,
    ) -> Result<(), CanonicalDeclarationError> {
        if !self.symbols.contains_symbol(local) {
            return Err(CanonicalDeclarationError::InvalidLocalSymbol(local));
        }
        if !self.symbols.contains_symbol(export) {
            return Err(CanonicalDeclarationError::InvalidExportSymbol(export));
        }
        let Some(file) = self.files.get_mut(&node.file) else {
            return Err(CanonicalDeclarationError::UnboundFile(node.file));
        };
        let Some(binding) = file
            .node_binding_mut(node)
            .filter(|binding| binding.visited)
        else {
            return Err(CanonicalDeclarationError::UnboundNode(node));
        };
        if binding.symbol != Some(export) {
            return Err(CanonicalDeclarationError::ExportSymbolMismatch {
                node,
                actual: binding.symbol,
                export,
            });
        }
        let local_record = self
            .symbols
            .symbol(local)
            .expect("local symbol was preflighted");
        let (members, exports, parent) = (
            local_record.members(),
            local_record.exports(),
            local_record.parent(),
        );
        assert!(self.symbols.set_symbol_relationships(
            local,
            members,
            exports,
            parent,
            Some(export),
        ));
        binding.local_symbol = Some(local);
        Ok(())
    }

    /// Runs complete TypeScript-family declaration dispatch over the captured
    /// visitation order and container state.
    ///
    /// This is a linear replay of declaration entry points, not a second AST
    /// traversal. Locals, members, and exports remain nil until the exact
    /// declaration route first requests their table.
    ///
    /// # Errors
    ///
    /// Missing/foreign source facts, JavaScript/CommonJS files, duplicate
    /// dispatch, and declaration-provenance failures are rejected.
    ///
    /// # Panics
    ///
    /// Panics if preflighted captured binder state disappears during the
    /// sealed dispatch, or on the pinned declaration-parent mismatch path.
    pub fn bind_typescript_declaration_slice(
        &mut self,
        arena: &NodeArena,
        file: FileId,
    ) -> Result<&BoundFile, CanonicalDeclarationError> {
        self.bind_declaration_slice(arena, file, false)
    }

    /// Binds ordinary JavaScript script and ES-module declarations.
    ///
    /// Functions, variables, classes, imports, exports, `CommonJS` assignments,
    /// expandos, constructor properties, and synthetic `JSDoc` aliases follow
    /// the pinned JavaScript binder rules.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid source provenance, duplicate dispatch,
    /// unsupported JavaScript declaration families.
    ///
    /// # Panics
    ///
    /// Panics if preflighted captured binder state disappears during dispatch.
    pub fn bind_javascript_declaration_slice(
        &mut self,
        arena: &NodeArena,
        file: FileId,
    ) -> Result<&BoundFile, CanonicalDeclarationError> {
        self.bind_declaration_slice(arena, file, true)
    }

    #[allow(clippy::too_many_lines)] // Preserve upstream preflight and declaration order.
    fn bind_declaration_slice(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        allow_javascript: bool,
    ) -> Result<&BoundFile, CanonicalDeclarationError> {
        let Some(bound) = self.files.get(&file) else {
            return Err(CanonicalDeclarationError::UnboundFile(file));
        };
        if bound.arena != arena.id() {
            return Err(CanonicalDeclarationError::WrongArena {
                file,
                expected: bound.arena,
                actual: arena.id(),
            });
        }
        if bound.arena_revision != arena.revision() {
            return Err(CanonicalDeclarationError::ArenaRevisionMismatch {
                file,
                expected: bound.arena_revision,
                actual: arena.revision(),
            });
        }
        if bound.declaration_slice_bound {
            return Err(CanonicalDeclarationError::DuplicateDeclarationDispatch(
                file,
            ));
        }
        let Some(mut facts) = bound.source_facts.clone() else {
            return Err(CanonicalDeclarationError::MissingSourceFileFacts(file));
        };
        if facts.is_javascript_file() && !allow_javascript {
            return Err(CanonicalDeclarationError::JavaScriptDeclarationsDeferred(
                file,
            ));
        }
        if facts.is_common_js_module() && (!allow_javascript || !facts.is_javascript_file()) {
            return Err(CanonicalDeclarationError::CommonJsDeclarationsDeferred(
                file,
            ));
        }
        let order = bound.traversal_order.clone();
        if let Some(node) = order.iter().copied().find(|node| {
            !declaration_family_supported(arena, *node, &facts)
                || declaration_name_shape_unsupported(arena, *node)
                || (facts.is_javascript_file()
                    && assignment_name_requires_javascript_file_kind(arena, *node)
                    && javascript_assignment_kind(arena, *node).is_none())
        }) {
            return Err(CanonicalDeclarationError::UnsupportedDeclarationFamily(
                NodeRef::new(arena.id(), file, node),
            ));
        }
        if facts.is_javascript_file()
            && !facts.is_external_or_common_js_module()
            && order.iter().copied().any(|node| {
                matches!(
                    javascript_assignment_kind(arena, node),
                    Some(
                        JavaScriptAssignmentKind::ModuleExports
                            | JavaScriptAssignmentKind::ExportsProperty
                    )
                ) || is_javascript_require_call(arena, node)
            })
        {
            facts.module_state = CanonicalModuleState::CommonJs;
            self.files
                .get_mut(&file)
                .expect("declaration-dispatch file remains registered")
                .source_facts = Some(facts.clone());
        }
        // TypeScript-Go records these while traversing, including the exact
        // scope pair active at the assignment. The immutable Rust traversal
        // already captured that state, so build the same ordered queue before
        // any declaration writes and replay it only after ordinary binding.
        let expando_assignments = order
            .iter()
            .copied()
            .filter(|node| {
                if facts.is_javascript_file() {
                    javascript_assignment_kind(arena, *node)
                        == Some(JavaScriptAssignmentKind::ExpandoProperty)
                } else {
                    is_typescript_expando_property_assignment(arena, *node)
                }
            })
            .map(|node| {
                let binding = self
                    .files
                    .get(&file)
                    .and_then(|bound| bound.nodes.get(node.index()))
                    .expect("expando assignment was captured by traversal");
                ExpandoAssignmentInfo {
                    node,
                    container: binding.container,
                    block_scope_container: binding.block_scope_container,
                    this_container: binding.this_container,
                }
            })
            .collect::<Vec<_>>();
        let module_states = order
            .iter()
            .copied()
            .filter(|node| {
                arena
                    .get(*node)
                    .is_some_and(|node| node.kind == SyntaxKind::ModuleDeclaration)
            })
            .map(|node| (node, get_module_instance_state(arena, node)))
            .collect::<HashMap<_, _>>();
        for node in order.iter().copied() {
            if facts.is_javascript_file()
                && arena
                    .get(node)
                    .is_some_and(|node| node.kind == SyntaxKind::JsTypeAliasDeclaration)
                && self
                    .files
                    .get(&file)
                    .and_then(|bound| bound.nodes.get(node.index()))
                    .and_then(|binding| binding.block_scope_container)
                    .is_some_and(|container| {
                        arena
                            .get(container)
                            .is_some_and(|container| container.kind == SyntaxKind::SourceFile)
                    })
            {
                continue;
            }
            self.bind_declaration_node(arena, file, node, &facts, &module_states)?;
        }
        if facts.is_javascript_file() {
            for node in order.iter().copied().filter(|node| {
                arena
                    .get(*node)
                    .is_some_and(|node| node.kind == SyntaxKind::JsTypeAliasDeclaration)
                    && arena
                        .get(*node)
                        .and_then(|node| node.parent)
                        .is_some_and(|parent| {
                            arena
                                .get(parent)
                                .is_some_and(|parent| parent.kind == SyntaxKind::SourceFile)
                        })
            }) {
                self.bind_block_scoped_declaration(
                    arena,
                    file,
                    node,
                    SymbolFlags::TYPE_ALIAS,
                    SymbolFlags::TYPE_ALIAS_EXCLUDES,
                    &facts,
                )?;
            }
        }
        if facts.is_common_js_module() {
            self.declare_commonjs_variable(arena, file, "module");
            self.declare_commonjs_variable(arena, file, "exports");
            self.bind_commonjs_type_exports(file);
        }
        self.bind_deferred_expando_assignments(arena, file, &expando_assignments);
        let bound = self
            .files
            .get_mut(&file)
            .expect("declaration-dispatch file remains registered");
        bound.declaration_slice_bound = true;
        bound.phase = BindingPhase::Declarations;
        Ok(self
            .files
            .get(&file)
            .expect("declaration-dispatch file remains registered"))
    }

    fn ensure_node_locals(&mut self, file: FileId, node: NodeId) -> SymbolTableId {
        let bound = self
            .files
            .get_mut(&file)
            .expect("declaration-dispatch file is registered");
        let binding = &mut bound.nodes[node.index()];
        if let Some(locals) = binding.locals {
            return locals;
        }
        let locals = self.symbols.alloc_symbol_table();
        binding.locals = Some(locals);
        locals
    }

    fn declare_commonjs_variable(&mut self, arena: &NodeArena, file: FileId, name: &str) {
        let source = self
            .files
            .get(&file)
            .expect("CommonJS file is registered")
            .source_file;
        let locals = self.ensure_node_locals(file, source);
        if self
            .symbols
            .symbol_table(locals)
            .expect("CommonJS locals belong to this store")
            .get_source(name)
            .is_some()
        {
            return;
        }

        let source_ref = NodeRef::new(arena.id(), file, source);
        let escaped_name = EscapedName::source(name);
        let symbol = self.new_symbol(file, escaped_name.clone());
        self.or_symbol_flags(
            symbol,
            SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::MODULE_EXPORTS,
        );
        assert!(self.symbols.set_symbol_declarations(
            symbol,
            Some(vec![source_ref]),
            Some(source_ref),
        ));

        if name == "module" {
            let exports_name = EscapedName::source("exports");
            let exports = self.new_symbol(file, exports_name.clone());
            self.or_symbol_flags(exports, SymbolFlags::MODULE_EXPORTS | SymbolFlags::PROPERTY);
            assert!(self.symbols.set_symbol_declarations(
                exports,
                Some(vec![source_ref]),
                Some(source_ref),
            ));
            assert!(
                self.symbols
                    .set_symbol_relationships(exports, None, None, Some(symbol), None,)
            );
            let members = self.ensure_symbol_members(symbol);
            assert_eq!(
                self.symbols.insert_symbol(members, exports_name, exports),
                Some(None)
            );
        }

        assert_eq!(
            self.symbols.insert_symbol(locals, escaped_name, symbol),
            Some(None)
        );
    }

    fn bind_commonjs_type_exports(&mut self, file: FileId) {
        let Some(source) = self
            .files
            .get(&file)
            .and_then(|bound| bound.symbol(bound.source_file()))
        else {
            return;
        };
        let Some(exports) = self
            .symbols
            .symbol(source)
            .and_then(crate::semantic::Symbol::exports)
        else {
            return;
        };
        let Some(export_equals) = self
            .symbols
            .symbol_table(exports)
            .and_then(|exports| exports.get(InternalSymbolName::ExportEquals.as_ref()))
        else {
            return;
        };
        let promoted = self
            .symbols
            .symbol_table(exports)
            .expect("CommonJS exports belong to this store")
            .iter()
            .filter(|(name, symbol)| {
                *name != InternalSymbolName::ExportEquals.as_ref()
                    && self.symbols.symbol(*symbol).is_some_and(|record| {
                        record
                            .flags()
                            .intersects(SymbolFlags::TYPE | SymbolFlags::NAMESPACE)
                    })
            })
            .map(|(name, symbol)| (name.to_owned(), symbol))
            .collect::<Vec<_>>();
        if promoted.is_empty() {
            return;
        }
        let target = self.ensure_symbol_exports(export_equals);
        for (name, symbol) in promoted {
            self.symbols
                .insert_symbol(target, name, symbol)
                .expect("promoted CommonJS type export belongs to this store");
        }
        self.or_symbol_flags(export_equals, SymbolFlags::NAMESPACE_MODULE);
    }

    fn ensure_symbol_members(&mut self, symbol: SemanticSymbolId) -> SymbolTableId {
        let record = self
            .symbols
            .symbol(symbol)
            .expect("declaration container symbol is store-owned");
        if let Some(members) = record.members() {
            return members;
        }
        let (exports, parent, export_symbol) =
            (record.exports(), record.parent(), record.export_symbol());
        let members = self.symbols.alloc_symbol_table();
        assert!(self.symbols.set_symbol_relationships(
            symbol,
            Some(members),
            exports,
            parent,
            export_symbol,
        ));
        members
    }

    fn ensure_symbol_exports(&mut self, symbol: SemanticSymbolId) -> SymbolTableId {
        let record = self
            .symbols
            .symbol(symbol)
            .expect("declaration container symbol is store-owned");
        if let Some(exports) = record.exports() {
            return exports;
        }
        let (members, parent, export_symbol) =
            (record.members(), record.parent(), record.export_symbol());
        let exports = self.symbols.alloc_symbol_table();
        assert!(self.symbols.set_symbol_relationships(
            symbol,
            members,
            Some(exports),
            parent,
            export_symbol,
        ));
        exports
    }

    fn ensure_file_global_exports(&mut self, file: FileId) -> SymbolTableId {
        if let Some(exports) = self
            .files
            .get(&file)
            .expect("declaration-dispatch file is registered")
            .global_exports
        {
            return exports;
        }
        let exports = self.symbols.alloc_symbol_table();
        self.files
            .get_mut(&file)
            .expect("declaration-dispatch file is registered")
            .global_exports = Some(exports);
        exports
    }

    fn declaration_container(&self, file: FileId, node: NodeId) -> Option<NodeId> {
        self.files.get(&file)?.nodes.get(node.index())?.container
    }

    fn bound_node_symbol(&self, file: FileId, node: NodeId) -> Option<SemanticSymbolId> {
        self.files.get(&file)?.nodes.get(node.index())?.symbol
    }

    fn declare_symbol_and_add_to_symbol_table(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        includes: SymbolFlags,
        excludes: SymbolFlags,
        facts: &CanonicalSourceFileFacts,
    ) -> Result<SemanticSymbolId, CanonicalDeclarationError> {
        let container = self
            .declaration_container(file, node)
            .expect("ordinary declarations have a captured container");
        let container_kind = arena
            .get(container)
            .expect("captured containers are reachable")
            .kind;
        match container_kind {
            SyntaxKind::ModuleDeclaration => {
                self.declare_module_member(arena, file, node, includes, excludes, facts)
            }
            SyntaxKind::SourceFile => {
                self.declare_source_file_member(arena, file, node, includes, excludes, facts)
            }
            SyntaxKind::ClassExpression | SyntaxKind::ClassDeclaration => {
                let parent = self
                    .bound_node_symbol(file, container)
                    .expect("class declaration precedes its members");
                let table = if is_static_declaration(arena, node) {
                    self.ensure_symbol_exports(parent)
                } else {
                    self.ensure_symbol_members(parent)
                };
                self.declare_symbol(arena, file, table, Some(parent), node, includes, excludes)
            }
            SyntaxKind::EnumDeclaration => {
                let parent = self
                    .bound_node_symbol(file, container)
                    .expect("enum declaration precedes its members");
                let table = self.ensure_symbol_exports(parent);
                self.declare_symbol(arena, file, table, Some(parent), node, includes, excludes)
            }
            SyntaxKind::TypeLiteral
            | SyntaxKind::ObjectLiteralExpression
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::JsxAttributes => {
                let parent = self
                    .bound_node_symbol(file, container)
                    .expect("member container declaration precedes its members");
                let table = self.ensure_symbol_members(parent);
                self.declare_symbol(arena, file, table, Some(parent), node, includes, excludes)
            }
            SyntaxKind::FunctionType
            | SyntaxKind::ConstructorType
            | SyntaxKind::CallSignature
            | SyntaxKind::ConstructSignature
            | SyntaxKind::IndexSignature
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::MethodSignature
            | SyntaxKind::Constructor
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::FunctionDeclaration
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ArrowFunction
            | SyntaxKind::ClassStaticBlockDeclaration
            | SyntaxKind::TypeAliasDeclaration
            | SyntaxKind::JsTypeAliasDeclaration
            | SyntaxKind::MappedType => {
                let table = self.ensure_node_locals(file, container);
                self.declare_symbol(arena, file, table, None, node, includes, excludes)
            }
            _ => panic!("unhandled canonical declaration container {container_kind:?}"),
        }
    }

    fn declare_source_file_member(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        includes: SymbolFlags,
        excludes: SymbolFlags,
        facts: &CanonicalSourceFileFacts,
    ) -> Result<SemanticSymbolId, CanonicalDeclarationError> {
        if facts.is_external_module()
            || is_implicitly_exported_jsdoc_declaration(arena, node, facts)
        {
            self.declare_module_member(arena, file, node, includes, excludes, facts)
        } else {
            let source_file = self
                .files
                .get(&file)
                .expect("declaration file is registered")
                .source_file;
            let table = self.ensure_node_locals(file, source_file);
            self.declare_symbol(arena, file, table, None, node, includes, excludes)
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn declare_module_member(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        includes: SymbolFlags,
        excludes: SymbolFlags,
        facts: &CanonicalSourceFileFacts,
    ) -> Result<SemanticSymbolId, CanonicalDeclarationError> {
        let container = self
            .declaration_container(file, node)
            .expect("module members have a captured container");
        let parent = self
            .bound_node_symbol(file, container)
            .expect("module/source declaration precedes its members");
        let has_export_modifier = has_combined_modifier(arena, node, SyntaxKind::ExportKeyword)
            || is_implicitly_exported_jsdoc_declaration(arena, node, facts);
        if includes.intersects(SymbolFlags::ALIAS) {
            if arena
                .get(node)
                .is_some_and(|node| node.kind == SyntaxKind::ExportSpecifier)
                || (arena
                    .get(node)
                    .is_some_and(|node| node.kind == SyntaxKind::ImportEqualsDeclaration)
                    && has_export_modifier)
            {
                let table = self.ensure_symbol_exports(parent);
                return self.declare_symbol(
                    arena,
                    file,
                    table,
                    Some(parent),
                    node,
                    includes,
                    excludes,
                );
            }
            let table = self.ensure_node_locals(file, container);
            return self.declare_symbol(arena, file, table, None, node, includes, excludes);
        }

        let implicitly_exported =
            has_export_modifier || container_has_export_context(arena, container, facts);
        if !is_ambient_module(arena, node) && implicitly_exported {
            let unnamed_default = has_syntactic_modifier(arena, node, SyntaxKind::DefaultKeyword)
                && get_name_of_declaration(arena, node).is_none();
            if !container_flags(arena, container).contains(ContainerFlags::HAS_LOCALS)
                || unnamed_default
            {
                let table = self.ensure_symbol_exports(parent);
                return self.declare_symbol(
                    arena,
                    file,
                    table,
                    Some(parent),
                    node,
                    includes,
                    excludes,
                );
            }
            let local_table = self.ensure_node_locals(file, container);
            let local_flags = if includes.intersects(SymbolFlags::VALUE) {
                SymbolFlags::EXPORT_VALUE
            } else {
                SymbolFlags::NONE
            };
            let local =
                self.declare_symbol(arena, file, local_table, None, node, local_flags, excludes)?;
            let export_table = self.ensure_symbol_exports(parent);
            let export = self.declare_symbol(
                arena,
                file,
                export_table,
                Some(parent),
                node,
                includes,
                excludes,
            )?;
            self.link_exported_declaration(NodeRef::new(arena.id(), file, node), local, export)?;
            return Ok(local);
        }
        let table = self.ensure_node_locals(file, container);
        self.declare_symbol(arena, file, table, None, node, includes, excludes)
    }

    fn bind_block_scoped_declaration(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        includes: SymbolFlags,
        excludes: SymbolFlags,
        facts: &CanonicalSourceFileFacts,
    ) -> Result<SemanticSymbolId, CanonicalDeclarationError> {
        let block_container = self
            .files
            .get(&file)
            .and_then(|file| file.nodes.get(node.index()))
            .and_then(|binding| binding.block_scope_container)
            .expect("block-scoped declarations have a captured block container");
        match arena
            .get(block_container)
            .expect("captured block container is reachable")
            .kind
        {
            SyntaxKind::ModuleDeclaration => {
                self.declare_module_member(arena, file, node, includes, excludes, facts)
            }
            SyntaxKind::SourceFile if facts.is_external_or_common_js_module() => {
                self.declare_module_member(arena, file, node, includes, excludes, facts)
            }
            _ => {
                let table = self.ensure_node_locals(file, block_container);
                self.declare_symbol(arena, file, table, None, node, includes, excludes)
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn bind_declaration_node(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        facts: &CanonicalSourceFileFacts,
        module_states: &HashMap<NodeId, ModuleInstanceState>,
    ) -> Result<(), CanonicalDeclarationError> {
        let kind = arena
            .get(node)
            .expect("declaration dispatch uses captured reachable nodes")
            .kind;
        match kind {
            SyntaxKind::SourceFile if facts.is_external_or_common_js_module() => {
                self.bind_anonymous_declaration(
                    arena,
                    file,
                    node,
                    SymbolFlags::VALUE_MODULE,
                    facts.source_file_symbol_name.clone(),
                );
            }
            SyntaxKind::TypeParameter => self.bind_type_parameter(arena, file, node, facts)?,
            SyntaxKind::Parameter => self.bind_parameter(arena, file, node, facts)?,
            SyntaxKind::VariableDeclaration | SyntaxKind::BindingElement => {
                self.bind_variable_declaration_or_binding_element(arena, file, node, facts)?;
            }
            SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature => {
                let is_accessor = has_syntactic_modifier(arena, node, SyntaxKind::AccessorKeyword);
                let includes = if is_accessor {
                    SymbolFlags::ACCESSOR
                } else {
                    SymbolFlags::PROPERTY
                } | optional_symbol_flag(arena, node);
                let excludes = if is_accessor {
                    SymbolFlags::ACCESSOR_EXCLUDES
                } else {
                    SymbolFlags::PROPERTY_EXCLUDES
                };
                self.bind_property_or_method_or_accessor(
                    arena, file, node, includes, excludes, facts,
                )?;
            }
            SyntaxKind::PropertyAssignment | SyntaxKind::ShorthandPropertyAssignment => {
                self.bind_property_or_method_or_accessor(
                    arena,
                    file,
                    node,
                    SymbolFlags::PROPERTY,
                    SymbolFlags::PROPERTY_EXCLUDES,
                    facts,
                )?;
            }
            SyntaxKind::EnumMember => {
                self.bind_property_or_method_or_accessor(
                    arena,
                    file,
                    node,
                    SymbolFlags::ENUM_MEMBER,
                    SymbolFlags::ENUM_MEMBER_EXCLUDES,
                    facts,
                )?;
            }
            SyntaxKind::CallSignature
            | SyntaxKind::ConstructSignature
            | SyntaxKind::IndexSignature => {
                self.declare_symbol_and_add_to_symbol_table(
                    arena,
                    file,
                    node,
                    SymbolFlags::SIGNATURE,
                    SymbolFlags::NONE,
                    facts,
                )?;
            }
            SyntaxKind::MethodDeclaration | SyntaxKind::MethodSignature => {
                let excludes = if arena
                    .get(node)
                    .and_then(|node| node.parent)
                    .and_then(|parent| arena.get(parent))
                    .is_some_and(|parent| parent.kind == SyntaxKind::ObjectLiteralExpression)
                {
                    SymbolFlags::VALUE
                } else {
                    SymbolFlags::METHOD_EXCLUDES
                };
                self.bind_property_or_method_or_accessor(
                    arena,
                    file,
                    node,
                    SymbolFlags::METHOD | optional_symbol_flag(arena, node),
                    excludes,
                    facts,
                )?;
            }
            SyntaxKind::FunctionDeclaration => {
                self.bind_block_scoped_declaration(
                    arena,
                    file,
                    node,
                    SymbolFlags::FUNCTION,
                    SymbolFlags::FUNCTION_EXCLUDES,
                    facts,
                )?;
            }
            SyntaxKind::Constructor => {
                self.declare_symbol_and_add_to_symbol_table(
                    arena,
                    file,
                    node,
                    SymbolFlags::CONSTRUCTOR,
                    SymbolFlags::NONE,
                    facts,
                )?;
            }
            SyntaxKind::GetAccessor => {
                self.bind_property_or_method_or_accessor(
                    arena,
                    file,
                    node,
                    SymbolFlags::GET_ACCESSOR,
                    SymbolFlags::GET_ACCESSOR_EXCLUDES,
                    facts,
                )?;
            }
            SyntaxKind::SetAccessor => {
                self.bind_property_or_method_or_accessor(
                    arena,
                    file,
                    node,
                    SymbolFlags::SET_ACCESSOR,
                    SymbolFlags::SET_ACCESSOR_EXCLUDES,
                    facts,
                )?;
            }
            SyntaxKind::FunctionType | SyntaxKind::ConstructorType => {
                self.bind_function_or_constructor_type(arena, file, node)?;
            }
            SyntaxKind::TypeLiteral | SyntaxKind::MappedType => {
                self.bind_anonymous_declaration(
                    arena,
                    file,
                    node,
                    SymbolFlags::TYPE_LITERAL,
                    EscapedName::internal(InternalSymbolName::Type),
                );
            }
            SyntaxKind::ObjectLiteralExpression => {
                self.bind_anonymous_declaration(
                    arena,
                    file,
                    node,
                    SymbolFlags::OBJECT_LITERAL,
                    EscapedName::internal(InternalSymbolName::Object),
                );
            }
            SyntaxKind::FunctionExpression | SyntaxKind::ArrowFunction => {
                let name = match &arena
                    .get(node)
                    .expect("function expression is reachable")
                    .data
                {
                    NodeData::FunctionExpression(function) => function
                        .name
                        .and_then(|name| node_text(arena, name))
                        .map_or_else(
                            || EscapedName::internal(InternalSymbolName::Function),
                            EscapedName::source,
                        ),
                    _ => EscapedName::internal(InternalSymbolName::Function),
                };
                self.bind_anonymous_declaration(arena, file, node, SymbolFlags::FUNCTION, name);
            }
            SyntaxKind::ClassExpression | SyntaxKind::ClassDeclaration => {
                self.bind_class_like_declaration(arena, file, node, facts)?;
            }
            SyntaxKind::InterfaceDeclaration => {
                self.bind_block_scoped_declaration(
                    arena,
                    file,
                    node,
                    SymbolFlags::INTERFACE,
                    SymbolFlags::INTERFACE_EXCLUDES,
                    facts,
                )?;
            }
            SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration => {
                self.bind_block_scoped_declaration(
                    arena,
                    file,
                    node,
                    SymbolFlags::TYPE_ALIAS,
                    SymbolFlags::TYPE_ALIAS_EXCLUDES,
                    facts,
                )?;
            }
            SyntaxKind::EnumDeclaration => {
                let is_const = has_combined_modifier(arena, node, SyntaxKind::ConstKeyword);
                self.bind_block_scoped_declaration(
                    arena,
                    file,
                    node,
                    if is_const {
                        SymbolFlags::CONST_ENUM
                    } else {
                        SymbolFlags::REGULAR_ENUM
                    },
                    if is_const {
                        SymbolFlags::CONST_ENUM_EXCLUDES
                    } else {
                        SymbolFlags::REGULAR_ENUM_EXCLUDES
                    },
                    facts,
                )?;
            }
            SyntaxKind::ModuleDeclaration => {
                let state = *module_states
                    .get(&node)
                    .expect("module state was preflighted for every module declaration");
                self.bind_module_declaration(arena, file, node, facts, state)?;
            }
            SyntaxKind::ImportEqualsDeclaration
            | SyntaxKind::NamespaceImport
            | SyntaxKind::ImportSpecifier
            | SyntaxKind::ExportSpecifier => {
                self.declare_symbol_and_add_to_symbol_table(
                    arena,
                    file,
                    node,
                    SymbolFlags::ALIAS,
                    SymbolFlags::ALIAS_EXCLUDES,
                    facts,
                )?;
            }
            SyntaxKind::NamespaceExportDeclaration => {
                self.bind_namespace_export_declaration(arena, file, node, facts)?;
            }
            SyntaxKind::ImportClause => {
                if matches!(
                    arena.get(node).map(|node| &node.data),
                    Some(NodeData::ImportClause(clause)) if clause.name.is_some()
                ) {
                    self.declare_symbol_and_add_to_symbol_table(
                        arena,
                        file,
                        node,
                        SymbolFlags::ALIAS,
                        SymbolFlags::ALIAS_EXCLUDES,
                        facts,
                    )?;
                }
            }
            SyntaxKind::ExportDeclaration => {
                self.bind_export_declaration(arena, file, node)?;
            }
            SyntaxKind::ExportAssignment => {
                self.bind_export_assignment(arena, file, node)?;
            }
            SyntaxKind::JsxAttributes => {
                self.bind_anonymous_declaration(
                    arena,
                    file,
                    node,
                    SymbolFlags::OBJECT_LITERAL,
                    EscapedName::internal(InternalSymbolName::JsxAttributes),
                );
            }
            SyntaxKind::JsxAttribute => {
                self.declare_symbol_and_add_to_symbol_table(
                    arena,
                    file,
                    node,
                    SymbolFlags::PROPERTY,
                    SymbolFlags::PROPERTY_EXCLUDES,
                    facts,
                )?;
            }
            SyntaxKind::BinaryExpression | SyntaxKind::CallExpression
                if facts.is_javascript_file() =>
            {
                self.bind_javascript_assignment_declaration(arena, file, node, facts)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn bind_namespace_export_declaration(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        facts: &CanonicalSourceFileFacts,
    ) -> Result<(), CanonicalDeclarationError> {
        if arena
            .get(node)
            .and_then(|node| modifier_list(&node.data))
            .is_some()
        {
            self.push_bind_diagnostic(arena, file, node, 1184, std::iter::empty::<String>());
        }
        let parent = arena.get(node).and_then(|node| node.parent);
        if !parent.is_some_and(|parent| {
            arena
                .get(parent)
                .is_some_and(|parent| parent.kind == SyntaxKind::SourceFile)
        }) {
            self.push_bind_diagnostic(arena, file, node, 1316, std::iter::empty::<String>());
        } else if !facts.is_external_module() {
            self.push_bind_diagnostic(arena, file, node, 1314, std::iter::empty::<String>());
        } else if !facts.is_declaration_file() {
            self.push_bind_diagnostic(arena, file, node, 1315, std::iter::empty::<String>());
        } else {
            let source_file = self
                .files
                .get(&file)
                .expect("namespace-export file is registered")
                .source_file;
            let parent = self
                .bound_node_symbol(file, source_file)
                .expect("external source file is declared before its children");
            let exports = self.ensure_file_global_exports(file);
            self.declare_symbol(
                arena,
                file,
                exports,
                Some(parent),
                node,
                SymbolFlags::ALIAS,
                SymbolFlags::ALIAS_EXCLUDES,
            )?;
        }
        Ok(())
    }

    fn bind_export_declaration(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
    ) -> Result<(), CanonicalDeclarationError> {
        let Some(NodeData::ExportDeclaration(export)) = arena.get(node).map(|node| &node.data)
        else {
            unreachable!("export declaration dispatch is kind checked");
        };
        let container = self
            .declaration_container(file, node)
            .expect("export declarations have a captured container");
        let Some(parent) = self.bound_node_symbol(file, container) else {
            let name = self.get_declaration_name(arena, NodeRef::new(arena.id(), file, node))?;
            self.bind_anonymous_declaration(arena, file, node, SymbolFlags::EXPORT_STAR, name);
            return Ok(());
        };
        if export.export_clause.is_none() {
            let exports = self.ensure_symbol_exports(parent);
            self.declare_symbol(
                arena,
                file,
                exports,
                Some(parent),
                node,
                SymbolFlags::EXPORT_STAR,
                SymbolFlags::NONE,
            )?;
        } else if let Some(clause) = export.export_clause.filter(|clause| {
            arena
                .get(*clause)
                .is_some_and(|clause| clause.kind == SyntaxKind::NamespaceExport)
        }) {
            let exports = self.ensure_symbol_exports(parent);
            self.declare_symbol(
                arena,
                file,
                exports,
                Some(parent),
                clause,
                SymbolFlags::ALIAS,
                SymbolFlags::ALIAS_EXCLUDES,
            )?;
        }
        Ok(())
    }

    fn bind_export_assignment(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
    ) -> Result<(), CanonicalDeclarationError> {
        let Some(NodeData::ExportAssignment(assignment)) = arena.get(node).map(|node| &node.data)
        else {
            unreachable!("export-assignment dispatch is kind checked");
        };
        let container = self
            .declaration_container(file, node)
            .expect("export assignments have a captured container");
        let Some(parent) = self.bound_node_symbol(file, container) else {
            let name = self.get_declaration_name(arena, NodeRef::new(arena.id(), file, node))?;
            self.bind_anonymous_declaration(arena, file, node, SymbolFlags::VALUE, name);
            return Ok(());
        };
        let expression_is_alias = is_entity_name_expression(arena, assignment.expression)
            || arena
                .get(assignment.expression)
                .is_some_and(|expression| expression.kind == SyntaxKind::ClassExpression);
        let exports = self.ensure_symbol_exports(parent);
        let symbol = self.declare_symbol(
            arena,
            file,
            exports,
            Some(parent),
            node,
            if expression_is_alias {
                SymbolFlags::ALIAS
            } else {
                SymbolFlags::PROPERTY
            },
            SymbolFlags::ALL,
        )?;
        if assignment.is_export_equals {
            self.set_value_declaration(symbol, NodeRef::new(arena.id(), file, node));
        }
        Ok(())
    }

    fn bind_javascript_assignment_declaration(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        facts: &CanonicalSourceFileFacts,
    ) -> Result<(), CanonicalDeclarationError> {
        match javascript_assignment_kind(arena, node) {
            Some(JavaScriptAssignmentKind::ModuleExports) if facts.is_common_js_module() => {
                self.bind_commonjs_assignment(arena, file, node, true)?;
            }
            Some(JavaScriptAssignmentKind::ExportsProperty) if facts.is_common_js_module() => {
                self.bind_commonjs_assignment(arena, file, node, false)?;
            }
            Some(JavaScriptAssignmentKind::ThisProperty) => {
                self.bind_javascript_this_property_assignment(arena, file, node)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn bind_commonjs_assignment(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        module_exports: bool,
    ) -> Result<(), CanonicalDeclarationError> {
        let source = self
            .files
            .get(&file)
            .expect("CommonJS assignment file is registered")
            .source_file;
        let parent = self
            .bound_node_symbol(file, source)
            .expect("CommonJS source declaration precedes its assignments");
        let exports = self.ensure_symbol_exports(parent);
        let is_alias = match arena.get(node).map(|node| &node.data) {
            Some(NodeData::BinaryExpression(binary)) => {
                is_entity_name_expression(arena, binary.right)
                    || arena
                        .get(binary.right)
                        .is_some_and(|right| right.kind == SyntaxKind::ClassExpression)
            }
            _ => false,
        };
        let includes = if is_alias {
            SymbolFlags::ALIAS
        } else if module_exports {
            SymbolFlags::PROPERTY
        } else {
            SymbolFlags::FUNCTION_SCOPED_VARIABLE
        };
        let excludes = if module_exports {
            SymbolFlags::NONE
        } else {
            SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES
        };
        let symbol = self.declare_symbol_ex_worker(
            arena,
            file,
            exports,
            Some(parent),
            node,
            includes,
            excludes,
            false,
            false,
            true,
        )?;
        if module_exports {
            self.set_value_declaration(symbol, NodeRef::new(arena.id(), file, node));
        }
        Ok(())
    }

    fn bind_javascript_this_property_assignment(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
    ) -> Result<(), CanonicalDeclarationError> {
        if let Some(NodeData::BinaryExpression(binary)) = arena.get(node).map(|node| &node.data)
            && let Some(NodeData::PropertyAccessExpression(access)) =
                arena.get(binary.left).map(|node| &node.data)
            && arena
                .get(access.name)
                .is_some_and(|name| name.kind == SyntaxKind::PrivateIdentifier)
        {
            return Ok(());
        }
        let Some(this_container) = self
            .files
            .get(&file)
            .and_then(|bound| bound.nodes.get(node.index()))
            .and_then(|binding| binding.this_container)
        else {
            return Ok(());
        };
        let Some(kind) = arena.get(this_container).map(|node| node.kind) else {
            return Ok(());
        };
        if !matches!(
            kind,
            SyntaxKind::Constructor
                | SyntaxKind::PropertyDeclaration
                | SyntaxKind::MethodDeclaration
                | SyntaxKind::GetAccessor
                | SyntaxKind::SetAccessor
                | SyntaxKind::ClassStaticBlockDeclaration
        ) {
            return Ok(());
        }
        let Some(class) = arena
            .get(this_container)
            .and_then(|container| container.parent)
        else {
            return Ok(());
        };
        let Some(parent) = self.bound_node_symbol(file, class) else {
            return Ok(());
        };
        let table = if is_static_declaration(arena, this_container) {
            self.ensure_symbol_exports(parent)
        } else {
            self.ensure_symbol_members(parent)
        };
        let is_computed_name = has_dynamic_name(arena, node);
        let includes = if is_computed_name {
            SymbolFlags::PROPERTY
        } else {
            SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
        };
        self.declare_symbol_ex_worker(
            arena,
            file,
            table,
            Some(parent),
            node,
            includes,
            SymbolFlags::NONE,
            true,
            is_computed_name,
            true,
        )?;
        if is_computed_name {
            self.add_late_bound_assignment_declaration(arena, file, node, parent);
        }
        Ok(())
    }

    fn bind_module_declaration(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        facts: &CanonicalSourceFileFacts,
        state: ModuleInstanceState,
    ) -> Result<(), CanonicalDeclarationError> {
        if is_ambient_module(arena, node) {
            if has_syntactic_modifier(arena, node, SyntaxKind::ExportKeyword) {
                self.push_bind_diagnostic(arena, file, node, 2668, std::iter::empty::<String>());
            }
            let is_external_augmentation = is_module_augmentation_external(arena, node, facts);
            if is_external_augmentation
                && is_parser_collected_module_augmentation(arena, node, facts)
            {
                self.record_module_augmentation(arena, file, node, facts);
            }
            if is_external_augmentation {
                self.declare_module_symbol(arena, file, node, facts, state)?;
            } else {
                let symbol = self.declare_symbol_and_add_to_symbol_table(
                    arena,
                    file,
                    node,
                    SymbolFlags::VALUE_MODULE,
                    SymbolFlags::VALUE_MODULE_EXCLUDES,
                    facts,
                )?;
                let Some(NodeData::ModuleDeclaration(module)) =
                    arena.get(node).map(|node| &node.data)
                else {
                    unreachable!("module declaration dispatch is kind checked");
                };
                if arena
                    .get(module.name)
                    .is_some_and(|name| name.kind == SyntaxKind::StringLiteral)
                {
                    let pattern = node_text(arena, module.name).unwrap_or_default();
                    let mut stars = pattern.match_indices('*').map(|(index, _)| index);
                    if let Some(star_index) = stars.next() {
                        if stars.next().is_some() {
                            self.push_bind_diagnostic(arena, file, module.name, 5061, [pattern]);
                        } else {
                            self.files
                                .get_mut(&file)
                                .expect("ambient-module file is registered")
                                .pattern_ambient_modules
                                .push(CanonicalPatternAmbientModule {
                                    pattern,
                                    star_index,
                                    symbol,
                                });
                        }
                    }
                }
            }
            return Ok(());
        }

        self.declare_module_symbol(arena, file, node, facts, state)?;
        if state == ModuleInstanceState::NonInstantiated {
            return Ok(());
        }
        let symbol = self
            .bound_node_symbol(file, node)
            .expect("module declaration writes its node symbol");
        let record = self
            .symbols
            .symbol(symbol)
            .expect("declared module symbol is store-owned");
        let (flags, check_flags) = (record.flags(), record.check_flags());
        let was_permanently_cleared = self
            .files
            .get(&file)
            .expect("module file is registered")
            .not_const_enum_only_modules
            .contains(&symbol);
        let const_enum_only = !flags
            .intersects(SymbolFlags::FUNCTION | SymbolFlags::CLASS | SymbolFlags::REGULAR_ENUM)
            && state == ModuleInstanceState::ConstEnumOnly
            && !was_permanently_cleared;
        if const_enum_only {
            assert!(self.symbols.set_symbol_flags(
                symbol,
                flags | SymbolFlags::CONST_ENUM_ONLY_MODULE,
                check_flags,
            ));
        } else {
            assert!(self.symbols.set_symbol_flags(
                symbol,
                flags.without(SymbolFlags::CONST_ENUM_ONLY_MODULE),
                check_flags,
            ));
            self.files
                .get_mut(&file)
                .expect("module file is registered")
                .not_const_enum_only_modules
                .insert(symbol);
        }
        Ok(())
    }

    fn record_module_augmentation(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        facts: &CanonicalSourceFileFacts,
    ) {
        let Some(NodeData::ModuleDeclaration(module)) = arena.get(node).map(|node| &node.data)
        else {
            unreachable!("ambient-module dispatch is kind checked");
        };
        let container = arena
            .get(node)
            .and_then(|module| module.parent)
            .expect("parser-collected module augmentation has a container");
        let in_ambient_context = is_ambient_node(arena, container, facts);
        self.files
            .get_mut(&file)
            .expect("module-augmentation file is registered")
            .module_augmentations
            .push(CanonicalModuleAugmentation {
                name: NodeRef::new(arena.id(), file, module.name),
                in_ambient_context,
            });
    }

    fn declare_module_symbol(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        facts: &CanonicalSourceFileFacts,
        state: ModuleInstanceState,
    ) -> Result<SemanticSymbolId, CanonicalDeclarationError> {
        let instantiated = state != ModuleInstanceState::NonInstantiated;
        self.declare_symbol_and_add_to_symbol_table(
            arena,
            file,
            node,
            if instantiated {
                SymbolFlags::VALUE_MODULE
            } else {
                SymbolFlags::NAMESPACE_MODULE
            },
            if instantiated {
                SymbolFlags::VALUE_MODULE_EXCLUDES
            } else {
                SymbolFlags::NAMESPACE_MODULE_EXCLUDES
            },
            facts,
        )
    }

    fn push_bind_diagnostic<I, S>(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        code: u32,
        arguments: I,
    ) where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.files
            .get_mut(&file)
            .expect("diagnostic file is registered")
            .diagnostics
            .push(CanonicalBindDiagnostic {
                node: NodeRef::new(arena.id(), file, node),
                diagnostic: make_diagnostic(code, arguments),
                related_information: Vec::new(),
            });
    }

    fn declaration_facts_for(
        arena: &NodeArena,
        node: NodeRef,
        name: &EscapedName,
    ) -> DeclarationFacts {
        let declaration = arena
            .get(node.node)
            .expect("anonymous declarations are reachable");
        let diagnostic_node = get_name_of_declaration(arena, node.node)
            .map_or(node, |name| NodeRef::new(node.arena, node.file, name));
        DeclarationFacts {
            kind: declaration.kind,
            diagnostic_node,
            display_name: if name.as_ref() == InternalSymbolName::Missing.as_ref() {
                "(Missing)".to_owned()
            } else {
                name.escaped_display().to_string()
            },
        }
    }

    fn bind_anonymous_declaration(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        includes: SymbolFlags,
        name: EscapedName,
    ) -> SemanticSymbolId {
        let node_ref = NodeRef::new(arena.id(), file, node);
        let declaration_facts = Self::declaration_facts_for(arena, node_ref, &name);
        let symbol = self.new_symbol(file, name);
        if includes.intersects(SymbolFlags::ENUM_MEMBER | SymbolFlags::CLASS_MEMBER) {
            let container = self
                .declaration_container(file, node)
                .expect("anonymous member declarations have a container");
            // A script source file has no symbol. TypeScript-Go writes the
            // current container's (possibly nil) symbol as the anonymous
            // declaration's parent, so retain `None` for that exact case.
            if let Some(parent) = self.bound_node_symbol(file, container) {
                assert!(self.symbols.set_symbol_relationships(
                    symbol,
                    None,
                    None,
                    Some(parent),
                    None,
                ));
            } else {
                assert!(
                    arena
                        .get(container)
                        .is_some_and(|container| container.kind == SyntaxKind::SourceFile)
                        && self
                            .files
                            .get(&file)
                            .and_then(|bound| bound.source_facts.as_ref())
                            .is_some_and(|facts| !facts.is_external_module()),
                    "only a script source container has an absent declaration symbol",
                );
            }
        }
        self.add_declaration_to_symbol(symbol, node_ref, includes, declaration_facts);
        symbol
    }

    fn bind_deferred_expando_assignments(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        assignments: &[ExpandoAssignmentInfo],
    ) {
        for assignment in assignments {
            self.bind_deferred_expando_assignment(arena, file, *assignment);
        }
    }

    fn bind_deferred_expando_assignment(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        assignment: ExpandoAssignmentInfo,
    ) {
        let parent = expando_assignment_parent(arena, assignment.node)
            .expect("the expando queue contains only access assignments");
        let mut symbol = assignment.block_scope_container.and_then(|container| {
            self.lookup_entity(arena, file, parent, container, assignment.this_container)
        });
        // A block-scope hit shadows the semantic-container table even when it
        // is not an expando-capable initializer. Only an actual lookup miss
        // takes the fallback, matching the pinned binder.
        if symbol.is_none() {
            symbol = assignment.container.and_then(|container| {
                self.lookup_entity(arena, file, parent, container, assignment.this_container)
            });
        }
        let Some(symbol) =
            symbol.and_then(|symbol| self.get_expando_initializer_symbol(arena, file, symbol))
        else {
            return;
        };

        if has_dynamic_name(arena, assignment.node) {
            self.bind_anonymous_declaration(
                arena,
                file,
                assignment.node,
                SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT,
                EscapedName::internal(InternalSymbolName::Computed),
            );
            self.add_late_bound_assignment_declaration(arena, file, assignment.node, symbol);
            return;
        }

        let exports = self.ensure_symbol_exports(symbol);
        let name = self
            .get_declaration_name(arena, NodeRef::new(arena.id(), file, assignment.node))
            .expect("expando name shapes were preflighted");
        let may_declare = self
            .symbols
            .symbol_table(exports)
            .expect("expando export table is store-owned")
            .get(name.as_ref())
            .is_none_or(|existing| {
                self.symbols
                    .symbol(existing)
                    .expect("expando table entries are store-owned")
                    .flags()
                    .intersects(SymbolFlags::ASSIGNMENT)
            });
        if may_declare {
            self.declare_symbol_ex_worker(
                arena,
                file,
                exports,
                Some(symbol),
                assignment.node,
                SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT,
                SymbolFlags::PROPERTY_EXCLUDES,
                false,
                false,
                true,
            )
            .expect("expando declarations were preflighted");
        }
    }

    fn add_late_bound_assignment_declaration(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        symbol: SemanticSymbolId,
    ) {
        let exports = self.ensure_symbol_exports(symbol);
        let assignment = self
            .symbols
            .symbol_table(exports)
            .expect("late-bound export table is store-owned")
            .get(InternalSymbolName::AssignmentDeclaration.as_ref())
            .unwrap_or_else(|| {
                let assignment = self.new_symbol(
                    file,
                    EscapedName::internal(InternalSymbolName::AssignmentDeclaration),
                );
                assert_eq!(
                    self.symbols.insert_symbol(
                        exports,
                        EscapedName::internal(InternalSymbolName::AssignmentDeclaration),
                        assignment,
                    ),
                    Some(None),
                );
                assignment
            });
        let record = self
            .symbols
            .symbol(assignment)
            .expect("late-bound assignment symbol is store-owned");
        let mut declarations = record
            .declarations()
            .map_or_else(Vec::new, <[NodeRef]>::to_vec);
        declarations.push(NodeRef::new(arena.id(), file, node));
        assert!(
            self.symbols
                .set_symbol_declarations(assignment, Some(declarations), None)
        );
    }

    fn lookup_entity(
        &self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        container: NodeId,
        this_container: Option<NodeId>,
    ) -> Option<SemanticSymbolId> {
        if arena
            .get(node)
            .is_some_and(|node| node.kind == SyntaxKind::Identifier)
        {
            return self.lookup_name(arena, file, node, container);
        }
        let expression = access_expression_base(arena, node)?;
        if arena
            .get(expression)
            .is_some_and(|expression| expression.kind == SyntaxKind::ThisKeyword)
        {
            let class_member = this_container?;
            let class = arena.get(class_member)?.parent?;
            let class_symbol = self.bound_node_symbol(file, class)?;
            let class_record = self.symbols.symbol(class_symbol)?;
            let table = if is_static_declaration(arena, class_member) {
                class_record.exports()?
            } else {
                class_record.members()?
            };
            let name = element_or_property_access_name(arena, node)?;
            return self
                .symbols
                .symbol_table(table)?
                .get_source(&node_text(arena, name)?);
        }
        let base = self.lookup_entity(arena, file, expression, container, this_container)?;
        let base = self.get_expando_initializer_symbol(arena, file, base)?;
        let exports = self.symbols.symbol(base)?.exports()?;
        let name = element_or_property_access_name(arena, node)?;
        self.symbols
            .symbol_table(exports)?
            .get_source(&node_text(arena, name)?)
    }

    fn lookup_name(
        &self,
        arena: &NodeArena,
        file: FileId,
        name: NodeId,
        container: NodeId,
    ) -> Option<SemanticSymbolId> {
        let name = node_text(arena, name)?;
        let binding = self.files.get(&file)?.nodes.get(container.index())?;
        if let Some(local) = binding
            .locals
            .and_then(|locals| self.symbols.symbol_table(locals))
            .and_then(|locals| locals.get_source(&name))
        {
            return Some(
                self.symbols
                    .symbol(local)
                    .and_then(crate::semantic::Symbol::export_symbol)
                    .unwrap_or(local),
            );
        }
        let exports = binding
            .symbol
            .and_then(|symbol| self.symbols.symbol(symbol))
            .and_then(crate::semantic::Symbol::exports)?;
        self.symbols.symbol_table(exports)?.get_source(&name)
    }

    fn get_expando_initializer_symbol(
        &self,
        arena: &NodeArena,
        file: FileId,
        symbol: SemanticSymbolId,
    ) -> Option<SemanticSymbolId> {
        const NODE_FLAG_CONST: u32 = 1 << 1;

        let declaration = self.symbols.symbol(symbol)?.value_declaration()?;
        if !declaration.is_for(arena.id(), file) {
            return None;
        }
        let declaration_node = arena.get(declaration.node)?;
        let javascript = self
            .files
            .get(&file)
            .and_then(|bound| bound.source_facts.as_ref())
            .is_some_and(CanonicalSourceFileFacts::is_javascript_file);
        if declaration_node.kind == SyntaxKind::FunctionDeclaration
            || javascript && declaration_node.kind == SyntaxKind::ClassDeclaration
        {
            return Some(symbol);
        }
        let initializer = match &declaration_node.data {
            NodeData::VariableDeclaration(variable) => {
                let parent = declaration_node
                    .parent
                    .and_then(|parent| arena.get(parent))?;
                if !javascript && parent.flags.0 & NODE_FLAG_CONST == 0 {
                    return None;
                }
                variable.initializer?
            }
            NodeData::BinaryExpression(binary) if javascript => binary.right,
            _ => return None,
        };
        let initializer_record = arena.get(initializer)?;
        let valid = matches!(
            initializer_record.kind,
            SyntaxKind::FunctionExpression | SyntaxKind::ArrowFunction
        ) || javascript
            && (initializer_record.kind == SyntaxKind::ClassExpression
                || matches!(
                    &initializer_record.data,
                    NodeData::ObjectLiteralExpression(object)
                        if object.properties.nodes.is_empty()
                            && !has_javascript_type_annotation(arena, declaration.node)
                ));
        if !valid {
            return None;
        }
        self.bound_node_symbol(file, initializer)
    }

    fn bind_property_or_method_or_accessor(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        includes: SymbolFlags,
        excludes: SymbolFlags,
        facts: &CanonicalSourceFileFacts,
    ) -> Result<SemanticSymbolId, CanonicalDeclarationError> {
        if has_dynamic_name(arena, node) {
            Ok(self.bind_anonymous_declaration(
                arena,
                file,
                node,
                includes,
                EscapedName::internal(InternalSymbolName::Computed),
            ))
        } else {
            self.declare_symbol_and_add_to_symbol_table(
                arena, file, node, includes, excludes, facts,
            )
        }
    }

    fn bind_function_or_constructor_type(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
    ) -> Result<(), CanonicalDeclarationError> {
        let node_ref = NodeRef::new(arena.id(), file, node);
        let name = self.get_declaration_name(arena, node_ref)?;
        let signature = self.new_symbol(file, name.clone());
        let signature_facts = Self::declaration_facts_for(arena, node_ref, &name);
        self.add_declaration_to_symbol(
            signature,
            node_ref,
            SymbolFlags::SIGNATURE,
            signature_facts,
        );
        let type_name = EscapedName::internal(InternalSymbolName::Type);
        let type_literal = self.new_symbol(file, type_name.clone());
        let type_facts = Self::declaration_facts_for(arena, node_ref, &type_name);
        self.add_declaration_to_symbol(
            type_literal,
            node_ref,
            SymbolFlags::TYPE_LITERAL,
            type_facts,
        );
        let members = self.ensure_symbol_members(type_literal);
        assert_eq!(
            self.symbols.insert_symbol(members, name, signature),
            Some(None)
        );
        Ok(())
    }

    fn bind_class_like_declaration(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        facts: &CanonicalSourceFileFacts,
    ) -> Result<(), CanonicalDeclarationError> {
        match &arena
            .get(node)
            .expect("class declaration is reachable")
            .data
        {
            NodeData::ClassDeclaration(_) => {
                self.bind_block_scoped_declaration(
                    arena,
                    file,
                    node,
                    SymbolFlags::CLASS,
                    SymbolFlags::CLASS_EXCLUDES,
                    facts,
                )?;
            }
            NodeData::ClassExpression(class) => {
                let name = class.name.and_then(|name| node_text(arena, name));
                let symbol_name = name.as_ref().map_or_else(
                    || EscapedName::internal(InternalSymbolName::Class),
                    |name| EscapedName::source(name.clone()),
                );
                if let Some(name) = name {
                    self.files
                        .get_mut(&file)
                        .expect("class-expression file is registered")
                        .classifiable_names
                        .insert(EscapedName::source(name));
                }
                self.bind_anonymous_declaration(arena, file, node, SymbolFlags::CLASS, symbol_name);
            }
            _ => unreachable!("class-like dispatch is kind checked"),
        }

        let class_symbol = self
            .bound_node_symbol(file, node)
            .expect("class-like declaration writes its node symbol");
        let prototype_name = EscapedName::source("prototype");
        let prototype = self.new_symbol(file, prototype_name.clone());
        self.or_symbol_flags(prototype, SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE);
        let exports = self.ensure_symbol_exports(class_symbol);
        let existing = self
            .symbols
            .symbol_table(exports)
            .expect("class exports were just allocated")
            .get(prototype_name.as_ref());
        if let Some(existing) = existing
            && let Some(first) = self
                .symbols
                .symbol(existing)
                .expect("class export is store-owned")
                .declarations()
                .and_then(|declarations| declarations.first())
                .copied()
        {
            self.files
                .get_mut(&file)
                .expect("class file is registered")
                .diagnostics
                .push(CanonicalBindDiagnostic {
                    node: first,
                    diagnostic: make_diagnostic(2300, ["prototype"]),
                    related_information: Vec::new(),
                });
        }
        assert_eq!(
            self.symbols
                .insert_symbol(exports, prototype_name, prototype),
            Some(existing)
        );
        assert!(self.symbols.set_symbol_relationships(
            prototype,
            None,
            None,
            Some(class_symbol),
            None,
        ));
        Ok(())
    }

    fn bind_type_parameter(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        facts: &CanonicalSourceFileFacts,
    ) -> Result<(), CanonicalDeclarationError> {
        let parent = arena.get(node).and_then(|node| node.parent);
        if parent.is_some_and(|parent| {
            arena
                .get(parent)
                .is_some_and(|parent| parent.kind == SyntaxKind::InferType)
        }) {
            if let Some(container) = infer_type_container(arena, parent.expect("checked above")) {
                let table = self.ensure_node_locals(file, container);
                self.declare_symbol(
                    arena,
                    file,
                    table,
                    None,
                    node,
                    SymbolFlags::TYPE_PARAMETER,
                    SymbolFlags::TYPE_PARAMETER_EXCLUDES,
                )?;
            } else {
                let name =
                    self.get_declaration_name(arena, NodeRef::new(arena.id(), file, node))?;
                self.bind_anonymous_declaration(
                    arena,
                    file,
                    node,
                    SymbolFlags::TYPE_PARAMETER,
                    name,
                );
            }
        } else {
            self.declare_symbol_and_add_to_symbol_table(
                arena,
                file,
                node,
                SymbolFlags::TYPE_PARAMETER,
                SymbolFlags::TYPE_PARAMETER_EXCLUDES,
                facts,
            )?;
        }
        Ok(())
    }

    fn bind_parameter(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        facts: &CanonicalSourceFileFacts,
    ) -> Result<(), CanonicalDeclarationError> {
        let Some(NodeData::ParameterDeclaration(parameter)) =
            arena.get(node).map(|node| &node.data)
        else {
            unreachable!("parameter dispatch is kind checked");
        };
        if is_binding_pattern(arena, parameter.name) {
            let parent = arena
                .get(node)
                .and_then(|node| node.parent)
                .expect("parameters have a function-like parent");
            let index = function_like_parameters(arena, parent)
                .and_then(|parameters| parameters.iter().position(|parameter| *parameter == node))
                .expect("parameter occurs in its parent's parameter list");
            self.bind_anonymous_declaration(
                arena,
                file,
                node,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source(format!("__{index}")),
            );
        } else {
            self.declare_symbol_and_add_to_symbol_table(
                arena,
                file,
                node,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::PARAMETER_EXCLUDES,
                facts,
            )?;
        }

        if is_parameter_property_declaration(arena, node) {
            let constructor = arena
                .get(node)
                .and_then(|node| node.parent)
                .expect("parameter property has a constructor parent");
            let class = arena
                .get(constructor)
                .and_then(|constructor| constructor.parent)
                .expect("constructor has a containing class");
            let parent = self
                .bound_node_symbol(file, class)
                .expect("class declaration precedes constructor parameters");
            let members = self.ensure_symbol_members(parent);
            self.declare_symbol(
                arena,
                file,
                members,
                Some(parent),
                node,
                SymbolFlags::PROPERTY | optional_symbol_flag(arena, node),
                SymbolFlags::PROPERTY_EXCLUDES,
            )?;
        }
        Ok(())
    }

    fn bind_variable_declaration_or_binding_element(
        &mut self,
        arena: &NodeArena,
        file: FileId,
        node: NodeId,
        facts: &CanonicalSourceFileFacts,
    ) -> Result<(), CanonicalDeclarationError> {
        let Some(name) = get_name_of_declaration(arena, node) else {
            return Ok(());
        };
        if is_binding_pattern(arena, name) {
            return Ok(());
        }
        if facts.is_javascript_file()
            && arena
                .get(node)
                .and_then(|node| match &node.data {
                    NodeData::VariableDeclaration(variable) => variable.initializer,
                    _ => None,
                })
                .is_some_and(|initializer| is_javascript_require_call(arena, initializer))
        {
            self.declare_symbol_and_add_to_symbol_table(
                arena,
                file,
                node,
                SymbolFlags::ALIAS,
                SymbolFlags::ALIAS_EXCLUDES,
                facts,
            )?;
        } else if is_block_or_catch_scoped(arena, node) {
            self.bind_block_scoped_declaration(
                arena,
                file,
                node,
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
                SymbolFlags::BLOCK_SCOPED_VARIABLE_EXCLUDES,
                facts,
            )?;
        } else if is_part_of_parameter_declaration(arena, node) {
            self.declare_symbol_and_add_to_symbol_table(
                arena,
                file,
                node,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::PARAMETER_EXCLUDES,
                facts,
            )?;
        } else {
            self.declare_symbol_and_add_to_symbol_table(
                arena,
                file,
                node,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES,
                facts,
            )?;
        }
        Ok(())
    }

    fn preflight_declaration(
        &self,
        arena: &NodeArena,
        file: FileId,
        symbol_table: SymbolTableId,
        parent: Option<SemanticSymbolId>,
        node: NodeId,
    ) -> Result<NodeRef, CanonicalDeclarationError> {
        let Some(bound) = self.files.get(&file) else {
            return Err(CanonicalDeclarationError::UnboundFile(file));
        };
        if bound.arena != arena.id() {
            return Err(CanonicalDeclarationError::WrongArena {
                file,
                expected: bound.arena,
                actual: arena.id(),
            });
        }
        if bound.arena_revision != arena.revision() {
            return Err(CanonicalDeclarationError::ArenaRevisionMismatch {
                file,
                expected: bound.arena_revision,
                actual: arena.revision(),
            });
        }
        let node_ref = NodeRef::new(arena.id(), file, node);
        if !bound.contains(node_ref)
            || !arena
                .get(node)
                .is_some_and(|node| node.data.matches_syntax_kind(node.kind))
        {
            return Err(CanonicalDeclarationError::UnboundNode(node_ref));
        }
        if !self.symbols.contains_symbol_table(symbol_table) {
            return Err(CanonicalDeclarationError::InvalidSymbolTable(symbol_table));
        }
        if let Some(parent) = parent.filter(|parent| !self.symbols.contains_symbol(*parent)) {
            return Err(CanonicalDeclarationError::InvalidParent(parent));
        }
        Ok(node_ref)
    }

    fn prepare_declaration(
        &mut self,
        arena: &NodeArena,
        node: NodeRef,
        parent: Option<SemanticSymbolId>,
        is_computed_name: bool,
        has_known_typescript_file_kind: bool,
    ) -> Result<PreparedDeclaration, CanonicalDeclarationError> {
        if !is_computed_name
            && !has_known_typescript_file_kind
            && assignment_name_requires_javascript_file_kind(arena, node.node)
        {
            return Err(CanonicalDeclarationError::JavaScriptFileKindRequired(node));
        }
        if !is_computed_name && has_dynamic_name(arena, node.node) {
            return Err(CanonicalDeclarationError::DynamicNameRequiresComputed(node));
        }
        let declaration = arena
            .get(node.node)
            .expect("bound declaration was preflighted");
        let is_default_export =
            has_syntactic_modifier(arena, node.node, SyntaxKind::DefaultKeyword)
                || matches!(
                    &declaration.data,
                    NodeData::ExportSpecifier(specifier)
                        if node_text(arena, specifier.name).as_deref() == Some("default")
                );
        let name = if is_computed_name {
            EscapedName::internal(InternalSymbolName::Computed)
        } else if is_default_export && parent.is_some() {
            EscapedName::internal(InternalSymbolName::Default)
        } else {
            self.get_declaration_name(arena, node)?
        };
        let diagnostic_node = get_name_of_declaration(arena, node.node)
            .map_or(node, |name| NodeRef::new(node.arena, node.file, name));
        let display_name = schema_declaration_name(&declaration.data).map_or_else(
            || {
                if name.as_ref() == InternalSymbolName::Missing.as_ref() {
                    "(Missing)".to_owned()
                } else {
                    name.escaped_display().to_string()
                }
            },
            |name| declaration_name_to_string(arena, name),
        );
        let export_type_suggestion = export_type_suggestion(arena, node);
        Ok(PreparedDeclaration {
            name,
            facts: DeclarationFacts {
                kind: declaration.kind,
                diagnostic_node,
                display_name,
            },
            is_default_export,
            is_export_assignment_default: matches!(
                &declaration.data,
                NodeData::ExportAssignment(assignment) if !assignment.is_export_equals
            ),
            export_type_suggestion,
        })
    }

    #[allow(clippy::too_many_lines)] // Keep upstream declaration-name cases together.
    fn get_declaration_name(
        &mut self,
        arena: &NodeArena,
        declaration: NodeRef,
    ) -> Result<EscapedName, CanonicalDeclarationError> {
        let node = arena
            .get(declaration.node)
            .expect("bound declaration was preflighted");
        if let NodeData::ExportAssignment(assignment) = &node.data {
            return Ok(EscapedName::internal(if assignment.is_export_equals {
                InternalSymbolName::ExportEquals
            } else {
                InternalSymbolName::Default
            }));
        }
        if self
            .files
            .get(&declaration.file)
            .and_then(|bound| bound.source_facts.as_ref())
            .is_some_and(CanonicalSourceFileFacts::is_javascript_file)
            && javascript_assignment_kind(arena, declaration.node)
                == Some(JavaScriptAssignmentKind::ModuleExports)
        {
            return Ok(EscapedName::internal(InternalSymbolName::ExportEquals));
        }

        if let Some(name_id) = get_name_of_declaration(arena, declaration.node) {
            let name = arena
                .get(name_id)
                .expect("bound declaration names are reachable");
            if let NodeData::ModuleDeclaration(module) = &node.data {
                if module.keyword == SyntaxKind::GlobalKeyword {
                    return Ok(EscapedName::internal(InternalSymbolName::Global));
                }
                if name.kind == SyntaxKind::StringLiteral {
                    let text = node_text(arena, name_id).unwrap_or_default();
                    return Ok(EscapedName::source(format!("\"{text}\"")));
                }
            }
            if let NodeData::PrivateIdentifier(private) = &name.data {
                let Some(containing_class) = containing_class(arena, declaration.node) else {
                    return Ok(EscapedName::internal(InternalSymbolName::Missing));
                };
                let class_ref = NodeRef::new(declaration.arena, declaration.file, containing_class);
                let class_symbol = self
                    .files
                    .get(&declaration.file)
                    .and_then(|file| file.symbol(class_ref))
                    .ok_or(CanonicalDeclarationError::MissingContainingClassSymbol(
                        declaration,
                    ))?;
                return self
                    .symbols
                    .private_identifier_name(class_symbol, &private.text)
                    .ok_or(CanonicalDeclarationError::MissingContainingClassSymbol(
                        declaration,
                    ));
            }
            if is_property_name_literal(name.kind) {
                return Ok(EscapedName::source(
                    node_text(arena, name_id).unwrap_or_default(),
                ));
            }
            if name.kind == SyntaxKind::JsxNamespacedName {
                return Ok(EscapedName::source(
                    node_text(arena, name_id).unwrap_or_default(),
                ));
            }
            if let NodeData::ComputedPropertyName(computed) = &name.data {
                let expression = arena
                    .get(computed.expression)
                    .expect("computed-name expression is reachable");
                if is_string_or_numeric_literal_like(expression.kind) {
                    return Ok(EscapedName::source(
                        node_text(arena, computed.expression).unwrap_or_default(),
                    ));
                }
                if let NodeData::PrefixUnaryExpression(unary) = &expression.data
                    && matches!(
                        unary.operator,
                        SyntaxKind::PlusToken | SyntaxKind::MinusToken
                    )
                    && arena
                        .get(unary.operand)
                        .is_some_and(|operand| operand.kind == SyntaxKind::NumericLiteral)
                {
                    let operator = if unary.operator == SyntaxKind::PlusToken {
                        "+"
                    } else {
                        "-"
                    };
                    return Ok(EscapedName::source(format!(
                        "{operator}{}",
                        node_text(arena, unary.operand).unwrap_or_default()
                    )));
                }
                return Err(CanonicalDeclarationError::DynamicNameRequiresComputed(
                    declaration,
                ));
            }
            return Ok(EscapedName::internal(InternalSymbolName::Missing));
        }

        Ok(EscapedName::internal(match node.kind {
            SyntaxKind::Constructor => InternalSymbolName::Constructor,
            SyntaxKind::FunctionType | SyntaxKind::CallSignature => InternalSymbolName::Call,
            SyntaxKind::ConstructorType | SyntaxKind::ConstructSignature => InternalSymbolName::New,
            SyntaxKind::IndexSignature => InternalSymbolName::Index,
            SyntaxKind::ExportDeclaration => InternalSymbolName::ExportStar,
            SyntaxKind::SourceFile | SyntaxKind::BinaryExpression => {
                InternalSymbolName::ExportEquals
            }
            _ => InternalSymbolName::Missing,
        }))
    }

    fn new_symbol(&mut self, file: FileId, name: EscapedName) -> SemanticSymbolId {
        let count = &mut self
            .files
            .get_mut(&file)
            .expect("symbol allocation file was preflighted")
            .symbol_count;
        *count = count.checked_add(1).expect("binder symbol count exhausted");
        self.symbols
            .alloc_symbol(SymbolData::new(SymbolFlags::NONE, name))
            .expect("reference-free binder symbol allocation is valid")
    }

    fn or_symbol_flags(&mut self, symbol: SemanticSymbolId, flags: SymbolFlags) {
        let record = self
            .symbols
            .symbol(symbol)
            .expect("declared symbol is store-owned");
        let (combined, check_flags) = (record.flags() | flags, record.check_flags());
        assert!(self.symbols.set_symbol_flags(symbol, combined, check_flags));
    }

    fn set_value_declaration(&mut self, symbol: SemanticSymbolId, node: NodeRef) {
        let record = self
            .symbols
            .symbol(symbol)
            .expect("declared symbol is store-owned");
        let declarations = record.declarations().map(<[NodeRef]>::to_vec);
        let current = record.value_declaration();
        let replace = current.is_none_or(|current| {
            let current_facts = self
                .declaration_facts
                .get(&current)
                .expect("value declarations were added by this binder");
            let incoming_facts = self
                .declaration_facts
                .get(&node)
                .expect("forced value declaration was already declared");
            should_replace_value_declaration(current_facts.kind, incoming_facts.kind)
        });
        if replace {
            assert!(
                self.symbols
                    .set_symbol_declarations(symbol, declarations, Some(node))
            );
        }
    }

    fn add_declaration_to_symbol(
        &mut self,
        symbol: SemanticSymbolId,
        node: NodeRef,
        includes: SymbolFlags,
        facts: DeclarationFacts,
    ) {
        let record = self
            .symbols
            .symbol(symbol)
            .expect("declared symbol is store-owned");
        let mut flags = record.flags() | includes;
        let check_flags = record.check_flags();
        let mut declarations = record.declarations().map(<[NodeRef]>::to_vec);
        let mut value_declaration = record.value_declaration();

        match &mut declarations {
            None => declarations = Some(vec![node]),
            Some(declarations) if !declarations.contains(&node) => declarations.push(node),
            Some(_) => {}
        }

        let no_longer_const_enum_only = flags.intersects(SymbolFlags::CONST_ENUM_ONLY_MODULE)
            && flags
                .intersects(SymbolFlags::FUNCTION | SymbolFlags::CLASS | SymbolFlags::REGULAR_ENUM);
        if no_longer_const_enum_only {
            flags = flags.without(SymbolFlags::CONST_ENUM_ONLY_MODULE);
        }

        if includes.intersects(SymbolFlags::VALUE) {
            let replace = value_declaration.is_none_or(|current| {
                let current_facts = if current == node {
                    &facts
                } else {
                    self.declaration_facts
                        .get(&current)
                        .expect("value declarations were added by this binder")
                };
                should_replace_value_declaration(current_facts.kind, facts.kind)
            });
            if replace {
                value_declaration = Some(node);
            }
        }

        assert!(self.symbols.set_symbol_flags(symbol, flags, check_flags));
        assert!(
            self.symbols
                .set_symbol_declarations(symbol, declarations, value_declaration,)
        );
        self.files
            .get_mut(&node.file)
            .expect("declaration file was preflighted")
            .node_binding_mut(node)
            .expect("declaration node was preflighted")
            .symbol = Some(symbol);
        self.declaration_facts.entry(node).or_insert(facts);
        if no_longer_const_enum_only {
            self.files
                .get_mut(&node.file)
                .expect("declaration file was preflighted")
                .not_const_enum_only_modules
                .insert(symbol);
        }
    }

    fn report_declaration_conflict(
        &mut self,
        file: FileId,
        _arena: &NodeArena,
        existing: SemanticSymbolId,
        node: NodeRef,
        includes: SymbolFlags,
        prepared: &PreparedDeclaration,
    ) {
        let record = self
            .symbols
            .symbol(existing)
            .expect("conflicting symbol is store-owned");
        let existing_flags = record.flags();
        let declarations = record.declarations().unwrap_or_default().to_vec();
        let mut code = if existing_flags.intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE) {
            2451
        } else {
            2300
        };
        let mut message_needs_name = true;
        if existing_flags.intersects(SymbolFlags::ENUM) || includes.intersects(SymbolFlags::ENUM) {
            code = 2567;
            message_needs_name = false;
        }
        let multiple_default_exports = !declarations.is_empty()
            && (prepared.is_default_export || prepared.is_export_assignment_default);
        if multiple_default_exports {
            code = 2528;
            message_needs_name = false;
        }

        let current_args = message_needs_name
            .then(|| [prepared.facts.display_name.clone()])
            .into_iter()
            .flatten();
        let mut current = CanonicalBindDiagnostic {
            node: prepared.facts.diagnostic_node,
            diagnostic: make_diagnostic(code, current_args),
            related_information: Vec::new(),
        };
        if existing_flags
            .intersects(SymbolFlags::ALIAS | SymbolFlags::TYPE | SymbolFlags::NAMESPACE)
            && let Some(suggestion) = prepared.export_type_suggestion.clone()
        {
            current.related_information.push(suggestion);
        }

        for (index, declaration) in declarations.into_iter().enumerate() {
            let previous = self
                .declaration_facts
                .get(&declaration)
                .expect("conflicting declarations were added by this binder");
            let previous_args = message_needs_name
                .then(|| [previous.display_name.clone()])
                .into_iter()
                .flatten();
            let mut diagnostic = CanonicalBindDiagnostic {
                node: previous.diagnostic_node,
                diagnostic: make_diagnostic(code, previous_args),
                related_information: Vec::new(),
            };
            if multiple_default_exports {
                diagnostic
                    .related_information
                    .push(CanonicalRelatedInformation {
                        node: prepared.facts.diagnostic_node,
                        diagnostic: make_diagnostic(
                            if index == 0 { 2753 } else { 6204 },
                            std::iter::empty::<String>(),
                        ),
                    });
                current
                    .related_information
                    .push(CanonicalRelatedInformation {
                        node: previous.diagnostic_node,
                        diagnostic: make_diagnostic(2752, std::iter::empty::<String>()),
                    });
            }
            self.files
                .get_mut(&file)
                .expect("declaration file was preflighted")
                .diagnostics
                .push(diagnostic);
        }
        self.files
            .get_mut(&file)
            .expect("declaration file was preflighted")
            .diagnostics
            .push(current);

        let _ = node;
    }

    /// Traverses one Program source file into canonical side data.
    ///
    /// The existing flow traversal is the sole recursive walk. Canonical
    /// enter/exit hooks capture declaration-order state while that same walk
    /// builds the one control-flow graph.
    ///
    /// # Errors
    ///
    /// Returns [`CanonicalBindError`] when the root or its generated child
    /// graph is invalid, the Program file slot is already occupied, or the AST
    /// arena conflicts with an existing Program scope.
    ///
    /// # Panics
    ///
    /// Panics if the preflighted tree violates the flow walk's internal enter/
    /// exit invariants, or if the inserted file disappears from the private
    /// file map.
    pub fn bind_source_file(
        &mut self,
        arena: &NodeArena,
        source_file: NodeId,
        file: FileId,
    ) -> Result<&BoundFile, CanonicalBindError> {
        self.bind_source_file_inner(arena, source_file, file, None)
    }

    /// Traverses one Program source file while retaining the exact
    /// parser/Program source facts required by declaration binding.
    ///
    /// This entry point intentionally completes only traversal. Call
    /// [`Self::bind_typescript_declaration_slice`] after every Program file has
    /// supplied its facts to complete declaration binding.
    ///
    /// # Errors
    ///
    /// Returns the same structural/provenance errors as
    /// [`Self::bind_source_file`].
    pub fn bind_source_file_with_facts(
        &mut self,
        arena: &NodeArena,
        source_file: NodeId,
        file: FileId,
        facts: CanonicalSourceFileFacts,
    ) -> Result<&BoundFile, CanonicalBindError> {
        self.bind_source_file_inner(arena, source_file, file, Some(facts))
    }

    fn bind_source_file_inner(
        &mut self,
        arena: &NodeArena,
        source_file: NodeId,
        file: FileId,
        source_facts: Option<CanonicalSourceFileFacts>,
    ) -> Result<&BoundFile, CanonicalBindError> {
        let root = NodeRef::new(arena.id(), file, source_file);
        if self.files.contains_key(&file) {
            return Err(CanonicalBindError::DuplicateFile(file));
        }
        if !matches!(
            arena.get(source_file),
            Some(node)
                if node.kind == SyntaxKind::SourceFile
                    && matches!(node.data, NodeData::SourceFile(_))
        ) {
            return Err(CanonicalBindError::InvalidSourceFile(root));
        }

        let children = collect_children(arena, file)?;
        validate_reachable_tree(arena, source_file, file, &children)?;
        let scope = AstScope::new(file, arena);
        if !self.symbols.register_ast_scope(scope) {
            return Err(CanonicalBindError::AstScopeConflict {
                file,
                arena: arena.id(),
            });
        }

        let mut traversal = FileTraversal::new(arena, source_file, file, source_facts);
        let flow = build_flow_graph_with_hooks(arena, &children, source_file, file, &mut traversal);
        let file_binding = traversal.finish(flow);
        self.files.insert(file, file_binding);
        Ok(self
            .files
            .get(&file)
            .expect("canonical file was inserted immediately above"))
    }

    #[must_use]
    pub fn finish(self) -> CanonicalProgramBindings {
        CanonicalProgramBindings {
            symbols: self.symbols,
            files: self.files,
        }
    }
}

fn assignment_variable_merge(incoming: SymbolFlags, existing: SymbolFlags) -> bool {
    incoming.intersects(SymbolFlags::VARIABLE) && existing.intersects(SymbolFlags::ASSIGNMENT)
        || incoming.intersects(SymbolFlags::ASSIGNMENT)
            && existing.intersects(SymbolFlags::VARIABLE)
}

fn declaration_family_supported(
    arena: &NodeArena,
    node: NodeId,
    facts: &CanonicalSourceFileFacts,
) -> bool {
    !arena.get(node).is_some_and(|node| {
        node.kind == SyntaxKind::JsTypeAliasDeclaration && !facts.is_javascript_file()
    })
}

fn get_module_instance_state(arena: &NodeArena, node: NodeId) -> ModuleInstanceState {
    let mut visited = HashMap::new();
    get_module_instance_state_worker_for_declaration(arena, node, &mut visited)
}

fn get_module_instance_state_worker_for_declaration(
    arena: &NodeArena,
    node: NodeId,
    visited: &mut HashMap<NodeId, ModuleInstanceState>,
) -> ModuleInstanceState {
    let Some(NodeData::ModuleDeclaration(module)) = arena.get(node).map(|node| &node.data) else {
        unreachable!("module-instance state starts at a module declaration");
    };
    module
        .body
        .map_or(ModuleInstanceState::Instantiated, |body| {
            get_module_instance_state_cached(arena, body, visited)
        })
}

fn get_module_instance_state_cached(
    arena: &NodeArena,
    node: NodeId,
    visited: &mut HashMap<NodeId, ModuleInstanceState>,
) -> ModuleInstanceState {
    if let Some(cached) = visited.get(&node).copied() {
        return if cached == ModuleInstanceState::Unknown {
            ModuleInstanceState::NonInstantiated
        } else {
            cached
        };
    }
    visited.insert(node, ModuleInstanceState::Unknown);
    let result = get_module_instance_state_worker(arena, node, visited);
    visited.insert(node, result);
    result
}

fn get_module_instance_state_worker(
    arena: &NodeArena,
    node: NodeId,
    visited: &mut HashMap<NodeId, ModuleInstanceState>,
) -> ModuleInstanceState {
    let declaration = arena
        .get(node)
        .expect("module-instance state only follows reachable nodes");
    match &declaration.data {
        NodeData::InterfaceDeclaration(_) | NodeData::TypeAliasDeclaration(_)
            if matches!(
                declaration.kind,
                SyntaxKind::InterfaceDeclaration
                    | SyntaxKind::TypeAliasDeclaration
                    | SyntaxKind::JsTypeAliasDeclaration
            ) =>
        {
            ModuleInstanceState::NonInstantiated
        }
        NodeData::EnumDeclaration(_)
            if has_combined_modifier(arena, node, SyntaxKind::ConstKeyword) =>
        {
            ModuleInstanceState::ConstEnumOnly
        }
        NodeData::ImportDeclaration(_) | NodeData::ImportEqualsDeclaration(_)
            if matches!(
                declaration.kind,
                SyntaxKind::ImportDeclaration
                    | SyntaxKind::JsImportDeclaration
                    | SyntaxKind::ImportEqualsDeclaration
            ) && !has_syntactic_modifier(arena, node, SyntaxKind::ExportKeyword) =>
        {
            ModuleInstanceState::NonInstantiated
        }
        NodeData::ExportDeclaration(export)
            if export.module_specifier.is_none()
                && export.export_clause.is_some_and(|clause| {
                    arena
                        .get(clause)
                        .is_some_and(|clause| clause.kind == SyntaxKind::NamedExports)
                }) =>
        {
            let clause = export.export_clause.expect("guarded above");
            let Some(NodeData::NamedExports(exports)) = arena.get(clause).map(|node| &node.data)
            else {
                unreachable!("named export clause was kind checked");
            };
            let mut state = ModuleInstanceState::NonInstantiated;
            for specifier in &exports.elements.nodes {
                let specifier_state =
                    get_module_instance_state_for_alias_target(arena, *specifier, visited);
                if module_instance_state_rank(specifier_state) > module_instance_state_rank(state) {
                    state = specifier_state;
                }
                if state == ModuleInstanceState::Instantiated {
                    return state;
                }
            }
            state
        }
        NodeData::ModuleBlock(block) => {
            let mut state = ModuleInstanceState::NonInstantiated;
            for statement in &block.statements.nodes {
                match get_module_instance_state_cached(arena, *statement, visited) {
                    ModuleInstanceState::NonInstantiated => {}
                    ModuleInstanceState::ConstEnumOnly => {
                        state = ModuleInstanceState::ConstEnumOnly;
                    }
                    ModuleInstanceState::Instantiated => {
                        return ModuleInstanceState::Instantiated;
                    }
                    ModuleInstanceState::Unknown => {
                        unreachable!("cached module state never exposes its cycle sentinel");
                    }
                }
            }
            state
        }
        NodeData::ModuleDeclaration(_) => {
            get_module_instance_state_worker_for_declaration(arena, node, visited)
        }
        _ => ModuleInstanceState::Instantiated,
    }
}

const fn module_instance_state_rank(state: ModuleInstanceState) -> u8 {
    match state {
        ModuleInstanceState::Unknown => 0,
        ModuleInstanceState::NonInstantiated => 1,
        ModuleInstanceState::Instantiated => 2,
        ModuleInstanceState::ConstEnumOnly => 3,
    }
}

fn get_module_instance_state_for_alias_target(
    arena: &NodeArena,
    node: NodeId,
    visited: &mut HashMap<NodeId, ModuleInstanceState>,
) -> ModuleInstanceState {
    let Some(NodeData::ExportSpecifier(specifier)) = arena.get(node).map(|node| &node.data) else {
        return ModuleInstanceState::Instantiated;
    };
    let name = specifier.property_name.unwrap_or(specifier.name);
    if !arena
        .get(name)
        .is_some_and(|name| name.kind == SyntaxKind::Identifier)
    {
        return ModuleInstanceState::Instantiated;
    }
    let Some(name_text) = node_text(arena, name) else {
        return ModuleInstanceState::Instantiated;
    };

    let mut parent = arena.get(node).and_then(|node| node.parent);
    while let Some(scope) = parent {
        if matches!(
            arena.get(scope).map(|scope| scope.kind),
            Some(SyntaxKind::Block | SyntaxKind::ModuleBlock | SyntaxKind::SourceFile)
        ) {
            let mut found = ModuleInstanceState::Unknown;
            if let Some(statements) = statement_list(arena, scope) {
                for statement in statements {
                    if node_has_name(arena, *statement, &name_text) {
                        let state = get_module_instance_state_cached(arena, *statement, visited);
                        if found == ModuleInstanceState::Unknown
                            || module_instance_state_rank(state) > module_instance_state_rank(found)
                        {
                            found = state;
                        }
                        if found == ModuleInstanceState::Instantiated {
                            return found;
                        }
                        if arena.get(*statement).is_some_and(|statement| {
                            statement.kind == SyntaxKind::ImportEqualsDeclaration
                        }) {
                            found = ModuleInstanceState::Instantiated;
                        }
                    }
                }
            }
            if found != ModuleInstanceState::Unknown {
                return found;
            }
        }
        parent = arena.get(scope).and_then(|scope| scope.parent);
    }
    ModuleInstanceState::Instantiated
}

fn statement_list(arena: &NodeArena, node: NodeId) -> Option<&[NodeId]> {
    match &arena.get(node)?.data {
        NodeData::Block(block) => Some(&block.statements.nodes),
        NodeData::ModuleBlock(block) => Some(&block.statements.nodes),
        NodeData::SourceFile(source) => Some(&source.statements.nodes),
        _ => None,
    }
}

fn node_has_name(arena: &NodeArena, node: NodeId, expected: &str) -> bool {
    if let Some(name) = get_name_of_declaration(arena, node) {
        return arena
            .get(name)
            .is_some_and(|name| name.kind == SyntaxKind::Identifier)
            && node_text(arena, name).as_deref() == Some(expected);
    }
    let Some(NodeData::VariableStatement(statement)) = arena.get(node).map(|node| &node.data)
    else {
        return false;
    };
    let Some(NodeData::VariableDeclarationList(list)) =
        arena.get(statement.declaration_list).map(|node| &node.data)
    else {
        return false;
    };
    list.declarations
        .nodes
        .iter()
        .any(|declaration| node_has_name(arena, *declaration, expected))
}

fn declaration_name_shape_unsupported(arena: &NodeArena, node: NodeId) -> bool {
    let Some(declaration) = arena.get(node) else {
        return true;
    };
    let dynamic_is_handled = matches!(
        declaration.kind,
        SyntaxKind::PropertyDeclaration
            | SyntaxKind::PropertySignature
            | SyntaxKind::PropertyAssignment
            | SyntaxKind::ShorthandPropertyAssignment
            | SyntaxKind::EnumMember
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::MethodSignature
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
    ) || is_typescript_expando_property_assignment(arena, node)
        || javascript_assignment_kind(arena, node) == Some(JavaScriptAssignmentKind::ThisProperty);
    if has_dynamic_name(arena, node) && !dynamic_is_handled {
        return true;
    }
    false
}

fn root_declaration(arena: &NodeArena, mut node: NodeId) -> NodeId {
    while arena
        .get(node)
        .is_some_and(|node| node.kind == SyntaxKind::BindingElement)
    {
        let Some(parent) = arena.get(node).and_then(|node| node.parent) else {
            break;
        };
        let Some(grandparent) = arena.get(parent).and_then(|parent| parent.parent) else {
            break;
        };
        node = grandparent;
    }
    node
}

fn has_combined_modifier(arena: &NodeArena, node: NodeId, modifier: SyntaxKind) -> bool {
    let mut declaration = root_declaration(arena, node);
    if has_syntactic_modifier(arena, declaration, modifier) {
        return true;
    }
    if arena
        .get(declaration)
        .is_some_and(|node| node.kind == SyntaxKind::VariableDeclaration)
        && let Some(parent) = arena.get(declaration).and_then(|node| node.parent)
    {
        declaration = parent;
    }
    if has_syntactic_modifier(arena, declaration, modifier) {
        return true;
    }
    if arena
        .get(declaration)
        .is_some_and(|node| node.kind == SyntaxKind::VariableDeclarationList)
        && let Some(parent) = arena.get(declaration).and_then(|node| node.parent)
    {
        declaration = parent;
    }
    has_syntactic_modifier(arena, declaration, modifier)
}

fn combined_node_flags(arena: &NodeArena, node: NodeId) -> u32 {
    let mut declaration = root_declaration(arena, node);
    let mut flags = arena.get(declaration).map_or(0, |node| node.flags.0);
    if arena
        .get(declaration)
        .is_some_and(|node| node.kind == SyntaxKind::VariableDeclaration)
        && let Some(parent) = arena.get(declaration).and_then(|node| node.parent)
    {
        declaration = parent;
        flags |= arena.get(declaration).map_or(0, |node| node.flags.0);
    }
    if arena
        .get(declaration)
        .is_some_and(|node| node.kind == SyntaxKind::VariableDeclarationList)
        && let Some(parent) = arena.get(declaration).and_then(|node| node.parent)
    {
        flags |= arena.get(parent).map_or(0, |node| node.flags.0);
    }
    flags
}

fn is_block_or_catch_scoped(arena: &NodeArena, node: NodeId) -> bool {
    const BLOCK_SCOPED_FLAGS: u32 = (1 << 0) | (1 << 1) | (1 << 2);
    if combined_node_flags(arena, node) & BLOCK_SCOPED_FLAGS != 0 {
        return true;
    }
    let root = root_declaration(arena, node);
    arena
        .get(root)
        .filter(|root| root.kind == SyntaxKind::VariableDeclaration)
        .and_then(|root| root.parent)
        .and_then(|parent| arena.get(parent))
        .is_some_and(|parent| parent.kind == SyntaxKind::CatchClause)
}

fn is_part_of_parameter_declaration(arena: &NodeArena, node: NodeId) -> bool {
    arena
        .get(root_declaration(arena, node))
        .is_some_and(|node| node.kind == SyntaxKind::Parameter)
}

fn is_binding_pattern(arena: &NodeArena, node: NodeId) -> bool {
    arena.get(node).is_some_and(|node| {
        matches!(
            node.kind,
            SyntaxKind::ObjectBindingPattern | SyntaxKind::ArrayBindingPattern
        )
    })
}

fn infer_type_container(arena: &NodeArena, mut node: NodeId) -> Option<NodeId> {
    loop {
        let parent = arena.get(node)?.parent?;
        if let NodeData::ConditionalTypeNode(conditional) = &arena.get(parent)?.data
            && conditional.extends_type == node
        {
            return Some(parent);
        }
        node = parent;
    }
}

fn function_like_parameters(arena: &NodeArena, node: NodeId) -> Option<&[NodeId]> {
    let parameters = match &arena.get(node)?.data {
        NodeData::ArrowFunction(data) => &data.parameters,
        NodeData::CallSignatureDeclaration(data) => &data.parameters,
        NodeData::ConstructSignatureDeclaration(data) => &data.parameters,
        NodeData::ConstructorDeclaration(data) => &data.parameters,
        NodeData::ConstructorTypeNode(data) => &data.parameters,
        NodeData::FunctionDeclaration(data) => &data.parameters,
        NodeData::FunctionExpression(data) => &data.parameters,
        NodeData::FunctionTypeNode(data) => &data.parameters,
        NodeData::GetAccessorDeclaration(data) => &data.parameters,
        NodeData::IndexSignatureDeclaration(data) => &data.parameters,
        NodeData::MethodDeclaration(data) => &data.parameters,
        NodeData::MethodSignatureDeclaration(data) => &data.parameters,
        NodeData::SetAccessorDeclaration(data) => &data.parameters,
        _ => return None,
    };
    Some(&parameters.nodes)
}

fn is_parameter_property_declaration(arena: &NodeArena, node: NodeId) -> bool {
    let Some(parent) = arena.get(node).and_then(|node| node.parent) else {
        return false;
    };
    arena
        .get(parent)
        .is_some_and(|parent| parent.kind == SyntaxKind::Constructor)
        && [
            SyntaxKind::PublicKeyword,
            SyntaxKind::PrivateKeyword,
            SyntaxKind::ProtectedKeyword,
            SyntaxKind::ReadonlyKeyword,
            SyntaxKind::OverrideKeyword,
        ]
        .into_iter()
        .any(|modifier| has_syntactic_modifier(arena, node, modifier))
}

fn optional_symbol_flag(arena: &NodeArena, node: NodeId) -> SymbolFlags {
    let token = match arena.get(node).map(|node| &node.data) {
        Some(NodeData::GetAccessorDeclaration(data)) => data.postfix_token,
        Some(NodeData::MethodDeclaration(data)) => data.postfix_token,
        Some(NodeData::MethodSignatureDeclaration(data)) => data.postfix_token,
        Some(NodeData::ParameterDeclaration(data)) => data.question_token,
        Some(NodeData::PropertyDeclaration(data)) => data.postfix_token,
        Some(NodeData::PropertySignatureDeclaration(data)) => data.postfix_token,
        Some(NodeData::SetAccessorDeclaration(data)) => data.postfix_token,
        _ => None,
    };
    if token.is_some_and(|token| {
        arena
            .get(token)
            .is_some_and(|token| token.kind == SyntaxKind::QuestionToken)
    }) {
        SymbolFlags::OPTIONAL
    } else {
        SymbolFlags::NONE
    }
}

fn is_static_declaration(arena: &NodeArena, node: NodeId) -> bool {
    arena
        .get(node)
        .is_some_and(|node| node.kind == SyntaxKind::ClassStaticBlockDeclaration)
        || has_syntactic_modifier(arena, node, SyntaxKind::StaticKeyword)
}

fn is_ambient_module(arena: &NodeArena, node: NodeId) -> bool {
    let Some(NodeData::ModuleDeclaration(module)) = arena.get(node).map(|node| &node.data) else {
        return false;
    };
    module.keyword == SyntaxKind::GlobalKeyword
        || arena
            .get(module.name)
            .is_some_and(|name| name.kind == SyntaxKind::StringLiteral)
}

fn is_module_augmentation_external(
    arena: &NodeArena,
    node: NodeId,
    facts: &CanonicalSourceFileFacts,
) -> bool {
    let Some(parent) = arena.get(node).and_then(|node| node.parent) else {
        return false;
    };
    match arena.get(parent).map(|parent| parent.kind) {
        Some(SyntaxKind::SourceFile) => facts.is_external_module(),
        Some(SyntaxKind::ModuleBlock) => {
            let Some(module) = arena.get(parent).and_then(|parent| parent.parent) else {
                return false;
            };
            is_ambient_module(arena, module)
                && arena
                    .get(module)
                    .and_then(|module| module.parent)
                    .is_some_and(|source| {
                        arena
                            .get(source)
                            .is_some_and(|source| source.kind == SyntaxKind::SourceFile)
                    })
                && !facts.is_external_module()
        }
        _ => false,
    }
}

fn is_parser_collected_module_augmentation(
    arena: &NodeArena,
    node: NodeId,
    facts: &CanonicalSourceFileFacts,
) -> bool {
    if !is_ambient_node(arena, node, facts) {
        return false;
    }
    if facts.is_external_module() {
        return true;
    }
    let Some(NodeData::ModuleDeclaration(module)) = arena.get(node).map(|node| &node.data) else {
        return false;
    };
    let name = node_text(arena, module.name).unwrap_or_default();
    !ts_path::is_relative(&name) && !ts_path::is_rooted_disk_path(&name)
}

fn is_ambient_node(arena: &NodeArena, mut node: NodeId, facts: &CanonicalSourceFileFacts) -> bool {
    if facts.is_declaration_file() {
        return true;
    }
    loop {
        if has_syntactic_modifier(arena, node, SyntaxKind::DeclareKeyword) {
            return true;
        }
        let Some(parent) = arena.get(node).and_then(|node| node.parent) else {
            return false;
        };
        node = parent;
    }
}

fn container_has_export_context(
    arena: &NodeArena,
    container: NodeId,
    facts: &CanonicalSourceFileFacts,
) -> bool {
    is_ambient_node(arena, container, facts) && !has_export_declarations(arena, container)
}

fn is_implicitly_exported_jsdoc_declaration(
    arena: &NodeArena,
    node: NodeId,
    facts: &CanonicalSourceFileFacts,
) -> bool {
    if !facts.is_javascript_file() || !facts.is_external_or_common_js_module() {
        return false;
    }
    let Some(declaration) = arena.get(node) else {
        return false;
    };
    if !declaration.parent.is_some_and(|parent| {
        arena
            .get(parent)
            .is_some_and(|parent| parent.kind == SyntaxKind::SourceFile)
    }) {
        return false;
    }
    declaration.kind == SyntaxKind::JsTypeAliasDeclaration
        || declaration.kind == SyntaxKind::ModuleDeclaration
            && declaration.flags.0 & NodeFlags::REPARSED.0 != 0
}

fn has_export_declarations(arena: &NodeArena, node: NodeId) -> bool {
    let statements = match arena.get(node).map(|node| &node.data) {
        Some(NodeData::SourceFile(source)) => Some(&source.statements.nodes),
        Some(NodeData::ModuleDeclaration(module)) => module.body.and_then(|body| {
            let NodeData::ModuleBlock(block) = &arena.get(body)?.data else {
                return None;
            };
            Some(&block.statements.nodes)
        }),
        _ => None,
    };
    statements.is_some_and(|statements| {
        statements.iter().any(|statement| {
            arena.get(*statement).is_some_and(|statement| {
                matches!(
                    statement.kind,
                    SyntaxKind::ExportDeclaration | SyntaxKind::ExportAssignment
                )
            })
        })
    })
}

fn make_diagnostic<I, S>(code: u32, arguments: I) -> Diagnostic
where
    I: IntoIterator<Item = S>,
    S: Into<String>,
{
    let message = message_by_code(code).expect("pinned binder diagnostic is in the catalog");
    Diagnostic::with_arguments(message, arguments)
}

fn is_property_name_literal(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Identifier
            | SyntaxKind::StringLiteral
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::NumericLiteral
    )
}

fn is_string_or_numeric_literal_like(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::StringLiteral
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::NumericLiteral
    )
}

fn node_text(arena: &NodeArena, node: NodeId) -> Option<String> {
    let node = arena.get(node)?;
    match &node.data {
        NodeData::Identifier(data) => Some(data.text.clone()),
        NodeData::PrivateIdentifier(data) => Some(data.text.clone()),
        NodeData::StringLiteral(data) => Some(data.text.clone()),
        NodeData::NoSubstitutionTemplateLiteral(data) => Some(data.text.clone()),
        NodeData::NumericLiteral(data) => Some(data.text.clone()),
        NodeData::JsxNamespacedName(data) => Some(format!(
            "{}:{}",
            node_text(arena, data.namespace)?,
            node_text(arena, data.name)?
        )),
        _ => source_text_of_node(arena, node).map(str::to_owned),
    }
}

fn source_text_of_node<'a>(arena: &'a NodeArena, node: &ts_ast::Node) -> Option<&'a str> {
    let text = arena.source_text()?;
    text.get(node.range.start.get() as usize..node.range.end.get() as usize)
}

fn declaration_name_to_string(arena: &NodeArena, name: NodeId) -> String {
    let node = arena
        .get(name)
        .expect("declaration name is reachable from a bound node");
    if node.range.is_empty() {
        "(Missing)".to_owned()
    } else {
        source_text_of_node(arena, node)
            .map_or_else(|| node_text(arena, name).unwrap_or_default(), str::to_owned)
    }
}

#[allow(clippy::too_many_lines)]
fn schema_declaration_name(data: &NodeData) -> Option<NodeId> {
    match data {
        NodeData::BindingElement(data) => data.name,
        NodeData::ClassDeclaration(data) => data.name,
        NodeData::ClassExpression(data) => data.name,
        NodeData::EnumDeclaration(data) => Some(data.name),
        NodeData::EnumMember(data) => Some(data.name),
        NodeData::ExportSpecifier(data) => Some(data.name),
        NodeData::FunctionDeclaration(data) => data.name,
        NodeData::FunctionExpression(data) => data.name,
        NodeData::GetAccessorDeclaration(data) => Some(data.name),
        NodeData::ImportAttribute(data) => Some(data.name),
        NodeData::ImportClause(data) => data.name,
        NodeData::ImportEqualsDeclaration(data) => Some(data.name),
        NodeData::ImportSpecifier(data) => Some(data.name),
        NodeData::InterfaceDeclaration(data) => Some(data.name),
        NodeData::JsDocCallbackTag(data) => data.name,
        NodeData::JsDocLink(data) => data.name,
        NodeData::JsDocLinkCode(data) => data.name,
        NodeData::JsDocLinkPlain(data) => data.name,
        NodeData::JsDocNameReference(data) => Some(data.name),
        NodeData::JsDocParameterOrPropertyTag(data) => Some(data.name),
        NodeData::JsDocTypedefTag(data) => data.name,
        NodeData::JsxAttribute(data) => Some(data.name),
        NodeData::JsxNamespacedName(data) => Some(data.name),
        NodeData::MetaProperty(data) => Some(data.name),
        NodeData::MethodDeclaration(data) => Some(data.name),
        NodeData::MethodSignatureDeclaration(data) => Some(data.name),
        NodeData::ModuleDeclaration(data) => Some(data.name),
        NodeData::NamedTupleMember(data) => Some(data.name),
        NodeData::NamespaceExport(data) => Some(data.name),
        NodeData::NamespaceExportDeclaration(data) => Some(data.name),
        NodeData::NamespaceImport(data) => Some(data.name),
        NodeData::ParameterDeclaration(data) => Some(data.name),
        NodeData::PropertyAssignment(data) => Some(data.name),
        NodeData::PropertyAccessExpression(data) => Some(data.name),
        NodeData::PropertyDeclaration(data) => Some(data.name),
        NodeData::PropertySignatureDeclaration(data) => Some(data.name),
        NodeData::SetAccessorDeclaration(data) => Some(data.name),
        NodeData::ShorthandPropertyAssignment(data) => Some(data.name),
        NodeData::TypeAliasDeclaration(data) => Some(data.name),
        NodeData::TypeParameterDeclaration(data) => Some(data.name),
        NodeData::VariableDeclaration(data) => Some(data.name),
        _ => None,
    }
}

fn get_name_of_declaration(arena: &NodeArena, declaration: NodeId) -> Option<NodeId> {
    let node = arena.get(declaration)?;
    let non_assigned = match &node.data {
        NodeData::BinaryExpression(_) | NodeData::CallExpression(_) => {
            assignment_declaration_name(arena, declaration)
        }
        NodeData::ExportAssignment(assignment) => arena
            .get(assignment.expression)
            .is_some_and(|expression| expression.kind == SyntaxKind::Identifier)
            .then_some(assignment.expression),
        _ => schema_declaration_name(&node.data),
    };
    if non_assigned.is_some() {
        return non_assigned;
    }
    matches!(
        node.kind,
        SyntaxKind::FunctionExpression | SyntaxKind::ArrowFunction | SyntaxKind::ClassExpression
    )
    .then(|| get_assigned_name(arena, declaration))
    .flatten()
}

fn get_assigned_name(arena: &NodeArena, declaration: NodeId) -> Option<NodeId> {
    let parent_id = arena.get(declaration)?.parent?;
    let parent = arena.get(parent_id)?;
    match &parent.data {
        NodeData::PropertyAssignment(data) => Some(data.name),
        NodeData::BindingElement(data) => data.name,
        NodeData::BinaryExpression(data) if data.right == declaration => {
            let left = arena.get(data.left)?;
            match &left.data {
                NodeData::Identifier(_) => Some(data.left),
                NodeData::PropertyAccessExpression(access) => Some(access.name),
                NodeData::ElementAccessExpression(access) => {
                    let argument = skip_parentheses(arena, access.argument_expression)?;
                    arena
                        .get(argument)
                        .is_some_and(|argument| is_string_or_numeric_literal_like(argument.kind))
                        .then_some(argument)
                }
                _ => None,
            }
        }
        NodeData::VariableDeclaration(data) => arena
            .get(data.name)
            .is_some_and(|name| name.kind == SyntaxKind::Identifier)
            .then_some(data.name),
        _ => None,
    }
}

fn assignment_declaration_name(arena: &NodeArena, declaration: NodeId) -> Option<NodeId> {
    let node = arena.get(declaration)?;
    match &node.data {
        NodeData::BinaryExpression(binary)
            if arena
                .get(binary.operator_token)
                .is_some_and(|operator| operator.kind == SyntaxKind::EqualsToken) =>
        {
            let left = arena.get(binary.left)?;
            match &left.data {
                NodeData::PropertyAccessExpression(access)
                    if is_entity_name_expression_ex(arena, access.expression, true)
                        && arena
                            .get(access.name)
                            .is_some_and(|name| name.kind == SyntaxKind::Identifier) =>
                {
                    Some(access.name)
                }
                NodeData::ElementAccessExpression(access)
                    if is_entity_name_expression_ex(arena, access.expression, true) =>
                {
                    let argument = skip_parentheses(arena, access.argument_expression)?;
                    arena
                        .get(argument)
                        .is_some_and(|argument| is_string_or_numeric_literal_like(argument.kind))
                        .then_some(argument)
                        .or(Some(binary.left))
                }
                _ => None,
            }
        }
        NodeData::CallExpression(call)
            if is_bindable_object_define_property_call(arena, declaration) =>
        {
            call.arguments.nodes.get(1).copied()
        }
        _ => None,
    }
}

fn javascript_assignment_kind(
    arena: &NodeArena,
    declaration: NodeId,
) -> Option<JavaScriptAssignmentKind> {
    match arena.get(declaration).map(|node| &node.data)? {
        NodeData::BinaryExpression(binary)
            if arena
                .get(binary.operator_token)
                .is_some_and(|operator| operator.kind == SyntaxKind::EqualsToken) =>
        {
            if is_module_exports_access(arena, binary.left)
                && !is_exports_identifier(arena, binary.right)
            {
                return Some(JavaScriptAssignmentKind::ModuleExports);
            }
            let base = access_expression_base(arena, binary.left)?;
            if (is_exports_identifier(arena, base) || is_module_exports_access(arena, base))
                && element_or_property_access_name(arena, binary.left).is_some()
            {
                Some(JavaScriptAssignmentKind::ExportsProperty)
            } else if arena
                .get(base)
                .is_some_and(|base| base.kind == SyntaxKind::ThisKeyword)
            {
                Some(JavaScriptAssignmentKind::ThisProperty)
            } else if is_entity_name_expression_ex(arena, base, true) {
                Some(JavaScriptAssignmentKind::ExpandoProperty)
            } else {
                None
            }
        }
        NodeData::CallExpression(call)
            if is_bindable_object_define_property_call(arena, declaration) =>
        {
            let receiver = call.arguments.nodes[0];
            Some(
                if is_exports_identifier(arena, receiver)
                    || is_module_exports_access(arena, receiver)
                {
                    JavaScriptAssignmentKind::ExportsProperty
                } else {
                    JavaScriptAssignmentKind::ExpandoProperty
                },
            )
        }
        _ => None,
    }
}

fn is_javascript_require_call(arena: &NodeArena, node: NodeId) -> bool {
    let Some(NodeData::CallExpression(call)) = arena.get(node).map(|node| &node.data) else {
        return false;
    };
    call.arguments.nodes.len() == 1
        && arena
            .get(call.expression)
            .is_some_and(|expression| expression.kind == SyntaxKind::Identifier)
        && node_text(arena, call.expression).as_deref() == Some("require")
}

fn has_javascript_type_annotation(arena: &NodeArena, declaration: NodeId) -> bool {
    let Some(record) = arena.get(declaration) else {
        return false;
    };
    if matches!(&record.data, NodeData::VariableDeclaration(variable) if variable.type_.is_some()) {
        return true;
    }
    let mut host = declaration;
    while let Some(parent) = arena.get(host).and_then(|node| node.parent) {
        if arena.get(parent).is_some_and(|parent| {
            matches!(
                parent.kind,
                SyntaxKind::VariableStatement | SyntaxKind::ExpressionStatement
            )
        }) {
            host = parent;
            break;
        }
        if arena.get(parent).is_some_and(|parent| {
            !matches!(
                parent.kind,
                SyntaxKind::VariableDeclarationList | SyntaxKind::ParenthesizedExpression
            )
        }) {
            break;
        }
        host = parent;
    }
    let Some(source) = arena.source_text() else {
        return false;
    };
    let Some(start) = arena
        .get(host)
        .and_then(|node| usize::try_from(node.range.start.get()).ok())
    else {
        return false;
    };
    let prefix = source.get(..start).unwrap_or_default().trim_end();
    if !prefix.ends_with("*/") {
        return false;
    }
    let Some(comment_start) = prefix.rfind("/**") else {
        return false;
    };
    prefix[comment_start..]
        .match_indices("@type")
        .any(|(index, _)| {
            prefix[comment_start + index + "@type".len()..]
                .chars()
                .next()
                .is_some_and(|next| next.is_whitespace() || next == '{')
        })
}

fn assignment_name_requires_javascript_file_kind(arena: &NodeArena, declaration: NodeId) -> bool {
    let Some(node) = arena.get(declaration) else {
        return false;
    };
    match &node.data {
        NodeData::BinaryExpression(binary)
            if arena
                .get(binary.operator_token)
                .is_some_and(|operator| operator.kind == SyntaxKind::EqualsToken) =>
        {
            if is_module_exports_access(arena, binary.left)
                && !is_exports_identifier(arena, binary.right)
            {
                return true;
            }
            let Some(base) = access_expression_base(arena, binary.left) else {
                return false;
            };
            !is_entity_name_expression(arena, base)
                && (is_entity_name_expression_ex(arena, base, true)
                    || (is_module_exports_access(arena, base)
                        && has_static_access_name(arena, binary.left)))
        }
        NodeData::CallExpression(_) => is_bindable_object_define_property_call(arena, declaration),
        _ => false,
    }
}

fn access_expression_base(arena: &NodeArena, node: NodeId) -> Option<NodeId> {
    match &arena.get(node)?.data {
        NodeData::PropertyAccessExpression(access) => Some(access.expression),
        NodeData::ElementAccessExpression(access) => Some(access.expression),
        _ => None,
    }
}

fn element_or_property_access_name(arena: &NodeArena, node: NodeId) -> Option<NodeId> {
    match arena.get(node).map(|node| &node.data) {
        Some(NodeData::PropertyAccessExpression(access))
            if arena
                .get(access.name)
                .is_some_and(|name| name.kind == SyntaxKind::Identifier) =>
        {
            Some(access.name)
        }
        Some(NodeData::ElementAccessExpression(access)) => {
            let name = skip_parentheses(arena, access.argument_expression)?;
            arena
                .get(name)
                .is_some_and(|name| is_string_or_numeric_literal_like(name.kind))
                .then_some(name)
        }
        _ => None,
    }
}

fn is_typescript_expando_property_assignment(arena: &NodeArena, node: NodeId) -> bool {
    let Some(NodeData::BinaryExpression(binary)) = arena.get(node).map(|node| &node.data) else {
        return false;
    };
    if !arena
        .get(binary.operator_token)
        .is_some_and(|operator| operator.kind == SyntaxKind::EqualsToken)
    {
        return false;
    }
    match arena.get(binary.left).map(|left| &left.data) {
        Some(NodeData::PropertyAccessExpression(access)) => {
            arena
                .get(access.name)
                .is_some_and(|name| name.kind == SyntaxKind::Identifier)
                && is_entity_name_expression(arena, access.expression)
        }
        Some(NodeData::ElementAccessExpression(access)) => {
            is_entity_name_expression(arena, access.expression)
        }
        _ => false,
    }
}

fn expando_assignment_parent(arena: &NodeArena, node: NodeId) -> Option<NodeId> {
    match &arena.get(node)?.data {
        NodeData::BinaryExpression(binary) => access_expression_base(arena, binary.left),
        NodeData::CallExpression(call) => call.arguments.nodes.first().copied(),
        _ => None,
    }
}

fn has_static_access_name(arena: &NodeArena, node: NodeId) -> bool {
    match arena.get(node).map(|node| &node.data) {
        Some(NodeData::PropertyAccessExpression(access)) => arena
            .get(access.name)
            .is_some_and(|name| name.kind == SyntaxKind::Identifier),
        Some(NodeData::ElementAccessExpression(access)) => {
            skip_parentheses(arena, access.argument_expression)
                .and_then(|name| arena.get(name))
                .is_some_and(|name| is_string_or_numeric_literal_like(name.kind))
        }
        _ => false,
    }
}

fn is_exports_identifier(arena: &NodeArena, node: NodeId) -> bool {
    arena
        .get(node)
        .is_some_and(|node| node.kind == SyntaxKind::Identifier)
        && node_text(arena, node).as_deref() == Some("exports")
}

fn is_module_exports_access(arena: &NodeArena, node: NodeId) -> bool {
    let (base, name) = match arena.get(node).map(|node| &node.data) {
        Some(NodeData::PropertyAccessExpression(access))
            if arena
                .get(access.name)
                .is_some_and(|name| name.kind == SyntaxKind::Identifier) =>
        {
            (access.expression, access.name)
        }
        Some(NodeData::ElementAccessExpression(access)) => {
            let Some(name) = skip_parentheses(arena, access.argument_expression) else {
                return false;
            };
            if !arena
                .get(name)
                .is_some_and(|name| is_string_or_numeric_literal_like(name.kind))
            {
                return false;
            }
            (access.expression, name)
        }
        _ => return false,
    };
    arena
        .get(base)
        .is_some_and(|base| base.kind == SyntaxKind::Identifier)
        && node_text(arena, base).as_deref() == Some("module")
        && node_text(arena, name).as_deref() == Some("exports")
}

fn is_bindable_object_define_property_call(arena: &NodeArena, node: NodeId) -> bool {
    let Some(NodeData::CallExpression(call)) = arena.get(node).map(|node| &node.data) else {
        return false;
    };
    if call.arguments.nodes.len() != 3 {
        return false;
    }
    let Some(NodeData::PropertyAccessExpression(expression)) =
        arena.get(call.expression).map(|node| &node.data)
    else {
        return false;
    };
    arena
        .get(expression.expression)
        .is_some_and(|base| base.kind == SyntaxKind::Identifier)
        && node_text(arena, expression.expression).as_deref() == Some("Object")
        && node_text(arena, expression.name).as_deref() == Some("defineProperty")
        && arena
            .get(call.arguments.nodes[1])
            .is_some_and(|name| is_string_or_numeric_literal_like(name.kind))
        && is_bindable_static_name_expression(arena, call.arguments.nodes[0], true)
}

fn is_bindable_static_name_expression(
    arena: &NodeArena,
    node: NodeId,
    exclude_this_keyword: bool,
) -> bool {
    is_entity_name_expression(arena, node)
        || is_bindable_static_access_expression(arena, node, exclude_this_keyword)
}

fn is_bindable_static_access_expression(
    arena: &NodeArena,
    node: NodeId,
    exclude_this_keyword: bool,
) -> bool {
    let Some(base) = (match arena.get(node).map(|node| &node.data) {
        Some(NodeData::PropertyAccessExpression(access))
            if arena
                .get(access.name)
                .is_some_and(|name| name.kind == SyntaxKind::Identifier) =>
        {
            Some(access.expression)
        }
        Some(NodeData::ElementAccessExpression(access))
            if arena
                .get(access.argument_expression)
                .is_some_and(|argument| is_string_or_numeric_literal_like(argument.kind)) =>
        {
            Some(access.expression)
        }
        _ => None,
    }) else {
        return false;
    };
    (!exclude_this_keyword
        && arena
            .get(base)
            .is_some_and(|base| base.kind == SyntaxKind::ThisKeyword))
        || is_entity_name_expression(arena, base)
        || is_bindable_static_access_expression(arena, base, true)
}

fn is_entity_name_expression(arena: &NodeArena, node: NodeId) -> bool {
    is_entity_name_expression_ex(arena, node, false)
}

fn is_entity_name_expression_ex(arena: &NodeArena, node: NodeId, allow_js: bool) -> bool {
    arena.get(node).is_some_and(|node| match &node.data {
        NodeData::Identifier(_) => true,
        NodeData::PropertyAccessExpression(access) => {
            arena
                .get(access.name)
                .is_some_and(|name| name.kind == SyntaxKind::Identifier)
                && is_entity_name_expression_ex(arena, access.expression, allow_js)
        }
        NodeData::ElementAccessExpression(access) if allow_js => {
            arena
                .get(access.argument_expression)
                .is_some_and(|argument| is_string_or_numeric_literal_like(argument.kind))
                && is_entity_name_expression_ex(arena, access.expression, true)
        }
        NodeData::KeywordExpression(_) if allow_js && node.kind == SyntaxKind::ThisKeyword => true,
        _ => false,
    })
}

fn skip_parentheses(arena: &NodeArena, mut node: NodeId) -> Option<NodeId> {
    while let NodeData::ParenthesizedExpression(parenthesized) = &arena.get(node)?.data {
        node = parenthesized.expression;
    }
    Some(node)
}

fn has_dynamic_name(arena: &NodeArena, declaration: NodeId) -> bool {
    let Some(name) = get_name_of_declaration(arena, declaration) else {
        return false;
    };
    let Some(name_node) = arena.get(name) else {
        return false;
    };
    let expression = match &name_node.data {
        NodeData::ComputedPropertyName(computed) => computed.expression,
        NodeData::ElementAccessExpression(access) => {
            let Some(argument) = skip_parentheses(arena, access.argument_expression) else {
                return true;
            };
            argument
        }
        _ => return false,
    };
    let Some(expression) = arena.get(expression) else {
        return true;
    };
    !(is_string_or_numeric_literal_like(expression.kind)
        || matches!(
            &expression.data,
            NodeData::PrefixUnaryExpression(unary)
                if matches!(unary.operator, SyntaxKind::PlusToken | SyntaxKind::MinusToken)
                    && arena
                        .get(unary.operand)
                        .is_some_and(|operand| operand.kind == SyntaxKind::NumericLiteral)
        ))
}

fn containing_class(arena: &NodeArena, declaration: NodeId) -> Option<NodeId> {
    let mut current = arena.get(declaration)?.parent;
    while let Some(node) = current {
        let record = arena.get(node)?;
        if matches!(
            record.kind,
            SyntaxKind::ClassDeclaration | SyntaxKind::ClassExpression
        ) {
            return Some(node);
        }
        current = record.parent;
    }
    None
}

fn modifier_list(data: &NodeData) -> Option<&ModifierList> {
    match data {
        NodeData::ArrowFunction(data) => data.modifiers.as_ref(),
        NodeData::BinaryExpression(data) => data.modifiers.as_ref(),
        NodeData::ClassDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ClassExpression(data) => data.modifiers.as_ref(),
        NodeData::ClassStaticBlockDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ConstructorDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ConstructorTypeNode(data) => data.modifiers.as_ref(),
        NodeData::EnumDeclaration(data) => data.modifiers.as_ref(),
        NodeData::EnumMember(data) => data.modifiers.as_ref(),
        NodeData::ExportAssignment(data) => data.modifiers.as_ref(),
        NodeData::ExportDeclaration(data) => data.modifiers.as_ref(),
        NodeData::FunctionDeclaration(data) => data.modifiers.as_ref(),
        NodeData::FunctionExpression(data) => data.modifiers.as_ref(),
        NodeData::FunctionTypeNode(data) => data.modifiers.as_ref(),
        NodeData::GetAccessorDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ImportDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ImportEqualsDeclaration(data) => data.modifiers.as_ref(),
        NodeData::IndexSignatureDeclaration(data) => data.modifiers.as_ref(),
        NodeData::InterfaceDeclaration(data) => data.modifiers.as_ref(),
        NodeData::MethodDeclaration(data) => data.modifiers.as_ref(),
        NodeData::MethodSignatureDeclaration(data) => data.modifiers.as_ref(),
        NodeData::MissingDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ModuleDeclaration(data) => data.modifiers.as_ref(),
        NodeData::NamespaceExportDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ParameterDeclaration(data) => data.modifiers.as_ref(),
        NodeData::PropertyAssignment(data) => data.modifiers.as_ref(),
        NodeData::PropertyDeclaration(data) => data.modifiers.as_ref(),
        NodeData::PropertySignatureDeclaration(data) => data.modifiers.as_ref(),
        NodeData::SetAccessorDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ShorthandPropertyAssignment(data) => data.modifiers.as_ref(),
        NodeData::TypeAliasDeclaration(data) => data.modifiers.as_ref(),
        NodeData::TypeParameterDeclaration(data) => data.modifiers.as_ref(),
        NodeData::VariableStatement(data) => data.modifiers.as_ref(),
        _ => None,
    }
}

fn has_syntactic_modifier(arena: &NodeArena, node: NodeId, modifier: SyntaxKind) -> bool {
    arena
        .get(node)
        .and_then(|node| modifier_list(&node.data))
        .is_some_and(|modifiers| {
            modifiers
                .list
                .nodes
                .iter()
                .any(|node| arena.get(*node).is_some_and(|node| node.kind == modifier))
        })
}

fn export_type_suggestion(arena: &NodeArena, node: NodeRef) -> Option<CanonicalRelatedInformation> {
    let declaration = arena.get(node.node)?;
    let NodeData::TypeAliasDeclaration(alias) = &declaration.data else {
        return None;
    };
    if !arena.get(alias.type_)?.range.is_empty()
        || !has_syntactic_modifier(arena, node.node, SyntaxKind::ExportKeyword)
    {
        return None;
    }
    let name = node_text(arena, alias.name)?;
    Some(CanonicalRelatedInformation {
        node,
        diagnostic: make_diagnostic(1369, [format!("export type {{ {name} }}")]),
    })
}

fn collect_children(
    arena: &NodeArena,
    file: FileId,
) -> Result<HashMap<NodeId, Vec<NodeId>>, CanonicalBindError> {
    let mut result = HashMap::with_capacity(arena.len());
    for (parent, node) in arena.iter() {
        if !node.data.matches_syntax_kind(node.kind) {
            return Err(CanonicalBindError::MismatchedNodeKind {
                node: NodeRef::new(arena.id(), file, parent),
                kind: node.kind,
                data: node.data.schema_name(),
            });
        }
        let mut children = Vec::new();
        node.for_each_child(|child| children.push(child));
        if let Some(child) = children
            .iter()
            .copied()
            .find(|child| arena.get(*child).is_none())
        {
            return Err(CanonicalBindError::MissingChild {
                parent: NodeRef::new(arena.id(), file, parent),
                child,
            });
        }
        result.insert(parent, children);
    }
    Ok(result)
}

fn validate_reachable_tree(
    arena: &NodeArena,
    source_file: NodeId,
    file: FileId,
    children: &HashMap<NodeId, Vec<NodeId>>,
) -> Result<(), CanonicalBindError> {
    let mut seen = vec![false; arena.len()];
    let mut pending = vec![(source_file, None)];
    while let Some((node_id, expected_parent)) = pending.pop() {
        if std::mem::replace(&mut seen[node_id.index()], true) {
            return Err(CanonicalBindError::RepeatedNode(NodeRef::new(
                arena.id(),
                file,
                node_id,
            )));
        }
        let node = arena
            .get(node_id)
            .expect("all generated child references were validated");
        let node_ref = NodeRef::new(arena.id(), file, node_id);
        if node.parent != expected_parent {
            return Err(CanonicalBindError::InvalidParent {
                node: node_ref,
                expected: expected_parent,
                actual: node.parent,
            });
        }
        pending.extend(
            children
                .get(&node_id)
                .expect("every arena node has a generated child entry")
                .iter()
                .rev()
                .map(|child| (*child, Some(node_id))),
        );
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Default)]
struct TraversalState {
    container: Option<NodeId>,
    block_scope_container: Option<NodeId>,
    this_container: Option<NodeId>,
}

#[derive(Clone, Copy, Debug)]
enum SeenThisBoundary {
    PassThrough,
    ControlFlow { saved: bool, propagates: bool },
    Interface { saved: bool },
}

#[derive(Clone, Copy, Debug)]
struct TraversalFrame {
    node: NodeId,
    state: TraversalState,
    seen_this_boundary: SeenThisBoundary,
}

struct FileTraversal<'a> {
    arena: &'a NodeArena,
    source_file: NodeId,
    source_facts: Option<CanonicalSourceFileFacts>,
    file: FileId,
    nodes: Vec<NodeBinding>,
    traversal_order: Vec<NodeId>,
    container_chain: Vec<NodeId>,
    last_container: Option<NodeId>,
    state: TraversalState,
    seen_this_keyword: bool,
    state_stack: Vec<TraversalFrame>,
}

impl<'a> FileTraversal<'a> {
    fn new(
        arena: &'a NodeArena,
        source_file: NodeId,
        file: FileId,
        source_facts: Option<CanonicalSourceFileFacts>,
    ) -> Self {
        Self {
            arena,
            source_file,
            source_facts,
            file,
            nodes: vec![NodeBinding::default(); arena.len()],
            traversal_order: Vec::with_capacity(arena.len()),
            container_chain: Vec::new(),
            last_container: None,
            state: TraversalState::default(),
            seen_this_keyword: false,
            state_stack: Vec::new(),
        }
    }

    fn finish(self, flow: BoundFlowGraph) -> BoundFile {
        assert!(
            self.state_stack.is_empty(),
            "canonical traversal exits every entered node"
        );
        assert!(
            !self.seen_this_keyword,
            "source-file ContainsThis capture restores the outer accumulator"
        );
        BoundFile {
            file: self.file,
            arena: self.arena.id(),
            arena_revision: self.arena.revision(),
            source_file: self.source_file,
            source_facts: self.source_facts,
            node_count: self.arena.len(),
            phase: BindingPhase::Traversal,
            declaration_slice_bound: false,
            nodes: self.nodes,
            traversal_order: self.traversal_order,
            container_chain: self.container_chain,
            diagnostics: Vec::new(),
            pattern_ambient_modules: Vec::new(),
            module_augmentations: Vec::new(),
            global_exports: None,
            classifiable_names: BTreeSet::new(),
            not_const_enum_only_modules: BTreeSet::new(),
            symbol_count: 0,
            flow,
        }
    }

    fn enter(&mut self, node_id: NodeId) {
        let binding = &mut self.nodes[node_id.index()];
        assert!(!binding.visited, "reachable tree was preflighted");

        // Pinned binder.go performs declaration work before bindContainer.
        // Capture the state at that exact boundary for B02.
        *binding = NodeBinding {
            visited: true,
            container: self.state.container,
            block_scope_container: self.state.block_scope_container,
            this_container: self.state.this_container,
            ..NodeBinding::default()
        };
        self.traversal_order.push(node_id);

        let kind = self
            .arena
            .get(node_id)
            .expect("reachable tree was preflighted")
            .kind;
        if matches!(kind, SyntaxKind::ThisKeyword | SyntaxKind::ThisType) {
            self.seen_this_keyword = true;
        }

        let flags = container_flags(self.arena, node_id);
        let saved_state = self.state;
        if flags.contains(ContainerFlags::IS_CONTAINER) {
            self.state.container = Some(node_id);
            self.state.block_scope_container = Some(node_id);
            if flags.contains(ContainerFlags::HAS_LOCALS) {
                self.add_to_container_chain(node_id);
            }
        } else if flags.contains(ContainerFlags::IS_BLOCK_SCOPED_CONTAINER) {
            self.state.block_scope_container = Some(node_id);
            // Block locals are intentionally lazy. Joining the chain must not
            // collapse nil into an allocated empty table.
            self.add_to_container_chain(node_id);
        }
        if flags.contains(ContainerFlags::IS_THIS_CONTAINER) {
            self.state.this_container = Some(node_id);
        }

        let seen_this_boundary = if flags.contains(ContainerFlags::IS_CONTROL_FLOW_CONTAINER) {
            let saved = self.seen_this_keyword;
            self.seen_this_keyword = false;
            SeenThisBoundary::ControlFlow {
                saved,
                propagates: flags.contains(ContainerFlags::PROPAGATES_THIS_KEYWORD),
            }
        } else if flags.contains(ContainerFlags::IS_INTERFACE) {
            let saved = self.seen_this_keyword;
            self.seen_this_keyword = false;
            SeenThisBoundary::Interface { saved }
        } else {
            SeenThisBoundary::PassThrough
        };
        self.state_stack.push(TraversalFrame {
            node: node_id,
            state: saved_state,
            seen_this_boundary,
        });
    }

    fn exit(&mut self, node_id: NodeId) {
        let frame = self
            .state_stack
            .pop()
            .expect("every canonical exit has a matching enter");
        assert_eq!(
            frame.node, node_id,
            "canonical traversal exits in stack order"
        );
        match frame.seen_this_boundary {
            SeenThisBoundary::PassThrough => {}
            SeenThisBoundary::ControlFlow { saved, propagates } => {
                let captured = self.seen_this_keyword;
                self.nodes[node_id.index()].contains_this = captured;
                self.seen_this_keyword = if propagates { saved || captured } else { saved };
            }
            SeenThisBoundary::Interface { saved } => {
                self.nodes[node_id.index()].contains_this = self.seen_this_keyword;
                self.seen_this_keyword = saved;
            }
        }
        self.state = frame.state;
    }

    fn add_to_container_chain(&mut self, node: NodeId) {
        if let Some(previous) = self.last_container {
            self.nodes[previous.index()].next_container = Some(node);
        }
        self.last_container = Some(node);
        self.container_chain.push(node);
    }
}

impl FlowTraversalHooks for FileTraversal<'_> {
    fn enter_node(&mut self, node: NodeId) {
        self.enter(node);
    }

    fn exit_node(&mut self, node: NodeId) {
        self.exit(node);
    }
}

#[derive(Clone, Copy)]
struct ContainerFlags(u16);

impl ContainerFlags {
    const NONE: Self = Self(0);
    const IS_CONTAINER: Self = Self(1 << 0);
    const IS_BLOCK_SCOPED_CONTAINER: Self = Self(1 << 1);
    const IS_CONTROL_FLOW_CONTAINER: Self = Self(1 << 2);
    const IS_FUNCTION_LIKE: Self = Self(1 << 3);
    const IS_FUNCTION_EXPRESSION: Self = Self(1 << 4);
    const HAS_LOCALS: Self = Self(1 << 5);
    const IS_INTERFACE: Self = Self(1 << 6);
    const IS_OBJECT_LITERAL_OR_CLASS_EXPRESSION_METHOD_OR_ACCESSOR: Self = Self(1 << 7);
    const IS_THIS_CONTAINER: Self = Self(1 << 8);
    const PROPAGATES_THIS_KEYWORD: Self = Self(1 << 9);

    const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }
}

impl std::ops::BitOr for ContainerFlags {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

#[allow(clippy::match_same_arms)] // Arms mirror pinned binder.go::GetContainerFlags.
fn container_flags(arena: &NodeArena, node_id: NodeId) -> ContainerFlags {
    let node = arena
        .get(node_id)
        .expect("container classification only runs for validated nodes");
    match node.kind {
        SyntaxKind::ClassExpression
        | SyntaxKind::ClassDeclaration
        | SyntaxKind::EnumDeclaration
        | SyntaxKind::ObjectLiteralExpression
        | SyntaxKind::TypeLiteral
        | SyntaxKind::JsxAttributes => ContainerFlags::IS_CONTAINER,
        SyntaxKind::InterfaceDeclaration => {
            ContainerFlags::IS_CONTAINER | ContainerFlags::IS_INTERFACE
        }
        SyntaxKind::ModuleDeclaration
        | SyntaxKind::TypeAliasDeclaration
        | SyntaxKind::JsTypeAliasDeclaration
        | SyntaxKind::MappedType
        | SyntaxKind::IndexSignature => ContainerFlags::IS_CONTAINER | ContainerFlags::HAS_LOCALS,
        SyntaxKind::SourceFile => {
            ContainerFlags::IS_CONTAINER
                | ContainerFlags::IS_CONTROL_FLOW_CONTAINER
                | ContainerFlags::HAS_LOCALS
        }
        SyntaxKind::GetAccessor | SyntaxKind::SetAccessor | SyntaxKind::MethodDeclaration
            if is_object_literal_or_class_expression_method_or_accessor(arena, node_id) =>
        {
            ContainerFlags::IS_CONTAINER
                | ContainerFlags::IS_CONTROL_FLOW_CONTAINER
                | ContainerFlags::HAS_LOCALS
                | ContainerFlags::IS_FUNCTION_LIKE
                | ContainerFlags::IS_OBJECT_LITERAL_OR_CLASS_EXPRESSION_METHOD_OR_ACCESSOR
                | ContainerFlags::IS_THIS_CONTAINER
        }
        SyntaxKind::GetAccessor
        | SyntaxKind::SetAccessor
        | SyntaxKind::MethodDeclaration
        | SyntaxKind::Constructor
        | SyntaxKind::FunctionDeclaration
        | SyntaxKind::ClassStaticBlockDeclaration => {
            ContainerFlags::IS_CONTAINER
                | ContainerFlags::IS_CONTROL_FLOW_CONTAINER
                | ContainerFlags::HAS_LOCALS
                | ContainerFlags::IS_FUNCTION_LIKE
                | ContainerFlags::IS_THIS_CONTAINER
        }
        SyntaxKind::MethodSignature
        | SyntaxKind::CallSignature
        | SyntaxKind::FunctionType
        | SyntaxKind::ConstructSignature
        | SyntaxKind::ConstructorType => {
            ContainerFlags::IS_CONTAINER
                | ContainerFlags::IS_CONTROL_FLOW_CONTAINER
                | ContainerFlags::HAS_LOCALS
                | ContainerFlags::IS_FUNCTION_LIKE
                | ContainerFlags::PROPAGATES_THIS_KEYWORD
        }
        SyntaxKind::FunctionExpression => {
            ContainerFlags::IS_CONTAINER
                | ContainerFlags::IS_CONTROL_FLOW_CONTAINER
                | ContainerFlags::HAS_LOCALS
                | ContainerFlags::IS_FUNCTION_LIKE
                | ContainerFlags::IS_FUNCTION_EXPRESSION
                | ContainerFlags::IS_THIS_CONTAINER
        }
        SyntaxKind::ArrowFunction => {
            ContainerFlags::IS_CONTAINER
                | ContainerFlags::IS_CONTROL_FLOW_CONTAINER
                | ContainerFlags::HAS_LOCALS
                | ContainerFlags::IS_FUNCTION_LIKE
                | ContainerFlags::IS_FUNCTION_EXPRESSION
                | ContainerFlags::PROPAGATES_THIS_KEYWORD
        }
        SyntaxKind::ModuleBlock => ContainerFlags::IS_CONTROL_FLOW_CONTAINER,
        SyntaxKind::PropertyDeclaration
            if matches!(
                &node.data,
                NodeData::PropertyDeclaration(data) if data.initializer.is_some()
            ) =>
        {
            ContainerFlags::IS_CONTROL_FLOW_CONTAINER | ContainerFlags::IS_THIS_CONTAINER
        }
        SyntaxKind::CatchClause
        | SyntaxKind::ForStatement
        | SyntaxKind::ForInStatement
        | SyntaxKind::ForOfStatement
        | SyntaxKind::CaseBlock => {
            ContainerFlags::IS_BLOCK_SCOPED_CONTAINER | ContainerFlags::HAS_LOCALS
        }
        SyntaxKind::Block
            if !node.parent.is_some_and(|parent| {
                arena.get(parent).is_some_and(|parent| {
                    is_function_like_kind(parent.kind)
                        || parent.kind == SyntaxKind::ClassStaticBlockDeclaration
                })
            }) =>
        {
            ContainerFlags::IS_BLOCK_SCOPED_CONTAINER | ContainerFlags::HAS_LOCALS
        }
        _ => ContainerFlags::NONE,
    }
}

fn is_object_literal_or_class_expression_method_or_accessor(
    arena: &NodeArena,
    node: NodeId,
) -> bool {
    arena
        .get(node)
        .and_then(|node| node.parent)
        .and_then(|parent| arena.get(parent))
        .is_some_and(|parent| {
            matches!(
                parent.kind,
                SyntaxKind::ObjectLiteralExpression | SyntaxKind::ClassExpression
            )
        })
}

fn is_function_like_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::FunctionDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::Constructor
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ArrowFunction
            | SyntaxKind::MethodSignature
            | SyntaxKind::CallSignature
            | SyntaxKind::JsDocSignature
            | SyntaxKind::ConstructSignature
            | SyntaxKind::IndexSignature
            | SyntaxKind::FunctionType
            | SyntaxKind::ConstructorType
    )
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet, panic::AssertUnwindSafe};

    use ts_ast::{FileId, NodeData, NodeFlags, NodeId, NodeRef, SyntaxKind};
    use ts_parser::{
        ParseResult, parse_javascript_source_file, parse_jsx_source_file, parse_source_file,
    };

    use super::{
        BindingPhase, CanonicalBindError, CanonicalBinder, CanonicalDeclarationError,
        CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage, node_text,
    };
    use crate::{EscapedName, InternalSymbolName, SymbolFlags};

    fn position(order: &[NodeRef], node: NodeId) -> usize {
        order
            .iter()
            .position(|visited| visited.node == node)
            .expect("test node is reachable")
    }

    fn reachable_nodes(arena: &ts_ast::NodeArena, root: NodeId) -> BTreeSet<NodeId> {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            assert!(reachable.insert(node));
            arena
                .get(node)
                .unwrap()
                .for_each_child(|child| pending.push(child));
        }
        reachable
    }

    fn nodes_of_kind(arena: &ts_ast::NodeArena, kind: SyntaxKind) -> Vec<NodeId> {
        arena
            .iter()
            .filter_map(|(id, node)| (node.kind == kind).then_some(id))
            .collect()
    }

    fn node_ref(arena: &ts_ast::NodeArena, file: FileId, node: NodeId) -> NodeRef {
        NodeRef::new(arena.id(), file, node)
    }

    fn node_with_source(arena: &ts_ast::NodeArena, kind: SyntaxKind, source: &str) -> NodeId {
        arena
            .iter()
            .find_map(|(id, node)| {
                (node.kind == kind && super::source_text_of_node(arena, node) == Some(source))
                    .then_some(id)
            })
            .unwrap_or_else(|| panic!("missing {kind:?} with source {source:?}"))
    }

    fn node_with_source_fragment(
        arena: &ts_ast::NodeArena,
        kind: SyntaxKind,
        fragment: &str,
    ) -> NodeId {
        arena
            .iter()
            .find_map(|(id, node)| {
                (node.kind == kind
                    && super::source_text_of_node(arena, node)
                        .is_some_and(|source| source.contains(fragment)))
                .then_some(id)
            })
            .unwrap_or_else(|| panic!("missing {kind:?} containing {fragment:?}"))
    }

    fn assert_focused_declaration_rejects_stale_revision(
        mut parsed: ParseResult,
        file: FileId,
        mutate: impl FnOnce(&mut ts_ast::NodeArena),
    ) {
        let declaration = nodes_of_kind(&parsed.arena, SyntaxKind::VariableDeclaration)[0];
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let table = binder.create_symbol_table();
        let before_file = binder.file(file).unwrap().clone();
        let expected = before_file.node_arena_revision();
        let symbol_count = binder.symbol_store().symbol_len();
        let table_count = binder.symbol_store().symbol_table_len();
        let declaration_fact_count = binder.declaration_facts.len();

        mutate(&mut parsed.arena);
        let actual = parsed.arena.revision();
        assert_ne!(actual, expected);
        assert_eq!(
            binder.declare_symbol(
                &parsed.arena,
                file,
                table,
                None,
                declaration,
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
                SymbolFlags::BLOCK_SCOPED_VARIABLE_EXCLUDES,
            ),
            Err(CanonicalDeclarationError::ArenaRevisionMismatch {
                file,
                expected,
                actual,
            })
        );
        assert_eq!(binder.file(file), Some(&before_file));
        assert_eq!(binder.symbol_store().symbol_len(), symbol_count);
        assert_eq!(binder.symbol_store().symbol_table_len(), table_count);
        assert_eq!(binder.declaration_facts.len(), declaration_fact_count);
    }

    fn variable_initializers_named(arena: &ts_ast::NodeArena, expected: &str) -> Vec<NodeId> {
        arena
            .iter()
            .filter_map(|(_, node)| {
                let NodeData::VariableDeclaration(variable) = &node.data else {
                    return None;
                };
                (super::node_text(arena, variable.name).as_deref() == Some(expected))
                    .then_some(variable.initializer)
                    .flatten()
            })
            .collect()
    }

    fn assert_contains_this(
        bound: &super::BoundFile,
        arena: &ts_ast::NodeArena,
        file: FileId,
        node: NodeId,
        expected: bool,
    ) {
        assert_eq!(
            bound.contains_this(node_ref(arena, file, node)),
            Some(expected)
        );
    }

    fn assert_contains_this_type_capture_matrix(
        bound: &super::BoundFile,
        arena: &ts_ast::NodeArena,
        file: FileId,
    ) {
        for (fragment, expected) in [
            ("interface Empty", false),
            ("interface Direct", true),
            ("interface Signatures", true),
            ("interface Nested", true),
        ] {
            let node = node_with_source_fragment(arena, SyntaxKind::InterfaceDeclaration, fragment);
            assert_contains_this(bound, arena, file, node, expected);
        }

        for kind in [
            SyntaxKind::CallSignature,
            SyntaxKind::ConstructSignature,
            SyntaxKind::MethodSignature,
            SyntaxKind::FunctionType,
            SyntaxKind::ConstructorType,
        ] {
            let nodes = nodes_of_kind(arena, kind);
            assert_eq!(nodes.len(), 1, "fixture has one {kind:?}");
            assert_contains_this(bound, arena, file, nodes[0], true);
        }

        let index_signature = nodes_of_kind(arena, SyntaxKind::IndexSignature);
        assert_eq!(index_signature.len(), 1);
        assert_contains_this(bound, arena, file, index_signature[0], false);
        assert!(
            nodes_of_kind(arena, SyntaxKind::ThisType)
                .into_iter()
                .all(|node| bound.contains_this(node_ref(arena, file, node)) == Some(false)),
            "this type nodes update the accumulator but are not capture boundaries"
        );
    }

    fn assert_contains_this_value_capture_matrix(
        bound: &super::BoundFile,
        arena: &ts_ast::NodeArena,
        source_file: NodeId,
        file: FileId,
    ) {
        let arrow = nodes_of_kind(arena, SyntaxKind::ArrowFunction);
        assert_eq!(arrow.len(), 1);
        assert_contains_this(bound, arena, file, arrow[0], true);
        let arrow_outer = node_with_source_fragment(
            arena,
            SyntaxKind::FunctionDeclaration,
            "function arrowOuter",
        );
        assert_contains_this(bound, arena, file, arrow_outer, true);

        let function_expression = nodes_of_kind(arena, SyntaxKind::FunctionExpression);
        assert_eq!(function_expression.len(), 1);
        assert_contains_this(bound, arena, file, function_expression[0], true);
        for fragment in ["function ordinaryOuter", "function interfaceOuter"] {
            let node = node_with_source_fragment(arena, SyntaxKind::FunctionDeclaration, fragment);
            assert_contains_this(bound, arena, file, node, false);
        }

        let base_method = node_with_source(arena, SyntaxKind::MethodDeclaration, "method() {}");
        assert_contains_this(bound, arena, file, base_method, false);
        for (fragment, expected) in [("onlySuper()", false), ("hasThis()", true)] {
            let node = node_with_source_fragment(arena, SyntaxKind::MethodDeclaration, fragment);
            assert_contains_this(bound, arena, file, node, expected);
        }
        assert_contains_this(bound, arena, file, source_file, false);

        assert!(
            nodes_of_kind(arena, SyntaxKind::ThisKeyword)
                .into_iter()
                .all(|node| bound.contains_this(node_ref(arena, file, node)) == Some(false)),
            "this keyword nodes update the accumulator but are not capture boundaries"
        );
        let super_keyword = nodes_of_kind(arena, SyntaxKind::SuperKeyword);
        assert_eq!(super_keyword.len(), 1);
        assert_contains_this(bound, arena, file, super_keyword[0], false);
    }

    #[test]
    fn contains_this_matches_pinned_capture_and_propagation_matrix() {
        let parsed = parse_source_file(
            r"
                interface Empty {}
                interface Direct { value: this }
                interface Signatures {
                    (): this;
                    new (): this;
                    method(): this;
                    fn: () => this;
                    ctor: new () => this;
                    [key: string]: this;
                }

                function arrowOuter() {
                    const arrow = () => this;
                }
                function ordinaryOuter() {
                    const ordinary = function () { return this; };
                }
                function interfaceOuter() {
                    interface Nested { value: this }
                }

                class Base { method() {} }
                class Derived extends Base {
                    onlySuper() { return super.method(); }
                    hasThis() { return this; }
                }
            ",
        );
        let file = FileId::new(80);
        let mut binder = CanonicalBinder::new();
        let bound = binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        assert_contains_this_type_capture_matrix(bound, &parsed.arena, file);
        assert_contains_this_value_capture_matrix(bound, &parsed.arena, parsed.source_file, file);
    }

    #[test]
    fn contains_this_captures_remaining_non_propagating_control_flow_boundaries() {
        let parsed = parse_source_file(
            r"
                namespace Nested { this; }
                class Container {
                    field = this;
                    constructor() { this; }
                    get value() { return this; }
                    set value(next: unknown) { this; }
                    static { this; }
                }
            ",
        );
        let file = FileId::new(86);
        let mut binder = CanonicalBinder::new();
        let bound = binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();

        for kind in [
            SyntaxKind::ModuleBlock,
            SyntaxKind::PropertyDeclaration,
            SyntaxKind::Constructor,
            SyntaxKind::GetAccessor,
            SyntaxKind::SetAccessor,
            SyntaxKind::ClassStaticBlockDeclaration,
        ] {
            let nodes = nodes_of_kind(&parsed.arena, kind);
            assert_eq!(nodes.len(), 1, "fixture has one {kind:?}");
            assert_contains_this(bound, &parsed.arena, file, nodes[0], true);
        }
        assert_contains_this(bound, &parsed.arena, file, parsed.source_file, false);

        let top_level = parse_source_file("this;");
        let top_level_file = FileId::new(87);
        let mut top_level_binder = CanonicalBinder::new();
        let top_level_bound = top_level_binder
            .bind_source_file(&top_level.arena, top_level.source_file, top_level_file)
            .unwrap();
        assert_contains_this(
            top_level_bound,
            &top_level.arena,
            top_level_file,
            top_level.source_file,
            true,
        );
    }

    #[test]
    fn contains_this_side_data_ignores_stale_ast_bits() {
        let mut parsed = parse_source_file("interface Empty {}");
        let interface = nodes_of_kind(&parsed.arena, SyntaxKind::InterfaceDeclaration)[0];
        parsed.arena.get_mut(interface).unwrap().flags.0 |= NodeFlags::CONTAINS_THIS.0;
        let file = FileId::new(81);
        let mut binder = CanonicalBinder::new();
        let bound = binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();

        assert_ne!(
            parsed.arena.get(interface).unwrap().flags.0 & NodeFlags::CONTAINS_THIS.0,
            0
        );
        assert_eq!(
            bound.contains_this(node_ref(&parsed.arena, file, interface)),
            Some(false),
            "canonical binding owns the fact instead of trusting parser flags"
        );
    }

    #[test]
    fn contains_this_queries_are_provenance_safe_and_stable_through_extraction() {
        let parsed = parse_source_file("interface Box { value: this }");
        let other = parse_source_file("");
        let file = FileId::new(82);
        let interface = nodes_of_kind(&parsed.arena, SyntaxKind::InterfaceDeclaration)[0];
        let name = node_with_source(&parsed.arena, SyntaxKind::Identifier, "Box");
        let interface_ref = node_ref(&parsed.arena, file, interface);
        let facts = CanonicalSourceFileFacts::new(
            EscapedName::source("\"/project/box.ts\""),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::Script,
        );
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts)
            .unwrap();

        let bound = binder.file(file).unwrap();
        assert_eq!(bound.phase(), BindingPhase::Traversal);
        assert_eq!(bound.contains_this(interface_ref), Some(true));
        assert_eq!(
            bound.contains_this(node_ref(&parsed.arena, file, name)),
            Some(false)
        );
        assert_eq!(
            bound.contains_this(NodeRef::new(parsed.arena.id(), FileId::new(83), interface)),
            None
        );
        assert_eq!(
            bound.contains_this(NodeRef::new(other.arena.id(), file, interface)),
            None
        );
        assert_eq!(
            bound.contains_this(NodeRef::new(
                parsed.arena.id(),
                file,
                NodeId::new(u32::try_from(parsed.arena.len()).unwrap()),
            )),
            None
        );

        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let bound = binder.file(file).unwrap();
        assert_eq!(bound.phase(), BindingPhase::Declarations);
        assert_eq!(bound.contains_this(interface_ref), Some(true));

        let program = binder.finish();
        assert_eq!(
            program.file(file).unwrap().contains_this(interface_ref),
            Some(true)
        );
        let (_, files) = program.try_into_parts().unwrap();
        assert_eq!(
            files.get(&file).unwrap().contains_this(interface_ref),
            Some(true)
        );

        let mut detached = parse_source_file("interface Detached { value: this }");
        let detached_interface =
            nodes_of_kind(&detached.arena, SyntaxKind::InterfaceDeclaration)[0];
        match &mut detached.arena.get_mut(detached.source_file).unwrap().data {
            NodeData::SourceFile(source) => source.statements.nodes.clear(),
            _ => unreachable!(),
        }
        let detached_file = FileId::new(84);
        let mut detached_binder = CanonicalBinder::new();
        let detached_bound = detached_binder
            .bind_source_file(&detached.arena, detached.source_file, detached_file)
            .unwrap();
        assert_eq!(
            detached_bound.contains_this(node_ref(
                &detached.arena,
                detached_file,
                detached_interface,
            )),
            None,
            "valid same-arena slots remain None when traversal never reached them"
        );
    }

    #[test]
    fn contains_this_preflight_failure_is_atomic_and_retryable() {
        let mut parsed = parse_source_file("interface Box { value: this }");
        let source = parsed.source_file;
        let interface = nodes_of_kind(&parsed.arena, SyntaxKind::InterfaceDeclaration)[0];
        parsed.arena.get_mut(interface).unwrap().parent = None;
        let file = FileId::new(85);
        let interface_ref = node_ref(&parsed.arena, file, interface);
        let mut binder = CanonicalBinder::new();

        assert_eq!(
            binder.bind_source_file(&parsed.arena, source, file),
            Err(CanonicalBindError::InvalidParent {
                node: interface_ref,
                expected: Some(source),
                actual: None,
            })
        );
        assert!(binder.file(file).is_none());
        assert_eq!(binder.symbol_store().symbol_len(), 0);
        assert_eq!(binder.symbol_store().symbol_table_len(), 0);

        parsed.arena.get_mut(interface).unwrap().parent = Some(source);
        let bound = binder
            .bind_source_file(&parsed.arena, source, file)
            .unwrap();
        assert_eq!(bound.contains_this(interface_ref), Some(true));
    }

    #[test]
    fn full_declaration_dispatch_rejects_stale_identifier_text_without_binder_writes() {
        let mut parsed = parse_source_file("export interface Before { value: string }");
        let file = FileId::new(86);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/revision.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        let before_file = binder.file(file).unwrap().clone();
        let expected = before_file.node_arena_revision();
        let symbol_count = binder.symbol_store().symbol_len();
        let table_count = binder.symbol_store().symbol_table_len();
        let declaration_fact_count = binder.declaration_facts.len();

        let identifier = node_with_source(&parsed.arena, SyntaxKind::Identifier, "Before");
        let NodeData::Identifier(identifier_data) =
            &mut parsed.arena.get_mut(identifier).unwrap().data
        else {
            panic!("the selected node is an identifier");
        };
        identifier_data.text = "After".to_owned();
        let actual = parsed.arena.revision();

        assert_eq!(
            binder.bind_typescript_declaration_slice(&parsed.arena, file),
            Err(CanonicalDeclarationError::ArenaRevisionMismatch {
                file,
                expected,
                actual,
            })
        );
        assert_eq!(binder.file(file), Some(&before_file));
        assert_eq!(binder.symbol_store().symbol_len(), symbol_count);
        assert_eq!(binder.symbol_store().symbol_table_len(), table_count);
        assert_eq!(binder.declaration_facts.len(), declaration_fact_count);
    }

    #[test]
    fn focused_declaration_rejects_stale_modifier_and_literal_content_without_writes() {
        assert_focused_declaration_rejects_stale_revision(
            parse_source_file("export const value = 1;"),
            FileId::new(87),
            |arena| {
                let modifier = nodes_of_kind(arena, SyntaxKind::ExportKeyword)[0];
                arena.get_mut(modifier).unwrap().kind = SyntaxKind::DefaultKeyword;
            },
        );
        assert_focused_declaration_rejects_stale_revision(
            parse_source_file("const value = 'before';"),
            FileId::new(88),
            |arena| {
                let literal = nodes_of_kind(arena, SyntaxKind::StringLiteral)[0];
                let NodeData::StringLiteral(literal_data) =
                    &mut arena.get_mut(literal).unwrap().data
                else {
                    panic!("the selected node is a string literal");
                };
                literal_data.text = "after".to_owned();
            },
        );
    }

    #[test]
    fn declaration_primitive_inserts_merges_and_deduplicates_exactly() {
        let parsed = parse_source_file("let same; let same;");
        let declarations = nodes_of_kind(&parsed.arena, SyntaxKind::VariableDeclaration);
        assert_eq!(declarations.len(), 2);
        let file = FileId::new(20);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let table = binder.create_symbol_table();
        assert!(
            binder
                .symbol_store()
                .symbol_table(table)
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            binder
                .file(file)
                .unwrap()
                .locals(node_ref(&parsed.arena, file, parsed.source_file)),
            None
        );

        let first = binder
            .declare_symbol(
                &parsed.arena,
                file,
                table,
                None,
                declarations[0],
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES,
            )
            .unwrap();
        let second = binder
            .declare_symbol(
                &parsed.arena,
                file,
                table,
                None,
                declarations[1],
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES,
            )
            .unwrap();
        assert_eq!(first, second);
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(table)
                .unwrap()
                .get_source("same"),
            Some(first)
        );
        let symbol = binder.symbol_store().symbol(first).unwrap();
        assert_eq!(
            symbol.declarations(),
            Some(
                [
                    node_ref(&parsed.arena, file, declarations[0]),
                    node_ref(&parsed.arena, file, declarations[1]),
                ]
                .as_slice()
            )
        );
        assert_eq!(
            symbol.value_declaration(),
            Some(node_ref(&parsed.arena, file, declarations[0]))
        );
        assert_eq!(binder.file(file).unwrap().symbol_count(), 1);
        assert!(binder.file(file).unwrap().diagnostics().is_empty());

        let repeated = binder
            .declare_symbol(
                &parsed.arena,
                file,
                table,
                None,
                declarations[1],
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES,
            )
            .unwrap();
        assert_eq!(repeated, first);
        assert_eq!(
            binder
                .symbol_store()
                .symbol(first)
                .unwrap()
                .declarations()
                .unwrap()
                .len(),
            2
        );
        assert_eq!(binder.file(file).unwrap().symbol_count(), 1);
        assert_eq!(binder.file(file).unwrap().phase(), BindingPhase::Traversal);
    }

    #[test]
    fn missing_names_allocate_detached_symbols_without_touching_the_table() {
        let parsed = parse_source_file("{} {}");
        let blocks = nodes_of_kind(&parsed.arena, SyntaxKind::Block);
        assert_eq!(blocks.len(), 2);
        let file = FileId::new(21);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let table = binder.create_symbol_table();
        let first = binder
            .declare_symbol(
                &parsed.arena,
                file,
                table,
                None,
                blocks[0],
                SymbolFlags::NONE,
                SymbolFlags::NONE,
            )
            .unwrap();
        let second = binder
            .declare_symbol(
                &parsed.arena,
                file,
                table,
                None,
                blocks[1],
                SymbolFlags::NONE,
                SymbolFlags::NONE,
            )
            .unwrap();
        assert_ne!(first, second);
        assert!(
            binder
                .symbol_store()
                .symbol_table(table)
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            binder.symbol_store().symbol(first).unwrap().name(),
            InternalSymbolName::Missing.as_ref()
        );
        assert_eq!(binder.file(file).unwrap().symbol_count(), 2);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn replaceable_method_branches_preserve_pinned_early_return_and_displacement() {
        let parsed = parse_source_file("class C { same() {} same = 1; same() {} same = 2; }");
        let methods = nodes_of_kind(&parsed.arena, SyntaxKind::MethodDeclaration);
        let properties = nodes_of_kind(&parsed.arena, SyntaxKind::PropertyDeclaration);
        assert_eq!((methods.len(), properties.len()), (2, 2));
        let file = FileId::new(22);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();

        let early_table = binder.create_symbol_table();
        let retained = binder
            .declare_symbol(
                &parsed.arena,
                file,
                early_table,
                None,
                methods[0],
                SymbolFlags::METHOD,
                SymbolFlags::NONE,
            )
            .unwrap();
        let before_count = binder.file(file).unwrap().symbol_count();
        let skipped = binder
            .declare_symbol_ex(
                &parsed.arena,
                file,
                early_table,
                None,
                properties[0],
                SymbolFlags::PROPERTY | SymbolFlags::CLASS,
                SymbolFlags::METHOD,
                true,
                false,
            )
            .unwrap();
        assert_eq!(skipped, retained);
        assert_eq!(binder.file(file).unwrap().symbol_count(), before_count);
        assert_eq!(
            binder
                .file(file)
                .unwrap()
                .symbol(node_ref(&parsed.arena, file, properties[0])),
            None
        );
        assert_eq!(
            binder
                .symbol_store()
                .symbol(retained)
                .unwrap()
                .declarations()
                .unwrap(),
            [node_ref(&parsed.arena, file, methods[0])]
        );
        assert!(
            binder
                .file(file)
                .unwrap()
                .classifiable_names()
                .any(|name| name.as_utf8() == Some("same"))
        );

        let displacement_table = binder.create_symbol_table();
        let discarded = binder
            .declare_symbol_ex(
                &parsed.arena,
                file,
                displacement_table,
                None,
                properties[1],
                SymbolFlags::PROPERTY,
                SymbolFlags::NONE,
                true,
                false,
            )
            .unwrap();
        let replacement = binder
            .declare_symbol(
                &parsed.arena,
                file,
                displacement_table,
                None,
                methods[1],
                SymbolFlags::METHOD,
                SymbolFlags::PROPERTY,
            )
            .unwrap();
        assert_ne!(replacement, discarded);
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(displacement_table)
                .unwrap()
                .get_source("same"),
            Some(replacement)
        );
        assert!(
            binder
                .symbol_store()
                .symbol(discarded)
                .unwrap()
                .flags()
                .intersects(SymbolFlags::REPLACEABLE_BY_METHOD)
        );
        assert!(binder.file(file).unwrap().diagnostics().is_empty());
        assert_eq!(binder.file(file).unwrap().symbol_count(), 3);
    }

    #[test]
    fn ordinary_conflicts_diagnose_old_then_new_and_keep_the_table_entry() {
        let parsed = parse_source_file("let clash; class clash {}");
        let variable = nodes_of_kind(&parsed.arena, SyntaxKind::VariableDeclaration)[0];
        let class = nodes_of_kind(&parsed.arena, SyntaxKind::ClassDeclaration)[0];
        let file = FileId::new(23);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let table = binder.create_symbol_table();
        let retained = binder
            .declare_symbol(
                &parsed.arena,
                file,
                table,
                None,
                variable,
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
                SymbolFlags::BLOCK_SCOPED_VARIABLE_EXCLUDES,
            )
            .unwrap();
        let detached = binder
            .declare_symbol(
                &parsed.arena,
                file,
                table,
                None,
                class,
                SymbolFlags::CLASS,
                SymbolFlags::CLASS_EXCLUDES,
            )
            .unwrap();
        assert_ne!(retained, detached);
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(table)
                .unwrap()
                .get_source("clash"),
            Some(retained)
        );
        assert_eq!(
            binder
                .file(file)
                .unwrap()
                .symbol(node_ref(&parsed.arena, file, class)),
            Some(detached)
        );
        let diagnostics = binder.file(file).unwrap().diagnostics();
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2451, 2451]
        );
        assert_eq!(diagnostics[0].diagnostic.arguments, ["clash"]);
        assert_eq!(diagnostics[1].diagnostic.arguments, ["clash"]);
        assert_eq!(
            diagnostics[0].node.node,
            super::schema_declaration_name(&parsed.arena.get(variable).unwrap().data).unwrap()
        );
        assert_eq!(
            diagnostics[1].node.node,
            super::schema_declaration_name(&parsed.arena.get(class).unwrap().data).unwrap()
        );
        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.related_information.is_empty())
        );
        assert_eq!(binder.file(file).unwrap().symbol_count(), 2);
    }

    #[test]
    fn assignment_and_variable_flags_merge_in_both_directions() {
        let parsed = parse_source_file("let merge; let merge;");
        let declarations = nodes_of_kind(&parsed.arena, SyntaxKind::VariableDeclaration);
        let file = FileId::new(24);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();

        let assignment_first = binder.create_symbol_table();
        let first = binder
            .declare_symbol(
                &parsed.arena,
                file,
                assignment_first,
                None,
                declarations[0],
                SymbolFlags::ASSIGNMENT | SymbolFlags::PROPERTY,
                SymbolFlags::NONE,
            )
            .unwrap();
        let merged = binder
            .declare_symbol(
                &parsed.arena,
                file,
                assignment_first,
                None,
                declarations[1],
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::PROPERTY,
            )
            .unwrap();
        assert_eq!(merged, first);

        let variable_first = binder.create_symbol_table();
        let first = binder
            .declare_symbol(
                &parsed.arena,
                file,
                variable_first,
                None,
                declarations[0],
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::NONE,
            )
            .unwrap();
        let merged = binder
            .declare_symbol(
                &parsed.arena,
                file,
                variable_first,
                None,
                declarations[1],
                SymbolFlags::ASSIGNMENT | SymbolFlags::PROPERTY,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            )
            .unwrap();
        assert_eq!(merged, first);
        assert!(binder.file(file).unwrap().diagnostics().is_empty());
        assert_eq!(binder.file(file).unwrap().symbol_count(), 2);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn const_enum_only_clearing_and_value_declaration_precedence_match_pinned() {
        let parsed = parse_source_file(
            "namespace N {} function N() {} function M() {} namespace M {} identifier; let value;",
        );
        let modules = nodes_of_kind(&parsed.arena, SyntaxKind::ModuleDeclaration);
        let functions = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionDeclaration);
        let variable = nodes_of_kind(&parsed.arena, SyntaxKind::VariableDeclaration)[0];
        let identifier_expression =
            match &parsed.arena.get(parsed.source_file).expect("source").data {
                NodeData::SourceFile(source) => {
                    let statement = source.statements.nodes[4];
                    match &parsed.arena.get(statement).unwrap().data {
                        NodeData::ExpressionStatement(statement) => statement.expression,
                        _ => unreachable!(),
                    }
                }
                _ => unreachable!(),
            };
        let file = FileId::new(25);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let named = binder.create_symbol_table();

        let n = binder
            .declare_symbol(
                &parsed.arena,
                file,
                named,
                None,
                modules[0],
                SymbolFlags::VALUE_MODULE | SymbolFlags::CONST_ENUM_ONLY_MODULE,
                SymbolFlags::NONE,
            )
            .unwrap();
        assert_eq!(
            binder.symbol_store().symbol(n).unwrap().value_declaration(),
            Some(node_ref(&parsed.arena, file, modules[0]))
        );
        assert_eq!(
            binder
                .declare_symbol(
                    &parsed.arena,
                    file,
                    named,
                    None,
                    functions[0],
                    SymbolFlags::FUNCTION,
                    SymbolFlags::NONE,
                )
                .unwrap(),
            n
        );
        let n_record = binder.symbol_store().symbol(n).unwrap();
        assert!(
            !n_record
                .flags()
                .intersects(SymbolFlags::CONST_ENUM_ONLY_MODULE)
        );
        assert_eq!(
            n_record.value_declaration(),
            Some(node_ref(&parsed.arena, file, functions[0]))
        );
        assert!(binder.file(file).unwrap().is_not_const_enum_only_module(n));

        let m = binder
            .declare_symbol(
                &parsed.arena,
                file,
                named,
                None,
                functions[1],
                SymbolFlags::FUNCTION,
                SymbolFlags::NONE,
            )
            .unwrap();
        assert_eq!(
            binder
                .declare_symbol(
                    &parsed.arena,
                    file,
                    named,
                    None,
                    modules[1],
                    SymbolFlags::VALUE_MODULE,
                    SymbolFlags::NONE,
                )
                .unwrap(),
            m
        );
        assert_eq!(
            binder.symbol_store().symbol(m).unwrap().value_declaration(),
            Some(node_ref(&parsed.arena, file, functions[1]))
        );

        let computed = binder.create_symbol_table();
        let assignment = binder
            .declare_symbol_ex(
                &parsed.arena,
                file,
                computed,
                None,
                identifier_expression,
                SymbolFlags::PROPERTY,
                SymbolFlags::NONE,
                false,
                true,
            )
            .unwrap();
        assert_eq!(
            binder
                .declare_symbol_ex(
                    &parsed.arena,
                    file,
                    computed,
                    None,
                    variable,
                    SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                    SymbolFlags::NONE,
                    false,
                    true,
                )
                .unwrap(),
            assignment
        );
        assert_eq!(
            binder
                .symbol_store()
                .symbol(assignment)
                .unwrap()
                .value_declaration(),
            Some(node_ref(&parsed.arena, file, variable))
        );
    }

    #[test]
    fn accessor_widening_and_enum_conflicts_preserve_diagnostic_facts() {
        let parsed = parse_source_file(
            "class C { get x() { return 1; } x = 1; set x(v) {} } enum E {} class E {}",
        );
        let getter = nodes_of_kind(&parsed.arena, SyntaxKind::GetAccessor)[0];
        let setter = nodes_of_kind(&parsed.arena, SyntaxKind::SetAccessor)[0];
        let property = nodes_of_kind(&parsed.arena, SyntaxKind::PropertyDeclaration)[0];
        let enumeration = nodes_of_kind(&parsed.arena, SyntaxKind::EnumDeclaration)[0];
        let classes = nodes_of_kind(&parsed.arena, SyntaxKind::ClassDeclaration);
        let conflicting_class = classes[1];
        let file = FileId::new(26);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();

        let members = binder.create_symbol_table();
        let accessor = binder
            .declare_symbol(
                &parsed.arena,
                file,
                members,
                None,
                getter,
                SymbolFlags::GET_ACCESSOR,
                SymbolFlags::NONE,
            )
            .unwrap();
        let property_symbol = binder
            .declare_symbol(
                &parsed.arena,
                file,
                members,
                None,
                property,
                SymbolFlags::PROPERTY,
                SymbolFlags::GET_ACCESSOR,
            )
            .unwrap();
        assert_ne!(property_symbol, accessor);
        assert!(
            binder
                .symbol_store()
                .symbol(accessor)
                .unwrap()
                .flags()
                .contains(SymbolFlags::ACCESSOR)
        );
        let setter_symbol = binder
            .declare_symbol(
                &parsed.arena,
                file,
                members,
                None,
                setter,
                SymbolFlags::SET_ACCESSOR,
                SymbolFlags::ACCESSOR,
            )
            .unwrap();
        assert_ne!(setter_symbol, accessor);
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(members)
                .unwrap()
                .get_source("x"),
            Some(accessor)
        );

        let declarations = binder.create_symbol_table();
        let enum_symbol = binder
            .declare_symbol(
                &parsed.arena,
                file,
                declarations,
                None,
                enumeration,
                SymbolFlags::REGULAR_ENUM,
                SymbolFlags::NONE,
            )
            .unwrap();
        let class_symbol = binder
            .declare_symbol(
                &parsed.arena,
                file,
                declarations,
                None,
                conflicting_class,
                SymbolFlags::CLASS,
                SymbolFlags::REGULAR_ENUM,
            )
            .unwrap();
        assert_ne!(enum_symbol, class_symbol);
        let diagnostics = binder.file(file).unwrap().diagnostics();
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2300, 2300, 2300, 2300, 2567, 2567]
        );
        assert!(diagnostics[4].diagnostic.arguments.is_empty());
        assert!(diagnostics[5].diagnostic.arguments.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn default_export_conflicts_keep_related_information_in_exact_order() {
        let parsed = parse_source_file(
            "export default function first() {} export default function second() {} export default class third {}",
        );
        let functions = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionDeclaration);
        let class = nodes_of_kind(&parsed.arena, SyntaxKind::ClassDeclaration)[0];
        let file = FileId::new(27);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();

        let parent_table = binder.create_symbol_table();
        let parent = binder
            .declare_symbol(
                &parsed.arena,
                file,
                parent_table,
                None,
                parsed.source_file,
                SymbolFlags::VALUE_MODULE,
                SymbolFlags::NONE,
            )
            .unwrap();
        let local_table = binder.create_symbol_table();
        let local = binder
            .declare_symbol(
                &parsed.arena,
                file,
                local_table,
                None,
                functions[0],
                SymbolFlags::FUNCTION,
                SymbolFlags::NONE,
            )
            .unwrap();
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(local_table)
                .unwrap()
                .get_source("first"),
            Some(local)
        );

        let exports = binder.create_symbol_table();
        let first = binder
            .declare_symbol(
                &parsed.arena,
                file,
                exports,
                Some(parent),
                functions[0],
                SymbolFlags::FUNCTION,
                SymbolFlags::NONE,
            )
            .unwrap();
        assert_eq!(
            binder.link_exported_declaration(
                node_ref(&parsed.arena, file, functions[0]),
                local,
                parent,
            ),
            Err(CanonicalDeclarationError::ExportSymbolMismatch {
                node: node_ref(&parsed.arena, file, functions[0]),
                actual: Some(first),
                export: parent,
            })
        );
        assert_eq!(
            binder.symbol_store().symbol(local).unwrap().export_symbol(),
            None
        );
        assert_eq!(
            binder
                .file(file)
                .unwrap()
                .local_symbol(node_ref(&parsed.arena, file, functions[0])),
            None
        );
        binder
            .link_exported_declaration(node_ref(&parsed.arena, file, functions[0]), local, first)
            .unwrap();
        assert_eq!(
            binder.symbol_store().symbol(local).unwrap().export_symbol(),
            Some(first)
        );
        let merged = binder
            .declare_symbol(
                &parsed.arena,
                file,
                exports,
                Some(parent),
                functions[1],
                SymbolFlags::FUNCTION,
                SymbolFlags::NONE,
            )
            .unwrap();
        assert_eq!(merged, first);
        let detached = binder
            .declare_symbol(
                &parsed.arena,
                file,
                exports,
                Some(parent),
                class,
                SymbolFlags::CLASS,
                SymbolFlags::FUNCTION,
            )
            .unwrap();
        assert_ne!(detached, first);
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(exports)
                .unwrap()
                .get(InternalSymbolName::Default.as_ref()),
            Some(first)
        );
        let bound = binder.file(file).unwrap();
        assert_eq!(
            bound.symbol(node_ref(&parsed.arena, file, functions[0])),
            Some(first)
        );
        assert_eq!(
            bound.local_symbol(node_ref(&parsed.arena, file, functions[0])),
            Some(local)
        );
        let diagnostics = bound.diagnostics();
        assert_eq!(diagnostics.len(), 3);
        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() == 2528)
        );
        assert_eq!(
            diagnostics[0]
                .related_information
                .iter()
                .map(|related| related.diagnostic.code())
                .collect::<Vec<_>>(),
            [2753]
        );
        assert_eq!(
            diagnostics[1]
                .related_information
                .iter()
                .map(|related| related.diagnostic.code())
                .collect::<Vec<_>>(),
            [6204]
        );
        assert_eq!(
            diagnostics[2]
                .related_information
                .iter()
                .map(|related| related.diagnostic.code())
                .collect::<Vec<_>>(),
            [2752, 2752]
        );
    }

    #[test]
    fn parent_mismatch_panics_only_after_pinned_add_declaration_mutations() {
        let parsed = parse_source_file("{} {} let same; let same;");
        let blocks = nodes_of_kind(&parsed.arena, SyntaxKind::Block);
        let declarations = nodes_of_kind(&parsed.arena, SyntaxKind::VariableDeclaration);
        let file = FileId::new(28);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let parent_table = binder.create_symbol_table();
        let first_parent = binder
            .declare_symbol(
                &parsed.arena,
                file,
                parent_table,
                None,
                blocks[0],
                SymbolFlags::NONE,
                SymbolFlags::NONE,
            )
            .unwrap();
        let second_parent = binder
            .declare_symbol(
                &parsed.arena,
                file,
                parent_table,
                None,
                blocks[1],
                SymbolFlags::NONE,
                SymbolFlags::NONE,
            )
            .unwrap();
        let table = binder.create_symbol_table();
        let symbol = binder
            .declare_symbol(
                &parsed.arena,
                file,
                table,
                Some(first_parent),
                declarations[0],
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES,
            )
            .unwrap();

        let mismatch = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let _ = binder.declare_symbol(
                &parsed.arena,
                file,
                table,
                Some(second_parent),
                declarations[1],
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES,
            );
        }));
        assert!(mismatch.is_err());
        let record = binder.symbol_store().symbol(symbol).unwrap();
        assert_eq!(record.parent(), Some(first_parent));
        assert_eq!(
            record.declarations().unwrap(),
            [
                node_ref(&parsed.arena, file, declarations[0]),
                node_ref(&parsed.arena, file, declarations[1]),
            ]
        );
        assert_eq!(
            binder
                .file(file)
                .unwrap()
                .symbol(node_ref(&parsed.arena, file, declarations[1])),
            Some(symbol)
        );
        assert_eq!(binder.file(file).unwrap().symbol_count(), 3);
    }

    #[test]
    fn foreign_declaration_provenance_is_rejected_atomically() {
        let parsed = parse_source_file("class Local {}");
        let foreign = parse_source_file("class Foreign {}");
        let local_class = nodes_of_kind(&parsed.arena, SyntaxKind::ClassDeclaration)[0];
        let foreign_class = nodes_of_kind(&foreign.arena, SyntaxKind::ClassDeclaration)[0];
        let file = FileId::new(29);
        let foreign_file = FileId::new(30);

        let mut foreign_binder = CanonicalBinder::new();
        foreign_binder
            .bind_source_file(&foreign.arena, foreign.source_file, foreign_file)
            .unwrap();
        let foreign_table = foreign_binder.create_symbol_table();
        let foreign_symbol = foreign_binder
            .declare_symbol(
                &foreign.arena,
                foreign_file,
                foreign_table,
                None,
                foreign_class,
                SymbolFlags::CLASS,
                SymbolFlags::NONE,
            )
            .unwrap();

        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let table = binder.create_symbol_table();
        assert_eq!(
            binder.declare_symbol(
                &parsed.arena,
                file,
                foreign_table,
                None,
                local_class,
                SymbolFlags::CLASS,
                SymbolFlags::NONE,
            ),
            Err(CanonicalDeclarationError::InvalidSymbolTable(foreign_table))
        );
        assert_eq!(
            binder.declare_symbol(
                &parsed.arena,
                file,
                table,
                Some(foreign_symbol),
                local_class,
                SymbolFlags::CLASS,
                SymbolFlags::NONE,
            ),
            Err(CanonicalDeclarationError::InvalidParent(foreign_symbol))
        );
        assert!(matches!(
            binder.declare_symbol(
                &foreign.arena,
                file,
                table,
                None,
                local_class,
                SymbolFlags::CLASS,
                SymbolFlags::NONE,
            ),
            Err(CanonicalDeclarationError::WrongArena { .. })
        ));
        assert_eq!(
            binder.link_exported_declaration(
                node_ref(&parsed.arena, file, local_class),
                foreign_symbol,
                foreign_symbol,
            ),
            Err(CanonicalDeclarationError::InvalidLocalSymbol(
                foreign_symbol
            ))
        );
        let bound = binder.file(file).unwrap();
        assert_eq!(bound.symbol_count(), 0);
        assert!(bound.diagnostics().is_empty());
        assert_eq!(bound.classifiable_names().count(), 0);
        assert_eq!(
            bound.symbol(node_ref(&parsed.arena, file, local_class)),
            None
        );
        assert_eq!(
            bound.local_symbol(node_ref(&parsed.arena, file, local_class)),
            None
        );
        assert!(
            binder
                .symbol_store()
                .symbol_table(table)
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn javascript_only_assignment_names_wait_for_a_canonical_file_kind() {
        let parsed = parse_source_file(
            "this.field = 1; module.exports = value; module[\"exports\"] = value; module[(\"exports\")].field = value; module[(\"exports\")][\"field\"] = value; Object.defineProperty(exports, \"name\", {});",
        );
        let this_assignment = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "this.field = 1",
        );
        let module_assignment = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "module.exports = value",
        );
        let module_element_assignment = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "module[\"exports\"] = value",
        );
        let module_element_property_assignment = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "module[(\"exports\")].field = value",
        );
        let nested_module_element_assignment = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "module[(\"exports\")][\"field\"] = value",
        );
        let define_property = node_with_source(
            &parsed.arena,
            SyntaxKind::CallExpression,
            "Object.defineProperty(exports, \"name\", {})",
        );
        let file = FileId::new(34);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let table = binder.create_symbol_table();
        for declaration in [
            this_assignment,
            module_assignment,
            module_element_assignment,
            module_element_property_assignment,
            nested_module_element_assignment,
            define_property,
        ] {
            assert_eq!(
                binder.declare_symbol(
                    &parsed.arena,
                    file,
                    table,
                    None,
                    declaration,
                    SymbolFlags::ASSIGNMENT | SymbolFlags::CLASS,
                    SymbolFlags::NONE,
                ),
                Err(CanonicalDeclarationError::JavaScriptFileKindRequired(
                    node_ref(&parsed.arena, file, declaration)
                ))
            );
        }
        assert_eq!(binder.file(file).unwrap().symbol_count(), 0);
        assert!(
            binder
                .symbol_store()
                .symbol_table(table)
                .unwrap()
                .is_empty()
        );

        let bound = binder.file(file).unwrap();
        assert_eq!(bound.symbol_count(), 0);
        assert_eq!(bound.classifiable_names().count(), 0);
        assert!(bound.diagnostics().is_empty());
    }

    #[test]
    fn malformed_export_type_conflict_carries_the_exact_suggestion() {
        let parsed = parse_source_file("type Existing = string; export type Existing;");
        let aliases = nodes_of_kind(&parsed.arena, SyntaxKind::TypeAliasDeclaration);
        assert_eq!(aliases.len(), 2);
        let file = FileId::new(31);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let table = binder.create_symbol_table();
        binder
            .declare_symbol(
                &parsed.arena,
                file,
                table,
                None,
                aliases[0],
                SymbolFlags::TYPE_ALIAS,
                SymbolFlags::NONE,
            )
            .unwrap();
        binder
            .declare_symbol(
                &parsed.arena,
                file,
                table,
                None,
                aliases[1],
                SymbolFlags::TYPE_ALIAS,
                SymbolFlags::TYPE_ALIAS_EXCLUDES,
            )
            .unwrap();
        let diagnostics = binder.file(file).unwrap().diagnostics();
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(diagnostics[0].diagnostic.code(), 2300);
        assert!(diagnostics[0].related_information.is_empty());
        assert_eq!(diagnostics[1].diagnostic.code(), 2300);
        assert_eq!(diagnostics[1].related_information.len(), 1);
        let suggestion = &diagnostics[1].related_information[0];
        assert_eq!(suggestion.node.node, aliases[1]);
        assert_eq!(suggestion.diagnostic.code(), 1369);
        assert_eq!(
            suggestion.diagnostic.arguments,
            ["export type { Existing }"]
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn computed_private_and_ambient_names_use_exact_table_keys() {
        let parsed = parse_source_file(
            r#"
                declare module "pkg" {}
                declare global {}
                class Names {
                    ["text"]() {}
                    [1]() {}
                    [+2]() {}
                    [-3]() {}
                    [dynamic]() {}
                    #private = 1;
                }
            "#,
        );
        let modules = nodes_of_kind(&parsed.arena, SyntaxKind::ModuleDeclaration);
        let class = nodes_of_kind(&parsed.arena, SyntaxKind::ClassDeclaration)[0];
        let methods = nodes_of_kind(&parsed.arena, SyntaxKind::MethodDeclaration);
        let private_property = nodes_of_kind(&parsed.arena, SyntaxKind::PropertyDeclaration)[0];
        assert_eq!((modules.len(), methods.len()), (2, 5));
        let file = FileId::new(32);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();

        let declarations = binder.create_symbol_table();
        let class_symbol = binder
            .declare_symbol(
                &parsed.arena,
                file,
                declarations,
                None,
                class,
                SymbolFlags::CLASS,
                SymbolFlags::NONE,
            )
            .unwrap();
        for module in &modules {
            binder
                .declare_symbol(
                    &parsed.arena,
                    file,
                    declarations,
                    None,
                    *module,
                    SymbolFlags::NAMESPACE_MODULE,
                    SymbolFlags::NONE,
                )
                .unwrap();
        }
        let declaration_table = binder.symbol_store().symbol_table(declarations).unwrap();
        assert!(declaration_table.get_source("\"pkg\"").is_some());
        assert!(
            declaration_table
                .get(InternalSymbolName::Global.as_ref())
                .is_some()
        );

        let members = binder.create_symbol_table();
        for (method, key) in methods[..4].iter().zip(["text", "1", "+2", "-3"]) {
            let symbol = binder
                .declare_symbol(
                    &parsed.arena,
                    file,
                    members,
                    Some(class_symbol),
                    *method,
                    SymbolFlags::METHOD,
                    SymbolFlags::NONE,
                )
                .unwrap();
            assert_eq!(
                binder
                    .symbol_store()
                    .symbol_table(members)
                    .unwrap()
                    .get_source(key),
                Some(symbol)
            );
        }
        let before = binder.file(file).unwrap().symbol_count();
        assert_eq!(
            binder.declare_symbol(
                &parsed.arena,
                file,
                members,
                Some(class_symbol),
                methods[4],
                SymbolFlags::METHOD | SymbolFlags::CLASS,
                SymbolFlags::NONE,
            ),
            Err(CanonicalDeclarationError::DynamicNameRequiresComputed(
                node_ref(&parsed.arena, file, methods[4])
            ))
        );
        assert_eq!(binder.file(file).unwrap().symbol_count(), before);
        assert_eq!(
            binder
                .file(file)
                .unwrap()
                .symbol(node_ref(&parsed.arena, file, methods[4])),
            None
        );
        let computed = binder
            .declare_symbol_ex(
                &parsed.arena,
                file,
                members,
                Some(class_symbol),
                methods[4],
                SymbolFlags::METHOD,
                SymbolFlags::NONE,
                false,
                true,
            )
            .unwrap();
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(members)
                .unwrap()
                .get(InternalSymbolName::Computed.as_ref()),
            Some(computed)
        );
        let private = binder
            .declare_symbol(
                &parsed.arena,
                file,
                members,
                Some(class_symbol),
                private_property,
                SymbolFlags::PROPERTY,
                SymbolFlags::NONE,
            )
            .unwrap();
        let private_name = binder.symbol_store().symbol(private).unwrap().name();
        assert!(private_name.is_private_identifier());
        assert!(private_name.as_bytes().ends_with(b"@#private"));
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(members)
                .unwrap()
                .get(private_name),
            Some(private)
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn special_and_assigned_declaration_names_cover_the_typescript_closure() {
        let mut parsed = parse_source_file(
            r#"
                interface I {
                    (): void;
                    new (): object;
                    [key: string]: unknown;
                }
                class C { constructor() {} }
                type F = () => void;
                type K = new () => object;
                export * from "m";
                export default 1;
                export = value;
                module.exports = exports;
                left + right;
                const assignedFunction = function() {};
                const assignedArrow = () => {};
                const assignedClass = class {};
                const object = { property: function() {} };
                holder.method = function() {};
                holder["element"] = class {};
                holder.literal = 1;
                holder[dynamic] = 1;
            "#,
        );
        for property in nodes_of_kind(&parsed.arena, SyntaxKind::PropertyAssignment) {
            let name = match &parsed.arena.get(property).unwrap().data {
                NodeData::PropertyAssignment(data) => data.name,
                _ => unreachable!(),
            };
            let mut duplicate = parsed.arena.get(name).unwrap().clone();
            duplicate.parent = Some(property);
            let duplicate = parsed.arena.alloc(duplicate);
            match &mut parsed.arena.get_mut(property).unwrap().data {
                NodeData::PropertyAssignment(data) => data.type_ = Some(duplicate),
                _ => unreachable!(),
            }
        }
        let file = FileId::new(33);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();

        let internals = binder.create_symbol_table();
        let call_signature = nodes_of_kind(&parsed.arena, SyntaxKind::CallSignature)[0];
        let function_type = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionType)[0];
        let call = binder
            .declare_symbol(
                &parsed.arena,
                file,
                internals,
                None,
                call_signature,
                SymbolFlags::SIGNATURE,
                SymbolFlags::NONE,
            )
            .unwrap();
        assert_eq!(
            binder
                .declare_symbol(
                    &parsed.arena,
                    file,
                    internals,
                    None,
                    function_type,
                    SymbolFlags::SIGNATURE,
                    SymbolFlags::NONE,
                )
                .unwrap(),
            call
        );
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(internals)
                .unwrap()
                .get(InternalSymbolName::Call.as_ref()),
            Some(call)
        );

        let construct_signature = nodes_of_kind(&parsed.arena, SyntaxKind::ConstructSignature)[0];
        let constructor_type = nodes_of_kind(&parsed.arena, SyntaxKind::ConstructorType)[0];
        let construct = binder
            .declare_symbol(
                &parsed.arena,
                file,
                internals,
                None,
                construct_signature,
                SymbolFlags::SIGNATURE,
                SymbolFlags::NONE,
            )
            .unwrap();
        assert_eq!(
            binder
                .declare_symbol(
                    &parsed.arena,
                    file,
                    internals,
                    None,
                    constructor_type,
                    SymbolFlags::SIGNATURE,
                    SymbolFlags::NONE,
                )
                .unwrap(),
            construct
        );
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(internals)
                .unwrap()
                .get(InternalSymbolName::New.as_ref()),
            Some(construct)
        );
        for (kind, internal) in [
            (SyntaxKind::Constructor, InternalSymbolName::Constructor),
            (SyntaxKind::IndexSignature, InternalSymbolName::Index),
            (
                SyntaxKind::ExportDeclaration,
                InternalSymbolName::ExportStar,
            ),
        ] {
            let nodes = nodes_of_kind(&parsed.arena, kind);
            assert!(!nodes.is_empty(), "missing {kind:?}");
            let node = nodes[0];
            let symbol = binder
                .declare_symbol(
                    &parsed.arena,
                    file,
                    internals,
                    None,
                    node,
                    SymbolFlags::SIGNATURE,
                    SymbolFlags::NONE,
                )
                .unwrap();
            assert_eq!(
                binder
                    .symbol_store()
                    .symbol_table(internals)
                    .unwrap()
                    .get(internal.as_ref()),
                Some(symbol)
            );
        }

        let exports = binder.create_symbol_table();
        let export_assignments = nodes_of_kind(&parsed.arena, SyntaxKind::ExportAssignment);
        assert_eq!(export_assignments.len(), 2);
        for assignment in &export_assignments {
            binder
                .declare_symbol(
                    &parsed.arena,
                    file,
                    exports,
                    None,
                    *assignment,
                    SymbolFlags::ALIAS,
                    SymbolFlags::NONE,
                )
                .unwrap();
        }
        assert!(
            binder
                .symbol_store()
                .symbol_table(exports)
                .unwrap()
                .get(InternalSymbolName::Default.as_ref())
                .is_some()
        );
        assert!(
            binder
                .symbol_store()
                .symbol_table(exports)
                .unwrap()
                .get(InternalSymbolName::ExportEquals.as_ref())
                .is_some()
        );

        let js_names = binder.create_symbol_table();
        let module_exports = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "module.exports = exports",
        );
        let module_exports_property = binder
            .declare_symbol(
                &parsed.arena,
                file,
                js_names,
                None,
                module_exports,
                SymbolFlags::ASSIGNMENT,
                SymbolFlags::NONE,
            )
            .unwrap();
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(js_names)
                .unwrap()
                .get_source("exports"),
            Some(module_exports_property)
        );
        let ordinary_binary =
            node_with_source(&parsed.arena, SyntaxKind::BinaryExpression, "left + right");
        let export_equals = binder
            .declare_symbol(
                &parsed.arena,
                file,
                js_names,
                None,
                ordinary_binary,
                SymbolFlags::ASSIGNMENT,
                SymbolFlags::NONE,
            )
            .unwrap();
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(js_names)
                .unwrap()
                .get(InternalSymbolName::ExportEquals.as_ref()),
            Some(export_equals)
        );

        let assigned = binder.create_symbol_table();
        for (kind, source, key) in [
            (
                SyntaxKind::FunctionExpression,
                "function() {}",
                "assignedFunction",
            ),
            (SyntaxKind::ArrowFunction, "() => {}", "assignedArrow"),
            (SyntaxKind::ClassExpression, "class {}", "assignedClass"),
            (SyntaxKind::FunctionExpression, "function() {}", "property"),
            (SyntaxKind::FunctionExpression, "function() {}", "method"),
            (SyntaxKind::ClassExpression, "class {}", "element"),
        ] {
            let candidates = parsed
                .arena
                .iter()
                .filter_map(|(id, node)| {
                    (node.kind == kind
                        && super::source_text_of_node(&parsed.arena, node) == Some(source)
                        && super::get_name_of_declaration(&parsed.arena, id)
                            .and_then(|name| super::node_text(&parsed.arena, name))
                            .as_deref()
                            == Some(key))
                    .then_some(id)
                })
                .collect::<Vec<_>>();
            assert_eq!(candidates.len(), 1, "assigned key {key}");
            let symbol = binder
                .declare_symbol(
                    &parsed.arena,
                    file,
                    assigned,
                    None,
                    candidates[0],
                    SymbolFlags::FUNCTION,
                    SymbolFlags::NONE,
                )
                .unwrap();
            assert_eq!(
                binder
                    .symbol_store()
                    .symbol_table(assigned)
                    .unwrap()
                    .get_source(key),
                Some(symbol)
            );
        }
        for (source, key) in [
            ("holder.literal = 1", "literal"),
            ("holder[\"element\"] = class {}", "element"),
        ] {
            let binary = node_with_source(&parsed.arena, SyntaxKind::BinaryExpression, source);
            let symbol = binder
                .declare_symbol(
                    &parsed.arena,
                    file,
                    assigned,
                    None,
                    binary,
                    SymbolFlags::ASSIGNMENT | SymbolFlags::PROPERTY,
                    SymbolFlags::NONE,
                )
                .unwrap();
            assert_eq!(
                binder
                    .symbol_store()
                    .symbol_table(assigned)
                    .unwrap()
                    .get_source(key),
                Some(symbol)
            );
        }
        let dynamic = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "holder[dynamic] = 1",
        );
        assert_eq!(
            binder.declare_symbol(
                &parsed.arena,
                file,
                assigned,
                None,
                dynamic,
                SymbolFlags::ASSIGNMENT | SymbolFlags::PROPERTY,
                SymbolFlags::NONE,
            ),
            Err(CanonicalDeclarationError::DynamicNameRequiresComputed(
                node_ref(&parsed.arena, file, dynamic)
            ))
        );
        let computed = binder
            .declare_symbol_ex(
                &parsed.arena,
                file,
                assigned,
                None,
                dynamic,
                SymbolFlags::ASSIGNMENT | SymbolFlags::PROPERTY,
                SymbolFlags::NONE,
                false,
                true,
            )
            .unwrap();
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(assigned)
                .unwrap()
                .get(InternalSymbolName::Computed.as_ref()),
            Some(computed)
        );
    }

    #[test]
    fn traverses_source_blocks_and_module_blocks_functions_first() {
        let parsed = parse_source_file(
            r"
                const topBefore = 0;
                function topFunction() {
                    const blockBefore = 0;
                    function blockFunction() {}
                }
                namespace N {
                    const moduleBefore = 0;
                    function moduleFunction() {}
                }
            ",
        );
        let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
        else {
            unreachable!()
        };
        let top_variable = source.statements.nodes[0];
        let top_function = source.statements.nodes[1];
        let module = source.statements.nodes[2];

        let function_body = match &parsed.arena.get(top_function).unwrap().data {
            NodeData::FunctionDeclaration(function) => function.body.unwrap(),
            _ => unreachable!(),
        };
        let NodeData::Block(block) = &parsed.arena.get(function_body).unwrap().data else {
            unreachable!()
        };
        let block_variable = block.statements.nodes[0];
        let block_function = block.statements.nodes[1];

        let module_block = match &parsed.arena.get(module).unwrap().data {
            NodeData::ModuleDeclaration(module) => module.body.unwrap(),
            _ => unreachable!(),
        };
        let module_statements = match &parsed.arena.get(module_block).unwrap().data {
            NodeData::ModuleBlock(block) => &block.statements.nodes,
            _ => unreachable!(),
        };
        let module_variable = module_statements[0];
        let module_function = module_statements[1];

        let mut binder = CanonicalBinder::new();
        let bound = binder
            .bind_source_file(&parsed.arena, parsed.source_file, FileId::new(0))
            .unwrap();
        let order = bound.traversal_order().collect::<Vec<_>>();

        assert_eq!(bound.phase(), BindingPhase::Traversal);
        assert!(!bound.declarations_complete());
        assert_eq!(order[0], bound.source_file());
        assert!(position(&order, top_function) < position(&order, top_variable));
        assert!(position(&order, block_function) < position(&order, block_variable));
        assert!(position(&order, module_function) < position(&order, module_variable));
        assert_eq!(
            order.iter().map(|node| node.node).collect::<BTreeSet<_>>(),
            reachable_nodes(&parsed.arena, parsed.source_file)
        );
    }

    #[test]
    fn preserves_container_state_and_nil_locals() {
        let parsed = parse_source_file(
            r"
                function outer() {
                    { let blockScoped = 1; }
                    const arrow = () => this;
                    const expression = function () { return this; };
                }
            ",
        );
        let source = parsed.source_file;
        let function = match &parsed.arena.get(source).unwrap().data {
            NodeData::SourceFile(source) => source.statements.nodes[0],
            _ => unreachable!(),
        };
        let body = match &parsed.arena.get(function).unwrap().data {
            NodeData::FunctionDeclaration(function) => function.body.unwrap(),
            _ => unreachable!(),
        };
        let statements = match &parsed.arena.get(body).unwrap().data {
            NodeData::Block(block) => &block.statements.nodes,
            _ => unreachable!(),
        };
        let nested_block = statements[0];
        let nested_statement = match &parsed.arena.get(nested_block).unwrap().data {
            NodeData::Block(block) => block.statements.nodes[0],
            _ => unreachable!(),
        };
        let arrow = parsed
            .arena
            .iter()
            .find_map(|(id, node)| (node.kind == SyntaxKind::ArrowFunction).then_some(id))
            .unwrap();
        let function_expression = parsed
            .arena
            .iter()
            .find_map(|(id, node)| (node.kind == SyntaxKind::FunctionExpression).then_some(id))
            .unwrap();

        let mut binder = CanonicalBinder::new();
        let bound = binder
            .bind_source_file(&parsed.arena, source, FileId::new(4))
            .unwrap();
        let source_ref = bound.source_file();
        let function_ref = NodeRef::new(parsed.arena.id(), FileId::new(4), function);
        let body_ref = NodeRef::new(parsed.arena.id(), FileId::new(4), body);
        let nested_block_ref = NodeRef::new(parsed.arena.id(), FileId::new(4), nested_block);
        let nested_statement_ref =
            NodeRef::new(parsed.arena.id(), FileId::new(4), nested_statement);
        let arrow_ref = NodeRef::new(parsed.arena.id(), FileId::new(4), arrow);
        let function_expression_ref =
            NodeRef::new(parsed.arena.id(), FileId::new(4), function_expression);

        assert_eq!(bound.container(source_ref), None);
        assert_eq!(bound.container(function_ref), Some(source_ref));
        assert_eq!(bound.container(body_ref), Some(function_ref));
        assert_eq!(bound.container(nested_block_ref), Some(function_ref));
        assert_eq!(
            bound.block_scope_container(nested_statement_ref),
            Some(nested_block_ref)
        );
        assert_eq!(bound.this_container(body_ref), Some(function_ref));

        assert_eq!(bound.locals(source_ref), None);
        assert_eq!(bound.locals(function_ref), None);
        assert_eq!(bound.locals(body_ref), None);
        assert_eq!(bound.locals(nested_block_ref), None);
        let chain = bound.container_chain().collect::<Vec<_>>();
        assert_eq!(
            chain,
            [
                source_ref,
                function_ref,
                nested_block_ref,
                arrow_ref,
                function_expression_ref
            ]
        );
        assert_eq!(bound.next_container(source_ref), Some(function_ref));
        assert_eq!(bound.next_container(function_ref), Some(nested_block_ref));
        assert_eq!(bound.next_container(nested_block_ref), Some(arrow_ref));
        assert_eq!(
            bound.next_container(arrow_ref),
            Some(function_expression_ref)
        );
        assert_eq!(bound.next_container(function_expression_ref), None);
        assert_eq!(binder.symbol_store().symbol_table_len(), 0);
    }

    #[test]
    fn one_symbol_owner_covers_every_file_before_checker_adoption() {
        let first = parse_source_file("const first = 1;");
        let second = parse_source_file("function second() {};");
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&second.arena, second.source_file, FileId::new(7))
            .unwrap();
        binder
            .bind_source_file(&first.arena, first.source_file, FileId::new(3))
            .unwrap();

        let files = binder.finish();
        assert!(!files.declarations_complete());
        assert_eq!(
            files
                .files()
                .map(super::BoundFile::file_id)
                .collect::<Vec<_>>(),
            [FileId::new(3), FileId::new(7)]
        );
        let first_bound = files.file(FileId::new(3)).unwrap();
        let second_bound = files.file(FileId::new(7)).unwrap();
        let first_root = first_bound.source_file();
        let second_root = second_bound.source_file();
        assert!(files.symbol_store().contains_node_ref(first_root));
        assert!(files.symbol_store().contains_node_ref(second_root));
        assert_eq!(files.symbol_store().symbol_table_len(), 0);
        assert_eq!(first_bound.locals(first_root), None);
        assert_eq!(second_bound.locals(second_root), None);

        let wrong_file = NodeRef::new(first.arena.id(), FileId::new(7), first.source_file);
        let wrong_arena = NodeRef::new(second.arena.id(), FileId::new(3), first.source_file);
        assert!(!first_bound.contains(wrong_file));
        assert!(!first_bound.contains(wrong_arena));

        assert!(files.try_into_parts().is_err());
    }

    #[test]
    fn source_file_facts_are_explicit_canonical_input() {
        let parsed = parse_source_file("export interface Box<T> { value: T }");
        let file = FileId::new(41);
        let facts = CanonicalSourceFileFacts::new_with_default_library(
            EscapedName::source("\"/project/main\""),
            CanonicalSourceLanguage::TypeScript,
            true,
            true,
            CanonicalModuleState::External,
        );
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts.clone())
            .unwrap();
        let bound = binder.file(file).unwrap();
        assert_eq!(bound.source_facts(), Some(&facts));
        assert!(bound.source_facts().unwrap().is_default_library());
        assert_eq!(bound.phase(), BindingPhase::Traversal);
        assert_eq!(bound.symbol_count(), 0);

        let mut traversal_only = CanonicalBinder::new();
        traversal_only
            .bind_source_file(&parsed.arena, parsed.source_file, FileId::new(42))
            .unwrap();
        assert_eq!(
            traversal_only.file(FileId::new(42)).unwrap().source_facts(),
            None
        );

        let ordinary = CanonicalSourceFileFacts::new(
            EscapedName::source("\"/project/ordinary\""),
            CanonicalSourceLanguage::TypeScript,
            true,
            CanonicalModuleState::Script,
        );
        assert!(!ordinary.is_default_library());
    }

    #[test]
    fn declaration_slice_preflight_rejects_atomically_and_retry_is_stable() {
        let mut parsed = parse_source_file("type Deferred = string;");
        let file = FileId::new(43);
        let facts = CanonicalSourceFileFacts::new(
            EscapedName::source("\"/project/deferred\""),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::Script,
        );
        let alias = nodes_of_kind(&parsed.arena, SyntaxKind::TypeAliasDeclaration)[0];
        parsed.arena.get_mut(alias).unwrap().kind = SyntaxKind::JsTypeAliasDeclaration;
        let expected = Err(CanonicalDeclarationError::UnsupportedDeclarationFamily(
            node_ref(&parsed.arena, file, alias),
        ));
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts)
            .unwrap();

        assert_eq!(
            binder.bind_typescript_declaration_slice(&parsed.arena, file),
            expected
        );
        assert_eq!(
            binder.bind_typescript_declaration_slice(&parsed.arena, file),
            expected
        );
        let bound = binder.file(file).unwrap();
        assert!(!bound.declaration_slice_bound());
        assert_eq!(bound.phase(), BindingPhase::Traversal);
        assert_eq!(bound.symbol_count(), 0);
        assert_eq!(bound.locals(bound.source_file()), None);
        assert_eq!(bound.symbol(bound.source_file()), None);
        assert!(bound.diagnostics().is_empty());
        assert_eq!(binder.symbol_store().symbol_len(), 0);
        assert_eq!(binder.symbol_store().symbol_table_len(), 0);
    }

    #[test]
    fn private_name_outside_a_class_follows_the_pinned_missing_name_path() {
        let parsed = parse_source_file("const #orphan = 1;");
        let file = FileId::new(66);
        let variable = nodes_of_kind(&parsed.arena, SyntaxKind::VariableDeclaration)[0];
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/private-recovery\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        assert_eq!(bound.phase(), BindingPhase::Declarations);
        let symbol = bound
            .symbol(node_ref(&parsed.arena, file, variable))
            .unwrap();
        let record = binder.symbol_store().symbol(symbol).unwrap();
        assert_eq!(record.name(), InternalSymbolName::Missing.as_ref());
        assert_eq!(record.flags(), SymbolFlags::BLOCK_SCOPED_VARIABLE);
        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        assert!(locals.is_empty());
        assert_eq!(bound.symbol_count(), 1);
    }

    #[test]
    fn module_dispatch_uses_exact_instance_state_and_const_enum_marker_rules() {
        let parsed = parse_source_file(
            r"
namespace Types { export interface Shape {} }
namespace Runtime { export const value = 1; }
namespace Constants { export const enum E { A } }
function Merged() {}
namespace Merged { export const enum E { A } }
",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(46);
        let facts = CanonicalSourceFileFacts::new(
            EscapedName::source("\"/project/modules\""),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::Script,
        );
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts)
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        let types = locals.get_source("Types").unwrap();
        let runtime = locals.get_source("Runtime").unwrap();
        let constants = locals.get_source("Constants").unwrap();
        let merged = locals.get_source("Merged").unwrap();
        assert_eq!(
            binder.symbol_store().symbol(types).unwrap().flags(),
            SymbolFlags::NAMESPACE_MODULE
        );
        assert_eq!(
            binder.symbol_store().symbol(runtime).unwrap().flags(),
            SymbolFlags::VALUE_MODULE
        );
        assert_eq!(
            binder.symbol_store().symbol(constants).unwrap().flags(),
            SymbolFlags::VALUE_MODULE | SymbolFlags::CONST_ENUM_ONLY_MODULE
        );
        assert_eq!(
            binder.symbol_store().symbol(merged).unwrap().flags(),
            SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE
        );
        assert!(bound.is_not_const_enum_only_module(merged));
        assert!(!bound.is_not_const_enum_only_module(constants));
        assert!(bound.diagnostics().is_empty());
    }

    #[test]
    fn ambient_function_namespaces_preserve_callable_and_generic_export_symbols() {
        for (index, (body, expected_module_flags)) in [
            ("export const items: string[];", SymbolFlags::VALUE_MODULE),
            (
                "export interface Box<T> { value: T; }",
                SymbolFlags::NAMESPACE_MODULE,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(&format!(
                "declare function callable(): void; declare namespace callable {{ {body} }} export = callable;"
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(89 + u32::try_from(index).unwrap());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/callable.d.ts\""),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();

            let bound = binder.file(file).unwrap();
            assert!(bound.diagnostics().is_empty(), "{:?}", bound.diagnostics());
            let locals = binder
                .symbol_store()
                .symbol_table(bound.locals(bound.source_file()).unwrap())
                .unwrap();
            let callable = locals.get_source("callable").unwrap();
            let record = binder.symbol_store().symbol(callable).unwrap();
            assert_eq!(
                record.flags(),
                SymbolFlags::FUNCTION | expected_module_flags
            );
            assert_eq!(record.declarations().unwrap().len(), 2);
            let namespace = nodes_of_kind(&parsed.arena, SyntaxKind::ModuleDeclaration)[0];
            assert_eq!(
                bound.symbol(node_ref(&parsed.arena, file, namespace)),
                Some(callable)
            );
            let exports = binder
                .symbol_store()
                .symbol_table(record.exports().unwrap())
                .unwrap();

            if expected_module_flags == SymbolFlags::NAMESPACE_MODULE {
                let interface = exports.get_source("Box").unwrap();
                let members = binder
                    .symbol_store()
                    .symbol_table(
                        binder
                            .symbol_store()
                            .symbol(interface)
                            .unwrap()
                            .members()
                            .unwrap(),
                    )
                    .unwrap();
                assert!(members.get_source("T").is_some());
                assert!(members.get_source("value").is_some());
            } else {
                assert!(exports.get_source("items").is_some());
            }
        }
    }

    #[test]
    fn ambient_modules_record_patterns_and_diagnostics_in_declaration_order() {
        let parsed = parse_source_file(
            r#"
declare module "*.css" { export const classes: object; }
declare module "bad**pattern" {}
export declare module "visible" {}
declare global { interface Window {} }
"#,
        );
        let file = FileId::new(47);
        let facts = CanonicalSourceFileFacts::new(
            EscapedName::source("\"/project/ambient\""),
            CanonicalSourceLanguage::TypeScript,
            true,
            CanonicalModuleState::Script,
        );
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts)
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        assert_eq!(bound.pattern_ambient_modules().len(), 1);
        let pattern = &bound.pattern_ambient_modules()[0];
        assert_eq!(pattern.pattern(), "*.css");
        assert_eq!(pattern.star_index(), 0);
        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        assert_eq!(locals.get_source("\"*.css\""), Some(pattern.symbol()));
        assert!(locals.get(InternalSymbolName::Global.as_ref()).is_some());
        assert_eq!(
            bound
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [5061, 2668]
        );
        assert_eq!(
            bound.diagnostics()[0].diagnostic.arguments,
            ["bad**pattern"]
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Covers both parser collection branches and provenance.
    fn module_augmentations_preserve_parser_order_and_exact_name_provenance() {
        let external = parse_source_file(
            r#"
declare module "./relative" {}
declare module "pkg" {}
declare global { interface Window { marker: true } }
"#,
        );
        assert!(
            external.diagnostics.is_empty(),
            "{:?}",
            external.diagnostics
        );
        let external_file = FileId::new(147);
        let mut external_binder = CanonicalBinder::new();
        external_binder
            .bind_source_file_with_facts(
                &external.arena,
                external.source_file,
                external_file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/external\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        external_binder
            .bind_typescript_declaration_slice(&external.arena, external_file)
            .unwrap();

        let external_augmentations = external_binder
            .file(external_file)
            .unwrap()
            .module_augmentations();
        assert_eq!(external_augmentations.len(), 3);
        assert_eq!(
            external_augmentations
                .iter()
                .map(|augmentation| {
                    node_text(&external.arena, augmentation.name().node).unwrap()
                })
                .collect::<Vec<_>>(),
            ["./relative", "pkg", "global"]
        );
        for augmentation in external_augmentations {
            let name = augmentation.name();
            assert!(name.is_for(external.arena.id(), external_file));
            let module = external.arena.get(name.node).unwrap().parent.unwrap();
            assert_eq!(
                external.arena.get(module).unwrap().kind,
                SyntaxKind::ModuleDeclaration
            );
            assert!(!augmentation.in_ambient_context());
        }

        let script = parse_source_file(
            r#"
declare module "outer" {
    module "nested" {}
    module "./relative" {}
    module "C:\\rooted" {}
}
"#,
        );
        assert!(script.diagnostics.is_empty(), "{:?}", script.diagnostics);
        let script_file = FileId::new(148);
        let mut script_binder = CanonicalBinder::new();
        script_binder
            .bind_source_file_with_facts(
                &script.arena,
                script.source_file,
                script_file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/script\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        script_binder
            .bind_typescript_declaration_slice(&script.arena, script_file)
            .unwrap();

        let script_augmentations = script_binder
            .file(script_file)
            .unwrap()
            .module_augmentations();
        assert_eq!(script_augmentations.len(), 1);
        assert_eq!(
            node_text(&script.arena, script_augmentations[0].name().node).as_deref(),
            Some("nested")
        );
        assert!(
            script_augmentations[0]
                .name()
                .is_for(script.arena.id(), script_file)
        );
        assert!(script_augmentations[0].in_ambient_context());
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn export_context_uses_ambient_flags_not_recovered_module_shape() {
        let parsed = parse_source_file(
            r#"
module "recovery" { interface Hidden {} }
declare module "declared" { interface Visible {} }
"#,
        );
        let modules = nodes_of_kind(&parsed.arena, SyntaxKind::ModuleDeclaration);
        assert_eq!(modules.len(), 2);
        let file = FileId::new(70);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/recovered-module\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let source_locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        let recovered = source_locals.get_source("\"recovery\"").unwrap();
        let declared = source_locals.get_source("\"declared\"").unwrap();
        assert!(
            binder
                .symbol_store()
                .symbol(recovered)
                .unwrap()
                .exports()
                .is_none_or(|exports| binder
                    .symbol_store()
                    .symbol_table(exports)
                    .unwrap()
                    .get_source("Hidden")
                    .is_none())
        );
        let recovered_locals = binder
            .symbol_store()
            .symbol_table(
                bound
                    .locals(node_ref(&parsed.arena, file, modules[0]))
                    .unwrap(),
            )
            .unwrap();
        assert!(recovered_locals.get_source("Hidden").is_some());
        let declared_exports = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(declared)
                    .unwrap()
                    .exports()
                    .unwrap(),
            )
            .unwrap();
        assert!(declared_exports.get_source("Visible").is_some());

        let declaration_file =
            parse_source_file(r#"module "file-context" { interface FileVisible {} }"#);
        let declaration_file_id = FileId::new(71);
        let mut declaration_binder = CanonicalBinder::new();
        declaration_binder
            .bind_source_file_with_facts(
                &declaration_file.arena,
                declaration_file.source_file,
                declaration_file_id,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/types.d.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        declaration_binder
            .bind_typescript_declaration_slice(&declaration_file.arena, declaration_file_id)
            .unwrap();
        let declaration_bound = declaration_binder.file(declaration_file_id).unwrap();
        let declaration_source_locals = declaration_binder
            .symbol_store()
            .symbol_table(
                declaration_bound
                    .locals(declaration_bound.source_file())
                    .unwrap(),
            )
            .unwrap();
        let file_module = declaration_source_locals
            .get_source("\"file-context\"")
            .unwrap();
        let file_exports = declaration_binder
            .symbol_store()
            .symbol_table(
                declaration_binder
                    .symbol_store()
                    .symbol(file_module)
                    .unwrap()
                    .exports()
                    .unwrap(),
            )
            .unwrap();
        assert!(file_exports.get_source("FileVisible").is_some());
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn external_alias_dispatch_routes_imports_reexports_and_assignments_exactly() {
        let parsed = parse_source_file(
            r#"
import defaultValue, { source as local, same } from "pkg";
import * as namespaceValue from "namespace-pkg";
import equalsValue = require("equals-pkg");
export import exportedEquals = require("exported-equals-pkg");
export { local as renamed, same as unchanged };
export * from "star-pkg";
export * as namespaceExport from "namespace-export-pkg";
export default local;
export = equalsValue;
"#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(48);
        let facts = CanonicalSourceFileFacts::new(
            EscapedName::source("\"/project/aliases\""),
            CanonicalSourceLanguage::TypeScript,
            true,
            CanonicalModuleState::External,
        );
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts)
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let source = bound.symbol(bound.source_file()).unwrap();
        let source_record = binder.symbol_store().symbol(source).unwrap();
        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        let exports = binder
            .symbol_store()
            .symbol_table(source_record.exports().unwrap())
            .unwrap();
        for name in [
            "defaultValue",
            "local",
            "same",
            "namespaceValue",
            "equalsValue",
        ] {
            let symbol = locals
                .get_source(name)
                .unwrap_or_else(|| panic!("missing {name}"));
            assert_eq!(
                binder.symbol_store().symbol(symbol).unwrap().flags(),
                SymbolFlags::ALIAS
            );
        }
        assert!(locals.get_source("exportedEquals").is_none());
        for name in ["exportedEquals", "renamed", "unchanged", "namespaceExport"] {
            let symbol = exports
                .get_source(name)
                .unwrap_or_else(|| panic!("missing {name}"));
            let record = binder.symbol_store().symbol(symbol).unwrap();
            assert_eq!(record.flags(), SymbolFlags::ALIAS);
            assert_eq!(record.parent(), Some(source));
        }

        let export_star = exports
            .get(InternalSymbolName::ExportStar.as_ref())
            .unwrap();
        assert_eq!(
            binder.symbol_store().symbol(export_star).unwrap().flags(),
            SymbolFlags::EXPORT_STAR
        );
        let default_export = exports.get(InternalSymbolName::Default.as_ref()).unwrap();
        let default_record = binder.symbol_store().symbol(default_export).unwrap();
        assert_eq!(default_record.flags(), SymbolFlags::ALIAS);
        assert_eq!(default_record.value_declaration(), None);
        let export_equals = exports
            .get(InternalSymbolName::ExportEquals.as_ref())
            .unwrap();
        let export_equals_record = binder.symbol_store().symbol(export_equals).unwrap();
        assert_eq!(export_equals_record.flags(), SymbolFlags::ALIAS);
        let export_assignments = nodes_of_kind(&parsed.arena, SyntaxKind::ExportAssignment);
        assert_eq!(export_assignments.len(), 2);
        let export_equals_node = export_assignments
            .iter()
            .copied()
            .find(|assignment| {
                matches!(
                    &parsed.arena.get(*assignment).unwrap().data,
                    NodeData::ExportAssignment(assignment) if assignment.is_export_equals
                )
            })
            .unwrap();
        assert_eq!(
            export_equals_record.value_declaration(),
            Some(node_ref(&parsed.arena, file, export_equals_node))
        );
        assert!(export_assignments.iter().all(|assignment| {
            matches!(
                &parsed.arena.get(*assignment).unwrap().data,
                NodeData::ExportAssignment(assignment) if assignment.type_.is_none()
            )
        }));

        let import_clauses = nodes_of_kind(&parsed.arena, SyntaxKind::ImportClause);
        assert_eq!(import_clauses.len(), 2);
        assert_eq!(
            import_clauses
                .iter()
                .filter(|clause| bound
                    .symbol(node_ref(&parsed.arena, file, **clause))
                    .is_some())
                .count(),
            1
        );
        let namespace_export = nodes_of_kind(&parsed.arena, SyntaxKind::NamespaceExport)[0];
        assert_eq!(
            bound.symbol(node_ref(&parsed.arena, file, namespace_export)),
            exports.get_source("namespaceExport")
        );
        assert!(bound.diagnostics().is_empty());
    }

    #[test]
    fn empty_import_export_forms_preserve_nil_symbol_tables() {
        let parsed = parse_source_file("import \"side-effect\"; export {};");
        let file = FileId::new(54);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/empty-aliases\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let source = bound.symbol(bound.source_file()).unwrap();
        assert_eq!(bound.locals(bound.source_file()), None);
        assert_eq!(
            binder.symbol_store().symbol(source).unwrap().exports(),
            None
        );
        assert_eq!(binder.symbol_store().symbol_table_len(), 0);
        assert!(bound.diagnostics().is_empty());
    }

    #[test]
    fn module_instance_state_resolves_local_export_alias_targets() {
        let parsed = parse_source_file(
            r#"
namespace Types { interface Shape {} export { Shape }; }
namespace Values { const value = 1; export { value }; }
namespace Constants { const enum E { A } export { E }; }
namespace Ambiguous { import Imported = require("pkg"); export { Imported }; }
"#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(49);
        let facts = CanonicalSourceFileFacts::new(
            EscapedName::source("\"/project/module-aliases\""),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::Script,
        );
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts)
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        let flags = |name: &str| {
            binder
                .symbol_store()
                .symbol(locals.get_source(name).unwrap())
                .unwrap()
                .flags()
        };
        assert_eq!(flags("Types"), SymbolFlags::NAMESPACE_MODULE);
        assert_eq!(flags("Values"), SymbolFlags::VALUE_MODULE);
        assert_eq!(
            flags("Constants"),
            SymbolFlags::VALUE_MODULE | SymbolFlags::CONST_ENUM_ONLY_MODULE
        );
        assert_eq!(flags("Ambiguous"), SymbolFlags::VALUE_MODULE);
        assert!(bound.diagnostics().is_empty());
    }

    #[test]
    fn namespace_export_declarations_allocate_global_tables_only_on_success() {
        let valid = parse_source_file("export as namespace UMD;");
        let valid_file = FileId::new(50);
        let mut valid_binder = CanonicalBinder::new();
        valid_binder
            .bind_source_file_with_facts(
                &valid.arena,
                valid.source_file,
                valid_file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/umd\""),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        valid_binder
            .bind_typescript_declaration_slice(&valid.arena, valid_file)
            .unwrap();
        let valid_bound = valid_binder.file(valid_file).unwrap();
        let source = valid_bound.symbol(valid_bound.source_file()).unwrap();
        let globals = valid_binder
            .symbol_store()
            .symbol_table(valid_bound.global_exports().unwrap())
            .unwrap();
        let umd = globals.get_source("UMD").unwrap();
        let umd_record = valid_binder.symbol_store().symbol(umd).unwrap();
        assert_eq!(umd_record.flags(), SymbolFlags::ALIAS);
        assert_eq!(umd_record.parent(), Some(source));
        assert!(valid_bound.diagnostics().is_empty());

        for (index, source_text, declaration_file, module_state, code) in [
            (
                0,
                "export as namespace ScriptGlobal;",
                true,
                CanonicalModuleState::Script,
                1314,
            ),
            (
                1,
                "export as namespace RuntimeGlobal;",
                false,
                CanonicalModuleState::External,
                1315,
            ),
            (
                2,
                "export namespace Wrapper { export as namespace NestedGlobal; }",
                true,
                CanonicalModuleState::External,
                1316,
            ),
        ] {
            let parsed = parse_source_file(source_text);
            let file = FileId::new(51 + index);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/project/global-{index}\"")),
                        CanonicalSourceLanguage::TypeScript,
                        declaration_file,
                        module_state,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
            let bound = binder.file(file).unwrap();
            assert_eq!(bound.global_exports(), None);
            assert_eq!(bound.diagnostics().len(), 1);
            assert_eq!(bound.diagnostics()[0].diagnostic.code(), code);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn ordinary_typescript_dispatch_routes_scopes_members_and_anonymous_symbols() {
        let parsed = parse_source_file(
            r"
interface Box<T> {
    value?: T;
    method?<U>(input: U): T;
    get item(): T;
    set item(value: T);
    (input: T): T;
    new (input: T): Box<T>;
    [key: string]: T;
}
type Mapper<T> = { result: T };
type Callable = (input: number) => string;
const [first, { nested }] = source;
var loose;
function make<T>({ value }: Box<T>, extra?: T): T { return extra; }
enum E { A }
const enum CE { B }
class Model<T> {
    static count: number;
    value?: T;
    constructor(public id: string, value: T) { this.value = value; }
    method<U>(input: U): U { return input; }
    get item(): T { return this.value; }
    set item(value: T) { this.value = value; }
}
const expression = class Named { field = 1; };
const object = {};
",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(44);
        let facts = CanonicalSourceFileFacts::new(
            EscapedName::source("\"/project/ordinary\""),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::Script,
        );
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts)
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        assert!(bound.declaration_slice_bound());
        assert_eq!(bound.phase(), BindingPhase::Declarations);
        assert!(bound.declarations_complete());
        assert_eq!(bound.symbol(bound.source_file()), None);
        let source_locals = bound.locals(bound.source_file()).unwrap();
        let source_table = binder.symbol_store().symbol_table(source_locals).unwrap();
        for name in [
            "Box",
            "Mapper",
            "Callable",
            "first",
            "nested",
            "loose",
            "make",
            "E",
            "CE",
            "Model",
            "expression",
            "object",
        ] {
            assert!(source_table.get_source(name).is_some(), "missing {name}");
        }

        let interface = node_with_source(
            &parsed.arena,
            SyntaxKind::InterfaceDeclaration,
            "interface Box<T> {\n    value?: T;\n    method?<U>(input: U): T;\n    get item(): T;\n    set item(value: T);\n    (input: T): T;\n    new (input: T): Box<T>;\n    [key: string]: T;\n}",
        );
        let interface_symbol = bound
            .symbol(node_ref(&parsed.arena, file, interface))
            .unwrap();
        let interface_record = binder.symbol_store().symbol(interface_symbol).unwrap();
        assert_eq!(interface_record.flags(), SymbolFlags::INTERFACE);
        let interface_members = binder
            .symbol_store()
            .symbol_table(interface_record.members().unwrap())
            .unwrap();
        for name in ["T", "value", "method", "item"] {
            assert!(
                interface_members.get_source(name).is_some(),
                "missing interface member {name}"
            );
        }
        assert!(
            interface_members
                .get(InternalSymbolName::Call.as_ref())
                .is_some()
        );
        assert!(
            interface_members
                .get(InternalSymbolName::New.as_ref())
                .is_some()
        );
        assert!(
            interface_members
                .get(InternalSymbolName::Index.as_ref())
                .is_some()
        );

        let class = node_with_source(
            &parsed.arena,
            SyntaxKind::ClassDeclaration,
            "class Model<T> {\n    static count: number;\n    value?: T;\n    constructor(public id: string, value: T) { this.value = value; }\n    method<U>(input: U): U { return input; }\n    get item(): T { return this.value; }\n    set item(value: T) { this.value = value; }\n}",
        );
        let class_symbol = bound.symbol(node_ref(&parsed.arena, file, class)).unwrap();
        let class_record = binder.symbol_store().symbol(class_symbol).unwrap();
        let class_members = binder
            .symbol_store()
            .symbol_table(class_record.members().unwrap())
            .unwrap();
        for name in ["T", "value", "id", "method", "item"] {
            assert!(class_members.get_source(name).is_some());
        }
        assert!(
            class_members
                .get(InternalSymbolName::Constructor.as_ref())
                .is_some()
        );
        let class_exports = binder
            .symbol_store()
            .symbol_table(class_record.exports().unwrap())
            .unwrap();
        assert!(class_exports.get_source("count").is_some());
        let prototype = class_exports.get_source("prototype").unwrap();
        let prototype_record = binder.symbol_store().symbol(prototype).unwrap();
        assert_eq!(
            prototype_record.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE
        );
        assert_eq!(prototype_record.parent(), Some(class_symbol));
        assert!(prototype_record.declarations().is_none());

        let constructor = nodes_of_kind(&parsed.arena, SyntaxKind::Constructor)[0];
        let constructor_locals = binder
            .symbol_store()
            .symbol_table(
                bound
                    .locals(node_ref(&parsed.arena, file, constructor))
                    .unwrap(),
            )
            .unwrap();
        let NodeData::ConstructorDeclaration(constructor_data) =
            &parsed.arena.get(constructor).unwrap().data
        else {
            unreachable!();
        };
        let property_parameter = constructor_data.parameters.nodes[0];
        let local_parameter = constructor_locals.get_source("id").unwrap();
        let property = class_members.get_source("id").unwrap();
        assert_ne!(local_parameter, property);
        assert_eq!(
            bound
                .symbol(node_ref(&parsed.arena, file, property_parameter))
                .unwrap(),
            property
        );
        assert_eq!(
            binder.symbol_store().symbol(property).unwrap().flags(),
            SymbolFlags::PROPERTY
        );

        let function_type = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionType)[0];
        let function_type_symbol = bound
            .symbol(node_ref(&parsed.arena, file, function_type))
            .unwrap();
        let function_type_record = binder.symbol_store().symbol(function_type_symbol).unwrap();
        assert_eq!(function_type_record.flags(), SymbolFlags::TYPE_LITERAL);
        let signature = binder
            .symbol_store()
            .symbol_table(function_type_record.members().unwrap())
            .unwrap()
            .get(InternalSymbolName::Call.as_ref())
            .unwrap();
        assert_eq!(
            binder.symbol_store().symbol(signature).unwrap().flags(),
            SymbolFlags::SIGNATURE
        );
        assert!(bound.diagnostics().is_empty());
    }

    #[test]
    fn reopened_interfaces_merge_method_index_and_accessor_symbols() {
        let parsed = parse_source_file(concat!(
            "interface Combined { ",
            "method(value: string): number; ",
            "[key: string]: number; ",
            "get item(): number; ",
            "set item(value: number); ",
            "} ",
            "interface Combined { ",
            "method(value: number): number; ",
            "[key: number]: number; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(93);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/merged-interface.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        let interface = locals.get_source("Combined").unwrap();
        assert_eq!(
            binder
                .symbol_store()
                .symbol(interface)
                .unwrap()
                .declarations()
                .unwrap()
                .len(),
            2
        );
        let members = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(interface)
                    .unwrap()
                    .members()
                    .unwrap(),
            )
            .unwrap();
        for (name, expected_flags, declaration_count) in [
            ("method", SymbolFlags::METHOD, 2),
            (
                "item",
                SymbolFlags::GET_ACCESSOR | SymbolFlags::SET_ACCESSOR,
                2,
            ),
        ] {
            let symbol = members.get_source(name).unwrap();
            let record = binder.symbol_store().symbol(symbol).unwrap();
            assert_eq!(record.flags(), expected_flags);
            assert_eq!(record.parent(), Some(interface));
            assert_eq!(record.declarations().unwrap().len(), declaration_count);
        }
        let indexes = members.get(InternalSymbolName::Index.as_ref()).unwrap();
        let index_record = binder.symbol_store().symbol(indexes).unwrap();
        assert_eq!(index_record.flags(), SymbolFlags::SIGNATURE);
        assert_eq!(index_record.declarations().unwrap().len(), 2);
    }

    #[test]
    fn constructor_parameter_properties_keep_distinct_locals_and_class_members() {
        let parsed = parse_source_file(concat!(
            "class Model { constructor(",
            "private readonly hidden: string, ",
            "protected shared: number, ",
            "readonly fixed = 1, ",
            "public optional?: boolean",
            ") {} }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(94);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/parameters.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let class = nodes_of_kind(&parsed.arena, SyntaxKind::ClassDeclaration)[0];
        let class_symbol = bound.symbol(node_ref(&parsed.arena, file, class)).unwrap();
        let members = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(class_symbol)
                    .unwrap()
                    .members()
                    .unwrap(),
            )
            .unwrap();
        let constructor = nodes_of_kind(&parsed.arena, SyntaxKind::Constructor)[0];
        let locals = binder
            .symbol_store()
            .symbol_table(
                bound
                    .locals(node_ref(&parsed.arena, file, constructor))
                    .unwrap(),
            )
            .unwrap();
        for name in ["hidden", "shared", "fixed", "optional"] {
            let property = members.get_source(name).unwrap();
            let local = locals.get_source(name).unwrap();
            assert_ne!(property, local, "{name}");
            let expected_flags = SymbolFlags::PROPERTY
                | if name == "optional" {
                    SymbolFlags::OPTIONAL
                } else {
                    SymbolFlags::NONE
                };
            assert_eq!(
                binder.symbol_store().symbol(property).unwrap().flags(),
                expected_flags,
                "{name}"
            );
            assert_eq!(
                binder.symbol_store().symbol(property).unwrap().parent(),
                Some(class_symbol)
            );
        }
    }

    #[test]
    fn loop_binding_patterns_keep_iteration_and_body_scope_symbols() {
        let parsed = parse_source_file(concat!(
            "for (const [key, value] of entries) { ",
            "const { inner, nested: { deep } } = value; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(95);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/loop-bindings.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        assert!(bound.flow_graph().is_complete(), "{:?}", bound.flow_graph());
        let loop_node = nodes_of_kind(&parsed.arena, SyntaxKind::ForOfStatement)[0];
        let loop_locals = binder
            .symbol_store()
            .symbol_table(
                bound
                    .locals(node_ref(&parsed.arena, file, loop_node))
                    .unwrap(),
            )
            .unwrap();
        for name in ["key", "value"] {
            assert!(loop_locals.get_source(name).is_some(), "{name}");
        }
        let body = nodes_of_kind(&parsed.arena, SyntaxKind::Block)[0];
        let body_locals = binder
            .symbol_store()
            .symbol_table(bound.locals(node_ref(&parsed.arena, file, body)).unwrap())
            .unwrap();
        for name in ["inner", "deep"] {
            assert!(body_locals.get_source(name).is_some(), "{name}");
            assert!(loop_locals.get_source(name).is_none());
        }
        assert_eq!(bound.locals(bound.source_file()), None);
    }

    #[test]
    fn object_shorthand_and_computed_members_keep_exact_declaration_symbols() {
        let parsed = parse_source_file(
            "const value = 1; const source = { source: value }; const object = { ...source, value, ['named']: value, [1]: value, [dynamic]: value };",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(91);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/object.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let object = variable_initializers_named(&parsed.arena, "object")[0];
        let owner = bound.symbol(node_ref(&parsed.arena, file, object)).unwrap();
        let members = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(owner)
                    .unwrap()
                    .members()
                    .unwrap(),
            )
            .unwrap();
        for name in ["value", "named", "1"] {
            let symbol = members.get_source(name).unwrap();
            let record = binder.symbol_store().symbol(symbol).unwrap();
            assert_eq!(record.flags(), SymbolFlags::PROPERTY);
            assert_eq!(record.parent(), Some(owner));
            assert_eq!(record.declarations().unwrap().len(), 1);
        }
        assert_eq!(members.len(), 3);

        let dynamic =
            node_with_source_fragment(&parsed.arena, SyntaxKind::PropertyAssignment, "[dynamic]");
        let dynamic_symbol = bound
            .symbol(node_ref(&parsed.arena, file, dynamic))
            .unwrap();
        let dynamic_record = binder.symbol_store().symbol(dynamic_symbol).unwrap();
        assert_eq!(dynamic_record.name(), InternalSymbolName::Computed.as_ref());
        assert_eq!(dynamic_record.parent(), Some(owner));
        let spread = nodes_of_kind(&parsed.arena, SyntaxKind::SpreadAssignment)[0];
        assert_eq!(bound.symbol(node_ref(&parsed.arena, file, spread)), None);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn typescript_expandos_bind_after_declarations_with_exact_static_and_dynamic_records() {
        let parsed = parse_source_file(
            r#"
Forward.before = 0;
Forward["literal"] = 1;
Forward.same = 2;
Forward.same = 3;
Forward[key] = 4;
Forward[other] = 5;
Forward[+0] = 6;
function Forward() {}
function module() {}
module.exports = 7;

Arrow.before = 1;
const Arrow = () => {};
const Expression = function () {};
Expression.property = 1;
namespace NS {
    export function nested() {}
    nested.value = 1;
}
"#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(67);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/expandos\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        assert_eq!(bound.phase(), BindingPhase::Declarations);
        let source_locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        let forward = source_locals.get_source("Forward").unwrap();
        let forward_record = binder.symbol_store().symbol(forward).unwrap();
        assert_eq!(forward_record.flags(), SymbolFlags::FUNCTION);
        let forward_exports = binder
            .symbol_store()
            .symbol_table(forward_record.exports().unwrap())
            .unwrap();
        for name in ["before", "literal", "same"] {
            let property = forward_exports.get_source(name).unwrap();
            let record = binder.symbol_store().symbol(property).unwrap();
            assert_eq!(
                record.flags(),
                SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
            );
            assert_eq!(record.parent(), Some(forward));
        }

        let same_first = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "Forward.same = 2",
        );
        let same_second = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "Forward.same = 3",
        );
        let same = forward_exports.get_source("same").unwrap();
        assert_eq!(
            binder.symbol_store().symbol(same).unwrap().declarations(),
            Some(
                [
                    node_ref(&parsed.arena, file, same_first),
                    node_ref(&parsed.arena, file, same_second),
                ]
                .as_slice()
            )
        );
        assert_eq!(
            bound.symbol(node_ref(&parsed.arena, file, same_first)),
            Some(same)
        );
        assert_eq!(
            bound.symbol(node_ref(&parsed.arena, file, same_second)),
            Some(same)
        );

        let dynamic_nodes = [
            node_with_source(
                &parsed.arena,
                SyntaxKind::BinaryExpression,
                "Forward[key] = 4",
            ),
            node_with_source(
                &parsed.arena,
                SyntaxKind::BinaryExpression,
                "Forward[other] = 5",
            ),
        ];
        for dynamic in dynamic_nodes {
            let computed = bound
                .symbol(node_ref(&parsed.arena, file, dynamic))
                .unwrap();
            let record = binder.symbol_store().symbol(computed).unwrap();
            assert_eq!(record.name(), InternalSymbolName::Computed.as_ref());
            assert_eq!(
                record.flags(),
                SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
            );
            assert_eq!(record.parent(), None);
        }
        let assignments = forward_exports
            .get(InternalSymbolName::AssignmentDeclaration.as_ref())
            .unwrap();
        let assignment_record = binder.symbol_store().symbol(assignments).unwrap();
        assert_eq!(assignment_record.flags(), SymbolFlags::NONE);
        assert_eq!(assignment_record.parent(), None);
        assert_eq!(assignment_record.value_declaration(), None);
        assert_eq!(
            assignment_record.declarations(),
            Some(
                dynamic_nodes
                    .map(|node| node_ref(&parsed.arena, file, node))
                    .as_slice()
            )
        );

        // The pinned access-name helper deliberately does not turn signed
        // numeric element names into a table key. It still creates the
        // detached missing-name declaration because the name is not dynamic.
        let signed = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "Forward[+0] = 6",
        );
        let signed_symbol = bound.symbol(node_ref(&parsed.arena, file, signed)).unwrap();
        assert_eq!(
            binder.symbol_store().symbol(signed_symbol).unwrap().name(),
            InternalSymbolName::Missing.as_ref()
        );
        assert!(
            forward_exports
                .get(InternalSymbolName::Missing.as_ref())
                .is_none()
        );

        // In a TypeScript file this is an ordinary property expando on a
        // function named `module`; the JavaScript-only module.exports route
        // must not be selected.
        let module = source_locals.get_source("module").unwrap();
        let module_exports = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(module)
                    .unwrap()
                    .exports()
                    .unwrap(),
            )
            .unwrap();
        assert!(module_exports.get_source("exports").is_some());

        let arrow = variable_initializers_named(&parsed.arena, "Arrow")[0];
        let arrow_symbol = bound.symbol(node_ref(&parsed.arena, file, arrow)).unwrap();
        let arrow_exports = binder
            .symbol_store()
            .symbol(arrow_symbol)
            .unwrap()
            .exports()
            .unwrap();
        assert!(
            binder
                .symbol_store()
                .symbol_table(arrow_exports)
                .unwrap()
                .get_source("before")
                .is_some()
        );
        assert_eq!(
            binder
                .symbol_store()
                .symbol(source_locals.get_source("Arrow").unwrap())
                .unwrap()
                .exports(),
            None
        );

        let expression = variable_initializers_named(&parsed.arena, "Expression")[0];
        let expression_symbol = bound
            .symbol(node_ref(&parsed.arena, file, expression))
            .unwrap();
        let expression_exports = binder
            .symbol_store()
            .symbol(expression_symbol)
            .unwrap()
            .exports()
            .unwrap();
        assert!(
            binder
                .symbol_store()
                .symbol_table(expression_exports)
                .unwrap()
                .get_source("property")
                .is_some()
        );

        let namespace = source_locals.get_source("NS").unwrap();
        let namespace_exports = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(namespace)
                    .unwrap()
                    .exports()
                    .unwrap(),
            )
            .unwrap();
        let nested = namespace_exports.get_source("nested").unwrap();
        let nested_exports = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(nested)
                    .unwrap()
                    .exports()
                    .unwrap(),
            )
            .unwrap();
        assert!(nested_exports.get_source("value").is_some());
        assert!(bound.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn typescript_expando_lookup_preserves_shadowing_and_fail_closed_boundaries() {
        let parsed = parse_source_file(
            r#"
function Scope() {
    const Target = () => {};
    {
        let Target = () => {};
        Target.blocked = 1;
    }
    {
        Target.fallback = 2;
    }
    Target.attached = 1;
}
let Loose = () => {};
Loose.nope = 1;
var VarFn = function () {};
VarFn.nope = 1;
const Classy = class {};
Classy.nope = 1;
function Declared() {}
Object.defineProperty(Declared, "defined", { value: 1 });
Declared["compound"] += 1;
factory().ignored = 1;
function Merged() {}
namespace Merged { export const member = 1; }
Merged.member = 2;
Merged.fresh = 1;
"#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(68);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/expando-boundaries\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let targets = variable_initializers_named(&parsed.arena, "Target");
        assert_eq!(targets.len(), 2);
        let outer_target = bound
            .symbol(node_ref(&parsed.arena, file, targets[0]))
            .unwrap();
        let inner_target = bound
            .symbol(node_ref(&parsed.arena, file, targets[1]))
            .unwrap();
        let outer_exports = binder
            .symbol_store()
            .symbol(outer_target)
            .unwrap()
            .exports()
            .unwrap();
        assert!(
            binder
                .symbol_store()
                .symbol_table(outer_exports)
                .unwrap()
                .get_source("attached")
                .is_some()
        );
        assert!(
            binder
                .symbol_store()
                .symbol_table(outer_exports)
                .unwrap()
                .get_source("fallback")
                .is_some()
        );
        assert_eq!(
            binder
                .symbol_store()
                .symbol(inner_target)
                .unwrap()
                .exports(),
            None
        );
        let blocked = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "Target.blocked = 1",
        );
        assert_eq!(bound.symbol(node_ref(&parsed.arena, file, blocked)), None);

        for (name, assignment) in [
            ("Loose", "Loose.nope = 1"),
            ("VarFn", "VarFn.nope = 1"),
            ("Classy", "Classy.nope = 1"),
        ] {
            let initializer = variable_initializers_named(&parsed.arena, name)[0];
            let initializer_symbol = bound
                .symbol(node_ref(&parsed.arena, file, initializer))
                .unwrap();
            let has_property = binder
                .symbol_store()
                .symbol(initializer_symbol)
                .unwrap()
                .exports()
                .and_then(|exports| binder.symbol_store().symbol_table(exports))
                .is_some_and(|exports| exports.get_source("nope").is_some());
            assert!(!has_property, "unexpected expando on {name}");
            let assignment =
                node_with_source(&parsed.arena, SyntaxKind::BinaryExpression, assignment);
            assert_eq!(
                bound.symbol(node_ref(&parsed.arena, file, assignment)),
                None
            );
        }

        let source_locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        let declared = source_locals.get_source("Declared").unwrap();
        let declared_exports = binder.symbol_store().symbol(declared).unwrap().exports();
        assert!(declared_exports.is_none_or(|exports| {
            let exports = binder.symbol_store().symbol_table(exports).unwrap();
            exports.get_source("defined").is_none() && exports.get_source("compound").is_none()
        }));
        let ignored = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "factory().ignored = 1",
        );
        assert_eq!(bound.symbol(node_ref(&parsed.arena, file, ignored)), None);

        let merged = source_locals.get_source("Merged").unwrap();
        let merged_exports = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(merged)
                    .unwrap()
                    .exports()
                    .unwrap(),
            )
            .unwrap();
        assert!(merged_exports.get_source("member").is_some());
        let existing_member = merged_exports.get_source("member").unwrap();
        let member_assignment = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "Merged.member = 2",
        );
        assert_eq!(
            bound.symbol(node_ref(&parsed.arena, file, member_assignment)),
            None
        );
        assert!(
            binder
                .symbol_store()
                .symbol(existing_member)
                .unwrap()
                .flags()
                .intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE)
        );
        let fresh_property = merged_exports.get_source("fresh").unwrap();
        let fresh = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "Merged.fresh = 1",
        );
        assert_eq!(
            bound.symbol(node_ref(&parsed.arena, file, fresh)),
            Some(fresh_property)
        );
        assert_eq!(
            binder
                .symbol_store()
                .symbol(fresh_property)
                .unwrap()
                .flags(),
            SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
        );
        assert_eq!(bound.phase(), BindingPhase::Declarations);
        assert!(bound.diagnostics().is_empty());
    }

    #[test]
    fn javascript_duplicate_function_implementations_share_their_declaration_symbol() {
        let parsed =
            parse_javascript_source_file("function repeated() {} function repeated(arg) {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(92);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/repeated.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        assert!(bound.diagnostics().is_empty(), "{:?}", bound.diagnostics());
        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        let repeated = locals.get_source("repeated").unwrap();
        let record = binder.symbol_store().symbol(repeated).unwrap();
        assert_eq!(record.flags(), SymbolFlags::FUNCTION);
        let declarations = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionDeclaration);
        let expected = declarations
            .iter()
            .map(|node| node_ref(&parsed.arena, file, *node))
            .collect::<Vec<_>>();
        assert_eq!(record.declarations(), Some(expected.as_slice()));
        for declaration in declarations {
            assert_eq!(
                bound.symbol(node_ref(&parsed.arena, file, declaration)),
                Some(repeated)
            );
        }
    }

    #[test]
    fn javascript_dynamic_export_names_do_not_create_commonjs_module_indicators() {
        let parsed = parse_javascript_source_file("function F() {} exports[dynamic] = F;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(69);
        let assignment = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "exports[dynamic] = F",
        );
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/expando.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        assert_eq!(
            binder.bind_typescript_declaration_slice(&parsed.arena, file),
            Err(CanonicalDeclarationError::JavaScriptDeclarationsDeferred(
                file
            ))
        );
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        assert_eq!(bound.phase(), BindingPhase::Declarations);
        assert!(!bound.source_facts().unwrap().is_common_js_module());
        assert_eq!(bound.symbol(bound.source_file()), None);
        assert_eq!(
            bound.symbol(node_ref(&parsed.arena, file, assignment)),
            None
        );
        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        assert!(locals.get_source("F").is_some());
        assert!(locals.get_source("exports").is_none());
    }

    #[test]
    fn javascript_module_exports_self_assignment_does_not_create_commonjs_module() {
        let parsed = parse_javascript_source_file("module.exports = exports; const marker = 1;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(77);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/self-assignment.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        assert!(!bound.source_facts().unwrap().is_common_js_module());
        assert_eq!(bound.symbol(bound.source_file()), None);
        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        assert!(locals.get_source("marker").is_some());
        assert!(locals.get_source("module").is_none());
        assert!(locals.get_source("exports").is_none());
        let assignment = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "module.exports = exports",
        );
        assert_eq!(
            bound.symbol(node_ref(&parsed.arena, file, assignment)),
            None
        );
    }

    #[test]
    fn javascript_require_calls_need_exactly_one_argument_for_commonjs() {
        for (index, (source, expected_commonjs, expected_flags)) in [
            (
                "const dependency = require();",
                false,
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
            ),
            (
                "const dependency = require(first, second);",
                false,
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
            ),
            (
                "const dependency = require(first);",
                true,
                SymbolFlags::ALIAS,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_javascript_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(78 + u32::try_from(index).unwrap());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/require.js\""),
                        CanonicalSourceLanguage::JavaScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_javascript_declaration_slice(&parsed.arena, file)
                .unwrap();

            let bound = binder.file(file).unwrap();
            assert_eq!(
                bound.source_facts().unwrap().is_common_js_module(),
                expected_commonjs,
                "{source}"
            );
            let locals = binder
                .symbol_store()
                .symbol_table(bound.locals(bound.source_file()).unwrap())
                .unwrap();
            let dependency = locals.get_source("dependency").unwrap();
            assert_eq!(
                binder.symbol_store().symbol(dependency).unwrap().flags(),
                expected_flags,
                "{source}"
            );
            assert_eq!(locals.get_source("module").is_some(), expected_commonjs);
            assert_eq!(locals.get_source("exports").is_some(), expected_commonjs);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep one complete CommonJS binding scenario together.
    fn javascript_commonjs_assignments_create_exact_source_exports_and_locals() {
        let parsed = parse_javascript_source_file(concat!(
            "exports.first = 1;\n",
            "exports.alias = local;\n",
            "module.exports = local;\n",
            "module.exports[1] = 2;\n",
            "Object.defineProperty(exports, 'defined', {});\n",
            "const local = {};\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(73);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/common.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        assert!(bound.source_facts().unwrap().is_common_js_module());
        assert!(!bound.source_facts().unwrap().is_external_module());
        let source = bound.symbol(bound.source_file()).unwrap();
        let source_record = binder.symbol_store().symbol(source).unwrap();
        assert_eq!(source_record.flags(), SymbolFlags::VALUE_MODULE);
        let exports = binder
            .symbol_store()
            .symbol_table(source_record.exports().unwrap())
            .unwrap();
        for name in ["first", "alias", "1", "defined"] {
            assert!(exports.get_source(name).is_some(), "{name}");
        }
        assert_eq!(
            binder
                .symbol_store()
                .symbol(exports.get_source("first").unwrap())
                .unwrap()
                .flags(),
            SymbolFlags::FUNCTION_SCOPED_VARIABLE
        );
        assert_eq!(
            binder
                .symbol_store()
                .symbol(exports.get_source("alias").unwrap())
                .unwrap()
                .flags(),
            SymbolFlags::ALIAS
        );
        let export_equals = exports
            .get(InternalSymbolName::ExportEquals.as_ref())
            .unwrap();
        let assignment = node_with_source(
            &parsed.arena,
            SyntaxKind::BinaryExpression,
            "module.exports = local",
        );
        assert_eq!(
            binder
                .symbol_store()
                .symbol(export_equals)
                .unwrap()
                .value_declaration(),
            Some(node_ref(&parsed.arena, file, assignment))
        );

        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        let module = locals.get_source("module").unwrap();
        let exports_local = locals.get_source("exports").unwrap();
        assert!(
            binder
                .symbol_store()
                .symbol(exports_local)
                .unwrap()
                .flags()
                .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::MODULE_EXPORTS)
        );
        let module_exports = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(module)
                    .unwrap()
                    .members()
                    .unwrap(),
            )
            .unwrap()
            .get_source("exports")
            .unwrap();
        assert_eq!(
            binder
                .symbol_store()
                .symbol(module_exports)
                .unwrap()
                .parent(),
            Some(module)
        );
    }

    #[test]
    fn javascript_expandos_follow_function_class_object_and_annotation_rules() {
        let parsed = parse_javascript_source_file(concat!(
            "Forward.before = 0;\n",
            "function Forward() {}\n",
            "var bag = {};\n",
            "bag['if'] = 1;\n",
            "let callback = () => {};\n",
            "callback.value = 2;\n",
            "class Box {}\n",
            "Box.staticValue = 3;\n",
            "/** @type {Record<string, boolean>} */\n",
            "let typed = {};\n",
            "typed.ignored = true;\n",
            "function owner() {}\n",
            "/** @type {Record<string, boolean>} */\n",
            "owner.bucket = {};\n",
            "owner.bucket.ignored = true;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(74);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/expandos.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        for (owner, initializer, property) in [
            ("Forward", None, "before"),
            ("bag", Some("bag"), "if"),
            ("callback", Some("callback"), "value"),
            ("Box", None, "staticValue"),
        ] {
            let symbol = initializer.map_or_else(
                || locals.get_source(owner).unwrap(),
                |name| {
                    let initializer = variable_initializers_named(&parsed.arena, name)[0];
                    bound
                        .symbol(node_ref(&parsed.arena, file, initializer))
                        .unwrap()
                },
            );
            let exports = binder
                .symbol_store()
                .symbol_table(
                    binder
                        .symbol_store()
                        .symbol(symbol)
                        .unwrap()
                        .exports()
                        .unwrap(),
                )
                .unwrap();
            let declaration = exports.get_source(property).unwrap();
            assert_eq!(
                binder.symbol_store().symbol(declaration).unwrap().flags(),
                SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
            );
        }

        let typed_initializer = variable_initializers_named(&parsed.arena, "typed")[0];
        let typed = bound
            .symbol(node_ref(&parsed.arena, file, typed_initializer))
            .unwrap();
        assert_eq!(binder.symbol_store().symbol(typed).unwrap().exports(), None);

        let owner = locals.get_source("owner").unwrap();
        let owner_exports = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(owner)
                    .unwrap()
                    .exports()
                    .unwrap(),
            )
            .unwrap();
        let bucket = owner_exports.get_source("bucket").unwrap();
        assert_eq!(
            binder.symbol_store().symbol(bucket).unwrap().exports(),
            None
        );
    }

    #[test]
    fn javascript_this_assignments_preserve_method_replacement_and_static_ownership() {
        let parsed = parse_javascript_source_file(concat!(
            "class Fields { constructor() { this.value = 1; this.value = 2; } }\n",
            "class Replaced { constructor() { this.work = () => {}; } work() {} }\n",
            "class Kept { work() {} constructor() { this.work = () => {}; } }\n",
            "class Static { static init() { this.value = 1; } }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(75);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/classes.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        let fields = locals.get_source("Fields").unwrap();
        let fields_members = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(fields)
                    .unwrap()
                    .members()
                    .unwrap(),
            )
            .unwrap();
        let value = fields_members.get_source("value").unwrap();
        let value_record = binder.symbol_store().symbol(value).unwrap();
        assert!(
            value_record
                .flags()
                .contains(SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT)
        );
        assert_eq!(value_record.declarations().unwrap().len(), 2);

        for class in ["Replaced", "Kept"] {
            let symbol = locals.get_source(class).unwrap();
            let members = binder
                .symbol_store()
                .symbol_table(
                    binder
                        .symbol_store()
                        .symbol(symbol)
                        .unwrap()
                        .members()
                        .unwrap(),
                )
                .unwrap();
            assert_eq!(
                binder
                    .symbol_store()
                    .symbol(members.get_source("work").unwrap())
                    .unwrap()
                    .flags(),
                SymbolFlags::METHOD,
                "{class}"
            );
        }

        let static_class = locals.get_source("Static").unwrap();
        let static_exports = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(static_class)
                    .unwrap()
                    .exports()
                    .unwrap(),
            )
            .unwrap();
        assert!(static_exports.get_source("value").is_some());
    }

    #[test]
    fn javascript_jsdoc_aliases_and_namespaces_export_from_commonjs_assignments() {
        let mut parsed = parse_source_file(concat!(
            "type Alias = number;\n",
            "namespace Docs { export type Nested = string; }\n",
            "const value = 1;\n",
            "module.exports = value;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let alias = nodes_of_kind(&parsed.arena, SyntaxKind::TypeAliasDeclaration)[0];
        parsed.arena.get_mut(alias).unwrap().kind = SyntaxKind::JsTypeAliasDeclaration;
        let namespace = nodes_of_kind(&parsed.arena, SyntaxKind::ModuleDeclaration)[0];
        parsed.arena.get_mut(namespace).unwrap().flags.0 |= NodeFlags::REPARSED.0;
        let file = FileId::new(76);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/docs.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let source = bound.symbol(bound.source_file()).unwrap();
        let exports = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(source)
                    .unwrap()
                    .exports()
                    .unwrap(),
            )
            .unwrap();
        let alias_symbol = exports.get_source("Alias").unwrap();
        let namespace_symbol = exports.get_source("Docs").unwrap();
        assert!(
            binder
                .symbol_store()
                .symbol(alias_symbol)
                .unwrap()
                .flags()
                .contains(SymbolFlags::TYPE_ALIAS)
        );
        assert!(
            binder
                .symbol_store()
                .symbol(namespace_symbol)
                .unwrap()
                .flags()
                .contains(SymbolFlags::NAMESPACE_MODULE)
        );
        let export_equals = exports
            .get(InternalSymbolName::ExportEquals.as_ref())
            .unwrap();
        let promoted = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(export_equals)
                    .unwrap()
                    .exports()
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(promoted.get_source("Alias"), Some(alias_symbol));
        assert_eq!(promoted.get_source("Docs"), Some(namespace_symbol));
        assert!(
            binder
                .symbol_store()
                .symbol(export_equals)
                .unwrap()
                .flags()
                .contains(SymbolFlags::NAMESPACE_MODULE)
        );
    }

    #[test]
    fn javascript_scripts_bind_ordinary_declarations_with_jsdoc_comments() {
        let parsed = parse_javascript_source_file(concat!(
            "/** @param {number} value */\n",
            "function read(value) { return value; }\n",
            "/** @type {number} */\n",
            "const input = 1;\n",
            "class Box { value = input; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(70);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/input.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        assert_eq!(bound.phase(), BindingPhase::Declarations);
        assert!(bound.diagnostics().is_empty(), "{:?}", bound.diagnostics());
        let source_locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        for name in ["read", "input", "Box"] {
            assert!(source_locals.get_source(name).is_some(), "{name}");
        }

        let function = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionDeclaration)[0];
        let function_locals = binder
            .symbol_store()
            .symbol_table(
                bound
                    .locals(node_ref(&parsed.arena, file, function))
                    .unwrap(),
            )
            .unwrap();
        assert!(function_locals.get_source("value").is_some());

        let class = source_locals.get_source("Box").unwrap();
        let members = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(class)
                    .unwrap()
                    .members()
                    .unwrap(),
            )
            .unwrap();
        assert!(members.get_source("value").is_some());
    }

    #[test]
    fn javascript_es_modules_share_program_symbols_with_typescript() {
        let javascript = parse_javascript_source_file(
            "import { seed } from './dep.js'; export const value = seed; export function read(input) { return input; }",
        );
        let typescript = parse_source_file("export const typed = 1;");
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        assert!(
            typescript.diagnostics.is_empty(),
            "{:?}",
            typescript.diagnostics
        );
        let javascript_file = FileId::new(71);
        let typescript_file = FileId::new(72);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &javascript.arena,
                javascript.source_file,
                javascript_file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/input.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        binder
            .bind_source_file_with_facts(
                &typescript.arena,
                typescript.source_file,
                typescript_file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/input.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&javascript.arena, javascript_file)
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&typescript.arena, typescript_file)
            .unwrap();

        let javascript_bound = binder.file(javascript_file).unwrap();
        let source = javascript_bound
            .symbol(javascript_bound.source_file())
            .unwrap();
        let exports = binder
            .symbol_store()
            .symbol_table(
                binder
                    .symbol_store()
                    .symbol(source)
                    .unwrap()
                    .exports()
                    .unwrap(),
            )
            .unwrap();
        assert!(exports.get_source("value").is_some());
        assert!(exports.get_source("read").is_some());
        let locals = binder
            .symbol_store()
            .symbol_table(
                javascript_bound
                    .locals(javascript_bound.source_file())
                    .unwrap(),
            )
            .unwrap();
        assert!(locals.get_source("seed").is_some());

        let program = binder.finish();
        assert!(program.declarations_complete());
        assert_eq!(program.try_into_parts().unwrap().1.len(), 2);
    }

    #[test]
    fn completed_typescript_family_files_extract_one_canonical_symbol_store() {
        let ts = parse_source_file("export interface Box<T> { value: T }");
        let tsx = parse_jsx_source_file(
            "export const view = <Component value={1} />; export type View = typeof view;",
        );
        let declaration = parse_source_file(
            "export as namespace Library; export interface PublicShape { id: string }",
        );
        let inputs = [
            (
                &ts,
                FileId::new(61),
                false,
                CanonicalModuleState::External,
                "\"/project/index.mts\"",
            ),
            (
                &tsx,
                FileId::new(62),
                false,
                CanonicalModuleState::External,
                "\"/project/view.tsx\"",
            ),
            (
                &declaration,
                FileId::new(63),
                true,
                CanonicalModuleState::External,
                "\"/project/library.d.cts\"",
            ),
        ];
        assert!(inputs.iter().all(|(parsed, ..)| {
            nodes_of_kind(&parsed.arena, SyntaxKind::JsTypeAliasDeclaration).is_empty()
        }));
        let mut binder = CanonicalBinder::new();
        for (parsed, file, is_declaration, module_state, name) in inputs {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(name),
                        CanonicalSourceLanguage::TypeScript,
                        is_declaration,
                        module_state,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
            let bound = binder.file(file).unwrap();
            assert_eq!(bound.phase(), BindingPhase::Declarations);
            assert!(bound.declarations_complete());
        }

        let program = binder.finish();
        assert!(program.declarations_complete());
        let store_id = program.symbol_store().id();
        for file in program.files() {
            let source = file.symbol(file.source_file()).unwrap();
            assert!(program.symbol_store().contains_symbol(source));
        }
        let (symbols, files) = program.try_into_parts().unwrap();
        assert_eq!(symbols.id(), store_id);
        assert_eq!(files.len(), 3);
    }

    #[test]
    fn deferred_javascript_and_commonjs_files_keep_program_extraction_closed() {
        let javascript = parse_source_file("export const value = 1;");
        let commonjs = parse_source_file("export const other = 2;");
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &javascript.arena,
                javascript.source_file,
                FileId::new(64),
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/allow-js.jsx\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        binder
            .bind_source_file_with_facts(
                &commonjs.arena,
                commonjs.source_file,
                FileId::new(65),
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/common.cts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::ExternalAndCommonJs,
                ),
            )
            .unwrap();
        assert_eq!(
            binder.bind_typescript_declaration_slice(&javascript.arena, FileId::new(64)),
            Err(CanonicalDeclarationError::JavaScriptDeclarationsDeferred(
                FileId::new(64)
            ))
        );
        assert_eq!(
            binder.bind_typescript_declaration_slice(&commonjs.arena, FileId::new(65)),
            Err(CanonicalDeclarationError::CommonJsDeclarationsDeferred(
                FileId::new(65)
            ))
        );
        assert!(binder.finish().try_into_parts().is_err());
    }

    #[test]
    fn external_module_dispatch_preserves_pair_and_hoisted_allocation_order() {
        let parsed = parse_source_file(
            "export class C {} export interface I { value: string } export const value = 1; export function fn() {}",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(45);
        let facts = CanonicalSourceFileFacts::new(
            EscapedName::source("\"/project/external\""),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::External,
        );
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts)
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let bound = binder.file(file).unwrap();
        let source = bound.symbol(bound.source_file()).unwrap();
        assert_eq!(source.get(), 1);
        let source_record = binder.symbol_store().symbol(source).unwrap();
        assert_eq!(source_record.flags(), SymbolFlags::VALUE_MODULE);
        assert_eq!(
            source_record.name().escaped_display().to_string(),
            "\"/project/external\""
        );
        let locals = binder
            .symbol_store()
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        let exports = binder
            .symbol_store()
            .symbol_table(source_record.exports().unwrap())
            .unwrap();

        let named_function = node_with_source(
            &parsed.arena,
            SyntaxKind::FunctionDeclaration,
            "export function fn() {}",
        );
        let named_ref = node_ref(&parsed.arena, file, named_function);
        let named_export = bound.symbol(named_ref).unwrap();
        let named_local = bound.local_symbol(named_ref).unwrap();
        assert_eq!(named_local.get(), 2);
        assert_eq!(named_export.get(), 3);
        assert_eq!(locals.get_source("fn"), Some(named_local));
        assert_eq!(exports.get_source("fn"), Some(named_export));
        assert_eq!(
            binder.symbol_store().symbol(named_local).unwrap().flags(),
            SymbolFlags::EXPORT_VALUE
        );
        assert_eq!(
            binder
                .symbol_store()
                .symbol(named_local)
                .unwrap()
                .export_symbol(),
            Some(named_export)
        );

        let class = nodes_of_kind(&parsed.arena, SyntaxKind::ClassDeclaration)[0];
        let class_ref = node_ref(&parsed.arena, file, class);
        let class_export = bound.symbol(class_ref).unwrap();
        let class_local = bound.local_symbol(class_ref).unwrap();
        assert_eq!(locals.get_source("C"), Some(class_local));
        assert_eq!(exports.get_source("C"), Some(class_export));
        assert_eq!(
            binder.symbol_store().symbol(class_export).unwrap().flags(),
            SymbolFlags::CLASS
        );
        assert!(
            binder
                .symbol_store()
                .symbol_table(
                    binder
                        .symbol_store()
                        .symbol(class_export)
                        .unwrap()
                        .exports()
                        .unwrap()
                )
                .unwrap()
                .get_source("prototype")
                .is_some()
        );
        assert!(bound.diagnostics().is_empty());
    }

    #[test]
    fn duplicate_and_conflicting_file_identity_fail_without_side_effects() {
        let parsed = parse_source_file("const value = 1;");
        let other = parse_source_file("const other = 2;");
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, FileId::new(1))
            .unwrap();
        let table_count = binder.symbol_store().symbol_table_len();

        assert_eq!(
            binder.bind_source_file(&other.arena, other.source_file, FileId::new(1)),
            Err(CanonicalBindError::DuplicateFile(FileId::new(1)))
        );
        assert!(matches!(
            binder.bind_source_file(&parsed.arena, parsed.source_file, FileId::new(2)),
            Err(CanonicalBindError::AstScopeConflict { .. })
        ));
        assert_eq!(binder.symbol_store().symbol_table_len(), table_count);
        assert!(binder.file(FileId::new(2)).is_none());
    }

    #[test]
    fn canonical_file_reuses_the_existing_provenance_bearing_flow_graph() {
        let parsed = parse_source_file("let value = 1; if (value) value = 2;");
        let if_statement = parsed
            .arena
            .iter()
            .find_map(|(id, node)| (node.kind == SyntaxKind::IfStatement).then_some(id))
            .unwrap();
        let mut binder = CanonicalBinder::new();
        let bound = binder
            .bind_source_file(&parsed.arena, parsed.source_file, FileId::new(9))
            .unwrap();
        let statement_ref = NodeRef::new(parsed.arena.id(), FileId::new(9), if_statement);

        assert_eq!(
            bound.flow_at(statement_ref),
            bound.flow_graph().flow_at(statement_ref)
        );
        assert_eq!(
            bound.flow_container(statement_ref),
            bound.flow_graph().flow_container(statement_ref)
        );
        assert_eq!(
            bound.flow_container(statement_ref),
            Some(bound.source_file())
        );
        assert!(bound.flow_graph().is_complete());

        let foreign = NodeRef::new(parsed.arena.id(), FileId::new(10), if_statement);
        assert_eq!(bound.flow_at(foreign), None);
        assert_eq!(bound.flow_container(foreign), None);
    }

    #[test]
    fn follows_pinned_loop_and_iife_child_orders() {
        let parsed = parse_source_file(
            r"
                for (init(); condition(); increment()) body();
                for (left in right()) inBody();
                for await (item of asyncItems()) ofBody();
                (function () {})(argument());
            ",
        );
        let statements = match &parsed.arena.get(parsed.source_file).unwrap().data {
            NodeData::SourceFile(source) => &source.statements.nodes,
            _ => unreachable!(),
        };
        let (for_initializer, for_condition, for_statement, for_incrementor) =
            match &parsed.arena.get(statements[0]).unwrap().data {
                NodeData::ForStatement(statement) => (
                    statement.initializer.unwrap(),
                    statement.condition.unwrap(),
                    statement.statement,
                    statement.incrementor.unwrap(),
                ),
                _ => unreachable!(),
            };
        let (in_expression, in_initializer) = match &parsed.arena.get(statements[1]).unwrap().data {
            NodeData::ForInOrOfStatement(statement) => {
                (statement.expression, statement.initializer)
            }
            _ => unreachable!(),
        };
        let (of_expression, of_await, of_initializer) =
            match &parsed.arena.get(statements[2]).unwrap().data {
                NodeData::ForInOrOfStatement(statement) => (
                    statement.expression,
                    statement.await_modifier.unwrap(),
                    statement.initializer,
                ),
                _ => unreachable!(),
            };
        let iife_call = match &parsed.arena.get(statements[3]).unwrap().data {
            NodeData::ExpressionStatement(statement) => statement.expression,
            _ => unreachable!(),
        };
        let (iife_callee, iife_argument) = match &parsed.arena.get(iife_call).unwrap().data {
            NodeData::CallExpression(call) => (call.expression, call.arguments.nodes[0]),
            _ => unreachable!(),
        };

        let mut binder = CanonicalBinder::new();
        let bound = binder
            .bind_source_file(&parsed.arena, parsed.source_file, FileId::new(10))
            .unwrap();
        let order = bound.traversal_order().collect::<Vec<_>>();

        assert!(position(&order, for_initializer) < position(&order, for_condition));
        assert!(position(&order, for_condition) < position(&order, for_statement));
        assert!(position(&order, for_statement) < position(&order, for_incrementor));
        assert!(position(&order, in_expression) < position(&order, in_initializer));
        assert!(position(&order, of_expression) < position(&order, of_await));
        assert!(position(&order, of_await) < position(&order, of_initializer));
        assert!(position(&order, iife_argument) < position(&order, iife_callee));
    }

    #[test]
    fn unreachable_blocks_use_generated_statement_order() {
        let parsed = parse_source_file(
            r"
                function outer() {
                    return;
                    {
                        const before = 0;
                        function after() {}
                    }
                }
            ",
        );
        let outer = match &parsed.arena.get(parsed.source_file).unwrap().data {
            NodeData::SourceFile(source) => source.statements.nodes[0],
            _ => unreachable!(),
        };
        let outer_body = match &parsed.arena.get(outer).unwrap().data {
            NodeData::FunctionDeclaration(function) => function.body.unwrap(),
            _ => unreachable!(),
        };
        let unreachable_block = match &parsed.arena.get(outer_body).unwrap().data {
            NodeData::Block(block) => block.statements.nodes[1],
            _ => unreachable!(),
        };
        let (variable, function) = match &parsed.arena.get(unreachable_block).unwrap().data {
            NodeData::Block(block) => (block.statements.nodes[0], block.statements.nodes[1]),
            _ => unreachable!(),
        };

        let mut binder = CanonicalBinder::new();
        let bound = binder
            .bind_source_file(&parsed.arena, parsed.source_file, FileId::new(11))
            .unwrap();
        let order = bound.traversal_order().collect::<Vec<_>>();

        assert!(position(&order, variable) < position(&order, function));
    }

    #[test]
    fn unsupported_flow_still_walks_all_ordinary_children() {
        let parsed = parse_source_file(
            r"
                try {
                    const ordinary = 1;
                    function nested() {}
                } finally {
                    cleanup();
                }
            ",
        );
        let try_statement = match &parsed.arena.get(parsed.source_file).unwrap().data {
            NodeData::SourceFile(source) => source.statements.nodes[0],
            _ => unreachable!(),
        };
        let try_block = match &parsed.arena.get(try_statement).unwrap().data {
            NodeData::TryStatement(statement) => statement.try_block,
            _ => unreachable!(),
        };
        let (ordinary, nested) = match &parsed.arena.get(try_block).unwrap().data {
            NodeData::Block(block) => (block.statements.nodes[0], block.statements.nodes[1]),
            _ => unreachable!(),
        };

        let mut binder = CanonicalBinder::new();
        let bound = binder
            .bind_source_file(&parsed.arena, parsed.source_file, FileId::new(16))
            .unwrap();
        let order = bound.traversal_order().collect::<Vec<_>>();

        assert!(!bound.flow_graph().is_complete());
        assert!(bound.contains(NodeRef::new(parsed.arena.id(), FileId::new(16), ordinary)));
        assert!(position(&order, nested) < position(&order, ordinary));
        assert_eq!(
            order.iter().map(|node| node.node).collect::<BTreeSet<_>>(),
            reachable_nodes(&parsed.arena, parsed.source_file)
        );
    }

    #[test]
    fn nested_destructuring_defaults_preserve_assignment_pattern_order() {
        let parsed = parse_source_file("[[value] = inner()] = outer();");
        let outer_assignment = match &parsed.arena.get(parsed.source_file).unwrap().data {
            NodeData::SourceFile(source) => {
                match &parsed.arena.get(source.statements.nodes[0]).unwrap().data {
                    NodeData::ExpressionStatement(statement) => statement.expression,
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        };
        let outer_pattern = match &parsed.arena.get(outer_assignment).unwrap().data {
            NodeData::BinaryExpression(expression) => expression.left,
            _ => unreachable!(),
        };
        let inner_assignment = match &parsed.arena.get(outer_pattern).unwrap().data {
            NodeData::ArrayLiteralExpression(pattern) => pattern.elements.nodes[0],
            _ => unreachable!(),
        };
        let (inner_pattern, inner_operator, inner_default) =
            match &parsed.arena.get(inner_assignment).unwrap().data {
                NodeData::BinaryExpression(expression) => {
                    (expression.left, expression.operator_token, expression.right)
                }
                _ => unreachable!(),
            };

        let mut binder = CanonicalBinder::new();
        let bound = binder
            .bind_source_file(&parsed.arena, parsed.source_file, FileId::new(17))
            .unwrap();
        let order = bound.traversal_order().collect::<Vec<_>>();

        assert!(position(&order, inner_operator) < position(&order, inner_default));
        assert!(position(&order, inner_default) < position(&order, inner_pattern));
    }

    #[test]
    fn malformed_parent_backlinks_are_rejected_atomically() {
        let mut parsed = parse_source_file("const value = 1;");
        let source = parsed.source_file;
        let statement = match &parsed.arena.get(source).unwrap().data {
            NodeData::SourceFile(source) => source.statements.nodes[0],
            _ => unreachable!(),
        };
        parsed.arena.get_mut(statement).unwrap().parent = None;
        let file = FileId::new(12);
        let statement_ref = NodeRef::new(parsed.arena.id(), file, statement);
        let root_ref = NodeRef::new(parsed.arena.id(), file, source);
        let mut binder = CanonicalBinder::new();

        assert_eq!(
            binder.bind_source_file(&parsed.arena, source, file),
            Err(CanonicalBindError::InvalidParent {
                node: statement_ref,
                expected: Some(source),
                actual: None,
            })
        );
        assert_eq!(binder.symbol_store().symbol_len(), 0);
        assert_eq!(binder.symbol_store().symbol_table_len(), 0);
        assert!(!binder.symbol_store().contains_node_ref(root_ref));
        assert!(binder.file(file).is_none());
    }

    #[test]
    fn malformed_root_parent_is_rejected_atomically() {
        let mut parsed = parse_source_file("");
        let source = parsed.source_file;
        let end_of_file = match &parsed.arena.get(source).unwrap().data {
            NodeData::SourceFile(source) => source.end_of_file_token,
            _ => unreachable!(),
        };
        parsed.arena.get_mut(source).unwrap().parent = Some(end_of_file);
        let file = FileId::new(13);
        let root_ref = NodeRef::new(parsed.arena.id(), file, source);
        let mut binder = CanonicalBinder::new();

        assert_eq!(
            binder.bind_source_file(&parsed.arena, source, file),
            Err(CanonicalBindError::InvalidParent {
                node: root_ref,
                expected: None,
                actual: Some(end_of_file),
            })
        );
        assert_eq!(binder.symbol_store().symbol_len(), 0);
        assert_eq!(binder.symbol_store().symbol_table_len(), 0);
        assert!(!binder.symbol_store().contains_node_ref(root_ref));
        assert!(binder.file(file).is_none());
    }

    #[test]
    fn mismatched_kind_and_data_are_rejected_atomically() {
        let mut parsed = parse_source_file("function f() {}");
        let source = parsed.source_file;
        let function = match &parsed.arena.get(source).unwrap().data {
            NodeData::SourceFile(source) => source.statements.nodes[0],
            _ => unreachable!(),
        };
        parsed.arena.get_mut(function).unwrap().kind = SyntaxKind::Block;
        let file = FileId::new(14);
        let function_ref = NodeRef::new(parsed.arena.id(), file, function);
        let root_ref = NodeRef::new(parsed.arena.id(), file, source);
        let mut binder = CanonicalBinder::new();

        assert_eq!(
            binder.bind_source_file(&parsed.arena, source, file),
            Err(CanonicalBindError::MismatchedNodeKind {
                node: function_ref,
                kind: SyntaxKind::Block,
                data: "FunctionDeclaration",
            })
        );
        assert_eq!(binder.symbol_store().symbol_len(), 0);
        assert_eq!(binder.symbol_store().symbol_table_len(), 0);
        assert!(!binder.symbol_store().contains_node_ref(root_ref));
        assert!(binder.file(file).is_none());
    }

    #[test]
    fn malformed_child_graph_is_rejected_before_store_mutation() {
        let mut parsed = parse_source_file("const value = 1;");
        let source = parsed.source_file;
        match &mut parsed.arena.get_mut(source).unwrap().data {
            NodeData::SourceFile(data) => data.statements.nodes.push(source),
            _ => unreachable!(),
        }
        let mut binder = CanonicalBinder::new();
        let root = NodeRef::new(parsed.arena.id(), FileId::new(15), source);

        assert_eq!(
            binder.bind_source_file(&parsed.arena, source, FileId::new(15)),
            Err(CanonicalBindError::RepeatedNode(root))
        );
        assert_eq!(binder.symbol_store().symbol_table_len(), 0);
        assert!(!binder.symbol_store().contains_node_ref(root));
        assert!(binder.file(FileId::new(15)).is_none());
    }
}
