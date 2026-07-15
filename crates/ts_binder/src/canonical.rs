//! Program-owned canonical binder traversal and AST side data.
//!
//! TypeScript-Go writes binder results directly onto mutable AST nodes. Rust
//! keeps the parse tree immutable, so [`BoundFile`] is the provenance-bearing
//! equivalent of those node slots. This slice freezes the traversal, container,
//! locals, and flow contracts and exposes the dependency-closed declaration
//! primitive used by the pinned binder. Full declaration dispatch is still a
//! later phase; callers can observe that boundary through [`BindingPhase`].

use std::collections::{BTreeMap, BTreeSet, HashMap};

use ts_ast::{
    FileId, FlowRef, ModifierList, NodeArena, NodeArenaId, NodeData, NodeId, NodeRef, SyntaxKind,
};
use ts_diagnostics::{Diagnostic, message_by_code};

use crate::{
    AstScope, BoundFlowGraph, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolData,
    SymbolFlags, SymbolStore, SymbolTableId,
    flow_builder::{FlowTraversalHooks, build_flow_graph_with_hooks},
};

/// The last completed phase of the canonical binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BindingPhase {
    /// Exact declaration-order traversal and side-data allocation are complete.
    /// Symbol declaration and merge behavior has not run yet.
    Traversal,
    /// Declaration symbols and merge diagnostics are complete.
    ///
    /// No B01a entry point produces this phase. It is reserved as the explicit
    /// handoff to the B02 declaration slice.
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
    /// JavaScript declaration dispatch remains outside the B02b closure.
    JavaScriptDeclarationsDeferred(FileId),
    /// `CommonJS` declaration dispatch remains outside the B02b closure.
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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalSourceLanguage {
    TypeScript,
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
    module_state: CanonicalModuleState,
}

impl CanonicalSourceFileFacts {
    #[must_use]
    pub const fn new(
        source_file_symbol_name: EscapedName,
        language: CanonicalSourceLanguage,
        is_declaration_file: bool,
        module_state: CanonicalModuleState,
    ) -> Self {
        Self {
            source_file_symbol_name,
            language,
            is_declaration_file,
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
    source_file: NodeId,
    source_facts: Option<CanonicalSourceFileFacts>,
    node_count: usize,
    phase: BindingPhase,
    declaration_slice_bound: bool,
    nodes: Vec<NodeBinding>,
    traversal_order: Vec<NodeId>,
    container_chain: Vec<NodeId>,
    diagnostics: Vec<CanonicalBindDiagnostic>,
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

    #[must_use]
    pub const fn phase(&self) -> BindingPhase {
        self.phase
    }

    #[must_use]
    pub fn declarations_complete(&self) -> bool {
        self.phase == BindingPhase::Declarations
    }

    /// Whether the currently ported non-JavaScript declaration slice ran.
    /// This remains distinct from [`Self::declarations_complete`] until every
    /// parser-reachable family in the claimed source kinds is audited exact.
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
/// traversed (and, once B02 lands, declaration-bound).
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
    is_assignment: bool,
    is_effective_module: bool,
}

struct PreparedDeclaration {
    name: EscapedName,
    facts: DeclarationFacts,
    is_default_export: bool,
    is_export_assignment_default: bool,
    export_type_suggestion: Option<CanonicalRelatedInformation>,
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
    pub fn declare_symbol_ex(
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
        let node_ref = self.preflight_declaration(arena, file, symbol_table, parent, node)?;
        let prepared = self.prepare_declaration(arena, node_ref, parent, is_computed_name)?;
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

    /// Runs the dependency-closed non-JavaScript declaration-dispatch slice
    /// over B01's captured visitation order and container state.
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
        if bound.declaration_slice_bound {
            return Err(CanonicalDeclarationError::DuplicateDeclarationDispatch(
                file,
            ));
        }
        let Some(facts) = bound.source_facts.clone() else {
            return Err(CanonicalDeclarationError::MissingSourceFileFacts(file));
        };
        if facts.is_javascript_file() {
            return Err(CanonicalDeclarationError::JavaScriptDeclarationsDeferred(
                file,
            ));
        }
        if facts.is_common_js_module() {
            return Err(CanonicalDeclarationError::CommonJsDeclarationsDeferred(
                file,
            ));
        }
        let order = bound.traversal_order.clone();
        if let Some(node) = order.iter().copied().find(|node| {
            !declaration_family_supported(arena, *node)
                || declaration_name_shape_unsupported(arena, *node)
        }) {
            return Err(CanonicalDeclarationError::UnsupportedDeclarationFamily(
                NodeRef::new(arena.id(), file, node),
            ));
        }
        for node in order {
            self.bind_declaration_node(arena, file, node, &facts)?;
        }
        self.files
            .get_mut(&file)
            .expect("declaration-dispatch file remains registered")
            .declaration_slice_bound = true;
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
        if facts.is_external_module() {
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
        let has_export_modifier = has_combined_modifier(arena, node, SyntaxKind::ExportKeyword);
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
            SyntaxKind::SourceFile if facts.is_external_module() => {
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
    ) -> Result<(), CanonicalDeclarationError> {
        let kind = arena
            .get(node)
            .expect("declaration dispatch uses captured reachable nodes")
            .kind;
        match kind {
            SyntaxKind::SourceFile if facts.is_external_module() => {
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
                    SymbolFlags::GET_ACCESSOR | optional_symbol_flag(arena, node),
                    SymbolFlags::GET_ACCESSOR_EXCLUDES,
                    facts,
                )?;
            }
            SyntaxKind::SetAccessor => {
                self.bind_property_or_method_or_accessor(
                    arena,
                    file,
                    node,
                    SymbolFlags::SET_ACCESSOR | optional_symbol_flag(arena, node),
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
            SyntaxKind::TypeAliasDeclaration => {
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
            _ => {}
        }
        Ok(())
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
            is_assignment: is_assignment_declaration(declaration.kind),
            is_effective_module: matches!(
                declaration.kind,
                SyntaxKind::ModuleDeclaration | SyntaxKind::Identifier
            ),
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
            let parent = self
                .bound_node_symbol(file, container)
                .expect("anonymous member container is already declared");
            assert!(
                self.symbols
                    .set_symbol_relationships(symbol, None, None, Some(parent), None)
            );
        }
        self.add_declaration_to_symbol(symbol, node_ref, includes, declaration_facts);
        symbol
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
        if is_block_or_catch_scoped(arena, node) {
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
    ) -> Result<PreparedDeclaration, CanonicalDeclarationError> {
        if !is_computed_name && assignment_name_requires_javascript_file_kind(arena, node.node) {
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
                is_assignment: is_assignment_declaration(declaration.kind),
                is_effective_module: matches!(
                    declaration.kind,
                    SyntaxKind::ModuleDeclaration | SyntaxKind::Identifier
                ),
            },
            is_default_export,
            is_export_assignment_default: matches!(
                &declaration.data,
                NodeData::ExportAssignment(assignment) if !assignment.is_export_equals
            ),
            export_type_suggestion,
        })
    }

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
                current_facts.is_assignment && !facts.is_assignment
                    || current_facts.kind != facts.kind && current_facts.is_effective_module
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
    /// This B02b entry point still completes only the traversal phase until
    /// the dependency-closed non-JavaScript declaration switch is installed.
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

fn declaration_family_supported(arena: &NodeArena, node: NodeId) -> bool {
    !arena.get(node).is_some_and(|node| {
        matches!(
            node.kind,
            SyntaxKind::ModuleDeclaration
                | SyntaxKind::ImportEqualsDeclaration
                | SyntaxKind::NamespaceImport
                | SyntaxKind::ImportSpecifier
                | SyntaxKind::ExportSpecifier
                | SyntaxKind::NamespaceExportDeclaration
                | SyntaxKind::NamespaceExport
                | SyntaxKind::ImportClause
                | SyntaxKind::ExportDeclaration
                | SyntaxKind::ExportAssignment
                | SyntaxKind::JsTypeAliasDeclaration
        )
    })
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
    );
    if has_dynamic_name(arena, node) && !dynamic_is_handled {
        return true;
    }
    get_name_of_declaration(arena, node)
        .and_then(|name| arena.get(name))
        .is_some_and(|name| name.kind == SyntaxKind::PrivateIdentifier)
        && containing_class(arena, node).is_none()
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

fn is_ambient_node(arena: &NodeArena, mut node: NodeId, facts: &CanonicalSourceFileFacts) -> bool {
    if facts.is_declaration_file() {
        return true;
    }
    loop {
        if has_syntactic_modifier(arena, node, SyntaxKind::DeclareKeyword)
            || is_ambient_module(arena, node)
        {
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

fn is_assignment_declaration(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::BinaryExpression
            | SyntaxKind::PropertyAccessExpression
            | SyntaxKind::ElementAccessExpression
            | SyntaxKind::Identifier
            | SyntaxKind::CallExpression
    )
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
                    if is_entity_name_expression(arena, access.expression)
                        && arena
                            .get(access.name)
                            .is_some_and(|name| name.kind == SyntaxKind::Identifier) =>
                {
                    Some(access.name)
                }
                NodeData::ElementAccessExpression(access)
                    if is_entity_name_expression(arena, access.expression) =>
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
        _ => None,
    }
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
    state_stack: Vec<(NodeId, TraversalState)>,
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
            state_stack: Vec::new(),
        }
    }

    fn finish(self, flow: BoundFlowGraph) -> BoundFile {
        assert!(
            self.state_stack.is_empty(),
            "canonical traversal exits every entered node"
        );
        BoundFile {
            file: self.file,
            arena: self.arena.id(),
            source_file: self.source_file,
            source_facts: self.source_facts,
            node_count: self.arena.len(),
            phase: BindingPhase::Traversal,
            declaration_slice_bound: false,
            nodes: self.nodes,
            traversal_order: self.traversal_order,
            container_chain: self.container_chain,
            diagnostics: Vec::new(),
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

        let flags = container_flags(self.arena, node_id);
        self.state_stack.push((node_id, self.state));
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
    }

    fn exit(&mut self, node_id: NodeId) {
        let (entered, saved) = self
            .state_stack
            .pop()
            .expect("every canonical exit has a matching enter");
        assert_eq!(entered, node_id, "canonical traversal exits in stack order");
        self.state = saved;
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

    use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
    use ts_parser::parse_source_file;

    use super::{
        BindingPhase, CanonicalBindError, CanonicalBinder, CanonicalDeclarationError,
        CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
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

        let computed = binder
            .declare_symbol_ex(
                &parsed.arena,
                file,
                table,
                None,
                module_assignment,
                SymbolFlags::ASSIGNMENT,
                SymbolFlags::NONE,
                false,
                true,
            )
            .unwrap();
        let bound = binder.file(file).unwrap();
        assert_eq!(bound.symbol_count(), 1);
        assert_eq!(bound.classifiable_names().count(), 0);
        assert!(bound.diagnostics().is_empty());
        assert_eq!(
            binder
                .symbol_store()
                .symbol_table(table)
                .unwrap()
                .get(InternalSymbolName::Computed.as_ref()),
            Some(computed)
        );
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
        // The current parser aliases ExportAssignment.expression into its
        // generated `type_` slot. Canonical traversal correctly rejects that
        // DAG, so give this focused binder probe distinct but equivalent leaf
        // nodes until the parser schema slice fixes the alias.
        for assignment in nodes_of_kind(&parsed.arena, SyntaxKind::ExportAssignment) {
            let expression = match &parsed.arena.get(assignment).unwrap().data {
                NodeData::ExportAssignment(data) => data.expression,
                _ => unreachable!(),
            };
            let mut duplicate = parsed.arena.get(expression).unwrap().clone();
            duplicate.parent = Some(assignment);
            let duplicate = parsed.arena.alloc(duplicate);
            match &mut parsed.arena.get_mut(assignment).unwrap().data {
                NodeData::ExportAssignment(data) => data.type_ = duplicate,
                _ => unreachable!(),
            }
        }
        for property in nodes_of_kind(&parsed.arena, SyntaxKind::PropertyAssignment) {
            let name = match &parsed.arena.get(property).unwrap().data {
                NodeData::PropertyAssignment(data) => data.name,
                _ => unreachable!(),
            };
            let mut duplicate = parsed.arena.get(name).unwrap().clone();
            duplicate.parent = Some(property);
            let duplicate = parsed.arena.alloc(duplicate);
            match &mut parsed.arena.get_mut(property).unwrap().data {
                NodeData::PropertyAssignment(data) => data.type_ = duplicate,
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
        let facts = CanonicalSourceFileFacts::new(
            EscapedName::source("\"/project/main\""),
            CanonicalSourceLanguage::TypeScript,
            true,
            CanonicalModuleState::External,
        );
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts.clone())
            .unwrap();
        let bound = binder.file(file).unwrap();
        assert_eq!(bound.source_facts(), Some(&facts));
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
    }

    #[test]
    fn declaration_slice_preflight_rejects_atomically_and_retry_is_stable() {
        let parsed = parse_source_file("namespace Deferred { export const value = 1; }");
        let file = FileId::new(43);
        let facts = CanonicalSourceFileFacts::new(
            EscapedName::source("\"/project/deferred\""),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::Script,
        );
        let module = nodes_of_kind(&parsed.arena, SyntaxKind::ModuleDeclaration)[0];
        let expected = Err(CanonicalDeclarationError::UnsupportedDeclarationFamily(
            node_ref(&parsed.arena, file, module),
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
        assert_eq!(bound.phase(), BindingPhase::Traversal);
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
