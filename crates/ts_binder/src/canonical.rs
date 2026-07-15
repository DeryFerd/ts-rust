//! Program-owned canonical binder traversal and AST side data.
//!
//! TypeScript-Go writes binder results directly onto mutable AST nodes. Rust
//! keeps the parse tree immutable, so [`BoundFile`] is the provenance-bearing
//! equivalent of those node slots. This slice freezes the traversal, container,
//! locals, and flow contracts. Declaration creation and merge diagnostics are
//! deliberately the next phase; callers can observe that boundary through
//! [`BindingPhase`] rather than mistaking an empty symbol slot for a completed
//! declaration pass.

use std::collections::{BTreeMap, HashMap};

use ts_ast::{FileId, FlowRef, NodeArena, NodeArenaId, NodeData, NodeId, NodeRef, SyntaxKind};

use crate::{
    AstScope, BoundFlowGraph, SemanticSymbolId, SymbolStore, SymbolTableId,
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
    node_count: usize,
    phase: BindingPhase,
    nodes: Vec<NodeBinding>,
    traversal_order: Vec<NodeId>,
    container_chain: Vec<NodeId>,
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

    #[must_use]
    pub const fn source_file(&self) -> NodeRef {
        NodeRef::new(self.arena, self.file, self.source_file)
    }

    /// Whether `node` was reached from this exact source-file root.
    #[must_use]
    pub fn contains(&self, node: NodeRef) -> bool {
        self.node_binding(node)
            .is_some_and(|binding| binding.visited)
    }

    /// Canonical declaration symbol written by the declaration phase.
    ///
    /// This is always `None` while [`Self::phase`] is
    /// [`BindingPhase::Traversal`].
    #[must_use]
    pub fn symbol(&self, node: NodeRef) -> Option<SemanticSymbolId> {
        self.node_binding(node)?.symbol
    }

    /// Canonical local half of an exported declaration pair.
    #[must_use]
    pub fn local_symbol(&self, node: NodeRef) -> Option<SemanticSymbolId> {
        self.node_binding(node)?.local_symbol
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
/// There is intentionally no mutable `SymbolStore` escape hatch. B02 will add
/// declaration operations on this owner, then [`Self::finish`] transfers the
/// fully bound store to checker construction.
#[derive(Debug, Default)]
pub struct CanonicalBinder {
    symbols: SymbolStore,
    files: BTreeMap<FileId, BoundFile>,
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

        let mut traversal = FileTraversal::new(arena, source_file, file);
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
    file: FileId,
    nodes: Vec<NodeBinding>,
    traversal_order: Vec<NodeId>,
    container_chain: Vec<NodeId>,
    last_container: Option<NodeId>,
    state: TraversalState,
    state_stack: Vec<(NodeId, TraversalState)>,
}

impl<'a> FileTraversal<'a> {
    fn new(arena: &'a NodeArena, source_file: NodeId, file: FileId) -> Self {
        Self {
            arena,
            source_file,
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
            node_count: self.arena.len(),
            phase: BindingPhase::Traversal,
            nodes: self.nodes,
            traversal_order: self.traversal_order,
            container_chain: self.container_chain,
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
    use std::collections::BTreeSet;

    use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
    use ts_parser::parse_source_file;

    use super::{BindingPhase, CanonicalBindError, CanonicalBinder};

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
