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
    flow_builder::build_flow_graph,
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
    /// checker. Both retain the same unforgeable semantic-store brand.
    #[must_use]
    pub fn into_parts(self) -> (SymbolStore, BTreeMap<FileId, BoundFile>) {
        (self.symbols, self.files)
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
    /// The exact generated child visitor drives declaration order. The existing
    /// `flow_builder` then performs a temporary second pass over the same child
    /// graph; it remains the only CFG implementation. Interleaving flow with
    /// declaration binding later does not change [`BoundFile`]'s contract.
    ///
    /// # Errors
    ///
    /// Returns [`CanonicalBindError`] when the root or its generated child
    /// graph is invalid, the Program file slot is already occupied, or the AST
    /// arena conflicts with an existing Program scope.
    ///
    /// # Panics
    ///
    /// Panics if a canonical symbol-table identity cannot be represented, or
    /// if the inserted file disappears from the private file map. The latter
    /// indicates an internal invariant violation.
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
            arena.get(source_file).map(|node| &node.data),
            Some(NodeData::SourceFile(_))
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

        let file_binding =
            FileTraversal::new(arena, source_file, file, &children, &mut self.symbols).bind()?;
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
    let mut pending = vec![source_file];
    while let Some(node) = pending.pop() {
        if std::mem::replace(&mut seen[node.index()], true) {
            return Err(CanonicalBindError::RepeatedNode(NodeRef::new(
                arena.id(),
                file,
                node,
            )));
        }
        pending.extend(
            children
                .get(&node)
                .expect("every arena node has a generated child entry")
                .iter()
                .rev()
                .copied(),
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
    children: &'a HashMap<NodeId, Vec<NodeId>>,
    symbols: &'a mut SymbolStore,
    nodes: Vec<NodeBinding>,
    traversal_order: Vec<NodeId>,
    container_chain: Vec<NodeId>,
    last_container: Option<NodeId>,
    state: TraversalState,
}

impl<'a> FileTraversal<'a> {
    fn new(
        arena: &'a NodeArena,
        source_file: NodeId,
        file: FileId,
        children: &'a HashMap<NodeId, Vec<NodeId>>,
        symbols: &'a mut SymbolStore,
    ) -> Self {
        Self {
            arena,
            source_file,
            file,
            children,
            symbols,
            nodes: vec![NodeBinding::default(); arena.len()],
            traversal_order: Vec::with_capacity(arena.len()),
            container_chain: Vec::new(),
            last_container: None,
            state: TraversalState::default(),
        }
    }

    fn bind(mut self) -> Result<BoundFile, CanonicalBindError> {
        self.bind_node(self.source_file)?;

        // This is the existing, shared flow implementation, not a parallel CFG
        // model. B01a keeps it as an explicit second pass until declarations and
        // flow can be interleaved without changing observable side data.
        let flow = build_flow_graph(self.arena, self.children, self.source_file, self.file);
        Ok(BoundFile {
            file: self.file,
            arena: self.arena.id(),
            source_file: self.source_file,
            node_count: self.arena.len(),
            phase: BindingPhase::Traversal,
            nodes: self.nodes,
            traversal_order: self.traversal_order,
            container_chain: self.container_chain,
            flow,
        })
    }

    fn bind_node(&mut self, node_id: NodeId) -> Result<(), CanonicalBindError> {
        let node_ref = NodeRef::new(self.arena.id(), self.file, node_id);
        let binding = &mut self.nodes[node_id.index()];
        if binding.visited {
            return Err(CanonicalBindError::RepeatedNode(node_ref));
        }

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
        let saved = self.state;
        if flags.contains(ContainerFlags::IS_CONTAINER) {
            self.state.container = Some(node_id);
            self.state.block_scope_container = Some(node_id);
            if flags.contains(ContainerFlags::HAS_LOCALS) {
                self.nodes[node_id.index()].locals = Some(self.symbols.alloc_symbol_table());
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

        self.bind_children(node_id)?;
        self.state = saved;
        Ok(())
    }

    fn bind_children(&mut self, node_id: NodeId) -> Result<(), CanonicalBindError> {
        match self
            .arena
            .get(node_id)
            .expect("all generated child references were validated")
            .data
            .clone()
        {
            NodeData::SourceFile(data) => {
                self.bind_statements_functions_first(&data.statements.nodes)?;
                self.bind_node(data.end_of_file_token)
            }
            NodeData::Block(data) => self.bind_statements_functions_first(&data.statements.nodes),
            NodeData::ModuleBlock(data) => {
                self.bind_statements_functions_first(&data.statements.nodes)
            }
            _ => {
                let children = self
                    .children
                    .get(&node_id)
                    .expect("every arena node has a generated child entry")
                    .clone();
                for child in children {
                    self.bind_node(child)?;
                }
                Ok(())
            }
        }
    }

    fn bind_statements_functions_first(
        &mut self,
        statements: &[NodeId],
    ) -> Result<(), CanonicalBindError> {
        for statement in statements.iter().copied().filter(|statement| {
            self.arena
                .get(*statement)
                .is_some_and(|node| node.kind == SyntaxKind::FunctionDeclaration)
        }) {
            self.bind_node(statement)?;
        }
        for statement in statements.iter().copied().filter(|statement| {
            self.arena
                .get(*statement)
                .is_some_and(|node| node.kind != SyntaxKind::FunctionDeclaration)
        }) {
            self.bind_node(statement)?;
        }
        Ok(())
    }

    fn add_to_container_chain(&mut self, node: NodeId) {
        if let Some(previous) = self.last_container {
            self.nodes[previous.index()].next_container = Some(node);
        }
        self.last_container = Some(node);
        self.container_chain.push(node);
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

        let source_locals = bound.locals(source_ref).unwrap();
        let function_locals = bound.locals(function_ref).unwrap();
        assert_ne!(source_locals, function_locals);
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

        assert!(
            binder
                .symbol_store()
                .symbol_table(source_locals)
                .unwrap()
                .is_empty()
        );
        assert!(
            binder
                .symbol_store()
                .symbol_table(function_locals)
                .unwrap()
                .is_empty()
        );
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
        assert!(
            files
                .symbol_store()
                .contains_symbol_table(first_bound.locals(first_root).unwrap())
        );
        assert!(
            files
                .symbol_store()
                .contains_symbol_table(second_bound.locals(second_root).unwrap())
        );

        let wrong_file = NodeRef::new(first.arena.id(), FileId::new(7), first.source_file);
        let wrong_arena = NodeRef::new(second.arena.id(), FileId::new(3), first.source_file);
        assert!(!first_bound.contains(wrong_file));
        assert!(!first_bound.contains(wrong_arena));

        let (symbols, bound_files) = files.into_parts();
        assert_eq!(bound_files.len(), 2);
        assert!(symbols.contains_node_ref(first_root));
        assert!(symbols.contains_node_ref(second_root));
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
    fn malformed_child_graph_is_rejected_before_store_mutation() {
        let mut parsed = parse_source_file("const value = 1;");
        let source = parsed.source_file;
        match &mut parsed.arena.get_mut(source).unwrap().data {
            NodeData::SourceFile(data) => data.statements.nodes.push(source),
            _ => unreachable!(),
        }
        let mut binder = CanonicalBinder::new();
        let root = NodeRef::new(parsed.arena.id(), FileId::new(12), source);

        assert_eq!(
            binder.bind_source_file(&parsed.arena, source, FileId::new(12)),
            Err(CanonicalBindError::RepeatedNode(root))
        );
        assert_eq!(binder.symbol_store().symbol_table_len(), 0);
        assert!(!binder.symbol_store().contains_node_ref(root));
        assert!(binder.file(FileId::new(12)).is_none());
    }
}
