//! Declaration binding and lexical symbol tables.

mod canonical;
mod escaped_name;
mod flow_builder;
mod name_resolver;
pub mod semantic;

pub use canonical::{
    BindingPhase, BoundFile, CanonicalBindDiagnostic, CanonicalBindError, CanonicalBinder,
    CanonicalDeclarationError, CanonicalExtractionError, CanonicalModuleState,
    CanonicalPatternAmbientModule, CanonicalProgramBindings, CanonicalRelatedInformation,
    CanonicalSourceFileFacts, CanonicalSourceLanguage,
};
pub use escaped_name::{
    EscapedDisplay, EscapedName, EscapedNameRef, INTERNAL_SYMBOL_NAME_PREFIX, InternalSymbolName,
};
pub use name_resolver::{
    CanonicalNameResolutionError, CanonicalNameResolver, CanonicalNameResolverHost,
    CanonicalNameResolverOptions, CanonicalResolutionLocation, CanonicalResolvedName,
    CanonicalScopeChangeState, CanonicalSyntheticScope, CanonicalSyntheticScopeId,
    CanonicalSyntheticScopeStore, CanonicalSyntheticScopeStoreError, resolve_global_name,
};
pub use semantic::{
    AstScope, CheckFlags, SemanticStoreId, SemanticSymbolId, SymbolData, SymbolStore, SymbolTableId,
};

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    ops::{BitAnd, BitOr, BitOrAssign},
};

use ts_ast::{
    FileId, FlowNodeArena, FlowRef, NodeArena, NodeArenaId, NodeData, NodeFlags, NodeId, NodeRef,
    SymbolId, SyntaxKind,
};
use ts_diagnostics::{Diagnostic, message_by_code};

use flow_builder::build_flow_graph;

/// TypeScript symbol meanings and merge masks.
///
/// Bit positions match `microsoft/typescript-go`'s `internal/ast/symbolflags.go`
/// at `dc37b5249ab60e2bbce936f71b883e6c8136167e`.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct SymbolFlags(u32);

impl SymbolFlags {
    pub const NONE: Self = Self(0);
    pub const FUNCTION_SCOPED_VARIABLE: Self = Self(1 << 0);
    pub const BLOCK_SCOPED_VARIABLE: Self = Self(1 << 1);
    pub const PROPERTY: Self = Self(1 << 2);
    pub const ENUM_MEMBER: Self = Self(1 << 3);
    pub const FUNCTION: Self = Self(1 << 4);
    pub const CLASS: Self = Self(1 << 5);
    pub const INTERFACE: Self = Self(1 << 6);
    pub const CONST_ENUM: Self = Self(1 << 7);
    pub const REGULAR_ENUM: Self = Self(1 << 8);
    pub const VALUE_MODULE: Self = Self(1 << 9);
    pub const NAMESPACE_MODULE: Self = Self(1 << 10);
    pub const TYPE_LITERAL: Self = Self(1 << 11);
    pub const OBJECT_LITERAL: Self = Self(1 << 12);
    pub const METHOD: Self = Self(1 << 13);
    pub const CONSTRUCTOR: Self = Self(1 << 14);
    pub const GET_ACCESSOR: Self = Self(1 << 15);
    pub const SET_ACCESSOR: Self = Self(1 << 16);
    pub const SIGNATURE: Self = Self(1 << 17);
    pub const TYPE_PARAMETER: Self = Self(1 << 18);
    pub const TYPE_ALIAS: Self = Self(1 << 19);
    pub const EXPORT_VALUE: Self = Self(1 << 20);
    pub const ALIAS: Self = Self(1 << 21);
    pub const PROTOTYPE: Self = Self(1 << 22);
    pub const EXPORT_STAR: Self = Self(1 << 23);
    pub const OPTIONAL: Self = Self(1 << 24);
    pub const TRANSIENT: Self = Self(1 << 25);
    pub const ASSIGNMENT: Self = Self(1 << 26);
    pub const MODULE_EXPORTS: Self = Self(1 << 27);
    pub const CONST_ENUM_ONLY_MODULE: Self = Self(1 << 28);
    pub const REPLACEABLE_BY_METHOD: Self = Self(1 << 29);
    pub const GLOBAL_LOOKUP: Self = Self(1 << 30);
    pub const ALL: Self = Self((1 << 30) - 1);

    pub const ENUM: Self = Self(Self::CONST_ENUM.0 | Self::REGULAR_ENUM.0);
    pub const VARIABLE: Self =
        Self(Self::FUNCTION_SCOPED_VARIABLE.0 | Self::BLOCK_SCOPED_VARIABLE.0);
    pub const VALUE: Self = Self(
        Self::VARIABLE.0
            | Self::PROPERTY.0
            | Self::ENUM_MEMBER.0
            | Self::OBJECT_LITERAL.0
            | Self::FUNCTION.0
            | Self::CLASS.0
            | Self::ENUM.0
            | Self::VALUE_MODULE.0
            | Self::METHOD.0
            | Self::GET_ACCESSOR.0
            | Self::SET_ACCESSOR.0,
    );
    pub const TYPE: Self = Self(
        Self::CLASS.0
            | Self::INTERFACE.0
            | Self::ENUM.0
            | Self::ENUM_MEMBER.0
            | Self::TYPE_LITERAL.0
            | Self::TYPE_PARAMETER.0
            | Self::TYPE_ALIAS.0,
    );
    pub const NAMESPACE: Self =
        Self(Self::VALUE_MODULE.0 | Self::NAMESPACE_MODULE.0 | Self::ENUM.0);
    pub const MODULE: Self = Self(Self::VALUE_MODULE.0 | Self::NAMESPACE_MODULE.0);
    pub const ACCESSOR: Self = Self(Self::GET_ACCESSOR.0 | Self::SET_ACCESSOR.0);

    pub const FUNCTION_SCOPED_VARIABLE_EXCLUDES: Self =
        Self(Self::VALUE.0 & !Self::FUNCTION_SCOPED_VARIABLE.0);
    pub const BLOCK_SCOPED_VARIABLE_EXCLUDES: Self = Self::VALUE;
    pub const PARAMETER_EXCLUDES: Self = Self::VALUE;
    pub const PROPERTY_EXCLUDES: Self =
        Self(Self::VALUE.0 & !(Self::PROPERTY.0 | Self::ACCESSOR.0));
    pub const ENUM_MEMBER_EXCLUDES: Self = Self(Self::VALUE.0 | Self::TYPE.0);
    pub const FUNCTION_EXCLUDES: Self =
        Self(Self::VALUE.0 & !(Self::FUNCTION.0 | Self::VALUE_MODULE.0 | Self::CLASS.0));
    pub const CLASS_EXCLUDES: Self = Self(
        (Self::VALUE.0 | Self::TYPE.0)
            & !(Self::VALUE_MODULE.0 | Self::INTERFACE.0 | Self::FUNCTION.0),
    );
    pub const INTERFACE_EXCLUDES: Self = Self(Self::TYPE.0 & !(Self::INTERFACE.0 | Self::CLASS.0));
    pub const REGULAR_ENUM_EXCLUDES: Self =
        Self((Self::VALUE.0 | Self::TYPE.0) & !(Self::REGULAR_ENUM.0 | Self::VALUE_MODULE.0));
    pub const CONST_ENUM_EXCLUDES: Self =
        Self((Self::VALUE.0 | Self::TYPE.0) & !Self::CONST_ENUM.0);
    pub const VALUE_MODULE_EXCLUDES: Self = Self(
        Self::VALUE.0
            & !(Self::FUNCTION.0 | Self::CLASS.0 | Self::REGULAR_ENUM.0 | Self::VALUE_MODULE.0),
    );
    pub const NAMESPACE_MODULE_EXCLUDES: Self = Self::NONE;
    pub const METHOD_EXCLUDES: Self = Self(Self::VALUE.0 & !Self::METHOD.0);
    pub const GET_ACCESSOR_EXCLUDES: Self =
        Self(Self::VALUE.0 & !(Self::SET_ACCESSOR.0 | Self::PROPERTY.0));
    pub const SET_ACCESSOR_EXCLUDES: Self =
        Self(Self::VALUE.0 & !(Self::GET_ACCESSOR.0 | Self::PROPERTY.0));
    pub const ACCESSOR_EXCLUDES: Self = Self(Self::VALUE.0 & !Self::PROPERTY.0);
    pub const TYPE_PARAMETER_EXCLUDES: Self = Self(Self::TYPE.0 & !Self::TYPE_PARAMETER.0);
    pub const TYPE_ALIAS_EXCLUDES: Self = Self::TYPE;
    pub const ALIAS_EXCLUDES: Self = Self::ALIAS;
    pub const MODULE_MEMBER: Self = Self(
        Self::VARIABLE.0
            | Self::FUNCTION.0
            | Self::CLASS.0
            | Self::INTERFACE.0
            | Self::ENUM.0
            | Self::MODULE.0
            | Self::TYPE_ALIAS.0
            | Self::ALIAS.0,
    );
    pub const EXPORT_HAS_LOCAL: Self =
        Self(Self::FUNCTION.0 | Self::CLASS.0 | Self::ENUM.0 | Self::VALUE_MODULE.0);
    pub const BLOCK_SCOPED: Self =
        Self(Self::BLOCK_SCOPED_VARIABLE.0 | Self::CLASS.0 | Self::ENUM.0);
    pub const PROPERTY_OR_ACCESSOR: Self = Self(Self::PROPERTY.0 | Self::ACCESSOR.0);
    pub const CLASS_MEMBER: Self = Self(Self::METHOD.0 | Self::ACCESSOR.0 | Self::PROPERTY.0);
    pub const EXPORT_SUPPORTS_DEFAULT_MODIFIER: Self =
        Self(Self::CLASS.0 | Self::FUNCTION.0 | Self::INTERFACE.0);
    pub const EXPORT_DOES_NOT_SUPPORT_DEFAULT_MODIFIER: Self =
        Self(!Self::EXPORT_SUPPORTS_DEFAULT_MODIFIER.0);
    pub const CLASSIFIABLE: Self = Self(
        Self::CLASS.0
            | Self::ENUM.0
            | Self::TYPE_ALIAS.0
            | Self::INTERFACE.0
            | Self::TYPE_PARAMETER.0
            | Self::MODULE.0
            | Self::ALIAS.0,
    );
    pub const LATE_BINDING_CONTAINER: Self = Self(
        Self::CLASS.0
            | Self::INTERFACE.0
            | Self::TYPE_LITERAL.0
            | Self::OBJECT_LITERAL.0
            | Self::FUNCTION.0,
    );

    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[must_use]
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    /// Returns these flags with every bit in `other` cleared.
    #[must_use]
    pub const fn without(self, other: Self) -> Self {
        Self(self.0 & !other.0)
    }
}

impl BitOr for SymbolFlags {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for SymbolFlags {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl BitAnd for SymbolFlags {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

/// One bound declaration symbol.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Symbol {
    pub id: SymbolId,
    pub name: String,
    pub flags: SymbolFlags,
    pub declarations: Vec<NodeId>,
    pub value_declaration: Option<NodeId>,
    pub parent: Option<SymbolId>,
    pub members: SymbolTable,
    pub target: Option<SymbolId>,
}

/// Stable storage for symbols allocated in binding order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SymbolArena {
    symbols: Vec<Symbol>,
}

impl SymbolArena {
    #[must_use]
    pub fn get(&self, id: SymbolId) -> Option<&Symbol> {
        self.symbols.get(id.0 as usize)
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }

    #[must_use]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &Symbol> {
        self.symbols.iter()
    }

    fn get_mut(&mut self, id: SymbolId) -> Option<&mut Symbol> {
        self.symbols.get_mut(id.0 as usize)
    }

    fn alloc(
        &mut self,
        name: String,
        flags: SymbolFlags,
        declaration: NodeId,
        parent: Option<SymbolId>,
    ) -> SymbolId {
        let id = SymbolId(
            u32::try_from(self.symbols.len()).expect("symbol arena exceeds u32::MAX symbols"),
        );
        self.symbols.push(Symbol {
            id,
            name,
            flags,
            declarations: vec![declaration],
            value_declaration: is_value(flags).then_some(declaration),
            parent,
            members: SymbolTable::default(),
            target: None,
        });
        id
    }
}

/// Deterministic mapping from escaped declaration names to symbols.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SymbolTable(BTreeMap<String, SymbolId>);

impl SymbolTable {
    #[must_use]
    pub fn get(&self, name: &str) -> Option<SymbolId> {
        self.0.get(name).copied()
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[must_use]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (&str, SymbolId)> {
        self.0.iter().map(|(name, id)| (name.as_str(), *id))
    }

    fn insert(&mut self, name: String, id: SymbolId) {
        self.0.insert(name, id);
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ScopeId(u32);

impl ScopeId {
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScopeKind {
    SourceFile,
    Block,
    Function,
    Class,
    Interface,
    Enum,
    Module,
    TypeAlias,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Scope {
    pub id: ScopeId,
    pub kind: ScopeKind,
    pub owner: NodeId,
    pub parent: Option<ScopeId>,
    pub symbols: SymbolTable,
}

/// A declaration diagnostic associated with its AST node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindDiagnostic {
    pub node: NodeId,
    pub diagnostic: Diagnostic,
}

/// A control-flow family that this binder slice deliberately does not model.
///
/// Recording these boundaries keeps partial graphs inspectable without letting
/// downstream semantic work mistake them for complete TypeScript control flow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnsupportedFlowKind {
    TryStatement,
    WithStatement,
    LogicalExpression,
    OptionalChain,
    DestructuringAssignment,
    ImmediatelyInvokedFunction,
    DirectFunctionCall,
    ClassStaticBlock,
    CrossContainerFlowEffects,
}

/// One explicit incompleteness boundary in a bound control-flow container.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnsupportedFlow {
    pub node: NodeRef,
    pub container: NodeRef,
    pub kind: UnsupportedFlowKind,
}

/// Binder-created control flow for one program source file.
///
/// AST nodes remain immutable after parsing. The maps here are the returned,
/// provenance-bearing equivalent of typescript-go's mutable `FlowNode` and
/// `EndFlowNode` AST fields.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoundFlowGraph {
    nodes: FlowNodeArena,
    node_flows: BTreeMap<NodeId, FlowRef>,
    node_containers: BTreeMap<NodeId, NodeId>,
    container_starts: BTreeMap<NodeId, FlowRef>,
    container_ends: BTreeMap<NodeId, FlowRef>,
    container_returns: BTreeMap<NodeId, FlowRef>,
    fallthrough_flows: BTreeMap<NodeId, FlowRef>,
    unreachable_nodes: BTreeSet<NodeId>,
    incomplete_containers: BTreeSet<NodeId>,
    unsupported: Vec<UnsupportedFlow>,
}

impl BoundFlowGraph {
    fn new(arena: NodeArenaId, file: FileId) -> Self {
        Self {
            nodes: FlowNodeArena::new(arena, file),
            node_flows: BTreeMap::new(),
            node_containers: BTreeMap::new(),
            container_starts: BTreeMap::new(),
            container_ends: BTreeMap::new(),
            container_returns: BTreeMap::new(),
            fallthrough_flows: BTreeMap::new(),
            unreachable_nodes: BTreeSet::new(),
            incomplete_containers: BTreeSet::new(),
            unsupported: Vec::new(),
        }
    }

    #[must_use]
    pub const fn file_id(&self) -> FileId {
        self.nodes.file()
    }

    #[must_use]
    pub const fn node_arena_id(&self) -> NodeArenaId {
        self.nodes.node_arena()
    }

    /// Raw flow-node storage for graph algorithms and parity inspection.
    #[must_use]
    pub const fn nodes(&self) -> &FlowNodeArena {
        &self.nodes
    }

    /// Returns the entry flow recorded on `node` only when its complete
    /// control-flow container and file provenance are known.
    #[must_use]
    pub fn flow_at(&self, node: NodeRef) -> Option<FlowRef> {
        if !node.is_for(self.node_arena_id(), self.file_id()) {
            return None;
        }
        let container = self.node_containers.get(&node.node)?;
        (!self.incomplete_containers.contains(container))
            .then(|| self.node_flows.get(&node.node).copied())
            .flatten()
    }

    #[must_use]
    pub fn container_start(&self, container: NodeRef) -> Option<FlowRef> {
        if !container.is_for(self.node_arena_id(), self.file_id())
            || self.incomplete_containers.contains(&container.node)
        {
            return None;
        }
        self.container_starts.get(&container.node).copied()
    }

    #[must_use]
    pub fn container_end(&self, container: NodeRef) -> Option<FlowRef> {
        if !container.is_for(self.node_arena_id(), self.file_id())
            || self.incomplete_containers.contains(&container.node)
        {
            return None;
        }
        self.container_ends.get(&container.node).copied()
    }

    #[must_use]
    pub fn container_return(&self, container: NodeRef) -> Option<FlowRef> {
        if !container.is_for(self.node_arena_id(), self.file_id())
            || self.incomplete_containers.contains(&container.node)
        {
            return None;
        }
        self.container_returns.get(&container.node).copied()
    }

    /// Flow retained on a non-final switch clause that can fall through.
    #[must_use]
    pub fn fallthrough_flow_at(&self, clause: NodeRef) -> Option<FlowRef> {
        if !clause.is_for(self.node_arena_id(), self.file_id()) {
            return None;
        }
        let container = self.node_containers.get(&clause.node)?;
        (!self.incomplete_containers.contains(container))
            .then(|| self.fallthrough_flows.get(&clause.node).copied())
            .flatten()
    }

    /// Returns `None` when `container` was never recognized as a flow
    /// container in this file.
    #[must_use]
    pub fn container_is_complete(&self, container: NodeRef) -> Option<bool> {
        if !container.is_for(self.node_arena_id(), self.file_id()) {
            return None;
        }
        (self.container_starts.contains_key(&container.node)
            || self.incomplete_containers.contains(&container.node))
        .then(|| !self.incomplete_containers.contains(&container.node))
    }

    #[must_use]
    pub fn is_unreachable(&self, node: NodeRef) -> Option<bool> {
        if !node.is_for(self.node_arena_id(), self.file_id()) {
            return None;
        }
        let container = self.node_containers.get(&node.node)?;
        (!self.incomplete_containers.contains(container))
            .then(|| self.unreachable_nodes.contains(&node.node))
    }

    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.incomplete_containers.is_empty()
    }

    #[must_use]
    pub fn unsupported(&self) -> &[UnsupportedFlow] {
        &self.unsupported
    }

    /// Returns the control-flow container associated with `node` by the flow
    /// builder, including containers later marked incomplete.
    ///
    /// This is distinct from the binder's semantic container association. A
    /// module block, for example, starts a control-flow container without
    /// becoming the semantic declaration container.
    #[must_use]
    pub fn flow_container(&self, node: NodeRef) -> Option<NodeRef> {
        if !node.is_for(self.node_arena_id(), self.file_id()) {
            return None;
        }
        self.node_containers
            .get(&node.node)
            .copied()
            .map(|container| NodeRef::new(self.node_arena_id(), self.file_id(), container))
    }
}

/// Complete binding output for one source-file arena.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindResult {
    /// Program provenance when this file was bound as part of a Program.
    /// Standalone bindings deliberately remain unassigned.
    file_id: Option<FileId>,
    arena_id: NodeArenaId,
    bound_source_file: NodeId,
    pub symbols: SymbolArena,
    pub scopes: Vec<Scope>,
    pub node_symbols: BTreeMap<NodeId, SymbolId>,
    pub node_scopes: BTreeMap<NodeId, ScopeId>,
    pub containers: BTreeMap<NodeId, NodeId>,
    pub exports: SymbolTable,
    pub diagnostics: Vec<BindDiagnostic>,
    flow: Option<BoundFlowGraph>,
}

impl BindResult {
    fn new(arena: &NodeArena, source_file: NodeId, file_id: Option<FileId>) -> Self {
        Self {
            file_id,
            arena_id: arena.id(),
            bound_source_file: source_file,
            symbols: SymbolArena::default(),
            scopes: Vec::new(),
            node_symbols: BTreeMap::new(),
            node_scopes: BTreeMap::new(),
            containers: BTreeMap::new(),
            exports: SymbolTable::default(),
            diagnostics: Vec::new(),
            flow: None,
        }
    }

    /// Program provenance, or `None` for a standalone binding.
    #[must_use]
    pub const fn file_id(&self) -> Option<FileId> {
        self.file_id
    }

    /// Whether these bindings were produced for this exact arena and root.
    #[must_use]
    pub fn is_for_source(&self, arena: &NodeArena, source_file: NodeId) -> bool {
        self.arena_id == arena.id() && self.bound_source_file == source_file
    }

    #[must_use]
    pub fn root_scope(&self) -> Option<&Scope> {
        self.scopes.first()
    }

    /// Returns program-bound control flow only for the exact arena and source
    /// root that produced this result. Standalone binding has no graph because
    /// it has no trustworthy program `FileId` for `NodeRef` payloads.
    #[must_use]
    pub fn flow_graph(&self, arena: &NodeArena, source_file: NodeId) -> Option<&BoundFlowGraph> {
        self.is_for_source(arena, source_file)
            .then_some(self.flow.as_ref())
            .flatten()
    }

    #[must_use]
    pub fn scope(&self, id: ScopeId) -> Option<&Scope> {
        self.scopes.get(id.index())
    }

    /// Resolves a name using the lexical scope containing `node`.
    #[must_use]
    pub fn resolve_name_at(&self, node: NodeId, name: &str) -> Option<SymbolId> {
        if let Some(symbol) = self.node_symbols.get(&node).copied()
            && self
                .symbols
                .get(symbol)
                .is_some_and(|symbol| symbol.name == name)
        {
            return Some(symbol);
        }
        let container = self.containers.get(&node).copied().unwrap_or(node);
        let mut scope = self.node_scopes.get(&container).copied().or_else(|| {
            self.scopes
                .iter()
                .find(|scope| scope.owner == container)
                .map(|scope| scope.id)
        })?;
        loop {
            let current = self.scope(scope)?;
            if let Some(symbol) = current.symbols.get(name) {
                return Some(symbol);
            }
            if current.kind == ScopeKind::Module
                && let Some(symbol) = self.node_symbols.get(&current.owner)
                && let Some(symbol) = self.symbols.get(*symbol)
                && let Some(member) = symbol.members.get(name)
            {
                return Some(member);
            }
            scope = current.parent?;
        }
    }
}

/// Binds declarations reachable from one source-file node.
///
/// # Panics
///
/// Panics if `source_file` is not a `SourceFile` node in `arena`.
#[must_use]
pub fn bind_source_file(arena: &NodeArena, source_file: NodeId) -> BindResult {
    Binder::new(arena, source_file, None).bind()
}

/// Binds one source file using its stable identity in a compiler Program.
///
/// # Panics
///
/// Panics if `source_file` is not a `SourceFile` node in `arena`.
#[must_use]
pub fn bind_source_file_in_file(
    arena: &NodeArena,
    source_file: NodeId,
    file_id: FileId,
) -> BindResult {
    Binder::new(arena, source_file, Some(file_id)).bind()
}

struct Binder<'a> {
    arena: &'a NodeArena,
    result: BindResult,
    children: HashMap<NodeId, Vec<NodeId>>,
    implicit_export_depth: usize,
}

impl<'a> Binder<'a> {
    fn new(arena: &'a NodeArena, source_file: NodeId, file_id: Option<FileId>) -> Self {
        assert!(
            matches!(
                arena.get(source_file).map(|node| &node.data),
                Some(NodeData::SourceFile(_))
            ),
            "binder source file must be a valid SourceFile node in its arena"
        );
        let mut children = HashMap::<NodeId, Vec<NodeId>>::new();
        for (id, node) in arena.iter() {
            if let Some(parent) = node.parent {
                children.entry(parent).or_default().push(id);
            }
        }
        Self {
            arena,
            result: BindResult::new(arena, source_file, file_id),
            children,
            implicit_export_depth: 0,
        }
    }

    fn bind(mut self) -> BindResult {
        let source_file = self.result.bound_source_file;
        let Some(node) = self.arena.get(source_file) else {
            return self.result;
        };
        if !matches!(node.data, NodeData::SourceFile(_)) {
            return self.result;
        }
        let root = self.create_scope(ScopeKind::SourceFile, source_file, None);
        self.result.node_scopes.insert(source_file, root);
        self.result.containers.insert(source_file, source_file);
        self.bind_node(source_file, root, source_file, None);
        if let Some(file_id) = self.result.file_id {
            self.result.flow = Some(build_flow_graph(
                self.arena,
                &self.children,
                source_file,
                file_id,
            ));
        }
        self.result
    }

    // Keeping declaration-kind dispatch together makes additions auditable
    // against NodeData as the port expands.
    #[allow(clippy::too_many_lines)]
    fn bind_node(
        &mut self,
        node_id: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        self.result.containers.insert(node_id, container);
        let Some(node) = self.arena.get(node_id) else {
            return;
        };
        if self.implicit_export_depth > 0 && self.has_modifier(node_id, SyntaxKind::DeclareKeyword)
        {
            let message = message_by_code(1038).expect("binder diagnostic is in catalog");
            self.result.diagnostics.push(BindDiagnostic {
                node: node_id,
                diagnostic: Diagnostic::new(message),
            });
        }
        match &node.data {
            NodeData::SourceFile(data) => {
                for statement in &data.statements.nodes {
                    self.bind_node(*statement, scope, node_id, parent_symbol);
                }
            }
            NodeData::Block(data) => {
                let block_scope = self.create_scope(ScopeKind::Block, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, block_scope);
                for statement in &data.statements.nodes {
                    self.bind_node(*statement, block_scope, node_id, parent_symbol);
                }
            }
            NodeData::CaseBlock(data) => {
                let case_scope = self.create_scope(ScopeKind::Block, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, case_scope);
                for clause in &data.clauses.nodes {
                    self.bind_node(*clause, case_scope, node_id, parent_symbol);
                }
            }
            NodeData::CatchClause(data) => {
                let catch_scope = self.create_scope(ScopeKind::Block, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, catch_scope);
                if let Some(variable) = data.variable_declaration {
                    self.bind_node(variable, catch_scope, node_id, parent_symbol);
                }
                self.bind_node(data.block, catch_scope, node_id, parent_symbol);
            }
            NodeData::ForStatement(data) => {
                let loop_scope = self.create_scope(ScopeKind::Block, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, loop_scope);
                if let Some(initializer) = data.initializer {
                    self.bind_node(initializer, loop_scope, node_id, parent_symbol);
                }
                if let Some(condition) = data.condition {
                    self.bind_node(condition, loop_scope, node_id, parent_symbol);
                }
                if let Some(incrementor) = data.incrementor {
                    self.bind_node(incrementor, loop_scope, node_id, parent_symbol);
                }
                self.bind_node(data.statement, loop_scope, node_id, parent_symbol);
            }
            NodeData::ForInOrOfStatement(data) => {
                let loop_scope = self.create_scope(ScopeKind::Block, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, loop_scope);
                self.bind_node(data.initializer, loop_scope, node_id, parent_symbol);
                self.bind_node(data.expression, loop_scope, node_id, parent_symbol);
                self.bind_node(data.statement, loop_scope, node_id, parent_symbol);
            }
            NodeData::ModuleBlock(data) => {
                self.result.node_scopes.insert(node_id, scope);
                for statement in &data.statements.nodes {
                    self.bind_node(*statement, scope, node_id, parent_symbol);
                }
            }
            NodeData::FunctionDeclaration(data) => {
                let symbol = data.name.and_then(|name| {
                    self.declare_and_export(
                        scope,
                        node_id,
                        name,
                        SymbolFlags::FUNCTION,
                        SymbolFlags::FUNCTION_EXCLUDES,
                        parent_symbol,
                    )
                });
                let function_scope = self.create_scope(ScopeKind::Function, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, function_scope);
                self.bind_type_parameters(
                    data.type_parameters.as_ref(),
                    function_scope,
                    node_id,
                    symbol,
                );
                for parameter in &data.parameters.nodes {
                    self.bind_parameter(*parameter, function_scope, node_id, symbol);
                }
                if let Some(return_type) = data.type_ {
                    self.bind_node(return_type, function_scope, node_id, symbol);
                }
                if let Some(body) = data.body {
                    self.bind_node(body, function_scope, node_id, symbol);
                }
            }
            NodeData::ClassDeclaration(data) => {
                let symbol = data.name.and_then(|name| {
                    self.declare_and_export(
                        scope,
                        node_id,
                        name,
                        SymbolFlags::CLASS,
                        SymbolFlags::CLASS_EXCLUDES,
                        parent_symbol,
                    )
                });
                let class_scope = self.create_scope(ScopeKind::Class, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, class_scope);
                self.bind_type_parameters(
                    data.type_parameters.as_ref(),
                    class_scope,
                    node_id,
                    symbol,
                );
                for member in &data.members.nodes {
                    self.bind_node(*member, class_scope, node_id, symbol);
                }
                if let Some(heritage) = &data.heritage_clauses {
                    for clause in &heritage.nodes {
                        self.bind_node(*clause, class_scope, node_id, symbol);
                    }
                }
            }
            NodeData::ClassExpression(data) => {
                // A named class expression introduces its name only in the class's own
                // lexical scope. Binding it in the enclosing scope would incorrectly
                // expose the name after the expression, while omitting it leaves static
                // field initializers and methods unable to resolve self references.
                let class_scope = self.create_scope(ScopeKind::Class, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, class_scope);
                let symbol = data.name.and_then(|name| {
                    self.declare_named(
                        class_scope,
                        node_id,
                        name,
                        SymbolFlags::CLASS,
                        SymbolFlags::CLASS_EXCLUDES,
                        parent_symbol,
                    )
                });
                self.bind_type_parameters(
                    data.type_parameters.as_ref(),
                    class_scope,
                    node_id,
                    symbol,
                );
                for member in &data.members.nodes {
                    self.bind_node(*member, class_scope, node_id, symbol);
                }
                if let Some(heritage) = &data.heritage_clauses {
                    for clause in &heritage.nodes {
                        self.bind_node(*clause, class_scope, node_id, symbol);
                    }
                }
            }
            NodeData::InterfaceDeclaration(data) => {
                let symbol = self.declare_and_export(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::INTERFACE,
                    SymbolFlags::INTERFACE_EXCLUDES,
                    parent_symbol,
                );
                let interface_scope = self.create_scope(ScopeKind::Interface, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, interface_scope);
                self.bind_type_parameters(
                    data.type_parameters.as_ref(),
                    interface_scope,
                    node_id,
                    symbol,
                );
                for member in &data.members.nodes {
                    self.bind_node(*member, interface_scope, node_id, symbol);
                }
                if let Some(heritage) = &data.heritage_clauses {
                    for clause in &heritage.nodes {
                        self.bind_node(*clause, interface_scope, node_id, symbol);
                    }
                }
            }
            NodeData::TypeAliasDeclaration(data) => {
                let symbol = self.declare_and_export(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::TYPE_ALIAS,
                    SymbolFlags::TYPE_ALIAS_EXCLUDES,
                    parent_symbol,
                );
                if data.type_parameters.is_some() {
                    let alias_scope = self.create_scope(ScopeKind::TypeAlias, node_id, Some(scope));
                    self.result.node_scopes.insert(node_id, alias_scope);
                    self.bind_type_parameters(
                        data.type_parameters.as_ref(),
                        alias_scope,
                        node_id,
                        symbol,
                    );
                    self.bind_node(data.type_, alias_scope, node_id, symbol);
                } else {
                    self.bind_node(data.type_, scope, container, symbol);
                }
            }
            NodeData::EnumDeclaration(data) => {
                let flags = if self.has_modifier(node_id, SyntaxKind::ConstKeyword) {
                    SymbolFlags::CONST_ENUM
                } else {
                    SymbolFlags::REGULAR_ENUM
                };
                let excludes = if flags == SymbolFlags::CONST_ENUM {
                    SymbolFlags::CONST_ENUM_EXCLUDES
                } else {
                    SymbolFlags::REGULAR_ENUM_EXCLUDES
                };
                let symbol = self.declare_and_export(
                    scope,
                    node_id,
                    data.name,
                    flags,
                    excludes,
                    parent_symbol,
                );
                let enum_scope = self.create_scope(ScopeKind::Enum, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, enum_scope);
                for member in &data.members.nodes {
                    self.bind_node(*member, enum_scope, node_id, symbol);
                }
            }
            NodeData::ModuleDeclaration(data) => {
                let ambient = self.implicit_export_depth > 0
                    || self.has_modifier(node_id, SyntaxKind::DeclareKeyword);
                let symbol = self.declare_and_export(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::NAMESPACE_MODULE,
                    SymbolFlags::NAMESPACE_MODULE_EXCLUDES,
                    parent_symbol,
                );
                let module_scope = self.create_scope(ScopeKind::Module, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, module_scope);
                if let Some(body) = data.body {
                    if ambient {
                        self.implicit_export_depth += 1;
                    }
                    self.bind_node(body, module_scope, node_id, symbol);
                    if ambient {
                        self.implicit_export_depth -= 1;
                    }
                }
            }
            NodeData::EnumMember(data) => {
                self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::ENUM_MEMBER,
                    SymbolFlags::ENUM_MEMBER_EXCLUDES,
                    parent_symbol,
                );
            }
            NodeData::VariableStatement(data) => {
                self.bind_variable_list(data.declaration_list, scope, container, parent_symbol);
                if self.should_export(node_id, parent_symbol) {
                    self.export_variable_list(data.declaration_list, parent_symbol);
                }
            }
            NodeData::VariableDeclarationList(_) => {
                self.bind_variable_list(node_id, scope, container, parent_symbol);
            }
            NodeData::VariableDeclaration(data) => {
                self.declare_binding_name(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::BLOCK_SCOPED_VARIABLE,
                    SymbolFlags::BLOCK_SCOPED_VARIABLE_EXCLUDES,
                    parent_symbol,
                );
            }
            NodeData::PropertyDeclaration(data) => {
                self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::PROPERTY,
                    SymbolFlags::PROPERTY_EXCLUDES,
                    parent_symbol,
                );
                if let Some(initializer) = data.initializer {
                    self.bind_node(initializer, scope, container, parent_symbol);
                }
                if let Some(type_) = data.type_ {
                    self.bind_node(type_, scope, container, parent_symbol);
                }
            }
            NodeData::PropertySignatureDeclaration(data) => {
                self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::PROPERTY,
                    SymbolFlags::PROPERTY_EXCLUDES,
                    parent_symbol,
                );
                self.bind_node(data.type_, scope, container, parent_symbol);
            }
            NodeData::MethodDeclaration(data) => {
                let symbol = self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::METHOD,
                    SymbolFlags::METHOD_EXCLUDES,
                    parent_symbol,
                );
                self.bind_function_like(
                    node_id,
                    scope,
                    symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.body,
                );
                if let Some(type_) = data.type_ {
                    self.bind_node(type_, scope, node_id, symbol);
                }
            }
            NodeData::MethodSignatureDeclaration(data) => {
                let symbol = self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::METHOD,
                    SymbolFlags::METHOD_EXCLUDES,
                    parent_symbol,
                );
                self.bind_function_like(
                    node_id,
                    scope,
                    symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    None,
                );
                if let Some(type_) = data.type_ {
                    self.bind_node(type_, scope, node_id, symbol);
                }
            }
            NodeData::GetAccessorDeclaration(data) => {
                let symbol = self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::GET_ACCESSOR,
                    SymbolFlags::GET_ACCESSOR_EXCLUDES,
                    parent_symbol,
                );
                self.bind_function_like(
                    node_id,
                    scope,
                    symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.body,
                );
            }
            NodeData::SetAccessorDeclaration(data) => {
                let symbol = self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::SET_ACCESSOR,
                    SymbolFlags::SET_ACCESSOR_EXCLUDES,
                    parent_symbol,
                );
                self.bind_function_like(
                    node_id,
                    scope,
                    symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.body,
                );
            }
            NodeData::ConstructorDeclaration(data) => {
                let symbol = self.declare_synthetic(
                    scope,
                    node_id,
                    "__constructor",
                    SymbolFlags::CONSTRUCTOR,
                    SymbolFlags::NONE,
                    parent_symbol,
                );
                self.bind_function_like(
                    node_id,
                    scope,
                    Some(symbol),
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.body,
                );
            }
            NodeData::FunctionTypeNode(data) => {
                self.bind_signature_type(
                    node_id,
                    scope,
                    parent_symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.type_,
                );
            }
            NodeData::ConstructorTypeNode(data) => {
                self.bind_signature_type(
                    node_id,
                    scope,
                    parent_symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.type_,
                );
            }
            NodeData::CallSignatureDeclaration(data) => {
                self.bind_signature_type(
                    node_id,
                    scope,
                    parent_symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.type_,
                );
            }
            NodeData::ConstructSignatureDeclaration(data) => {
                self.bind_signature_type(
                    node_id,
                    scope,
                    parent_symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.type_,
                );
            }
            NodeData::TypeLiteralNode(_) => {
                let type_scope = self.create_scope(ScopeKind::Interface, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, type_scope);
                self.bind_children(node_id, type_scope, node_id, parent_symbol);
            }
            NodeData::ArrowFunction(data) => {
                self.bind_function_like(
                    node_id,
                    scope,
                    parent_symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    Some(data.body),
                );
            }
            NodeData::FunctionExpression(data) => {
                self.bind_function_like(
                    node_id,
                    scope,
                    parent_symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    Some(data.body),
                );
            }
            NodeData::TypeParameterDeclaration(data) => {
                self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::TYPE_PARAMETER,
                    SymbolFlags::TYPE_PARAMETER_EXCLUDES,
                    parent_symbol,
                );
                if let Some(constraint) = data.constraint {
                    self.bind_node(constraint, scope, container, parent_symbol);
                }
                if let Some(default_type) = data.default_type {
                    self.bind_node(default_type, scope, container, parent_symbol);
                }
            }
            NodeData::ImportDeclaration(data) => {
                if let Some(clause) = data.import_clause {
                    self.bind_import_clause(clause, scope, container, parent_symbol);
                }
                self.bind_node(data.module_specifier, scope, container, parent_symbol);
            }
            NodeData::ImportEqualsDeclaration(data) => {
                self.declare_and_export(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::ALIAS,
                    SymbolFlags::ALIAS_EXCLUDES,
                    parent_symbol,
                );
                self.bind_node(data.module_reference, scope, container, parent_symbol);
            }
            NodeData::ExportDeclaration(data) => {
                if let Some(clause) = data.export_clause {
                    self.bind_export_clause(clause, scope, container, parent_symbol);
                }
                if let Some(module_specifier) = data.module_specifier {
                    self.bind_node(module_specifier, scope, container, parent_symbol);
                }
            }
            NodeData::ExportAssignment(data) => {
                let name = if data.is_export_equals {
                    "export="
                } else {
                    "default"
                };
                self.declare_export_alias(node_id, name, None, parent_symbol);
                self.bind_node(data.expression, scope, container, parent_symbol);
            }
            NodeData::BinaryExpression(_) => {
                self.bind_binary_expression_children(node_id, scope, container, parent_symbol);
            }
            _ => self.bind_children(node_id, scope, container, parent_symbol),
        }
    }

    fn bind_binary_expression_children(
        &mut self,
        node_id: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        let mut pending = self
            .children
            .get(&node_id)
            .into_iter()
            .flatten()
            .rev()
            .copied()
            .collect::<Vec<_>>();
        while let Some(child) = pending.pop() {
            if matches!(
                self.arena.get(child).map(|node| &node.data),
                Some(NodeData::BinaryExpression(_))
            ) {
                self.result.containers.insert(child, container);
                if let Some(children) = self.children.get(&child) {
                    pending.extend(children.iter().rev().copied());
                }
            } else {
                self.bind_node(child, scope, container, parent_symbol);
            }
        }
    }

    fn bind_variable_list(
        &mut self,
        list_id: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        self.result.containers.insert(list_id, container);
        let Some(node) = self.arena.get(list_id) else {
            return;
        };
        let NodeData::VariableDeclarationList(data) = &node.data else {
            return;
        };
        let block_scoped = node.flags.0 & (NodeFlags(1 << 0).0 | NodeFlags(1 << 1).0) != 0;
        let flags = if block_scoped {
            SymbolFlags::BLOCK_SCOPED_VARIABLE
        } else {
            SymbolFlags::FUNCTION_SCOPED_VARIABLE
        };
        let excludes = if block_scoped {
            SymbolFlags::BLOCK_SCOPED_VARIABLE_EXCLUDES
        } else {
            SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES
        };
        let target_scope = if block_scoped {
            scope
        } else {
            self.nearest_var_scope(scope)
        };
        for declaration in &data.declarations.nodes {
            self.result.containers.insert(*declaration, container);
            if let Some(NodeData::VariableDeclaration(declaration_data)) =
                self.arena.get(*declaration).map(|node| &node.data)
            {
                let name = declaration_data.name;
                let type_ = declaration_data.type_;
                let initializer = declaration_data.initializer;
                self.declare_binding_name(
                    target_scope,
                    *declaration,
                    name,
                    flags,
                    excludes,
                    parent_symbol,
                );
                if let Some(type_) = type_ {
                    self.bind_node(type_, scope, container, parent_symbol);
                }
                if let Some(initializer) = initializer {
                    self.bind_node(initializer, scope, container, parent_symbol);
                }
            }
        }
    }

    fn export_variable_list(&mut self, list_id: NodeId, parent_symbol: Option<SymbolId>) {
        let Some(NodeData::VariableDeclarationList(list)) =
            self.arena.get(list_id).map(|node| &node.data)
        else {
            return;
        };
        for declaration in &list.declarations.nodes {
            let Some(symbol_id) = self.result.node_symbols.get(declaration).copied() else {
                continue;
            };
            let Some(symbol) = self.result.symbols.get(symbol_id) else {
                continue;
            };
            let name = symbol.name.clone();
            if let Some(parent) = parent_symbol {
                self.result
                    .symbols
                    .get_mut(parent)
                    .unwrap()
                    .members
                    .insert(name, symbol_id);
            } else {
                self.result.exports.insert(name, symbol_id);
            }
        }
    }

    fn bind_parameter(
        &mut self,
        parameter: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        self.result.containers.insert(parameter, container);
        if let Some(NodeData::ParameterDeclaration(data)) =
            self.arena.get(parameter).map(|node| &node.data)
        {
            let name = data.name;
            let type_ = data.type_;
            let initializer = data.initializer;
            let property_name = data
                .modifiers
                .as_ref()
                .filter(|modifiers| {
                    modifiers.list.nodes.iter().any(|modifier| {
                        self.arena.get(*modifier).is_some_and(|modifier| {
                            matches!(
                                modifier.kind,
                                SyntaxKind::OverrideKeyword
                                    | SyntaxKind::PrivateKeyword
                                    | SyntaxKind::ProtectedKeyword
                                    | SyntaxKind::PublicKeyword
                                    | SyntaxKind::ReadonlyKeyword
                            )
                        })
                    })
                })
                .and_then(|_| self.identifier_text(name).map(str::to_owned));
            self.declare_binding_name(
                scope,
                parameter,
                name,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::PARAMETER_EXCLUDES,
                parent_symbol,
            );
            if let Some(property_name) = property_name
                && self.is_constructor_like(container)
                && let Some(class_scope) = self.result.scopes[scope.index()].parent
                && self.result.scopes[class_scope.index()].kind == ScopeKind::Class
                && let Some(class_symbol) = parent_symbol
                    .and_then(|symbol| self.result.symbols.get(symbol))
                    .and_then(|symbol| symbol.parent)
            {
                self.declare_name(
                    class_scope,
                    parameter,
                    property_name,
                    SymbolFlags::PROPERTY,
                    SymbolFlags::PROPERTY_EXCLUDES,
                    Some(class_symbol),
                );
            }
            if let Some(type_) = type_ {
                self.bind_node(type_, scope, container, parent_symbol);
            }
            if let Some(initializer) = initializer {
                self.bind_node(initializer, scope, container, parent_symbol);
            }
        }
    }

    fn is_constructor_like(&self, node: NodeId) -> bool {
        matches!(
            self.arena.get(node).map(|node| &node.data),
            Some(NodeData::ConstructorDeclaration(_))
        )
    }

    fn bind_type_parameters(
        &mut self,
        type_parameters: Option<&ts_ast::NodeList>,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        if let Some(type_parameters) = type_parameters {
            for type_parameter in &type_parameters.nodes {
                self.bind_node(*type_parameter, scope, container, parent_symbol);
            }
        }
    }

    fn bind_function_like(
        &mut self,
        node_id: NodeId,
        parent_scope: ScopeId,
        parent_symbol: Option<SymbolId>,
        type_parameters: Option<&ts_ast::NodeList>,
        parameters: &[NodeId],
        body: Option<NodeId>,
    ) {
        let function_scope = self.create_scope(ScopeKind::Function, node_id, Some(parent_scope));
        self.result.node_scopes.insert(node_id, function_scope);
        self.bind_type_parameters(type_parameters, function_scope, node_id, parent_symbol);
        for parameter in parameters {
            self.bind_parameter(*parameter, function_scope, node_id, parent_symbol);
        }
        if let Some(body) = body {
            self.bind_node(body, function_scope, node_id, parent_symbol);
        }
    }

    fn bind_signature_type(
        &mut self,
        node_id: NodeId,
        parent_scope: ScopeId,
        parent_symbol: Option<SymbolId>,
        type_parameters: Option<&ts_ast::NodeList>,
        parameters: &[NodeId],
        return_type: Option<NodeId>,
    ) {
        self.bind_function_like(
            node_id,
            parent_scope,
            parent_symbol,
            type_parameters,
            parameters,
            None,
        );
        if let Some(return_type) = return_type {
            let function_scope = self.result.node_scopes[&node_id];
            self.bind_node(return_type, function_scope, node_id, parent_symbol);
        }
    }

    fn bind_import_clause(
        &mut self,
        clause: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        self.result.containers.insert(clause, container);
        let Some(NodeData::ImportClause(data)) = self.arena.get(clause).map(|node| &node.data)
        else {
            return;
        };
        if let Some(name) = data.name {
            self.declare_named(
                scope,
                clause,
                name,
                SymbolFlags::ALIAS,
                SymbolFlags::ALIAS_EXCLUDES,
                parent_symbol,
            );
        }
        let Some(bindings) = data.named_bindings else {
            return;
        };
        self.result.containers.insert(bindings, container);
        match self.arena.get(bindings).map(|node| &node.data) {
            Some(NodeData::NamedImports(imports)) => {
                let elements = imports.elements.nodes.clone();
                for specifier in elements {
                    self.result.containers.insert(specifier, container);
                    if let Some(NodeData::ImportSpecifier(specifier_data)) =
                        self.arena.get(specifier).map(|node| &node.data)
                    {
                        if let Some(property_name) = specifier_data.property_name {
                            self.result.containers.insert(property_name, container);
                        }
                        self.declare_named(
                            scope,
                            specifier,
                            specifier_data.name,
                            SymbolFlags::ALIAS,
                            SymbolFlags::ALIAS_EXCLUDES,
                            parent_symbol,
                        );
                    }
                }
            }
            Some(NodeData::NamespaceImport(import)) => {
                self.declare_named(
                    scope,
                    bindings,
                    import.name,
                    SymbolFlags::ALIAS,
                    SymbolFlags::ALIAS_EXCLUDES,
                    parent_symbol,
                );
            }
            _ => {}
        }
    }

    fn bind_export_clause(
        &mut self,
        clause: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        self.result.containers.insert(clause, container);
        let Some(NodeData::NamedExports(exports)) = self.arena.get(clause).map(|node| &node.data)
        else {
            return;
        };
        let elements = exports.elements.nodes.clone();
        for specifier in elements {
            self.result.containers.insert(specifier, container);
            let Some(NodeData::ExportSpecifier(data)) =
                self.arena.get(specifier).map(|node| &node.data)
            else {
                continue;
            };
            let Some(name) = self.declaration_name_text(data.name) else {
                continue;
            };
            let local_name_node = data.property_name.unwrap_or(data.name);
            let target = self
                .identifier_text(local_name_node)
                .and_then(|name| self.lookup_symbol(scope, name));
            self.result.containers.insert(local_name_node, container);
            if let Some(target) = target {
                self.result.node_symbols.insert(local_name_node, target);
            }
            let alias = self.declare_export_alias(specifier, &name, target, parent_symbol);
            self.result.node_symbols.insert(data.name, alias);
            self.result.node_symbols.insert(specifier, alias);
        }
    }

    fn declare_binding_name(
        &mut self,
        scope: ScopeId,
        declaration: NodeId,
        name: NodeId,
        flags: SymbolFlags,
        excludes: SymbolFlags,
        parent_symbol: Option<SymbolId>,
    ) {
        let Some(node) = self.arena.get(name) else {
            return;
        };
        match &node.data {
            NodeData::Identifier(_) => {
                self.declare_named(scope, declaration, name, flags, excludes, parent_symbol);
            }
            NodeData::BindingPattern(pattern) => {
                for element in &pattern.elements.nodes {
                    if let Some(NodeData::BindingElement(element_data)) =
                        self.arena.get(*element).map(|node| &node.data)
                        && let Some(element_name) = element_data.name
                    {
                        self.declare_binding_name(
                            scope,
                            declaration,
                            element_name,
                            flags,
                            excludes,
                            parent_symbol,
                        );
                    }
                }
            }
            _ => {}
        }
    }

    fn declare_named(
        &mut self,
        scope: ScopeId,
        declaration: NodeId,
        name_node: NodeId,
        flags: SymbolFlags,
        excludes: SymbolFlags,
        parent_symbol: Option<SymbolId>,
    ) -> Option<SymbolId> {
        let computed_expression = match self.arena.get(name_node).map(|node| &node.data) {
            Some(NodeData::ComputedPropertyName(computed)) => Some(computed.expression),
            _ => None,
        };
        if let Some(expression) = computed_expression {
            let expression_scope = self
                .result
                .scope(scope)
                .and_then(|scope| {
                    matches!(
                        scope.kind,
                        ScopeKind::Class
                            | ScopeKind::Interface
                            | ScopeKind::Enum
                            | ScopeKind::TypeAlias
                    )
                    .then_some(scope.parent)
                    .flatten()
                })
                .unwrap_or(scope);
            let expression_container = self
                .result
                .scope(expression_scope)
                .map_or(declaration, |scope| scope.owner);
            let expression_parent_symbol =
                self.result.node_symbols.get(&expression_container).copied();
            self.bind_node(
                expression,
                expression_scope,
                expression_container,
                expression_parent_symbol,
            );
        }
        let name = self.declaration_name_text(name_node)?;
        let id = self.declare_name(scope, declaration, name, flags, excludes, parent_symbol)?;
        self.result.node_symbols.insert(declaration, id);
        self.result.node_symbols.insert(name_node, id);
        if let Some(container) = self.result.containers.get(&declaration).copied() {
            self.result.containers.insert(name_node, container);
        }
        Some(id)
    }

    fn declare_and_export(
        &mut self,
        scope: ScopeId,
        declaration: NodeId,
        name_node: NodeId,
        flags: SymbolFlags,
        excludes: SymbolFlags,
        parent_symbol: Option<SymbolId>,
    ) -> Option<SymbolId> {
        let id = self.declare_named(
            scope,
            declaration,
            name_node,
            flags,
            excludes,
            parent_symbol,
        )?;
        if self.should_export(declaration, parent_symbol) {
            let export_name = if self.has_modifier(declaration, SyntaxKind::DefaultKeyword) {
                "default".to_owned()
            } else {
                self.identifier_text(name_node)?.to_owned()
            };
            if let Some(parent) = parent_symbol {
                self.result
                    .symbols
                    .get_mut(parent)?
                    .members
                    .insert(export_name, id);
            } else {
                self.result.exports.insert(export_name, id);
            }
        }
        Some(id)
    }

    fn declare_synthetic(
        &mut self,
        scope: ScopeId,
        declaration: NodeId,
        name: &str,
        flags: SymbolFlags,
        excludes: SymbolFlags,
        parent_symbol: Option<SymbolId>,
    ) -> SymbolId {
        let id = self
            .declare_name(
                scope,
                declaration,
                name.to_owned(),
                flags,
                excludes,
                parent_symbol,
            )
            .expect("scope and symbol IDs originate from this binder");
        self.result.node_symbols.insert(declaration, id);
        id
    }

    fn declare_name(
        &mut self,
        scope: ScopeId,
        declaration: NodeId,
        name: String,
        flags: SymbolFlags,
        excludes: SymbolFlags,
        parent_symbol: Option<SymbolId>,
    ) -> Option<SymbolId> {
        let existing = self.result.scopes[scope.index()].symbols.get(&name);
        let id = if let Some(existing) = existing {
            let existing_flags = self.result.symbols.get(existing)?.flags;
            if !can_merge(existing_flags, flags, excludes) {
                if existing_flags.intersects(SymbolFlags::ENUM)
                    || flags.intersects(SymbolFlags::ENUM)
                {
                    let prior_declarations =
                        self.result.symbols.get(existing)?.declarations.clone();
                    for prior in prior_declarations {
                        self.report_enum_merge_error(prior);
                    }
                    self.report_enum_merge_error(declaration);
                } else {
                    let code = if existing_flags.intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE)
                        || flags.intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE)
                    {
                        2451
                    } else {
                        2300
                    };
                    let message = message_by_code(code).expect("binder diagnostic is in catalog");
                    self.result.diagnostics.push(BindDiagnostic {
                        node: declaration,
                        diagnostic: Diagnostic::with_arguments(message, [name.clone()]),
                    });
                }
            }
            let symbol = self.result.symbols.get_mut(existing)?;
            symbol.flags |= flags;
            symbol.declarations.push(declaration);
            if symbol.value_declaration.is_none() && is_value(flags) {
                symbol.value_declaration = Some(declaration);
            }
            existing
        } else {
            let id = self
                .result
                .symbols
                .alloc(name.clone(), flags, declaration, parent_symbol);
            self.result.scopes[scope.index()]
                .symbols
                .insert(name.clone(), id);
            if matches!(
                self.result.scopes[scope.index()].kind,
                ScopeKind::Class | ScopeKind::Interface | ScopeKind::Enum
            ) && let Some(parent) = parent_symbol
                && let Some(parent) = self.result.symbols.get_mut(parent)
            {
                parent.members.insert(name, id);
            }
            id
        };
        Some(id)
    }

    fn report_enum_merge_error(&mut self, declaration: NodeId) {
        if self.result.diagnostics.iter().any(|diagnostic| {
            diagnostic.node == declaration && diagnostic.diagnostic.code() == 2567
        }) {
            return;
        }
        let message = message_by_code(2567).expect("binder diagnostic is in catalog");
        self.result.diagnostics.push(BindDiagnostic {
            node: declaration,
            diagnostic: Diagnostic::new(message),
        });
    }

    fn declare_export_alias(
        &mut self,
        declaration: NodeId,
        name: &str,
        target: Option<SymbolId>,
        parent_symbol: Option<SymbolId>,
    ) -> SymbolId {
        let id = self.result.symbols.alloc(
            name.to_owned(),
            SymbolFlags::ALIAS,
            declaration,
            parent_symbol,
        );
        self.result.symbols.get_mut(id).unwrap().target = target;
        if let Some(parent) = parent_symbol {
            self.result
                .symbols
                .get_mut(parent)
                .unwrap()
                .members
                .insert(name.to_owned(), id);
        } else {
            self.result.exports.insert(name.to_owned(), id);
        }
        id
    }

    fn lookup_symbol(&self, mut scope: ScopeId, name: &str) -> Option<SymbolId> {
        loop {
            let current = self.result.scope(scope)?;
            if let Some(symbol) = current.symbols.get(name) {
                return Some(symbol);
            }
            scope = current.parent?;
        }
    }

    fn has_modifier(&self, declaration: NodeId, modifier: SyntaxKind) -> bool {
        let modifiers = match &self.arena.get(declaration).map(|node| &node.data) {
            Some(NodeData::FunctionDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::ClassDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::InterfaceDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::TypeAliasDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::EnumDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::ImportDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::ImportEqualsDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::ModuleDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::VariableStatement(data)) => data.modifiers.as_ref(),
            _ => None,
        };
        modifiers.is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|node| {
                self.arena
                    .get(*node)
                    .is_some_and(|node| node.kind == modifier)
            })
        })
    }

    fn should_export(&self, declaration: NodeId, parent_symbol: Option<SymbolId>) -> bool {
        self.has_modifier(declaration, SyntaxKind::ExportKeyword)
            || (parent_symbol.is_some()
                && self.implicit_export_depth > 0
                && self
                    .result
                    .containers
                    .get(&declaration)
                    .and_then(|container| self.arena.get(*container))
                    .is_some_and(|container| {
                        matches!(
                            container.data,
                            NodeData::ModuleBlock(_) | NodeData::ModuleDeclaration(_)
                        )
                    }))
    }

    fn bind_children(
        &mut self,
        node_id: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        let children = self.children.get(&node_id).cloned().unwrap_or_default();
        for child in children {
            self.bind_node(child, scope, container, parent_symbol);
        }
    }

    fn create_scope(&mut self, kind: ScopeKind, owner: NodeId, parent: Option<ScopeId>) -> ScopeId {
        let id = ScopeId(
            u32::try_from(self.result.scopes.len()).expect("scope arena exceeds u32::MAX scopes"),
        );
        self.result.scopes.push(Scope {
            id,
            kind,
            owner,
            parent,
            symbols: SymbolTable::default(),
        });
        id
    }

    fn nearest_var_scope(&self, mut scope: ScopeId) -> ScopeId {
        loop {
            let current = &self.result.scopes[scope.index()];
            if matches!(
                current.kind,
                ScopeKind::SourceFile | ScopeKind::Function | ScopeKind::Module
            ) {
                return scope;
            }
            scope = current.parent.unwrap_or(scope);
        }
    }

    fn identifier_text(&self, node: NodeId) -> Option<&str> {
        match &self.arena.get(node)?.data {
            NodeData::Identifier(identifier) => Some(&identifier.text),
            _ => None,
        }
    }

    fn declaration_name_text(&self, node: NodeId) -> Option<String> {
        match &self.arena.get(node)?.data {
            NodeData::Identifier(identifier) => Some(identifier.text.clone()),
            NodeData::PrivateIdentifier(identifier) => Some(identifier.text.clone()),
            NodeData::StringLiteral(literal) => Some(literal.text.clone()),
            NodeData::NumericLiteral(literal) => Some(literal.text.clone()),
            NodeData::NoSubstitutionTemplateLiteral(literal) => Some(literal.text.clone()),
            NodeData::ComputedPropertyName(computed) => {
                self.computed_property_name_text(computed.expression)
            }
            _ => None,
        }
    }

    fn computed_property_name_text(&self, node: NodeId) -> Option<String> {
        match &self.arena.get(node)?.data {
            NodeData::StringLiteral(literal) => Some(literal.text.clone()),
            NodeData::NumericLiteral(literal) => Some(literal.text.clone()),
            NodeData::NoSubstitutionTemplateLiteral(literal) => Some(literal.text.clone()),
            NodeData::ParenthesizedExpression(parenthesized) => {
                self.computed_property_name_text(parenthesized.expression)
            }
            _ => None,
        }
    }
}

fn can_merge(existing: SymbolFlags, new: SymbolFlags, excludes: SymbolFlags) -> bool {
    if existing.intersects(excludes) {
        return false;
    }

    // This allowlist is intentionally not full upstream parity. Keep the
    // binder's currently supported merge set after applying the conflict mask:
    // other mask-permitted merges depend on duplicate-member and class/function
    // checker diagnostics or module-instantiation state that are not ported.
    let existing_has_alias = existing.contains(SymbolFlags::ALIAS);
    let new_has_alias = new.contains(SymbolFlags::ALIAS);
    if new_has_alias {
        return true;
    }
    if existing_has_alias {
        let existing_without_alias = SymbolFlags(existing.0 & !SymbolFlags::ALIAS.0);
        return existing_without_alias == SymbolFlags::NONE
            || can_merge(existing_without_alias, new, excludes);
    }

    (existing.contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        && new == SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        || (existing.contains(SymbolFlags::FUNCTION) && new == SymbolFlags::FUNCTION)
        || (existing.contains(SymbolFlags::METHOD) && new == SymbolFlags::METHOD)
        || (existing.contains(SymbolFlags::INTERFACE) && new == SymbolFlags::INTERFACE)
        || (existing.intersects(SymbolFlags::INTERFACE | SymbolFlags::TYPE_ALIAS)
            && new.intersects(SymbolFlags::VARIABLE))
        || (new.intersects(SymbolFlags::INTERFACE | SymbolFlags::TYPE_ALIAS)
            && existing.intersects(SymbolFlags::VARIABLE))
        || (existing.contains(SymbolFlags::CONST_ENUM) && new == SymbolFlags::CONST_ENUM)
        || (existing.contains(SymbolFlags::REGULAR_ENUM) && new == SymbolFlags::REGULAR_ENUM)
        || (existing.contains(SymbolFlags::NAMESPACE_MODULE)
            && new == SymbolFlags::NAMESPACE_MODULE)
        || (new == SymbolFlags::NAMESPACE_MODULE
            && existing.intersects(
                SymbolFlags::FUNCTION
                    | SymbolFlags::CLASS
                    | SymbolFlags::ENUM
                    | SymbolFlags::NAMESPACE_MODULE,
            ))
        || (existing.contains(SymbolFlags::NAMESPACE_MODULE)
            && new.intersects(SymbolFlags::FUNCTION | SymbolFlags::CLASS | SymbolFlags::ENUM))
        || (existing == SymbolFlags::GET_ACCESSOR && new == SymbolFlags::SET_ACCESSOR)
        || (existing == SymbolFlags::SET_ACCESSOR && new == SymbolFlags::GET_ACCESSOR)
        || (new == SymbolFlags::CLASS
            && existing.contains(SymbolFlags::INTERFACE)
            && !existing.contains(SymbolFlags::CLASS))
        || (new == SymbolFlags::INTERFACE
            && existing.intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE))
}

fn is_value(flags: SymbolFlags) -> bool {
    flags.intersects(
        SymbolFlags::VARIABLE
            | SymbolFlags::PROPERTY
            | SymbolFlags::ENUM_MEMBER
            | SymbolFlags::FUNCTION
            | SymbolFlags::CLASS
            | SymbolFlags::ENUM
            | SymbolFlags::MODULE
            | SymbolFlags::METHOD
            | SymbolFlags::CONSTRUCTOR
            | SymbolFlags::GET_ACCESSOR
            | SymbolFlags::SET_ACCESSOR,
    )
}

#[cfg(test)]
mod tests {
    use ts_ast::{
        BlockData, ClassDeclarationData, EnumDeclarationData, EnumMemberData, FileId, FlowFlags,
        FlowNodePayload, FlowRef, FunctionDeclarationData, IdentifierData,
        InterfaceDeclarationData, Node, NodeArena, NodeData, NodeFlags, NodeId, NodeList, NodeRef,
        ReturnStatementData, SourceFileData, SymbolTable as AstSymbolTable, SyntaxKind, TokenData,
        TypeAliasDeclarationData, VariableDeclarationData, VariableDeclarationListData,
        VariableStatementData,
    };
    use ts_core::TextRange;
    use ts_parser::parse_source_file;

    use super::{
        BoundFlowGraph, ScopeKind, SymbolFlags, UnsupportedFlowKind, bind_source_file,
        bind_source_file_in_file, can_merge,
    };

    fn nodes_of_kind(arena: &NodeArena, kind: SyntaxKind) -> Vec<NodeId> {
        arena
            .iter()
            .filter_map(|(id, node)| (node.kind == kind).then_some(id))
            .collect()
    }

    fn source_statements(arena: &NodeArena, source_file: NodeId) -> Vec<NodeId> {
        let NodeData::SourceFile(source) = &arena.get(source_file).unwrap().data else {
            panic!("expected source file");
        };
        source.statements.nodes.clone()
    }

    fn block_statements(arena: &NodeArena, block: NodeId) -> Vec<NodeId> {
        let NodeData::Block(block) = &arena.get(block).unwrap().data else {
            panic!("expected block");
        };
        block.statements.nodes.clone()
    }

    fn switch_clauses(arena: &NodeArena, switch_statement: NodeId) -> Vec<NodeId> {
        let NodeData::SwitchStatement(switch) = &arena.get(switch_statement).unwrap().data else {
            panic!("expected switch statement");
        };
        let NodeData::CaseBlock(block) = &arena.get(switch.case_block).unwrap().data else {
            panic!("expected case block");
        };
        block.clauses.nodes.clone()
    }

    fn clause_statements(arena: &NodeArena, clause: NodeId) -> Vec<NodeId> {
        let NodeData::CaseOrDefaultClause(clause) = &arena.get(clause).unwrap().data else {
            panic!("expected case or default clause");
        };
        clause.statements.nodes.clone()
    }

    fn switch_clause_ranges(graph: &BoundFlowGraph) -> Vec<(NodeRef, i32, i32)> {
        graph
            .nodes()
            .iter()
            .filter_map(|node| match &node.payload {
                Some(FlowNodePayload::SwitchClause {
                    switch_statement,
                    clause_start,
                    clause_end,
                }) => Some((*switch_statement, *clause_start, *clause_end)),
                _ => None,
            })
            .collect()
    }

    fn nearest_ancestor_of_kind(arena: &NodeArena, node: NodeId, kind: SyntaxKind) -> NodeId {
        let mut current = node;
        loop {
            let parent = arena
                .get(current)
                .and_then(|node| node.parent)
                .expect("expected ancestor");
            if arena.get(parent).unwrap().kind == kind {
                return parent;
            }
            current = parent;
        }
    }

    fn label_named(arena: &NodeArena, name: &str) -> NodeId {
        nodes_of_kind(arena, SyntaxKind::LabeledStatement)
            .into_iter()
            .find_map(|statement| {
                let NodeData::LabeledStatement(data) = &arena.get(statement).unwrap().data else {
                    return None;
                };
                matches!(
                    &arena.get(data.label).unwrap().data,
                    NodeData::Identifier(identifier) if identifier.text == name
                )
                .then_some(data.label)
            })
            .unwrap()
    }

    fn branch_target_index(graph: &BoundFlowGraph, antecedent: FlowRef) -> usize {
        graph
            .nodes()
            .iter()
            .position(|node| {
                node.flags.contains(FlowFlags::BRANCH_LABEL)
                    && node.antecedents.contains(&antecedent)
            })
            .unwrap()
    }

    fn node_ref(arena: &NodeArena, file: FileId, node: NodeId) -> NodeRef {
        NodeRef::new(arena.id(), file, node)
    }

    fn assert_flow_flags(graph: &BoundFlowGraph, flow: FlowRef, flags: FlowFlags) {
        assert!(graph.nodes().get(flow).unwrap().flags.contains(flags));
    }

    #[test]
    fn symbol_flag_bits_match_pinned_upstream() {
        let primitive_flags = [
            (SymbolFlags::NONE, 0x0000_0000),
            (SymbolFlags::FUNCTION_SCOPED_VARIABLE, 0x0000_0001),
            (SymbolFlags::BLOCK_SCOPED_VARIABLE, 0x0000_0002),
            (SymbolFlags::PROPERTY, 0x0000_0004),
            (SymbolFlags::ENUM_MEMBER, 0x0000_0008),
            (SymbolFlags::FUNCTION, 0x0000_0010),
            (SymbolFlags::CLASS, 0x0000_0020),
            (SymbolFlags::INTERFACE, 0x0000_0040),
            (SymbolFlags::CONST_ENUM, 0x0000_0080),
            (SymbolFlags::REGULAR_ENUM, 0x0000_0100),
            (SymbolFlags::VALUE_MODULE, 0x0000_0200),
            (SymbolFlags::NAMESPACE_MODULE, 0x0000_0400),
            (SymbolFlags::TYPE_LITERAL, 0x0000_0800),
            (SymbolFlags::OBJECT_LITERAL, 0x0000_1000),
            (SymbolFlags::METHOD, 0x0000_2000),
            (SymbolFlags::CONSTRUCTOR, 0x0000_4000),
            (SymbolFlags::GET_ACCESSOR, 0x0000_8000),
            (SymbolFlags::SET_ACCESSOR, 0x0001_0000),
            (SymbolFlags::SIGNATURE, 0x0002_0000),
            (SymbolFlags::TYPE_PARAMETER, 0x0004_0000),
            (SymbolFlags::TYPE_ALIAS, 0x0008_0000),
            (SymbolFlags::EXPORT_VALUE, 0x0010_0000),
            (SymbolFlags::ALIAS, 0x0020_0000),
            (SymbolFlags::PROTOTYPE, 0x0040_0000),
            (SymbolFlags::EXPORT_STAR, 0x0080_0000),
            (SymbolFlags::OPTIONAL, 0x0100_0000),
            (SymbolFlags::TRANSIENT, 0x0200_0000),
            (SymbolFlags::ASSIGNMENT, 0x0400_0000),
            (SymbolFlags::MODULE_EXPORTS, 0x0800_0000),
            (SymbolFlags::CONST_ENUM_ONLY_MODULE, 0x1000_0000),
            (SymbolFlags::REPLACEABLE_BY_METHOD, 0x2000_0000),
            (SymbolFlags::GLOBAL_LOOKUP, 0x4000_0000),
            (SymbolFlags::ALL, 0x3fff_ffff),
        ];

        for (flags, expected) in primitive_flags {
            assert_eq!(flags.bits(), expected);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn symbol_flag_composites_and_exclusions_match_pinned_upstream() {
        let masks = [
            (SymbolFlags::ENUM, 0x0000_0180),
            (SymbolFlags::VARIABLE, 0x0000_0003),
            (SymbolFlags::VALUE, 0x0001_b3bf),
            (SymbolFlags::TYPE, 0x000c_09e8),
            (SymbolFlags::NAMESPACE, 0x0000_0780),
            (SymbolFlags::MODULE, 0x0000_0600),
            (SymbolFlags::ACCESSOR, 0x0001_8000),
            (SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES, 0x0001_b3be),
            (SymbolFlags::BLOCK_SCOPED_VARIABLE_EXCLUDES, 0x0001_b3bf),
            (SymbolFlags::PARAMETER_EXCLUDES, 0x0001_b3bf),
            (SymbolFlags::PROPERTY_EXCLUDES, 0x0000_33bb),
            (SymbolFlags::ENUM_MEMBER_EXCLUDES, 0x000d_bbff),
            (SymbolFlags::FUNCTION_EXCLUDES, 0x0001_b18f),
            (SymbolFlags::CLASS_EXCLUDES, 0x000d_b9af),
            (SymbolFlags::INTERFACE_EXCLUDES, 0x000c_0988),
            (SymbolFlags::REGULAR_ENUM_EXCLUDES, 0x000d_b8ff),
            (SymbolFlags::CONST_ENUM_EXCLUDES, 0x000d_bb7f),
            (SymbolFlags::VALUE_MODULE_EXCLUDES, 0x0001_b08f),
            (SymbolFlags::NAMESPACE_MODULE_EXCLUDES, 0x0000_0000),
            (SymbolFlags::METHOD_EXCLUDES, 0x0001_93bf),
            (SymbolFlags::GET_ACCESSOR_EXCLUDES, 0x0000_b3bb),
            (SymbolFlags::SET_ACCESSOR_EXCLUDES, 0x0001_33bb),
            (SymbolFlags::ACCESSOR_EXCLUDES, 0x0001_b3bb),
            (SymbolFlags::TYPE_PARAMETER_EXCLUDES, 0x0008_09e8),
            (SymbolFlags::TYPE_ALIAS_EXCLUDES, 0x000c_09e8),
            (SymbolFlags::ALIAS_EXCLUDES, 0x0020_0000),
            (SymbolFlags::MODULE_MEMBER, 0x0028_07f3),
            (SymbolFlags::EXPORT_HAS_LOCAL, 0x0000_03b0),
            (SymbolFlags::BLOCK_SCOPED, 0x0000_01a2),
            (SymbolFlags::PROPERTY_OR_ACCESSOR, 0x0001_8004),
            (SymbolFlags::CLASS_MEMBER, 0x0001_a004),
            (SymbolFlags::EXPORT_SUPPORTS_DEFAULT_MODIFIER, 0x0000_0070),
            (
                SymbolFlags::EXPORT_DOES_NOT_SUPPORT_DEFAULT_MODIFIER,
                0xffff_ff8f,
            ),
            (SymbolFlags::CLASSIFIABLE, 0x002c_07e0),
            (SymbolFlags::LATE_BINDING_CONTAINER, 0x0000_1870),
        ];

        for (flags, expected) in masks {
            assert_eq!(flags.bits(), expected);
        }
    }

    #[test]
    fn merge_checks_use_the_incoming_declarations_exclusion_mask() {
        assert!(can_merge(
            SymbolFlags::FUNCTION,
            SymbolFlags::FUNCTION,
            SymbolFlags::FUNCTION_EXCLUDES
        ));
        assert!(can_merge(
            SymbolFlags::INTERFACE,
            SymbolFlags::CLASS,
            SymbolFlags::CLASS_EXCLUDES
        ));
        assert!(can_merge(
            SymbolFlags::CLASS,
            SymbolFlags::INTERFACE,
            SymbolFlags::INTERFACE_EXCLUDES
        ));
        assert!(can_merge(
            SymbolFlags::GET_ACCESSOR,
            SymbolFlags::SET_ACCESSOR,
            SymbolFlags::SET_ACCESSOR_EXCLUDES
        ));
        assert!(can_merge(
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES
        ));
        assert!(!can_merge(
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            SymbolFlags::PARAMETER_EXCLUDES
        ));
        assert!(!can_merge(
            SymbolFlags::ALIAS,
            SymbolFlags::ALIAS,
            SymbolFlags::ALIAS_EXCLUDES
        ));
        assert!(!can_merge(
            SymbolFlags::REGULAR_ENUM,
            SymbolFlags::CONST_ENUM,
            SymbolFlags::CONST_ENUM_EXCLUDES
        ));
        assert!(can_merge(
            SymbolFlags::FUNCTION,
            SymbolFlags::NAMESPACE_MODULE,
            SymbolFlags::NAMESPACE_MODULE_EXCLUDES
        ));
    }

    #[test]
    fn defers_mask_permitted_merges_that_need_downstream_semantics() {
        // Upstream permits these at bind time, then relies on checker diagnostics
        // such as TS2813/TS2814 or duplicate-member checks.
        assert!(!SymbolFlags::CLASS.intersects(SymbolFlags::FUNCTION_EXCLUDES));
        assert!(!can_merge(
            SymbolFlags::CLASS,
            SymbolFlags::FUNCTION,
            SymbolFlags::FUNCTION_EXCLUDES
        ));
        assert!(!SymbolFlags::PROPERTY.intersects(SymbolFlags::PROPERTY_EXCLUDES));
        assert!(!can_merge(
            SymbolFlags::PROPERTY,
            SymbolFlags::PROPERTY,
            SymbolFlags::PROPERTY_EXCLUDES
        ));
        assert!(!SymbolFlags::PROPERTY.intersects(SymbolFlags::GET_ACCESSOR_EXCLUDES));
        assert!(!can_merge(
            SymbolFlags::PROPERTY,
            SymbolFlags::GET_ACCESSOR,
            SymbolFlags::GET_ACCESSOR_EXCLUDES
        ));

        // The current binder does not yet classify instantiated namespaces as
        // VALUE_MODULE, so applying the exclusion-free NAMESPACE_MODULE mask
        // directly would allow value/namespace merges that upstream rejects.
        assert!(!can_merge(
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            SymbolFlags::NAMESPACE_MODULE,
            SymbolFlags::NAMESPACE_MODULE_EXCLUDES
        ));
    }

    #[test]
    fn binds_representative_declaration_merges_with_upstream_exclusions() {
        let parsed = parse_source_file(
            r#"
                function overloaded(value: string): string;
                function overloaded(value: number): number;
                function overloaded(value: string | number) { return value; }
                class Shape {}
                interface Shape { value: string; }
                class Accessors {
                    get item(): string { return ""; }
                    set item(value: string) {}
                }
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let root = result.root_scope().unwrap();
        let overloaded = result
            .symbols
            .get(root.symbols.get("overloaded").unwrap())
            .unwrap();
        assert!(overloaded.flags.contains(SymbolFlags::FUNCTION));
        assert_eq!(overloaded.declarations.len(), 3);

        let shape = result
            .symbols
            .get(root.symbols.get("Shape").unwrap())
            .unwrap();
        assert!(shape.flags.contains(SymbolFlags::CLASS));
        assert!(shape.flags.contains(SymbolFlags::INTERFACE));

        let accessors = result
            .symbols
            .get(root.symbols.get("Accessors").unwrap())
            .unwrap();
        let item = result
            .symbols
            .get(accessors.members.get("item").unwrap())
            .unwrap();
        assert!(item.flags.contains(SymbolFlags::GET_ACCESSOR));
        assert!(item.flags.contains(SymbolFlags::SET_ACCESSOR));
    }

    #[test]
    fn parameter_exclusions_reject_duplicate_parameter_names() {
        let parsed = parse_source_file("function duplicate(value: string, value: number) {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
        assert_eq!(result.diagnostics[0].diagnostic.code(), 2300);
    }
    struct AstBuilder {
        arena: NodeArena,
    }

    #[test]
    fn standalone_binding_does_not_claim_program_identity() {
        let parsed = parse_source_file("const value = 1;");
        let detached = bind_source_file(&parsed.arena, parsed.source_file);
        assert_eq!(detached.file_id(), None);
        assert!(detached.is_for_source(&parsed.arena, parsed.source_file));
        assert!(
            detached
                .flow_graph(&parsed.arena, parsed.source_file)
                .is_none()
        );

        let file_id = FileId::new(7);
        let assigned = bind_source_file_in_file(&parsed.arena, parsed.source_file, file_id);
        assert_eq!(assigned.file_id(), Some(file_id));
        assert!(assigned.is_for_source(&parsed.arena, parsed.source_file));
        assert!(
            assigned
                .flow_graph(&parsed.arena, parsed.source_file)
                .is_some()
        );
        let cloned_arena = parsed.arena.clone();
        let graph = assigned
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert_eq!(
            graph.container_start(node_ref(&cloned_arena, file_id, parsed.source_file)),
            None
        );

        let other = parse_source_file("const other = 2;");
        assert!(!assigned.is_for_source(&other.arena, other.source_file));
        assert!(!assigned.is_for_source(&parsed.arena, NodeId::new(u32::MAX)));
        assert!(
            assigned
                .flow_graph(&other.arena, other.source_file)
                .is_none()
        );
    }

    #[test]
    fn builds_sequential_if_flow_with_exact_branch_order() {
        let parsed = parse_source_file(
            r"
                let value = 0;
                if (flag) { value = 1; } else { value = 2; }
                value = 3;
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(11);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let statements = source_statements(&parsed.arena, parsed.source_file);
        let [initial, conditional, final_assignment] = statements.as_slice() else {
            panic!("expected three source statements");
        };
        let source = node_ref(&parsed.arena, file, parsed.source_file);
        let start = graph.container_start(source).unwrap();
        assert_flow_flags(graph, start, FlowFlags::START);
        assert_eq!(
            graph.flow_at(node_ref(&parsed.arena, file, *initial)),
            Some(start)
        );
        let initial_flow = graph
            .flow_at(node_ref(&parsed.arena, file, *conditional))
            .unwrap();
        let initial_node = graph.nodes().get(initial_flow).unwrap();
        assert!(initial_node.flags.contains(FlowFlags::ASSIGNMENT));
        assert!(initial_node.flags.contains(FlowFlags::SHARED));
        assert!(matches!(
            &initial_node.payload,
            Some(FlowNodePayload::Ast(_))
        ));
        assert_eq!(initial_node.antecedent, Some(start));

        let NodeData::IfStatement(if_statement) = &parsed.arena.get(*conditional).unwrap().data
        else {
            panic!("expected if statement");
        };
        let NodeData::Block(then_block) =
            &parsed.arena.get(if_statement.then_statement).unwrap().data
        else {
            panic!("expected then block");
        };
        let NodeData::Block(else_block) = &parsed
            .arena
            .get(if_statement.else_statement.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected else block");
        };
        let then_statement = then_block.statements.nodes[0];
        let else_statement = else_block.statements.nodes[0];
        let then_entry = graph
            .flow_at(node_ref(&parsed.arena, file, then_statement))
            .unwrap();
        let else_entry = graph
            .flow_at(node_ref(&parsed.arena, file, else_statement))
            .unwrap();
        let then_condition = graph.nodes().get(then_entry).unwrap();
        let else_condition = graph.nodes().get(else_entry).unwrap();
        assert!(then_condition.flags.contains(FlowFlags::TRUE_CONDITION));
        assert!(else_condition.flags.contains(FlowFlags::FALSE_CONDITION));
        assert!(then_condition.flags.contains(FlowFlags::SHARED));
        assert!(else_condition.flags.contains(FlowFlags::SHARED));
        assert_eq!(then_condition.antecedent, Some(initial_flow));
        assert_eq!(else_condition.antecedent, Some(initial_flow));
        assert_eq!(
            then_condition.payload,
            Some(FlowNodePayload::Ast(node_ref(
                &parsed.arena,
                file,
                if_statement.expression,
            )))
        );
        assert_eq!(else_condition.payload, then_condition.payload);

        let post_if = graph
            .flow_at(node_ref(&parsed.arena, file, *final_assignment))
            .unwrap();
        let post_if_node = graph.nodes().get(post_if).unwrap();
        assert!(post_if_node.flags.contains(FlowFlags::BRANCH_LABEL));
        assert!(post_if_node.flags.contains(FlowFlags::REFERENCED));
        assert_eq!(post_if_node.antecedents.len(), 2);
        let then_assignment = graph.nodes().get(post_if_node.antecedents[0]).unwrap();
        let else_assignment = graph.nodes().get(post_if_node.antecedents[1]).unwrap();
        assert!(then_assignment.flags.contains(FlowFlags::ASSIGNMENT));
        assert!(else_assignment.flags.contains(FlowFlags::ASSIGNMENT));
        assert_eq!(then_assignment.antecedent, Some(then_entry));
        assert_eq!(else_assignment.antecedent, Some(else_entry));

        let end = graph.container_end(source).unwrap();
        let end_node = graph.nodes().get(end).unwrap();
        assert!(end_node.flags.contains(FlowFlags::ASSIGNMENT));
        assert_eq!(end_node.antecedent, Some(post_if));
    }

    #[test]
    fn while_flow_preserves_entry_condition_and_back_edge_order() {
        let parsed = parse_source_file("let value = 0; while (value) { value = 1; } value = 2;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(26);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let statements = source_statements(&parsed.arena, parsed.source_file);
        let [_, while_statement, final_statement] = statements.as_slice() else {
            panic!("expected initializer, while, and final assignment");
        };
        let NodeData::WhileStatement(while_data) =
            &parsed.arena.get(*while_statement).unwrap().data
        else {
            panic!("expected while statement");
        };
        let body_statement = block_statements(&parsed.arena, while_data.statement)[0];
        let while_entry = graph
            .flow_at(node_ref(&parsed.arena, file, *while_statement))
            .unwrap();
        let body_entry = graph
            .flow_at(node_ref(&parsed.arena, file, body_statement))
            .unwrap();
        let true_condition = graph.nodes().get(body_entry).unwrap();
        assert!(true_condition.flags.contains(FlowFlags::TRUE_CONDITION));
        let loop_flow = true_condition.antecedent.unwrap();
        let loop_node = graph.nodes().get(loop_flow).unwrap();
        assert!(loop_node.flags.contains(FlowFlags::LOOP_LABEL));
        assert_eq!(loop_node.antecedents.len(), 2);
        assert_eq!(loop_node.antecedents[0], while_entry);
        assert!(
            graph
                .nodes()
                .get(loop_node.antecedents[1])
                .unwrap()
                .flags
                .contains(FlowFlags::ASSIGNMENT)
        );

        let final_entry = graph
            .flow_at(node_ref(&parsed.arena, file, *final_statement))
            .unwrap();
        let false_condition = graph.nodes().get(final_entry).unwrap();
        assert!(false_condition.flags.contains(FlowFlags::FALSE_CONDITION));
        assert_eq!(false_condition.antecedent, Some(loop_flow));
    }

    #[test]
    fn do_flow_runs_the_body_before_its_condition_back_edge() {
        let parsed =
            parse_source_file("let value = 0; do { value = 1; } while (value); value = 2;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(27);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let statements = source_statements(&parsed.arena, parsed.source_file);
        let [_, do_statement, final_statement] = statements.as_slice() else {
            panic!("expected initializer, do, and final assignment");
        };
        let NodeData::DoStatement(do_data) = &parsed.arena.get(*do_statement).unwrap().data else {
            panic!("expected do statement");
        };
        let body_statement = block_statements(&parsed.arena, do_data.statement)[0];
        let loop_flow = graph
            .flow_at(node_ref(&parsed.arena, file, body_statement))
            .unwrap();
        let loop_node = graph.nodes().get(loop_flow).unwrap();
        assert!(loop_node.flags.contains(FlowFlags::LOOP_LABEL));
        assert_eq!(loop_node.antecedents.len(), 2);
        assert_eq!(
            loop_node.antecedents[0],
            graph
                .flow_at(node_ref(&parsed.arena, file, *do_statement))
                .unwrap()
        );
        let true_flow = loop_node.antecedents[1];
        let true_condition = graph.nodes().get(true_flow).unwrap();
        assert!(true_condition.flags.contains(FlowFlags::TRUE_CONDITION));

        let false_flow = graph
            .flow_at(node_ref(&parsed.arena, file, *final_statement))
            .unwrap();
        let false_condition = graph.nodes().get(false_flow).unwrap();
        assert!(false_condition.flags.contains(FlowFlags::FALSE_CONDITION));
        assert_eq!(true_condition.antecedent, false_condition.antecedent);
    }

    #[test]
    fn classic_for_without_condition_keeps_initializer_and_incrementor_edges() {
        let parsed = parse_source_file("for (let i = 0; ; i++) { if (i) break; } i;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(28);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let statements = source_statements(&parsed.arena, parsed.source_file);
        let [for_statement, final_statement] = statements.as_slice() else {
            panic!("expected for and final statements");
        };
        let NodeData::ForStatement(for_data) = &parsed.arena.get(*for_statement).unwrap().data
        else {
            panic!("expected for statement");
        };
        assert_eq!(for_data.condition, None);
        let loop_node = graph
            .nodes()
            .iter()
            .find(|flow| flow.flags.contains(FlowFlags::LOOP_LABEL))
            .unwrap();
        assert_eq!(loop_node.antecedents.len(), 2);
        for antecedent in &loop_node.antecedents {
            assert!(
                graph
                    .nodes()
                    .get(*antecedent)
                    .unwrap()
                    .flags
                    .contains(FlowFlags::ASSIGNMENT)
            );
        }
        assert_eq!(
            graph
                .nodes()
                .iter()
                .filter(|flow| flow.flags.intersects(FlowFlags::CONDITION))
                .count(),
            2
        );
        let final_flow = graph
            .flow_at(node_ref(&parsed.arena, file, *final_statement))
            .unwrap();
        assert!(
            graph
                .nodes()
                .get(final_flow)
                .unwrap()
                .flags
                .contains(FlowFlags::TRUE_CONDITION)
        );
    }

    #[test]
    fn labeled_for_continue_bypasses_the_incrementor_target() {
        let parsed = parse_source_file(
            "outer: for (let i = 0; cond; i++) { if (a) continue; if (b) continue outer; }",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(36);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let mut unlabeled_continue = None;
        let mut labeled_continue = None;
        for statement in nodes_of_kind(&parsed.arena, SyntaxKind::ContinueStatement) {
            let NodeData::ContinueStatement(data) = &parsed.arena.get(statement).unwrap().data
            else {
                unreachable!();
            };
            if data.label.is_some() {
                labeled_continue = Some(statement);
            } else {
                unlabeled_continue = Some(statement);
            }
        }
        let unlabeled_continue_flow = graph
            .flow_at(node_ref(&parsed.arena, file, unlabeled_continue.unwrap()))
            .unwrap();
        let labeled_continue_flow = graph
            .flow_at(node_ref(&parsed.arena, file, labeled_continue.unwrap()))
            .unwrap();

        let pre_loop = graph
            .nodes()
            .iter()
            .find(|flow| flow.flags.contains(FlowFlags::LOOP_LABEL))
            .unwrap();
        assert_eq!(pre_loop.antecedents.len(), 3);
        assert!(
            graph
                .nodes()
                .get(pre_loop.antecedents[0])
                .unwrap()
                .flags
                .contains(FlowFlags::ASSIGNMENT)
        );
        assert_eq!(pre_loop.antecedents[1], labeled_continue_flow);

        let incrementor_flow = pre_loop.antecedents[2];
        let incrementor = graph.nodes().get(incrementor_flow).unwrap();
        assert!(incrementor.flags.contains(FlowFlags::ASSIGNMENT));
        let pre_incrementor_flow = incrementor.antecedent.unwrap();
        let pre_incrementor = graph.nodes().get(pre_incrementor_flow).unwrap();
        assert!(pre_incrementor.flags.contains(FlowFlags::BRANCH_LABEL));
        assert_eq!(pre_incrementor.antecedents.len(), 2);
        assert_eq!(pre_incrementor.antecedents[0], unlabeled_continue_flow);
        assert!(!pre_incrementor.antecedents.contains(&labeled_continue_flow));
        assert!(!pre_loop.antecedents.contains(&unlabeled_continue_flow));
    }

    #[test]
    fn for_in_and_for_of_create_iteration_assignment_back_edges() {
        let parsed = parse_source_file(
            "let key; for (key in object) {} for (const value of values) {} key;",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(29);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let statements = source_statements(&parsed.arena, parsed.source_file);
        let [_, for_in, for_of, after] = statements.as_slice() else {
            panic!("expected declaration, for-in, for-of, and trailing statement");
        };
        let NodeData::ForInOrOfStatement(for_in_data) = &parsed.arena.get(*for_in).unwrap().data
        else {
            panic!("expected for-in statement");
        };
        let NodeData::ForInOrOfStatement(for_of_data) = &parsed.arena.get(*for_of).unwrap().data
        else {
            panic!("expected for-of statement");
        };
        let first_loop = graph
            .flow_at(node_ref(&parsed.arena, file, *for_of))
            .unwrap();
        let first_loop_node = graph.nodes().get(first_loop).unwrap();
        assert!(first_loop_node.flags.contains(FlowFlags::LOOP_LABEL));
        assert_eq!(first_loop_node.antecedents.len(), 2);
        let first_assignment = graph.nodes().get(first_loop_node.antecedents[1]).unwrap();
        assert!(first_assignment.flags.contains(FlowFlags::ASSIGNMENT));
        assert_eq!(
            first_assignment.payload,
            Some(FlowNodePayload::Ast(node_ref(
                &parsed.arena,
                file,
                for_in_data.initializer,
            )))
        );

        let second_loop = graph
            .flow_at(node_ref(&parsed.arena, file, *after))
            .unwrap();
        let second_loop_node = graph.nodes().get(second_loop).unwrap();
        assert!(second_loop_node.flags.contains(FlowFlags::LOOP_LABEL));
        assert_eq!(second_loop_node.antecedents.len(), 2);
        assert_eq!(second_loop_node.antecedents[0], first_loop);
        let NodeData::VariableDeclarationList(list) =
            &parsed.arena.get(for_of_data.initializer).unwrap().data
        else {
            panic!("expected for-of declaration list");
        };
        let declaration = list.declarations.nodes[0];
        let second_assignment = graph.nodes().get(second_loop_node.antecedents[1]).unwrap();
        assert!(second_assignment.flags.contains(FlowFlags::ASSIGNMENT));
        assert_eq!(
            second_assignment.payload,
            Some(FlowNodePayload::Ast(node_ref(
                &parsed.arena,
                file,
                declaration,
            )))
        );
    }

    #[test]
    fn for_in_assignment_expression_creates_only_the_outer_iteration_assignment() {
        let parsed = parse_source_file("for (a = 1 in b) {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(37);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let statement = source_statements(&parsed.arena, parsed.source_file)[0];
        let NodeData::ForInOrOfStatement(data) = &parsed.arena.get(statement).unwrap().data else {
            panic!("expected for-in statement");
        };
        assert_eq!(
            parsed.arena.get(data.initializer).unwrap().kind,
            SyntaxKind::BinaryExpression
        );
        let assignments = graph
            .nodes()
            .iter()
            .filter(|node| node.flags.contains(FlowFlags::ASSIGNMENT))
            .collect::<Vec<_>>();
        assert_eq!(assignments.len(), 1);
        let assignment = assignments[0];
        assert_eq!(
            assignment.flags,
            FlowFlags::ASSIGNMENT | FlowFlags::REFERENCED
        );
        assert_eq!(
            assignment.payload,
            Some(FlowNodePayload::Ast(node_ref(
                &parsed.arena,
                file,
                data.initializer,
            )))
        );

        let loop_flow = assignment.antecedent.unwrap();
        let loop_node = graph.nodes().get(loop_flow).unwrap();
        assert_eq!(
            loop_node.flags,
            FlowFlags::LOOP_LABEL | FlowFlags::REFERENCED | FlowFlags::SHARED
        );
        assert_eq!(loop_node.antecedents.len(), 2);
        assert_eq!(
            loop_node.antecedents[0],
            graph
                .container_start(node_ref(&parsed.arena, file, parsed.source_file))
                .unwrap()
        );
        assert_eq!(
            graph.nodes().get(loop_node.antecedents[1]),
            Some(assignment)
        );
    }

    #[test]
    fn for_in_binds_rhs_mutations_before_lhs_iteration_assignment() {
        let parsed = parse_source_file("let rhs, lhs; for (lhs in (rhs = 1)) {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(38);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let statement = source_statements(&parsed.arena, parsed.source_file)[1];
        let NodeData::ForInOrOfStatement(data) = &parsed.arena.get(statement).unwrap().data else {
            panic!("expected for-in statement");
        };
        let NodeData::ParenthesizedExpression(parenthesized) =
            &parsed.arena.get(data.expression).unwrap().data
        else {
            panic!("expected parenthesized right-hand side");
        };
        let NodeData::BinaryExpression(rhs) =
            &parsed.arena.get(parenthesized.expression).unwrap().data
        else {
            panic!("expected right-hand assignment");
        };

        let lhs_assignment = graph
            .nodes()
            .iter()
            .find(|node| {
                node.payload
                    == Some(FlowNodePayload::Ast(node_ref(
                        &parsed.arena,
                        file,
                        data.initializer,
                    )))
            })
            .unwrap();
        let loop_flow = lhs_assignment.antecedent.unwrap();
        let loop_node = graph.nodes().get(loop_flow).unwrap();
        assert_eq!(loop_node.antecedents.len(), 2);
        let rhs_assignment = graph.nodes().get(loop_node.antecedents[0]).unwrap();
        assert_eq!(
            rhs_assignment.payload,
            Some(FlowNodePayload::Ast(node_ref(
                &parsed.arena,
                file,
                rhs.left,
            )))
        );
        assert_eq!(
            graph.nodes().get(loop_node.antecedents[1]),
            Some(lhs_assignment)
        );
        for assignment in [rhs_assignment, lhs_assignment] {
            assert_eq!(
                assignment.flags,
                FlowFlags::ASSIGNMENT | FlowFlags::REFERENCED
            );
        }
    }

    #[test]
    fn for_await_binds_its_modifier_and_unlabeled_continue_to_the_loop_head() {
        let parsed = parse_source_file(
            "async function consume(values: any) { for await (const value of values) { continue; } }",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(30);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let for_of = nodes_of_kind(&parsed.arena, SyntaxKind::ForOfStatement)[0];
        let NodeData::ForInOrOfStatement(for_of_data) = &parsed.arena.get(for_of).unwrap().data
        else {
            panic!("expected for-await-of statement");
        };
        assert!(for_of_data.await_modifier.is_some());
        let continue_statement = nodes_of_kind(&parsed.arena, SyntaxKind::ContinueStatement)[0];
        let continue_flow = graph
            .flow_at(node_ref(&parsed.arena, file, continue_statement))
            .unwrap();
        let loop_node = graph
            .nodes()
            .iter()
            .find(|flow| flow.flags.contains(FlowFlags::LOOP_LABEL))
            .unwrap();
        assert_eq!(loop_node.antecedents.len(), 2);
        assert_eq!(loop_node.antecedents[1], continue_flow);
        assert!(
            graph
                .nodes()
                .get(continue_flow)
                .unwrap()
                .flags
                .contains(FlowFlags::ASSIGNMENT)
        );
    }

    #[test]
    fn function_and_conditional_expression_flows_are_detached_from_source_flow() {
        let parsed = parse_source_file(
            "const choose = (flag: boolean) => flag ? (flag = true) : (flag = false);",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(12);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let arrow = nodes_of_kind(&parsed.arena, SyntaxKind::ArrowFunction)[0];
        let source = node_ref(&parsed.arena, file, parsed.source_file);
        let source_start = graph.container_start(source).unwrap();
        assert_eq!(
            graph.flow_at(node_ref(&parsed.arena, file, arrow)),
            Some(source_start)
        );

        let arrow_ref = node_ref(&parsed.arena, file, arrow);
        let arrow_start = graph.container_start(arrow_ref).unwrap();
        let arrow_start_node = graph.nodes().get(arrow_start).unwrap();
        assert_eq!(
            arrow_start_node.payload,
            Some(FlowNodePayload::Ast(arrow_ref))
        );
        let arrow_end = graph.container_end(arrow_ref).unwrap();
        let arrow_end_node = graph.nodes().get(arrow_end).unwrap();
        assert!(arrow_end_node.flags.contains(FlowFlags::BRANCH_LABEL));
        assert_eq!(arrow_end_node.antecedents.len(), 2);
        for antecedent in &arrow_end_node.antecedents {
            let assignment = graph.nodes().get(*antecedent).unwrap();
            assert!(assignment.flags.contains(FlowFlags::ASSIGNMENT));
            assert!(matches!(&assignment.payload, Some(FlowNodePayload::Ast(_))));
        }

        let source_end = graph.container_end(source).unwrap();
        let source_end_node = graph.nodes().get(source_end).unwrap();
        assert!(source_end_node.flags.contains(FlowFlags::ASSIGNMENT));
        assert_eq!(source_end_node.antecedent, Some(source_start));
    }

    #[test]
    fn index_signatures_are_not_control_flow_containers() {
        let parsed =
            parse_source_file("interface Shape { [name: string]: number; method(): void; }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(18);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let index = nodes_of_kind(&parsed.arena, SyntaxKind::IndexSignature)[0];
        assert_eq!(
            graph.container_is_complete(node_ref(&parsed.arena, file, index)),
            None
        );
        let method = nodes_of_kind(&parsed.arena, SyntaxKind::MethodSignature)[0];
        assert_eq!(
            graph.container_is_complete(node_ref(&parsed.arena, file, method)),
            Some(true)
        );
    }

    #[test]
    fn object_literal_and_class_expression_members_capture_outer_flow() {
        let parsed = parse_source_file(
            r"
                const object = {
                    method() {},
                    get value() { return 1; },
                    set value(next: number) {}
                };
                const Expression = class {
                    method() {}
                    get value() { return 1; }
                    set value(next: number) {}
                };
                class Declaration {
                    method() {}
                    get value() { return 1; }
                    set value(next: number) {}
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(19);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let mut expression_members = 0;
        let mut declaration_members = 0;
        for kind in [
            SyntaxKind::MethodDeclaration,
            SyntaxKind::GetAccessor,
            SyntaxKind::SetAccessor,
        ] {
            for member in nodes_of_kind(&parsed.arena, kind) {
                let member_ref = node_ref(&parsed.arena, file, member);
                let parent_kind = parsed
                    .arena
                    .get(member)
                    .and_then(|node| node.parent)
                    .and_then(|parent| parsed.arena.get(parent))
                    .map(|parent| parent.kind);
                match parent_kind {
                    Some(SyntaxKind::ObjectLiteralExpression | SyntaxKind::ClassExpression) => {
                        expression_members += 1;
                        assert!(graph.flow_at(member_ref).is_some());
                        let start = graph.container_start(member_ref).unwrap();
                        assert_eq!(
                            graph.nodes().get(start).unwrap().payload,
                            Some(FlowNodePayload::Ast(member_ref))
                        );
                    }
                    Some(SyntaxKind::ClassDeclaration) => {
                        declaration_members += 1;
                        assert_eq!(graph.flow_at(member_ref), None);
                        let start = graph.container_start(member_ref).unwrap();
                        assert_eq!(graph.nodes().get(start).unwrap().payload, None);
                    }
                    other => panic!("unexpected member parent: {other:?}"),
                }
            }
        }
        assert_eq!(expression_members, 6);
        assert_eq!(declaration_members, 3);
    }

    #[test]
    fn qualified_names_capture_flow_only_inside_type_queries() {
        let parsed = parse_source_file(
            "declare const value: typeof ns.deep.member; declare const other: ns.deep.Member;",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(20);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let mut in_query = 0;
        let mut outside_query = 0;
        for qualified in nodes_of_kind(&parsed.arena, SyntaxKind::QualifiedName) {
            let mut ancestor = qualified;
            let part_of_query = loop {
                let Some(parent) = parsed.arena.get(ancestor).and_then(|node| node.parent) else {
                    break false;
                };
                match parsed.arena.get(parent).map(|node| node.kind) {
                    Some(SyntaxKind::QualifiedName | SyntaxKind::Identifier) => ancestor = parent,
                    Some(SyntaxKind::TypeQuery) => break true,
                    _ => break false,
                }
            };
            let flow = graph.flow_at(node_ref(&parsed.arena, file, qualified));
            if part_of_query {
                in_query += 1;
                assert!(flow.is_some());
            } else {
                outside_query += 1;
                assert_eq!(flow, None);
            }
        }
        assert!(in_query > 0);
        assert!(outside_query > 0);
    }

    #[test]
    fn comma_expression_calls_follow_upstream_assertion_order() {
        let parsed = parse_source_file("checks.first(value), checks.second(value);");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(16);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let calls = nodes_of_kind(&parsed.arena, SyntaxKind::CallExpression);
        let [first_call, second_call] = calls.as_slice() else {
            panic!("expected two calls");
        };
        let source = node_ref(&parsed.arena, file, parsed.source_file);
        let start = graph.container_start(source).unwrap();
        let second_flow = graph.container_end(source).unwrap();
        let second = graph.nodes().get(second_flow).unwrap();
        assert!(second.flags.contains(FlowFlags::CALL));
        assert_eq!(
            second.payload,
            Some(FlowNodePayload::Ast(node_ref(
                &parsed.arena,
                file,
                *second_call,
            )))
        );
        let first_flow = second.antecedent.unwrap();
        let first = graph.nodes().get(first_flow).unwrap();
        assert!(first.flags.contains(FlowFlags::CALL));
        assert_eq!(first.antecedent, Some(start));
        assert_eq!(
            first.payload,
            Some(FlowNodePayload::Ast(node_ref(
                &parsed.arena,
                file,
                *first_call,
            )))
        );
    }

    #[test]
    fn nested_function_effects_preserve_upstream_conditional_join() {
        let parsed = parse_source_file(
            "const result = flag ? ((value: number) => { value = 1; }) : ((value: number) => { value = 2; });",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(17);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        // The pinned binder does not save/restore hasFlowEffects around a
        // control-flow container. Preserve that observable allocation choice.
        let source = node_ref(&parsed.arena, file, parsed.source_file);
        let declaration_assignment = graph.container_end(source).unwrap();
        let conditional_join = graph
            .nodes()
            .get(declaration_assignment)
            .unwrap()
            .antecedent
            .unwrap();
        let join = graph.nodes().get(conditional_join).unwrap();
        assert!(join.flags.contains(FlowFlags::BRANCH_LABEL));
        assert_eq!(join.antecedents.len(), 2);
    }

    #[test]
    fn nested_conditions_preserve_unreachable_function_tails() {
        let parsed = parse_source_file(
            r"
                function decide(outer: boolean, inner: boolean) {
                    if (outer) {
                        if (inner) return 1;
                        throw 2;
                    }
                    return 3;
                    const never = 4;
                    const unreachableArrow = () => 5;
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(13);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let function = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionDeclaration)[0];
        let function_ref = node_ref(&parsed.arena, file, function);
        assert!(graph.container_start(function_ref).is_some());
        assert_eq!(graph.container_end(function_ref), None);

        let condition_count = graph
            .nodes()
            .iter()
            .filter(|node| node.flags.intersects(FlowFlags::CONDITION))
            .count();
        assert_eq!(condition_count, 4);

        let never = nodes_of_kind(&parsed.arena, SyntaxKind::VariableStatement)[0];
        let never_ref = node_ref(&parsed.arena, file, never);
        assert_eq!(graph.is_unreachable(never_ref), Some(true));
        assert_eq!(graph.flow_at(never_ref), None);
        let arrow = nodes_of_kind(&parsed.arena, SyntaxKind::ArrowFunction)[0];
        let arrow_ref = node_ref(&parsed.arena, file, arrow);
        assert_eq!(graph.flow_at(arrow_ref), Some(graph.nodes().unreachable()));
        assert!(graph.container_start(arrow_ref).is_some());
        for statement in nodes_of_kind(&parsed.arena, SyntaxKind::ReturnStatement)
            .into_iter()
            .chain(nodes_of_kind(&parsed.arena, SyntaxKind::ThrowStatement))
        {
            assert!(
                graph
                    .flow_at(node_ref(&parsed.arena, file, statement))
                    .is_some()
            );
        }
    }

    #[test]
    fn unreachable_traversal_marks_only_potentially_executable_nodes() {
        let parsed = parse_source_file(
            r"
                function stop() {
                    return;
                    {
                        var dormant;
                        var initialized = 1;
                        let lexical;
                        class Local {}
                        enum Choice { One }
                        namespace Nested {}
                    }
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(21);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let function = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionDeclaration)[0];
        let NodeData::FunctionDeclaration(function_data) =
            &parsed.arena.get(function).unwrap().data
        else {
            panic!("expected function declaration");
        };
        let NodeData::Block(body) = &parsed.arena.get(function_data.body.unwrap()).unwrap().data
        else {
            panic!("expected function body");
        };
        let nested_block = body.statements.nodes[1];
        assert_eq!(
            graph.is_unreachable(node_ref(&parsed.arena, file, nested_block)),
            None
        );

        let NodeData::Block(nested) = &parsed.arena.get(nested_block).unwrap().data else {
            panic!("expected nested block");
        };
        let [dormant, initialized, lexical, class, enum_, module] =
            nested.statements.nodes.as_slice()
        else {
            panic!("expected six unreachable statements");
        };
        assert_eq!(
            graph.is_unreachable(node_ref(&parsed.arena, file, *dormant)),
            None
        );
        for executable in [initialized, lexical, class, enum_, module] {
            assert_eq!(
                graph.is_unreachable(node_ref(&parsed.arena, file, *executable)),
                Some(true)
            );
        }
    }

    #[test]
    fn unreachable_synthetic_variables_use_combined_statement_and_list_flags() {
        let mut builder = AstBuilder::new();
        let return_statement = builder.return_statement();
        let (statement_flag_let, _) =
            builder.variable_statement("statementFlagLet", NodeFlags::default());
        builder.arena.get_mut(statement_flag_let).unwrap().flags = NodeFlags(1);
        let (dormant_var, _) = builder.variable_statement("dormantVar", NodeFlags::default());

        let NodeData::VariableStatement(statement) =
            &builder.arena.get(statement_flag_let).unwrap().data
        else {
            panic!("expected variable statement");
        };
        assert_eq!(
            builder.arena.get(statement.declaration_list).unwrap().flags,
            NodeFlags::default()
        );

        let body = builder.block(&[return_statement, statement_flag_let, dormant_var]);
        let function = builder.function("stop", body);
        let source = builder.source_file(vec![function]);
        let file = FileId::new(25);
        let result = bind_source_file_in_file(&builder.arena, source, file);
        let graph = result.flow_graph(&builder.arena, source).unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        assert_eq!(
            graph.is_unreachable(node_ref(&builder.arena, file, statement_flag_let)),
            Some(true)
        );
        assert_eq!(
            graph.is_unreachable(node_ref(&builder.arena, file, dormant_var)),
            None
        );
    }

    #[test]
    fn nested_labeled_jumps_select_distinct_break_and_continue_targets() {
        let parsed = parse_source_file(
            r"
                outer: for (;;) {
                    inner: while (flag) {
                        if (skip) continue outer;
                        if (done) break inner;
                        break outer;
                    }
                }
                after;
                unused: { after; }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(31);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let outer_label = label_named(&parsed.arena, "outer");
        let inner_label = label_named(&parsed.arena, "inner");
        let unused_label = label_named(&parsed.arena, "unused");
        assert_eq!(
            graph.is_unreachable(node_ref(&parsed.arena, file, outer_label)),
            Some(false)
        );
        assert_eq!(
            graph.is_unreachable(node_ref(&parsed.arena, file, inner_label)),
            Some(false)
        );
        assert_eq!(
            graph.is_unreachable(node_ref(&parsed.arena, file, unused_label)),
            Some(true)
        );

        let continue_statement = nodes_of_kind(&parsed.arena, SyntaxKind::ContinueStatement)[0];
        let continue_flow = graph
            .flow_at(node_ref(&parsed.arena, file, continue_statement))
            .unwrap();
        let mut inner_break = None;
        let mut outer_break = None;
        for statement in nodes_of_kind(&parsed.arena, SyntaxKind::BreakStatement) {
            let NodeData::BreakStatement(data) = &parsed.arena.get(statement).unwrap().data else {
                unreachable!();
            };
            let label = data.label.unwrap();
            let name = match &parsed.arena.get(label).unwrap().data {
                NodeData::Identifier(identifier) => identifier.text.as_str(),
                _ => panic!("expected jump label"),
            };
            match name {
                "inner" => inner_break = Some(statement),
                "outer" => outer_break = Some(statement),
                _ => panic!("unexpected jump label"),
            }
        }
        let inner_break_flow = graph
            .flow_at(node_ref(&parsed.arena, file, inner_break.unwrap()))
            .unwrap();
        let outer_break_flow = graph
            .flow_at(node_ref(&parsed.arena, file, outer_break.unwrap()))
            .unwrap();
        let continue_target = branch_target_index(graph, continue_flow);
        let inner_break_target = branch_target_index(graph, inner_break_flow);
        let outer_break_target = branch_target_index(graph, outer_break_flow);
        assert_ne!(continue_target, inner_break_target);
        assert_ne!(continue_target, outer_break_target);
        assert_ne!(inner_break_target, outer_break_target);
        assert_eq!(
            graph
                .nodes()
                .iter()
                .nth(inner_break_target)
                .unwrap()
                .antecedents
                .len(),
            2
        );
        assert_eq!(
            graph
                .nodes()
                .iter()
                .nth(outer_break_target)
                .unwrap()
                .antecedents,
            vec![outer_break_flow]
        );
        let after = source_statements(&parsed.arena, parsed.source_file)[1];
        assert_eq!(
            graph.flow_at(node_ref(&parsed.arena, file, after)),
            Some(outer_break_flow)
        );
    }

    #[test]
    fn unknown_jump_labels_do_not_capture_the_current_loop_targets() {
        let parsed = parse_source_file(
            "while (flag) { break missing; continue absent; afterInvalidJumps; }",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(32);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let break_statement = nodes_of_kind(&parsed.arena, SyntaxKind::BreakStatement)[0];
        let continue_statement = nodes_of_kind(&parsed.arena, SyntaxKind::ContinueStatement)[0];
        let expression_statement = nodes_of_kind(&parsed.arena, SyntaxKind::ExpressionStatement)[0];
        let break_flow = graph
            .flow_at(node_ref(&parsed.arena, file, break_statement))
            .unwrap();
        assert_eq!(
            graph.flow_at(node_ref(&parsed.arena, file, continue_statement)),
            Some(break_flow)
        );
        assert_eq!(
            graph.flow_at(node_ref(&parsed.arena, file, expression_statement)),
            Some(break_flow)
        );
    }

    #[test]
    fn continue_to_a_non_iteration_label_leaves_current_flow_unchanged() {
        let parsed = parse_source_file("block: { continue block; afterContinue; } afterLabel;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(39);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let continue_statement = nodes_of_kind(&parsed.arena, SyntaxKind::ContinueStatement)[0];
        let expressions = nodes_of_kind(&parsed.arena, SyntaxKind::ExpressionStatement);
        let continue_flow = graph
            .flow_at(node_ref(&parsed.arena, file, continue_statement))
            .unwrap();
        for expression in expressions {
            assert_eq!(
                graph.flow_at(node_ref(&parsed.arena, file, expression)),
                Some(continue_flow)
            );
        }
        let label = label_named(&parsed.arena, "block");
        assert_eq!(
            graph.is_unreachable(node_ref(&parsed.arena, file, label)),
            Some(false)
        );
    }

    #[test]
    fn unlabeled_while_and_do_continues_leave_their_loop_tails_unreachable() {
        let parsed = parse_source_file(
            r"
                function tails(flag: boolean) {
                    while (flag) { continue; const afterWhile = 1; }
                    do { continue; const afterDo = 2; } while (flag);
                    const reachable = 3;
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(33);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let variables = nodes_of_kind(&parsed.arena, SyntaxKind::VariableStatement);
        let [after_while, after_do, reachable] = variables.as_slice() else {
            panic!("expected two loop tails and one reachable declaration");
        };
        for unreachable in [after_while, after_do] {
            assert_eq!(
                graph.is_unreachable(node_ref(&parsed.arena, file, *unreachable)),
                Some(true)
            );
        }
        assert_eq!(
            graph.is_unreachable(node_ref(&parsed.arena, file, *reachable)),
            Some(false)
        );

        let continue_statements = nodes_of_kind(&parsed.arena, SyntaxKind::ContinueStatement);
        let while_continue_flow = graph
            .flow_at(node_ref(&parsed.arena, file, continue_statements[0]))
            .unwrap();
        assert!(graph.nodes().iter().any(|node| {
            node.flags.contains(FlowFlags::LOOP_LABEL)
                && node.antecedents.contains(&while_continue_flow)
        }));
        let do_statement = nodes_of_kind(&parsed.arena, SyntaxKind::DoStatement)[0];
        let NodeData::DoStatement(do_data) = &parsed.arena.get(do_statement).unwrap().data else {
            unreachable!();
        };
        let do_continue_flow = graph
            .flow_at(node_ref(&parsed.arena, file, continue_statements[1]))
            .unwrap();
        assert!(graph.nodes().iter().any(|node| {
            node.flags.contains(FlowFlags::TRUE_CONDITION)
                && node.antecedent == Some(do_continue_flow)
                && node.payload
                    == Some(FlowNodePayload::Ast(node_ref(
                        &parsed.arena,
                        file,
                        do_data.expression,
                    )))
        }));
    }

    #[test]
    fn detached_function_jumps_cannot_capture_outer_labels_or_loop_targets() {
        let parsed = parse_source_file(
            r"
                outer: while (flag) {
                    function detached() {
                        break outer;
                        afterInvalidBreak;
                    }
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(34);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let labeled = nodes_of_kind(&parsed.arena, SyntaxKind::LabeledStatement)[0];
        let NodeData::LabeledStatement(label_data) = &parsed.arena.get(labeled).unwrap().data
        else {
            unreachable!();
        };
        assert_eq!(
            graph.is_unreachable(node_ref(&parsed.arena, file, label_data.label)),
            Some(true)
        );
        let function = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionDeclaration)[0];
        assert_eq!(
            graph.container_is_complete(node_ref(&parsed.arena, file, function)),
            Some(true)
        );
        let after_invalid_break = nodes_of_kind(&parsed.arena, SyntaxKind::ExpressionStatement)[0];
        let break_statement = nodes_of_kind(&parsed.arena, SyntaxKind::BreakStatement)[0];
        assert_eq!(
            graph.flow_at(node_ref(&parsed.arena, file, after_invalid_break)),
            graph.flow_at(node_ref(&parsed.arena, file, break_statement))
        );
        assert!(
            graph
                .flow_at(node_ref(&parsed.arena, file, after_invalid_break))
                .is_some()
        );
    }

    #[test]
    fn for_await_of_destructuring_invalidates_only_its_flow_container() {
        let parsed = parse_source_file(
            r"
                async function consume(entries: any) {
                    for await (const [key, value] of entries) {}
                }
                const after = 1;
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(35);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(!graph.is_complete());

        let function = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionDeclaration)[0];
        let function_ref = node_ref(&parsed.arena, file, function);
        let source_ref = node_ref(&parsed.arena, file, parsed.source_file);
        assert_eq!(graph.container_is_complete(function_ref), Some(false));
        assert_eq!(graph.container_is_complete(source_ref), Some(true));
        assert_eq!(graph.unsupported().len(), 1);
        assert_eq!(
            graph.unsupported()[0].kind,
            UnsupportedFlowKind::DestructuringAssignment
        );
        assert_eq!(graph.unsupported()[0].container, function_ref);
        let after = source_statements(&parsed.arena, parsed.source_file)[1];
        assert!(
            graph
                .flow_at(node_ref(&parsed.arena, file, after))
                .is_some()
        );
    }

    #[test]
    fn direct_for_of_destructuring_fails_closed_at_the_initializer() {
        let parsed = parse_source_file("for ([value] of values) { body; } after;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(40);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();

        let for_of = nodes_of_kind(&parsed.arena, SyntaxKind::ForOfStatement)[0];
        let NodeData::ForInOrOfStatement(data) = &parsed.arena.get(for_of).unwrap().data else {
            panic!("expected for-of statement");
        };
        let source = node_ref(&parsed.arena, file, parsed.source_file);
        assert!(!graph.is_complete());
        assert_eq!(graph.container_is_complete(source), Some(false));
        assert_eq!(graph.unsupported().len(), 1);
        assert_eq!(
            graph.unsupported()[0],
            super::UnsupportedFlow {
                node: node_ref(&parsed.arena, file, data.initializer),
                container: source,
                kind: UnsupportedFlowKind::DestructuringAssignment,
            }
        );
    }

    #[test]
    fn switch_groups_consecutive_empty_clauses_into_exact_ranges() {
        let parsed =
            parse_source_file("switch (true) { case 0: case 1: case 2: hit = 1; default: } after;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(41);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let switch_statement = source_statements(&parsed.arena, parsed.source_file)[0];
        let switch_ref = node_ref(&parsed.arena, file, switch_statement);
        assert_eq!(
            switch_clause_ranges(graph),
            vec![(switch_ref, 0, 3), (switch_ref, 3, 4)]
        );
        let clauses = switch_clauses(&parsed.arena, switch_statement);
        assert_eq!(clauses.len(), 4);
        assert_eq!(
            graph.fallthrough_flow_at(node_ref(&parsed.arena, file, clauses[0])),
            None
        );
        assert_eq!(
            graph.fallthrough_flow_at(node_ref(&parsed.arena, file, clauses[1])),
            None
        );
        let fallthrough = graph
            .fallthrough_flow_at(node_ref(&parsed.arena, file, clauses[2]))
            .unwrap();
        assert!(
            graph
                .nodes()
                .get(fallthrough)
                .unwrap()
                .flags
                .contains(FlowFlags::ASSIGNMENT)
        );
        assert_eq!(
            graph.fallthrough_flow_at(node_ref(&parsed.arena, file, clauses[3])),
            None
        );
    }

    #[test]
    fn switch_without_default_adds_the_empty_no_match_edge_last() {
        let parsed = parse_source_file("switch (subject) { case 0: break; } after;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(42);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let statements = source_statements(&parsed.arena, parsed.source_file);
        let switch_statement = statements[0];
        let break_statement = clause_statements(
            &parsed.arena,
            switch_clauses(&parsed.arena, switch_statement)[0],
        )[0];
        let break_flow = graph
            .flow_at(node_ref(&parsed.arena, file, break_statement))
            .unwrap();
        let post_switch_flow = graph
            .flow_at(node_ref(&parsed.arena, file, statements[1]))
            .unwrap();
        let post_switch = graph.nodes().get(post_switch_flow).unwrap();
        assert_eq!(post_switch.flags, FlowFlags::BRANCH_LABEL);
        assert_eq!(post_switch.antecedents[0], break_flow);
        let no_match_flow = post_switch.antecedents[1];
        let no_match = graph.nodes().get(no_match_flow).unwrap();
        assert_eq!(
            no_match.flags,
            FlowFlags::SWITCH_CLAUSE | FlowFlags::REFERENCED
        );
        assert_eq!(
            no_match.payload,
            Some(FlowNodePayload::SwitchClause {
                switch_statement: node_ref(&parsed.arena, file, switch_statement),
                clause_start: 0,
                clause_end: 0,
            })
        );
        assert_eq!(
            no_match.antecedent,
            graph.flow_at(node_ref(&parsed.arena, file, switch_statement))
        );
    }

    #[test]
    fn switch_with_default_has_only_clause_break_edges() {
        let parsed =
            parse_source_file("switch (subject) { case 0: break; default: break; } after;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(43);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let statements = source_statements(&parsed.arena, parsed.source_file);
        let switch_statement = statements[0];
        let switch_ref = node_ref(&parsed.arena, file, switch_statement);
        assert_eq!(
            switch_clause_ranges(graph),
            vec![(switch_ref, 0, 1), (switch_ref, 1, 2)]
        );
        let break_flows = switch_clauses(&parsed.arena, switch_statement)
            .into_iter()
            .map(|clause| clause_statements(&parsed.arena, clause)[0])
            .map(|statement| {
                graph
                    .flow_at(node_ref(&parsed.arena, file, statement))
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let post_switch_flow = graph
            .flow_at(node_ref(&parsed.arena, file, statements[1]))
            .unwrap();
        let post_switch = graph.nodes().get(post_switch_flow).unwrap();
        assert_eq!(post_switch.flags, FlowFlags::BRANCH_LABEL);
        assert_eq!(post_switch.antecedents, break_flows);
        assert!(!graph.nodes().iter().any(|node| {
            node.payload
                .as_ref()
                .is_some_and(FlowNodePayload::is_empty_switch_clause)
        }));
    }

    #[test]
    fn non_narrowing_switch_with_default_emits_no_clause_flow_nodes() {
        let parsed =
            parse_source_file("switch (0) { case 0: first = 1; default: last = 1; } after;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(44);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        assert!(switch_clause_ranges(graph).is_empty());
        assert!(
            graph
                .nodes()
                .iter()
                .all(|node| !node.flags.contains(FlowFlags::SWITCH_CLAUSE))
        );
        let switch_statement = source_statements(&parsed.arena, parsed.source_file)[0];
        let clauses = switch_clauses(&parsed.arena, switch_statement);
        let first_fallthrough = graph
            .fallthrough_flow_at(node_ref(&parsed.arena, file, clauses[0]))
            .unwrap();
        assert!(
            graph
                .nodes()
                .get(first_fallthrough)
                .unwrap()
                .flags
                .contains(FlowFlags::ASSIGNMENT)
        );
        assert_eq!(
            graph.fallthrough_flow_at(node_ref(&parsed.arena, file, clauses[1])),
            None
        );
    }

    #[test]
    fn switch_fallthrough_and_break_edges_preserve_statement_order() {
        let parsed = parse_source_file(
            "switch (subject) { case 0: first = 1; case 1: break; default: last = 1; } after;",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(45);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let statements = source_statements(&parsed.arena, parsed.source_file);
        let switch_statement = statements[0];
        let clauses = switch_clauses(&parsed.arena, switch_statement);
        let first_fallthrough = graph
            .fallthrough_flow_at(node_ref(&parsed.arena, file, clauses[0]))
            .unwrap();
        let break_statement = clause_statements(&parsed.arena, clauses[1])[0];
        let break_flow = graph
            .flow_at(node_ref(&parsed.arena, file, break_statement))
            .unwrap();
        let pre_second_case = graph.nodes().get(break_flow).unwrap();
        assert_eq!(
            pre_second_case.flags,
            FlowFlags::BRANCH_LABEL | FlowFlags::REFERENCED
        );
        assert_eq!(pre_second_case.antecedents[1], first_fallthrough);
        assert_eq!(
            graph
                .nodes()
                .get(pre_second_case.antecedents[0])
                .unwrap()
                .payload,
            Some(FlowNodePayload::SwitchClause {
                switch_statement: node_ref(&parsed.arena, file, switch_statement),
                clause_start: 1,
                clause_end: 2,
            })
        );

        let post_switch_flow = graph
            .flow_at(node_ref(&parsed.arena, file, statements[1]))
            .unwrap();
        let post_switch = graph.nodes().get(post_switch_flow).unwrap();
        assert_eq!(post_switch.flags, FlowFlags::BRANCH_LABEL);
        assert_eq!(post_switch.antecedents[0], break_flow);
        assert!(
            graph
                .nodes()
                .get(post_switch.antecedents[1])
                .unwrap()
                .flags
                .contains(FlowFlags::ASSIGNMENT)
        );
        assert_eq!(
            graph.fallthrough_flow_at(node_ref(&parsed.arena, file, clauses[1])),
            None
        );
        assert_eq!(
            graph.fallthrough_flow_at(node_ref(&parsed.arena, file, clauses[2])),
            None
        );
    }

    #[test]
    fn nested_switches_restore_break_and_case_expression_targets() {
        let parsed = parse_source_file(
            r"
                switch (outer) {
                    case 0:
                        switch (inner) { default: break; }
                        tail = 1;
                        break;
                    case (probe = 1):
                        break;
                }
                after;
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(46);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let outer_switch = source_statements(&parsed.arena, parsed.source_file)[0];
        let inner_switch = nodes_of_kind(&parsed.arena, SyntaxKind::SwitchStatement)
            .into_iter()
            .find(|statement| *statement != outer_switch)
            .unwrap();
        let mut inner_break_flow = None;
        let mut outer_break_flows = Vec::new();
        for statement in nodes_of_kind(&parsed.arena, SyntaxKind::BreakStatement) {
            let flow = graph
                .flow_at(node_ref(&parsed.arena, file, statement))
                .unwrap();
            if nearest_ancestor_of_kind(&parsed.arena, statement, SyntaxKind::SwitchStatement)
                == inner_switch
            {
                inner_break_flow = Some(flow);
            } else {
                outer_break_flows.push(flow);
            }
        }
        let inner_target = branch_target_index(graph, inner_break_flow.unwrap());
        assert_eq!(outer_break_flows.len(), 2);
        let outer_target = branch_target_index(graph, outer_break_flows[0]);
        assert_eq!(
            branch_target_index(graph, outer_break_flows[1]),
            outer_target
        );
        assert_ne!(inner_target, outer_target);

        let probe = nodes_of_kind(&parsed.arena, SyntaxKind::Identifier)
            .into_iter()
            .find(|identifier| {
                matches!(
                    &parsed.arena.get(*identifier).unwrap().data,
                    NodeData::Identifier(data) if data.text == "probe"
                )
            })
            .unwrap();
        let probe_assignment = graph
            .nodes()
            .iter()
            .find(|node| {
                node.payload == Some(FlowNodePayload::Ast(node_ref(&parsed.arena, file, probe)))
            })
            .unwrap();
        let outer_entry = graph
            .flow_at(node_ref(&parsed.arena, file, outer_switch))
            .unwrap();
        let inner_entry = graph
            .flow_at(node_ref(&parsed.arena, file, inner_switch))
            .unwrap();
        assert_eq!(probe_assignment.antecedent, Some(outer_entry));
        assert_ne!(probe_assignment.antecedent, Some(inner_entry));
    }

    #[test]
    fn recovered_switch_at_eof_retains_clause_and_no_match_ranges() {
        let parsed = parse_source_file("switch (true) { case 1:");
        assert!(!parsed.diagnostics.is_empty());
        let file = FileId::new(47);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let switch_statement = source_statements(&parsed.arena, parsed.source_file)[0];
        let switch_ref = node_ref(&parsed.arena, file, switch_statement);
        assert_eq!(
            switch_clause_ranges(graph),
            vec![(switch_ref, 0, 1), (switch_ref, 0, 0)]
        );
        let clauses = switch_clauses(&parsed.arena, switch_statement);
        assert_eq!(clauses.len(), 1);
        assert!(clause_statements(&parsed.arena, clauses[0]).is_empty());
    }

    #[test]
    fn no_default_switch_restores_reachability_after_all_cases_return() {
        let parsed = parse_source_file(
            "function choose(subject: number) { switch (subject) { case 0: return 0; } after; }",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(48);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let after = nodes_of_kind(&parsed.arena, SyntaxKind::ExpressionStatement)[0];
        let after_flow = graph.flow_at(node_ref(&parsed.arena, file, after)).unwrap();
        let no_match = graph.nodes().get(after_flow).unwrap();
        assert_eq!(
            no_match.flags,
            FlowFlags::SWITCH_CLAUSE | FlowFlags::REFERENCED
        );
        assert!(
            no_match
                .payload
                .as_ref()
                .is_some_and(FlowNodePayload::is_empty_switch_clause)
        );
        assert_eq!(
            graph.is_unreachable(node_ref(&parsed.arena, file, after)),
            Some(false)
        );
    }

    #[test]
    fn default_switch_post_flow_can_come_only_from_a_conditional_break() {
        let parsed = parse_source_file(
            r"
                function choose(subject: number, stop: boolean) {
                    switch (subject) {
                        default:
                            if (stop) break;
                            return 1;
                    }
                    after;
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(49);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let break_statement = nodes_of_kind(&parsed.arena, SyntaxKind::BreakStatement)[0];
        let break_flow = graph
            .flow_at(node_ref(&parsed.arena, file, break_statement))
            .unwrap();
        let after = nodes_of_kind(&parsed.arena, SyntaxKind::ExpressionStatement)[0];
        assert_eq!(
            graph.flow_at(node_ref(&parsed.arena, file, after)),
            Some(break_flow)
        );
        assert!(
            graph
                .nodes()
                .get(break_flow)
                .unwrap()
                .flags
                .contains(FlowFlags::TRUE_CONDITION)
        );
        assert!(!graph.nodes().iter().any(|node| {
            node.payload
                .as_ref()
                .is_some_and(FlowNodePayload::is_empty_switch_clause)
        }));
    }

    #[test]
    fn terminating_case_does_not_prevent_later_case_binding() {
        let parsed = parse_source_file(
            r"
                function choose(subject: number) {
                    switch (subject) {
                        case 0: return;
                        case 1: selected = 1;
                    }
                    after;
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(50);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let switch_statement = nodes_of_kind(&parsed.arena, SyntaxKind::SwitchStatement)[0];
        let clauses = switch_clauses(&parsed.arena, switch_statement);
        let selected = clause_statements(&parsed.arena, clauses[1])[0];
        let selected_flow = graph
            .flow_at(node_ref(&parsed.arena, file, selected))
            .unwrap();
        let selected_entry = graph.nodes().get(selected_flow).unwrap();
        assert_eq!(
            selected_entry.payload,
            Some(FlowNodePayload::SwitchClause {
                switch_statement: node_ref(&parsed.arena, file, switch_statement),
                clause_start: 1,
                clause_end: 2,
            })
        );
        assert_eq!(
            graph.is_unreachable(node_ref(&parsed.arena, file, selected)),
            Some(false)
        );
    }

    #[test]
    fn terminating_detached_case_expression_restores_selected_clause_flow() {
        let parsed = parse_source_file(
            r"
                switch (subject) {
                    case (() => { return 1; }): selected = 1;
                    default:
                }
                after;
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(51);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let switch_statement = source_statements(&parsed.arena, parsed.source_file)[0];
        let selected = clause_statements(
            &parsed.arena,
            switch_clauses(&parsed.arena, switch_statement)[0],
        )[0];
        let selected_flow = graph
            .flow_at(node_ref(&parsed.arena, file, selected))
            .unwrap();
        assert_eq!(
            graph.nodes().get(selected_flow).unwrap().payload,
            Some(FlowNodePayload::SwitchClause {
                switch_statement: node_ref(&parsed.arena, file, switch_statement),
                clause_start: 0,
                clause_end: 1,
            })
        );
        let arrow = nodes_of_kind(&parsed.arena, SyntaxKind::ArrowFunction)[0];
        assert_eq!(
            graph.container_is_complete(node_ref(&parsed.arena, file, arrow)),
            Some(true)
        );
    }

    #[test]
    fn unsupported_switch_clause_fails_closed_but_discovers_later_containers() {
        let parsed = parse_source_file(
            r"
                function broken(value: number) {
                    switch (value) {
                        case 0: try { work; } finally {}
                        default: function nested() { return; }
                    }
                }
                const after = 1;
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(52);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(!graph.is_complete());

        let functions = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionDeclaration);
        let outer = functions
            .iter()
            .copied()
            .find(|function| {
                parsed.arena.get(*function).unwrap().parent == Some(parsed.source_file)
            })
            .unwrap();
        let nested = functions
            .into_iter()
            .find(|function| *function != outer)
            .unwrap();
        let source = node_ref(&parsed.arena, file, parsed.source_file);
        assert_eq!(
            graph.container_is_complete(node_ref(&parsed.arena, file, outer)),
            Some(false)
        );
        assert_eq!(
            graph.container_is_complete(node_ref(&parsed.arena, file, nested)),
            Some(true)
        );
        assert_eq!(graph.container_is_complete(source), Some(true));
        assert_eq!(graph.unsupported().len(), 1);
        assert_eq!(
            graph.unsupported()[0].kind,
            UnsupportedFlowKind::TryStatement
        );
        assert_eq!(
            graph.unsupported()[0].container,
            node_ref(&parsed.arena, file, outer)
        );
        let after = source_statements(&parsed.arena, parsed.source_file)[1];
        assert!(
            graph
                .flow_at(node_ref(&parsed.arena, file, after))
                .is_some()
        );
    }

    #[test]
    fn case_statements_allocate_detached_function_flow_in_source_order() {
        let parsed = parse_source_file(
            r"
                switch (subject) {
                    default:
                        before = 1;
                        function detached() { inside = 1; }
                        after = 1;
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(53);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let switch_statement = source_statements(&parsed.arena, parsed.source_file)[0];
        let statements = clause_statements(
            &parsed.arena,
            switch_clauses(&parsed.arena, switch_statement)[0],
        );
        let assignment_left = |statement| {
            let NodeData::ExpressionStatement(expression) =
                &parsed.arena.get(statement).unwrap().data
            else {
                panic!("expected expression statement");
            };
            let NodeData::BinaryExpression(assignment) =
                &parsed.arena.get(expression.expression).unwrap().data
            else {
                panic!("expected assignment");
            };
            assignment.left
        };
        let before = assignment_left(statements[0]);
        let detached = statements[1];
        let after = assignment_left(statements[2]);

        let source_end = graph
            .container_end(node_ref(&parsed.arena, file, parsed.source_file))
            .unwrap();
        let after_flow = graph.nodes().get(source_end).unwrap();
        assert_eq!(
            after_flow.payload,
            Some(FlowNodePayload::Ast(node_ref(&parsed.arena, file, after)))
        );
        let before_flow_ref = after_flow.antecedent.unwrap();
        assert_eq!(
            graph.nodes().get(before_flow_ref).unwrap().payload,
            Some(FlowNodePayload::Ast(node_ref(&parsed.arena, file, before)))
        );
        let detached_start = graph
            .container_start(node_ref(&parsed.arena, file, detached))
            .unwrap();
        assert!(before_flow_ref.flow.0 < detached_start.flow.0);
        assert!(detached_start.flow.0 < source_end.flow.0);
    }

    #[test]
    fn unsupported_nested_effects_invalidate_an_enclosing_conditional() {
        let parsed = parse_source_file(
            "const result = flag ? (() => { try { value = 1; } finally {} }) : 0;",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(22);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(!graph.is_complete());

        let source_ref = node_ref(&parsed.arena, file, parsed.source_file);
        let arrow = nodes_of_kind(&parsed.arena, SyntaxKind::ArrowFunction)[0];
        let arrow_ref = node_ref(&parsed.arena, file, arrow);
        assert_eq!(graph.container_is_complete(source_ref), Some(false));
        assert_eq!(graph.container_is_complete(arrow_ref), Some(false));
        assert!(graph.unsupported().iter().any(|unsupported| {
            unsupported.container == arrow_ref
                && unsupported.kind == UnsupportedFlowKind::TryStatement
        }));
        assert!(graph.unsupported().iter().any(|unsupported| {
            unsupported.container == source_ref
                && unsupported.kind == UnsupportedFlowKind::CrossContainerFlowEffects
        }));
    }

    #[test]
    fn unreachable_direct_functions_and_static_blocks_remain_explicit_boundaries() {
        let parsed = parse_source_file(
            r"
                function stop() {
                    return;
                    (() => 1)();
                    (async () => 2)();
                    (function* () { yield 3; })();
                    class Local { static { sideEffect(); } }
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(23);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(!graph.is_complete());

        let function = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionDeclaration)[0];
        let function_ref = node_ref(&parsed.arena, file, function);
        let source_ref = node_ref(&parsed.arena, file, parsed.source_file);
        assert_eq!(graph.container_is_complete(function_ref), Some(false));
        assert_eq!(graph.container_is_complete(source_ref), Some(true));
        let kinds = graph
            .unsupported()
            .iter()
            .filter(|unsupported| unsupported.container == function_ref)
            .map(|unsupported| unsupported.kind)
            .collect::<Vec<_>>();
        assert_eq!(
            kinds
                .iter()
                .filter(|kind| **kind == UnsupportedFlowKind::ImmediatelyInvokedFunction)
                .count(),
            1
        );
        assert_eq!(
            kinds
                .iter()
                .filter(|kind| **kind == UnsupportedFlowKind::DirectFunctionCall)
                .count(),
            2
        );
        assert_eq!(
            kinds
                .iter()
                .filter(|kind| **kind == UnsupportedFlowKind::ClassStaticBlock)
                .count(),
            1
        );
    }

    #[test]
    fn assignment_references_use_left_hand_side_expression_kinds() {
        let parsed = parse_source_file("if ((get() = value).property) { value; }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(24);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());

        let conditions = graph
            .nodes()
            .iter()
            .filter(|node| node.flags.intersects(FlowFlags::CONDITION))
            .collect::<Vec<_>>();
        assert_eq!(conditions.len(), 2);
        let condition = nodes_of_kind(&parsed.arena, SyntaxKind::PropertyAccessExpression)[0];
        assert!(conditions.iter().all(|flow| {
            flow.payload
                == Some(FlowNodePayload::Ast(node_ref(
                    &parsed.arena,
                    file,
                    condition,
                )))
        }));
    }

    #[test]
    fn unsupported_flow_invalidates_only_its_affected_container() {
        let parsed = parse_source_file(
            r"
                function iterate(value: number) {
                    try { value = 0; } finally {}
                    value = 1;
                }
                const after = 1;
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(14);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .unwrap();
        assert!(!graph.is_complete());

        let function = nodes_of_kind(&parsed.arena, SyntaxKind::FunctionDeclaration)[0];
        let function_ref = node_ref(&parsed.arena, file, function);
        let source_ref = node_ref(&parsed.arena, file, parsed.source_file);
        assert_eq!(graph.container_is_complete(function_ref), Some(false));
        assert_eq!(graph.container_start(function_ref), None);
        assert_eq!(graph.container_is_complete(source_ref), Some(true));

        let after = source_statements(&parsed.arena, parsed.source_file)[1];
        assert!(
            graph
                .flow_at(node_ref(&parsed.arena, file, after))
                .is_some()
        );
        assert_eq!(graph.unsupported().len(), 1);
        assert_eq!(
            graph.unsupported()[0].kind,
            UnsupportedFlowKind::TryStatement
        );
        assert_eq!(graph.unsupported()[0].container, function_ref);

        let top_level = parse_source_file("try { flag; } finally {} const after = 1;");
        let top_result =
            bind_source_file_in_file(&top_level.arena, top_level.source_file, FileId::new(15));
        let top_graph = top_result
            .flow_graph(&top_level.arena, top_level.source_file)
            .unwrap();
        let top_source = node_ref(&top_level.arena, FileId::new(15), top_level.source_file);
        assert_eq!(top_graph.container_is_complete(top_source), Some(false));
        assert_eq!(top_graph.container_start(top_source), None);
        let after = source_statements(&top_level.arena, top_level.source_file)[1];
        assert_eq!(
            top_graph.flow_at(node_ref(&top_level.arena, FileId::new(15), after)),
            None
        );
    }

    #[test]
    #[should_panic(expected = "binder source file must be a valid SourceFile node in its arena")]
    fn binding_rejects_invalid_source_file_ids() {
        let arena = NodeArena::new();
        let _ = bind_source_file(&arena, NodeId::new(u32::MAX));
    }

    impl AstBuilder {
        fn new() -> Self {
            Self {
                arena: NodeArena::new(),
            }
        }

        fn alloc(
            &mut self,
            kind: SyntaxKind,
            flags: NodeFlags,
            data: NodeData,
            children: &[NodeId],
        ) -> NodeId {
            let id = self.arena.alloc(Node {
                kind,
                flags,
                range: TextRange::default(),
                parent: None,
                data,
            });
            for child in children {
                self.arena.get_mut(*child).unwrap().parent = Some(id);
            }
            id
        }

        fn identifier(&mut self, text: &str) -> NodeId {
            self.alloc(
                SyntaxKind::Identifier,
                NodeFlags::default(),
                NodeData::Identifier(Box::new(IdentifierData {
                    flow_node: None,
                    text: text.to_owned(),
                })),
                &[],
            )
        }

        fn variable_statement(&mut self, name: &str, flags: NodeFlags) -> (NodeId, NodeId) {
            let name = self.identifier(name);
            let declaration = self.alloc(
                SyntaxKind::VariableDeclaration,
                NodeFlags::default(),
                NodeData::VariableDeclaration(Box::new(VariableDeclarationData {
                    exclamation_token: None,
                    initializer: None,
                    local_symbol: None,
                    symbol: None,
                    type_: None,
                    facts: 0,
                    name,
                })),
                &[name],
            );
            let list = self.alloc(
                SyntaxKind::VariableDeclarationList,
                flags,
                NodeData::VariableDeclarationList(Box::new(VariableDeclarationListData {
                    declarations: NodeList {
                        range: TextRange::default(),
                        nodes: vec![declaration],
                        has_trailing_comma: false,
                    },
                    facts: 0,
                })),
                &[declaration],
            );
            let statement = self.alloc(
                SyntaxKind::VariableStatement,
                NodeFlags::default(),
                NodeData::VariableStatement(Box::new(VariableStatementData {
                    declaration_list: list,
                    flow_node: None,
                    facts: 0,
                    modifiers: None,
                })),
                &[list],
            );
            (statement, declaration)
        }

        fn return_statement(&mut self) -> NodeId {
            self.alloc(
                SyntaxKind::ReturnStatement,
                NodeFlags::default(),
                NodeData::ReturnStatement(Box::new(ReturnStatementData {
                    expression: None,
                    flow_node: None,
                    facts: 0,
                })),
                &[],
            )
        }

        fn block(&mut self, statements: &[NodeId]) -> NodeId {
            self.alloc(
                SyntaxKind::Block,
                NodeFlags::default(),
                NodeData::Block(Box::new(BlockData {
                    flow_node: None,
                    locals: AstSymbolTable,
                    multi_line: false,
                    next_container: None,
                    statements: NodeList {
                        range: TextRange::default(),
                        nodes: statements.to_owned(),
                        has_trailing_comma: false,
                    },
                    facts: 0,
                })),
                statements,
            )
        }

        fn function(&mut self, name: &str, body: NodeId) -> NodeId {
            let name = self.identifier(name);
            self.alloc(
                SyntaxKind::FunctionDeclaration,
                NodeFlags::default(),
                NodeData::FunctionDeclaration(Box::new(FunctionDeclarationData {
                    asterisk_token: None,
                    body: Some(body),
                    end_flow_node: None,
                    flow_node: None,
                    full_signature: None,
                    local_symbol: None,
                    locals: AstSymbolTable,
                    next_container: None,
                    parameters: NodeList::default(),
                    return_flow_node: None,
                    symbol: None,
                    type_: None,
                    type_parameters: None,
                    facts: 0,
                    modifiers: None,
                    name: Some(name),
                })),
                &[name, body],
            )
        }

        fn class(&mut self, name: &str) -> NodeId {
            let name = self.identifier(name);
            self.alloc(
                SyntaxKind::ClassDeclaration,
                NodeFlags::default(),
                NodeData::ClassDeclaration(Box::new(ClassDeclarationData {
                    flow_node: None,
                    heritage_clauses: None,
                    local_symbol: None,
                    locals: AstSymbolTable,
                    members: NodeList::default(),
                    next_container: None,
                    symbol: None,
                    type_parameters: None,
                    facts: 0,
                    modifiers: None,
                    name: Some(name),
                })),
                &[name],
            )
        }

        fn interface(&mut self, name: &str) -> NodeId {
            let name = self.identifier(name);
            self.alloc(
                SyntaxKind::InterfaceDeclaration,
                NodeFlags::default(),
                NodeData::InterfaceDeclaration(Box::new(InterfaceDeclarationData {
                    flow_node: None,
                    heritage_clauses: None,
                    local_symbol: None,
                    members: NodeList::default(),
                    symbol: None,
                    type_parameters: None,
                    modifiers: None,
                    name,
                })),
                &[name],
            )
        }

        fn type_alias(&mut self, name: &str) -> NodeId {
            let name = self.identifier(name);
            let type_node = self.identifier("string");
            self.alloc(
                SyntaxKind::TypeAliasDeclaration,
                NodeFlags::default(),
                NodeData::TypeAliasDeclaration(Box::new(TypeAliasDeclarationData {
                    flow_node: None,
                    local_symbol: None,
                    locals: AstSymbolTable,
                    next_container: None,
                    symbol: None,
                    type_: type_node,
                    type_parameters: None,
                    modifiers: None,
                    name,
                })),
                &[name, type_node],
            )
        }

        fn enum_declaration(&mut self, name: &str, member: &str) -> (NodeId, NodeId) {
            let member_name = self.identifier(member);
            let member = self.alloc(
                SyntaxKind::EnumMember,
                NodeFlags::default(),
                NodeData::EnumMember(Box::new(EnumMemberData {
                    initializer: None,
                    postfix_token: None,
                    symbol: None,
                    facts: 0,
                    modifiers: None,
                    name: member_name,
                })),
                &[member_name],
            );
            let name = self.identifier(name);
            let declaration = self.alloc(
                SyntaxKind::EnumDeclaration,
                NodeFlags::default(),
                NodeData::EnumDeclaration(Box::new(EnumDeclarationData {
                    flow_node: None,
                    local_symbol: None,
                    members: NodeList {
                        range: TextRange::default(),
                        nodes: vec![member],
                        has_trailing_comma: false,
                    },
                    symbol: None,
                    facts: 0,
                    modifiers: None,
                    name,
                })),
                &[name, member],
            );
            (declaration, member)
        }

        fn source_file(&mut self, statements: Vec<NodeId>) -> NodeId {
            let eof = self.alloc(
                SyntaxKind::EndOfFile,
                NodeFlags::default(),
                NodeData::Token(Box::new(TokenData)),
                &[],
            );
            let mut children = statements.clone();
            children.push(eof);
            self.alloc(
                SyntaxKind::SourceFile,
                NodeFlags::default(),
                NodeData::SourceFile(Box::new(SourceFileData {
                    end_of_file_token: eof,
                    locals: AstSymbolTable,
                    next_container: None,
                    statements: NodeList {
                        range: TextRange::default(),
                        nodes: statements,
                        has_trailing_comma: false,
                    },
                    symbol: None,
                    facts: 0,
                })),
                &children,
            )
        }
    }

    #[test]
    fn binds_var_and_block_scoped_declarations_with_stable_ids() {
        let mut builder = AstBuilder::new();
        let (first_var, first_var_decl) = builder.variable_statement("value", NodeFlags::default());
        let (second_var, _) = builder.variable_statement("value", NodeFlags::default());
        let (first_let, first_let_decl) = builder.variable_statement("value", NodeFlags(1));
        let (second_let, second_let_decl) = builder.variable_statement("value", NodeFlags(1));
        let block = builder.block(&[first_let, second_let]);
        let source = builder.source_file(vec![first_var, second_var, block]);

        let result = bind_source_file(&builder.arena, source);
        let root = result.root_scope().unwrap();
        let root_value = root.symbols.get("value").unwrap();
        assert_eq!(root_value.0, 0);
        assert_eq!(
            result.symbols.get(root_value).unwrap().declarations.len(),
            2
        );

        let block_scope = result
            .scopes
            .iter()
            .find(|scope| scope.owner == block)
            .unwrap();
        assert_eq!(block_scope.kind, ScopeKind::Block);
        let block_value = block_scope.symbols.get("value").unwrap();
        assert_eq!(block_value.0, 1);
        assert_eq!(result.symbols.len(), 2);
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].node, second_let_decl);
        assert_eq!(result.diagnostics[0].diagnostic.code(), 2451);
        assert_eq!(
            result.diagnostics[0].diagnostic.render().unwrap(),
            "Cannot redeclare block-scoped variable 'value'."
        );
        assert_eq!(result.containers[&first_let_decl], block);
        assert_eq!(result.node_symbols[&first_var_decl], root_value);
    }

    #[test]
    fn binds_named_declaration_kinds_and_enum_members() {
        let mut builder = AstBuilder::new();
        let (local_statement, local_declaration) =
            builder.variable_statement("local", NodeFlags::default());
        let function_body = builder.block(&[local_statement]);
        let function = builder.function("run", function_body);
        let class = builder.class("Model");
        let first_interface = builder.interface("Shape");
        let second_interface = builder.interface("Shape");
        let alias = builder.type_alias("Name");
        let (enum_declaration, enum_member) = builder.enum_declaration("Color", "Red");
        let source = builder.source_file(vec![
            function,
            class,
            first_interface,
            second_interface,
            alias,
            enum_declaration,
        ]);

        let result = bind_source_file(&builder.arena, source);
        assert!(result.diagnostics.is_empty());
        let root = result.root_scope().unwrap();
        assert_eq!(root.symbols.len(), 5);
        assert!(
            result
                .symbols
                .get(root.symbols.get("run").unwrap())
                .unwrap()
                .flags
                .contains(SymbolFlags::FUNCTION)
        );
        assert!(
            result
                .symbols
                .get(root.symbols.get("Model").unwrap())
                .unwrap()
                .flags
                .contains(SymbolFlags::CLASS)
        );
        let shape = result
            .symbols
            .get(root.symbols.get("Shape").unwrap())
            .unwrap();
        assert!(shape.flags.contains(SymbolFlags::INTERFACE));
        assert_eq!(shape.declarations.len(), 2);
        assert!(
            result
                .symbols
                .get(root.symbols.get("Name").unwrap())
                .unwrap()
                .flags
                .contains(SymbolFlags::TYPE_ALIAS)
        );

        let color_id = root.symbols.get("Color").unwrap();
        let color = result.symbols.get(color_id).unwrap();
        assert!(color.flags.contains(SymbolFlags::REGULAR_ENUM));
        let red_id = color.members.get("Red").unwrap();
        let red = result.symbols.get(red_id).unwrap();
        assert_eq!(red.parent, Some(color_id));
        assert!(red.flags.contains(SymbolFlags::ENUM_MEMBER));
        assert_eq!(result.node_symbols[&enum_member], red_id);

        let function_scope = result
            .scopes
            .iter()
            .find(|scope| scope.owner == function)
            .unwrap();
        let local_id = function_scope.symbols.get("local").unwrap();
        assert_eq!(result.node_symbols[&local_declaration], local_id);
        assert_eq!(
            result.symbols.get(local_id).unwrap().parent,
            Some(root.symbols.get("run").unwrap())
        );
    }

    #[test]
    fn binds_literal_and_computed_enum_member_names() {
        let parsed = parse_source_file(
            r#"enum Names { Identifier, "quoted", 2, ["computed"] = 3, [4] = 4 }"#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let root = result.root_scope().unwrap();
        let names = result
            .symbols
            .get(root.symbols.get("Names").unwrap())
            .unwrap();
        assert_eq!(
            names
                .members
                .iter()
                .map(|(name, _)| name)
                .collect::<Vec<_>>(),
            ["2", "4", "Identifier", "computed", "quoted"]
        );

        let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
        else {
            panic!("expected source file");
        };
        let NodeData::EnumDeclaration(enumeration) =
            &parsed.arena.get(source.statements.nodes[0]).unwrap().data
        else {
            panic!("expected enum declaration");
        };
        for member in &enumeration.members.nodes {
            let NodeData::EnumMember(member_data) = &parsed.arena.get(*member).unwrap().data else {
                panic!("expected enum member");
            };
            assert!(result.node_symbols.contains_key(member));
            assert!(result.node_symbols.contains_key(&member_data.name));
            if let NodeData::ComputedPropertyName(computed) =
                &parsed.arena.get(member_data.name).unwrap().data
            {
                assert_eq!(
                    result.containers.get(&computed.expression),
                    Some(&parsed.source_file)
                );
            }
        }
    }

    #[test]
    fn computed_class_names_resolve_in_the_enclosing_scope() {
        let parsed = parse_source_file(
            "const key = Symbol(), value = 12; export class Foo { [key] = value; }",
        );
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        let key_declaration = parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::VariableDeclaration(declaration) = &node.data else {
                    return None;
                };
                matches!(
                    parsed.arena.get(declaration.name).map(|name| &name.data),
                    Some(NodeData::Identifier(name)) if name.text == "key"
                )
                .then_some(declaration.name)
            })
            .unwrap();
        let computed_name = parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::PropertyDeclaration(property) = &node.data else {
                    return None;
                };
                matches!(
                    parsed.arena.get(property.name).map(|name| &name.data),
                    Some(NodeData::ComputedPropertyName(_))
                )
                .then_some(property.name)
            })
            .unwrap();
        let NodeData::ComputedPropertyName(computed) =
            &parsed.arena.get(computed_name).unwrap().data
        else {
            unreachable!();
        };
        let computed_expression = computed.expression;
        assert_eq!(
            result.root_scope().unwrap().symbols.get("key"),
            result.node_symbols.get(&key_declaration).copied()
        );
        assert_eq!(
            result.containers.get(&computed_expression),
            Some(&parsed.source_file)
        );
        assert_eq!(
            result.node_scopes.get(&parsed.source_file).copied(),
            result.root_scope().map(|scope| scope.id)
        );
        assert_eq!(
            result.resolve_name_at(computed_expression, "key"),
            result.node_symbols.get(&key_declaration).copied()
        );
    }

    #[test]
    fn reports_incompatible_duplicate_declarations() {
        let mut builder = AstBuilder::new();
        let class = builder.class("Conflict");
        let alias = builder.type_alias("Conflict");
        let source = builder.source_file(vec![class, alias]);

        let result = bind_source_file(&builder.arena, source);
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].node, alias);
        assert_eq!(result.diagnostics[0].diagnostic.code(), 2300);
        assert_eq!(
            result.diagnostics[0].diagnostic.render().unwrap(),
            "Duplicate identifier 'Conflict'."
        );
    }

    #[test]
    fn isolates_type_literal_and_signature_type_scopes() {
        let parsed = parse_source_file(concat!(
            "declare let first: { value: string; call<T>(input: T): T }; ",
            "declare let second: { value: number; call<T>(input: T): T }; ",
            "declare let generic: <T>(input: T) => T; ",
            "declare let other: <T>(input: T) => T;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    }

    #[test]
    fn binds_parsed_import_and_export_aliases() {
        let parsed = parse_source_file(
            r#"
                import DefaultThing, { source as local, same } from "pkg";
                const value = 1;
                export { value as renamed };
                export default function make<T>(input: T): T { return input; }
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let root = result.root_scope().unwrap();
        for name in ["DefaultThing", "local", "same"] {
            let symbol = result.symbols.get(root.symbols.get(name).unwrap()).unwrap();
            assert!(symbol.flags.contains(SymbolFlags::ALIAS));
            assert!(symbol.target.is_none());
        }
        let value = root.symbols.get("value").unwrap();
        let renamed = result
            .symbols
            .get(result.exports.get("renamed").unwrap())
            .unwrap();
        assert!(renamed.flags.contains(SymbolFlags::ALIAS));
        assert_eq!(renamed.target, Some(value));

        let make = root.symbols.get("make").unwrap();
        assert_eq!(result.exports.get("default"), Some(make));
        let function_scope = result
            .scopes
            .iter()
            .find(|scope| scope.kind == ScopeKind::Function && scope.symbols.get("input").is_some())
            .unwrap();
        assert!(
            result
                .symbols
                .get(function_scope.symbols.get("T").unwrap())
                .unwrap()
                .flags
                .contains(SymbolFlags::TYPE_PARAMETER)
        );
    }

    #[test]
    fn merges_import_aliases_with_type_declarations_in_either_order() {
        for source in [
            r#"export default interface Shape {} import Shape from "pkg";"#,
            r#"interface Shape {} import Shape from "pkg";"#,
            r#"import Shape from "pkg"; interface Shape {}"#,
            r#"type Shape = {}; import Shape from "pkg";"#,
            r#"import Shape from "pkg"; type Shape = {};"#,
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let result = bind_source_file(&parsed.arena, parsed.source_file);
            assert!(
                result.diagnostics.is_empty(),
                "{source}: {:?}",
                result.diagnostics
            );
            let root = result.root_scope().unwrap();
            let symbol_id = root.symbols.get("Shape").unwrap();
            let symbol = result.symbols.get(symbol_id).unwrap();
            assert!(symbol.flags.contains(SymbolFlags::ALIAS), "{source}");
            assert!(
                symbol
                    .flags
                    .intersects(SymbolFlags::INTERFACE | SymbolFlags::TYPE_ALIAS),
                "{source}"
            );
            assert_eq!(symbol.declarations.len(), 2, "{source}");
            if source.starts_with("export default") {
                assert_eq!(result.exports.get("default"), Some(symbol_id));
            }
        }
    }

    #[test]
    fn does_not_merge_two_import_aliases() {
        let parsed = parse_source_file(r#"import Shape from "first"; import Shape from "second";"#);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].diagnostic.code(), 2300);
    }

    #[test]
    fn binds_parsed_modules_and_class_interface_members() {
        let parsed = parse_source_file(
            r"
                namespace Outer {
                    export function run() {}
                    function hidden() {}
                }
                namespace Outer { export function second() {} }
                class Model<T> {
                    value: T;
                    read(input: T): T { return input; }
                }
                interface Shape {
                    width: number;
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let root = result.root_scope().unwrap();
        let outer_id = root.symbols.get("Outer").unwrap();
        let outer = result.symbols.get(outer_id).unwrap();
        assert!(outer.flags.contains(SymbolFlags::NAMESPACE_MODULE));
        assert_eq!(outer.declarations.len(), 2);
        assert!(outer.members.get("run").is_some());
        assert!(outer.members.get("second").is_some());
        assert!(outer.members.get("hidden").is_none());

        let model = result
            .symbols
            .get(root.symbols.get("Model").unwrap())
            .unwrap();
        assert!(
            result
                .symbols
                .get(model.members.get("value").unwrap())
                .unwrap()
                .flags
                .contains(SymbolFlags::PROPERTY)
        );
        let method_id = model.members.get("read").unwrap();
        assert!(
            result
                .symbols
                .get(method_id)
                .unwrap()
                .flags
                .contains(SymbolFlags::METHOD)
        );
        let method_scope = result
            .scopes
            .iter()
            .find(|scope| scope.kind == ScopeKind::Function && scope.symbols.get("input").is_some())
            .unwrap();
        assert_eq!(
            result
                .symbols
                .get(method_scope.symbols.get("input").unwrap())
                .unwrap()
                .parent,
            Some(method_id)
        );

        let shape = result
            .symbols
            .get(root.symbols.get("Shape").unwrap())
            .unwrap();
        assert!(shape.members.get("width").is_some());
        assert!(
            result
                .scopes
                .iter()
                .any(|scope| scope.kind == ScopeKind::Module)
        );
    }

    #[test]
    fn keeps_function_scoped_variables_inside_namespace_scopes() {
        let parsed = parse_source_file(
            r"
                namespace m1 {
                    export var m1 = 10;
                    var local = m1;
                }
                var value = m1.m1;
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let root = result.root_scope().unwrap();
        let namespace_id = root.symbols.get("m1").unwrap();
        let namespace = result.symbols.get(namespace_id).unwrap();
        let exported_id = namespace.members.get("m1").unwrap();
        assert_ne!(namespace_id, exported_id);

        let module_scope = result
            .scopes
            .iter()
            .find(|scope| scope.kind == ScopeKind::Module)
            .unwrap();
        assert_eq!(module_scope.symbols.get("m1"), Some(exported_id));
        assert!(module_scope.symbols.get("local").is_some());
        assert!(root.symbols.get("local").is_none());
    }

    #[test]
    fn binds_namespace_exports_and_ambient_export_contexts() {
        let parsed = parse_source_file(
            r"
                namespace Ordinary {
                    const hidden = 0;
                    function hiddenFunction() {}
                    export const visible = 1;
                    export function visibleFunction() {}
                }
                declare namespace Ambient {
                    namespace Nested {
                        function func(): number;
                        const value: string;
                    }
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let root = result.root_scope().unwrap();

        let ordinary = result
            .symbols
            .get(root.symbols.get("Ordinary").unwrap())
            .unwrap();
        assert!(ordinary.members.get("visible").is_some());
        assert!(ordinary.members.get("visibleFunction").is_some());
        assert!(ordinary.members.get("hidden").is_none());
        assert!(ordinary.members.get("hiddenFunction").is_none());

        let ambient = result
            .symbols
            .get(root.symbols.get("Ambient").unwrap())
            .unwrap();
        let nested = result
            .symbols
            .get(ambient.members.get("Nested").unwrap())
            .unwrap();
        assert!(nested.members.get("func").is_some());
        assert!(nested.members.get("value").is_some());
    }

    #[test]
    fn binds_dotted_ambient_namespaces_as_nested_exports() {
        let parsed =
            parse_source_file("declare namespace Foo.Bar { export var foo; }; Foo.Bar.foo = 5;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let root = result.root_scope().unwrap();

        let foo_id = root.symbols.get("Foo").unwrap();
        let foo = result.symbols.get(foo_id).unwrap();
        assert!(foo.flags.contains(SymbolFlags::NAMESPACE_MODULE));
        let bar_id = foo.members.get("Bar").unwrap();
        let bar = result.symbols.get(bar_id).unwrap();
        assert!(bar.flags.contains(SymbolFlags::NAMESPACE_MODULE));
        assert_eq!(bar.parent, Some(foo_id));
        let value_id = bar.members.get("foo").unwrap();
        let value = result.symbols.get(value_id).unwrap();
        assert_eq!(value.parent, Some(bar_id));

        let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
        else {
            panic!("expected source file");
        };
        assert_eq!(source.statements.nodes.len(), 3);
        let outer_id = source.statements.nodes[0];
        let NodeData::ModuleDeclaration(outer) = &parsed.arena.get(outer_id).unwrap().data else {
            panic!("expected outer namespace");
        };
        let inner_id = outer.body.unwrap();
        assert_eq!(result.node_symbols.get(&outer_id), Some(&foo_id));
        assert_eq!(result.node_symbols.get(&inner_id), Some(&bar_id));
    }

    #[test]
    fn binds_non_ambient_dotted_namespaces_as_nested_exports() {
        let parsed = parse_source_file(
            "namespace Root.Middle.Leaf { export const value = 1; }",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let root_scope = result.root_scope().unwrap();

        let root_id = root_scope.symbols.get("Root").unwrap();
        let root = result.symbols.get(root_id).unwrap();
        let middle_id = root.members.get("Middle").unwrap();
        let middle = result.symbols.get(middle_id).unwrap();
        assert_eq!(middle.parent, Some(root_id));
        let leaf_id = middle.members.get("Leaf").unwrap();
        let leaf = result.symbols.get(leaf_id).unwrap();
        assert_eq!(leaf.parent, Some(middle_id));
        let value_id = leaf.members.get("value").unwrap();
        assert_eq!(result.symbols.get(value_id).unwrap().parent, Some(leaf_id));
    }

    #[test]
    fn merges_functions_classes_and_enums_with_namespaces() {
        let parsed = parse_source_file(
            r#"
                function Factory() {}
                namespace Factory { export const version = 1; }
                class Model {}
                namespace Model { export const kind = "model"; }
                enum Color { Red }
                namespace Color { export const label = "red"; }
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let root = result.root_scope().unwrap();
        for (name, declaration_flag, member) in [
            ("Factory", SymbolFlags::FUNCTION, "version"),
            ("Model", SymbolFlags::CLASS, "kind"),
            ("Color", SymbolFlags::REGULAR_ENUM, "label"),
        ] {
            let symbol = result.symbols.get(root.symbols.get(name).unwrap()).unwrap();
            assert!(symbol.flags.contains(declaration_flag));
            assert!(symbol.flags.contains(SymbolFlags::NAMESPACE_MODULE));
            assert!(symbol.members.get(member).is_some());
        }
    }

    #[test]
    fn binds_and_merges_const_enums_with_namespaces() {
        let parsed = parse_source_file(
            r"
                export declare const enum Status { Ready }
                export declare const enum Status { Done }
                export declare namespace Status { const label: string; }
                enum Ordinary { Value }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let root = result.root_scope().unwrap();

        let status = result
            .symbols
            .get(root.symbols.get("Status").unwrap())
            .unwrap();
        assert!(status.flags.contains(SymbolFlags::CONST_ENUM));
        assert!(!status.flags.contains(SymbolFlags::REGULAR_ENUM));
        assert!(status.flags.contains(SymbolFlags::NAMESPACE_MODULE));
        assert_eq!(status.declarations.len(), 3);
        assert!(status.members.get("label").is_some());

        let ordinary = result
            .symbols
            .get(root.symbols.get("Ordinary").unwrap())
            .unwrap();
        assert!(ordinary.flags.contains(SymbolFlags::REGULAR_ENUM));
        assert!(!ordinary.flags.contains(SymbolFlags::CONST_ENUM));
    }

    #[test]
    fn exports_import_equals_and_resolves_qualified_references() {
        let parsed = parse_source_file(
            r#"
                import { alias } from "foo";
                export import cls2 = alias.Class;
                namespace M {
                    export import cls = alias.Class;
                    let value = cls;
                }
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let root = result.root_scope().unwrap();
        let alias = root.symbols.get("alias").unwrap();
        let cls2 = root.symbols.get("cls2").unwrap();
        assert_eq!(result.exports.get("cls2"), Some(cls2));

        let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
        else {
            panic!("expected source file");
        };
        let NodeData::ImportEqualsDeclaration(top_alias) =
            &parsed.arena.get(source.statements.nodes[1]).unwrap().data
        else {
            panic!("expected top-level import-equals declaration");
        };
        let NodeData::QualifiedName(top_reference) =
            &parsed.arena.get(top_alias.module_reference).unwrap().data
        else {
            panic!("expected qualified module reference");
        };
        assert_eq!(
            result.resolve_name_at(top_reference.left, "alias"),
            Some(alias)
        );

        let NodeData::ModuleDeclaration(module) =
            &parsed.arena.get(source.statements.nodes[2]).unwrap().data
        else {
            panic!("expected namespace");
        };
        let module_symbol = result.symbols.get(root.symbols.get("M").unwrap()).unwrap();
        let namespace_alias = module_symbol.members.get("cls").unwrap();
        let NodeData::ModuleBlock(block) = &parsed.arena.get(module.body.unwrap()).unwrap().data
        else {
            panic!("expected namespace block");
        };
        let NodeData::ImportEqualsDeclaration(nested_alias) =
            &parsed.arena.get(block.statements.nodes[0]).unwrap().data
        else {
            panic!("expected namespace import-equals declaration");
        };
        let NodeData::QualifiedName(nested_reference) = &parsed
            .arena
            .get(nested_alias.module_reference)
            .unwrap()
            .data
        else {
            panic!("expected qualified namespace module reference");
        };
        assert_eq!(
            result.resolve_name_at(nested_reference.left, "alias"),
            Some(alias)
        );
        let NodeData::VariableStatement(statement) =
            &parsed.arena.get(block.statements.nodes[1]).unwrap().data
        else {
            panic!("expected namespace variable");
        };
        let NodeData::VariableDeclarationList(list) =
            &parsed.arena.get(statement.declaration_list).unwrap().data
        else {
            panic!("expected declaration list");
        };
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(list.declarations.nodes[0]).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let initializer = variable.initializer.unwrap();
        assert_eq!(
            result.resolve_name_at(initializer, "cls"),
            Some(namespace_alias)
        );
    }

    #[test]
    fn binds_named_class_expression_in_its_own_scope() {
        let parsed =
            parse_source_file("const value = class Inner { static self = Inner; }; Inner;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert_eq!(result.root_scope().unwrap().symbols.get("Inner"), None);

        let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
        else {
            panic!("expected source file");
        };
        let NodeData::VariableStatement(statement) =
            &parsed.arena.get(source.statements.nodes[0]).unwrap().data
        else {
            panic!("expected variable statement");
        };
        let NodeData::VariableDeclarationList(list) =
            &parsed.arena.get(statement.declaration_list).unwrap().data
        else {
            panic!("expected declaration list");
        };
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(list.declarations.nodes[0]).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let class_id = variable.initializer.unwrap();
        let NodeData::ClassExpression(class) = &parsed.arena.get(class_id).unwrap().data else {
            panic!("expected class expression");
        };
        let class_symbol = result.node_symbols[&class_id];
        assert_eq!(
            result.node_symbols.get(&class.name.unwrap()),
            Some(&class_symbol)
        );
        let NodeData::PropertyDeclaration(property) =
            &parsed.arena.get(class.members.nodes[0]).unwrap().data
        else {
            panic!("expected property declaration");
        };
        let self_reference = property.initializer.unwrap();
        assert_eq!(
            result.resolve_name_at(self_reference, "Inner"),
            Some(class_symbol)
        );
        let outside_reference = source.statements.nodes[1];
        let NodeData::ExpressionStatement(outside) =
            &parsed.arena.get(outside_reference).unwrap().data
        else {
            panic!("expected expression statement");
        };
        assert_eq!(result.resolve_name_at(outside.expression, "Inner"), None);
    }

    #[test]
    fn rejects_mixed_regular_and_const_enum_merges() {
        let parsed = parse_source_file("enum Mixed { A } const enum Mixed { B }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert_eq!(result.diagnostics.len(), 2);
        assert!(
            result
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() == 2567)
        );
        assert_eq!(
            result.diagnostics[0].diagnostic.render().unwrap(),
            "Enum declarations can only merge with namespace or other enum declarations."
        );
    }

    #[test]
    fn reports_enum_merge_diagnostics_for_each_incompatible_declaration() {
        let parsed = parse_source_file(
            r"
                const enum ConstFirst { A }
                class ConstFirst {}
                class ClassFirst {}
                const enum ClassFirst { A }
                const enum MixedFirst { A }
                enum MixedFirst { B }
                enum RegularFirst { A }
                const enum RegularFirst { B }
                declare const enum Legal { A }
                declare const enum Legal { B }
                declare namespace Legal { const label: string; }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert_eq!(result.diagnostics.len(), 8, "{:?}", result.diagnostics);
        assert!(
            result
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() == 2567)
        );
        let root = result.root_scope().unwrap();
        let legal = result
            .symbols
            .get(root.symbols.get("Legal").unwrap())
            .unwrap();
        assert!(legal.flags.contains(SymbolFlags::CONST_ENUM));
        assert!(legal.flags.contains(SymbolFlags::NAMESPACE_MODULE));
        assert_eq!(legal.declarations.len(), 3);
    }

    #[test]
    fn binds_modified_arrow_parameters_and_constructor_parameter_properties() {
        let parsed = parse_source_file(
            r"
                var v = (public x: string) => x;
                class C { constructor(public readonly value: string) { value; } }
                class any {}
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let root = result.root_scope().unwrap();
        assert!(root.symbols.get("v").is_some());
        assert!(root.symbols.get("any").is_some());
        let class = result.symbols.get(root.symbols.get("C").unwrap()).unwrap();
        assert!(
            result
                .symbols
                .get(class.members.get("value").unwrap())
                .unwrap()
                .flags
                .contains(SymbolFlags::PROPERTY)
        );
        for parameter in ["x", "value"] {
            assert!(result.scopes.iter().any(|scope| {
                scope.kind == ScopeKind::Function && scope.symbols.get(parameter).is_some()
            }));
        }
    }
}
