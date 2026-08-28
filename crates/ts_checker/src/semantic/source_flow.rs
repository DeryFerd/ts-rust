//! Invocation-local control-flow snapshots for source checking.
//!
//! This slice accepts the flow chains needed by direct identifier truthiness,
//! strict `typeof` comparisons, nullable equality, and declared discriminants:
//! function `START`, initialized local and authenticated parameter `ASSIGNMENT`
//! nodes, approved `CALL` nodes, condition edges, unreachable nodes, ordered
//! branch joins, and cyclic loop labels. Authenticated declaration-order queries
//! also retain the exact block-scoped, class, and enum diagnostics. Other
//! mutation expressions and switch-clause narrowing remain typed capability
//! boundaries.
//! Class initialization keeps the actual constructor exit and super-call edges.
//! Static blocks retain their outer start and receiver-specific property keys.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use ts_ast::{
    FlowFlags, FlowNode, FlowNodePayload, FlowRef, NodeArena, NodeData, NodeRef, SyntaxKind,
};
use ts_binder::{
    BoundFile, BoundFlowGraph, CanonicalNameResolver, CanonicalResolutionLocation,
    SemanticSymbolId, SymbolFlags,
};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerOptions, CanonicalCheckerRelatedInformation,
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable, TypeId,
    bootstrap::{LiteralTypeCacheError, UnionReduction},
    classes::{
        ClassBodyAccessToken, ClassBodyKind, ClassBodyPlan, ClassMemberOrigin, ClassMemberSource,
        ClassPropertySide, class_body_identities, class_member_source,
    },
    logical_operators::{LogicalBinaryError, TruthinessAssumption, narrow_by_truthiness},
    source::CheckedClassPropertyAssignment,
    source_properties::{
        ClassAccessContext, SourceClassPropertyWritePlan, SourcePropertyError,
        plan_class_property_write, validate_class_property_write_access,
    },
    type_records::{LiteralValue, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

const FLOW_DEPTH_LIMIT: usize = 2_000;
const FLOW_METADATA_BITS: u32 = FlowFlags::REFERENCED.bits() | FlowFlags::SHARED.bits();

pub(super) type SourceFlowTypes = HashMap<SemanticSymbolId, TypeId>;

/// One immutable map of current invocation-local symbol types.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceFlowSnapshot(Arc<SourceFlowTypes>);

impl SourceFlowSnapshot {
    fn new(types: SourceFlowTypes) -> Self {
        Self(Arc::new(types))
    }

    #[must_use]
    pub(super) fn types(&self) -> &SourceFlowTypes {
        self.0.as_ref()
    }

    #[must_use]
    pub(super) fn type_of(&self, symbol: SemanticSymbolId) -> Option<TypeId> {
        self.0.get(&symbol).copied()
    }

    fn with_type(&self, symbol: SemanticSymbolId, type_: TypeId) -> Self {
        if self.type_of(symbol) == Some(type_) {
            return self.clone();
        }
        let mut updated = self.types().clone();
        updated.insert(symbol, type_);
        Self::new(updated)
    }
}

/// A direct identifier whose current type is narrowed on an `if` edge.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceTruthinessCondition {
    /// The exact AST payload carried by both binder condition nodes.
    pub(super) expression: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

/// One JavaScript `typeof` result admitted by the bounded source-flow slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceTypeofTag {
    String,
    Number,
    Boolean,
    BigInt,
    Symbol,
    Undefined,
    Object,
    Function,
}

/// Whether the source condition compares equal or not equal to its tag.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceTypeofComparison {
    Equal,
    NotEqual,
}

/// A direct identifier narrowed by an exact `typeof` comparison.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceTypeofCondition {
    /// The exact AST payload carried by both binder condition nodes.
    pub(super) expression: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) tag: SourceTypeofTag,
    pub(super) comparison: SourceTypeofComparison,
}

/// One authenticated equality condition over a value or discriminant property.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceEqualityCondition {
    pub(super) expression: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) value: NodeRef,
    pub(super) comparison: SourceTypeofComparison,
    pub(super) strict: bool,
    pub(super) discriminant: Option<NodeRef>,
}

/// One cold-proven condition executable by the invocation-local flow frame.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFlowCondition {
    Truthiness(SourceTruthinessCondition),
    Typeof(SourceTypeofCondition),
    Equality(SourceEqualityCondition),
}

impl SourceFlowCondition {
    const fn expression(self) -> NodeRef {
        match self {
            Self::Truthiness(condition) => condition.expression,
            Self::Typeof(condition) => condition.expression,
            Self::Equality(condition) => condition.expression,
        }
    }

    const fn symbol(self) -> SemanticSymbolId {
        match self {
            Self::Truthiness(condition) => condition.symbol,
            Self::Typeof(condition) => condition.symbol,
            Self::Equality(condition) => condition.symbol,
        }
    }
}

/// One initialized local or proven parameter write represented by binder flow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceFlowAssignment {
    /// The exact declaration or assignment-target payload carried by the flow node.
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

/// One parameter assignment with its exact binder declaration and target.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceFlowParameterAssignment {
    pub(super) target: NodeRef,
    /// The direct parameter or binding element that owns the assigned symbol.
    pub(super) parameter: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

/// Immutable, cold-preflighted flow identities for one callable invocation.
#[derive(Clone, Debug)]
pub(super) struct SourceFlowPlan {
    container: NodeRef,
    start_container: NodeRef,
    start: FlowRef,
    start_payload: Option<NodeRef>,
    end: Option<FlowRef>,
    points: HashMap<NodeRef, FlowRef>,
    point_order: Vec<NodeRef>,
    conditions: HashMap<NodeRef, SourceFlowCondition>,
    assignments: HashMap<NodeRef, SourceFlowAssignment>,
    assignment_order: Vec<NodeRef>,
    parameter_assignments: HashMap<NodeRef, NodeRef>,
    calls: HashMap<NodeRef, NodeRef>,
    class_body: Option<ClassBodyPlan>,
    property_assignments: HashMap<NodeRef, ClassPropertyFlowAssignment>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum ClassPropertyFlowReceiver {
    This(NodeRef),
    Super(NodeRef),
    Named(SemanticSymbolId),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct ClassPropertyFlowReference {
    receiver: ClassPropertyFlowReceiver,
    name: String,
}

#[derive(Clone, Debug)]
struct ClassPropertyFlowAssignment {
    expression: NodeRef,
    reference: ClassPropertyFlowReference,
    write: Option<ClassPropertyWriteFlow>,
}

#[derive(Clone, Debug)]
struct ClassPropertyWriteFlow {
    plan: SourceClassPropertyWritePlan,
    flow: FlowRef,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ClassPropertyFlowState {
    type_: Option<TypeId>,
    initialized: bool,
}

struct ClassPropertyFlowQuery<'query> {
    reference: &'query ClassPropertyFlowReference,
    member: &'query ClassMemberSource,
    initial: ClassPropertyFlowState,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFlowUnsupported {
    IncompleteContainer(NodeRef),
    FlowKind { flow: FlowRef, flags: FlowFlags },
    Call(NodeRef),
    PropertyWrite(NodeRef),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFlowInvariant {
    ForeignNode(NodeRef),
    ForeignFlow(FlowRef),
    MissingContainer(NodeRef),
    ContainerMismatch {
        node: NodeRef,
        expected: NodeRef,
        actual: NodeRef,
    },
    MissingStart(NodeRef),
    StartMismatch {
        container: NodeRef,
        expected: FlowRef,
        actual: FlowRef,
    },
    InvalidStart(FlowRef),
    InvalidUnreachable(FlowRef),
    MissingFlowPoint(NodeRef),
    MissingFlowNode(FlowRef),
    InvalidFlowFlags {
        flow: FlowRef,
        flags: FlowFlags,
    },
    InvalidPayload(FlowRef),
    InvalidAntecedents(FlowRef),
    DuplicatePoint(NodeRef),
    DuplicateCondition(NodeRef),
    DuplicateAssignment(NodeRef),
    DuplicateCall(NodeRef),
    UnknownCondition(NodeRef),
    UnknownAssignment(NodeRef),
    UnreachedCall(NodeRef),
    UnreachedCondition(NodeRef),
    MissingConditionEdge {
        condition: NodeRef,
        true_edge: bool,
        false_edge: bool,
    },
    UnreachedAssignment(NodeRef),
    PendingAssignment(NodeRef),
    AssignmentSymbolMismatch {
        declaration: NodeRef,
        expected: SemanticSymbolId,
        actual: SemanticSymbolId,
    },
    InvalidParameterAssignment(NodeRef),
    InvalidCall(NodeRef),
    InvalidDeclarationUse(NodeRef),
    InvalidClassBody(NodeRef),
    InvalidClassProperty(NodeRef),
    AssignmentAlreadyCompleted(NodeRef),
    MissingCurrentType(SemanticSymbolId),
    TypeofNarrowing(SourceTypeofNarrowingError),
    EqualityNarrowing(SourceEqualityNarrowingError),
    Cycle(FlowRef),
    DepthLimit(FlowRef),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFlowError {
    Unsupported(SourceFlowUnsupported),
    Invariant(SourceFlowInvariant),
    Narrowing {
        condition: NodeRef,
        error: LogicalBinaryError,
    },
    Join {
        flow: FlowRef,
        error: LiteralTypeCacheError,
    },
}

/// A malformed type graph or unavailable union cache while applying a
/// preflighted `typeof` flow fact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceTypeofNarrowingError {
    MissingBootstrap,
    InvalidType(TypeId),
    InvalidUnion(TypeId),
    CyclicUnion(TypeId),
    UnsupportedType(TypeId),
    Union(LiteralTypeCacheError),
}

/// Invalid equality operands or unavailable authenticated discriminant values.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceEqualityNarrowingError {
    MissingBootstrap,
    InvalidType(TypeId),
    MissingValue(NodeRef),
    InvalidDiscriminant(NodeRef),
    UnsupportedType(TypeId),
    Relation(RelationUnavailable),
    Union(LiteralTypeCacheError),
}

impl From<SourceFlowUnsupported> for SourceFlowError {
    fn from(error: SourceFlowUnsupported) -> Self {
        Self::Unsupported(error)
    }
}

impl From<SourceFlowInvariant> for SourceFlowError {
    fn from(error: SourceFlowInvariant) -> Self {
        Self::Invariant(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceFlowKind {
    Unreachable,
    Start,
    Assignment,
    Call,
    TrueCondition,
    FalseCondition,
    BranchLabel,
    LoopLabel,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceFlowAssignmentState {
    Pending,
    Resolved(TypeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceTypeofLeafMatch {
    Exact(bool),
    Any,
    Unknown,
    NonNullableUnknown,
}

#[derive(Default)]
struct SourceFlowCoverage {
    assignments: HashSet<NodeRef>,
    calls: HashSet<NodeRef>,
    condition_edges: HashMap<NodeRef, u8>,
}

#[derive(Default)]
struct SourceFlowEffects {
    parameter_assignments: HashMap<NodeRef, NodeRef>,
    calls: HashMap<NodeRef, NodeRef>,
    class_body: Option<ClassBodyPlan>,
    start_container: Option<NodeRef>,
    property_assignments: HashMap<NodeRef, ClassPropertyFlowAssignment>,
}

const TRUE_CONDITION_EDGE: u8 = 1 << 0;
const FALSE_CONDITION_EDGE: u8 = 1 << 1;
const BOTH_CONDITION_EDGES: u8 = TRUE_CONDITION_EDGE | FALSE_CONDITION_EDGE;

/// Returns the exact upstream diagnostic for an immediate block-scoped value use.
///
/// Const enums are exempt unless isolated module checking requires runtime order.
pub(super) fn source_block_scoped_use_before_declaration(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    usage: NodeRef,
    symbol: SemanticSymbolId,
    isolated_modules: bool,
) -> Result<Option<CanonicalCheckerDiagnostic>, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidDeclarationUse(usage);
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || !usage.is_for(arena.id(), bound.file_id())
        || !bound.contains(usage)
        || !store.contains_node_ref(usage)
    {
        return Err(SourceFlowInvariant::ForeignNode(usage).into());
    }
    let usage_record = arena.get(usage.node).ok_or_else(invalid)?;
    let NodeData::Identifier(usage_name) = &usage_record.data else {
        return Err(invalid().into());
    };
    if usage_record.kind != SyntaxKind::Identifier
        || usage_record.flags.0 != 0
        || usage_name.flow_node.is_some()
        || usage_name.text.is_empty()
    {
        return Err(invalid().into());
    }

    let resolved = store.symbol(symbol).ok_or_else(invalid)?;
    let symbol = store
        .get_merged_symbol(resolved.export_symbol().unwrap_or(symbol))
        .ok_or_else(invalid)?;
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    let flags = record.flags();
    let code = if flags.contains(SymbolFlags::BLOCK_SCOPED_VARIABLE) {
        2448
    } else if flags.contains(SymbolFlags::CLASS) {
        if flags.intersects(
            SymbolFlags::FUNCTION | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::ASSIGNMENT,
        ) {
            return Ok(None);
        }
        2449
    } else if flags.contains(SymbolFlags::REGULAR_ENUM)
        || flags.contains(SymbolFlags::CONST_ENUM) && isolated_modules
    {
        2450
    } else {
        return Ok(None);
    };

    let declaration = record.value_declaration().ok_or_else(invalid)?;
    if !declaration.is_for(arena.id(), bound.file_id()) {
        return Ok(None);
    }
    if !bound.contains(declaration)
        || !store.contains_node_ref(declaration)
        || bound
            .symbol(declaration)
            .and_then(|owner| store.get_merged_symbol(owner))
            != Some(symbol)
    {
        return Err(invalid().into());
    }
    let declaration_record = arena.get(declaration.node).ok_or_else(invalid)?;
    let name = match (&declaration_record.data, code) {
        (NodeData::VariableDeclaration(declaration), 2448)
            if declaration_record.kind == SyntaxKind::VariableDeclaration =>
        {
            declaration.name
        }
        (NodeData::ClassDeclaration(declaration), 2449)
            if declaration_record.kind == SyntaxKind::ClassDeclaration =>
        {
            declaration.name.ok_or_else(invalid)?
        }
        (NodeData::EnumDeclaration(declaration), 2450)
            if declaration_record.kind == SyntaxKind::EnumDeclaration =>
        {
            declaration.name
        }
        _ => return Err(invalid().into()),
    };
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    let name_record = arena.get(name.node).ok_or_else(invalid)?;
    let NodeData::Identifier(declaration_name) = &name_record.data else {
        return Err(invalid().into());
    };
    if !bound.contains(name)
        || !store.contains_node_ref(name)
        || name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || name_record.flags.0 != 0
        || declaration_name.flow_node.is_some()
        || declaration_name.text != usage_name.text
        || record.name().as_utf8() != Some(declaration_name.text.as_str())
    {
        return Err(invalid().into());
    }

    let scope = bound
        .block_scope_container(declaration)
        .ok_or_else(invalid)?;
    let local = bound
        .locals(scope)
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get_source(&declaration_name.text))
        .ok_or_else(invalid)?;
    let local_record = store.symbol(local).ok_or_else(invalid)?;
    if store.get_merged_symbol(local_record.export_symbol().unwrap_or(local)) != Some(symbol) {
        return Err(invalid().into());
    }
    if source_declaration_is_ambient(arena, bound, declaration, usage)?
        || !source_declaration_use_is_immediate(arena, bound, usage, scope)?
    {
        return Ok(None);
    }

    let occurs_before_declaration = usage_record.range.start < declaration_record.range.start;
    let occurs_in_own_initializer = matches!(
        &declaration_record.data,
        NodeData::VariableDeclaration(variable)
            if variable.initializer.is_some_and(|initializer| {
                source_node_is_descendant_of(arena, usage, initializer)
            })
    );
    if !occurs_before_declaration && !occurs_in_own_initializer {
        return Ok(None);
    }

    Ok(Some(CanonicalCheckerDiagnostic {
        node: Some(usage),
        range_override: None,
        diagnostic: Diagnostic::with_arguments(
            message_by_code(code).expect("block-scoped diagnostic is in the catalog"),
            [declaration_name.text.clone()],
        ),
        related_information: vec![CanonicalCheckerRelatedInformation {
            node: Some(name),
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2728).expect("declaration-related diagnostic is in the catalog"),
                [declaration_name.text.clone()],
            ),
        }],
    }))
}

fn source_declaration_is_ambient(
    arena: &NodeArena,
    bound: &BoundFile,
    declaration: NodeRef,
    usage: NodeRef,
) -> Result<bool, SourceFlowError> {
    if bound
        .source_facts()
        .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file)
    {
        return Ok(true);
    }

    let invalid = || SourceFlowInvariant::InvalidDeclarationUse(usage);
    let mut current = declaration;
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(current) || !bound.contains(current) {
            return Err(invalid().into());
        }
        let record = arena.get(current.node).ok_or_else(invalid)?;
        let modifiers = match &record.data {
            NodeData::ClassDeclaration(declaration) => declaration.modifiers.as_ref(),
            NodeData::EnumDeclaration(declaration) => declaration.modifiers.as_ref(),
            NodeData::ModuleDeclaration(declaration) => declaration.modifiers.as_ref(),
            NodeData::VariableStatement(statement) => statement.modifiers.as_ref(),
            _ => None,
        };
        if let Some(modifiers) = modifiers {
            for modifier in &modifiers.list.nodes {
                let modifier = NodeRef::new(current.arena, current.file, *modifier);
                let modifier_record = arena.get(modifier.node).ok_or_else(invalid)?;
                if !bound.contains(modifier) || modifier_record.parent != Some(current.node) {
                    return Err(invalid().into());
                }
                if modifier_record.kind == SyntaxKind::DeclareKeyword {
                    return Ok(true);
                }
            }
        }
        let Some(parent) = record.parent else {
            return if current == bound.source_file() {
                Ok(false)
            } else {
                Err(invalid().into())
            };
        };
        current = NodeRef::new(current.arena, current.file, parent);
    }
}

fn source_declaration_use_is_immediate(
    arena: &NodeArena,
    bound: &BoundFile,
    usage: NodeRef,
    scope: NodeRef,
) -> Result<bool, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidDeclarationUse(usage);
    let mut current = usage;
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(current) || !bound.contains(current) {
            return Err(invalid().into());
        }
        if current == scope {
            return Ok(true);
        }
        let record = arena.get(current.node).ok_or_else(invalid)?;
        if matches!(
            record.kind,
            SyntaxKind::FunctionDeclaration
                | SyntaxKind::FunctionExpression
                | SyntaxKind::ArrowFunction
                | SyntaxKind::TypeAliasDeclaration
                | SyntaxKind::InterfaceDeclaration
                | SyntaxKind::TypeReference
                | SyntaxKind::TypeQuery
                | SyntaxKind::ImportType
                | SyntaxKind::ExportSpecifier
        ) {
            return Ok(false);
        }
        if matches!(
            &record.data,
            NodeData::ExportAssignment(assignment) if assignment.is_export_equals
        ) {
            return Ok(false);
        }
        let Some(parent) = record.parent else {
            return Ok(false);
        };
        current = NodeRef::new(current.arena, current.file, parent);
    }
}

fn source_node_is_descendant_of(
    arena: &NodeArena,
    usage: NodeRef,
    ancestor: ts_ast::NodeId,
) -> bool {
    let mut current = Some(usage.node);
    let mut visited = HashSet::new();
    while let Some(node) = current {
        if !visited.insert(node) {
            return false;
        }
        if node == ancestor {
            return true;
        }
        current = arena.get(node).and_then(|record| record.parent);
    }
    false
}

impl SourceFlowPlan {
    pub(super) fn has_reachable_end(&self) -> bool {
        self.end.is_some()
    }

    /// Uses the binder's body flow, including an inline static block's outer start.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_class_body(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        body: &ClassBodyPlan,
        points: impl IntoIterator<Item = NodeRef>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
    ) -> Result<Self, SourceFlowError> {
        let invalid = || SourceFlowInvariant::InvalidClassBody(body.declaration);
        if bound.node_arena_id() != arena.id()
            || bound.node_arena_revision() != arena.revision()
            || !body.declaration.is_for(arena.id(), bound.file_id())
            || !bound.contains(body.declaration)
            || !bound.contains(body.body)
            || host
                .source(body.declaration)
                .is_none_or(|(source, binding)| {
                    source.id() != arena.id() || binding.source_file() != bound.source_file()
                })
        {
            return Err(invalid().into());
        }
        let declaration = arena.get(body.declaration.node).ok_or_else(invalid)?;
        let expected_body = match (&declaration.data, &body.kind) {
            (NodeData::ConstructorDeclaration(data), ClassBodyKind::Constructor)
                if declaration.kind == SyntaxKind::Constructor =>
            {
                data.body
            }
            (NodeData::MethodDeclaration(data), ClassBodyKind::Method { .. })
                if declaration.kind == SyntaxKind::MethodDeclaration =>
            {
                data.body
            }
            (NodeData::ClassStaticBlockDeclaration(data), ClassBodyKind::StaticBlock)
                if declaration.kind == SyntaxKind::ClassStaticBlockDeclaration =>
            {
                Some(data.body)
            }
            _ => return Err(invalid().into()),
        };
        if expected_body != Some(body.body.node)
            || declaration.parent != Some(body.class_declaration.node)
            || arena.get(body.body.node).is_none_or(|block| {
                block.kind != SyntaxKind::Block || block.parent != Some(body.declaration.node)
            })
        {
            return Err(invalid().into());
        }
        let points = points.into_iter().collect::<Vec<_>>();
        let container = bound
            .flow_container(body.body)
            .or_else(|| {
                points
                    .first()
                    .and_then(|point| bound.flow_container(*point))
            })
            .unwrap_or(body.declaration);
        let mut effects = SourceFlowEffects {
            class_body: Some(body.clone()),
            start_container: matches!(body.kind, ClassBodyKind::StaticBlock)
                .then(|| class_control_flow_container(host, body.declaration))
                .transpose()?,
            ..SourceFlowEffects::default()
        };
        for call in calls {
            let statement = validate_class_body_call(arena, bound, body, container, call)?;
            if effects.calls.insert(call, statement).is_some() {
                return Err(SourceFlowInvariant::DuplicateCall(call).into());
            }
        }
        if matches!(
            body.kind,
            ClassBodyKind::Constructor | ClassBodyKind::StaticBlock
        ) {
            let mut pending = points
                .iter()
                .map(|point| {
                    bound
                        .flow_at(*point)
                        .ok_or(SourceFlowInvariant::MissingFlowPoint(*point))
                })
                .collect::<Result<Vec<_>, _>>()?;
            pending.extend(bound.flow_graph().container_return(body.declaration));
            let mut visited = HashSet::new();
            while let Some(flow) = pending.pop() {
                if !visited.insert(flow) {
                    continue;
                }
                if visited.len() > FLOW_DEPTH_LIMIT {
                    return Err(SourceFlowInvariant::DepthLimit(flow).into());
                }
                let node = flow_node(bound.flow_graph(), flow)?;
                if source_flow_kind(flow, node.flags)? == SourceFlowKind::Assignment {
                    let target = ast_payload(flow, &node)?;
                    let assignment = if matches!(body.kind, ClassBodyKind::Constructor) {
                        plan_constructor_property_assignment(
                            arena, bound, store, host, body, target, flow,
                        )?
                    } else {
                        plan_outer_class_property_assignment(
                            arena, bound, store, host, body, target,
                        )?
                    };
                    if let Some(assignment) = assignment {
                        effects.property_assignments.insert(target, assignment);
                    }
                }
                pending.extend(node.antecedent);
                pending.extend(node.antecedents.iter().copied());
            }
        }
        for &point in &points {
            if is_property_assignment_target(host, point)
                && source_node_is_descendant_of(arena, point, body.body.node)
                && !effects.property_assignments.contains_key(&point)
            {
                return Err(SourceFlowUnsupported::PropertyWrite(point).into());
            }
        }
        Self::preflight_with_effects(bound, container, None, points, [], assignments, effects)
    }

    /// Freezes and validates every flow chain that the source executor may
    /// request. No semantic store state is read or written during preflight.
    pub(super) fn preflight(
        bound: &BoundFile,
        container: NodeRef,
        expected_start_payload: Option<NodeRef>,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceFlowCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
    ) -> Result<Self, SourceFlowError> {
        Self::preflight_with_effects(
            bound,
            container,
            expected_start_payload,
            points,
            conditions,
            assignments,
            SourceFlowEffects::default(),
        )
    }

    /// Proves direct call statements and assignments to exact function parameters.
    pub(super) fn preflight_linear(
        arena: &NodeArena,
        bound: &BoundFile,
        container: NodeRef,
        points: impl IntoIterator<Item = NodeRef>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        parameter_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
    ) -> Result<Self, SourceFlowError> {
        if bound.node_arena_id() != arena.id()
            || bound.node_arena_revision() != arena.revision()
            || !container.is_for(arena.id(), bound.file_id())
        {
            return Err(SourceFlowInvariant::ForeignNode(container).into());
        }

        let mut planned_assignments = assignments.into_iter().collect::<Vec<_>>();
        let mut effects = SourceFlowEffects::default();
        for assignment in parameter_assignments {
            validate_parameter_assignment(arena, bound, container, assignment)?;
            if effects
                .parameter_assignments
                .insert(assignment.target, assignment.parameter)
                .is_some()
            {
                return Err(SourceFlowInvariant::DuplicateAssignment(assignment.target).into());
            }
            planned_assignments.push(SourceFlowAssignment {
                declaration: assignment.target,
                symbol: assignment.symbol,
            });
        }
        for call in calls {
            let statement = validate_direct_call(arena, bound, container, call)?;
            if effects.calls.insert(call, statement).is_some() {
                return Err(SourceFlowInvariant::DuplicateCall(call).into());
            }
        }

        let expected_start_payload = arena
            .get(container.node)
            .is_some_and(|record| {
                record.kind == SyntaxKind::ArrowFunction
                    && matches!(record.data, NodeData::ArrowFunction(_))
            })
            .then_some(container);
        Self::preflight_with_effects(
            bound,
            container,
            expected_start_payload,
            points,
            [],
            planned_assignments,
            effects,
        )
    }

    fn preflight_with_effects(
        bound: &BoundFile,
        container: NodeRef,
        expected_start_payload: Option<NodeRef>,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceFlowCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        effects: SourceFlowEffects,
    ) -> Result<Self, SourceFlowError> {
        let graph = bound.flow_graph();
        validate_container(graph, container)?;
        let start_container = effects.start_container.unwrap_or(container);
        let start = graph
            .container_start(start_container)
            .ok_or(SourceFlowInvariant::MissingStart(start_container))?;
        let start_payload = preflight_start_payload(graph, start_container, start)?;
        if start_payload != expected_start_payload {
            return Err(SourceFlowInvariant::InvalidStart(start).into());
        }

        let mut planned_conditions = HashMap::new();
        for condition in conditions {
            let expression = condition.expression();
            validate_bound_node(bound, graph, expression)?;
            if planned_conditions.insert(expression, condition).is_some() {
                return Err(SourceFlowInvariant::DuplicateCondition(expression).into());
            }
        }

        let mut planned_assignments = HashMap::new();
        let mut assignment_order = Vec::new();
        for assignment in assignments {
            validate_bound_node(bound, graph, assignment.declaration)?;
            if let Some(parameter) = effects.parameter_assignments.get(&assignment.declaration) {
                if bound.symbol(*parameter) != Some(assignment.symbol)
                    || bound.container(*parameter) != Some(container)
                    || bound.container(assignment.declaration) != Some(container)
                {
                    return Err(SourceFlowInvariant::InvalidParameterAssignment(
                        assignment.declaration,
                    )
                    .into());
                }
            } else if bound.symbol(assignment.declaration) != Some(assignment.symbol) {
                return Err(SourceFlowInvariant::InvalidParameterAssignment(
                    assignment.declaration,
                )
                .into());
            }
            if planned_assignments
                .insert(assignment.declaration, assignment)
                .is_some()
            {
                return Err(
                    SourceFlowInvariant::DuplicateAssignment(assignment.declaration).into(),
                );
            }
            assignment_order.push(assignment.declaration);
        }

        let mut planned_points = HashMap::new();
        let mut point_order = Vec::new();
        for point in points {
            insert_flow_point(
                bound,
                graph,
                container,
                &mut planned_points,
                &mut point_order,
                point,
                true,
            )?;
        }
        let end = match effects.class_body.as_ref() {
            Some(body)
                if matches!(
                    body.kind,
                    ClassBodyKind::Constructor | ClassBodyKind::StaticBlock
                ) =>
            {
                Some(
                    graph
                        .container_return(body.declaration)
                        .ok_or(SourceFlowInvariant::InvalidClassBody(body.declaration))?,
                )
            }
            _ => graph.container_end(container),
        };
        let plan = Self {
            container,
            start_container,
            start,
            start_payload,
            end,
            points: planned_points,
            point_order,
            conditions: planned_conditions,
            assignments: planned_assignments,
            assignment_order,
            parameter_assignments: effects.parameter_assignments,
            calls: effects.calls,
            class_body: effects.class_body,
            property_assignments: effects.property_assignments,
        };
        plan.validate_flow_paths(bound)?;
        Ok(plan)
    }

    /// Starts one fresh execution frame. Flow snapshots and assignment state
    /// are never retained across callable checks or source retries.
    pub(super) fn frame<'plan, 'graph>(
        &'plan self,
        bound: &'graph BoundFile,
        base: SourceFlowTypes,
    ) -> Result<SourceFlowFrame<'plan, 'graph>, SourceFlowError> {
        let graph = bound.flow_graph();
        validate_container(graph, self.container)?;
        let actual = graph
            .container_start(self.start_container)
            .ok_or(SourceFlowInvariant::MissingStart(self.start_container))?;
        if actual != self.start {
            return Err(SourceFlowInvariant::StartMismatch {
                container: self.container,
                expected: self.start,
                actual,
            }
            .into());
        }
        let start_node = flow_node(graph, actual)?;
        if source_flow_kind(actual, start_node.flags)? != SourceFlowKind::Start {
            return Err(SourceFlowInvariant::InvalidStart(actual).into());
        }
        validate_start_node(self, actual, &start_node)?;
        for (target, parameter) in &self.parameter_assignments {
            let assignment = self
                .assignments
                .get(target)
                .ok_or(SourceFlowInvariant::UnknownAssignment(*target))?;
            if bound.symbol(*parameter) != Some(assignment.symbol)
                || bound.container(*parameter) != Some(self.container)
                || bound.container(*target) != Some(self.container)
            {
                return Err(SourceFlowInvariant::InvalidParameterAssignment(*target).into());
            }
        }
        Ok(SourceFlowFrame {
            plan: self,
            bound,
            graph,
            base: SourceFlowSnapshot::new(base),
            assignment_states: self
                .assignments
                .keys()
                .copied()
                .map(|declaration| (declaration, SourceFlowAssignmentState::Pending))
                .collect(),
            memo: HashMap::new(),
            visiting: HashSet::new(),
            loop_snapshots: HashMap::new(),
        })
    }

    fn validate_flow_paths(&self, bound: &BoundFile) -> Result<(), SourceFlowError> {
        let mut validated = HashSet::new();
        let mut visiting = HashSet::new();
        let mut coverage = SourceFlowCoverage::default();
        for point in &self.point_order {
            let flow = *self
                .points
                .get(point)
                .ok_or(SourceFlowInvariant::MissingFlowPoint(*point))?;
            self.validate_flow(bound, flow, 0, &mut validated, &mut visiting, &mut coverage)?;
        }
        if let Some(end) = self.end {
            self.validate_flow(bound, end, 0, &mut validated, &mut visiting, &mut coverage)?;
        }
        for declaration in self.assignments.keys() {
            if !coverage.assignments.contains(declaration) {
                return Err(SourceFlowInvariant::UnreachedAssignment(*declaration).into());
            }
        }
        for (target, assignment) in &self.property_assignments {
            if assignment.write.is_some() && !coverage.assignments.contains(target) {
                return Err(SourceFlowInvariant::UnreachedAssignment(*target).into());
            }
        }
        for call in self.calls.keys() {
            if !coverage.calls.contains(call) {
                return Err(SourceFlowInvariant::UnreachedCall(*call).into());
            }
        }
        for condition in self.conditions.keys() {
            let Some(edges) = coverage.condition_edges.get(condition).copied() else {
                return Err(SourceFlowInvariant::UnreachedCondition(*condition).into());
            };
            if edges != BOTH_CONDITION_EDGES {
                return Err(SourceFlowInvariant::MissingConditionEdge {
                    condition: *condition,
                    true_edge: edges & TRUE_CONDITION_EDGE != 0,
                    false_edge: edges & FALSE_CONDITION_EDGE != 0,
                }
                .into());
            }
        }
        Ok(())
    }

    fn validate_flow(
        &self,
        bound: &BoundFile,
        flow: FlowRef,
        depth: usize,
        validated: &mut HashSet<FlowRef>,
        visiting: &mut HashSet<FlowRef>,
        coverage: &mut SourceFlowCoverage,
    ) -> Result<(), SourceFlowError> {
        let graph = bound.flow_graph();
        if validated.contains(&flow) {
            return Ok(());
        }
        if depth > FLOW_DEPTH_LIMIT {
            return Err(SourceFlowInvariant::DepthLimit(flow).into());
        }
        if !visiting.insert(flow) {
            let node = flow_node(graph, flow)?;
            return if source_flow_kind(flow, node.flags)? == SourceFlowKind::LoopLabel {
                Ok(())
            } else {
                Err(SourceFlowInvariant::Cycle(flow).into())
            };
        }
        let result = self.validate_flow_uncached(bound, flow, depth, validated, visiting, coverage);
        let removed = visiting.remove(&flow);
        debug_assert!(removed);
        if result.is_ok() {
            validated.insert(flow);
        }
        result
    }

    fn validate_flow_uncached(
        &self,
        bound: &BoundFile,
        flow: FlowRef,
        depth: usize,
        validated: &mut HashSet<FlowRef>,
        visiting: &mut HashSet<FlowRef>,
        coverage: &mut SourceFlowCoverage,
    ) -> Result<(), SourceFlowError> {
        let graph = bound.flow_graph();
        let node = flow_node(graph, flow)?;
        match source_flow_kind(flow, node.flags)? {
            SourceFlowKind::Unreachable => validate_unreachable_node(graph, flow, &node),
            SourceFlowKind::Start => validate_start_node(self, flow, &node),
            SourceFlowKind::Assignment => {
                let antecedent = linear_antecedent(flow, &node)?;
                let declaration = ast_payload(flow, &node)?;
                if !self.assignments.contains_key(&declaration)
                    && !self.property_assignments.contains_key(&declaration)
                {
                    return Err(SourceFlowInvariant::UnknownAssignment(declaration).into());
                }
                coverage.assignments.insert(declaration);
                self.validate_flow(bound, antecedent, depth + 1, validated, visiting, coverage)
            }
            SourceFlowKind::Call => {
                let antecedent = linear_antecedent(flow, &node)?;
                let call = ast_payload(flow, &node)?;
                let statement = self
                    .calls
                    .get(&call)
                    .copied()
                    .ok_or(SourceFlowUnsupported::Call(call))?;
                validate_planned_call_container(bound, self, call, statement, antecedent)?;
                coverage.calls.insert(call);
                self.validate_flow(bound, antecedent, depth + 1, validated, visiting, coverage)
            }
            kind @ (SourceFlowKind::TrueCondition | SourceFlowKind::FalseCondition) => {
                let antecedent = linear_antecedent(flow, &node)?;
                let condition = ast_payload(flow, &node)?;
                if !self.conditions.contains_key(&condition) {
                    return Err(SourceFlowInvariant::UnknownCondition(condition).into());
                }
                let edge = match kind {
                    SourceFlowKind::TrueCondition => TRUE_CONDITION_EDGE,
                    SourceFlowKind::FalseCondition => FALSE_CONDITION_EDGE,
                    SourceFlowKind::Unreachable
                    | SourceFlowKind::Start
                    | SourceFlowKind::Assignment
                    | SourceFlowKind::Call
                    | SourceFlowKind::BranchLabel
                    | SourceFlowKind::LoopLabel => unreachable!(),
                };
                *coverage.condition_edges.entry(condition).or_default() |= edge;
                self.validate_flow(bound, antecedent, depth + 1, validated, visiting, coverage)
            }
            SourceFlowKind::BranchLabel | SourceFlowKind::LoopLabel => {
                for antecedent in label_antecedents(flow, &node)? {
                    self.validate_flow(
                        bound,
                        *antecedent,
                        depth + 1,
                        validated,
                        visiting,
                        coverage,
                    )?;
                }
                Ok(())
            }
        }
    }
}

/// Mutable state for exactly one source-callable execution.
pub(super) struct SourceFlowFrame<'plan, 'graph> {
    plan: &'plan SourceFlowPlan,
    bound: &'graph BoundFile,
    graph: &'graph BoundFlowGraph,
    base: SourceFlowSnapshot,
    assignment_states: HashMap<NodeRef, SourceFlowAssignmentState>,
    memo: HashMap<FlowRef, SourceFlowSnapshot>,
    visiting: HashSet<FlowRef>,
    loop_snapshots: HashMap<FlowRef, SourceFlowSnapshot>,
}

/// Keeps class initialization queries tied to one prepared body and binder graph.
pub(super) struct ClassInitializationFrame<'plan, 'graph> {
    access: ClassBodyAccessToken,
    body: &'plan ClassBodyPlan,
    flow: SourceFlowFrame<'plan, 'graph>,
    completed_calls: HashSet<NodeRef>,
    property_assignments: HashMap<NodeRef, CheckedClassPropertyAssignment>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ClassPropertyFlowRead {
    type_: TypeId,
    used_before_assignment: bool,
    access: NodeRef,
    flow: FlowRef,
}

impl ClassPropertyFlowRead {
    pub(super) const fn type_(&self) -> TypeId {
        self.type_
    }

    pub(super) const fn used_before_assignment(&self) -> bool {
        self.used_before_assignment
    }

    pub(super) const fn access(&self) -> NodeRef {
        self.access
    }

    pub(super) const fn flow(&self) -> FlowRef {
        self.flow
    }
}

impl<'plan, 'graph> ClassInitializationFrame<'plan, 'graph> {
    pub(super) fn new(
        body: &'plan ClassBodyPlan,
        plan: &'plan SourceFlowPlan,
        bound: &'graph BoundFile,
        access: ClassBodyAccessToken,
        base: SourceFlowTypes,
    ) -> Result<Self, SourceFlowError> {
        if plan.class_body.as_ref() != Some(body) {
            return Err(SourceFlowInvariant::InvalidClassBody(body.declaration).into());
        }
        Ok(Self {
            access,
            body,
            flow: plan.frame(bound, base)?,
            completed_calls: HashSet::new(),
            property_assignments: HashMap::new(),
        })
    }

    pub(super) const fn access_token(&self) -> &ClassBodyAccessToken {
        &self.access
    }

    pub(super) fn snapshot_at(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        node: NodeRef,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        self.flow.snapshot_at(store, globals, node)
    }

    pub(super) fn complete_assignment(
        &mut self,
        declaration: NodeRef,
        symbol: SemanticSymbolId,
        current_type: TypeId,
    ) -> Result<(), SourceFlowError> {
        self.flow
            .complete_assignment(declaration, symbol, current_type)
    }

    pub(super) fn complete_call(&mut self, call: NodeRef) -> Result<(), SourceFlowError> {
        if !self.flow.plan.calls.contains_key(&call) || !self.completed_calls.insert(call) {
            return Err(SourceFlowInvariant::InvalidCall(call).into());
        }
        Ok(())
    }

    pub(super) fn preflight_property_assignment(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        plan: &SourceClassPropertyWritePlan,
    ) -> Result<(), SourceFlowError> {
        let target = plan.target();
        let invalid = || SourceFlowInvariant::InvalidClassProperty(target);
        let (identities, _) = validate_class_property_write_access(store, host, plan, &self.access)
            .map_err(|_| invalid())?;
        if !matches!(self.body.kind, ClassBodyKind::Constructor)
            || identities.class_symbol != self.body.class_symbol
            || identities.body_declaration != self.body.declaration
            || identities.class_declaration != self.body.class_declaration
        {
            return Err(invalid().into());
        }
        let assignment = self
            .flow
            .plan
            .property_assignments
            .get(&target)
            .ok_or(SourceFlowInvariant::UnknownAssignment(target))?;
        let write = assignment.write.as_ref().ok_or_else(invalid)?;
        if write.plan != *plan
            || assignment.expression != plan.node()
            || assignment.reference
                != (ClassPropertyFlowReference {
                    receiver: ClassPropertyFlowReceiver::This(self.body.class_declaration),
                    name: plan.name().to_owned(),
                })
            || self.flow.bound.flow_container(target) != Some(self.flow.plan.container)
            || self.flow.plan.container != self.body.declaration
        {
            return Err(invalid().into());
        }
        let node = flow_node(self.flow.graph, write.flow)?;
        if source_flow_kind(write.flow, node.flags)? != SourceFlowKind::Assignment
            || ast_payload(write.flow, &node)? != target
        {
            return Err(invalid().into());
        }
        linear_antecedent(write.flow, &node)?;
        for point in [plan.statement(), plan.target(), plan.receiver()] {
            let expected = self
                .flow
                .plan
                .points
                .get(&point)
                .copied()
                .ok_or(SourceFlowInvariant::MissingFlowPoint(point))?;
            if self.flow.bound.flow_at(point) != Some(expected)
                || self.flow.bound.flow_container(point) != Some(self.flow.plan.container)
            {
                return Err(invalid().into());
            }
        }
        if self.property_assignments.contains_key(&target) {
            return Err(SourceFlowInvariant::AssignmentAlreadyCompleted(target).into());
        }
        Ok(())
    }

    pub(super) fn complete_property_assignment(
        &mut self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        assignment: &CheckedClassPropertyAssignment,
    ) -> Result<(), SourceFlowError> {
        let target = assignment.target();
        let plan = target.plan();
        self.preflight_property_assignment(store, host, plan)?;
        let invalid = || SourceFlowInvariant::InvalidClassProperty(plan.target());
        if target.access_token() != &self.access
            || store.type_payload(assignment.assigned_type()).is_none()
            || store.type_payload(assignment.flow_type()).is_none()
            || store
                .type_node_links(plan.node())
                .and_then(|links| links.resolved_type)
                != Some(assignment.assigned_type())
            || class_member_source(store, host, plan.member()).map_err(|_| invalid())?
                != *target.member_source()
        {
            return Err(invalid().into());
        }
        self.property_assignments
            .insert(plan.target(), assignment.clone());
        Ok(())
    }

    pub(super) fn receiver_used_before_super(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        context: &ClassAccessContext,
    ) -> Result<bool, SourceFlowError> {
        let receiver = context.receiver();
        let invalid = || SourceFlowInvariant::InvalidClassProperty(receiver);
        let identities = class_body_identities(store, host, &self.access).map_err(|_| invalid())?;
        if context.class_symbol() != self.body.class_symbol
            || context.body_declaration() != self.body.declaration
            || context.class_declaration() != self.body.class_declaration
        {
            return Err(invalid().into());
        }
        if !matches!(self.body.kind, ClassBodyKind::Constructor) || identities.base.is_none() {
            return Ok(false);
        }
        let flow = self
            .flow
            .plan
            .points
            .get(&receiver)
            .copied()
            .ok_or_else(invalid)?;
        if self.flow.bound.flow_at(receiver) != Some(flow)
            || self.flow.bound.flow_container(receiver) != Some(self.flow.plan.container)
        {
            return Err(invalid().into());
        }
        Ok(!self.is_post_super_flow(host, flow, &mut HashSet::new(), 0)?)
    }

    fn is_post_super_flow(
        &self,
        host: &DeclaredTypeHost<'_>,
        flow: FlowRef,
        visiting: &mut HashSet<FlowRef>,
        depth: usize,
    ) -> Result<bool, SourceFlowError> {
        if depth > FLOW_DEPTH_LIMIT {
            return Err(SourceFlowInvariant::DepthLimit(flow).into());
        }
        if !visiting.insert(flow) {
            return Err(SourceFlowInvariant::Cycle(flow).into());
        }
        let node = flow_node(self.flow.graph, flow)?;
        let result = match source_flow_kind(flow, node.flags)? {
            SourceFlowKind::Start => {
                validate_start_node(self.flow.plan, flow, &node)?;
                Ok(false)
            }
            SourceFlowKind::Unreachable => {
                validate_unreachable_node(self.flow.graph, flow, &node)?;
                Ok(true)
            }
            SourceFlowKind::Call => {
                let call = ast_payload(flow, &node)?;
                let is_super = matches!(host.node(call).map(|node| &node.data),
                    Some(NodeData::CallExpression(data)) if host.node(NodeRef::new(call.arena, call.file, data.expression))
                        .is_some_and(|node| node.kind == SyntaxKind::SuperKeyword));
                if is_super {
                    if !self.completed_calls.contains(&call) {
                        return Err(SourceFlowInvariant::InvalidCall(call).into());
                    }
                    Ok(true)
                } else {
                    self.is_post_super_flow(
                        host,
                        linear_antecedent(flow, &node)?,
                        visiting,
                        depth + 1,
                    )
                }
            }
            SourceFlowKind::Assignment
            | SourceFlowKind::TrueCondition
            | SourceFlowKind::FalseCondition => {
                self.is_post_super_flow(host, linear_antecedent(flow, &node)?, visiting, depth + 1)
            }
            SourceFlowKind::BranchLabel | SourceFlowKind::LoopLabel => {
                let mut initialized = true;
                for antecedent in label_antecedents(flow, &node)? {
                    initialized &=
                        self.is_post_super_flow(host, *antecedent, visiting, depth + 1)?;
                }
                Ok(initialized)
            }
        };
        visiting.remove(&flow);
        result
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn property_read(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        context: &ClassAccessContext,
        access: NodeRef,
        member: &ClassMemberSource,
        declared_type: TypeId,
        options: CanonicalCheckerOptions,
    ) -> Result<ClassPropertyFlowRead, SourceFlowError> {
        let invalid = || SourceFlowInvariant::InvalidClassProperty(access);
        class_body_identities(store, host, &self.access).map_err(|_| invalid())?;
        let source = class_member_source(store, host, member.symbol).map_err(|_| invalid())?;
        if context.class_symbol() != self.body.class_symbol
            || context.class_declaration() != self.body.class_declaration
            || context.body_declaration() != self.body.declaration
            || &source != member
            || store.type_payload(declared_type).is_none()
        {
            return Err(invalid().into());
        }
        let flow = self
            .flow
            .plan
            .points
            .get(&access)
            .copied()
            .ok_or_else(invalid)?;
        if self.flow.bound.flow_at(access) != Some(flow)
            || self.flow.bound.flow_container(access) != Some(self.flow.plan.container)
        {
            return Err(invalid().into());
        }
        let record = host.node(access).ok_or_else(invalid)?;
        let NodeData::PropertyAccessExpression(property) = &record.data else {
            return Err(invalid().into());
        };
        let receiver = NodeRef::new(access.arena, access.file, property.expression);
        let name_node = NodeRef::new(access.arena, access.file, property.name);
        let name = match host.node(name_node).map(|record| &record.data) {
            Some(NodeData::Identifier(identifier)) => &identifier.text,
            Some(NodeData::PrivateIdentifier(identifier)) => &identifier.text,
            _ => return Err(invalid().into()),
        };
        if receiver != context.receiver() {
            return Err(invalid().into());
        }
        let receiver_kind = match host.node(receiver).map(|record| record.kind) {
            Some(SyntaxKind::ThisKeyword) => {
                ClassPropertyFlowReceiver::This(self.body.class_declaration)
            }
            Some(SyntaxKind::SuperKeyword) => {
                ClassPropertyFlowReceiver::Super(self.body.class_declaration)
            }
            _ => return Err(invalid().into()),
        };
        let reference = ClassPropertyFlowReference {
            receiver: receiver_kind,
            name: name.clone(),
        };
        let assume_uninitialized = options.intrinsic.strict_null_checks
            && match member.origin {
                ClassMemberOrigin::Field { initializer: None } => {
                    options.strict_property_initialization
                        && !member.abstract_
                        && matches!(reference.receiver, ClassPropertyFlowReceiver::This(_))
                        && matches!(self.body.kind, ClassBodyKind::Constructor)
                        && member.side == ClassPropertySide::Instance
                    && member.declaring_class == self.body.class_symbol
                    && host.node(member.declaration).is_some_and(|record| {
                        matches!(&record.data, NodeData::PropertyDeclaration(data)
                            if data.postfix_token.is_none_or(|token| {
                                host.node(NodeRef::new(member.declaration.arena, member.declaration.file, token))
                                    .is_some_and(|token| token.kind != SyntaxKind::ExclamationToken)
                            }))
                    })
                }
                ClassMemberOrigin::JavaScriptAssignment { assignment } => {
                    class_control_flow_container(host, access)?
                        == class_control_flow_container(host, assignment)?
                }
                _ => false,
            };
        let state = self.property_state_at(
            store,
            host,
            flow,
            &ClassPropertyFlowQuery {
                reference: &reference,
                member,
                initial: ClassPropertyFlowState {
                    type_: Some(declared_type),
                    initialized: !assume_uninitialized,
                },
            },
            &mut HashSet::new(),
            0,
        )?;
        Ok(ClassPropertyFlowRead {
            type_: state.type_.ok_or_else(invalid)?,
            used_before_assignment: !state.initialized
                && !class_property_type_skips_initialization_check(store, declared_type)?,
            access,
            flow,
        })
    }

    pub(super) fn property_initialized_at_constructor_exit(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        member: &ClassMemberSource,
    ) -> Result<bool, SourceFlowError> {
        let invalid = || SourceFlowInvariant::InvalidClassProperty(member.declaration);
        class_body_identities(store, host, &self.access).map_err(|_| invalid())?;
        if !matches!(self.body.kind, ClassBodyKind::Constructor)
            || member.declaring_class != self.body.class_symbol
            || member.side != ClassPropertySide::Instance
            || !matches!(
                member.origin,
                ClassMemberOrigin::Field { initializer: None }
                    | ClassMemberOrigin::AutoAccessor { initializer: None }
            )
            || class_member_source(store, host, member.symbol).map_err(|_| invalid())? != *member
        {
            return Err(invalid().into());
        }
        let Some(NodeData::PropertyDeclaration(property)) =
            host.node(member.declaration).map(|record| &record.data)
        else {
            return Err(invalid().into());
        };
        let name = NodeRef::new(
            member.declaration.arena,
            member.declaration.file,
            property.name,
        );
        let name = match host.node(name).map(|record| &record.data) {
            Some(NodeData::Identifier(name)) => &name.text,
            Some(NodeData::PrivateIdentifier(name)) => &name.text,
            _ => return Err(invalid().into()),
        };
        let flow = self
            .flow
            .graph
            .container_return(self.body.declaration)
            .ok_or_else(invalid)?;
        if self.flow.plan.end != Some(flow) {
            return Err(invalid().into());
        }
        let reference = ClassPropertyFlowReference {
            receiver: ClassPropertyFlowReceiver::This(self.body.class_declaration),
            name: name.clone(),
        };
        self.property_state_at(
            store,
            host,
            flow,
            &ClassPropertyFlowQuery {
                reference: &reference,
                member,
                initial: ClassPropertyFlowState {
                    type_: None,
                    initialized: false,
                },
            },
            &mut HashSet::new(),
            0,
        )
        .map(|state| state.initialized)
    }

    fn property_state_at(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        flow: FlowRef,
        query: &ClassPropertyFlowQuery<'_>,
        visiting: &mut HashSet<FlowRef>,
        depth: usize,
    ) -> Result<ClassPropertyFlowState, SourceFlowError> {
        if depth > FLOW_DEPTH_LIMIT {
            return Err(SourceFlowInvariant::DepthLimit(flow).into());
        }
        if !visiting.insert(flow) {
            return Err(SourceFlowInvariant::Cycle(flow).into());
        }
        let node = flow_node(self.flow.graph, flow)?;
        let result = match source_flow_kind(flow, node.flags)? {
            SourceFlowKind::Start => {
                validate_start_node(self.flow.plan, flow, &node)?;
                Ok(query.initial)
            }
            SourceFlowKind::Unreachable => {
                validate_unreachable_node(self.flow.graph, flow, &node)?;
                Ok(ClassPropertyFlowState {
                    initialized: true,
                    ..query.initial
                })
            }
            SourceFlowKind::Assignment => {
                let target = ast_payload(flow, &node)?;
                if let Some(assignment) = self.flow.plan.property_assignments.get(&target)
                    && &assignment.reference == query.reference
                {
                    if let Some(write) = &assignment.write {
                        let checked = self
                            .property_assignments
                            .get(&target)
                            .ok_or(SourceFlowInvariant::PendingAssignment(target))?;
                        if write.flow != flow
                            || checked.target().plan() != &write.plan
                            || checked.target().access_token() != &self.access
                            || checked.target().member_source() != query.member
                            || query
                                .initial
                                .type_
                                .is_some_and(|declared| declared != checked.target().read_type())
                            || store
                                .type_node_links(assignment.expression)
                                .and_then(|links| links.resolved_type)
                                != Some(checked.assigned_type())
                            || store.type_payload(checked.flow_type()).is_none()
                        {
                            return Err(SourceFlowInvariant::InvalidClassProperty(target).into());
                        }
                        Ok(ClassPropertyFlowState {
                            type_: query.initial.type_.map(|_| checked.flow_type()),
                            initialized: true,
                        })
                    } else {
                        if store
                            .type_node_links(assignment.expression)
                            .and_then(|links| links.resolved_type)
                            .is_none()
                        {
                            return Err(SourceFlowInvariant::PendingAssignment(target).into());
                        }
                        Ok(ClassPropertyFlowState {
                            initialized: true,
                            ..query.initial
                        })
                    }
                } else {
                    self.property_state_at(
                        store,
                        host,
                        linear_antecedent(flow, &node)?,
                        query,
                        visiting,
                        depth + 1,
                    )
                }
            }
            SourceFlowKind::Call => {
                let call = ast_payload(flow, &node)?;
                if let Some(NodeData::CallExpression(data)) = host.node(call).map(|node| &node.data)
                    && host
                        .node(NodeRef::new(call.arena, call.file, data.expression))
                        .is_some_and(|node| node.kind == SyntaxKind::SuperKeyword)
                    && !self.completed_calls.contains(&call)
                {
                    return Err(SourceFlowInvariant::InvalidCall(call).into());
                }
                self.property_state_at(
                    store,
                    host,
                    linear_antecedent(flow, &node)?,
                    query,
                    visiting,
                    depth + 1,
                )
            }
            SourceFlowKind::BranchLabel | SourceFlowKind::LoopLabel => {
                let mut result: Option<ClassPropertyFlowState> = None;
                for antecedent in label_antecedents(flow, &node)? {
                    let state = self.property_state_at(
                        store,
                        host,
                        *antecedent,
                        query,
                        visiting,
                        depth + 1,
                    )?;
                    if let Some(prior) = &mut result {
                        if prior.type_ != state.type_ {
                            return Err(SourceFlowUnsupported::FlowKind {
                                flow,
                                flags: node.flags,
                            }
                            .into());
                        }
                        prior.initialized &= state.initialized;
                    } else {
                        result = Some(state);
                    }
                }
                Ok(result.unwrap_or(ClassPropertyFlowState {
                    initialized: true,
                    ..query.initial
                }))
            }
            SourceFlowKind::TrueCondition | SourceFlowKind::FalseCondition => {
                Err(SourceFlowUnsupported::FlowKind {
                    flow,
                    flags: node.flags,
                }
                .into())
            }
        };
        visiting.remove(&flow);
        result
    }
}

pub(super) fn class_property_type_skips_initialization_check(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<bool, SourceFlowError> {
    class_type_has_uninitialized_value(store, type_, &mut HashSet::new())
}

fn class_type_has_uninitialized_value(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    visiting: &mut HashSet<TypeId>,
) -> Result<bool, SourceFlowError> {
    let invalid =
        SourceFlowInvariant::TypeofNarrowing(SourceTypeofNarrowingError::InvalidType(type_));
    if !visiting.insert(type_) {
        return Err(invalid.into());
    }
    let record = store.type_payload(type_).ok_or(invalid)?;
    let result = if record
        .flags()
        .intersects(TypeFlags::UNDEFINED | TypeFlags::ANY | TypeFlags::UNKNOWN)
    {
        true
    } else if let TypeData::Union(union) = record.data() {
        let mut contains = false;
        for type_ in &union.union.types {
            contains |= class_type_has_uninitialized_value(store, *type_, visiting)?;
        }
        contains
    } else {
        false
    };
    visiting.remove(&type_);
    Ok(result)
}

impl SourceFlowFrame<'_, '_> {
    /// Returns the immutable current-type map at one cold-preflighted AST
    /// point, memoizing completed flow nodes for the rest of this invocation.
    pub(super) fn snapshot_at(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        node: NodeRef,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        let flow = self
            .plan
            .points
            .get(&node)
            .copied()
            .ok_or(SourceFlowInvariant::MissingFlowPoint(node))?;
        self.resolve_flow(store, globals, flow, 0)
    }

    /// Makes the assignment flow created after an initializer executable.
    /// The caller passes the post-assignment current type, not the local's
    /// declared symbol type.
    pub(super) fn complete_assignment(
        &mut self,
        declaration: NodeRef,
        symbol: SemanticSymbolId,
        current_type: TypeId,
    ) -> Result<(), SourceFlowError> {
        let planned = self
            .plan
            .assignments
            .get(&declaration)
            .ok_or(SourceFlowInvariant::UnknownAssignment(declaration))?;
        if planned.symbol != symbol {
            return Err(SourceFlowInvariant::AssignmentSymbolMismatch {
                declaration,
                expected: planned.symbol,
                actual: symbol,
            }
            .into());
        }
        let state = self
            .assignment_states
            .get_mut(&declaration)
            .ok_or(SourceFlowInvariant::UnknownAssignment(declaration))?;
        match state {
            SourceFlowAssignmentState::Pending => {
                *state = SourceFlowAssignmentState::Resolved(current_type);
                Ok(())
            }
            SourceFlowAssignmentState::Resolved(_) => {
                Err(SourceFlowInvariant::AssignmentAlreadyCompleted(declaration).into())
            }
        }
    }

    fn resolve_flow(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        flow: FlowRef,
        depth: usize,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        if let Some(snapshot) = self.loop_snapshots.get(&flow) {
            return Ok(snapshot.clone());
        }
        if let Some(snapshot) = self.memo.get(&flow) {
            return Ok(snapshot.clone());
        }
        if depth > FLOW_DEPTH_LIMIT {
            return Err(SourceFlowInvariant::DepthLimit(flow).into());
        }
        if !self.visiting.insert(flow) {
            return Err(SourceFlowInvariant::Cycle(flow).into());
        }
        let result = self.resolve_flow_uncached(store, globals, flow, depth);
        let removed = self.visiting.remove(&flow);
        debug_assert!(removed);
        if let Ok(snapshot) = &result
            && self.loop_snapshots.is_empty()
        {
            self.memo.insert(flow, snapshot.clone());
        }
        result
    }

    fn resolve_flow_uncached(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        flow: FlowRef,
        depth: usize,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        let node = flow_node(self.graph, flow)?;
        match source_flow_kind(flow, node.flags)? {
            SourceFlowKind::Unreachable => {
                validate_unreachable_node(self.graph, flow, &node)?;
                Ok(self.base.clone())
            }
            SourceFlowKind::Start => {
                validate_start_node(self.plan, flow, &node)?;
                Ok(self.base.clone())
            }
            SourceFlowKind::Assignment => {
                let antecedent = linear_antecedent(flow, &node)?;
                let declaration = ast_payload(flow, &node)?;
                if self.plan.property_assignments.contains_key(&declaration) {
                    return self.resolve_flow(store, globals, antecedent, depth + 1);
                }
                let assignment = *self
                    .plan
                    .assignments
                    .get(&declaration)
                    .ok_or(SourceFlowInvariant::UnknownAssignment(declaration))?;
                let prior = self.resolve_flow(store, globals, antecedent, depth + 1)?;
                let current_type = match self.assignment_states.get(&declaration) {
                    Some(SourceFlowAssignmentState::Resolved(type_)) => *type_,
                    Some(SourceFlowAssignmentState::Pending) => {
                        return Err(SourceFlowInvariant::PendingAssignment(declaration).into());
                    }
                    None => {
                        return Err(SourceFlowInvariant::UnknownAssignment(declaration).into());
                    }
                };
                Ok(prior.with_type(assignment.symbol, current_type))
            }
            SourceFlowKind::Call => {
                let antecedent = linear_antecedent(flow, &node)?;
                let call = ast_payload(flow, &node)?;
                let statement = self
                    .plan
                    .calls
                    .get(&call)
                    .copied()
                    .ok_or(SourceFlowUnsupported::Call(call))?;
                validate_planned_call_container(
                    self.bound, self.plan, call, statement, antecedent,
                )?;
                self.resolve_flow(store, globals, antecedent, depth + 1)
            }
            kind @ (SourceFlowKind::TrueCondition | SourceFlowKind::FalseCondition) => {
                let antecedent = linear_antecedent(flow, &node)?;
                let condition_node = ast_payload(flow, &node)?;
                let condition = *self
                    .plan
                    .conditions
                    .get(&condition_node)
                    .ok_or(SourceFlowInvariant::UnknownCondition(condition_node))?;
                let prior = self.resolve_flow(store, globals, antecedent, depth + 1)?;
                let current = prior
                    .type_of(condition.symbol())
                    .ok_or(SourceFlowInvariant::MissingCurrentType(condition.symbol()))?;
                let assume_true = match kind {
                    SourceFlowKind::TrueCondition => true,
                    SourceFlowKind::FalseCondition => false,
                    SourceFlowKind::Unreachable
                    | SourceFlowKind::Start
                    | SourceFlowKind::Assignment
                    | SourceFlowKind::Call
                    | SourceFlowKind::BranchLabel
                    | SourceFlowKind::LoopLabel => unreachable!(),
                };
                let narrowed = match condition {
                    SourceFlowCondition::Truthiness(_) => narrow_by_truthiness(
                        store,
                        Some(globals),
                        current,
                        if assume_true {
                            TruthinessAssumption::Truthy
                        } else {
                            TruthinessAssumption::Falsy
                        },
                    )
                    .map_err(|error| SourceFlowError::Narrowing {
                        condition: condition_node,
                        error,
                    })?,
                    SourceFlowCondition::Typeof(condition) => narrow_by_typeof(
                        store,
                        globals,
                        current,
                        condition.tag,
                        assume_true
                            == matches!(condition.comparison, SourceTypeofComparison::Equal),
                    )
                    .map_err(|error| match error {
                        SourceTypeofNarrowingError::Union(error) => {
                            SourceFlowError::Join { flow, error }
                        }
                        error => {
                            SourceFlowError::Invariant(SourceFlowInvariant::TypeofNarrowing(error))
                        }
                    })?,
                    SourceFlowCondition::Equality(condition) => {
                        let value = store
                            .type_node_links(condition.value)
                            .and_then(|links| links.resolved_type)
                            .ok_or(SourceFlowError::Invariant(
                                SourceFlowInvariant::EqualityNarrowing(
                                    SourceEqualityNarrowingError::MissingValue(condition.value),
                                ),
                            ))?;
                        let discriminant = condition
                            .discriminant
                            .map(|access| {
                                store
                                    .symbol_node_links(access)
                                    .and_then(|links| links.resolved_symbol)
                                    .and_then(|symbol| store.symbol(symbol))
                                    .and_then(|symbol| symbol.name().as_utf8())
                                    .map(str::to_owned)
                                    .ok_or(SourceEqualityNarrowingError::InvalidDiscriminant(
                                        access,
                                    ))
                            })
                            .transpose()
                            .map_err(|error| {
                                SourceFlowError::Invariant(SourceFlowInvariant::EqualityNarrowing(
                                    error,
                                ))
                            })?;
                        narrow_by_equality(
                            store,
                            globals,
                            current,
                            value,
                            condition.strict,
                            assume_true
                                == matches!(condition.comparison, SourceTypeofComparison::Equal),
                            discriminant.as_deref(),
                        )
                        .map_err(|error| match error {
                            SourceEqualityNarrowingError::Union(error) => {
                                SourceFlowError::Join { flow, error }
                            }
                            error => SourceFlowError::Invariant(
                                SourceFlowInvariant::EqualityNarrowing(error),
                            ),
                        })?
                    }
                };
                Ok(prior.with_type(condition.symbol(), narrowed))
            }
            SourceFlowKind::BranchLabel => {
                self.resolve_branch_label(store, globals, flow, &node, depth)
            }
            SourceFlowKind::LoopLabel => {
                self.resolve_loop_label(store, globals, flow, &node, depth)
            }
        }
    }

    fn resolve_branch_label(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        flow: FlowRef,
        node: &FlowNode,
        depth: usize,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        let antecedents = label_antecedents(flow, node)?;
        let mut joined = self.resolve_flow(store, globals, antecedents[0], depth + 1)?;
        for antecedent in &antecedents[1..] {
            let next = self.resolve_flow(store, globals, *antecedent, depth + 1)?;
            joined = self.join_snapshots(store, globals, flow, &joined, &next)?;
        }
        Ok(joined)
    }

    fn resolve_loop_label(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        flow: FlowRef,
        node: &FlowNode,
        depth: usize,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        let antecedents = label_antecedents(flow, node)?;
        let mut current = self.resolve_flow(store, globals, antecedents[0], depth + 1)?;
        let previous = self.loop_snapshots.insert(flow, current.clone());
        debug_assert!(previous.is_none());

        let result = (|| {
            for antecedent in &antecedents[1..] {
                let next = self.resolve_flow(store, globals, *antecedent, depth + 1)?;
                current = self.join_snapshots(store, globals, flow, &current, &next)?;
                self.loop_snapshots.insert(flow, current.clone());
            }
            Ok(current)
        })();
        let removed = self.loop_snapshots.remove(&flow);
        debug_assert!(removed.is_some());
        result
    }

    fn join_snapshots(
        &self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        flow: FlowRef,
        then_snapshot: &SourceFlowSnapshot,
        else_snapshot: &SourceFlowSnapshot,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        let mut symbols = then_snapshot
            .types()
            .keys()
            .filter(|symbol| else_snapshot.types().contains_key(symbol))
            .copied()
            .collect::<Vec<_>>();
        symbols.sort_unstable();

        let mut joined = SourceFlowTypes::with_capacity(symbols.len());
        for symbol in symbols {
            let (Some(then_type), Some(else_type)) =
                (then_snapshot.type_of(symbol), else_snapshot.type_of(symbol))
            else {
                return Err(SourceFlowInvariant::MissingCurrentType(symbol).into());
            };
            let candidates = self.join_identity_candidates(symbol);
            let joined_type = if then_type == else_type {
                then_type
            } else if let Some(candidate) = candidates
                .iter()
                .copied()
                .find(|candidate| *candidate == then_type || *candidate == else_type)
            {
                candidate
            } else {
                let anonymous = store
                    .expression_union_type_with_global_types(
                        globals,
                        &[then_type, else_type],
                        UnionReduction::Literal,
                    )
                    .map_err(|error| SourceFlowError::Join { flow, error })?;
                Self::preferred_join_identity(store, anonymous, &candidates)
            };
            joined.insert(symbol, joined_type);
        }
        Ok(SourceFlowSnapshot::new(joined))
    }

    fn join_identity_candidates(&self, symbol: SemanticSymbolId) -> Vec<TypeId> {
        let mut candidates = Vec::new();
        if let Some(base) = self.base.type_of(symbol) {
            candidates.push(base);
        }
        for declaration in &self.plan.assignment_order {
            let Some(assignment) = self.plan.assignments.get(declaration) else {
                continue;
            };
            if assignment.symbol != symbol {
                continue;
            }
            if let Some(SourceFlowAssignmentState::Resolved(type_)) =
                self.assignment_states.get(declaration)
            {
                candidates.push(*type_);
            }
        }
        candidates
    }

    fn preferred_join_identity(
        store: &CanonicalTypeMapperStore,
        anonymous: TypeId,
        candidates: &[TypeId],
    ) -> TypeId {
        let Some(anonymous_types) = union_constituents(store, anonymous) else {
            return anonymous;
        };
        candidates
            .iter()
            .copied()
            .find(|candidate| union_constituents(store, *candidate) == Some(anonymous_types))
            .unwrap_or(anonymous)
    }
}

/// Confirms that `typeof` can classify canonical top types, authenticated
/// branded primitives, and every union leaf without general relation queries.
pub(super) fn source_typeof_narrowing_type_is_supported(
    store: &CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    type_: TypeId,
    tag: SourceTypeofTag,
) -> Result<bool, SourceTypeofNarrowingError> {
    let mut leaves = Vec::new();
    collect_source_typeof_leaves(store, type_, &mut leaves, &mut HashSet::new())?;
    for leaf in leaves {
        match source_typeof_leaf_matches(store, globals, leaf, tag) {
            Ok(_) => {}
            Err(SourceTypeofNarrowingError::UnsupportedType(_)) => return Ok(false),
            Err(error) => return Err(error),
        }
    }
    Ok(true)
}

pub(super) fn narrow_by_typeof(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    type_: TypeId,
    tag: SourceTypeofTag,
    require_match: bool,
) -> Result<TypeId, SourceTypeofNarrowingError> {
    let mut leaves = Vec::new();
    collect_source_typeof_leaves(store, type_, &mut leaves, &mut HashSet::new())?;
    let mut retained = Vec::with_capacity(leaves.len());
    for leaf in &leaves {
        let record = store
            .type_payload(*leaf)
            .ok_or(SourceTypeofNarrowingError::InvalidType(*leaf))?;
        if record.flags().intersects(TypeFlags::NEVER) {
            retained.push(*leaf);
            continue;
        }
        let flags = record.flags();
        match source_typeof_leaf_matches(store, globals, *leaf, tag)? {
            SourceTypeofLeafMatch::Exact(matches) if matches == require_match => {
                let retained_leaf = if require_match
                    && matches!(tag, SourceTypeofTag::Undefined)
                    && flags.intersects(TypeFlags::VOID)
                {
                    store
                        .intrinsic_bootstrap()
                        .map(|bootstrap| bootstrap.undefined_type)
                        .ok_or(SourceTypeofNarrowingError::MissingBootstrap)?
                } else {
                    *leaf
                };
                retained.push(retained_leaf);
            }
            SourceTypeofLeafMatch::Exact(_)
                if require_match
                    && matches!(tag, SourceTypeofTag::Function)
                    && flags.intersects(TypeFlags::NON_PRIMITIVE) =>
            {
                retained.push(globals.function_type);
            }
            SourceTypeofLeafMatch::Exact(_) => {}
            kind @ (SourceTypeofLeafMatch::Any
            | SourceTypeofLeafMatch::Unknown
            | SourceTypeofLeafMatch::NonNullableUnknown) => {
                append_narrowed_source_typeof_top(
                    store,
                    globals,
                    *leaf,
                    kind,
                    tag,
                    require_match,
                    &mut retained,
                )?;
            }
        }
    }
    if retained == leaves {
        return Ok(type_);
    }
    if retained.is_empty() {
        return store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.never_type)
            .ok_or(SourceTypeofNarrowingError::MissingBootstrap);
    }
    if let [only] = retained.as_slice() {
        return Ok(*only);
    }
    store
        .expression_union_type_with_global_types(globals, &retained, UnionReduction::Literal)
        .map_err(SourceTypeofNarrowingError::Union)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceEqualityValueKind {
    Null,
    Undefined,
    Literal(TypeId),
}

/// Narrows exact nullable or literal comparisons without synthesizing facts.
pub(super) fn narrow_by_equality(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    input: TypeId,
    value: TypeId,
    strict: bool,
    require_match: bool,
    discriminant: Option<&str>,
) -> Result<TypeId, SourceEqualityNarrowingError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceEqualityNarrowingError::MissingBootstrap)?;
    let (any, unknown, non_nullable, undefined, null, never, strict_null_checks) = (
        bootstrap.any_type,
        bootstrap.unknown_type,
        bootstrap.unknown_empty_object_type,
        bootstrap.undefined_type,
        bootstrap.null_type,
        bootstrap.never_type,
        bootstrap.options.strict_null_checks,
    );
    let value_kind = source_equality_value_kind(store, value)?;
    if !strict_null_checks
        && matches!(
            value_kind,
            SourceEqualityValueKind::Null | SourceEqualityValueKind::Undefined
        )
    {
        return Ok(input);
    }
    if !strict && matches!(value_kind, SourceEqualityValueKind::Literal(_)) {
        return Err(SourceEqualityNarrowingError::UnsupportedType(value));
    }

    let mut leaves = Vec::new();
    collect_source_equality_leaves(store, input, &mut leaves, &mut HashSet::new())?;
    let mut retained = Vec::with_capacity(leaves.len());
    for leaf in &leaves {
        let flags = store
            .type_payload(*leaf)
            .map(TypeRecord::flags)
            .ok_or(SourceEqualityNarrowingError::InvalidType(*leaf))?;
        if flags.intersects(TypeFlags::NEVER) {
            retained.push(*leaf);
            continue;
        }
        if *leaf == any {
            retained.push(*leaf);
            continue;
        }
        if flags.intersects(TypeFlags::ANY) {
            return Err(SourceEqualityNarrowingError::UnsupportedType(*leaf));
        }

        if let Some(name) = discriminant {
            if !flags.intersects(TypeFlags::OBJECT) {
                return Err(SourceEqualityNarrowingError::UnsupportedType(*leaf));
            }
            let property = store
                .resolved_own_property(*leaf, name)
                .map_err(SourceEqualityNarrowingError::Relation)?
                .ok_or(SourceEqualityNarrowingError::UnsupportedType(*leaf))?;
            let property_type = if property.optional && strict_null_checks {
                store
                    .expression_union_type_with_global_types(
                        globals,
                        &[property.type_, undefined],
                        UnionReduction::Literal,
                    )
                    .map_err(SourceEqualityNarrowingError::Union)?
            } else {
                property.type_
            };
            let narrowed = narrow_by_equality(
                store,
                globals,
                property_type,
                value,
                strict,
                require_match,
                None,
            )?;
            if narrowed != never {
                retained.push(*leaf);
            }
            continue;
        }

        if *leaf == unknown {
            match value_kind {
                SourceEqualityValueKind::Null | SourceEqualityValueKind::Undefined => {
                    if require_match {
                        if strict {
                            retained.push(if value_kind == SourceEqualityValueKind::Null {
                                null
                            } else {
                                undefined
                            });
                        } else {
                            retained.extend([null, undefined]);
                        }
                    } else if strict {
                        retained.push(non_nullable);
                        retained.push(if value_kind == SourceEqualityValueKind::Null {
                            undefined
                        } else {
                            null
                        });
                    } else {
                        retained.push(non_nullable);
                    }
                }
                SourceEqualityValueKind::Literal(literal) if require_match => {
                    retained.push(literal);
                }
                SourceEqualityValueKind::Literal(_) => retained.push(*leaf),
            }
            continue;
        }
        if *leaf == non_nullable {
            match value_kind {
                SourceEqualityValueKind::Null | SourceEqualityValueKind::Undefined => {
                    if !require_match {
                        retained.push(*leaf);
                    }
                }
                SourceEqualityValueKind::Literal(literal) if require_match => {
                    retained.push(literal);
                }
                SourceEqualityValueKind::Literal(_) => retained.push(*leaf),
            }
            continue;
        }

        let matched = match value_kind {
            SourceEqualityValueKind::Null => {
                if strict {
                    flags.intersects(TypeFlags::NULL)
                } else {
                    flags.intersects(TypeFlags::NULL | TypeFlags::VOID_LIKE)
                }
            }
            SourceEqualityValueKind::Undefined => {
                if strict {
                    flags.intersects(TypeFlags::VOID_LIKE)
                } else {
                    flags.intersects(TypeFlags::NULL | TypeFlags::VOID_LIKE)
                }
            }
            SourceEqualityValueKind::Literal(literal) => {
                source_equality_literal_matches(store, globals, *leaf, literal)?
            }
        };
        if matches!(value_kind, SourceEqualityValueKind::Literal(_))
            && !require_match
            && matched
            && !source_equality_is_unit_like(store, *leaf)?
        {
            retained.push(*leaf);
            continue;
        }
        if matched != require_match {
            continue;
        }
        let narrowed = match value_kind {
            SourceEqualityValueKind::Undefined
                if require_match && strict && flags.intersects(TypeFlags::VOID) =>
            {
                undefined
            }
            SourceEqualityValueKind::Literal(literal)
                if require_match && source_equality_is_wide_primitive(flags) =>
            {
                literal
            }
            _ => *leaf,
        };
        if !retained.contains(&narrowed) {
            retained.push(narrowed);
        }
    }

    if retained == leaves {
        return Ok(input);
    }
    match retained.as_slice() {
        [] => Ok(never),
        [only] => Ok(*only),
        _ => store
            .expression_union_type_with_global_types(globals, &retained, UnionReduction::Literal)
            .map_err(SourceEqualityNarrowingError::Union),
    }
}

fn source_equality_value_kind(
    store: &CanonicalTypeMapperStore,
    value: TypeId,
) -> Result<SourceEqualityValueKind, SourceEqualityNarrowingError> {
    let record = store
        .type_payload(value)
        .ok_or(SourceEqualityNarrowingError::InvalidType(value))?;
    let flags = record.flags();
    if flags.intersects(TypeFlags::NULL) {
        return Ok(SourceEqualityValueKind::Null);
    }
    if flags.intersects(TypeFlags::VOID_LIKE) {
        return Ok(SourceEqualityValueKind::Undefined);
    }
    let TypeData::Literal(literal) = record.data() else {
        return Err(SourceEqualityNarrowingError::UnsupportedType(value));
    };
    if !flags.intersects(
        TypeFlags::STRING_LITERAL
            | TypeFlags::NUMBER_LITERAL
            | TypeFlags::BOOLEAN_LITERAL
            | TypeFlags::BIG_INT_LITERAL,
    ) {
        return Err(SourceEqualityNarrowingError::UnsupportedType(value));
    }
    let regular = store
        .type_payload(literal.regular_type)
        .ok_or(SourceEqualityNarrowingError::InvalidType(value))?;
    if !matches!(regular.data(), TypeData::Literal(regular) if regular.value == literal.value) {
        return Err(SourceEqualityNarrowingError::InvalidType(value));
    }
    Ok(SourceEqualityValueKind::Literal(literal.regular_type))
}

fn collect_source_equality_leaves(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    leaves: &mut Vec<TypeId>,
    visiting: &mut HashSet<TypeId>,
) -> Result<(), SourceEqualityNarrowingError> {
    let record = store
        .type_payload(type_)
        .ok_or(SourceEqualityNarrowingError::InvalidType(type_))?;
    if !record.flags().intersects(TypeFlags::UNION) {
        if matches!(record.data(), TypeData::Union(_)) {
            return Err(SourceEqualityNarrowingError::InvalidType(type_));
        }
        leaves.push(type_);
        return Ok(());
    }
    if !visiting.insert(type_) {
        return Err(SourceEqualityNarrowingError::InvalidType(type_));
    }
    let TypeData::Union(union) = record.data() else {
        return Err(SourceEqualityNarrowingError::InvalidType(type_));
    };
    for constituent in &union.union.types {
        collect_source_equality_leaves(store, *constituent, leaves, visiting)?;
    }
    visiting.remove(&type_);
    Ok(())
}

fn source_equality_is_wide_primitive(flags: TypeFlags) -> bool {
    flags
        .intersects(TypeFlags::STRING | TypeFlags::NUMBER | TypeFlags::BIG_INT | TypeFlags::BOOLEAN)
        && !flags.intersects(
            TypeFlags::STRING_LITERAL
                | TypeFlags::NUMBER_LITERAL
                | TypeFlags::BOOLEAN_LITERAL
                | TypeFlags::BIG_INT_LITERAL,
        )
}

fn source_equality_is_unit_like(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<bool, SourceEqualityNarrowingError> {
    let record = store
        .type_payload(type_)
        .ok_or(SourceEqualityNarrowingError::InvalidType(type_))?;
    match record.data() {
        TypeData::Literal(_) => Ok(true),
        TypeData::Intersection(intersection) => {
            intersection
                .intersection
                .types
                .iter()
                .try_fold(false, |found, constituent| {
                    store
                        .type_payload(*constituent)
                        .map(|record| found || matches!(record.data(), TypeData::Literal(_)))
                        .ok_or(SourceEqualityNarrowingError::InvalidType(*constituent))
                })
        }
        _ => Ok(false),
    }
}

fn source_equality_literal_matches(
    store: &CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    candidate: TypeId,
    expected: TypeId,
) -> Result<bool, SourceEqualityNarrowingError> {
    let candidate_record = store
        .type_payload(candidate)
        .ok_or(SourceEqualityNarrowingError::InvalidType(candidate))?;
    let expected_record = store
        .type_payload(expected)
        .ok_or(SourceEqualityNarrowingError::InvalidType(expected))?;
    let expected_flags = expected_record.flags();
    if let TypeData::Literal(actual) = candidate_record.data() {
        let TypeData::Literal(wanted) = expected_record.data() else {
            return Err(SourceEqualityNarrowingError::InvalidType(expected));
        };
        return Ok(actual.value == wanted.value);
    }
    let candidate_flags = candidate_record.flags();
    if candidate_flags.intersects(TypeFlags::INTERSECTION) {
        let tag = match expected_record.data() {
            TypeData::Literal(literal) => match &literal.value {
                LiteralValue::String(_) => SourceTypeofTag::String,
                LiteralValue::Number(_) => SourceTypeofTag::Number,
                LiteralValue::Boolean(_) => SourceTypeofTag::Boolean,
                LiteralValue::BigInt(_) => SourceTypeofTag::BigInt,
                LiteralValue::ComputedEnum => {
                    return Err(SourceEqualityNarrowingError::UnsupportedType(expected));
                }
            },
            _ => return Err(SourceEqualityNarrowingError::InvalidType(expected)),
        };
        let SourceTypeofLeafMatch::Exact(matches) =
            source_typeof_branded_intersection_matches(store, globals, candidate, tag)
                .map_err(|_| SourceEqualityNarrowingError::UnsupportedType(candidate))?
        else {
            return Err(SourceEqualityNarrowingError::UnsupportedType(candidate));
        };
        if !matches {
            return Ok(false);
        }
        let TypeData::Intersection(intersection) = candidate_record.data() else {
            return Err(SourceEqualityNarrowingError::InvalidType(candidate));
        };
        let primitive = intersection
            .intersection
            .types
            .iter()
            .find_map(|constituent| {
                store
                    .type_payload(*constituent)
                    .and_then(|record| match record.data() {
                        TypeData::Literal(literal) => Some(&literal.value),
                        _ => None,
                    })
            });
        return Ok(primitive.is_none_or(|actual| {
            matches!(expected_record.data(), TypeData::Literal(wanted) if *actual == wanted.value)
        }));
    }
    Ok(candidate_flags.intersects(TypeFlags::STRING_LIKE)
        && expected_flags.intersects(TypeFlags::STRING_LITERAL)
        || candidate_flags.intersects(TypeFlags::NUMBER_LIKE)
            && expected_flags.intersects(TypeFlags::NUMBER_LITERAL)
        || candidate_flags.intersects(TypeFlags::BOOLEAN_LIKE)
            && expected_flags.intersects(TypeFlags::BOOLEAN_LITERAL)
        || candidate_flags.intersects(TypeFlags::BIG_INT_LIKE)
            && expected_flags.intersects(TypeFlags::BIG_INT_LITERAL))
}

fn append_narrowed_source_typeof_top(
    store: &CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    original: TypeId,
    kind: SourceTypeofLeafMatch,
    tag: SourceTypeofTag,
    require_match: bool,
    retained: &mut Vec<TypeId>,
) -> Result<(), SourceTypeofNarrowingError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceTypeofNarrowingError::MissingBootstrap)?;
    if !require_match {
        if kind == SourceTypeofLeafMatch::Unknown && bootstrap.options.strict_null_checks {
            match tag {
                SourceTypeofTag::Object => {
                    retained.extend([
                        bootstrap.unknown_empty_object_type,
                        bootstrap.undefined_type,
                    ]);
                    return Ok(());
                }
                SourceTypeofTag::Undefined => {
                    retained.extend([bootstrap.unknown_empty_object_type, bootstrap.null_type]);
                    return Ok(());
                }
                _ => {}
            }
        }
        retained.push(original);
        return Ok(());
    }

    let narrowed = match tag {
        SourceTypeofTag::String => bootstrap.string_type,
        SourceTypeofTag::Number => bootstrap.number_type,
        SourceTypeofTag::Boolean => bootstrap.boolean_type,
        SourceTypeofTag::BigInt => bootstrap.bigint_type,
        SourceTypeofTag::Symbol => bootstrap.es_symbol_type,
        SourceTypeofTag::Undefined
            if kind == SourceTypeofLeafMatch::NonNullableUnknown
                && bootstrap.options.strict_null_checks =>
        {
            return Ok(());
        }
        SourceTypeofTag::Undefined => bootstrap.undefined_type,
        SourceTypeofTag::Object | SourceTypeofTag::Function
            if kind == SourceTypeofLeafMatch::Any =>
        {
            original
        }
        SourceTypeofTag::Object => {
            retained.push(bootstrap.non_primitive_type);
            if kind == SourceTypeofLeafMatch::Unknown && bootstrap.options.strict_null_checks {
                retained.push(bootstrap.null_type);
            }
            return Ok(());
        }
        SourceTypeofTag::Function => globals.function_type,
    };
    retained.push(narrowed);
    Ok(())
}

fn collect_source_typeof_leaves(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    leaves: &mut Vec<TypeId>,
    visiting: &mut HashSet<TypeId>,
) -> Result<(), SourceTypeofNarrowingError> {
    let record = store
        .type_payload(type_)
        .ok_or(SourceTypeofNarrowingError::InvalidType(type_))?;
    if !record.flags().intersects(TypeFlags::UNION) {
        if matches!(record.data(), TypeData::Union(_)) {
            return Err(SourceTypeofNarrowingError::InvalidUnion(type_));
        }
        leaves.push(type_);
        return Ok(());
    }
    if !visiting.insert(type_) {
        return Err(SourceTypeofNarrowingError::CyclicUnion(type_));
    }
    let TypeData::Union(union) = record.data() else {
        return Err(SourceTypeofNarrowingError::InvalidUnion(type_));
    };
    for constituent in &union.union.types {
        collect_source_typeof_leaves(store, *constituent, leaves, visiting)?;
    }
    visiting.remove(&type_);
    Ok(())
}

fn source_typeof_leaf_matches(
    store: &CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    type_: TypeId,
    tag: SourceTypeofTag,
) -> Result<SourceTypeofLeafMatch, SourceTypeofNarrowingError> {
    let record = store
        .type_payload(type_)
        .ok_or(SourceTypeofNarrowingError::InvalidType(type_))?;
    let flags = record.flags();
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceTypeofNarrowingError::MissingBootstrap)?;
    if flags.intersects(TypeFlags::ANY) {
        return if type_ == bootstrap.any_type {
            Ok(SourceTypeofLeafMatch::Any)
        } else {
            Err(SourceTypeofNarrowingError::UnsupportedType(type_))
        };
    }
    if flags.intersects(TypeFlags::UNKNOWN) {
        return if type_ == bootstrap.unknown_type {
            Ok(SourceTypeofLeafMatch::Unknown)
        } else {
            Err(SourceTypeofNarrowingError::UnsupportedType(type_))
        };
    }
    if type_ == globals.function_type || type_ == bootstrap.any_function_type {
        return Ok(SourceTypeofLeafMatch::Exact(matches!(
            tag,
            SourceTypeofTag::Function
        )));
    }
    if type_ == bootstrap.unknown_empty_object_type
        || type_ == bootstrap.empty_object_type
        || type_ == bootstrap.empty_type_literal_type
    {
        return Ok(SourceTypeofLeafMatch::NonNullableUnknown);
    }
    if flags.intersects(TypeFlags::INTERSECTION) {
        return source_typeof_branded_intersection_matches(store, globals, type_, tag);
    }
    if flags.intersects(
        TypeFlags::TYPE_PARAMETER
            | TypeFlags::INDEX
            | TypeFlags::INDEXED_ACCESS
            | TypeFlags::CONDITIONAL
            | TypeFlags::SUBSTITUTION,
    ) {
        return Err(SourceTypeofNarrowingError::UnsupportedType(type_));
    }
    if flags.intersects(TypeFlags::UNION) {
        return Err(SourceTypeofNarrowingError::InvalidUnion(type_));
    }

    let function_object = if flags.intersects(TypeFlags::OBJECT) {
        let known_function = store
            .intrinsic_bootstrap()
            .map(|bootstrap| type_ == globals.function_type || type_ == bootstrap.any_function_type)
            .ok_or(SourceTypeofNarrowingError::MissingBootstrap)?;
        if !known_function
            && !record
                .object_flags()
                .intersects(ObjectFlags::MEMBERS_RESOLVED)
        {
            return Err(SourceTypeofNarrowingError::UnsupportedType(type_));
        }
        if source_typeof_is_unbounded_empty_object(store, globals, type_, record)? {
            return Err(SourceTypeofNarrowingError::UnsupportedType(type_));
        }
        if matches!(tag, SourceTypeofTag::Object | SourceTypeofTag::Function) {
            Some(source_typeof_object_is_function(
                store, globals, type_, record,
            )?)
        } else {
            None
        }
    } else {
        None
    };
    let matched = match tag {
        SourceTypeofTag::String => flags.intersects(TypeFlags::STRING_LIKE),
        SourceTypeofTag::Number => flags.intersects(TypeFlags::NUMBER_LIKE),
        SourceTypeofTag::Boolean => flags.intersects(TypeFlags::BOOLEAN_LIKE),
        SourceTypeofTag::BigInt => flags.intersects(TypeFlags::BIG_INT_LIKE),
        SourceTypeofTag::Symbol => flags.intersects(TypeFlags::ES_SYMBOL_LIKE),
        SourceTypeofTag::Undefined => flags.intersects(TypeFlags::VOID_LIKE),
        SourceTypeofTag::Object => {
            flags.intersects(TypeFlags::NULL | TypeFlags::NON_PRIMITIVE)
                || function_object == Some(false)
        }
        SourceTypeofTag::Function => function_object == Some(true),
    };
    let classifiable = flags.intersects(
        TypeFlags::NEVER
            | TypeFlags::STRING_LIKE
            | TypeFlags::NUMBER_LIKE
            | TypeFlags::BIG_INT_LIKE
            | TypeFlags::BOOLEAN_LIKE
            | TypeFlags::ES_SYMBOL_LIKE
            | TypeFlags::VOID_LIKE
            | TypeFlags::NULL
            | TypeFlags::NON_PRIMITIVE
            | TypeFlags::OBJECT,
    );
    if !classifiable {
        return Err(SourceTypeofNarrowingError::UnsupportedType(type_));
    }
    Ok(SourceTypeofLeafMatch::Exact(matched))
}

fn source_typeof_branded_intersection_matches(
    store: &CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    type_: TypeId,
    tag: SourceTypeofTag,
) -> Result<SourceTypeofLeafMatch, SourceTypeofNarrowingError> {
    let record = store
        .type_payload(type_)
        .ok_or(SourceTypeofNarrowingError::InvalidType(type_))?;
    let constituents = if record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
    {
        store
            .validate_intersection_type(type_)
            .map(|projection| projection.types)
    } else {
        store
            .validate_deferred_intersection_type(type_)
            .map(|projection| projection.types)
    }
    .map_err(|_| SourceTypeofNarrowingError::UnsupportedType(type_))?;

    let primitive_flags = TypeFlags::STRING_LIKE
        | TypeFlags::NUMBER_LIKE
        | TypeFlags::BIG_INT_LIKE
        | TypeFlags::BOOLEAN_LIKE
        | TypeFlags::ES_SYMBOL_LIKE;
    let mut matched = None;
    for constituent in constituents {
        let constituent_record = store
            .type_payload(constituent)
            .ok_or(SourceTypeofNarrowingError::InvalidType(constituent))?;
        let flags = constituent_record.flags();
        if flags.intersects(primitive_flags) {
            let SourceTypeofLeafMatch::Exact(candidate) =
                source_typeof_leaf_matches(store, globals, constituent, tag)?
            else {
                return Err(SourceTypeofNarrowingError::UnsupportedType(type_));
            };
            if matched.is_some_and(|previous| previous != candidate) {
                return Err(SourceTypeofNarrowingError::UnsupportedType(type_));
            }
            matched = Some(candidate);
        } else if !flags
            .intersects(TypeFlags::OBJECT | TypeFlags::NON_PRIMITIVE | TypeFlags::TYPE_PARAMETER)
        {
            return Err(SourceTypeofNarrowingError::UnsupportedType(type_));
        }
    }
    matched
        .map(SourceTypeofLeafMatch::Exact)
        .ok_or(SourceTypeofNarrowingError::UnsupportedType(type_))
}

fn source_typeof_is_unbounded_empty_object(
    store: &CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    type_: TypeId,
    record: &TypeRecord,
) -> Result<bool, SourceTypeofNarrowingError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceTypeofNarrowingError::MissingBootstrap)?;
    if type_ == globals.function_type || type_ == bootstrap.any_function_type {
        return Ok(false);
    }
    if !record.object_flags().intersects(ObjectFlags::ANONYMOUS) {
        return Ok(false);
    }
    let structured = record
        .data()
        .structured()
        .ok_or(SourceTypeofNarrowingError::InvalidType(type_))?;
    Ok(structured.properties.as_ref().is_none_or(Vec::is_empty)
        && structured.signatures.as_ref().is_none_or(Vec::is_empty)
        && structured.index_infos.as_ref().is_none_or(Vec::is_empty))
}

fn source_typeof_object_is_function(
    store: &CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    type_: TypeId,
    record: &TypeRecord,
) -> Result<bool, SourceTypeofNarrowingError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceTypeofNarrowingError::MissingBootstrap)?;
    if type_ == globals.function_type || type_ == bootstrap.any_function_type {
        return Ok(true);
    }
    let structured = record
        .data()
        .structured()
        .ok_or(SourceTypeofNarrowingError::InvalidType(type_))?;
    let signature_count = structured.signatures.as_ref().map_or(0, Vec::len);
    if structured.call_signature_count > signature_count {
        return Err(SourceTypeofNarrowingError::InvalidType(type_));
    }
    if signature_count != 0 {
        return Ok(true);
    }
    for property in structured.properties.as_deref().unwrap_or_default() {
        let symbol = store
            .symbol(*property)
            .ok_or(SourceTypeofNarrowingError::InvalidType(type_))?;
        if symbol.name().as_bytes() == b"bind" {
            return Err(SourceTypeofNarrowingError::UnsupportedType(type_));
        }
    }
    Ok(false)
}

fn validate_container(graph: &BoundFlowGraph, container: NodeRef) -> Result<(), SourceFlowError> {
    if !container.is_for(graph.node_arena_id(), graph.file_id()) {
        return Err(SourceFlowInvariant::ForeignNode(container).into());
    }
    match graph.container_is_complete(container) {
        Some(true) => Ok(()),
        Some(false) => Err(SourceFlowUnsupported::IncompleteContainer(container).into()),
        None => Err(SourceFlowInvariant::MissingContainer(container).into()),
    }
}

fn parameter_assignment_declaration_and_name(
    arena: &NodeArena,
    bound: &BoundFile,
    container: NodeRef,
    declaration: NodeRef,
) -> Option<(NodeRef, NodeRef)> {
    let record = arena.get(declaration.node)?;
    match &record.data {
        NodeData::ParameterDeclaration(parameter) if record.kind == SyntaxKind::Parameter => {
            Some((
                declaration,
                NodeRef::new(declaration.arena, declaration.file, parameter.name),
            ))
        }
        NodeData::BindingElement(binding) if record.kind == SyntaxKind::BindingElement => {
            let name = NodeRef::new(declaration.arena, declaration.file, binding.name?);
            let pattern = NodeRef::new(declaration.arena, declaration.file, record.parent?);
            let pattern_record = arena.get(pattern.node)?;
            let NodeData::BindingPattern(elements) = &pattern_record.data else {
                return None;
            };
            let parameter =
                NodeRef::new(declaration.arena, declaration.file, pattern_record.parent?);
            let parameter_record = arena.get(parameter.node)?;
            let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
                return None;
            };
            let name_record = arena.get(name.node)?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return None;
            };
            if record.flags.0 != 0
                || binding.dot_dot_dot_token.is_some()
                || binding.flow_node.is_some()
                || binding.initializer.is_some()
                || binding.local_symbol.is_some()
                || binding.property_name.is_some()
                || binding.symbol.is_some()
                || binding.facts != 0
                || pattern_record.kind != SyntaxKind::ArrayBindingPattern
                || pattern_record.flags.0 != 0
                || elements.facts != 0
                || elements.elements.range != pattern_record.range
                || elements
                    .elements
                    .nodes
                    .iter()
                    .filter(|element| **element == declaration.node)
                    .count()
                    != 1
                || parameter_record.kind != SyntaxKind::Parameter
                || parameter_record.parent != Some(container.node)
                || parameter_data.name != pattern.node
                || pattern_record.range.start < parameter_record.range.start
                || pattern_record.range.end > parameter_record.range.end
                || name_record.kind != SyntaxKind::Identifier
                || name_record.flags.0 != 0
                || name_record.parent != Some(declaration.node)
                || identifier.flow_node.is_some()
                || identifier.text.is_empty()
                || bound.symbol(parameter).is_none()
                || bound.symbol(pattern).is_some()
                || bound.local_symbol(pattern).is_some()
                || bound.local_symbol(declaration).is_some()
                || record.range.start < pattern_record.range.start
                || record.range.end > pattern_record.range.end
                || name_record.range.start < record.range.start
                || name_record.range.end > record.range.end
                || [declaration, name, pattern, parameter]
                    .into_iter()
                    .any(|node| {
                        !bound.contains(node)
                            || bound.container(node) != Some(container)
                            || bound.block_scope_container(node) != Some(container)
                    })
            {
                return None;
            }
            Some((parameter, name))
        }
        _ => None,
    }
}

fn validate_parameter_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    container: NodeRef,
    assignment: SourceFlowParameterAssignment,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidParameterAssignment(assignment.target);
    if !assignment.target.is_for(arena.id(), bound.file_id())
        || !assignment.parameter.is_for(arena.id(), bound.file_id())
        || !bound.contains(assignment.target)
        || !bound.contains(assignment.parameter)
        || bound.symbol(assignment.parameter) != Some(assignment.symbol)
        || bound.container(assignment.parameter) != Some(container)
        || bound.container(assignment.target) != Some(container)
        || bound.block_scope_container(assignment.target) != Some(container)
        || bound.flow_container(assignment.target) != Some(container)
    {
        return Err(invalid().into());
    }

    let function = arena.get(container.node).ok_or_else(invalid)?;
    let NodeData::FunctionDeclaration(function_data) = &function.data else {
        return Err(invalid().into());
    };
    let (parameter_declaration, parameter_name) =
        parameter_assignment_declaration_and_name(arena, bound, container, assignment.parameter)
            .ok_or_else(invalid)?;
    let parameter = arena.get(parameter_declaration.node).ok_or_else(invalid)?;
    let parameter_name = arena.get(parameter_name.node).ok_or_else(invalid)?;
    let NodeData::Identifier(parameter_identifier) = &parameter_name.data else {
        return Err(invalid().into());
    };
    let target = arena.get(assignment.target.node).ok_or_else(invalid)?;
    let NodeData::Identifier(target_identifier) = &target.data else {
        return Err(invalid().into());
    };
    if function.kind != SyntaxKind::FunctionDeclaration
        || parameter.kind != SyntaxKind::Parameter
        || parameter.parent != Some(container.node)
        || function_data
            .parameters
            .nodes
            .iter()
            .filter(|node| **node == parameter_declaration.node)
            .count()
            != 1
        || parameter_name.kind != SyntaxKind::Identifier
        || parameter_name.parent != Some(assignment.parameter.node)
        || target.kind != SyntaxKind::Identifier
        || target.flags.0 != 0
        || target_identifier.flow_node.is_some()
        || target_identifier.text.is_empty()
        || target_identifier.text != parameter_identifier.text
    {
        return Err(invalid().into());
    }

    let expression = target
        .parent
        .and_then(|node| arena.get(node))
        .ok_or_else(invalid)?;
    let NodeData::BinaryExpression(binary) = &expression.data else {
        return Err(invalid().into());
    };
    let operator = arena.get(binary.operator_token).ok_or_else(invalid)?;
    if expression.kind != SyntaxKind::BinaryExpression
        || expression.flags.0 != 0
        || binary.left != assignment.target.node
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.facts != 0
        || binary.modifiers.is_some()
        || operator.kind != SyntaxKind::EqualsToken
        || operator.flags.0 != 0
        || operator.parent != target.parent
        || !matches!(operator.data, NodeData::Token(_))
    {
        return Err(invalid().into());
    }

    let statement = expression
        .parent
        .and_then(|node| arena.get(node))
        .ok_or_else(invalid)?;
    let NodeData::ExpressionStatement(statement_data) = &statement.data else {
        return Err(invalid().into());
    };
    let body = statement
        .parent
        .and_then(|node| arena.get(node))
        .ok_or_else(invalid)?;
    if statement.kind != SyntaxKind::ExpressionStatement
        || statement.flags.0 != 0
        || statement_data.expression != target.parent.ok_or_else(invalid)?
        || statement_data.flow_node.is_some()
        || body.kind != SyntaxKind::Block
        || body.parent != Some(container.node)
        || function_data.body != statement.parent
    {
        return Err(invalid().into());
    }
    Ok(())
}

fn validate_direct_call(
    arena: &NodeArena,
    bound: &BoundFile,
    container: NodeRef,
    expression: NodeRef,
) -> Result<NodeRef, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCall(expression);
    if !expression.is_for(arena.id(), bound.file_id())
        || !bound.contains(expression)
        || bound.container(expression) != Some(container)
        || bound.block_scope_container(expression) != Some(container)
    {
        return Err(invalid().into());
    }

    let call = arena.get(expression.node).ok_or_else(invalid)?;
    let NodeData::CallExpression(call_data) = &call.data else {
        return Err(invalid().into());
    };
    let callee = arena.get(call_data.expression).ok_or_else(invalid)?;
    if call.kind != SyntaxKind::CallExpression
        || call.flags.0 != 0
        || call_data.question_dot_token.is_some()
        || call_data.symbol.is_some()
        || call_data.facts != 0
        || !matches!(
            callee.kind,
            SyntaxKind::Identifier | SyntaxKind::PropertyAccessExpression
        )
        || callee.parent != Some(expression.node)
    {
        return Err(invalid().into());
    }

    let statement_id = call.parent.ok_or_else(invalid)?;
    let statement = arena.get(statement_id).ok_or_else(invalid)?;
    let NodeData::ExpressionStatement(statement_data) = &statement.data else {
        return Err(invalid().into());
    };
    let body = statement
        .parent
        .and_then(|node| arena.get(node))
        .ok_or_else(invalid)?;
    let function = arena.get(container.node).ok_or_else(invalid)?;
    let NodeData::FunctionDeclaration(function_data) = &function.data else {
        return Err(invalid().into());
    };
    if statement.kind != SyntaxKind::ExpressionStatement
        || statement.flags.0 != 0
        || statement_data.expression != expression.node
        || statement_data.flow_node.is_some()
        || body.kind != SyntaxKind::Block
        || body.parent != Some(container.node)
        || function.kind != SyntaxKind::FunctionDeclaration
        || function_data.body != statement.parent
    {
        return Err(invalid().into());
    }
    let statement = NodeRef::new(arena.id(), bound.file_id(), statement_id);
    validate_node_container(bound, bound.flow_graph(), container, statement)?;
    Ok(statement)
}

fn validate_call_container(
    bound: &BoundFile,
    container: NodeRef,
    call: NodeRef,
    statement: NodeRef,
    antecedent: FlowRef,
) -> Result<(), SourceFlowError> {
    if !bound.contains(call)
        || bound.container(call) != Some(container)
        || bound.block_scope_container(call) != Some(container)
        || bound.flow_container(statement) != Some(container)
        || bound.flow_at(statement) != Some(antecedent)
    {
        return Err(SourceFlowInvariant::InvalidCall(call).into());
    }
    Ok(())
}

fn validate_planned_call_container(
    bound: &BoundFile,
    plan: &SourceFlowPlan,
    call: NodeRef,
    statement: NodeRef,
    antecedent: FlowRef,
) -> Result<(), SourceFlowError> {
    let Some(body) = plan.class_body.as_ref() else {
        return validate_call_container(bound, plan.container, call, statement, antecedent);
    };
    if !bound.contains(call)
        || bound.container(call) != Some(body.declaration)
        || bound.flow_container(statement) != Some(plan.container)
        || bound.flow_at(statement) != Some(antecedent)
    {
        return Err(SourceFlowInvariant::InvalidCall(call).into());
    }
    Ok(())
}

fn validate_class_body_call(
    arena: &NodeArena,
    bound: &BoundFile,
    body: &ClassBodyPlan,
    container: NodeRef,
    expression: NodeRef,
) -> Result<NodeRef, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCall(expression);
    if !expression.is_for(arena.id(), bound.file_id())
        || !bound.contains(expression)
        || bound.container(expression) != Some(body.declaration)
    {
        return Err(invalid().into());
    }
    let record = arena.get(expression.node).ok_or_else(invalid)?;
    let NodeData::CallExpression(call) = &record.data else {
        return Err(invalid().into());
    };
    let callee = arena.get(call.expression).ok_or_else(invalid)?;
    if record.kind != SyntaxKind::CallExpression
        || record.flags.0 != 0
        || call.question_dot_token.is_some()
        || call.symbol.is_some()
        || call.facts != 0
        || callee.parent != Some(expression.node)
        || !matches!(
            callee.kind,
            SyntaxKind::Identifier
                | SyntaxKind::PropertyAccessExpression
                | SyntaxKind::SuperKeyword
        )
        || callee.kind == SyntaxKind::SuperKeyword
            && !matches!(body.kind, ClassBodyKind::Constructor)
    {
        return Err(invalid().into());
    }
    let statement = NodeRef::new(
        expression.arena,
        expression.file,
        record.parent.ok_or_else(invalid)?,
    );
    let record = arena.get(statement.node).ok_or_else(invalid)?;
    let NodeData::ExpressionStatement(data) = &record.data else {
        return Err(invalid().into());
    };
    if record.kind != SyntaxKind::ExpressionStatement
        || record.flags.0 != 0
        || data.expression != expression.node
        || data.flow_node.is_some()
        || !source_node_is_descendant_of(arena, statement, body.body.node)
    {
        return Err(invalid().into());
    }
    validate_node_container(bound, bound.flow_graph(), container, statement)?;
    Ok(statement)
}

/// This owner follows checker control flow, which does not stop at a static block.
fn class_control_flow_container(
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<NodeRef, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidClassBody(node);
    let mut current = node;
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(current) {
            return Err(invalid().into());
        }
        let parent = host
            .node(current)
            .and_then(|record| record.parent)
            .ok_or_else(invalid)?;
        current = NodeRef::new(node.arena, node.file, parent);
        let record = host.node(current).ok_or_else(invalid)?;
        if matches!(
            record.kind,
            SyntaxKind::SourceFile
                | SyntaxKind::ModuleBlock
                | SyntaxKind::PropertyDeclaration
                | SyntaxKind::Constructor
                | SyntaxKind::MethodDeclaration
                | SyntaxKind::GetAccessor
                | SyntaxKind::SetAccessor
                | SyntaxKind::FunctionDeclaration
                | SyntaxKind::FunctionExpression
                | SyntaxKind::ArrowFunction
        ) {
            return Ok(current);
        }
    }
}

fn plan_outer_class_property_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    body: &ClassBodyPlan,
    target: NodeRef,
) -> Result<Option<ClassPropertyFlowAssignment>, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidClassProperty(target);
    let record = host.node(target).ok_or_else(invalid)?;
    let NodeData::PropertyAccessExpression(property) = &record.data else {
        return Ok(None);
    };
    if source_node_is_descendant_of(arena, target, body.body.node) {
        return Ok(None);
    }
    let expression = NodeRef::new(
        target.arena,
        target.file,
        record.parent.ok_or_else(invalid)?,
    );
    let expression_record = host.node(expression).ok_or_else(invalid)?;
    let NodeData::BinaryExpression(binary) = &expression_record.data else {
        return Err(invalid().into());
    };
    let operator = NodeRef::new(target.arena, target.file, binary.operator_token);
    let receiver = NodeRef::new(target.arena, target.file, property.expression);
    let receiver_record = host.node(receiver).ok_or_else(invalid)?;
    let NodeData::Identifier(receiver_name) = &receiver_record.data else {
        return Err(invalid().into());
    };
    let name = NodeRef::new(target.arena, target.file, property.name);
    let name_record = host.node(name).ok_or_else(invalid)?;
    let NodeData::Identifier(member_name) = &name_record.data else {
        return Err(invalid().into());
    };
    let statement = NodeRef::new(
        target.arena,
        target.file,
        expression_record.parent.ok_or_else(invalid)?,
    );
    let statement_record = host.node(statement).ok_or_else(invalid)?;
    if record.kind != SyntaxKind::PropertyAccessExpression
        || record.flags.0 != 0
        || property.question_dot_token.is_some()
        || property.flow_node.is_some()
        || property.facts != 0
        || expression_record.kind != SyntaxKind::BinaryExpression
        || expression_record.flags.0 != 0
        || binary.left != target.node
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.facts != 0
        || binary.modifiers.is_some()
        || host
            .node(operator)
            .is_none_or(|operator| operator.kind != SyntaxKind::EqualsToken)
        || receiver_record.kind != SyntaxKind::Identifier
        || receiver_record.parent != Some(target.node)
        || receiver_record.flags.0 != 0
        || receiver_name.flow_node.is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(target.node)
        || name_record.flags.0 != 0
        || member_name.flow_node.is_some()
        || !matches!(&statement_record.data, NodeData::ExpressionStatement(data)
            if data.expression == expression.node && data.flow_node.is_none())
        || statement_record.parent != Some(bound.source_file().node)
        || bound
            .source_facts()
            .is_none_or(|facts| !facts.is_javascript_file())
    {
        return Err(invalid().into());
    }
    let mut resolver_host = host.name_resolver_host(store).map_err(|_| invalid())?;
    let mut resolver =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut resolver_host)
            .map_err(|_| invalid())?;
    let symbol = resolver
        .resolve(
            Some(CanonicalResolutionLocation::Bound(receiver)),
            &receiver_name.text,
            SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
            None,
            false,
            false,
        )
        .map_err(|_| invalid())?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    let owner = store.symbol(symbol).ok_or_else(invalid)?;
    let member = owner
        .exports()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source(&member_name.text))
        .ok_or_else(invalid)?;
    let member_record = store.symbol(member).ok_or_else(invalid)?;
    if !owner.flags().contains(SymbolFlags::CLASS)
        || member_record.parent() != Some(symbol)
        || member_record.value_declaration() != Some(expression)
        || member_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&expression))
    {
        return Err(invalid().into());
    }
    Ok(Some(ClassPropertyFlowAssignment {
        expression,
        reference: ClassPropertyFlowReference {
            receiver: ClassPropertyFlowReceiver::Named(symbol),
            name: member_name.text.clone(),
        },
        write: None,
    }))
}

fn is_property_assignment_target(host: &DeclaredTypeHost<'_>, target: NodeRef) -> bool {
    let Some(record) = host.node(target) else {
        return false;
    };
    if !matches!(record.data, NodeData::PropertyAccessExpression(_)) {
        return false;
    }
    let Some(parent) = record.parent else {
        return false;
    };
    let expression = NodeRef::new(target.arena, target.file, parent);
    matches!(host.node(expression).map(|record| &record.data),
        Some(NodeData::BinaryExpression(binary))
            if binary.left == target.node
                && host.node(NodeRef::new(target.arena, target.file, binary.operator_token))
                    .is_some_and(|operator| operator.kind.is_assignment_operator()))
}

fn plan_constructor_property_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    body: &ClassBodyPlan,
    target: NodeRef,
    flow: FlowRef,
) -> Result<Option<ClassPropertyFlowAssignment>, SourceFlowError> {
    if !is_property_assignment_target(host, target) {
        return Ok(None);
    }
    let invalid = || SourceFlowInvariant::InvalidClassProperty(target);
    if !matches!(body.kind, ClassBodyKind::Constructor)
        || !source_node_is_descendant_of(arena, target, body.body.node)
        || bound.flow_container(target) != Some(body.declaration)
    {
        return Err(invalid().into());
    }
    let expression = NodeRef::new(
        target.arena,
        target.file,
        host.node(target)
            .and_then(|record| record.parent)
            .ok_or_else(invalid)?,
    );
    let plan = plan_class_property_write(store, host, expression).map_err(|error| match error {
        SourcePropertyError::Unsupported(_) => {
            SourceFlowError::Unsupported(SourceFlowUnsupported::PropertyWrite(target))
        }
        _ => invalid().into(),
    })?;
    let node = flow_node(bound.flow_graph(), flow)?;
    if plan.target() != target
        || plan.context().class_symbol() != body.class_symbol
        || plan.context().class_declaration() != body.class_declaration
        || plan.context().body_declaration() != body.declaration
        || source_flow_kind(flow, node.flags)? != SourceFlowKind::Assignment
        || ast_payload(flow, &node)? != target
    {
        return Err(invalid().into());
    }
    linear_antecedent(flow, &node)?;
    Ok(Some(ClassPropertyFlowAssignment {
        expression,
        reference: ClassPropertyFlowReference {
            receiver: ClassPropertyFlowReceiver::This(body.class_declaration),
            name: plan.name().to_owned(),
        },
        write: Some(ClassPropertyWriteFlow { plan, flow }),
    }))
}

fn validate_node_container(
    bound: &BoundFile,
    graph: &BoundFlowGraph,
    container: NodeRef,
    node: NodeRef,
) -> Result<(), SourceFlowError> {
    if !node.is_for(graph.node_arena_id(), graph.file_id()) {
        return Err(SourceFlowInvariant::ForeignNode(node).into());
    }
    let actual = bound
        .flow_container(node)
        .ok_or(SourceFlowInvariant::MissingContainer(node))?;
    if actual != container {
        return Err(SourceFlowInvariant::ContainerMismatch {
            node,
            expected: container,
            actual,
        }
        .into());
    }
    Ok(())
}

fn validate_bound_node(
    bound: &BoundFile,
    graph: &BoundFlowGraph,
    node: NodeRef,
) -> Result<(), SourceFlowError> {
    if !node.is_for(graph.node_arena_id(), graph.file_id()) {
        return Err(SourceFlowInvariant::ForeignNode(node).into());
    }
    if !bound.contains(node) {
        return Err(SourceFlowInvariant::MissingContainer(node).into());
    }
    Ok(())
}

fn insert_flow_point(
    bound: &BoundFile,
    graph: &BoundFlowGraph,
    container: NodeRef,
    points: &mut HashMap<NodeRef, FlowRef>,
    point_order: &mut Vec<NodeRef>,
    point: NodeRef,
    reject_duplicate: bool,
) -> Result<(), SourceFlowError> {
    validate_node_container(bound, graph, container, point)?;
    let flow = bound
        .flow_at(point)
        .ok_or(SourceFlowInvariant::MissingFlowPoint(point))?;
    if points.contains_key(&point) {
        return if reject_duplicate {
            Err(SourceFlowInvariant::DuplicatePoint(point).into())
        } else {
            Ok(())
        };
    }
    points.insert(point, flow);
    point_order.push(point);
    Ok(())
}

fn flow_node(graph: &BoundFlowGraph, flow: FlowRef) -> Result<FlowNode, SourceFlowError> {
    if !flow.is_for(graph.node_arena_id(), graph.file_id()) {
        return Err(SourceFlowInvariant::ForeignFlow(flow).into());
    }
    graph
        .nodes()
        .get(flow)
        .cloned()
        .ok_or_else(|| SourceFlowInvariant::MissingFlowNode(flow).into())
}

fn source_flow_kind(flow: FlowRef, flags: FlowFlags) -> Result<SourceFlowKind, SourceFlowError> {
    let semantic = flags.bits() & !FLOW_METADATA_BITS;
    if semantic == FlowFlags::UNREACHABLE.bits() {
        return Ok(SourceFlowKind::Unreachable);
    }
    if semantic == FlowFlags::START.bits() {
        return Ok(SourceFlowKind::Start);
    }
    if semantic == FlowFlags::ASSIGNMENT.bits() {
        return Ok(SourceFlowKind::Assignment);
    }
    if semantic == FlowFlags::CALL.bits() {
        return Ok(SourceFlowKind::Call);
    }
    if semantic == FlowFlags::TRUE_CONDITION.bits() {
        return Ok(SourceFlowKind::TrueCondition);
    }
    if semantic == FlowFlags::FALSE_CONDITION.bits() {
        return Ok(SourceFlowKind::FalseCondition);
    }
    if semantic == FlowFlags::BRANCH_LABEL.bits() {
        return Ok(SourceFlowKind::BranchLabel);
    }
    if semantic == FlowFlags::LOOP_LABEL.bits() {
        return Ok(SourceFlowKind::LoopLabel);
    }
    if matches!(
        semantic,
        value if value == FlowFlags::SWITCH_CLAUSE.bits()
            || value == FlowFlags::ARRAY_MUTATION.bits()
            || value == FlowFlags::REDUCE_LABEL.bits()
    ) {
        return Err(SourceFlowUnsupported::FlowKind { flow, flags }.into());
    }
    Err(SourceFlowInvariant::InvalidFlowFlags { flow, flags }.into())
}

fn validate_unreachable_node(
    graph: &BoundFlowGraph,
    flow: FlowRef,
    node: &FlowNode,
) -> Result<(), SourceFlowError> {
    if flow != graph.nodes().unreachable()
        || node.payload.is_some()
        || node.antecedent.is_some()
        || !node.antecedents.is_empty()
    {
        return Err(SourceFlowInvariant::InvalidUnreachable(flow).into());
    }
    Ok(())
}

fn validate_start_node(
    plan: &SourceFlowPlan,
    flow: FlowRef,
    node: &FlowNode,
) -> Result<(), SourceFlowError> {
    let payload_matches = match (node.payload.as_ref(), plan.start_payload) {
        (None, None) => true,
        (Some(FlowNodePayload::Ast(actual)), Some(expected)) => *actual == expected,
        _ => false,
    };
    if flow != plan.start
        || node.antecedent.is_some()
        || !node.antecedents.is_empty()
        || !payload_matches
    {
        return Err(SourceFlowInvariant::InvalidStart(flow).into());
    }
    Ok(())
}

fn preflight_start_payload(
    graph: &BoundFlowGraph,
    container: NodeRef,
    flow: FlowRef,
) -> Result<Option<NodeRef>, SourceFlowError> {
    let node = flow_node(graph, flow)?;
    if source_flow_kind(flow, node.flags)? != SourceFlowKind::Start
        || node.antecedent.is_some()
        || !node.antecedents.is_empty()
    {
        return Err(SourceFlowInvariant::InvalidStart(flow).into());
    }
    match node.payload.as_ref() {
        None => Ok(None),
        Some(FlowNodePayload::Ast(actual)) if *actual == container => Ok(Some(*actual)),
        _ => Err(SourceFlowInvariant::InvalidStart(flow).into()),
    }
}

fn linear_antecedent(flow: FlowRef, node: &FlowNode) -> Result<FlowRef, SourceFlowError> {
    if !node.antecedents.is_empty() {
        return Err(SourceFlowInvariant::InvalidAntecedents(flow).into());
    }
    node.antecedent
        .ok_or_else(|| SourceFlowInvariant::InvalidAntecedents(flow).into())
}

fn label_antecedents(flow: FlowRef, node: &FlowNode) -> Result<&[FlowRef], SourceFlowError> {
    if node.antecedents.len() < 2 {
        return Err(SourceFlowInvariant::InvalidAntecedents(flow).into());
    }
    let mut unique = HashSet::with_capacity(node.antecedents.len());
    if node.antecedent.is_some()
        || node.payload.is_some()
        || node
            .antecedents
            .iter()
            .any(|antecedent| !unique.insert(*antecedent))
    {
        return Err(SourceFlowInvariant::InvalidAntecedents(flow).into());
    }
    Ok(&node.antecedents)
}

fn union_constituents(store: &CanonicalTypeMapperStore, type_: TypeId) -> Option<&[TypeId]> {
    let TypeData::Union(union) = store.type_payload(type_)?.data() else {
        return None;
    };
    Some(&union.union.types)
}

fn ast_payload(flow: FlowRef, node: &FlowNode) -> Result<NodeRef, SourceFlowError> {
    match node.payload.as_ref() {
        Some(FlowNodePayload::Ast(node)) => Ok(*node),
        _ => Err(SourceFlowInvariant::InvalidPayload(flow).into()),
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, FlowNodeId, NodeArena, NodeData, NodeId};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeNodeLinks,
    };

    fn flow() -> FlowRef {
        let arena = NodeArena::default();
        FlowRef::new(arena.id(), FileId::new(7), FlowNodeId(3))
    }

    fn loop_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/source-flow-loop.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    #[test]
    fn constructor_property_writes_reject_wrong_flow_tokens_references_and_edges() {
        use crate::semantic::{classes, production::GlobalMergeCompletion};

        #[derive(Clone, Copy)]
        enum Change {
            Token,
            Reference,
            Edge,
            Container,
        }

        let parsed = parse_source_file(concat!(
            "class First { value?: number; constructor() { this.value = 1; this.value = 2; } } ",
            "class Second { value?: number; constructor() { this.value = 2; } }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(31_801);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let class_symbol = |context: &CanonicalCheckerContext<'_>, name| {
            context
                .store()
                .symbol_table(context.globals())
                .unwrap()
                .get_source(name)
                .unwrap()
        };
        let first_symbol = class_symbol(&context, "First");
        let second_symbol = class_symbol(&context, "Second");
        let first =
            classes::plan_source_class_members(context.store(), &host, first_symbol).unwrap();
        let second =
            classes::plan_source_class_members(context.store(), &host, second_symbol).unwrap();
        let assignment = parsed
            .arena
            .iter()
            .filter(|(_, record)| matches!(record.data, NodeData::BinaryExpression(_)))
            .min_by_key(|(_, record)| record.range.start)
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            .unwrap();
        let write = plan_class_property_write(context.store(), &host, assignment).unwrap();
        let body = &first.bodies()[0];
        let plan = SourceFlowPlan::preflight_class_body(
            &parsed.arena,
            &bound,
            context.store(),
            &host,
            body,
            [write.statement(), write.target(), write.receiver()],
            [],
            [],
        )
        .unwrap();
        let other_assignment_flow = plan
            .property_assignments
            .values()
            .filter_map(|assignment| assignment.write.as_ref())
            .find(|assignment| assignment.plan.target() != write.target())
            .unwrap()
            .flow;
        let first_prepared =
            classes::prepare_source_class_members(context.store_mut_for_test(), &host, &first)
                .unwrap();
        let access = first_prepared
            .body_access(context.store(), &host, body)
            .unwrap();
        let second_prepared =
            classes::prepare_source_class_members(context.store_mut_for_test(), &host, &second)
                .unwrap();
        let second_access = second_prepared
            .body_access(context.store(), &host, &second.bodies()[0])
            .unwrap();
        let frame =
            ClassInitializationFrame::new(body, &plan, &bound, access.clone(), HashMap::new())
                .unwrap();
        frame
            .preflight_property_assignment(context.store(), &host, &write)
            .unwrap();
        assert!(frame.property_assignments.is_empty());

        for change in [
            Change::Token,
            Change::Reference,
            Change::Edge,
            Change::Container,
        ] {
            let mut changed = plan.clone();
            let mut token = access.clone();
            match change {
                Change::Token => token = second_access.clone(),
                Change::Reference => {
                    changed
                        .property_assignments
                        .get_mut(&write.target())
                        .unwrap()
                        .reference
                        .receiver = ClassPropertyFlowReceiver::Named(first_symbol);
                }
                Change::Edge => {
                    changed
                        .property_assignments
                        .get_mut(&write.target())
                        .unwrap()
                        .write
                        .as_mut()
                        .unwrap()
                        .flow = other_assignment_flow;
                }
                Change::Container => changed.container = second.bodies()[0].declaration,
            }
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            let frame =
                ClassInitializationFrame::new(body, &changed, &bound, token, HashMap::new())
                    .unwrap();
            assert_eq!(
                frame.preflight_property_assignment(context.store(), &host, &write),
                Err(SourceFlowInvariant::InvalidClassProperty(write.target()).into())
            );
            assert!(frame.property_assignments.is_empty());
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before
            );
        }
    }

    fn loop_nodes(parsed: &ParseResult, file: FileId) -> (NodeRef, NodeRef, NodeRef, NodeRef) {
        let (function, parameter) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::FunctionDeclaration(function) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, *function.parameters.nodes.first()?),
                ))
            })
            .unwrap();
        let condition = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::WhileStatement(statement) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(parsed.arena.id(), file, statement.expression))
            })
            .unwrap();
        let return_statement = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(&record.data, NodeData::ReturnStatement(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        (function, parameter, condition, return_statement)
    }

    #[test]
    fn metadata_bits_do_not_change_admitted_flow_kinds() {
        let flow = flow();
        assert_eq!(
            source_flow_kind(flow, FlowFlags::UNREACHABLE | FlowFlags::REFERENCED),
            Ok(SourceFlowKind::Unreachable),
        );
        assert_eq!(
            source_flow_kind(
                flow,
                FlowFlags::START | FlowFlags::REFERENCED | FlowFlags::SHARED,
            ),
            Ok(SourceFlowKind::Start),
        );
        assert_eq!(
            source_flow_kind(
                flow,
                FlowFlags::ASSIGNMENT | FlowFlags::REFERENCED | FlowFlags::SHARED,
            ),
            Ok(SourceFlowKind::Assignment),
        );
        assert_eq!(
            source_flow_kind(flow, FlowFlags::CALL | FlowFlags::REFERENCED),
            Ok(SourceFlowKind::Call),
        );
        assert_eq!(
            source_flow_kind(flow, FlowFlags::TRUE_CONDITION | FlowFlags::REFERENCED,),
            Ok(SourceFlowKind::TrueCondition),
        );
        assert_eq!(
            source_flow_kind(flow, FlowFlags::FALSE_CONDITION | FlowFlags::SHARED),
            Ok(SourceFlowKind::FalseCondition),
        );
        assert_eq!(
            source_flow_kind(flow, FlowFlags::BRANCH_LABEL | FlowFlags::SHARED),
            Ok(SourceFlowKind::BranchLabel),
        );
        assert_eq!(
            source_flow_kind(flow, FlowFlags::LOOP_LABEL | FlowFlags::SHARED),
            Ok(SourceFlowKind::LoopLabel),
        );
    }

    #[test]
    fn composite_semantic_kinds_remain_invariants() {
        let flow = flow();
        let composite = FlowFlags::TRUE_CONDITION | FlowFlags::FALSE_CONDITION;
        assert_eq!(
            source_flow_kind(flow, composite),
            Err(SourceFlowError::Invariant(
                SourceFlowInvariant::InvalidFlowFlags {
                    flow,
                    flags: composite,
                },
            )),
        );
    }

    #[test]
    fn switch_clause_flow_remains_explicitly_unsupported() {
        let flow = flow();
        let flags = FlowFlags::SWITCH_CLAUSE | FlowFlags::REFERENCED;
        assert_eq!(
            source_flow_kind(flow, flags),
            Err(SourceFlowError::Unsupported(
                SourceFlowUnsupported::FlowKind { flow, flags }
            )),
        );
    }

    #[test]
    fn start_validation_preserves_the_exact_preflight_payload_shape() {
        let arena = NodeArena::default();
        let file = FileId::new(7);
        let container = NodeRef::new(arena.id(), file, NodeId::new(1));
        let start = FlowRef::new(arena.id(), file, FlowNodeId(3));
        let mut plan = SourceFlowPlan {
            container,
            start_container: container,
            start,
            start_payload: None,
            end: None,
            points: HashMap::new(),
            point_order: Vec::new(),
            conditions: HashMap::new(),
            assignments: HashMap::new(),
            assignment_order: Vec::new(),
            parameter_assignments: HashMap::new(),
            calls: HashMap::new(),
            class_body: None,
            property_assignments: HashMap::new(),
        };
        let without_payload = FlowNode::new(FlowFlags::START);
        assert_eq!(validate_start_node(&plan, start, &without_payload), Ok(()));

        let mut with_payload = FlowNode::new(FlowFlags::START);
        with_payload.payload = Some(FlowNodePayload::Ast(container));
        assert_eq!(
            validate_start_node(&plan, start, &with_payload),
            Err(SourceFlowInvariant::InvalidStart(start).into()),
        );

        plan.start_payload = Some(container);
        assert_eq!(validate_start_node(&plan, start, &with_payload), Ok(()));
        assert_eq!(
            validate_start_node(&plan, start, &without_payload),
            Err(SourceFlowInvariant::InvalidStart(start).into()),
        );
    }

    #[test]
    fn branch_and_loop_labels_require_distinct_ordered_antecedents() {
        let arena = NodeArena::default();
        let file = FileId::new(7);
        let first = FlowRef::new(arena.id(), file, FlowNodeId(1));
        let second = FlowRef::new(arena.id(), file, FlowNodeId(2));
        let third = FlowRef::new(arena.id(), file, FlowNodeId(3));
        let branch = FlowRef::new(arena.id(), file, FlowNodeId(4));

        let mut node = FlowNode::new(FlowFlags::BRANCH_LABEL);
        node.antecedents = vec![first, second];
        assert_eq!(
            label_antecedents(branch, &node),
            Ok([first, second].as_slice())
        );

        node.antecedents = vec![first, second, third];
        assert_eq!(
            label_antecedents(branch, &node),
            Ok([first, second, third].as_slice()),
        );

        node.antecedents = vec![first];
        assert_eq!(
            label_antecedents(branch, &node),
            Err(SourceFlowInvariant::InvalidAntecedents(branch).into()),
        );
        node.antecedents = vec![first, first];
        assert_eq!(
            label_antecedents(branch, &node),
            Err(SourceFlowInvariant::InvalidAntecedents(branch).into()),
        );
        node.antecedents = vec![first, second, first];
        assert_eq!(
            label_antecedents(branch, &node),
            Err(SourceFlowInvariant::InvalidAntecedents(branch).into()),
        );
        node.antecedents = vec![first, second];
        node.antecedent = Some(first);
        assert_eq!(
            label_antecedents(branch, &node),
            Err(SourceFlowInvariant::InvalidAntecedents(branch).into()),
        );
        node.antecedent = None;
        node.payload = Some(FlowNodePayload::Ast(NodeRef::new(
            arena.id(),
            file,
            NodeId::new(1),
        )));
        assert_eq!(
            label_antecedents(branch, &node),
            Err(SourceFlowInvariant::InvalidAntecedents(branch).into()),
        );
    }

    #[test]
    fn typeof_top_types_preserve_intrinsic_and_nullable_branch_identities() {
        let parsed =
            parse_source_file("function narrow(value: unknown): unknown { return value; }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_420);
        let mut context = loop_context(&parsed, file);
        let globals = context.global_types().clone();
        let (
            any,
            unknown,
            non_nullable,
            undefined,
            null,
            string,
            number,
            boolean,
            bigint,
            symbol,
            object,
            never,
            error,
            auto,
        ) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.any_type,
                bootstrap.unknown_type,
                bootstrap.unknown_empty_object_type,
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
                bootstrap.bigint_type,
                bootstrap.es_symbol_type,
                bootstrap.non_primitive_type,
                bootstrap.never_type,
                bootstrap.error_type,
                bootstrap.auto_type,
            )
        };
        let nullable_object = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[object, null],
                UnionReduction::Literal,
            )
            .unwrap();
        let not_object = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[non_nullable, undefined],
                UnionReduction::Literal,
            )
            .unwrap();
        let not_undefined = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[non_nullable, null],
                UnionReduction::Literal,
            )
            .unwrap();

        for (input, tag, require_match, expected) in [
            (unknown, SourceTypeofTag::String, true, string),
            (unknown, SourceTypeofTag::Number, true, number),
            (unknown, SourceTypeofTag::Boolean, true, boolean),
            (unknown, SourceTypeofTag::BigInt, true, bigint),
            (unknown, SourceTypeofTag::Symbol, true, symbol),
            (unknown, SourceTypeofTag::Undefined, true, undefined),
            (unknown, SourceTypeofTag::Object, true, nullable_object),
            (
                unknown,
                SourceTypeofTag::Function,
                true,
                globals.function_type,
            ),
            (unknown, SourceTypeofTag::String, false, unknown),
            (unknown, SourceTypeofTag::Object, false, not_object),
            (unknown, SourceTypeofTag::Undefined, false, not_undefined),
            (any, SourceTypeofTag::String, true, string),
            (any, SourceTypeofTag::Number, true, number),
            (any, SourceTypeofTag::Object, true, any),
            (any, SourceTypeofTag::Function, true, any),
            (any, SourceTypeofTag::Undefined, false, any),
            (non_nullable, SourceTypeofTag::String, true, string),
            (non_nullable, SourceTypeofTag::Object, true, object),
            (
                non_nullable,
                SourceTypeofTag::Function,
                true,
                globals.function_type,
            ),
            (non_nullable, SourceTypeofTag::Undefined, true, never),
            (
                non_nullable,
                SourceTypeofTag::Undefined,
                false,
                non_nullable,
            ),
        ] {
            assert_eq!(
                source_typeof_narrowing_type_is_supported(context.store(), &globals, input, tag),
                Ok(true),
            );
            assert_eq!(
                narrow_by_typeof(
                    context.store_mut_for_test(),
                    &globals,
                    input,
                    tag,
                    require_match,
                ),
                Ok(expected),
            );
            let warm = (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert_eq!(
                narrow_by_typeof(
                    context.store_mut_for_test(),
                    &globals,
                    input,
                    tag,
                    require_match,
                ),
                Ok(expected),
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
            );
        }

        for unsupported in [error, auto] {
            assert_eq!(
                source_typeof_narrowing_type_is_supported(
                    context.store(),
                    &globals,
                    unsupported,
                    SourceTypeofTag::String,
                ),
                Ok(false),
            );
            assert_eq!(
                narrow_by_typeof(
                    context.store_mut_for_test(),
                    &globals,
                    unsupported,
                    SourceTypeofTag::String,
                    true,
                ),
                Err(SourceTypeofNarrowingError::UnsupportedType(unsupported)),
            );
        }
    }

    #[test]
    fn equality_narrowing_distinguishes_strict_and_loose_nullish_facts() {
        let parsed =
            parse_source_file("function narrow(value: unknown): unknown { return value; }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_430);
        let mut context = loop_context(&parsed, file);
        let globals = context.global_types().clone();
        let (any, unknown, non_nullable, undefined, null, string, never) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.any_type,
                bootstrap.unknown_type,
                bootstrap.unknown_empty_object_type,
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.string_type,
                bootstrap.never_type,
            )
        };
        let nullable = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[string, null, undefined],
                UnionReduction::Literal,
            )
            .unwrap();
        let string_or_undefined = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[string, undefined],
                UnionReduction::Literal,
            )
            .unwrap();
        let string_or_null = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[string, null],
                UnionReduction::Literal,
            )
            .unwrap();
        let null_or_undefined = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[null, undefined],
                UnionReduction::Literal,
            )
            .unwrap();
        let unknown_without_null = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[non_nullable, undefined],
                UnionReduction::Literal,
            )
            .unwrap();
        let unknown_without_undefined = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[non_nullable, null],
                UnionReduction::Literal,
            )
            .unwrap();

        for (input, value, strict, require_match, expected) in [
            (nullable, null, true, true, null),
            (nullable, null, true, false, string_or_undefined),
            (nullable, undefined, true, true, undefined),
            (nullable, undefined, true, false, string_or_null),
            (nullable, null, false, true, null_or_undefined),
            (nullable, null, false, false, string),
            (nullable, undefined, false, true, null_or_undefined),
            (nullable, undefined, false, false, string),
            (unknown, null, true, true, null),
            (unknown, null, true, false, unknown_without_null),
            (unknown, undefined, true, true, undefined),
            (unknown, undefined, true, false, unknown_without_undefined),
            (unknown, null, false, true, null_or_undefined),
            (unknown, null, false, false, non_nullable),
            (non_nullable, null, true, true, never),
            (non_nullable, null, true, false, non_nullable),
            (any, null, true, true, any),
            (any, undefined, false, false, any),
        ] {
            assert_eq!(
                narrow_by_equality(
                    context.store_mut_for_test(),
                    &globals,
                    input,
                    value,
                    strict,
                    require_match,
                    None,
                ),
                Ok(expected),
            );
            let warm = (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert_eq!(
                narrow_by_equality(
                    context.store_mut_for_test(),
                    &globals,
                    input,
                    value,
                    strict,
                    require_match,
                    None,
                ),
                Ok(expected),
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn equality_narrowing_filters_literals_without_removing_wide_primitives() {
        let parsed =
            parse_source_file("function narrow(value: unknown): unknown { return value; }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_431);
        let mut context = loop_context(&parsed, file);
        let globals = context.global_types().clone();
        let (unknown, string, number, boolean, regular_true, regular_false) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.unknown_type,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
                bootstrap.regular_true_type,
                bootstrap.regular_false_type,
            )
        };
        let ready = context
            .store_mut_for_test()
            .regular_string_literal_type("ready".to_owned())
            .unwrap();
        let waiting = context
            .store_mut_for_test()
            .regular_string_literal_type("waiting".to_owned())
            .unwrap();
        let done = context
            .store_mut_for_test()
            .regular_string_literal_type("done".to_owned())
            .unwrap();
        let fresh_ready = context
            .store_mut_for_test()
            .fresh_type_of_literal_type(ready)
            .unwrap();
        let choices = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[ready, waiting, done],
                UnionReduction::Literal,
            )
            .unwrap();
        let rejected = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[waiting, done],
                UnionReduction::Literal,
            )
            .unwrap();
        let mixed = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[string, number],
                UnionReduction::Literal,
            )
            .unwrap();

        for (input, value, require_match, expected) in [
            (choices, fresh_ready, true, ready),
            (choices, ready, false, rejected),
            (string, ready, true, ready),
            (string, ready, false, string),
            (mixed, ready, true, ready),
            (mixed, ready, false, mixed),
            (unknown, ready, true, ready),
            (unknown, ready, false, unknown),
            (boolean, regular_true, true, regular_true),
            (boolean, regular_true, false, regular_false),
        ] {
            assert_eq!(
                narrow_by_equality(
                    context.store_mut_for_test(),
                    &globals,
                    input,
                    value,
                    true,
                    require_match,
                    None,
                ),
                Ok(expected),
            );
            let warm = (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert_eq!(
                narrow_by_equality(
                    context.store_mut_for_test(),
                    &globals,
                    input,
                    value,
                    true,
                    require_match,
                    None,
                ),
                Ok(expected),
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
            );
        }

        assert_eq!(
            narrow_by_equality(
                context.store_mut_for_test(),
                &globals,
                choices,
                ready,
                false,
                true,
                None,
            ),
            Err(SourceEqualityNarrowingError::UnsupportedType(ready)),
        );
    }

    #[test]
    fn equality_narrowing_selects_authenticated_declared_union_members() {
        let parsed = parse_source_file(concat!(
            "type Choice = { kind: 'left'; value: string } | ",
            "{ kind: 'right'; value: number };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_432);
        let mut context = loop_context(&parsed, file);
        let alias = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeAliasDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .and_then(|declaration| context.file(file).unwrap().1.symbol(declaration))
            .unwrap();
        let choice = context.get_declared_type_of_symbol(alias).unwrap();
        let globals = context.global_types().clone();
        let left = context
            .store_mut_for_test()
            .regular_string_literal_type("left".to_owned())
            .unwrap();
        let right = context
            .store_mut_for_test()
            .regular_string_literal_type("right".to_owned())
            .unwrap();
        let members = match context.store().type_payload(choice).unwrap().data() {
            TypeData::Union(union) => union.union.types.clone(),
            _ => panic!("expected a declared object union"),
        };
        let mut left_member = None;
        let mut right_member = None;
        for member in members {
            let property = context
                .store_mut_for_test()
                .resolved_own_property(member, "kind")
                .unwrap()
                .unwrap();
            if property.type_ == left {
                left_member = Some(member);
            } else if property.type_ == right {
                right_member = Some(member);
            }
        }
        let left_member = left_member.unwrap();
        let right_member = right_member.unwrap();

        for (value, require_match, expected) in [
            (left, true, left_member),
            (left, false, right_member),
            (right, true, right_member),
            (right, false, left_member),
        ] {
            assert_eq!(
                narrow_by_equality(
                    context.store_mut_for_test(),
                    &globals,
                    choice,
                    value,
                    true,
                    require_match,
                    Some("kind"),
                ),
                Ok(expected),
            );
            let warm = (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert_eq!(
                narrow_by_equality(
                    context.store_mut_for_test(),
                    &globals,
                    choice,
                    value,
                    true,
                    require_match,
                    Some("kind"),
                ),
                Ok(expected),
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn nullish_equality_conditions_narrow_final_and_joined_source_branches() {
        let parsed = parse_source_file(concat!(
            "function strict(value: string | null): string {\n",
            "  if (value !== null) { return value; } else { return ''; }\n",
            "}\n",
            "function reversed(value: string | null): string {\n",
            "  if (null === value) { return ''; } else { return value; }\n",
            "}\n",
            "function loose(value: string | null | undefined): string {\n",
            "  if (value == null) { return ''; } else { return value; }\n",
            "}\n",
            "function joined(value: string | null | undefined): string | null | undefined {\n",
            "  if (undefined != value) {\n",
            "    const selected: string = value;\n",
            "  } else {\n",
            "    const rejected: null | undefined = value;\n",
            "  }\n",
            "  return value;\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_433);
        let mut context = loop_context(&parsed, file);

        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());

        let (string, boolean) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.boolean_type)
        };
        let return_reads = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::Identifier(identifier) = &record.data else {
                    return None;
                };
                if identifier.text != "value" {
                    return None;
                }
                let parent = parsed.arena.get(record.parent?)?;
                matches!(&parent.data, NodeData::ReturnStatement(returned)
                    if returned.expression == Some(node))
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .collect::<Vec<_>>();
        let [strict, reversed, loose, _joined] = return_reads.as_slice() else {
            panic!("expected one returned parameter in each function")
        };
        for node in [*strict, *reversed, *loose] {
            assert_eq!(
                context
                    .store()
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type),
                Some(string),
            );
        }
        for node in parsed.arena.iter().filter_map(|(node, record)| {
            (record.kind == SyntaxKind::BinaryExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        }) {
            assert_eq!(
                context
                    .store()
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type),
                Some(boolean),
            );
        }

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn discriminated_equality_conditions_narrow_final_and_joined_source_branches() {
        let parsed = parse_source_file(concat!(
            "type Choice = { kind: 'left'; active: true; value: string } | ",
            "{ kind: 'right'; active: false; value: number };\n",
            "function choose(value: Choice): string | number {\n",
            "  if (value.kind === 'left') {\n",
            "    return value.value;\n",
            "  } else {\n",
            "    return value.value;\n",
            "  }\n",
            "}\n",
            "function joined(value: Choice): Choice {\n",
            "  if (false !== value.active) {\n",
            "    const selected: string = value.value;\n",
            "  } else {\n",
            "    const rejected: number = value.value;\n",
            "  }\n",
            "  return value;\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_434);
        let mut context = loop_context(&parsed, file);

        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());

        let (string, number, boolean) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            )
        };
        let returns = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                if record.kind != SyntaxKind::PropertyAccessExpression {
                    return None;
                }
                let parent = parsed.arena.get(record.parent?)?;
                matches!(&parent.data, NodeData::ReturnStatement(returned)
                    if returned.expression == Some(node))
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .collect::<Vec<_>>();
        let [left, right] = returns.as_slice() else {
            panic!("expected one property return from each discriminated branch")
        };
        for (node, expected) in [(*left, string), (*right, number)] {
            assert_eq!(
                context
                    .store()
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type),
                Some(expected),
            );
        }
        for node in parsed.arena.iter().filter_map(|(node, record)| {
            (record.kind == SyntaxKind::BinaryExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        }) {
            assert_eq!(
                context
                    .store()
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type),
                Some(boolean),
            );
        }

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn unknown_typeof_conditions_narrow_both_binder_flow_edges_and_replay() {
        let parsed = parse_source_file(concat!(
            "function classify(value: unknown): unknown { ",
            "if (typeof value === 'object') { return value; } ",
            "else { return value; } ",
            "} ",
            "function text(value: any): string { ",
            "if (typeof value === 'string') { return value; } ",
            "else { return ''; } ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_421);
        let mut context = loop_context(&parsed, file);

        context.check_source_file(file).unwrap();

        let returns = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::Identifier(identifier) = &record.data else {
                    return None;
                };
                if identifier.text != "value" {
                    return None;
                }
                let parent = parsed.arena.get(record.parent?)?;
                matches!(&parent.data, NodeData::ReturnStatement(returned)
                    if returned.expression == Some(node))
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .collect::<Vec<_>>();
        let [unknown_true, unknown_false, any_true] = returns.as_slice() else {
            panic!("expected two unknown return edges and one narrowed any return")
        };
        let (object, null, non_nullable, undefined, string) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.non_primitive_type,
                bootstrap.null_type,
                bootstrap.unknown_empty_object_type,
                bootstrap.undefined_type,
                bootstrap.string_type,
            )
        };
        for (node, expected) in [
            (*unknown_true, vec![object, null]),
            (*unknown_false, vec![non_nullable, undefined]),
        ] {
            let type_ = context
                .store()
                .type_node_links(node)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let TypeData::Union(union) = context.store().type_payload(type_).unwrap().data() else {
                panic!("the unknown branch must retain an exact nullable union")
            };
            assert_eq!(union.union.types.len(), expected.len());
            assert!(
                expected
                    .iter()
                    .all(|member| union.union.types.contains(member))
            );
        }
        assert_eq!(
            context
                .store()
                .type_node_links(*any_true)
                .and_then(|links| links.resolved_type),
            Some(string),
        );
        assert!(context.diagnostics().is_empty());

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn branded_string_intersections_keep_their_exact_identity_under_typeof() {
        let parsed = parse_source_file(concat!(
            "type Branded = 'ready' & { brand: true }; ",
            "function take(value: Branded): Branded { return value; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_422);
        let mut context = loop_context(&parsed, file);
        let alias = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeAliasDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .and_then(|declaration| context.file(file).unwrap().1.symbol(declaration))
            .unwrap();
        let branded = context.get_declared_type_of_symbol(alias).unwrap();
        let globals = context.global_types().clone();
        let never = context.store().intrinsic_bootstrap().unwrap().never_type;
        let before = (
            context.store().type_len(),
            context.store().checker_link_allocated_lengths(),
        );

        for (tag, require_match, expected) in [
            (SourceTypeofTag::String, true, branded),
            (SourceTypeofTag::String, false, never),
            (SourceTypeofTag::Number, true, never),
            (SourceTypeofTag::Object, false, branded),
        ] {
            assert_eq!(
                source_typeof_narrowing_type_is_supported(context.store(), &globals, branded, tag),
                Ok(true),
            );
            assert_eq!(
                narrow_by_typeof(
                    context.store_mut_for_test(),
                    &globals,
                    branded,
                    tag,
                    require_match,
                ),
                Ok(expected),
            );
        }
        assert_eq!(
            (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn loop_backedges_converge_and_preserve_false_edge_narrowing() {
        let parsed = parse_source_file(concat!(
            "function loop(value: object | undefined): object | undefined {\n",
            "  while (value) {}\n",
            "  return value;\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_401);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let (function, parameter, condition, return_statement) = loop_nodes(&parsed, file);
        let symbol = bound.symbol(parameter).unwrap();
        let plan = SourceFlowPlan::preflight(
            &bound,
            function,
            None,
            [condition, return_statement],
            [SourceFlowCondition::Truthiness(SourceTruthinessCondition {
                expression: condition,
                symbol,
            })],
            [],
        )
        .unwrap();
        let (object, undefined) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.non_primitive_type, bootstrap.undefined_type)
        };
        let input = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[object, undefined],
                UnionReduction::Literal,
            )
            .unwrap();
        let mut frame = plan
            .frame(&bound, [(symbol, input)].into_iter().collect())
            .unwrap();

        let at_loop = frame
            .snapshot_at(context.store_mut_for_test(), &globals, condition)
            .unwrap();
        assert_eq!(at_loop.type_of(symbol), Some(input));
        let after_loop = frame
            .snapshot_at(context.store_mut_for_test(), &globals, return_statement)
            .unwrap();
        assert_eq!(after_loop.type_of(symbol), Some(undefined));
        let repeated = frame
            .snapshot_at(context.store_mut_for_test(), &globals, return_statement)
            .unwrap();
        assert_eq!(repeated, after_loop);
    }

    #[test]
    fn nullable_equality_loop_backedges_preserve_the_exact_false_edge() {
        let parsed = parse_source_file(concat!(
            "function loop(value: string | null): string | null {\n",
            "  while (value !== null) {}\n",
            "  return value;\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_435);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let (function, parameter, condition, return_statement) = loop_nodes(&parsed, file);
        let NodeData::BinaryExpression(binary) = &parsed.arena.get(condition.node).unwrap().data
        else {
            panic!("expected a strict nullish equality condition")
        };
        let identifier = NodeRef::new(parsed.arena.id(), file, binary.left);
        let null_literal = NodeRef::new(parsed.arena.id(), file, binary.right);
        let symbol = bound.symbol(parameter).unwrap();
        let (string, null) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.null_type)
        };
        assert!(context.store_mut_for_test().set_type_node_links(
            null_literal,
            TypeNodeLinks {
                resolved_type: Some(null),
                ..TypeNodeLinks::default()
            },
        ));
        let input = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[string, null],
                UnionReduction::Literal,
            )
            .unwrap();
        let plan = SourceFlowPlan::preflight(
            &bound,
            function,
            None,
            [identifier, return_statement],
            [SourceFlowCondition::Equality(SourceEqualityCondition {
                expression: condition,
                symbol,
                value: null_literal,
                comparison: SourceTypeofComparison::NotEqual,
                strict: true,
                discriminant: None,
            })],
            [],
        )
        .unwrap();
        let mut frame = plan
            .frame(&bound, [(symbol, input)].into_iter().collect())
            .unwrap();

        let at_condition = frame
            .snapshot_at(context.store_mut_for_test(), &globals, identifier)
            .unwrap();
        assert_eq!(at_condition.type_of(symbol), Some(input));
        let after_loop = frame
            .snapshot_at(context.store_mut_for_test(), &globals, return_statement)
            .unwrap();
        assert_eq!(after_loop.type_of(symbol), Some(null));
        let repeated = frame
            .snapshot_at(context.store_mut_for_test(), &globals, return_statement)
            .unwrap();
        assert_eq!(repeated, after_loop);
    }

    #[test]
    fn approved_call_flow_preserves_parameter_types_and_replays() {
        let parsed = parse_source_file(concat!(
            "declare function consume(value: number): void;\n",
            "function effects(value: number): void {\n",
            "  consume(value);\n",
            "  value;\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_402);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let (function, parameter, statements) = linear_function_nodes(&parsed, file, "effects");
        let [call_statement, after_statement] = statements.as_slice() else {
            panic!("expected one call and one following statement")
        };
        let call = expression_statement_expression(&parsed, file, *call_statement);
        let symbol = bound.symbol(parameter).unwrap();

        assert!(matches!(
            SourceFlowPlan::preflight(
                &bound,
                function,
                None,
                [*call_statement, *after_statement],
                [],
                [],
            ),
            Err(SourceFlowError::Unsupported(SourceFlowUnsupported::Call(node))) if node == call
        ));

        let plan = SourceFlowPlan::preflight_linear(
            &parsed.arena,
            &bound,
            function,
            [*call_statement, *after_statement],
            [],
            [],
            [call],
        )
        .unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        for _ in 0..2 {
            let mut frame = plan
                .frame(&bound, [(symbol, number)].into_iter().collect())
                .unwrap();
            let before = frame
                .snapshot_at(context.store_mut_for_test(), &globals, *call_statement)
                .unwrap();
            let after = frame
                .snapshot_at(context.store_mut_for_test(), &globals, *after_statement)
                .unwrap();
            assert_eq!(before, after);
            assert_eq!(after.type_of(symbol), Some(number));
            assert_eq!(
                frame
                    .snapshot_at(context.store_mut_for_test(), &globals, *after_statement)
                    .unwrap(),
                after,
            );
        }
    }

    #[test]
    fn parameter_assignment_flow_updates_only_its_authenticated_symbol() {
        for (index, parameters) in [
            "value: string | number, other: number",
            "[, value, , other]: (string | number)[]",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(&format!(
                "function effects({parameters}): void {{ value = 1; value; }}",
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(2_403 + u32::try_from(index).unwrap());
            let mut context = loop_context(&parsed, file);
            let bound = context.file(file).unwrap().1.clone();
            let globals = context.global_types().clone();
            let (function, first_parameter, statements) =
                linear_function_nodes(&parsed, file, "effects");
            let locals = bound.locals(function).unwrap();
            let [parameter, other] = ["value", "other"].map(|name| {
                let symbol = context
                    .store()
                    .symbol_table(locals)
                    .unwrap()
                    .get_source(name)
                    .unwrap();
                context
                    .store()
                    .symbol(symbol)
                    .unwrap()
                    .value_declaration()
                    .unwrap()
            });
            let [assignment_statement, after_statement] = statements.as_slice() else {
                panic!("expected one assignment and one following statement")
            };
            let expression = expression_statement_expression(&parsed, file, *assignment_statement);
            let NodeData::BinaryExpression(binary) =
                &parsed.arena.get(expression.node).unwrap().data
            else {
                panic!("expected an assignment expression")
            };
            let target = NodeRef::new(parsed.arena.id(), file, binary.left);
            let symbol = bound.symbol(parameter).unwrap();
            let assignment = SourceFlowParameterAssignment {
                target,
                parameter,
                symbol,
            };

            let plan = SourceFlowPlan::preflight_linear(
                &parsed.arena,
                &bound,
                function,
                [*assignment_statement, *after_statement],
                [],
                [assignment],
                [],
            )
            .unwrap();
            let (union, number) = {
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                (bootstrap.string_or_number_type, bootstrap.number_type)
            };
            for _ in 0..2 {
                let mut frame = plan
                    .frame(&bound, [(symbol, union)].into_iter().collect())
                    .unwrap();
                let before = frame
                    .snapshot_at(
                        context.store_mut_for_test(),
                        &globals,
                        *assignment_statement,
                    )
                    .unwrap();
                assert_eq!(before.type_of(symbol), Some(union));
                assert_eq!(
                    frame.snapshot_at(context.store_mut_for_test(), &globals, *after_statement),
                    Err(SourceFlowInvariant::PendingAssignment(target).into()),
                );
                frame.complete_assignment(target, symbol, number).unwrap();
                let after = frame
                    .snapshot_at(context.store_mut_for_test(), &globals, *after_statement)
                    .unwrap();
                assert_eq!(after.type_of(symbol), Some(number));
                assert_eq!(
                    frame.complete_assignment(target, symbol, number),
                    Err(SourceFlowInvariant::AssignmentAlreadyCompleted(target).into()),
                );
            }

            for other in [other, first_parameter] {
                if other == parameter {
                    continue;
                }
                let forged = SourceFlowParameterAssignment {
                    target,
                    parameter: other,
                    symbol: bound.symbol(other).unwrap(),
                };
                assert!(matches!(
                    SourceFlowPlan::preflight_linear(
                        &parsed.arena,
                        &bound,
                        function,
                        [*assignment_statement, *after_statement],
                        [],
                        [forged],
                        [],
                    ),
                    Err(SourceFlowError::Invariant(
                        SourceFlowInvariant::InvalidParameterAssignment(node)
                    )) if node == target
                ));
            }
        }
    }

    #[test]
    fn regular_enums_report_exact_use_before_declaration_diagnostics() {
        let parsed = parse_source_file(concat!(
            "function regular() { return Regular.A; enum Regular { A } }\n",
            "function constant() { return Fixed.A; const enum Fixed { A } }\n",
            "function declared() { enum Ready { A } return Ready.A; }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_404);
        let context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();

        let (regular, regular_read, regular_symbol) =
            declaration_use_nodes(&parsed, &bound, SyntaxKind::EnumDeclaration, "Regular");
        let diagnostic = source_block_scoped_use_before_declaration(
            &parsed.arena,
            &bound,
            context.store(),
            regular_read,
            regular_symbol,
            false,
        )
        .unwrap()
        .unwrap();
        assert_eq!(diagnostic.node, Some(regular_read));
        assert_eq!(diagnostic.diagnostic.code(), 2450);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Enum 'Regular' used before its declaration.",
        );
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("expected one enum declaration reference")
        };
        let NodeData::EnumDeclaration(enumeration) = &parsed.arena.get(regular.node).unwrap().data
        else {
            panic!("expected an enum declaration")
        };
        assert_eq!(
            related.node,
            Some(NodeRef::new(parsed.arena.id(), file, enumeration.name)),
        );
        assert_eq!(related.diagnostic.code(), 2728);
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "'Regular' is declared here.",
        );

        let (_, constant_read, constant_symbol) =
            declaration_use_nodes(&parsed, &bound, SyntaxKind::EnumDeclaration, "Fixed");
        assert_eq!(
            source_block_scoped_use_before_declaration(
                &parsed.arena,
                &bound,
                context.store(),
                constant_read,
                constant_symbol,
                false,
            ),
            Ok(None),
        );
        let isolated = source_block_scoped_use_before_declaration(
            &parsed.arena,
            &bound,
            context.store(),
            constant_read,
            constant_symbol,
            true,
        )
        .unwrap()
        .unwrap();
        assert_eq!(isolated.diagnostic.code(), 2450);

        let (_, declared_read, declared_symbol) =
            declaration_use_nodes(&parsed, &bound, SyntaxKind::EnumDeclaration, "Ready");
        assert_eq!(
            source_block_scoped_use_before_declaration(
                &parsed.arena,
                &bound,
                context.store(),
                declared_read,
                declared_symbol,
                false,
            ),
            Ok(None),
        );
    }

    #[test]
    fn block_scoped_variable_and_class_reads_keep_their_distinct_diagnostics() {
        let parsed = parse_source_file(concat!(
            "function locals() { ",
            "{ value; const value = 1; } ",
            "Model; class Model {} ",
            "const own = own; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_405);
        let context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();

        for (kind, name, code, message) in [
            (
                SyntaxKind::VariableDeclaration,
                "value",
                2448,
                "Block-scoped variable 'value' used before its declaration.",
            ),
            (
                SyntaxKind::ClassDeclaration,
                "Model",
                2449,
                "Class 'Model' used before its declaration.",
            ),
            (
                SyntaxKind::VariableDeclaration,
                "own",
                2448,
                "Block-scoped variable 'own' used before its declaration.",
            ),
        ] {
            let (_, read, symbol) = declaration_use_nodes(&parsed, &bound, kind, name);
            let diagnostic = source_block_scoped_use_before_declaration(
                &parsed.arena,
                &bound,
                context.store(),
                read,
                symbol,
                false,
            )
            .unwrap()
            .unwrap();
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
            assert_eq!(diagnostic.related_information[0].diagnostic.code(), 2728);
        }
    }

    #[test]
    fn deferred_and_ambient_reads_do_not_report_declaration_order_errors() {
        let parsed = parse_source_file(concat!(
            "function deferred() { ",
            "function later() { return Delayed.A; } ",
            "enum Delayed { A } ",
            "} ",
            "Ambient.A; declare enum Ambient { A }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_406);
        let context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();

        for name in ["Delayed", "Ambient"] {
            let (_, read, symbol) =
                declaration_use_nodes(&parsed, &bound, SyntaxKind::EnumDeclaration, name);
            assert_eq!(
                source_block_scoped_use_before_declaration(
                    &parsed.arena,
                    &bound,
                    context.store(),
                    read,
                    symbol,
                    false,
                ),
                Ok(None),
                "unexpected declaration-order diagnostic for {name}",
            );
        }
    }

    #[test]
    fn declaration_order_queries_reject_forged_symbols_and_foreign_nodes() {
        let parsed = parse_source_file(
            "function forged() { return Real.A; enum Real { A } enum Other { A } }",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_407);
        let context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let (_, read, _) =
            declaration_use_nodes(&parsed, &bound, SyntaxKind::EnumDeclaration, "Real");
        let other = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::EnumDeclaration(enumeration) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(enumeration.name)?.data else {
                    return None;
                };
                (name.text == "Other").then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let other_symbol = bound.symbol(other).unwrap();
        assert_eq!(
            source_block_scoped_use_before_declaration(
                &parsed.arena,
                &bound,
                context.store(),
                read,
                other_symbol,
                false,
            ),
            Err(SourceFlowInvariant::InvalidDeclarationUse(read).into()),
        );

        let foreign = NodeRef::new(parsed.arena.id(), FileId::new(9_999), read.node);
        assert_eq!(
            source_block_scoped_use_before_declaration(
                &parsed.arena,
                &bound,
                context.store(),
                foreign,
                other_symbol,
                false,
            ),
            Err(SourceFlowInvariant::ForeignNode(foreign).into()),
        );
    }

    fn declaration_use_nodes(
        parsed: &ParseResult,
        bound: &BoundFile,
        kind: SyntaxKind,
        expected_name: &str,
    ) -> (NodeRef, NodeRef, SemanticSymbolId) {
        let file = bound.file_id();
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                if record.kind != kind {
                    return None;
                }
                let name = match &record.data {
                    NodeData::VariableDeclaration(declaration) => declaration.name,
                    NodeData::ClassDeclaration(declaration) => declaration.name?,
                    NodeData::EnumDeclaration(declaration) => declaration.name,
                    _ => return None,
                };
                let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                    return None;
                };
                (name.text == expected_name).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let read = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::Identifier(name) = &record.data else {
                    return None;
                };
                if name.text != expected_name {
                    return None;
                }
                let parent = parsed.arena.get(record.parent?)?;
                let runtime_read = match &parent.data {
                    NodeData::PropertyAccessExpression(access) => access.expression == node,
                    NodeData::ExpressionStatement(statement) => statement.expression == node,
                    NodeData::VariableDeclaration(declaration) => {
                        declaration.initializer == Some(node)
                    }
                    _ => false,
                };
                runtime_read.then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        (declaration, read, bound.symbol(declaration).unwrap())
    }

    fn linear_function_nodes(
        parsed: &ParseResult,
        file: FileId,
        expected_name: &str,
    ) -> (NodeRef, NodeRef, Vec<NodeRef>) {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::FunctionDeclaration(function) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(function.name?)?.data
                else {
                    return None;
                };
                if identifier.text != expected_name {
                    return None;
                }
                let body = parsed.arena.get(function.body?)?;
                let NodeData::Block(body) = &body.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, *function.parameters.nodes.first()?),
                    body.statements
                        .nodes
                        .iter()
                        .map(|statement| NodeRef::new(parsed.arena.id(), file, *statement))
                        .collect(),
                ))
            })
            .unwrap()
    }

    fn expression_statement_expression(
        parsed: &ParseResult,
        file: FileId,
        statement: NodeRef,
    ) -> NodeRef {
        let NodeData::ExpressionStatement(statement) =
            &parsed.arena.get(statement.node).unwrap().data
        else {
            panic!("expected an expression statement")
        };
        NodeRef::new(parsed.arena.id(), file, statement.expression)
    }
}
