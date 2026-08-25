//! Invocation-local control-flow snapshots for source checking.
//!
//! This slice accepts the flow chains needed by direct identifier truthiness
//! and strict `typeof` comparisons: function `START`, initialized local and
//! authenticated parameter `ASSIGNMENT` nodes, approved `CALL` nodes,
//! condition edges, unreachable nodes, ordered branch joins, and cyclic loop
//! labels. Authenticated declaration-order queries also retain the exact
//! block-scoped, class, and enum diagnostics. Other mutation expressions and
//! switch-clause narrowing remain typed capability boundaries.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use ts_ast::{
    FlowFlags, FlowNode, FlowNodePayload, FlowRef, NodeArena, NodeData, NodeRef, SyntaxKind,
};
use ts_binder::{BoundFile, BoundFlowGraph, SemanticSymbolId, SymbolFlags};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerRelatedInformation, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, TypeId,
    bootstrap::{LiteralTypeCacheError, UnionReduction},
    logical_operators::{LogicalBinaryError, TruthinessAssumption, narrow_by_truthiness},
    type_records::{TypeData, TypeRecord},
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

/// One cold-proven condition executable by the invocation-local flow frame.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFlowCondition {
    Truthiness(SourceTruthinessCondition),
    Typeof(SourceTypeofCondition),
}

impl SourceFlowCondition {
    const fn expression(self) -> NodeRef {
        match self {
            Self::Truthiness(condition) => condition.expression,
            Self::Typeof(condition) => condition.expression,
        }
    }

    const fn symbol(self) -> SemanticSymbolId {
        match self {
            Self::Truthiness(condition) => condition.symbol,
            Self::Typeof(condition) => condition.symbol,
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
    pub(super) parameter: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

/// Immutable, cold-preflighted flow identities for one callable invocation.
#[derive(Clone, Debug)]
pub(super) struct SourceFlowPlan {
    container: NodeRef,
    start: FlowRef,
    start_payload: Option<NodeRef>,
    points: HashMap<NodeRef, FlowRef>,
    point_order: Vec<NodeRef>,
    conditions: HashMap<NodeRef, SourceFlowCondition>,
    assignments: HashMap<NodeRef, SourceFlowAssignment>,
    assignment_order: Vec<NodeRef>,
    parameter_assignments: HashMap<NodeRef, NodeRef>,
    calls: HashMap<NodeRef, NodeRef>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFlowUnsupported {
    IncompleteContainer(NodeRef),
    FlowKind { flow: FlowRef, flags: FlowFlags },
    Call(NodeRef),
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
    AssignmentAlreadyCompleted(NodeRef),
    MissingCurrentType(SemanticSymbolId),
    TypeofNarrowing(SourceTypeofNarrowingError),
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

        Self::preflight_with_effects(
            bound,
            container,
            None,
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
        let start = graph
            .container_start(container)
            .ok_or(SourceFlowInvariant::MissingStart(container))?;
        let start_payload = preflight_start_payload(graph, container, start)?;
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
        let plan = Self {
            container,
            start,
            start_payload,
            points: planned_points,
            point_order,
            conditions: planned_conditions,
            assignments: planned_assignments,
            assignment_order,
            parameter_assignments: effects.parameter_assignments,
            calls: effects.calls,
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
            .container_start(self.container)
            .ok_or(SourceFlowInvariant::MissingStart(self.container))?;
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
        let graph = bound.flow_graph();
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
        if let Some(end) = graph.container_end(self.container) {
            self.validate_flow(bound, end, 0, &mut validated, &mut visiting, &mut coverage)?;
        }
        for declaration in self.assignments.keys() {
            if !coverage.assignments.contains(declaration) {
                return Err(SourceFlowInvariant::UnreachedAssignment(*declaration).into());
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
                if !self.assignments.contains_key(&declaration) {
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
                validate_call_container(bound, self.container, call, statement, antecedent)?;
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
                validate_call_container(
                    self.bound,
                    self.plan.container,
                    call,
                    statement,
                    antecedent,
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
    let parameter = arena.get(assignment.parameter.node).ok_or_else(invalid)?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter.data else {
        return Err(invalid().into());
    };
    let parameter_name = arena.get(parameter_data.name).ok_or_else(invalid)?;
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
            .filter(|node| **node == assignment.parameter.node)
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
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
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
            start,
            start_payload: None,
            points: HashMap::new(),
            point_order: Vec::new(),
            conditions: HashMap::new(),
            assignments: HashMap::new(),
            assignment_order: Vec::new(),
            parameter_assignments: HashMap::new(),
            calls: HashMap::new(),
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
        let parsed = parse_source_file(concat!(
            "function effects(value: string | number, other: number): void {\n",
            "  value = 1;\n",
            "  value;\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_403);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let (function, parameter, statements) = linear_function_nodes(&parsed, file, "effects");
        let [assignment_statement, after_statement] = statements.as_slice() else {
            panic!("expected one assignment and one following statement")
        };
        let expression = expression_statement_expression(&parsed, file, *assignment_statement);
        let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.node).unwrap().data
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

        let function_node = parsed.arena.get(function.node).unwrap();
        let NodeData::FunctionDeclaration(function_data) = &function_node.data else {
            panic!("expected a function declaration")
        };
        let other = NodeRef::new(parsed.arena.id(), file, function_data.parameters.nodes[1]);
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
