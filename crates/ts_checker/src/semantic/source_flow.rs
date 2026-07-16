//! Invocation-local control-flow snapshots for source checking.
//!
//! This first slice deliberately accepts only the linear flow chains needed by
//! a final `if`/`else` whose arms return: function `START`, direct identifier
//! truthiness conditions, and initialized local `ASSIGNMENT` nodes. Branch
//! joins, loops, reachability, and mutation expressions remain typed capability
//! boundaries.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use ts_ast::{FlowFlags, FlowNode, FlowNodePayload, FlowRef, NodeRef};
use ts_binder::{BoundFile, BoundFlowGraph, SemanticSymbolId};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, TypeId,
    logical_operators::{LogicalBinaryError, TruthinessAssumption, narrow_by_truthiness},
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

/// One initialized local represented by a binder assignment node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceFlowAssignment {
    /// The exact `VariableDeclaration` payload carried by the flow node.
    pub(super) declaration: NodeRef,
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
    conditions: HashMap<NodeRef, SourceTruthinessCondition>,
    assignments: HashMap<NodeRef, SourceFlowAssignment>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFlowUnsupported {
    IncompleteContainer(NodeRef),
    FlowKind { flow: FlowRef, flags: FlowFlags },
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
    UnknownCondition(NodeRef),
    UnknownAssignment(NodeRef),
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
    AssignmentAlreadyCompleted(NodeRef),
    MissingCurrentType(SemanticSymbolId),
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
    Start,
    Assignment,
    TrueCondition,
    FalseCondition,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceFlowAssignmentState {
    Pending,
    Resolved(TypeId),
}

#[derive(Default)]
struct SourceFlowCoverage {
    assignments: HashSet<NodeRef>,
    condition_edges: HashMap<NodeRef, u8>,
}

const TRUE_CONDITION_EDGE: u8 = 1 << 0;
const FALSE_CONDITION_EDGE: u8 = 1 << 1;
const BOTH_CONDITION_EDGES: u8 = TRUE_CONDITION_EDGE | FALSE_CONDITION_EDGE;

impl SourceFlowPlan {
    /// Freezes and validates every flow chain that the source executor may
    /// request. No semantic store state is read or written during preflight.
    pub(super) fn preflight(
        bound: &BoundFile,
        container: NodeRef,
        expected_start_payload: Option<NodeRef>,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceTruthinessCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
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
            validate_bound_node(bound, graph, condition.expression)?;
            if planned_conditions
                .insert(condition.expression, condition)
                .is_some()
            {
                return Err(SourceFlowInvariant::DuplicateCondition(condition.expression).into());
            }
        }

        let mut planned_assignments = HashMap::new();
        for assignment in assignments {
            validate_bound_node(bound, graph, assignment.declaration)?;
            if planned_assignments
                .insert(assignment.declaration, assignment)
                .is_some()
            {
                return Err(
                    SourceFlowInvariant::DuplicateAssignment(assignment.declaration).into(),
                );
            }
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
        };
        plan.validate_flow_paths(graph)?;
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
        Ok(SourceFlowFrame {
            plan: self,
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
        })
    }

    fn validate_flow_paths(&self, graph: &BoundFlowGraph) -> Result<(), SourceFlowError> {
        let mut validated = HashSet::new();
        let mut visiting = HashSet::new();
        let mut coverage = SourceFlowCoverage::default();
        for point in &self.point_order {
            let flow = *self
                .points
                .get(point)
                .ok_or(SourceFlowInvariant::MissingFlowPoint(*point))?;
            self.validate_flow(
                graph,
                flow,
                0,
                &mut validated,
                &mut visiting,
                &mut coverage,
            )?;
        }
        for declaration in self.assignments.keys() {
            if !coverage.assignments.contains(declaration) {
                return Err(SourceFlowInvariant::UnreachedAssignment(*declaration).into());
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
        graph: &BoundFlowGraph,
        flow: FlowRef,
        depth: usize,
        validated: &mut HashSet<FlowRef>,
        visiting: &mut HashSet<FlowRef>,
        coverage: &mut SourceFlowCoverage,
    ) -> Result<(), SourceFlowError> {
        if validated.contains(&flow) {
            return Ok(());
        }
        if depth > FLOW_DEPTH_LIMIT {
            return Err(SourceFlowInvariant::DepthLimit(flow).into());
        }
        if !visiting.insert(flow) {
            return Err(SourceFlowInvariant::Cycle(flow).into());
        }
        let result =
            self.validate_flow_uncached(graph, flow, depth, validated, visiting, coverage);
        let removed = visiting.remove(&flow);
        debug_assert!(removed);
        if result.is_ok() {
            validated.insert(flow);
        }
        result
    }

    fn validate_flow_uncached(
        &self,
        graph: &BoundFlowGraph,
        flow: FlowRef,
        depth: usize,
        validated: &mut HashSet<FlowRef>,
        visiting: &mut HashSet<FlowRef>,
        coverage: &mut SourceFlowCoverage,
    ) -> Result<(), SourceFlowError> {
        let node = flow_node(graph, flow)?;
        match source_flow_kind(flow, node.flags)? {
            SourceFlowKind::Start => validate_start_node(self, flow, &node),
            SourceFlowKind::Assignment => {
                let antecedent = linear_antecedent(flow, &node)?;
                let declaration = ast_payload(flow, &node)?;
                if !self.assignments.contains_key(&declaration) {
                    return Err(SourceFlowInvariant::UnknownAssignment(declaration).into());
                }
                coverage.assignments.insert(declaration);
                self.validate_flow(
                    graph,
                    antecedent,
                    depth + 1,
                    validated,
                    visiting,
                    coverage,
                )
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
                    SourceFlowKind::Start | SourceFlowKind::Assignment => unreachable!(),
                };
                *coverage.condition_edges.entry(condition).or_default() |= edge;
                self.validate_flow(
                    graph,
                    antecedent,
                    depth + 1,
                    validated,
                    visiting,
                    coverage,
                )
            }
        }
    }
}

/// Mutable state for exactly one source-callable execution.
pub(super) struct SourceFlowFrame<'plan, 'graph> {
    plan: &'plan SourceFlowPlan,
    graph: &'graph BoundFlowGraph,
    base: SourceFlowSnapshot,
    assignment_states: HashMap<NodeRef, SourceFlowAssignmentState>,
    memo: HashMap<FlowRef, SourceFlowSnapshot>,
    visiting: HashSet<FlowRef>,
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
        if let Ok(snapshot) = &result {
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
                    .type_of(condition.symbol)
                    .ok_or(SourceFlowInvariant::MissingCurrentType(condition.symbol))?;
                let assumption = match kind {
                    SourceFlowKind::TrueCondition => TruthinessAssumption::Truthy,
                    SourceFlowKind::FalseCondition => TruthinessAssumption::Falsy,
                    SourceFlowKind::Start | SourceFlowKind::Assignment => unreachable!(),
                };
                let narrowed = narrow_by_truthiness(store, Some(globals), current, assumption)
                    .map_err(|error| SourceFlowError::Narrowing {
                        condition: condition_node,
                        error,
                    })?;
                Ok(prior.with_type(condition.symbol, narrowed))
            }
        }
    }
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
    if semantic == FlowFlags::START.bits() {
        return Ok(SourceFlowKind::Start);
    }
    if semantic == FlowFlags::ASSIGNMENT.bits() {
        return Ok(SourceFlowKind::Assignment);
    }
    if semantic == FlowFlags::TRUE_CONDITION.bits() {
        return Ok(SourceFlowKind::TrueCondition);
    }
    if semantic == FlowFlags::FALSE_CONDITION.bits() {
        return Ok(SourceFlowKind::FalseCondition);
    }
    if matches!(
        semantic,
        value if value == FlowFlags::UNREACHABLE.bits()
            || value == FlowFlags::BRANCH_LABEL.bits()
            || value == FlowFlags::LOOP_LABEL.bits()
            || value == FlowFlags::SWITCH_CLAUSE.bits()
            || value == FlowFlags::ARRAY_MUTATION.bits()
            || value == FlowFlags::CALL.bits()
            || value == FlowFlags::REDUCE_LABEL.bits()
    ) {
        return Err(SourceFlowUnsupported::FlowKind { flow, flags }.into());
    }
    Err(SourceFlowInvariant::InvalidFlowFlags { flow, flags }.into())
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

fn ast_payload(flow: FlowRef, node: &FlowNode) -> Result<NodeRef, SourceFlowError> {
    match node.payload.as_ref() {
        Some(FlowNodePayload::Ast(node)) => Ok(*node),
        _ => Err(SourceFlowInvariant::InvalidPayload(flow).into()),
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, FlowNodeId, NodeArena, NodeId};

    use super::*;

    fn flow() -> FlowRef {
        let arena = NodeArena::default();
        FlowRef::new(arena.id(), FileId::new(7), FlowNodeId(3))
    }

    #[test]
    fn metadata_bits_do_not_change_admitted_flow_kinds() {
        let flow = flow();
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
            source_flow_kind(flow, FlowFlags::TRUE_CONDITION | FlowFlags::REFERENCED,),
            Ok(SourceFlowKind::TrueCondition),
        );
        assert_eq!(
            source_flow_kind(flow, FlowFlags::FALSE_CONDITION | FlowFlags::SHARED),
            Ok(SourceFlowKind::FalseCondition),
        );
    }

    #[test]
    fn joins_are_unsupported_and_composite_semantic_kinds_are_invariants() {
        let flow = flow();
        assert_eq!(
            source_flow_kind(flow, FlowFlags::BRANCH_LABEL | FlowFlags::SHARED),
            Err(SourceFlowError::Unsupported(
                SourceFlowUnsupported::FlowKind {
                    flow,
                    flags: FlowFlags::BRANCH_LABEL | FlowFlags::SHARED,
                },
            )),
        );
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
}
