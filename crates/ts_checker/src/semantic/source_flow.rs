//! Invocation-local control-flow snapshots for source checking.
//!
//! This slice accepts the flow chains needed by direct identifier truthiness
//! and strict `typeof` comparisons: function `START`, initialized local
//! `ASSIGNMENT` nodes, condition edges, unreachable nodes, ordered branch
//! joins, and cyclic loop labels. Mutation expressions and switch-clause
//! narrowing remain typed capability boundaries.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use ts_ast::{FlowFlags, FlowNode, FlowNodePayload, FlowRef, NodeRef};
use ts_binder::{BoundFile, BoundFlowGraph, SemanticSymbolId};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, TypeId,
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
    conditions: HashMap<NodeRef, SourceFlowCondition>,
    assignments: HashMap<NodeRef, SourceFlowAssignment>,
    assignment_order: Vec<NodeRef>,
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
        conditions: impl IntoIterator<Item = SourceFlowCondition>,
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
            loop_snapshots: HashMap::new(),
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
            self.validate_flow(graph, flow, 0, &mut validated, &mut visiting, &mut coverage)?;
        }
        if let Some(end) = graph.container_end(self.container) {
            self.validate_flow(graph, end, 0, &mut validated, &mut visiting, &mut coverage)?;
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
            let node = flow_node(graph, flow)?;
            return if source_flow_kind(flow, node.flags)? == SourceFlowKind::LoopLabel {
                Ok(())
            } else {
                Err(SourceFlowInvariant::Cycle(flow).into())
            };
        }
        let result = self.validate_flow_uncached(graph, flow, depth, validated, visiting, coverage);
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
            SourceFlowKind::Unreachable => validate_unreachable_node(graph, flow, &node),
            SourceFlowKind::Start => validate_start_node(self, flow, &node),
            SourceFlowKind::Assignment => {
                let antecedent = linear_antecedent(flow, &node)?;
                let declaration = ast_payload(flow, &node)?;
                if !self.assignments.contains_key(&declaration) {
                    return Err(SourceFlowInvariant::UnknownAssignment(declaration).into());
                }
                coverage.assignments.insert(declaration);
                self.validate_flow(graph, antecedent, depth + 1, validated, visiting, coverage)
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
                    | SourceFlowKind::BranchLabel
                    | SourceFlowKind::LoopLabel => unreachable!(),
                };
                *coverage.condition_edges.entry(condition).or_default() |= edge;
                self.validate_flow(graph, antecedent, depth + 1, validated, visiting, coverage)
            }
            SourceFlowKind::BranchLabel | SourceFlowKind::LoopLabel => {
                for antecedent in label_antecedents(flow, &node)? {
                    self.validate_flow(
                        graph,
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

/// Confirms that `typeof` filtering can classify every union leaf without
/// invoking general relation, intersection, or type-parameter machinery.
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

fn narrow_by_typeof(
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
        let matches = source_typeof_leaf_matches(store, globals, *leaf, tag)?;
        if matches == require_match {
            let retained_leaf = if require_match
                && matches!(tag, SourceTypeofTag::Undefined)
                && record.flags().intersects(TypeFlags::VOID)
            {
                store
                    .intrinsic_bootstrap()
                    .map(|bootstrap| bootstrap.undefined_type)
                    .ok_or(SourceTypeofNarrowingError::MissingBootstrap)?
            } else {
                *leaf
            };
            retained.push(retained_leaf);
        } else if require_match
            && matches!(tag, SourceTypeofTag::Function)
            && record.flags().intersects(TypeFlags::NON_PRIMITIVE)
        {
            retained.push(globals.function_type);
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
) -> Result<bool, SourceTypeofNarrowingError> {
    let record = store
        .type_payload(type_)
        .ok_or(SourceTypeofNarrowingError::InvalidType(type_))?;
    let flags = record.flags();
    if flags.intersects(
        TypeFlags::ANY
            | TypeFlags::UNKNOWN
            | TypeFlags::TYPE_PARAMETER
            | TypeFlags::INTERSECTION
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
    Ok(matched)
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
            || value == FlowFlags::CALL.bits()
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
}
