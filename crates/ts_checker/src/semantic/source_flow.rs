//! Invocation-local control-flow snapshots for source checking.
//!
//! This slice accepts the flow chains needed by direct identifier truthiness,
//! strict `typeof` comparisons, nullable equality, and declared discriminants:
//! function `START`, local and parameter `ASSIGNMENT` nodes, checked array
//! mutations, approved `CALL` nodes, condition edges, unreachable nodes, ordered
//! branch joins, and cyclic loop labels. Authenticated declaration-order queries
//! also retain the exact block-scoped, class, and enum diagnostics. Other
//! mutation expressions and switch-clause narrowing remain typed capability
//! boundaries.
//! Class initialization keeps the actual constructor exit and super-call edges.
//! Static blocks retain their outer start and receiver-specific property keys.
//! Field initializers retain their own flow containers. Local destructuring
//! assignments do not initialize class fields.
//! Private destructuring leaves use the real field assignment and source property.
//! Source-file field reads use checked own-field writes and real binder references.
//! Unknown flow effects and affected computed or binding reads stay unsupported.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use ts_ast::{
    FlowFlags, FlowNode, FlowNodeArena, FlowNodeId, FlowNodePayload, FlowRef, NodeArena,
    NodeArenaRevision, NodeData, NodeRef, SyntaxKind,
};
use ts_binder::{
    BoundFile, BoundFlowGraph, CanonicalNameResolver, CanonicalResolutionLocation, CheckFlags,
    EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerOptions, CanonicalCheckerRelatedInformation,
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost, EffectsSignatureState,
    RelationUnavailable, SignatureId, SymbolNodeLinks, TypeId, TypeNodeLinks, TypePredicateId,
    array_types::{ArrayTypeError, CanonicalArrayTargets},
    bootstrap::{LiteralTypeCacheError, UnionReduction},
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set_with_array_targets},
    classes::{
        ClassBodyAccessToken, ClassBodyKind, ClassBodyPlan, ClassMemberOrigin, ClassMemberSource,
        ClassPropertySide, class_body_identities, class_member_source,
    },
    instantiate::InstantiationSession,
    logical_operators::{
        LogicalBinaryError, TruthinessAssumption, base_type_of_literal_type, narrow_by_truthiness,
        narrow_by_truthiness_with_session,
    },
    relation::RelationKind,
    signatures::TypePredicateKind,
    source::{CheckedClassPropertyAssignment, PlannedExpressionKind, PlannedIdentifierRead},
    source_calls::{
        CheckedSourceCall, SourceCallPlan, plan_direct_source_call_syntax,
        resolve_source_call_effects_signature,
    },
    source_properties::{
        ClassAccessContext, ClassPropertyTruthinessSource, OwnClassPropertyWritePlan,
        SourceClassPropertyWritePlan, SourcePropertyError, class_destructuring_write_assignment,
        plan_class_destructuring_property_write, plan_class_property_truthiness,
        plan_class_property_write, validate_class_property_write_access,
        validate_own_class_property_write_target,
    },
    source_statements::{
        SourceCallableCatchBindingSyntax, SourceCallableStatementListSyntax,
        SourceCallableStatementSyntax, SourceCapturedIterationStatementSyntax,
        SourceLinearFunctionStatementSyntax, SourceLinearLogicalStatementSyntax,
        SourceLocalDeclarationSyntax, plan_source_callable_statement_list_syntax,
        plan_source_for_statement_syntax, plan_source_linear_logical_statement_syntax,
    },
    type_records::{LiteralValue, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
    variables::{VariableBindingKind, plan_top_level_variable},
};

const FLOW_DEPTH_LIMIT: usize = 2_000;
const FLOW_METADATA_BITS: u32 = FlowFlags::REFERENCED.bits() | FlowFlags::SHARED.bits();

pub(super) type SourceFlowTypes = HashMap<SemanticSymbolId, TypeId>;

/// Checked source writes for one source-check invocation, keyed by their real targets.
#[derive(Default)]
pub(super) struct OwnClassPropertyFlow {
    assignments: HashMap<NodeRef, CompletedOwnClassPropertyWrite>,
}

struct CompletedOwnClassPropertyWrite {
    plan: OwnClassPropertyWritePlan,
    receiver_type: TypeId,
    declared_type: TypeId,
    assigned_type: TypeId,
    flow_type: TypeId,
}

impl CompletedOwnClassPropertyWrite {
    fn validate(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        options: CanonicalCheckerOptions,
    ) -> Result<(), SourceFlowError> {
        let assignment = self.plan.assignment();
        let invalid = || SourceFlowInvariant::InvalidClassProperty(assignment.left);
        let checked = validate_own_class_property_write_target(
            store,
            host,
            options,
            &self.plan,
            self.receiver_type,
        )
        .map_err(|_| invalid())?;
        if checked.declared_type != self.declared_type
            || store.type_node_links(assignment.expression)
                != Some(&super::TypeNodeLinks {
                    resolved_type: Some(self.assigned_type),
                    ..super::TypeNodeLinks::default()
                })
            || store.type_payload(self.flow_type).is_none()
        {
            return Err(invalid().into());
        }
        Ok(())
    }
}

impl OwnClassPropertyFlow {
    pub(super) fn matching_receiver_symbol(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        receiver: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, SourceFlowError> {
        if self.assignments.is_empty() {
            return Ok(None);
        }
        let bound = host
            .bound_file(receiver)
            .ok_or(SourceFlowInvariant::ForeignNode(receiver))?;
        let symbol = own_class_flow_reference_symbol(store, host, bound, receiver)?;
        Ok(symbol.filter(|symbol| {
            self.assignments
                .values()
                .any(|write| write.plan.assignment().receiver_symbol == *symbol)
        }))
    }

    pub(super) fn has_reference(&self, receiver: SemanticSymbolId, name: &str) -> bool {
        self.assignments.values().any(|write| {
            write.plan.assignment().receiver_symbol == receiver && write.plan.name() == name
        })
    }

    pub(super) fn has_checked_reference(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        options: CanonicalCheckerOptions,
        receiver: SemanticSymbolId,
        name: Option<&str>,
    ) -> Result<bool, SourceFlowError> {
        let mut affected = false;
        for write in self.assignments.values().filter(|write| {
            write.plan.assignment().receiver_symbol == receiver
                && name.is_none_or(|name| write.plan.name() == name)
        }) {
            write.validate(store, host, options)?;
            affected = true;
        }
        Ok(affected)
    }

    /// Computed reads need their own reference proof before they can use checked writes.
    pub(super) fn has_unproved_element_read(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        options: CanonicalCheckerOptions,
        plan: &super::source_elements::SourceElementPlan,
    ) -> Result<bool, SourceFlowError> {
        let Some(receiver_symbol) =
            self.matching_receiver_symbol(store, host, plan.receiver.node)?
        else {
            return Ok(false);
        };
        let invalid = || SourceFlowInvariant::InvalidClassProperty(plan.node);
        let (arena, bound) = host.source(plan.node).ok_or_else(invalid)?;
        own_class_flow_node(store, host, plan.node)?;
        let syntax =
            super::source_elements::plan_direct_source_element_syntax(arena, store, plan.node)
                .map_err(|_| invalid())?;
        if syntax.receiver() != plan.receiver.node
            || syntax.index() != plan.index.node
            || own_class_flow_symbol(store, host, bound, plan.receiver.node)? != receiver_symbol
        {
            return Err(invalid().into());
        }
        let name = match &own_class_flow_node(store, host, plan.index.node)?.data {
            NodeData::StringLiteral(literal) => Some(literal.text.as_str()),
            NodeData::NoSubstitutionTemplateLiteral(literal) => Some(literal.text.as_str()),
            _ => None,
        };
        let affected = self.has_checked_reference(store, host, options, receiver_symbol, name)?;
        if affected
            && (store
                .type_node_links(plan.node)
                .is_some_and(|links| links != &super::TypeNodeLinks::default())
                || store
                    .symbol_node_links(plan.node)
                    .is_some_and(|links| links != &super::SymbolNodeLinks::default()))
        {
            return Err(invalid().into());
        }
        Ok(affected)
    }

    #[allow(clippy::too_many_arguments)] // Retain the result checked with the source caller's session.
    pub(super) fn complete_assignment(
        &mut self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        options: CanonicalCheckerOptions,
        plan: &OwnClassPropertyWritePlan,
        receiver_type: TypeId,
        assigned_type: TypeId,
        flow_type: TypeId,
    ) -> Result<(), SourceFlowError> {
        let assignment = plan.assignment();
        let invalid = || SourceFlowInvariant::InvalidClassProperty(assignment.left);
        let checked =
            validate_own_class_property_write_target(store, host, options, plan, receiver_type)
                .map_err(|_| invalid())?;
        let bound = host.bound_file(assignment.left).ok_or_else(invalid)?;
        if bound.flow_container(assignment.left) != Some(bound.source_file())
            || bound.flow_at(assignment.left).is_none()
            || store.type_node_links(assignment.expression)
                != Some(&super::TypeNodeLinks {
                    resolved_type: Some(assigned_type),
                    ..super::TypeNodeLinks::default()
                })
            || store.type_payload(flow_type).is_none()
            || self.assignments.contains_key(&assignment.left)
        {
            return Err(invalid().into());
        }
        self.assignments.insert(
            assignment.left,
            CompletedOwnClassPropertyWrite {
                plan: plan.clone(),
                receiver_type,
                declared_type: checked.declared_type,
                assigned_type,
                flow_type,
            },
        );
        Ok(())
    }

    /// Uses the actual source flow chain. Other instances of the same class do not match.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub(super) fn read_type(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        options: CanonicalCheckerOptions,
        access: NodeRef,
        receiver_symbol: SemanticSymbolId,
        receiver_type: TypeId,
        member: SemanticSymbolId,
        declared_type: TypeId,
    ) -> Result<Option<TypeId>, SourceFlowError> {
        if !self.assignments.values().any(|write| {
            write.plan.assignment().receiver_symbol == receiver_symbol
                && write.plan.member_source().symbol == member
        }) {
            return Ok(None);
        }
        let invalid = || SourceFlowInvariant::InvalidClassProperty(access);
        let bound = host.bound_file(access).ok_or_else(invalid)?;
        let container = bound.source_file();
        if bound.flow_container(access) != Some(container) {
            return Ok(None);
        }
        let graph = bound.flow_graph();
        if graph.container_is_complete(container) != Some(true) {
            return Err(SourceFlowUnsupported::IncompleteContainer(container).into());
        }
        let start = graph
            .container_start(container)
            .ok_or(SourceFlowInvariant::MissingStart(container))?;
        preflight_start_payload(graph, container, start)?;
        let record = own_class_flow_node(store, host, access)?;
        if is_property_assignment_target(host, access) {
            return Err(invalid().into());
        }
        let NodeData::PropertyAccessExpression(property) = &record.data else {
            return Err(invalid().into());
        };
        let receiver = NodeRef::new(access.arena, access.file, property.expression);
        let name = NodeRef::new(access.arena, access.file, property.name);
        let NodeData::Identifier(name) = &own_class_flow_node(store, host, name)?.data else {
            return Err(invalid().into());
        };
        if own_class_flow_symbol(store, host, bound, receiver)? != receiver_symbol {
            return Err(invalid().into());
        }
        let mut current = bound
            .flow_at(access)
            .ok_or(SourceFlowInvariant::MissingFlowPoint(access))?;
        let mut visited = HashSet::new();
        loop {
            if !visited.insert(current) {
                return Err(SourceFlowInvariant::Cycle(current).into());
            }
            if visited.len() > FLOW_DEPTH_LIMIT {
                return Err(SourceFlowInvariant::DepthLimit(current).into());
            }
            let node = flow_node(graph, current)?;
            match source_flow_kind(current, node.flags)? {
                SourceFlowKind::Start => {
                    if current != start {
                        return Err(SourceFlowInvariant::InvalidStart(current).into());
                    }
                    preflight_start_payload(graph, container, current)?;
                    return Ok(Some(declared_type));
                }
                SourceFlowKind::Assignment => {
                    let antecedent = linear_antecedent(current, &node)?;
                    flow_node(graph, antecedent)?;
                    if antecedent == current {
                        return Err(SourceFlowInvariant::Cycle(current).into());
                    }
                    let target = ast_payload(current, &node)?;
                    validate_bound_node(bound, graph, target)?;
                    let target_node = own_class_flow_node(store, host, target)?;
                    if let Some(write) = self.assignments.get(&target) {
                        let assignment = write.plan.assignment();
                        if assignment.left != target
                            || bound.flow_container(target) != Some(container)
                        {
                            return Err(SourceFlowInvariant::InvalidClassProperty(target).into());
                        }
                        write.validate(store, host, options)?;
                        if assignment.receiver_symbol == receiver_symbol
                            && write.plan.member_source().symbol == member
                        {
                            if write.receiver_type != receiver_type
                                || write.declared_type != declared_type
                            {
                                return Err(invalid().into());
                            }
                            return Ok(Some(write.flow_type));
                        }
                    } else {
                        match &target_node.data {
                            NodeData::VariableDeclaration(_) => {
                                let symbol = bound
                                    .symbol(target)
                                    .and_then(|symbol| store.get_merged_symbol(symbol))
                                    .ok_or_else(invalid)?;
                                if symbol == receiver_symbol {
                                    return Ok(Some(declared_type));
                                }
                            }
                            NodeData::Identifier(_) => {
                                if own_class_flow_symbol(store, host, bound, target)?
                                    == receiver_symbol
                                {
                                    return Ok(Some(declared_type));
                                }
                            }
                            NodeData::PropertyAccessExpression(property) => {
                                let receiver =
                                    NodeRef::new(target.arena, target.file, property.expression);
                                let property_name =
                                    NodeRef::new(target.arena, target.file, property.name);
                                let NodeData::Identifier(property_name) =
                                    &own_class_flow_node(store, host, property_name)?.data
                                else {
                                    return Err(SourceFlowUnsupported::PropertyWrite(target).into());
                                };
                                if own_class_flow_symbol(store, host, bound, receiver)?
                                    == receiver_symbol
                                    && property_name.text == name.text
                                {
                                    return Err(SourceFlowUnsupported::PropertyWrite(target).into());
                                }
                            }
                            _ => return Err(SourceFlowUnsupported::PropertyWrite(target).into()),
                        }
                    }
                    current = antecedent;
                }
                SourceFlowKind::Unreachable => {
                    validate_unreachable_node(graph, current, &node)?;
                    return Err(SourceFlowUnsupported::FlowKind {
                        flow: current,
                        flags: node.flags,
                    }
                    .into());
                }
                SourceFlowKind::BranchLabel | SourceFlowKind::LoopLabel => {
                    for &antecedent in label_antecedents(current, &node)? {
                        flow_node(graph, antecedent)?;
                    }
                    return Err(SourceFlowUnsupported::FlowKind {
                        flow: current,
                        flags: node.flags,
                    }
                    .into());
                }
                SourceFlowKind::Call
                | SourceFlowKind::ArrayMutation
                | SourceFlowKind::TrueCondition
                | SourceFlowKind::FalseCondition => {
                    let payload = ast_payload(current, &node)?;
                    validate_bound_node(bound, graph, payload)?;
                    own_class_flow_node(store, host, payload)?;
                    flow_node(graph, linear_antecedent(current, &node)?)?;
                    return Err(SourceFlowUnsupported::FlowKind {
                        flow: current,
                        flags: node.flags,
                    }
                    .into());
                }
            }
        }
    }
}

fn own_class_flow_node<'host>(
    store: &CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<&'host ts_ast::Node, SourceFlowError> {
    let invalid = || SourceFlowInvariant::ForeignNode(node);
    let record = super::declared::preflight_node(store, host, node).map_err(|_| invalid())?;
    let parent = record
        .parent
        .map_or(super::store::SourceNodeParent::Root, |parent| {
            super::store::SourceNodeParent::Parent(NodeRef::new(node.arena, node.file, parent))
        });
    if store.source_node_kind(node) != Some(record.kind)
        || store.source_node_parent(node) != Some(parent)
    {
        return Err(invalid().into());
    }
    Ok(record)
}

fn own_class_flow_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    bound: &BoundFile,
    node: NodeRef,
) -> Result<SemanticSymbolId, SourceFlowError> {
    own_class_flow_reference_symbol(store, host, bound, node)?
        .ok_or_else(|| SourceFlowUnsupported::PropertyWrite(node).into())
}

/// Match the reference wrappers used by Go without reading any annotation type.
#[allow(clippy::too_many_lines)] // Keep each source edge and the final symbol proof in one walk.
fn own_class_flow_reference_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    bound: &BoundFile,
    mut node: NodeRef,
) -> Result<Option<SemanticSymbolId>, SourceFlowError> {
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(node) || visited.len() > FLOW_DEPTH_LIMIT {
            return Err(SourceFlowInvariant::InvalidClassProperty(node).into());
        }
        let invalid = || SourceFlowInvariant::InvalidClassProperty(node);
        let record = own_class_flow_node(store, host, node)?;
        let child = match &record.data {
            NodeData::Identifier(_) => break,
            NodeData::ParenthesizedExpression(wrapper)
                if record.kind == SyntaxKind::ParenthesizedExpression =>
            {
                wrapper.expression
            }
            NodeData::NonNullExpression(wrapper)
                if record.kind == SyntaxKind::NonNullExpression =>
            {
                wrapper.expression
            }
            NodeData::SatisfiesExpression(wrapper)
                if record.kind == SyntaxKind::SatisfiesExpression =>
            {
                let annotation = NodeRef::new(node.arena, node.file, wrapper.type_);
                if own_class_flow_node(store, host, annotation)?.parent != Some(node.node) {
                    return Err(invalid().into());
                }
                wrapper.expression
            }
            NodeData::BinaryExpression(binary) if record.kind == SyntaxKind::BinaryExpression => {
                let operator = NodeRef::new(node.arena, node.file, binary.operator_token);
                let operator = own_class_flow_node(store, host, operator)?;
                if operator.kind != SyntaxKind::CommaToken {
                    return Ok(None);
                }
                let left = NodeRef::new(node.arena, node.file, binary.left);
                if operator.parent != Some(node.node)
                    || operator.flags.0 != 0
                    || !matches!(operator.data, NodeData::Token(_))
                    || binary.facts != 0
                    || binary.symbol.is_some()
                    || binary.type_.is_some()
                    || binary.modifiers.is_some()
                    || own_class_flow_node(store, host, left)?.parent != Some(node.node)
                {
                    return Err(invalid().into());
                }
                binary.right
            }
            _ => return Ok(None),
        };
        let child = NodeRef::new(node.arena, node.file, child);
        let child_record = own_class_flow_node(store, host, child)?;
        if record.flags.0 != 0
            || child_record.parent != Some(node.node)
            || child_record.range.start < record.range.start
            || child_record.range.end > record.range.end
        {
            return Err(invalid().into());
        }
        node = child;
    }
    let invalid = || SourceFlowInvariant::InvalidClassProperty(node);
    let record = own_class_flow_node(store, host, node)?;
    let NodeData::Identifier(identifier) = &record.data else {
        return Err(SourceFlowUnsupported::PropertyWrite(node).into());
    };
    let (arena, actual_bound) = host.source(node).ok_or_else(invalid)?;
    if actual_bound.source_file() != bound.source_file()
        || record.kind != SyntaxKind::Identifier
        || record.flags.0 != 0
        || identifier.flow_node.is_some()
    {
        return Err(invalid().into());
    }
    let mut callback = host.name_resolver_host(store).map_err(|_| invalid())?;
    let mut resolver =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback)
            .map_err(|_| invalid())?;
    let symbol = resolver
        .resolve(
            Some(CanonicalResolutionLocation::Bound(node)),
            &identifier.text,
            SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
            None,
            false,
            false,
        )
        .map_err(|_| invalid())?;
    let Some(symbol) = symbol else {
        if store
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol)
            .is_some_and(|cached| {
                store
                    .intrinsic_bootstrap()
                    .is_none_or(|bootstrap| cached != bootstrap.unknown_symbol)
            })
        {
            return Err(invalid().into());
        }
        return Ok(None);
    };
    if store
        .symbol_node_links(node)
        .and_then(|links| links.resolved_symbol)
        .is_some_and(|cached| cached != symbol)
    {
        return Err(invalid().into());
    }
    let symbol = store
        .symbol(symbol)
        .and_then(ts_binder::semantic::Symbol::export_symbol)
        .unwrap_or(symbol);
    store
        .get_merged_symbol(symbol)
        .map(Some)
        .ok_or_else(|| invalid().into())
}

/// One immutable map of current invocation-local symbol types.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceFlowSnapshot {
    types: Arc<SourceFlowTypes>,
    reachable: bool,
    incomplete: bool,
}

impl SourceFlowSnapshot {
    fn new(types: SourceFlowTypes) -> Self {
        Self {
            types: Arc::new(types),
            reachable: true,
            incomplete: false,
        }
    }

    #[must_use]
    pub(super) fn types(&self) -> &SourceFlowTypes {
        self.types.as_ref()
    }

    #[must_use]
    pub(super) fn type_of(&self, symbol: SemanticSymbolId) -> Option<TypeId> {
        self.types.get(&symbol).copied()
    }

    fn with_type(&self, symbol: SemanticSymbolId, type_: TypeId) -> Self {
        if self.type_of(symbol) == Some(type_) {
            return self.clone();
        }
        let mut updated = self.types().clone();
        updated.insert(symbol, type_);
        Self {
            types: Arc::new(updated),
            reachable: self.reachable,
            incomplete: self.incomplete,
        }
    }
}

/// An update target and the declaration found through the lexical resolver.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceFlowUpdate {
    pub(super) target: NodeRef,
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) readonly: bool,
}

/// A call fact keeps the checked effects signature and its actual argument.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFlowCallEffect {
    Unchanged,
    Assertion {
        signature: SignatureId,
        argument: NodeRef,
        symbol: SemanticSymbolId,
    },
    AssertionNoReference {
        signature: SignatureId,
        argument: Option<NodeRef>,
    },
    AssertionFalse {
        signature: SignatureId,
        argument: NodeRef,
    },
    Never(SignatureId),
}

/// A source statement uses its real entry and following source-file flow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceFlowRegion {
    statement: NodeRef,
    entry_node: NodeRef,
    entry: FlowRef,
    exit: FlowRef,
    unreachable_incrementor: Option<NodeRef>,
}

/// An identifier narrowed on an `if` edge, including enclosing `!` operators.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceTruthinessCondition {
    /// The exact AST payload carried by both binder condition nodes.
    pub(super) expression: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) negated: bool,
}

/// The left operand of an authenticated `??` or `??=` uses presence, not truthiness.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceNullishCondition {
    pub(super) expression: NodeRef,
    pub(super) symbol: Option<SemanticSymbolId>,
}

/// A planned expression condition still needs its source and retained-edge proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceClassExpressionCondition {
    pub(super) owner: NodeRef,
    pub(super) expression: NodeRef,
    pub(super) kind: SourceClassExpressionConditionKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceClassExpressionConditionKind {
    Nullish(SemanticSymbolId),
    Truthiness(SemanticSymbolId, bool),
    Call,
}

#[derive(Clone, Copy, Debug)]
struct SourceClassExpressionConditionProof {
    source: SourceClassExpressionCondition,
    /// Only edges reachable from this body's read points and effective exit.
    edges: u8,
}

/// A checked nullish write keeps its real target and declaration separate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceFlowNullishAssignment {
    pub(super) expression: NodeRef,
    pub(super) target: NodeRef,
    pub(super) declaration: Option<NodeRef>,
    pub(super) symbol: Option<SemanticSymbolId>,
    pub(super) readonly: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceNullishAssignmentProof {
    assignment: SourceFlowNullishAssignment,
    receiver: Option<SemanticSymbolId>,
    flow: Option<FlowRef>,
    revision: NodeArenaRevision,
}

/// One ordinary member write retains its source nodes and binder assignment edge.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceMemberAssignmentProof {
    pub(super) expression: NodeRef,
    pub(super) target: NodeRef,
    pub(super) receiver: NodeRef,
    pub(super) right: NodeRef,
    receiver_symbol: SemanticSymbolId,
    container: NodeRef,
    flow: FlowRef,
    revision: NodeArenaRevision,
}

/// A direct current-class field on the binder's real condition edges.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceClassPropertyTruthinessCondition {
    pub(super) expression: NodeRef,
    pub(super) access: NodeRef,
    pub(super) negated: bool,
}

/// A direct own-field comparison with the canonical global undefined value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceClassPropertyEqualityCondition {
    pub(super) expression: NodeRef,
    pub(super) access: NodeRef,
    pub(super) value: NodeRef,
    pub(super) comparison: SourceTypeofComparison,
}

/// A predicate call and the exact current-class field passed to it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceClassPropertyPredicateCondition {
    pub(super) expression: NodeRef,
    pub(super) call: NodeRef,
    pub(super) access: NodeRef,
    pub(super) negated: bool,
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

/// The exact operands of a checked property or class membership condition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceInCondition {
    pub(super) expression: NodeRef,
    pub(super) receiver: NodeRef,
    pub(super) key: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

/// A source condition. Expression candidates need preflight before execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFlowCondition {
    ClassExpression(SourceClassExpressionCondition),
    Unchanged(NodeRef),
    Nullish(SourceNullishCondition),
    Truthiness(SourceTruthinessCondition),
    ClassPropertyTruthiness(SourceClassPropertyTruthinessCondition),
    ClassPropertyEquality(SourceClassPropertyEqualityCondition),
    ClassPropertyPredicate(SourceClassPropertyPredicateCondition),
    Typeof(SourceTypeofCondition),
    Equality(SourceEqualityCondition),
    In(SourceInCondition),
    InstanceOf(SourceInCondition),
}

impl SourceFlowCondition {
    pub(super) const fn expression(self) -> NodeRef {
        match self {
            Self::ClassExpression(condition) => condition.expression,
            Self::Unchanged(expression) => expression,
            Self::Nullish(condition) => condition.expression,
            Self::Truthiness(condition) => condition.expression,
            Self::ClassPropertyTruthiness(condition) => condition.expression,
            Self::ClassPropertyEquality(condition) => condition.expression,
            Self::ClassPropertyPredicate(condition) => condition.expression,
            Self::Typeof(condition) => condition.expression,
            Self::Equality(condition) => condition.expression,
            Self::In(condition) | Self::InstanceOf(condition) => condition.expression,
        }
    }

    const fn symbol(self) -> Option<SemanticSymbolId> {
        Some(match self {
            Self::ClassExpression(_) => unreachable!("class expression conditions need preflight"),
            Self::Unchanged(_)
            | Self::ClassPropertyTruthiness(_)
            | Self::ClassPropertyEquality(_)
            | Self::ClassPropertyPredicate(_) => return None,
            Self::Nullish(condition) => return condition.symbol,
            Self::Truthiness(condition) => condition.symbol,
            Self::Typeof(condition) => condition.symbol,
            Self::Equality(condition) => condition.symbol,
            Self::In(condition) | Self::InstanceOf(condition) => condition.symbol,
        })
    }

    pub(super) const fn class_property_access(self) -> Option<NodeRef> {
        match self {
            Self::ClassPropertyTruthiness(condition) => Some(condition.access),
            Self::ClassPropertyEquality(condition) => Some(condition.access),
            Self::ClassPropertyPredicate(condition) => Some(condition.access),
            _ => None,
        }
    }
}

/// One local initialization, parameter write, or array mutation in binder flow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceFlowAssignment {
    /// The exact declaration, assignment target, or call carried by the flow node.
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

/// One retained assignment with its exact binder declaration and target.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceFlowParameterAssignment {
    pub(super) target: NodeRef,
    /// The declaration that owns the assigned symbol.
    pub(super) parameter: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

/// Source ownership for an annotated let captured by a stored arrow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceCapturedLocal {
    target: NodeRef,
    declaration: NodeRef,
    annotation: NodeRef,
    symbol: SemanticSymbolId,
    declaring_callable: NodeRef,
    writing_callable: NodeRef,
    revision: NodeArenaRevision,
}

impl SourceCapturedLocal {
    pub(super) const fn target(self) -> NodeRef {
        self.target
    }

    pub(super) const fn declaration(self) -> NodeRef {
        self.declaration
    }

    pub(super) const fn annotation(self) -> NodeRef {
        self.annotation
    }

    pub(super) const fn symbol(self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) const fn declaring_callable(self) -> NodeRef {
        self.declaring_callable
    }

    pub(super) const fn writing_callable(self) -> NodeRef {
        self.writing_callable
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceFlowCapturedAssignment {
    pub(super) statement: NodeRef,
    pub(super) expression: NodeRef,
    pub(super) local: SourceCapturedLocal,
}

/// A non-hoisted closure can keep flow narrowing only after the last write.
/// Writes in another callable prevent that proof, including earlier IIFEs.
pub(super) fn captured_variables_with_later_writes(
    host: &DeclaredTypeHost<'_>,
    location: NodeRef,
    assignments: &[SourceFlowParameterAssignment],
) -> Result<HashSet<SemanticSymbolId>, SourceFlowError> {
    let location_start = host
        .node(location)
        .ok_or(SourceFlowInvariant::ForeignNode(location))?
        .range
        .start
        .get();
    let mut captured = HashSet::new();
    for assignment in assignments {
        let target = assignment.target;
        let declaration = assignment.parameter;
        let invalid = || SourceFlowInvariant::InvalidParameterAssignment(target);
        let declaration_start = host
            .node(declaration)
            .ok_or_else(invalid)?
            .range
            .start
            .get();
        if capture_write_container(host, target)? != capture_write_container(host, declaration)? {
            captured.insert(assignment.symbol);
            continue;
        }
        let mut position = host.node(target).ok_or_else(invalid)?.range.start.get();
        let mut current = target;
        let mut visited = HashSet::new();
        loop {
            if !visited.insert(current) {
                return Err(invalid().into());
            }
            let record = host.node(current).ok_or_else(invalid)?;
            if record.range.start.get() <= declaration_start {
                break;
            }
            if matches!(
                record.kind,
                SyntaxKind::VariableStatement
                    | SyntaxKind::ExpressionStatement
                    | SyntaxKind::IfStatement
                    | SyntaxKind::DoStatement
                    | SyntaxKind::WhileStatement
                    | SyntaxKind::ForStatement
                    | SyntaxKind::ForInStatement
                    | SyntaxKind::ForOfStatement
                    | SyntaxKind::WithStatement
                    | SyntaxKind::SwitchStatement
                    | SyntaxKind::TryStatement
                    | SyntaxKind::ClassDeclaration
            ) {
                position = record.range.end.get();
            }
            let Some(parent) = record.parent else {
                break;
            };
            current = NodeRef::new(current.arena, current.file, parent);
        }
        if position >= location_start {
            captured.insert(assignment.symbol);
        }
    }
    Ok(captured)
}

fn capture_write_container(
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<NodeRef, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidParameterAssignment(node);
    let mut current = node;
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(current) {
            return Err(invalid().into());
        }
        let record = host.node(current).ok_or_else(invalid)?;
        if matches!(
            record.kind,
            SyntaxKind::SourceFile
                | SyntaxKind::FunctionDeclaration
                | SyntaxKind::FunctionExpression
                | SyntaxKind::ArrowFunction
                | SyntaxKind::MethodDeclaration
                | SyntaxKind::Constructor
                | SyntaxKind::GetAccessor
                | SyntaxKind::SetAccessor
        ) {
            return Ok(current);
        }
        let parent = record.parent.ok_or_else(invalid)?;
        current = NodeRef::new(current.arena, current.file, parent);
    }
}

/// Proves a visible enclosing let without demanding its staged value type.
#[allow(clippy::too_many_lines)] // Source ownership and lexical visibility form one proof.
pub(super) fn plan_source_captured_local(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    writing_callable: NodeRef,
    target: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<Option<SourceCapturedLocal>, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCapturedLocal(target);
    let (arena, bound) = host.source(target).ok_or_else(invalid)?;
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || !writing_callable.is_for(arena.id(), bound.file_id())
        || !bound.contains(writing_callable)
    {
        return Err(invalid().into());
    }
    let facts = bound.source_facts().ok_or_else(invalid)?;
    if facts.is_javascript_file() || facts.is_declaration_file() {
        return Ok(None);
    }
    let writer = host.node(writing_callable).ok_or_else(invalid)?;
    match &writer.data {
        NodeData::ArrowFunction(arrow)
            if arrow.modifiers.is_none() && arrow.asterisk_token.is_none() => {}
        NodeData::MethodDeclaration(method)
            if method.modifiers.is_none()
                && method.asterisk_token.is_none()
                && method.type_parameters.is_none()
                && method.postfix_token.is_none()
                && writer
                    .parent
                    .and_then(|parent| arena.get(parent))
                    .is_some_and(|parent| parent.kind == SyntaxKind::ObjectLiteralExpression) => {}
        _ => return Ok(None),
    }
    let owner = store.symbol(symbol).ok_or_else(invalid)?;
    if owner.flags() != SymbolFlags::BLOCK_SCOPED_VARIABLE {
        return Ok(None);
    }
    let declaration = owner.value_declaration().ok_or_else(invalid)?;
    if !declaration.is_for(arena.id(), bound.file_id()) {
        return Ok(None);
    }
    let declaration_record = host.node(declaration).ok_or_else(invalid)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Ok(None);
    };
    let Some(annotation) = variable.type_ else {
        return Ok(None);
    };
    let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let name_record = host.node(name).ok_or_else(invalid)?;
    let NodeData::Identifier(name_data) = &name_record.data else {
        return Ok(None);
    };
    let list = NodeRef::new(
        declaration.arena,
        declaration.file,
        declaration_record.parent.ok_or_else(invalid)?,
    );
    let list_record = host.node(list).ok_or_else(invalid)?;
    let NodeData::VariableDeclarationList(list_data) = &list_record.data else {
        return Err(invalid().into());
    };
    if list_record.flags.0 != 1 {
        return Ok(None);
    }
    let declaring_callable = capture_write_container(host, declaration)?;
    if declaring_callable == writing_callable
        || source_captured_callable_body(host, declaring_callable).is_none()
        || !source_node_is_descendant_of(arena, writing_callable, declaring_callable.node)
        || declaration_record.range.end > writer.range.start
    {
        return Ok(None);
    }
    if writer.kind == SyntaxKind::MethodDeclaration {
        validate_source_object_method_owner(arena, bound, store, host, writing_callable)
            .map_err(|_| invalid())?;
    } else {
        if !source_captured_arrow_is_stored(store, host, writing_callable)? {
            return Ok(None);
        }
        validate_source_arrow_owner(arena, bound, store, writing_callable)
            .map_err(|_| invalid())?;
    }
    validate_captured_declaring_owner(arena, bound, store, host, declaring_callable)
        .map_err(|_| invalid())?;
    let statement = NodeRef::new(
        list.arena,
        list.file,
        list_record.parent.ok_or_else(invalid)?,
    );
    let statement_record = host.node(statement).ok_or_else(invalid)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(invalid().into());
    };
    if statement_data.modifiers.is_some() {
        return Ok(None);
    }
    let annotation = NodeRef::new(declaration.arena, declaration.file, annotation);
    let annotation_record = host.node(annotation).ok_or_else(invalid)?;
    let target_record = host.node(target).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &target_record.data else {
        return Err(invalid().into());
    };
    let declaring_body =
        source_captured_callable_body(host, declaring_callable).ok_or_else(invalid)?;
    let block_scope = bound
        .block_scope_container(declaration)
        .ok_or_else(invalid)?;
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || variable.exclamation_token.is_some()
        || variable.symbol.is_some()
        || variable.local_symbol.is_some()
        || variable.facts != 0
        || list_record.kind != SyntaxKind::VariableDeclarationList
        || list_data.facts != 0
        || list_data
            .declarations
            .nodes
            .iter()
            .filter(|node| **node == declaration.node)
            .count()
            != 1
        || statement_record.kind != SyntaxKind::VariableStatement
        || statement_record.flags.0 != 0
        || statement_data.declaration_list != list.node
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || !source_node_is_descendant_of(arena, statement, declaring_body.node)
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || name_data.flow_node.is_some()
        || name_data.text.is_empty()
        || annotation_record.parent != Some(declaration.node)
        || target_record.kind != SyntaxKind::Identifier
        || target_record.flags.0 != 0
        || identifier.flow_node.is_some()
        || identifier.text != name_data.text
        || bound.container(declaration) != Some(declaring_callable)
        || bound.container(target) != Some(writing_callable)
        || bound.flow_container(target) != Some(writing_callable)
        || bound.symbol(declaration) != Some(symbol)
        || bound.local_symbol(declaration).is_some()
        || bound
            .locals(block_scope)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&name_data.text))
            != Some(symbol)
        || store
            .symbol_node_links(target)
            .is_some_and(|links| links.resolved_symbol.is_some_and(|actual| actual != symbol))
    {
        return Err(invalid().into());
    }
    let declared = super::variables::plan_top_level_variable(
        bound,
        store,
        declaration,
        name,
        &name_data.text,
        super::variables::VariableBindingKind::Let,
        false,
    )
    .map_err(|_| invalid())?;
    if declared != symbol {
        return Err(invalid().into());
    }
    let mut callback_host = host.name_resolver_host(store).map_err(|_| invalid())?;
    let mut resolver =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
            .map_err(|_| invalid())?;
    let found_symbol = resolver
        .resolve(
            Some(CanonicalResolutionLocation::Bound(target)),
            &identifier.text,
            SymbolFlags::VALUE,
            None,
            false,
            false,
        )
        .map_err(|_| invalid())?;
    if found_symbol != Some(symbol) {
        return Err(invalid().into());
    }
    Ok(Some(SourceCapturedLocal {
        target,
        declaration,
        annotation,
        symbol,
        declaring_callable,
        writing_callable,
        revision: arena.revision(),
    }))
}

pub(super) fn validate_source_captured_local(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    local: &SourceCapturedLocal,
) -> Result<(), SourceFlowError> {
    if plan_source_captured_local(
        store,
        host,
        local.writing_callable,
        local.target,
        local.symbol,
    )? != Some(*local)
    {
        return Err(SourceFlowInvariant::InvalidCapturedLocal(local.target).into());
    }
    Ok(())
}

fn source_captured_callable_body(
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
) -> Option<NodeRef> {
    let body = match &host.node(declaration)?.data {
        NodeData::FunctionDeclaration(data) => data.body?,
        NodeData::ArrowFunction(data) => data.body,
        _ => return None,
    };
    let body = NodeRef::new(declaration.arena, declaration.file, body);
    host.node(body)
        .filter(|record| {
            record.kind == SyntaxKind::Block && record.parent == Some(declaration.node)
        })
        .map(|_| body)
}

fn source_captured_arrow_is_stored(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    arrow: NodeRef,
) -> Result<bool, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCapturedLocal(arrow);
    let mut current = arrow;
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(current) {
            return Err(invalid().into());
        }
        let record = host.node(current).ok_or_else(invalid)?;
        let parent = NodeRef::new(
            current.arena,
            current.file,
            record.parent.ok_or_else(invalid)?,
        );
        let parent_record = host.node(parent).ok_or_else(invalid)?;
        match &parent_record.data {
            NodeData::ParenthesizedExpression(expression) => {
                if parent_record.kind != SyntaxKind::ParenthesizedExpression
                    || parent_record.flags.0 != 0
                    || expression.expression != current.node
                    || record.range.start < parent_record.range.start
                    || record.range.end > parent_record.range.end
                {
                    return Err(invalid().into());
                }
                current = parent;
            }
            NodeData::VariableDeclaration(variable) => {
                let bound = host.bound_file(parent).ok_or_else(invalid)?;
                let variable_symbol = bound.symbol(parent).ok_or_else(invalid)?;
                let symbol = store.symbol(variable_symbol).ok_or_else(invalid)?;
                if parent_record.kind != SyntaxKind::VariableDeclaration
                    || variable.initializer != Some(current.node)
                    || symbol.value_declaration() != Some(parent)
                    || symbol.declarations() != Some(&[parent])
                    || variable_symbol == bound.symbol(arrow).ok_or_else(invalid)?
                {
                    return Err(invalid().into());
                }
                return Ok(true);
            }
            NodeData::PropertyAssignment(_) if current == arrow => {
                return super::source_callables::source_object_property_arrow_symbol(
                    store, host, arrow,
                )
                .map(|symbol| symbol.is_some())
                .map_err(|_| invalid().into());
            }
            NodeData::NewExpression(_) if current == arrow => {
                return super::source_callables::source_promise_constructor_argument_arrow_is_exact(
                    store, host, arrow,
                )
                .map_err(|_| invalid().into());
            }
            _ => return Ok(false),
        }
    }
}

fn validate_captured_declaring_owner(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCapturedLocal(declaration);
    let record = host.node(declaration).ok_or_else(invalid)?;
    match &record.data {
        NodeData::ArrowFunction(_) => {
            validate_source_arrow_owner(arena, bound, store, declaration)?;
        }
        NodeData::FunctionDeclaration(function) => {
            let owner_symbol = bound
                .symbol(declaration)
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .ok_or_else(invalid)?;
            let owner = store.symbol(owner_symbol).ok_or_else(invalid)?;
            let name = NodeRef::new(
                declaration.arena,
                declaration.file,
                function.name.ok_or_else(invalid)?,
            );
            let name_record = host.node(name).ok_or_else(invalid)?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return Err(invalid().into());
            };
            if record.kind != SyntaxKind::FunctionDeclaration
                || function.full_signature.is_some()
                || function.next_container.is_some()
                || function.symbol.is_some()
                || function.local_symbol.is_some()
                || function.flow_node.is_some()
                || function.end_flow_node.is_some()
                || function.return_flow_node.is_some()
                || function.facts != 0
                || name_record.kind != SyntaxKind::Identifier
                || name_record.flags.0 != 0
                || name_record.parent != Some(declaration.node)
                || identifier.flow_node.is_some()
                || identifier.text.is_empty()
                || !store.source_declaration_belongs_to_symbol(declaration, owner_symbol)
                || !store.source_merged_symbol_declarations_match(owner_symbol)
                || !super::source_callables::valid_source_function_owner_shape(
                    store,
                    owner_symbol,
                    declaration,
                )
                || owner.check_flags() != CheckFlags::NONE
                || owner.members().is_some()
                || owner.export_symbol().is_some()
            {
                return Err(invalid().into());
            }
            let local = bound.local_symbol(declaration);
            if store.source_default_function_name(declaration).is_some() {
                if !local.is_some_and(|local| {
                    super::source_callables::named_default_function_export_is_exact(
                        store,
                        declaration,
                        owner_symbol,
                        local,
                    )
                }) {
                    return Err(invalid().into());
                }
            } else if owner.name().as_bytes() != identifier.text.as_bytes() {
                return Err(invalid().into());
            }
            match (owner.parent(), local) {
                (None, None) => {}
                (Some(parent), Some(local)) => {
                    let local_record = store.symbol(local).ok_or_else(invalid)?;
                    let source_parent = NodeRef::new(
                        declaration.arena,
                        declaration.file,
                        record.parent.ok_or_else(invalid)?,
                    );
                    let parent_node = match host.node(source_parent).ok_or_else(invalid)?.kind {
                        SyntaxKind::SourceFile => source_parent,
                        SyntaxKind::ModuleBlock => NodeRef::new(
                            declaration.arena,
                            declaration.file,
                            host.node(source_parent)
                                .ok_or_else(invalid)?
                                .parent
                                .ok_or_else(invalid)?,
                        ),
                        _ => return Err(invalid().into()),
                    };
                    if !matches!(
                        host.node(parent_node).ok_or_else(invalid)?.kind,
                        SyntaxKind::SourceFile | SyntaxKind::ModuleDeclaration
                    ) || bound
                        .symbol(parent_node)
                        .and_then(|symbol| store.get_merged_symbol(symbol))
                        != Some(parent)
                        || store.get_merged_symbol(parent) != Some(parent)
                        || store.get_merged_symbol(local) != Some(local)
                        || !store.source_declaration_belongs_to_symbol(parent_node, parent)
                        || !store.source_symbol_declarations_match(local)
                        || local_record.flags() != SymbolFlags::EXPORT_VALUE
                        || local_record.check_flags() != CheckFlags::NONE
                        || local_record.name().as_bytes() != identifier.text.as_bytes()
                        || local_record.declarations() != Some(&[declaration])
                        || local_record.value_declaration().is_some()
                        || local_record.members().is_some()
                        || local_record.exports().is_some()
                        || local_record.parent().is_some()
                        || local_record.export_symbol() != Some(owner_symbol)
                        || store
                            .symbol(parent)
                            .and_then(ts_binder::semantic::Symbol::exports)
                            .and_then(|exports| store.symbol_table(exports))
                            .and_then(|exports| exports.get(owner.name()))
                            != Some(owner_symbol)
                    {
                        return Err(invalid().into());
                    }
                }
                _ => return Err(invalid().into()),
            }
        }
        _ => return Err(invalid().into()),
    }
    Ok(())
}

fn validate_source_arrow_owner(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    container: NodeRef,
) -> Result<NodeRef, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCall(container);
    if !container.is_for(arena.id(), bound.file_id())
        || !bound.contains(container)
        || bound.node_arena_revision() != arena.revision()
        || bound
            .source_facts()
            .is_none_or(|facts| facts.is_javascript_file() || facts.is_declaration_file())
    {
        return Err(invalid().into());
    }
    let record = arena.get(container.node).ok_or_else(invalid)?;
    let NodeData::ArrowFunction(arrow) = &record.data else {
        return Err(invalid().into());
    };
    let body = NodeRef::new(container.arena, container.file, arrow.body);
    let body_record = arena.get(body.node).ok_or_else(invalid)?;
    let NodeData::Block(block) = &body_record.data else {
        return Err(invalid().into());
    };
    let token = arena
        .get(arrow.equals_greater_than_token)
        .ok_or_else(invalid)?;
    let owner_symbol = bound.symbol(container).ok_or_else(invalid)?;
    let owner = store.symbol(owner_symbol).ok_or_else(invalid)?;
    if record.kind != SyntaxKind::ArrowFunction
        || record.flags.0 != 0
        || arrow.asterisk_token.is_some()
        || arrow.modifiers.is_some()
        || arrow.full_signature.is_some()
        || arrow.next_container.is_some()
        || arrow.symbol.is_some()
        || arrow.flow_node.is_some()
        || arrow.end_flow_node.is_some()
        || arrow.facts != 0
        || body_record.kind != SyntaxKind::Block
        || body_record.flags.0 != 0
        || body_record.parent != Some(container.node)
        || body_record.range.start < record.range.start
        || body_record.range.end > record.range.end
        || block.flow_node.is_some()
        || block.next_container.is_some()
        || block.facts != 0
        || token.kind != SyntaxKind::EqualsGreaterThanToken
        || token.flags.0 != 0
        || token.parent != Some(container.node)
        || !matches!(token.data, NodeData::Token(_))
        || owner.flags() != SymbolFlags::FUNCTION
        || owner.check_flags() != CheckFlags::NONE
        || owner.name() != InternalSymbolName::Function.as_ref()
        || owner.declarations() != Some(&[container])
        || owner.value_declaration() != Some(container)
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || bound.local_symbol(container).is_some()
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
    {
        return Err(invalid().into());
    }
    let start = bound
        .flow_graph()
        .container_start(container)
        .ok_or_else(invalid)?;
    if preflight_start_payload(bound.flow_graph(), container, start)? != Some(container) {
        return Err(invalid().into());
    }
    Ok(body)
}

/// Proves the source owner without requiring a caller's statement-list plan.
fn validate_source_function_expression_owner(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    container: NodeRef,
) -> Result<NodeRef, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidParameterAssignment(container);
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || !container.is_for(arena.id(), bound.file_id())
        || !bound.contains(container)
        || bound
            .source_facts()
            .is_none_or(|facts| facts.is_javascript_file() || facts.is_declaration_file())
    {
        return Err(invalid().into());
    }
    let record = arena.get(container.node).ok_or_else(invalid)?;
    let NodeData::FunctionExpression(function) = &record.data else {
        return Err(invalid().into());
    };
    let body = NodeRef::new(container.arena, container.file, function.body);
    let body_record = arena.get(body.node).ok_or_else(invalid)?;
    let NodeData::Block(block) = &body_record.data else {
        return Err(invalid().into());
    };
    let owner_symbol = bound.symbol(container).ok_or_else(invalid)?;
    let owner = store.symbol(owner_symbol).ok_or_else(invalid)?;
    if record.kind != SyntaxKind::FunctionExpression
        || store.source_node_kind(container) != Some(SyntaxKind::FunctionExpression)
        || record.flags.0 != 0
        || function.asterisk_token.is_some()
        || function.modifiers.is_some()
        || function.full_signature.is_some()
        || function.next_container.is_some()
        || function.symbol.is_some()
        || function.flow_node.is_some()
        || function.end_flow_node.is_some()
        || function.return_flow_node.is_some()
        || function.facts != 0
        || body_record.kind != SyntaxKind::Block
        || body_record.flags.0 != 0
        || body_record.parent != Some(container.node)
        || body_record.range.start < record.range.start
        || body_record.range.end > record.range.end
        || !bound.contains(body)
        || store.source_node_parent(body) != Some(super::store::SourceNodeParent::Parent(container))
        || block.flow_node.is_some()
        || block.next_container.is_some()
        || block.facts != 0
        || owner.flags() != SymbolFlags::FUNCTION
        || owner.check_flags() != CheckFlags::NONE
        || owner.declarations() != Some(&[container])
        || owner.value_declaration() != Some(container)
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || bound.local_symbol(container).is_some()
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
    {
        return Err(invalid().into());
    }
    if let Some(name) = function.name {
        let name = NodeRef::new(container.arena, container.file, name);
        let name_record = arena.get(name.node).ok_or_else(invalid)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(invalid().into());
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(container.node)
            || name_record.range.start < record.range.start
            || name_record.range.end > record.range.end
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
            || !bound.contains(name)
            || store.source_child_with_kind(container, SyntaxKind::Identifier) != Some(name)
            || store.source_identifier_text(name) != Some(identifier.text.as_str())
            || owner.name().as_bytes() != identifier.text.as_bytes()
        {
            return Err(invalid().into());
        }
    } else if owner.name() != InternalSymbolName::Function.as_ref()
        || store
            .source_child_with_kind(container, SyntaxKind::Identifier)
            .is_some()
    {
        return Err(invalid().into());
    }
    let start = bound
        .flow_graph()
        .container_start(container)
        .ok_or_else(invalid)?;
    if preflight_start_payload(bound.flow_graph(), container, start)? != Some(container) {
        return Err(invalid().into());
    }
    Ok(body)
}

/// Reuses the object's member proof and retains the method's actual body and flow start.
fn validate_source_object_method_owner(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    container: NodeRef,
) -> Result<NodeRef, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCall(container);
    let owner =
        super::source_callables::source_object_literal_method_symbol(store, host, container)
            .ok_or_else(invalid)?;
    let record = host.node(container).ok_or_else(invalid)?;
    let NodeData::MethodDeclaration(method) = &record.data else {
        return Err(invalid().into());
    };
    let body = NodeRef::new(
        container.arena,
        container.file,
        method.body.ok_or_else(invalid)?,
    );
    let body_record = host.node(body).ok_or_else(invalid)?;
    let NodeData::Block(block) = &body_record.data else {
        return Err(invalid().into());
    };
    if !container.is_for(arena.id(), bound.file_id())
        || !bound.contains(container)
        || bound.node_arena_revision() != arena.revision()
        || bound
            .source_facts()
            .is_none_or(|facts| facts.is_javascript_file() || facts.is_declaration_file())
        || bound.symbol(container) != Some(owner)
        || bound.local_symbol(container).is_some()
        || record.flags.0 != 0
        || method.modifiers.is_some()
        || method.asterisk_token.is_some()
        || method.type_parameters.is_some()
        || method.postfix_token.is_some()
        || body_record.kind != SyntaxKind::Block
        || body_record.flags.0 != 0
        || body_record.parent != Some(container.node)
        || body_record.range.start < record.range.start
        || body_record.range.end > record.range.end
        || block.flow_node.is_some()
        || block.next_container.is_some()
        || block.facts != 0
    {
        return Err(invalid().into());
    }
    let start = bound
        .flow_graph()
        .container_start(container)
        .ok_or_else(invalid)?;
    if preflight_start_payload(bound.flow_graph(), container, start)? != Some(container) {
        return Err(invalid().into());
    }
    Ok(body)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceFlowArrayMutation {
    pub(super) call: NodeRef,
    pub(super) receiver: NodeRef,
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceFlowCapturedArrayMutation {
    pub(super) mutation: SourceFlowArrayMutation,
    pub(super) local: SourceCapturedLocal,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceCapturedFlowOrigin {
    Assignment(SourceFlowCapturedAssignment),
    ArrayMutation(SourceFlowCapturedArrayMutation),
}

impl SourceCapturedFlowOrigin {
    const fn local(self) -> SourceCapturedLocal {
        match self {
            Self::Assignment(assignment) => assignment.local,
            Self::ArrayMutation(mutation) => mutation.local,
        }
    }

    const fn assignment(self) -> SourceFlowAssignment {
        SourceFlowAssignment {
            declaration: match self {
                Self::Assignment(assignment) => assignment.local.target,
                Self::ArrayMutation(mutation) => mutation.mutation.call,
            },
            symbol: self.local().symbol,
        }
    }
}

fn validate_retained_captured_origin(
    bound: &BoundFile,
    container: NodeRef,
    assignment: SourceFlowAssignment,
    origin: SourceCapturedFlowOrigin,
    statement_list: Option<&SourceCallableStatementListSyntax>,
) -> Result<(), SourceFlowError> {
    let local = origin.local();
    let invalid = || SourceFlowInvariant::InvalidCapturedLocal(local.target);
    let scope = match statement_list {
        Some(syntax) => match origin {
            SourceCapturedFlowOrigin::Assignment(assignment) => {
                syntax.statement_scope(assignment.statement)
            }
            SourceCapturedFlowOrigin::ArrayMutation(mutation) => {
                syntax.expression_scope(mutation.mutation.call)
            }
        }
        .ok_or_else(invalid)?,
        None => container,
    };
    if assignment != origin.assignment()
        || local.writing_callable != container
        || local.declaring_callable == container
        || local.revision != bound.node_arena_revision()
        || [
            local.target,
            local.declaration,
            local.annotation,
            local.declaring_callable,
            container,
            assignment.declaration,
        ]
        .into_iter()
        .any(|node| !bound.contains(node))
        || bound.symbol(local.declaration) != Some(local.symbol)
        || bound.container(local.declaration) != Some(local.declaring_callable)
        || bound.container(local.annotation) != Some(local.declaring_callable)
        || bound.container(local.target) != Some(container)
        || bound.flow_container(local.target) != Some(container)
        || bound.container(assignment.declaration) != Some(container)
        || bound.block_scope_container(assignment.declaration) != Some(scope)
    {
        return Err(invalid().into());
    }
    let mut current = bound.container(container);
    let mut visited = HashSet::new();
    while let Some(parent) = current {
        if !visited.insert(parent) {
            return Err(invalid().into());
        }
        if parent == local.declaring_callable {
            return Ok(());
        }
        current = bound.container(parent);
    }
    Err(invalid().into())
}

fn validate_captured_flow_origin(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    container: NodeRef,
    origin: SourceCapturedFlowOrigin,
    statement_list: Option<&SourceCallableStatementListSyntax>,
) -> Result<(), SourceFlowError> {
    validate_source_captured_local(store, host, &origin.local())?;
    validate_retained_captured_origin(
        bound,
        container,
        origin.assignment(),
        origin,
        statement_list,
    )?;
    match origin {
        SourceCapturedFlowOrigin::Assignment(assignment) => {
            let invalid = || SourceFlowInvariant::InvalidCapturedLocal(assignment.local.target);
            match statement_list {
                Some(syntax) => validate_statement_list_expression(
                    arena,
                    bound,
                    syntax,
                    assignment.statement,
                    assignment.expression,
                )?,
                None => {
                    if arena
                        .get(container.node)
                        .is_some_and(|record| record.kind == SyntaxKind::MethodDeclaration)
                    {
                        let body = validate_source_object_method_owner(
                            arena, bound, store, host, container,
                        )?;
                        validate_callable_expression_statement(
                            arena,
                            bound,
                            container,
                            body,
                            assignment.statement,
                        )?;
                    } else {
                        validate_arrow_statement(
                            arena,
                            bound,
                            store,
                            container,
                            assignment.statement,
                        )?;
                    }
                }
            }
            let target = arena
                .get(assignment.local.target.node)
                .ok_or_else(invalid)?;
            let expression = arena.get(assignment.expression.node).ok_or_else(invalid)?;
            let NodeData::BinaryExpression(binary) = &expression.data else {
                return Err(invalid().into());
            };
            let operator = arena.get(binary.operator_token).ok_or_else(invalid)?;
            let right = arena.get(binary.right).ok_or_else(invalid)?;
            let statement = arena.get(assignment.statement.node).ok_or_else(invalid)?;
            let NodeData::ExpressionStatement(statement_data) = &statement.data else {
                return Err(invalid().into());
            };
            if !assignment.expression.is_for(arena.id(), bound.file_id())
                || !bound.contains(assignment.expression)
                || bound.container(assignment.expression) != Some(container)
                || expression.kind != SyntaxKind::BinaryExpression
                || expression.flags.0 != 0
                || expression.parent != Some(assignment.statement.node)
                || statement_data.expression != assignment.expression.node
                || target.parent != Some(assignment.expression.node)
                || binary.left != assignment.local.target.node
                || binary.symbol.is_some()
                || binary.type_.is_some()
                || binary.modifiers.is_some()
                || binary.facts != 0
                || operator.kind != SyntaxKind::EqualsToken
                || operator.flags.0 != 0
                || operator.parent != Some(assignment.expression.node)
                || !matches!(operator.data, NodeData::Token(_))
                || right.parent != Some(assignment.expression.node)
                || target.range.end > operator.range.start
                || operator.range.end > right.range.start
                || right.range.end > expression.range.end
            {
                return Err(invalid().into());
            }
        }
        SourceCapturedFlowOrigin::ArrayMutation(captured) => {
            let mutation = captured.mutation;
            let invalid = || SourceFlowInvariant::InvalidArrayMutation(mutation.call);
            if arena
                .get(container.node)
                .is_none_or(|record| record.kind != SyntaxKind::ArrowFunction)
            {
                return Err(invalid().into());
            }
            match statement_list {
                Some(syntax) => validate_statement_list_call(arena, bound, syntax, mutation.call)?,
                None => validate_linear_direct_call(arena, bound, store, container, mutation.call)?,
            };
            if mutation.receiver != captured.local.target
                || mutation.declaration != captured.local.declaration
                || mutation.symbol != captured.local.symbol
            {
                return Err(invalid().into());
            }
            let call_record = arena.get(mutation.call.node).ok_or_else(invalid)?;
            let NodeData::CallExpression(call) = &call_record.data else {
                return Err(invalid().into());
            };
            let property = arena.get(call.expression).ok_or_else(invalid)?;
            let NodeData::PropertyAccessExpression(access) = &property.data else {
                return Err(invalid().into());
            };
            let name = arena.get(access.name).ok_or_else(invalid)?;
            let receiver = arena.get(mutation.receiver.node).ok_or_else(invalid)?;
            if property.kind != SyntaxKind::PropertyAccessExpression
                || property.flags.0 != 0
                || access.expression != mutation.receiver.node
                || access.question_dot_token.is_some()
                || access.flow_node.is_some()
                || access.facts != 0
                || name.parent != Some(call.expression)
                || name.flags.0 != 0
                || !matches!(&name.data, NodeData::Identifier(name) if matches!(name.text.as_str(), "push" | "unshift"))
                || receiver.kind != SyntaxKind::Identifier
                || receiver.flags.0 != 0
                || receiver.parent != Some(call.expression)
            {
                return Err(invalid().into());
            }
        }
    }
    Ok(())
}

fn validate_captured_origin_flow_node(
    origin: SourceCapturedFlowOrigin,
    flow: FlowRef,
    node: &FlowNode,
) -> Result<(), SourceFlowError> {
    let expected_kind = match origin {
        SourceCapturedFlowOrigin::Assignment(_) => SourceFlowKind::Assignment,
        SourceCapturedFlowOrigin::ArrayMutation(_) => SourceFlowKind::ArrayMutation,
    };
    if source_flow_kind(flow, node.flags)? != expected_kind
        || ast_payload(flow, node)? != origin.assignment().declaration
    {
        return Err(SourceFlowInvariant::InvalidPayload(flow).into());
    }
    linear_antecedent(flow, node)?;
    Ok(())
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
    class_expression_conditions: HashMap<NodeRef, SourceClassExpressionConditionProof>,
    assignments: HashMap<NodeRef, SourceFlowAssignment>,
    assignment_order: Vec<NodeRef>,
    assignment_declarations: HashMap<NodeRef, NodeRef>,
    captured_origins: HashMap<NodeRef, SourceCapturedFlowOrigin>,
    statement_list: Option<SourceCallableStatementListSyntax>,
    calls: HashMap<NodeRef, NodeRef>,
    logical_statements: Vec<SourceLogicalStatementFlow>,
    class_body: Option<ClassBodyPlan>,
    property_assignments: HashMap<NodeRef, ClassPropertyFlowAssignment>,
    region: Option<SourceFlowRegion>,
    updates: HashMap<NodeRef, SourceFlowUpdate>,
    nullish_assignments: HashMap<NodeRef, SourceNullishAssignmentProof>,
    member_assignments: HashMap<NodeRef, SourceMemberAssignmentProof>,
    nullish_calls: HashMap<NodeRef, FlowRef>,
}

/// The detached logical join proves both condition edges, but is not an exit.
#[derive(Clone, Debug)]
struct SourceLogicalStatementFlow {
    syntax: SourceLinearLogicalStatementSyntax,
    revision: NodeArenaRevision,
    block_scope: NodeRef,
    entry: FlowRef,
    rows: SourceLogicalStatementRows,
    source_points: Vec<(NodeRef, Option<FlowRef>)>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceLogicalStatementRows {
    left_true: FlowRef,
    left_false: FlowRef,
    right_true: FlowRef,
    right_false: FlowRef,
    pre_right: FlowRef,
    join: FlowRef,
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

/// Initialization queries cannot allocate types or borrow a new caller.
enum ClassPropertyFlowTypes<'a> {
    Initialization(&'a CanonicalTypeMapperStore),
    Read {
        store: &'a mut CanonicalTypeMapperStore,
        globals: Option<&'a CanonicalGlobalTypes>,
        session: Option<&'a mut InstantiationSession>,
    },
}

impl ClassPropertyFlowTypes<'_> {
    fn store(&self) -> &CanonicalTypeMapperStore {
        match self {
            Self::Initialization(store) => store,
            Self::Read { store, .. } => store,
        }
    }

    fn narrow(
        &mut self,
        flow: FlowRef,
        flags: FlowFlags,
        condition: NodeRef,
        type_: TypeId,
        assumption: TruthinessAssumption,
    ) -> Result<TypeId, SourceFlowError> {
        let Self::Read {
            store,
            globals: Some(globals),
            session: Some(session),
        } = self
        else {
            return Err(SourceFlowUnsupported::FlowKind { flow, flags }.into());
        };
        narrow_by_truthiness_with_session(store, globals, type_, assumption, session)
            .map_err(|error| SourceFlowError::Narrowing { condition, error })
    }

    fn narrow_equality(
        &mut self,
        flow: FlowRef,
        flags: FlowFlags,
        type_: TypeId,
        value: TypeId,
        require_match: bool,
    ) -> Result<TypeId, SourceFlowError> {
        let Self::Read {
            store,
            globals: Some(globals),
            session: Some(session),
        } = self
        else {
            return Err(SourceFlowUnsupported::FlowKind { flow, flags }.into());
        };
        narrow_by_equality_worker(
            store,
            globals,
            type_,
            value,
            true,
            require_match,
            None,
            Some(session),
        )
        .map_err(|error| match error {
            SourceEqualityNarrowingError::Union(error) => SourceFlowError::Join { flow, error },
            error => SourceFlowInvariant::EqualityNarrowing(error).into(),
        })
    }

    fn narrow_predicate(
        &mut self,
        flow: FlowRef,
        flags: FlowFlags,
        condition: NodeRef,
        current: TypeId,
        predicate: TypeId,
        assume_true: bool,
    ) -> Result<TypeId, SourceFlowError> {
        let Self::Read {
            store,
            globals: Some(globals),
            session: Some(session),
        } = self
        else {
            return Err(SourceFlowUnsupported::FlowKind { flow, flags }.into());
        };
        narrow_class_property_predicate_type(
            store, globals, session, flow, condition, current, predicate, assume_true,
        )
    }

    fn join(
        &mut self,
        flow: FlowRef,
        flags: FlowFlags,
        types: &[TypeId],
        declared: TypeId,
    ) -> Result<TypeId, SourceFlowError> {
        let Self::Read {
            store,
            globals: Some(globals),
            session: Some(session),
        } = self
        else {
            return Err(SourceFlowUnsupported::FlowKind { flow, flags }.into());
        };
        store
            .validate_union_constituent_with_global_types(globals, declared)
            .map_err(|error| SourceFlowError::Join { flow, error })?;
        let joined = store
            .expression_union_type_with_global_types_and_session(
                globals,
                types,
                UnionReduction::Literal,
                session,
            )
            .map_err(|error| SourceFlowError::Join { flow, error })?;
        Ok(SourceFlowFrame::preferred_join_identity(
            store,
            joined,
            &[declared],
        ))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFlowUnsupported {
    IncompleteContainer(NodeRef),
    FlowKind { flow: FlowRef, flags: FlowFlags },
    Call(NodeRef),
    PropertyWrite(NodeRef),
    InNarrowing { condition: NodeRef, type_: TypeId },
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
    InvalidCapturedLocal(NodeRef),
    InvalidArrayMutation(NodeRef),
    InvalidCall(NodeRef),
    InvalidSourceRegion(NodeRef),
    InvalidUpdate(NodeRef),
    InvalidCallEffect(NodeRef),
    InvalidLogicalStatement(NodeRef),
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
    Array(ArrayTypeError),
    Relation(RelationUnavailable),
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

impl From<ArrayTypeError> for SourceFlowError {
    fn from(error: ArrayTypeError) -> Self {
        Self::Array(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceFlowKind {
    Unreachable,
    Start,
    Assignment,
    ArrayMutation,
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
    Update,
    ReadonlyUpdate,
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
struct SourceFlowActivePath {
    members: HashSet<FlowRef>,
    nodes: Vec<FlowRef>,
}

impl SourceFlowActivePath {
    fn validate_cycle(
        &self,
        nodes: &ts_ast::FlowNodeArena,
        flow: FlowRef,
    ) -> Result<(), SourceFlowError> {
        let Some(start) = self.nodes.iter().position(|active| *active == flow) else {
            return Err(SourceFlowInvariant::Cycle(flow).into());
        };
        // A backedge can return to a call or update inside a valid loop.
        // Only a loop label in this closed segment can justify the repeat.
        for active in &self.nodes[start..] {
            if !active.is_for(nodes.node_arena(), nodes.file()) {
                return Err(SourceFlowInvariant::ForeignFlow(*active).into());
            }
            let node = nodes
                .get(*active)
                .ok_or(SourceFlowInvariant::MissingFlowNode(*active))?;
            if source_flow_kind(*active, node.flags)? == SourceFlowKind::LoopLabel {
                label_antecedents(*active, node)?;
                return Ok(());
            }
        }
        Err(SourceFlowInvariant::Cycle(flow).into())
    }
}

#[derive(Default)]
struct SourceFlowEffects {
    class_expression_conditions: HashMap<NodeRef, SourceClassExpressionConditionProof>,
    assignment_declarations: HashMap<NodeRef, NodeRef>,
    captured_origins: HashMap<NodeRef, SourceCapturedFlowOrigin>,
    statement_list: Option<SourceCallableStatementListSyntax>,
    calls: HashMap<NodeRef, NodeRef>,
    logical_statements: Vec<SourceLogicalStatementFlow>,
    class_body: Option<ClassBodyPlan>,
    start_container: Option<NodeRef>,
    property_assignments: HashMap<NodeRef, ClassPropertyFlowAssignment>,
    region: Option<SourceFlowRegion>,
    updates: HashMap<NodeRef, SourceFlowUpdate>,
    nullish_assignments: HashMap<NodeRef, SourceNullishAssignmentProof>,
    member_assignments: HashMap<NodeRef, SourceMemberAssignmentProof>,
    nullish_calls: HashMap<NodeRef, FlowRef>,
    region_points: HashMap<NodeRef, FlowRef>,
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
    pub(super) fn statement_list_is_exact(
        &self,
        syntax: &SourceCallableStatementListSyntax,
    ) -> bool {
        self.container == syntax.callable.declaration
            && self.statement_list.as_ref() == Some(syntax)
    }

    /// Retains the same flow with an authenticated callable annotation context.
    pub(super) fn with_function_expression_statement_list_context(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        syntax: &SourceCallableStatementListSyntax,
        callable: &super::source_callables::SourceCallablePlan,
    ) -> Result<(SourceCallableStatementListSyntax, Self), SourceFlowError> {
        let declaration = syntax.callable.declaration;
        let invalid = || SourceFlowInvariant::InvalidCall(declaration);
        let (arena, _) = host.source(declaration).ok_or_else(invalid)?;
        let bound = host.bound_file(declaration).ok_or_else(invalid)?;
        if !self.statement_list_is_exact(syntax)
            || callable.declaration != declaration
            || bound.symbol(declaration) != Some(callable.owner_symbol)
            || arena.get(declaration.node).is_none_or(|record| {
                !matches!(
                    (&record.data, record.kind),
                    (NodeData::FunctionExpression(function), SyntaxKind::FunctionExpression)
                        if function.body == callable.body.node
                ) && !matches!(
                    (&record.data, record.kind),
                    (NodeData::ArrowFunction(function), SyntaxKind::ArrowFunction)
                        if function.body == callable.body.node
                )
            })
        {
            return Err(invalid().into());
        }
        let target = callable
            .contextual_function_expression_target()
            .ok_or_else(invalid)?;
        let mut contextual_callable = syntax.callable.clone();
        if !super::source_callables::apply_function_expression_context(
            store,
            host,
            &mut contextual_callable,
            target,
        )
        .map_err(|_| invalid())?
            || contextual_callable != *callable
        {
            return Err(invalid().into());
        }
        let mut syntax = syntax.clone();
        syntax.callable = contextual_callable;
        validate_statement_list_source(arena, bound, store, host, &syntax)?;
        let mut flow = self.clone();
        flow.statement_list = Some(syntax.clone());
        Ok((syntax, flow))
    }

    /// Adds exact statement scopes to the existing callable flow worker.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_statement_list(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        syntax: &SourceCallableStatementListSyntax,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceFlowCondition>,
        logical_conditions: Vec<SourceTruthinessCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        parameter_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
        captures: impl IntoIterator<Item = SourceFlowCapturedAssignment>,
        array_mutations: impl IntoIterator<Item = SourceFlowArrayMutation>,
    ) -> Result<Self, SourceFlowError> {
        Self::preflight_statement_list_with_nullish_assignments(
            arena,
            bound,
            store,
            host,
            syntax,
            points,
            conditions,
            logical_conditions,
            assignments,
            parameter_assignments,
            calls,
            captures,
            array_mutations,
            [],
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_statement_list_with_nullish_assignments(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        syntax: &SourceCallableStatementListSyntax,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceFlowCondition>,
        logical_conditions: Vec<SourceTruthinessCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        parameter_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
        captures: impl IntoIterator<Item = SourceFlowCapturedAssignment>,
        array_mutations: impl IntoIterator<Item = SourceFlowArrayMutation>,
        nullish_assignments: impl IntoIterator<Item = SourceFlowNullishAssignment>,
    ) -> Result<Self, SourceFlowError> {
        Self::preflight_statement_list_with_updates(
            arena,
            bound,
            store,
            host,
            syntax,
            points,
            conditions,
            logical_conditions,
            assignments,
            parameter_assignments,
            calls,
            captures,
            std::iter::empty(),
            array_mutations,
            nullish_assignments,
            std::iter::empty(),
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_statement_list_with_updates(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        syntax: &SourceCallableStatementListSyntax,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceFlowCondition>,
        logical_conditions: Vec<SourceTruthinessCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        parameter_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
        captures: impl IntoIterator<Item = SourceFlowCapturedAssignment>,
        captured_array_mutations: impl IntoIterator<Item = SourceFlowCapturedArrayMutation>,
        array_mutations: impl IntoIterator<Item = SourceFlowArrayMutation>,
        nullish_assignments: impl IntoIterator<Item = SourceFlowNullishAssignment>,
        updates: impl IntoIterator<Item = SourceFlowUpdate>,
    ) -> Result<Self, SourceFlowError> {
        validate_statement_list_source(arena, bound, store, host, syntax)?;
        let nullish_assignments = nullish_assignments.into_iter().collect::<Vec<_>>();
        let container = syntax.callable.declaration;
        let points = points.into_iter().collect::<Vec<_>>();
        let mut conditions = conditions.into_iter().collect::<Vec<_>>();
        conditions.extend(retained_linear_truthiness_conditions(
            arena,
            bound,
            container,
            &points,
            logical_conditions,
        )?);
        let mut assignments = assignments.into_iter().collect::<Vec<_>>();
        let mut effects = SourceFlowEffects {
            statement_list: Some(syntax.clone()),
            ..SourceFlowEffects::default()
        };
        for expression in syntax.expression_statements() {
            if let Some(proof) = source_member_assignment_proof(store, host, expression)? {
                if proof.container != container
                    || syntax.expression_scope(expression)
                        != bound.block_scope_container(expression)
                    || effects
                        .member_assignments
                        .insert(proof.target, proof)
                        .is_some()
                {
                    return Err(SourceFlowInvariant::InvalidParameterAssignment(expression).into());
                }
            }
        }
        for update in updates {
            validate_callable_update(arena, bound, store, host, syntax, update)?;
            if effects.updates.insert(update.target, update).is_some()
                || effects
                    .assignment_declarations
                    .insert(update.target, update.declaration)
                    .is_some()
            {
                return Err(SourceFlowInvariant::DuplicateAssignment(update.target).into());
            }
            assignments.push(SourceFlowAssignment {
                declaration: update.target,
                symbol: update.symbol,
            });
        }
        if syntax
            .counted_for_loops()
            .iter()
            .any(|iteration| !effects.updates.contains_key(&iteration.update_target))
        {
            return Err(SourceFlowInvariant::InvalidUpdate(syntax.callable.declaration).into());
        }
        for assignment in parameter_assignments {
            validate_parameter_assignment_in_list(
                arena,
                bound,
                store,
                Some(host),
                container,
                assignment,
                Some(syntax),
            )?;
            if effects
                .assignment_declarations
                .insert(assignment.target, assignment.parameter)
                .is_some()
            {
                return Err(SourceFlowInvariant::DuplicateAssignment(assignment.target).into());
            }
            assignments.push(SourceFlowAssignment {
                declaration: assignment.target,
                symbol: assignment.symbol,
            });
        }
        for origin in captures
            .into_iter()
            .map(SourceCapturedFlowOrigin::Assignment)
            .chain(
                captured_array_mutations
                    .into_iter()
                    .map(SourceCapturedFlowOrigin::ArrayMutation),
            )
        {
            validate_captured_flow_origin(
                arena,
                bound,
                store,
                host,
                container,
                origin,
                Some(syntax),
            )?;
            let assignment = origin.assignment();
            if effects
                .assignment_declarations
                .contains_key(&assignment.declaration)
                || effects
                    .captured_origins
                    .insert(assignment.declaration, origin)
                    .is_some()
            {
                return Err(
                    SourceFlowInvariant::DuplicateAssignment(assignment.declaration).into(),
                );
            }
            assignments.push(assignment);
        }
        for mutation in array_mutations {
            validate_array_mutation_in_list(arena, bound, container, mutation, Some(syntax))?;
            if effects.captured_origins.contains_key(&mutation.call)
                || effects
                    .assignment_declarations
                    .insert(mutation.call, mutation.declaration)
                    .is_some()
            {
                return Err(SourceFlowInvariant::DuplicateAssignment(mutation.call).into());
            }
            assignments.push(SourceFlowAssignment {
                declaration: mutation.call,
                symbol: mutation.symbol,
            });
        }
        for call in calls {
            let statement = match prepare_nullish_call(
                arena,
                bound,
                container,
                call,
                &nullish_assignments,
                &mut effects,
            )? {
                Some(statement) => statement,
                None => validate_statement_list_call(arena, bound, syntax, call)?,
            };
            if effects.calls.insert(call, statement).is_some() {
                return Err(SourceFlowInvariant::DuplicateCall(call).into());
            }
        }
        for origin in effects.captured_origins.values() {
            if let SourceCapturedFlowOrigin::ArrayMutation(mutation) = origin
                && !effects.calls.contains_key(&mutation.mutation.call)
            {
                return Err(
                    SourceFlowInvariant::InvalidArrayMutation(mutation.mutation.call).into(),
                );
            }
        }
        prepare_nullish_assignments(
            arena,
            bound,
            store,
            Some(host),
            container,
            nullish_assignments,
            &mut assignments,
            &mut conditions,
            &mut effects,
        )?;
        Self::preflight_with_effects(
            bound,
            container,
            matches!(
                syntax.callable.family,
                super::source_callables::SourceCallableFamily::ArrowFunction
                    | super::source_callables::SourceCallableFamily::ObjectLiteralMethod
            )
            .then_some(container),
            points,
            conditions,
            assignments,
            effects,
        )
    }

    pub(super) fn contains_call(&self, call: NodeRef) -> bool {
        self.calls.contains_key(&call)
    }

    pub(super) fn contains_condition_value(&self, value: NodeRef) -> bool {
        self.conditions.values().any(|condition| {
            matches!(condition,
            SourceFlowCondition::Equality(condition) if condition.value == value)
        })
    }

    /// Proves an ordinary source statement against the existing source-file graph.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_source_statement(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        statement: NodeRef,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceFlowCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        updates: impl IntoIterator<Item = SourceFlowUpdate>,
        calls: impl IntoIterator<Item = NodeRef>,
    ) -> Result<Self, SourceFlowError> {
        Self::preflight_source_statement_with_nullish_assignments(
            arena,
            bound,
            store,
            host,
            statement,
            points,
            conditions,
            assignments,
            updates,
            calls,
            [],
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_source_statement_with_nullish_assignments(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        statement: NodeRef,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceFlowCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        updates: impl IntoIterator<Item = SourceFlowUpdate>,
        calls: impl IntoIterator<Item = NodeRef>,
        nullish_assignments: impl IntoIterator<Item = SourceFlowNullishAssignment>,
    ) -> Result<Self, SourceFlowError> {
        let nullish_assignments = nullish_assignments.into_iter().collect::<Vec<_>>();
        let region = if nullish_assignments.is_empty() {
            source_statement_flow_region(arena, bound, store, statement)?
        } else {
            source_nullish_statement_flow_region(arena, bound, statement, &nullish_assignments)?
        };
        let container = bound.source_file();
        let mut effects = SourceFlowEffects {
            region: Some(region),
            ..SourceFlowEffects::default()
        };
        let points = points.into_iter().collect::<Vec<_>>();
        for point in &points {
            let flow = source_region_point_flow(arena, bound, *point, Some(region))?;
            if effects.region_points.insert(*point, flow).is_some() {
                return Err(SourceFlowInvariant::DuplicatePoint(*point).into());
            }
        }
        let mut assignments = assignments.into_iter().collect::<Vec<_>>();
        let retained_conditions = bound
            .flow_graph()
            .nodes()
            .iter()
            .filter(|node| {
                node.flags
                    .intersects(FlowFlags::TRUE_CONDITION | FlowFlags::FALSE_CONDITION)
            })
            .filter_map(|node| match node.payload.as_ref() {
                Some(FlowNodePayload::Ast(node)) => Some(*node),
                _ => None,
            })
            .collect::<HashSet<_>>();
        let mut conditions = conditions
            .into_iter()
            .filter(|condition| retained_conditions.contains(&condition.expression()))
            .collect::<Vec<_>>();
        for update in updates {
            validate_source_update(arena, bound, store, host, update)?;
            if effects.updates.insert(update.target, update).is_some()
                || effects
                    .assignment_declarations
                    .insert(update.target, update.declaration)
                    .is_some()
            {
                return Err(SourceFlowInvariant::DuplicateAssignment(update.target).into());
            }
            assignments.push(SourceFlowAssignment {
                declaration: update.target,
                symbol: update.symbol,
            });
        }
        for call in calls {
            let statement = match prepare_nullish_call(
                arena,
                bound,
                container,
                call,
                &nullish_assignments,
                &mut effects,
            )? {
                Some(statement) => statement,
                None => validate_source_statement_call(arena, bound, call)?,
            };
            if effects.calls.insert(call, statement).is_some() {
                return Err(SourceFlowInvariant::DuplicateCall(call).into());
            }
        }
        prepare_nullish_assignments(
            arena,
            bound,
            store,
            Some(host),
            container,
            nullish_assignments,
            &mut assignments,
            &mut conditions,
            &mut effects,
        )?;
        Self::preflight_with_effects(
            bound,
            container,
            None,
            points,
            conditions,
            assignments,
            effects,
        )
    }

    pub(super) fn has_reachable_end(&self) -> bool {
        self.end.is_some()
    }

    /// Uses the binder's body flow, including an inline static block's outer start.
    #[cfg(test)]
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
        Self::preflight_class_body_with_conditions(
            arena,
            bound,
            store,
            host,
            body,
            points,
            [],
            assignments,
            [],
            calls,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_class_body_with_conditions(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        body: &ClassBodyPlan,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceFlowCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        local_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
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
            (NodeData::PropertyDeclaration(data), ClassBodyKind::PropertyInitializer { .. })
                if declaration.kind == SyntaxKind::PropertyDeclaration =>
            {
                data.initializer
            }
            _ => return Err(invalid().into()),
        };
        if expected_body != Some(body.body.node)
            || declaration.parent != Some(body.class_declaration.node)
            || arena.get(body.body.node).is_none_or(|block| {
                !matches!(body.kind, ClassBodyKind::PropertyInitializer { .. })
                    && block.kind != SyntaxKind::Block
                    || block.parent != Some(body.declaration.node)
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
        let conditions = conditions.into_iter().collect::<Vec<_>>();
        let (conditions, expression_conditions) = prepare_class_expression_conditions(
            arena, bound, store, host, body, container, &points, conditions,
        )?;
        for condition in &conditions {
            if let Some(access) = condition.class_property_access() {
                validate_class_property_flow_condition(store, host, bound, body, *condition)?;
                if !points.contains(&access) {
                    return Err(SourceFlowInvariant::MissingFlowPoint(access).into());
                }
            }
        }
        let mut effects = SourceFlowEffects {
            class_expression_conditions: expression_conditions,
            class_body: Some(body.clone()),
            start_container: matches!(body.kind, ClassBodyKind::StaticBlock)
                .then(|| class_control_flow_container(host, body.declaration))
                .transpose()?,
            ..SourceFlowEffects::default()
        };
        let mut assignments = assignments.into_iter().collect::<Vec<_>>();
        for assignment in local_assignments {
            validate_class_local_assignment(arena, bound, store, host, body, assignment)?;
            if effects
                .assignment_declarations
                .insert(assignment.target, assignment.parameter)
                .is_some()
            {
                return Err(SourceFlowInvariant::DuplicateAssignment(assignment.target).into());
            }
            assignments.push(SourceFlowAssignment {
                declaration: assignment.target,
                symbol: assignment.symbol,
            });
        }
        for call in calls {
            let statement = validate_class_body_call(arena, bound, body, container, call)?;
            if effects.calls.insert(call, statement).is_some() {
                return Err(SourceFlowInvariant::DuplicateCall(call).into());
            }
        }
        if matches!(
            body.kind,
            ClassBodyKind::Constructor | ClassBodyKind::Method { .. } | ClassBodyKind::StaticBlock
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
            pending.extend(bound.flow_graph().container_end(body.declaration));
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
                    let assignment = if matches!(
                        body.kind,
                        ClassBodyKind::Constructor | ClassBodyKind::Method { .. }
                    ) {
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
        Self::preflight_with_effects(
            bound,
            container,
            None,
            points,
            conditions,
            assignments,
            effects,
        )
    }

    /// Freezes and validates every flow chain that the source executor may
    /// request. No semantic store state is read or written during preflight.
    #[cfg(test)]
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

    /// Uses ordinary call statements with the existing branch-flow checks.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_with_calls(
        arena: &NodeArena,
        bound: &BoundFile,
        container: NodeRef,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceFlowCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
        array_mutations: impl IntoIterator<Item = SourceFlowArrayMutation>,
    ) -> Result<Self, SourceFlowError> {
        if bound.node_arena_id() != arena.id()
            || bound.node_arena_revision() != arena.revision()
            || !container.is_for(arena.id(), bound.file_id())
        {
            return Err(SourceFlowInvariant::ForeignNode(container).into());
        }
        let mut assignments = assignments.into_iter().collect::<Vec<_>>();
        let mut effects = SourceFlowEffects::default();
        for mutation in array_mutations {
            validate_array_mutation(arena, bound, container, mutation)?;
            if effects
                .assignment_declarations
                .insert(mutation.call, mutation.declaration)
                .is_some()
            {
                return Err(SourceFlowInvariant::DuplicateAssignment(mutation.call).into());
            }
            assignments.push(SourceFlowAssignment {
                declaration: mutation.call,
                symbol: mutation.symbol,
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
            conditions,
            assignments,
            effects,
        )
    }

    /// Proves direct call statements and assignments to exact function parameters.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_linear(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        container: NodeRef,
        points: impl IntoIterator<Item = NodeRef>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        parameter_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
    ) -> Result<Self, SourceFlowError> {
        Self::preflight_linear_with_logical_statements(
            arena,
            bound,
            store,
            container,
            points,
            assignments,
            parameter_assignments,
            calls,
            [],
        )
    }

    /// Also proves the detached branches of bounded logical expression statements.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_linear_with_logical_statements(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        container: NodeRef,
        points: impl IntoIterator<Item = NodeRef>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        parameter_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
        logical_statements: impl IntoIterator<Item = SourceLinearLogicalStatementSyntax>,
    ) -> Result<Self, SourceFlowError> {
        Self::preflight_linear_effects(
            arena,
            bound,
            store,
            None,
            container,
            points,
            [],
            assignments,
            parameter_assignments,
            calls,
            logical_statements,
            [],
            [],
            [],
        )
    }

    /// Keeps captured writes separate from the existing own-parameter proof.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_linear_with_captured_effects(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        container: NodeRef,
        points: impl IntoIterator<Item = NodeRef>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        parameter_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
        logical_statements: impl IntoIterator<Item = SourceLinearLogicalStatementSyntax>,
        captured_assignments: impl IntoIterator<Item = SourceFlowCapturedAssignment>,
        captured_array_mutations: impl IntoIterator<Item = SourceFlowCapturedArrayMutation>,
    ) -> Result<Self, SourceFlowError> {
        Self::preflight_linear_effects(
            arena,
            bound,
            store,
            Some(host),
            container,
            points,
            [],
            assignments,
            parameter_assignments,
            calls,
            logical_statements,
            captured_assignments,
            captured_array_mutations,
            [],
        )
    }

    /// Keeps only eager truthiness conditions that the binder retained on these paths.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_linear_with_conditions(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        container: NodeRef,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceTruthinessCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        parameter_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
    ) -> Result<Self, SourceFlowError> {
        Self::preflight_linear_with_conditions_and_logical_statements(
            arena,
            bound,
            store,
            container,
            points,
            conditions,
            assignments,
            parameter_assignments,
            calls,
            [],
        )
    }

    /// Retains eager condition facts without replacing captured write evidence.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_linear_with_conditions_and_captured_effects(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        container: NodeRef,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceTruthinessCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        parameter_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
        logical_statements: impl IntoIterator<Item = SourceLinearLogicalStatementSyntax>,
        captured_assignments: impl IntoIterator<Item = SourceFlowCapturedAssignment>,
        captured_array_mutations: impl IntoIterator<Item = SourceFlowCapturedArrayMutation>,
    ) -> Result<Self, SourceFlowError> {
        let conditions = conditions.into_iter().collect::<Vec<_>>();
        if conditions.is_empty() {
            return Self::preflight_linear_with_captured_effects(
                arena,
                bound,
                store,
                host,
                container,
                points,
                assignments,
                parameter_assignments,
                calls,
                logical_statements,
                captured_assignments,
                captured_array_mutations,
            );
        }
        Self::preflight_linear_effects(
            arena,
            bound,
            store,
            Some(host),
            container,
            points,
            conditions,
            assignments,
            parameter_assignments,
            calls,
            logical_statements,
            captured_assignments,
            captured_array_mutations,
            [],
        )
    }

    /// Combines retained eager conditions with exact detached statement branches.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_linear_with_conditions_and_logical_statements(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        container: NodeRef,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceTruthinessCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        parameter_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
        logical_statements: impl IntoIterator<Item = SourceLinearLogicalStatementSyntax>,
    ) -> Result<Self, SourceFlowError> {
        Self::preflight_linear_effects(
            arena,
            bound,
            store,
            None,
            container,
            points,
            conditions,
            assignments,
            parameter_assignments,
            calls,
            logical_statements,
            [],
            [],
            [],
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn preflight_linear_with_nullish_assignments(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        container: NodeRef,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceTruthinessCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        parameter_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
        logical_statements: impl IntoIterator<Item = SourceLinearLogicalStatementSyntax>,
        captured_assignments: impl IntoIterator<Item = SourceFlowCapturedAssignment>,
        captured_array_mutations: impl IntoIterator<Item = SourceFlowCapturedArrayMutation>,
        nullish_assignments: impl IntoIterator<Item = SourceFlowNullishAssignment>,
    ) -> Result<Self, SourceFlowError> {
        Self::preflight_linear_effects(
            arena,
            bound,
            store,
            Some(host),
            container,
            points,
            conditions,
            assignments,
            parameter_assignments,
            calls,
            logical_statements,
            captured_assignments,
            captured_array_mutations,
            nullish_assignments,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn preflight_linear_effects(
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: Option<&DeclaredTypeHost<'_>>,
        container: NodeRef,
        points: impl IntoIterator<Item = NodeRef>,
        conditions: impl IntoIterator<Item = SourceTruthinessCondition>,
        assignments: impl IntoIterator<Item = SourceFlowAssignment>,
        parameter_assignments: impl IntoIterator<Item = SourceFlowParameterAssignment>,
        calls: impl IntoIterator<Item = NodeRef>,
        logical_statements: impl IntoIterator<Item = SourceLinearLogicalStatementSyntax>,
        captured_assignments: impl IntoIterator<Item = SourceFlowCapturedAssignment>,
        captured_array_mutations: impl IntoIterator<Item = SourceFlowCapturedArrayMutation>,
        nullish_assignments: impl IntoIterator<Item = SourceFlowNullishAssignment>,
    ) -> Result<Self, SourceFlowError> {
        if bound.node_arena_id() != arena.id()
            || bound.node_arena_revision() != arena.revision()
            || !container.is_for(arena.id(), bound.file_id())
        {
            return Err(SourceFlowInvariant::ForeignNode(container).into());
        }

        let nullish_assignments = nullish_assignments.into_iter().collect::<Vec<_>>();
        let mut planned_assignments = assignments.into_iter().collect::<Vec<_>>();
        let mut effects = SourceFlowEffects::default();
        for assignment in parameter_assignments {
            validate_parameter_assignment(arena, bound, store, host, container, assignment)?;
            if effects
                .assignment_declarations
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
        for origin in captured_assignments
            .into_iter()
            .map(SourceCapturedFlowOrigin::Assignment)
            .chain(
                captured_array_mutations
                    .into_iter()
                    .map(SourceCapturedFlowOrigin::ArrayMutation),
            )
        {
            let host = host.ok_or(SourceFlowInvariant::InvalidCapturedLocal(
                origin.local().target,
            ))?;
            validate_captured_flow_origin(arena, bound, store, host, container, origin, None)?;
            let assignment = origin.assignment();
            if effects
                .assignment_declarations
                .contains_key(&assignment.declaration)
                || effects
                    .captured_origins
                    .insert(assignment.declaration, origin)
                    .is_some()
            {
                return Err(
                    SourceFlowInvariant::DuplicateAssignment(assignment.declaration).into(),
                );
            }
            planned_assignments.push(assignment);
        }
        for call in calls {
            let statement = match prepare_nullish_call(
                arena,
                bound,
                container,
                call,
                &nullish_assignments,
                &mut effects,
            )? {
                Some(statement) => statement,
                None => validate_linear_direct_call(arena, bound, store, container, call)?,
            };
            if effects.calls.insert(call, statement).is_some() {
                return Err(SourceFlowInvariant::DuplicateCall(call).into());
            }
        }
        for origin in effects.captured_origins.values() {
            if let SourceCapturedFlowOrigin::ArrayMutation(mutation) = origin
                && !effects.calls.contains_key(&mutation.mutation.call)
            {
                return Err(
                    SourceFlowInvariant::InvalidArrayMutation(mutation.mutation.call).into(),
                );
            }
        }

        let candidates = conditions.into_iter().collect::<Vec<_>>();
        let mut condition_nodes = HashSet::new();
        for condition in &candidates {
            if !condition_nodes.insert(condition.expression) {
                return Err(SourceFlowInvariant::DuplicateCondition(condition.expression).into());
            }
        }
        let mut conditions = Vec::new();
        for syntax in logical_statements {
            let proof = preflight_logical_statement(arena, bound, container, syntax)?;
            for expression in [proof.syntax.left, proof.syntax.right] {
                if !condition_nodes.insert(expression) {
                    return Err(SourceFlowInvariant::DuplicateCondition(expression).into());
                }
            }
            conditions.extend([
                SourceFlowCondition::Unchanged(proof.syntax.left),
                SourceFlowCondition::Unchanged(proof.syntax.right),
            ]);
            effects.logical_statements.push(proof);
        }

        let points = points.into_iter().collect::<Vec<_>>();
        if !candidates.is_empty() {
            let graph = bound.flow_graph();
            let mut point_flows = HashMap::new();
            let mut effective_points = Vec::new();
            for &point in &points {
                insert_flow_point(
                    bound,
                    graph,
                    container,
                    &mut point_flows,
                    &mut effective_points,
                    point,
                    true,
                )?;
            }
            for proof in &effects.logical_statements {
                for &(point, flow) in &proof.source_points {
                    if flow.is_some() {
                        insert_flow_point(
                            bound,
                            graph,
                            container,
                            &mut point_flows,
                            &mut effective_points,
                            point,
                            false,
                        )?;
                    }
                }
            }
            let mut retained = retained_linear_truthiness_conditions(
                arena,
                bound,
                container,
                &effective_points,
                candidates,
            )?;
            retained.extend(conditions);
            conditions = retained;
        }

        prepare_nullish_assignments(
            arena,
            bound,
            store,
            host,
            container,
            nullish_assignments,
            &mut planned_assignments,
            &mut conditions,
            &mut effects,
        )?;
        let expected_start_payload = arena
            .get(container.node)
            .is_some_and(|record| {
                record.kind == SyntaxKind::ArrowFunction
                    && matches!(record.data, NodeData::ArrowFunction(_))
                    || record.kind == SyntaxKind::MethodDeclaration
                        && bound.symbol(container).is_some_and(|owner| {
                            store.source_object_literal_method_owner_is_exact(container, owner)
                        })
            })
            .then_some(container);
        Self::preflight_with_effects(
            bound,
            container,
            expected_start_payload,
            points,
            conditions,
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
            if matches!(condition, SourceFlowCondition::ClassExpression(_)) {
                return Err(SourceFlowInvariant::UnknownCondition(expression).into());
            }
            if condition.class_property_access().is_some() && effects.class_body.is_none()
            {
                return Err(SourceFlowInvariant::InvalidClassProperty(expression).into());
            }
            if let SourceFlowCondition::Nullish(condition) = condition
                && !effects
                    .class_expression_conditions
                    .get(&expression)
                    .is_some_and(|proof| {
                        matches!(proof.source.kind, SourceClassExpressionConditionKind::Nullish(symbol)
                            if condition.symbol == Some(symbol))
                    })
                && effects
                    .nullish_assignments
                    .get(&expression)
                    .is_none_or(|proof| {
                        proof.assignment.target != expression
                            || proof.assignment.symbol != condition.symbol
                    })
            {
                return Err(SourceFlowInvariant::UnknownCondition(expression).into());
            }
            if planned_conditions.insert(expression, condition).is_some() {
                return Err(SourceFlowInvariant::DuplicateCondition(expression).into());
            }
        }

        let mut planned_assignments = HashMap::new();
        let mut assignment_order = Vec::new();
        for assignment in assignments {
            validate_bound_node(bound, graph, assignment.declaration)?;
            if let Some(origin) = effects.captured_origins.get(&assignment.declaration) {
                if effects
                    .assignment_declarations
                    .contains_key(&assignment.declaration)
                {
                    return Err(
                        SourceFlowInvariant::DuplicateAssignment(assignment.declaration).into(),
                    );
                }
                validate_retained_captured_origin(
                    bound,
                    container,
                    assignment,
                    *origin,
                    effects.statement_list.as_ref(),
                )?;
            } else if let Some(parameter) =
                effects.assignment_declarations.get(&assignment.declaration)
            {
                if bound.symbol(*parameter) != Some(assignment.symbol)
                    || bound.container(*parameter) != Some(container)
                    || bound.container(assignment.declaration) != Some(container)
                        && !(effects.class_body.is_some()
                            && bound.flow_container(assignment.declaration) == Some(container))
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
            if let Some(flow) = effects.region_points.get(&point).copied() {
                validate_bound_node(bound, graph, point)?;
                if planned_points.insert(point, flow).is_some() {
                    return Err(SourceFlowInvariant::DuplicatePoint(point).into());
                }
                point_order.push(point);
                continue;
            }
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
        for proof in &effects.logical_statements {
            for &(point, flow) in &proof.source_points {
                if flow.is_some() {
                    insert_flow_point(
                        bound,
                        graph,
                        container,
                        &mut planned_points,
                        &mut point_order,
                        point,
                        false,
                    )?;
                }
            }
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
            _ => effects
                .region
                .map(|region| region.exit)
                .or_else(|| graph.container_end(container)),
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
            class_expression_conditions: effects.class_expression_conditions,
            assignments: planned_assignments,
            assignment_order,
            assignment_declarations: effects.assignment_declarations,
            captured_origins: effects.captured_origins,
            statement_list: effects.statement_list,
            calls: effects.calls,
            logical_statements: effects.logical_statements,
            class_body: effects.class_body,
            property_assignments: effects.property_assignments,
            region: effects.region,
            updates: effects.updates,
            nullish_assignments: effects.nullish_assignments,
            member_assignments: effects.member_assignments,
            nullish_calls: effects.nullish_calls,
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
        if let Some(origin) = self.captured_origins.values().next() {
            return Err(SourceFlowInvariant::InvalidCapturedLocal(origin.local().target).into());
        }
        self.frame_with_validated_captures(bound, base)
    }

    /// Revalidates captured source owners before any child-body execution.
    pub(super) fn frame_with_captured_locals<'plan, 'graph>(
        &'plan self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        bound: &'graph BoundFile,
        base: SourceFlowTypes,
    ) -> Result<SourceFlowFrame<'plan, 'graph>, SourceFlowError> {
        for proof in self.member_assignments.values() {
            if source_member_assignment_proof(store, host, proof.expression)? != Some(*proof) {
                return Err(SourceFlowInvariant::InvalidParameterAssignment(proof.target).into());
            }
        }
        if !self.nullish_assignments.is_empty() {
            let (arena, _) = host
                .source(self.container)
                .ok_or(SourceFlowInvariant::ForeignNode(self.container))?;
            for proof in self.nullish_assignments.values() {
                if source_nullish_assignment_proof(
                    arena,
                    bound,
                    store,
                    host,
                    self.container,
                    proof.assignment,
                )? != *proof
                {
                    return Err(SourceFlowInvariant::InvalidParameterAssignment(
                        proof.assignment.target,
                    )
                    .into());
                }
            }
            let assignments = self
                .nullish_assignments
                .values()
                .map(|proof| proof.assignment)
                .collect::<Vec<_>>();
            for (call, antecedent) in &self.nullish_calls {
                let (statement, actual) =
                    validate_nullish_call(arena, bound, self.container, *call, &assignments)?
                        .ok_or(SourceFlowInvariant::InvalidCall(*call))?;
                if actual != *antecedent || self.calls.get(call) != Some(&statement) {
                    return Err(SourceFlowInvariant::InvalidCall(*call).into());
                }
            }
        }
        if let Some(syntax) = &self.statement_list {
            let (arena, _) = host
                .source(self.container)
                .ok_or(SourceFlowInvariant::ForeignNode(self.container))?;
            validate_statement_list_source(arena, bound, store, host, syntax)?;
            if syntax.callable.declaration != self.container {
                return Err(SourceFlowInvariant::ForeignNode(self.container).into());
            }
            for (&target, &declaration) in &self.assignment_declarations {
                if !self.nullish_assignments.contains_key(&target)
                    && !self.updates.contains_key(&target)
                    && arena
                        .get(target.node)
                        .is_some_and(|record| record.kind == SyntaxKind::Identifier)
                    && arena.get(declaration.node).is_some_and(|record| {
                        record.kind == SyntaxKind::BindingElement
                            || matches!(&record.data, NodeData::VariableDeclaration(variable) if variable.initializer.is_some())
                    })
                {
                    let symbol = self
                        .assignments
                        .get(&target)
                        .ok_or(SourceFlowInvariant::UnknownAssignment(target))?
                        .symbol;
                    validate_initialized_local_assignment(
                        arena,
                        bound,
                        store,
                        host,
                        self.container,
                        SourceFlowParameterAssignment {
                            target,
                            parameter: declaration,
                            symbol,
                        },
                        syntax,
                    )?;
                }
            }
        }
        if let Some(region) = self.region {
            let (arena, _) = host
                .source(region.statement)
                .ok_or(SourceFlowInvariant::InvalidSourceRegion(region.statement))?;
            let actual = if self.nullish_assignments.is_empty() {
                source_statement_flow_region(arena, bound, store, region.statement)?
            } else {
                let assignments = self
                    .nullish_assignments
                    .values()
                    .map(|proof| proof.assignment)
                    .collect::<Vec<_>>();
                source_nullish_statement_flow_region(arena, bound, region.statement, &assignments)?
            };
            if actual != region {
                return Err(SourceFlowInvariant::InvalidSourceRegion(region.statement).into());
            }
            for (point, expected) in &self.points {
                if source_region_point_flow(arena, bound, *point, Some(region))? != *expected {
                    return Err(SourceFlowInvariant::MissingFlowPoint(*point).into());
                }
            }
            for update in self.updates.values() {
                validate_source_update(arena, bound, store, host, *update)?;
            }
        }
        if self.captured_origins.is_empty() {
            return self.frame(bound, base);
        }
        let (arena, _) = host
            .source(self.container)
            .ok_or(SourceFlowInvariant::ForeignNode(self.container))?;
        for (&target, origin) in &self.captured_origins {
            let assignment = self
                .assignments
                .get(&target)
                .ok_or(SourceFlowInvariant::UnknownAssignment(target))?;
            validate_retained_captured_origin(
                bound,
                self.container,
                *assignment,
                *origin,
                self.statement_list.as_ref(),
            )?;
            validate_captured_flow_origin(
                arena,
                bound,
                store,
                host,
                self.container,
                *origin,
                self.statement_list.as_ref(),
            )?;
        }
        self.frame_with_validated_captures(bound, base)
    }

    fn frame_with_validated_captures<'plan, 'graph>(
        &'plan self,
        bound: &'graph BoundFile,
        base: SourceFlowTypes,
    ) -> Result<SourceFlowFrame<'plan, 'graph>, SourceFlowError> {
        let graph = bound.flow_graph();
        validate_container(graph, self.container)?;
        for proof in self.nullish_assignments.values() {
            if bound.node_arena_revision() != proof.revision {
                return Err(SourceFlowInvariant::InvalidParameterAssignment(
                    proof.assignment.target,
                )
                .into());
            }
        }
        for proof in self.member_assignments.values() {
            if bound.node_arena_revision() != proof.revision
                || proof.container != self.container
            {
                return Err(SourceFlowInvariant::InvalidParameterAssignment(proof.target).into());
            }
        }
        if let Some(region) = self.region
            && (bound.flow_at(region.entry_node).or_else(|| {
                (bound.flow_graph().is_unreachable(region.entry_node) == Some(true))
                    .then(|| bound.flow_graph().nodes().unreachable())
            }) != Some(region.entry)
                || bound.flow_container(region.statement) != Some(self.container))
        {
            return Err(SourceFlowInvariant::InvalidSourceRegion(region.statement).into());
        }
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
        for (&target, assignment) in &self.assignments {
            if assignment.declaration != target {
                return Err(SourceFlowInvariant::UnknownAssignment(target).into());
            }
            if !self.assignment_declarations.contains_key(&target)
                && !self.captured_origins.contains_key(&target)
                && (bound.symbol(target) != Some(assignment.symbol)
                    || bound.container(target) != Some(self.container)
                        && !(self.class_body.is_some()
                            && bound.flow_container(target) == Some(self.container)))
            {
                return Err(SourceFlowInvariant::InvalidParameterAssignment(target).into());
            }
        }
        for (target, parameter) in &self.assignment_declarations {
            let assignment = self
                .assignments
                .get(target)
                .ok_or(SourceFlowInvariant::UnknownAssignment(*target))?;
            if bound.symbol(*parameter) != Some(assignment.symbol)
                || bound.container(*parameter) != Some(self.container)
                || bound.container(*target) != Some(self.container)
                    && !(self.class_body.is_some()
                        && bound.flow_container(*target) == Some(self.container))
            {
                return Err(SourceFlowInvariant::InvalidParameterAssignment(*target).into());
            }
        }
        for (&target, origin) in &self.captured_origins {
            let assignment = self
                .assignments
                .get(&target)
                .ok_or(SourceFlowInvariant::UnknownAssignment(target))?;
            if self.assignment_declarations.contains_key(&target) {
                return Err(SourceFlowInvariant::DuplicateAssignment(target).into());
            }
            validate_retained_captured_origin(
                bound,
                self.container,
                *assignment,
                *origin,
                self.statement_list.as_ref(),
            )?;
            if !base.contains_key(&assignment.symbol) {
                return Err(SourceFlowInvariant::MissingCurrentType(assignment.symbol).into());
            }
        }
        if !self.logical_statements.is_empty() {
            for proof in &self.logical_statements {
                validate_logical_statement(bound, self.container, proof)?;
                for &(point, flow) in &proof.source_points {
                    if flow.is_some() && self.points.get(&point).copied() != flow {
                        return Err(SourceFlowInvariant::InvalidLogicalStatement(
                            proof.syntax.statement,
                        )
                        .into());
                    }
                }
                for expression in [proof.syntax.left, proof.syntax.right] {
                    if self.conditions.get(&expression)
                        != Some(&SourceFlowCondition::Unchanged(expression))
                    {
                        return Err(SourceFlowInvariant::InvalidLogicalStatement(
                            proof.syntax.statement,
                        )
                        .into());
                    }
                }
            }
            if self.end != graph.container_end(self.container) {
                return Err(SourceFlowInvariant::InvalidLogicalStatement(
                    self.logical_statements[0].syntax.statement,
                )
                .into());
            }
            self.validate_flow_paths(bound)?;
        }
        if !self.captured_origins.is_empty() {
            if self.end != graph.container_end(self.container) {
                return Err(SourceFlowInvariant::InvalidCapturedLocal(self.container).into());
            }
            if self.logical_statements.is_empty() {
                self.validate_flow_paths(bound)?;
            }
        }
        if !self.nullish_assignments.is_empty() {
            self.validate_flow_paths(bound)?;
        }
        if self
            .statement_list
            .as_ref()
            .is_some_and(|syntax| syntax.contains_for_of() || syntax.contains_counted_for())
        {
            self.validate_flow_paths(bound)?;
        }
        Ok(SourceFlowFrame {
            plan: self,
            bound,
            graph,
            declared_types: base.clone(),
            base: SourceFlowSnapshot::new(base),
            assignment_states: self
                .assignments
                .keys()
                .copied()
                .map(|declaration| {
                    let state = match self.updates.get(&declaration) {
                        Some(update) if update.readonly => {
                            SourceFlowAssignmentState::ReadonlyUpdate
                        }
                        Some(_) => SourceFlowAssignmentState::Update,
                        None if self
                            .nullish_assignments
                            .get(&declaration)
                            .is_some_and(|proof| proof.assignment.readonly) =>
                        {
                            SourceFlowAssignmentState::ReadonlyUpdate
                        }
                        None => SourceFlowAssignmentState::Pending,
                    };
                    (declaration, state)
                })
                .collect(),
            completed_callable_updates: HashSet::new(),
            completed_expression_calls: HashSet::new(),
            call_effects: HashMap::new(),
            condition_values: HashMap::new(),
            in_conditions: HashMap::new(),
            memo: HashMap::new(),
            visiting: HashSet::new(),
            loop_snapshots: HashMap::new(),
            reference: None,
        })
    }

    /// Uses only retained reassignments. An initializer or array mutation does
    /// not replace the captured variable's value.
    pub(super) fn captured_variables_with_later_writes(
        &self,
        host: &DeclaredTypeHost<'_>,
        location: NodeRef,
    ) -> Result<HashSet<SemanticSymbolId>, SourceFlowError> {
        let mut assignments = Vec::with_capacity(self.assignment_declarations.len());
        for (&target, &declaration) in &self.assignment_declarations {
            let invalid = || SourceFlowInvariant::InvalidParameterAssignment(target);
            let assignment = self.assignments.get(&target).ok_or_else(invalid)?;
            if host.node(target).ok_or_else(invalid)?.kind == SyntaxKind::CallExpression {
                continue;
            }
            assignments.push(SourceFlowParameterAssignment {
                target,
                parameter: declaration,
                symbol: assignment.symbol,
            });
        }
        for origin in self.captured_origins.values() {
            if let SourceCapturedFlowOrigin::Assignment(assignment) = origin {
                assignments.push(SourceFlowParameterAssignment {
                    target: assignment.local.target,
                    parameter: assignment.local.declaration,
                    symbol: assignment.local.symbol,
                });
            }
        }
        captured_variables_with_later_writes(host, location, &assignments)
    }

    fn validate_flow_paths(&self, bound: &BoundFile) -> Result<(), SourceFlowError> {
        let mut validated = HashSet::new();
        let mut visiting = SourceFlowActivePath::default();
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
        for proof in &self.logical_statements {
            self.validate_flow(
                bound,
                proof.rows.join,
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
        for (target, proof) in &self.nullish_assignments {
            if proof.flow.is_some() && !coverage.assignments.contains(target) {
                return Err(SourceFlowInvariant::UnreachedAssignment(*target).into());
            }
        }
        for target in self.member_assignments.keys() {
            if !coverage.assignments.contains(target) {
                return Err(SourceFlowInvariant::UnreachedAssignment(*target).into());
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
        for (condition, planned) in &self.conditions {
            let Some(edges) = coverage.condition_edges.get(condition).copied() else {
                if matches!(planned, SourceFlowCondition::Unchanged(_))
                    && !self.class_expression_conditions.contains_key(condition)
                {
                    continue;
                }
                return Err(SourceFlowInvariant::UnreachedCondition(*condition).into());
            };
            let expected = self
                .class_expression_conditions
                .get(condition)
                .map_or(BOTH_CONDITION_EDGES, |proof| proof.edges);
            if edges != expected {
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
        visiting: &mut SourceFlowActivePath,
        coverage: &mut SourceFlowCoverage,
    ) -> Result<(), SourceFlowError> {
        let graph = bound.flow_graph();
        if self.region.is_some_and(|region| region.entry == flow) {
            flow_node(graph, flow)?;
            return Ok(());
        }
        if validated.contains(&flow) {
            return Ok(());
        }
        if depth > FLOW_DEPTH_LIMIT {
            return Err(SourceFlowInvariant::DepthLimit(flow).into());
        }
        if !visiting.members.insert(flow) {
            let _ = flow_node(graph, flow)?;
            return visiting.validate_cycle(graph.nodes(), flow);
        }
        visiting.nodes.push(flow);
        let result = self.validate_flow_uncached(bound, flow, depth, validated, visiting, coverage);
        let last = visiting.nodes.pop();
        debug_assert_eq!(last, Some(flow));
        let removed = visiting.members.remove(&flow);
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
        visiting: &mut SourceFlowActivePath,
        coverage: &mut SourceFlowCoverage,
    ) -> Result<(), SourceFlowError> {
        let graph = bound.flow_graph();
        let node = flow_node(graph, flow)?;
        match source_flow_kind(flow, node.flags)? {
            SourceFlowKind::Unreachable => validate_unreachable_node(graph, flow, &node),
            SourceFlowKind::Start => validate_start_node(self, flow, &node),
            SourceFlowKind::Assignment | SourceFlowKind::ArrayMutation => {
                let antecedent = linear_antecedent(flow, &node)?;
                let declaration = ast_payload(flow, &node)?;
                if let Some(origin) = self.captured_origins.get(&declaration) {
                    validate_captured_origin_flow_node(*origin, flow, &node)?;
                }
                if !self.assignments.contains_key(&declaration)
                    && !self.property_assignments.contains_key(&declaration)
                    && !self.nullish_assignments.contains_key(&declaration)
                    && !self.member_assignments.contains_key(&declaration)
                {
                    if source_flow_kind(flow, node.flags)? == SourceFlowKind::ArrayMutation {
                        return Err(SourceFlowUnsupported::FlowKind {
                            flow,
                            flags: node.flags,
                        }
                        .into());
                    }
                    return Err(SourceFlowInvariant::UnknownAssignment(declaration).into());
                }
                if let Some(proof) = self.nullish_assignments.get(&declaration)
                    && proof.flow != Some(flow)
                {
                    return Err(SourceFlowInvariant::InvalidPayload(flow).into());
                }
                if let Some(proof) = self.member_assignments.get(&declaration)
                    && proof.flow != flow
                {
                    return Err(SourceFlowInvariant::InvalidPayload(flow).into());
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
                    | SourceFlowKind::ArrayMutation
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
    declared_types: SourceFlowTypes,
    assignment_states: HashMap<NodeRef, SourceFlowAssignmentState>,
    completed_callable_updates: HashSet<NodeRef>,
    completed_expression_calls: HashSet<NodeRef>,
    call_effects: HashMap<NodeRef, SourceFlowCallEffect>,
    condition_values: HashMap<NodeRef, TypeId>,
    in_conditions: HashMap<NodeRef, CompletedInCondition>,
    memo: HashMap<(FlowRef, Option<SemanticSymbolId>), SourceFlowSnapshot>,
    visiting: HashSet<(FlowRef, Option<SemanticSymbolId>)>,
    loop_snapshots: HashMap<(FlowRef, Option<SemanticSymbolId>), SourceFlowSnapshot>,
    reference: Option<SemanticSymbolId>,
}

/// Membership results checked with the source caller's instantiation session.
struct CompletedInCondition {
    input: TypeId,
    key: TypeId,
    when_true: TypeId,
    when_false: TypeId,
}

/// Restores the catch entry without reverting writes to outer variables.
pub(super) struct SourceCatchFlowScope {
    symbol: SemanticSymbolId,
    base: Option<TypeId>,
    declared: Option<TypeId>,
}

/// Keeps class initialization queries tied to one prepared body and binder graph.
pub(super) struct ClassInitializationFrame<'plan, 'graph> {
    access: ClassBodyAccessToken,
    body: &'plan ClassBodyPlan,
    flow: SourceFlowFrame<'plan, 'graph>,
    completed_calls: HashSet<NodeRef>,
    property_assignments: HashMap<NodeRef, CheckedClassPropertyAssignment>,
    property_conditions: HashMap<NodeRef, CompletedClassPropertyCondition>,
    predicate_conditions: HashMap<NodeRef, CompletedClassPropertyPredicate>,
    ordinary_calls: HashMap<NodeRef, CompletedClassOrdinaryCall>,
}

#[derive(Clone)]
struct CompletedClassPropertyCondition {
    condition: SourceFlowCondition,
    source: ClassPropertyTruthinessSource,
    member: ClassMemberSource,
    access: ClassBodyAccessToken,
    flow: FlowRef,
    edges: [FlowRef; 2],
    type_: TypeId,
}

struct CompletedClassPropertyPredicate {
    condition: SourceClassPropertyPredicateCondition,
    source: ClassPropertyTruthinessSource,
    member: ClassMemberSource,
    access: ClassBodyAccessToken,
    flow: FlowRef,
    edges: [FlowRef; 2],
    argument_type: TypeId,
    callee: NodeRef,
    callee_type: TypeId,
    callee_read: PlannedIdentifierRead,
    signature: SignatureId,
    predicate: TypePredicateId,
    predicate_type: TypeId,
    return_type: TypeId,
    arrays: CanonicalArrayTargets,
}

struct CompletedClassOrdinaryCall {
    plan: SourceCallPlan,
    access: ClassBodyAccessToken,
    callee_type: TypeId,
    callee_symbol: SymbolNodeLinks,
    signature: SignatureId,
    return_type: TypeId,
    arrays: CanonicalArrayTargets,
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
            property_conditions: HashMap::new(),
            predicate_conditions: HashMap::new(),
            ordinary_calls: HashMap::new(),
        })
    }

    pub(super) const fn access_token(&self) -> &ClassBodyAccessToken {
        &self.access
    }

    pub(super) const fn body_declaration(&self) -> NodeRef {
        self.body.declaration
    }

    pub(super) fn has_property_conditions(&self) -> bool {
        self.flow
            .plan
            .conditions
            .values()
            .any(|condition| condition.class_property_access().is_some())
    }

    pub(super) fn is_expression_condition_call(&self, call: NodeRef) -> bool {
        self.flow
            .plan
            .class_expression_conditions
            .get(&call)
            .is_some_and(|proof| {
                proof.source.kind == SourceClassExpressionConditionKind::Call
                    && self.flow.plan.conditions.get(&call)
                        == Some(&SourceFlowCondition::Unchanged(call))
            })
    }

    pub(super) fn has_property_equality_condition(&self, expression: NodeRef) -> bool {
        matches!(
            self.flow.plan.conditions.get(&expression),
            Some(SourceFlowCondition::ClassPropertyEquality(_))
        )
    }

    pub(super) fn is_predicate_condition_call(&self, call: NodeRef) -> bool {
        self.flow.plan.conditions.values().any(|condition| {
            matches!(condition, SourceFlowCondition::ClassPropertyPredicate(condition)
                if condition.call == call)
        })
    }

    /// Records the ordinary read after the source checker accepts its condition.
    pub(super) fn complete_property_condition(
        &mut self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        condition: SourceClassPropertyTruthinessCondition,
        raw: TypeId,
        result: TypeId,
    ) -> Result<(), SourceFlowError> {
        self.complete_class_property_condition(
            store,
            host,
            SourceFlowCondition::ClassPropertyTruthiness(condition),
            raw,
            result,
        )
    }

    pub(super) fn complete_property_equality_condition(
        &mut self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        condition: SourceClassPropertyEqualityCondition,
        raw: TypeId,
        result: TypeId,
    ) -> Result<(), SourceFlowError> {
        self.complete_class_property_condition(
            store,
            host,
            SourceFlowCondition::ClassPropertyEquality(condition),
            raw,
            result,
        )
    }

    fn complete_class_property_condition(
        &mut self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        condition: SourceFlowCondition,
        raw: TypeId,
        result: TypeId,
    ) -> Result<(), SourceFlowError> {
        let expression = condition.expression();
        let invalid = || SourceFlowInvariant::InvalidClassProperty(expression);
        let access = condition.class_property_access().ok_or_else(invalid)?;
        if raw != result || self.property_conditions.contains_key(&expression) {
            return Err(invalid().into());
        }
        let (source, edges) = validate_class_property_flow_condition(
            store, host, self.flow.bound, self.body, condition,
        )?;
        let type_ = if matches!(condition, SourceFlowCondition::ClassPropertyEquality(_)) {
            if store
                .intrinsic_bootstrap()
                .is_none_or(|bootstrap| raw != bootstrap.boolean_type)
            {
                return Err(invalid().into());
            }
            store
                .type_node_links(access)
                .and_then(|links| links.resolved_type)
                .ok_or_else(invalid)?
        } else {
            raw
        };
        let member = class_member_source(store, host, source.member).map_err(|_| invalid())?;
        let flow = self
            .flow
            .plan
            .points
            .get(&access)
            .copied()
            .ok_or_else(invalid)?;
        let completed = CompletedClassPropertyCondition {
            condition,
            source,
            member,
            access: self.access.clone(),
            flow,
            edges,
            type_,
        };
        self.validate_property_condition(store, host, &completed)?;
        self.property_conditions
            .insert(expression, completed);
        Ok(())
    }

    fn validate_property_condition(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        completed: &CompletedClassPropertyCondition,
    ) -> Result<(), SourceFlowError> {
        let condition = completed.condition;
        let expression = condition.expression();
        let invalid = || SourceFlowInvariant::InvalidClassProperty(expression);
        let access = condition.class_property_access().ok_or_else(invalid)?;
        let identities = class_body_identities(store, host, &self.access).map_err(|_| invalid())?;
        let receiver_symbol = store
            .type_payload(identities.this_type)
            .and_then(TypeRecord::symbol)
            .ok_or_else(invalid)?;
        let (source, edges) = validate_class_property_flow_condition(
            store, host, self.flow.bound, self.body, condition,
        )?;
        if completed.access != self.access
            || self.flow.plan.conditions.get(&expression) != Some(&condition)
            || source != completed.source
            || edges != completed.edges
            || class_member_source(store, host, completed.source.member).map_err(|_| invalid())?
                != completed.member
            || completed.member.declaring_class != identities.class_symbol
            || completed.member.declaration != completed.source.declaration
            || completed.member.side != ClassPropertySide::Instance
            || !matches!(completed.member.origin, ClassMemberOrigin::Field { .. })
            || self.flow.plan.points.get(&access) != Some(&completed.flow)
            || self.flow.bound.flow_at(access) != Some(completed.flow)
            || self.flow.bound.flow_container(access) != Some(self.body.declaration)
            || store.type_payload(completed.type_).is_none()
            || store.type_node_links(access)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(completed.type_),
                    ..TypeNodeLinks::default()
                })
            || store.symbol_node_links(access)
                != Some(&SymbolNodeLinks {
                    resolved_symbol: Some(completed.member.symbol),
                })
            || store.type_node_links(completed.source.context.receiver())
                != Some(&TypeNodeLinks {
                    resolved_type: Some(identities.this_type),
                    ..TypeNodeLinks::default()
                })
            || store.symbol_node_links(completed.source.context.receiver())
                != Some(&SymbolNodeLinks {
                    resolved_symbol: Some(receiver_symbol),
                })
        {
            return Err(invalid().into());
        }
        if let SourceFlowCondition::ClassPropertyEquality(condition) = condition {
            let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
            if store.type_node_links(expression)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(bootstrap.boolean_type),
                    ..TypeNodeLinks::default()
                })
                || store.type_node_links(condition.value)
                    != Some(&TypeNodeLinks {
                        resolved_type: Some(bootstrap.undefined_widening_type),
                        ..TypeNodeLinks::default()
                    })
            {
                return Err(invalid().into());
            }
        }
        Ok(())
    }

    /// Retains the checked predicate and the field read for both condition edges.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn complete_predicate_condition(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        globals: &CanonicalGlobalTypes,
        condition: SourceClassPropertyPredicateCondition,
        plan: &SourceCallPlan,
        raw: TypeId,
        result: TypeId,
    ) -> Result<(), SourceFlowError> {
        let invalid = || SourceFlowInvariant::InvalidCallEffect(condition.call);
        if raw != result
            || plan.node != condition.call
            || plan.arguments.len() != 1
            || plan.arguments[0].node != condition.access
            || self
                .predicate_conditions
                .contains_key(&condition.expression)
        {
            return Err(invalid().into());
        }
        let PlannedExpressionKind::Identifier(callee_read) = &plan.callee.kind else {
            return Err(invalid().into());
        };
        let (source, edges) = validate_class_property_predicate_condition(
            store,
            host,
            self.flow.bound,
            self.body,
            condition,
        )?;
        let member = class_member_source(store, host, source.member).map_err(|_| invalid())?;
        let signature = store
            .signature_links(condition.call)
            .and_then(|links| links.resolved_signature.signature())
            .ok_or_else(invalid)?;
        let predicate = store
            .signature(signature)
            .and_then(super::signatures::Signature::resolved_type_predicate)
            .ok_or(SourceFlowUnsupported::Call(condition.call))?;
        let predicate_type = store
            .type_predicate(predicate)
            .and_then(super::signatures::TypePredicate::type_id)
            .ok_or(SourceFlowUnsupported::Call(condition.call))?;
        let callee_type = store
            .type_node_links(plan.callee.node)
            .and_then(|links| links.resolved_type)
            .ok_or_else(invalid)?;
        let effects = resolve_source_call_effects_signature(store, plan, Some(callee_type))
            .map_err(|error| match error {
                super::source::SourceCheckError::Unsupported(_) => {
                    SourceFlowError::Unsupported(SourceFlowUnsupported::Call(condition.call))
                }
                _ => SourceFlowError::Invariant(invalid()),
            })?;
        if effects != EffectsSignatureState::Resolved(signature) {
            return Err(invalid().into());
        }
        let completed = CompletedClassPropertyPredicate {
            condition,
            source,
            member,
            access: self.access.clone(),
            flow: *self
                .flow
                .plan
                .points
                .get(&condition.access)
                .ok_or_else(invalid)?,
            edges,
            argument_type: store
                .type_node_links(condition.access)
                .and_then(|links| links.resolved_type)
                .ok_or_else(invalid)?,
            callee: plan.callee.node,
            callee_type,
            callee_read: *callee_read,
            signature,
            predicate,
            predicate_type,
            return_type: result,
            arrays: CanonicalArrayTargets::from_global_types(globals),
        };
        self.validate_predicate_condition(store, host, &completed)?;
        self.predicate_conditions
            .insert(condition.expression, completed);
        Ok(())
    }

    #[allow(clippy::too_many_lines)] // The call and field retain one shared source proof.
    fn validate_predicate_condition(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        completed: &CompletedClassPropertyPredicate,
    ) -> Result<(), SourceFlowError> {
        let condition = completed.condition;
        let invalid = || SourceFlowInvariant::InvalidCallEffect(condition.call);
        let unsupported =
            || SourceFlowError::Unsupported(SourceFlowUnsupported::Call(condition.call));
        let identities = class_body_identities(store, host, &self.access).map_err(|_| invalid())?;
        let receiver_symbol = store
            .type_payload(identities.this_type)
            .and_then(TypeRecord::symbol)
            .ok_or_else(invalid)?;
        let (source, edges) = validate_class_property_predicate_condition(
            store,
            host,
            self.flow.bound,
            self.body,
            condition,
        )?;
        let (arena, _) = host.source(condition.call).ok_or_else(invalid)?;
        let syntax =
            plan_direct_source_call_syntax(arena, store, condition.call).map_err(|_| invalid())?;
        let links = store.signature_links(condition.call).ok_or_else(invalid)?;
        if completed.access != self.access
            || self.flow.plan.conditions.get(&condition.expression)
                != Some(&SourceFlowCondition::ClassPropertyPredicate(condition))
            || source != completed.source
            || edges != completed.edges
            || class_member_source(store, host, source.member).map_err(|_| invalid())?
                != completed.member
            || completed.member.declaring_class != identities.class_symbol
            || completed.member.declaration != source.declaration
            || completed.member.side != ClassPropertySide::Instance
            || !matches!(completed.member.origin, ClassMemberOrigin::Field { .. })
            || self.flow.plan.points.get(&condition.access) != Some(&completed.flow)
            || self.flow.bound.flow_at(condition.access) != Some(completed.flow)
            || syntax.callee() != completed.callee
            || syntax.arguments() != [condition.access]
            || links.resolved_signature.signature() != Some(completed.signature)
            || links.effects_signature != EffectsSignatureState::Resolved(completed.signature)
            || store.type_node_links(condition.call)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(completed.return_type),
                    ..TypeNodeLinks::default()
                })
            || store.type_node_links(completed.callee)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(completed.callee_type),
                    ..TypeNodeLinks::default()
                })
            || own_class_flow_reference_symbol(store, host, self.flow.bound, completed.callee)
                .map_err(|_| invalid())?
                != Some(completed.callee_read.value_symbol)
            // Source checking publishes identifier links after it checks class bodies.
            || store
                .symbol_node_links(completed.callee)
                .and_then(|links| links.resolved_symbol)
                .is_some_and(|symbol| symbol != completed.callee_read.resolved_symbol)
            || store.type_node_links(condition.access)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(completed.argument_type),
                    ..TypeNodeLinks::default()
                })
            || store.symbol_node_links(condition.access)
                != Some(&SymbolNodeLinks {
                    resolved_symbol: Some(completed.member.symbol),
                })
            || store.type_node_links(source.context.receiver())
                != Some(&TypeNodeLinks {
                    resolved_type: Some(identities.this_type),
                    ..TypeNodeLinks::default()
                })
            || store.symbol_node_links(source.context.receiver())
                != Some(&SymbolNodeLinks {
                    resolved_symbol: Some(receiver_symbol),
                })
        {
            return Err(invalid().into());
        }
        let projection = match validate_stored_callable_set_with_array_targets(
            store,
            completed.callee_type,
            Some(completed.arrays),
        ) {
            StoredCallableSetValidation::Valid { projection, .. } => projection,
            StoredCallableSetValidation::Malformed { .. } => return Err(invalid().into()),
            _ => return Err(unsupported()),
        };
        let [callable] = projection.call_signatures.as_ref() else {
            return Err(unsupported());
        };
        let signature = store.signature(completed.signature).ok_or_else(invalid)?;
        let predicate = store
            .type_predicate(completed.predicate)
            .ok_or_else(invalid)?;
        let declaration = signature.declaration().ok_or_else(unsupported)?;
        let declaration_record = class_flow_source_node(store, host, declaration)?;
        let NodeData::FunctionDeclaration(function) = &declaration_record.data else {
            return Err(unsupported());
        };
        let annotation = function
            .type_
            .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
            .ok_or_else(unsupported)?;
        let annotation_record = class_flow_source_node(store, host, annotation)?;
        if !projection.construct_signatures.is_empty()
            || !signature.type_parameters().is_empty()
            || signature.parameters().len() != 1
            || signature.this_parameter().is_some()
            || signature.has_rest_parameter()
            || signature.target().is_some()
            || signature.mapper().is_some()
            || signature.composite().is_some()
            || predicate.kind() != TypePredicateKind::Identifier
            || predicate.parameter_index() != 0
            || annotation_record.kind != SyntaxKind::TypePredicate
        {
            return Err(unsupported());
        }
        if projection.owner != completed.callee_type
            || callable.signature != completed.signature
            || callable.return_type != Some(completed.return_type)
            || signature.resolved_return_type() != Some(completed.return_type)
            || signature.resolved_type_predicate() != Some(completed.predicate)
            || predicate.type_id() != Some(completed.predicate_type)
            || annotation_record.parent != Some(declaration.node)
            || store
                .signature_links(declaration)
                .and_then(|links| links.resolved_signature.signature())
                != Some(completed.signature)
            || store
                .intrinsic_bootstrap()
                .map(|bootstrap| bootstrap.boolean_type)
                != Some(completed.return_type)
        {
            return Err(invalid().into());
        }
        for type_ in [completed.argument_type, completed.predicate_type] {
            store
                .validate_union_constituent_with_array_targets(completed.arrays, type_)
                .map_err(|_| invalid())?;
            class_predicate_scalar_leaves(store, condition.call, type_)?;
        }
        Ok(())
    }

    /// An ordinary call keeps property facts only after its real signature is known.
    pub(super) fn complete_non_effecting_call(
        &mut self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        globals: &CanonicalGlobalTypes,
        plan: &SourceCallPlan,
        callee: TypeId,
        checked: &CheckedSourceCall,
    ) -> Result<(), SourceFlowError> {
        if !self.has_property_conditions() && !self.is_expression_condition_call(plan.node) {
            return Ok(());
        }
        let invalid = || SourceFlowInvariant::InvalidCallEffect(plan.node);
        let signature = store
            .signature_links(plan.node)
            .and_then(|links| links.resolved_signature.signature())
            .ok_or_else(invalid)?;
        let completed = CompletedClassOrdinaryCall {
            plan: plan.clone(),
            access: self.access.clone(),
            callee_type: callee,
            callee_symbol: store
                .symbol_node_links(plan.callee.node)
                .cloned()
                .ok_or_else(invalid)?,
            signature,
            return_type: checked.return_type,
            arrays: CanonicalArrayTargets::from_global_types(globals),
        };
        if self.ordinary_calls.contains_key(&plan.node) {
            return Err(invalid().into());
        }
        self.validate_non_effecting_call(store, host, &completed)?;
        self.ordinary_calls.insert(plan.node, completed);
        if self.is_expression_condition_call(plan.node) {
            self.flow.completed_expression_calls.insert(plan.node);
            self.flow.memo.clear();
        }
        Ok(())
    }

    fn validate_non_effecting_call(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        completed: &CompletedClassOrdinaryCall,
    ) -> Result<(), SourceFlowError> {
        let call = completed.plan.node;
        let invalid = || SourceFlowInvariant::InvalidCallEffect(call);
        let unsupported = || SourceFlowError::Unsupported(SourceFlowUnsupported::Call(call));
        let (arena, bound) = host.source(call).ok_or_else(invalid)?;
        class_body_identities(store, host, &self.access).map_err(|_| invalid())?;
        let expression_condition = self.is_expression_condition_call(call);
        let statement = if expression_condition {
            let proof = self
                .flow
                .plan
                .class_expression_conditions
                .get(&call)
                .ok_or_else(invalid)?;
            if validate_class_expression_condition(arena, bound, store, host, self.body, proof.source)?
                != SourceFlowCondition::Unchanged(call)
            {
                return Err(invalid().into());
            }
            proof.source.owner
        } else {
            validate_class_body_call(arena, bound, self.body, self.flow.plan.container, call)?
        };
        let syntax = plan_direct_source_call_syntax(arena, store, call).map_err(|_| invalid())?;
        let source = class_flow_source_node(store, host, call).map_err(|_| invalid())?;
        let NodeData::CallExpression(data) = &source.data else {
            return Err(invalid().into());
        };
        if data.type_arguments.is_some() {
            return Err(unsupported());
        }
        let signature_links = store.signature_links(call).ok_or_else(invalid)?;
        if completed.access != self.access
            || !expression_condition && self.flow.plan.calls.get(&call) != Some(&statement)
            || syntax.callee() != completed.plan.callee.node
            || !syntax.arguments().iter().copied().eq(completed
                .plan
                .arguments
                .iter()
                .map(|argument| argument.node))
            || signature_links.resolved_signature.signature() != Some(completed.signature)
            || signature_links.effects_signature != EffectsSignatureState::Unresolved
            || store.symbol_node_links(completed.plan.callee.node) != Some(&completed.callee_symbol)
            || store.type_node_links(call)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(completed.return_type),
                    ..TypeNodeLinks::default()
                })
            || store.type_node_links(completed.plan.callee.node)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(completed.callee_type),
                    ..TypeNodeLinks::default()
                })
        {
            return Err(invalid().into());
        }
        if let super::source::PlannedExpressionKind::Identifier(read) = &completed.plan.callee.kind
            && completed.callee_symbol.resolved_symbol != Some(read.resolved_symbol)
        {
            return Err(invalid().into());
        }
        let projection = match validate_stored_callable_set_with_array_targets(
            store,
            completed.callee_type,
            Some(completed.arrays),
        ) {
            StoredCallableSetValidation::Valid { projection, .. } => projection,
            StoredCallableSetValidation::Malformed { .. } => return Err(invalid().into()),
            StoredCallableSetValidation::NotCallable
            | StoredCallableSetValidation::Pending { .. } => {
                return Err(unsupported());
            }
        };
        if projection.owner != completed.callee_type
            || !projection.construct_signatures.is_empty()
            || !projection.call_signatures.iter().any(|callable| {
                callable.signature == completed.signature
                    && callable.return_type == Some(completed.return_type)
            })
        {
            return Err(invalid().into());
        }
        // A missing predicate cache alone is not a proof of an ordinary call.
        // Each visible signature must retain an explicit non-predicate return.
        for callable in &projection.call_signatures {
            let signature = store.signature(callable.signature).ok_or_else(invalid)?;
            let declaration = signature.declaration().ok_or_else(unsupported)?;
            let node = class_flow_source_node(store, host, declaration).map_err(|_| invalid())?;
            let annotation = match &node.data {
                NodeData::FunctionDeclaration(function) => function.type_,
                NodeData::MethodDeclaration(method) => method.type_,
                NodeData::MethodSignatureDeclaration(method) => method.type_,
                NodeData::FunctionTypeNode(function) => function.type_,
                NodeData::CallSignatureDeclaration(signature) => signature.type_,
                _ => return Err(unsupported()),
            }
            .ok_or_else(unsupported)?;
            let annotation = NodeRef::new(declaration.arena, declaration.file, annotation);
            let annotation =
                class_flow_source_node(store, host, annotation).map_err(|_| invalid())?;
            let return_type = signature.resolved_return_type().ok_or_else(unsupported)?;
            let returned = store.type_payload(return_type).ok_or_else(invalid)?;
            if annotation.parent != Some(declaration.node)
                || store
                    .signature_links(declaration)
                    .and_then(|links| links.resolved_signature.signature())
                    != Some(callable.signature)
                || callable.return_type != Some(return_type)
            {
                return Err(invalid().into());
            }
            if annotation.kind == SyntaxKind::TypePredicate
                || signature.resolved_type_predicate().is_some()
                || returned.flags().intersects(TypeFlags::NEVER)
                || !signature.type_parameters().is_empty()
                || signature.target().is_some()
                || signature.mapper().is_some()
                || signature.composite().is_some()
            {
                return Err(unsupported());
            }
            store
                .validate_union_constituent_with_array_targets(completed.arrays, return_type)
                .map_err(|_| invalid())?;
        }
        Ok(())
    }

    /// A deferred capture keeps narrowing only after its last enclosing write.
    pub(super) fn captured_variables_with_later_writes(
        &self,
        host: &DeclaredTypeHost<'_>,
        location: NodeRef,
    ) -> Result<HashSet<SemanticSymbolId>, SourceFlowError> {
        host.node(location)
            .ok_or(SourceFlowInvariant::InvalidClassBody(self.body.declaration))?;
        self.flow
            .plan
            .captured_variables_with_later_writes(host, location)
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
        if !matches!(
            self.body.kind,
            ClassBodyKind::Constructor | ClassBodyKind::Method { .. }
        ) || identities.class_symbol != self.body.class_symbol
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
            || !assignment.source_is_exact(store, host, false)
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
        if context.is_deferred()
            || !matches!(self.body.kind, ClassBodyKind::Constructor)
            || identities.base.is_none()
        {
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
            | SourceFlowKind::ArrayMutation
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
    #[allow(dead_code)] // Keep the caller-free entry for existing private source checks.
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
        self.property_read_worker(
            store,
            host,
            context,
            access,
            member,
            declared_type,
            options,
            None,
            None,
        )
    }

    pub(super) fn property_read_with_session(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        globals: Option<&CanonicalGlobalTypes>,
        context: &ClassAccessContext,
        access: NodeRef,
        member: &ClassMemberSource,
        declared_type: TypeId,
        options: CanonicalCheckerOptions,
        session: &mut InstantiationSession,
    ) -> Result<ClassPropertyFlowRead, SourceFlowError> {
        self.property_read_worker(
            store,
            host,
            context,
            access,
            member,
            declared_type,
            options,
            globals,
            Some(session),
        )
    }

    fn property_read_worker(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        context: &ClassAccessContext,
        access: NodeRef,
        member: &ClassMemberSource,
        declared_type: TypeId,
        options: CanonicalCheckerOptions,
        globals: Option<&CanonicalGlobalTypes>,
        session: Option<&mut InstantiationSession>,
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
            &mut ClassPropertyFlowTypes::Read {
                store,
                globals,
                session,
            },
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
            &mut ClassPropertyFlowTypes::Initialization(store),
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
        types: &mut ClassPropertyFlowTypes<'_>,
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
            SourceFlowKind::Assignment | SourceFlowKind::ArrayMutation => {
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
                            || !checked.source_is_exact(types.store(), host, true)
                            || types.store().type_payload(checked.flow_type()).is_none()
                        {
                            return Err(SourceFlowInvariant::InvalidClassProperty(target).into());
                        }
                        Ok(ClassPropertyFlowState {
                            type_: query.initial.type_.map(|_| checked.flow_type()),
                            initialized: true,
                        })
                    } else {
                        if types
                            .store()
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
                        types,
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
                let is_super = if let Some(NodeData::CallExpression(data)) =
                    host.node(call).map(|node| &node.data)
                {
                    host.node(NodeRef::new(call.arena, call.file, data.expression))
                        .is_some_and(|node| node.kind == SyntaxKind::SuperKeyword)
                } else {
                    return Err(SourceFlowInvariant::InvalidCall(call).into());
                };
                if is_super && !self.completed_calls.contains(&call) {
                    return Err(SourceFlowInvariant::InvalidCall(call).into());
                }
                if !is_super && self.has_property_conditions() {
                    let completed = self
                        .ordinary_calls
                        .get(&call)
                        .ok_or(SourceFlowInvariant::InvalidCallEffect(call))?;
                    self.validate_non_effecting_call(types.store(), host, completed)?;
                }
                self.property_state_at(
                    types,
                    host,
                    linear_antecedent(flow, &node)?,
                    query,
                    visiting,
                    depth + 1,
                )
            }
            kind @ (SourceFlowKind::BranchLabel | SourceFlowKind::LoopLabel) => {
                let mut result: Option<ClassPropertyFlowState> = None;
                let mut branch_types = Vec::new();
                let can_join =
                    self.has_property_conditions() && kind == SourceFlowKind::BranchLabel;
                for antecedent in label_antecedents(flow, &node)? {
                    let state = self.property_state_at(
                        types,
                        host,
                        *antecedent,
                        query,
                        visiting,
                        depth + 1,
                    )?;
                    branch_types.extend(state.type_);
                    if let Some(prior) = &mut result {
                        if prior.type_ != state.type_ && !can_join {
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
                if can_join
                    && let Some(state) = &mut result
                    && let Some(declared) = query.initial.type_
                {
                    state.type_ = Some(types.join(flow, node.flags, &branch_types, declared)?);
                }
                Ok(result.unwrap_or(ClassPropertyFlowState {
                    initialized: true,
                    ..query.initial
                }))
            }
            kind @ (SourceFlowKind::TrueCondition | SourceFlowKind::FalseCondition) => {
                let expression = ast_payload(flow, &node)?;
                let condition = self
                    .flow
                    .plan
                    .conditions
                    .get(&expression)
                    .ok_or(SourceFlowInvariant::UnknownCondition(expression))?;
                if !matches!(
                    condition,
                    SourceFlowCondition::Truthiness(_)
                        | SourceFlowCondition::ClassPropertyTruthiness(_)
                        | SourceFlowCondition::ClassPropertyEquality(_)
                        | SourceFlowCondition::ClassPropertyPredicate(_)
                ) && !self
                    .flow
                    .plan
                    .class_expression_conditions
                    .get(&expression)
                    .is_some_and(|proof| {
                        matches!(proof.source.kind, SourceClassExpressionConditionKind::Nullish(_))
                            || proof.source.kind == SourceClassExpressionConditionKind::Call
                                && self.flow.completed_expression_calls.contains(&expression)
                    })
                {
                    return Err(SourceFlowUnsupported::FlowKind {
                        flow,
                        flags: node.flags,
                    }
                    .into());
                }
                if self.is_expression_condition_call(expression) {
                    let completed = self
                        .ordinary_calls
                        .get(&expression)
                        .ok_or(SourceFlowInvariant::UnreachedCondition(expression))?;
                    self.validate_non_effecting_call(types.store(), host, completed)?;
                }
                let mut state = self.property_state_at(
                    types,
                    host,
                    linear_antecedent(flow, &node)?,
                    query,
                    visiting,
                    depth + 1,
                )?;
                if !matches!(condition, SourceFlowCondition::ClassPropertyPredicate(_))
                    && let Some(access) = condition.class_property_access()
                {
                    let completed = self
                        .property_conditions
                        .get(&expression)
                        .ok_or(SourceFlowInvariant::UnreachedCondition(expression))?;
                    self.validate_property_condition(types.store(), host, completed)?;
                    let edge = usize::from(kind == SourceFlowKind::FalseCondition);
                    if completed.edges[edge] != flow {
                        return Err(
                            SourceFlowInvariant::InvalidClassProperty(access).into()
                        );
                    }
                    let reference = ClassPropertyFlowReference {
                        receiver: ClassPropertyFlowReceiver::This(
                            completed.source.context.class_declaration(),
                        ),
                        name: completed.source.name().to_owned(),
                    };
                    if query.reference == &reference
                        && query.member == &completed.member
                        && let Some(current) = state.type_
                    {
                        if current != completed.type_ {
                            return Err(SourceFlowInvariant::InvalidClassProperty(access).into());
                        }
                        state.type_ = Some(match condition {
                            SourceFlowCondition::ClassPropertyTruthiness(condition) => {
                                let truthy =
                                    (kind == SourceFlowKind::TrueCondition) != condition.negated;
                                types.narrow(
                                    flow,
                                    node.flags,
                                    expression,
                                    current,
                                    if truthy {
                                        TruthinessAssumption::Truthy
                                    } else {
                                        TruthinessAssumption::Falsy
                                    },
                                )?
                            }
                            SourceFlowCondition::ClassPropertyEquality(condition) => {
                                let value = types
                                    .store()
                                    .type_node_links(condition.value)
                                    .and_then(|links| links.resolved_type)
                                    .ok_or(SourceFlowInvariant::InvalidClassProperty(access))?;
                                types.narrow_equality(
                                    flow,
                                    node.flags,
                                    current,
                                    value,
                                    (kind == SourceFlowKind::TrueCondition)
                                        == matches!(
                                            condition.comparison,
                                            SourceTypeofComparison::Equal
                                        ),
                                )?
                            }
                            _ => unreachable!("the condition has a class property access"),
                        });
                    }
                }
                if let SourceFlowCondition::ClassPropertyPredicate(condition) = condition {
                    let completed = self
                        .predicate_conditions
                        .get(&expression)
                        .ok_or(SourceFlowInvariant::UnreachedCondition(expression))?;
                    self.validate_predicate_condition(types.store(), host, completed)?;
                    let edge = usize::from(kind == SourceFlowKind::FalseCondition);
                    if completed.edges[edge] != flow {
                        return Err(SourceFlowInvariant::InvalidCallEffect(condition.call).into());
                    }
                    let reference = ClassPropertyFlowReference {
                        receiver: ClassPropertyFlowReceiver::This(
                            completed.source.context.class_declaration(),
                        ),
                        name: completed.source.name().to_owned(),
                    };
                    if query.reference == &reference
                        && query.member == &completed.member
                        && let Some(current) = state.type_
                    {
                        if current != completed.argument_type {
                            return Err(SourceFlowInvariant::InvalidClassProperty(condition.access)
                                .into());
                        }
                        state.type_ = Some(types.narrow_predicate(
                            flow,
                            node.flags,
                            condition.call,
                            current,
                            completed.predicate_type,
                            (kind == SourceFlowKind::TrueCondition) != condition.negated,
                        )?);
                    }
                }
                Ok(state)
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
    pub(super) fn contains_call(&self, call: NodeRef) -> bool {
        self.plan.contains_call(call)
    }

    pub(super) fn enter_catch_binding(
        &mut self,
        store: &CanonicalTypeMapperStore,
        binding: &SourceCallableCatchBindingSyntax,
        declared_type: TypeId,
    ) -> Result<SourceCatchFlowScope, SourceFlowError> {
        let invalid = || SourceFlowInvariant::InvalidParameterAssignment(binding.declaration);
        let syntax = self.plan.statement_list.as_ref().ok_or_else(invalid)?;
        if !syntax.catch_bindings().contains(&binding)
            || self.bound.symbol(binding.declaration) != Some(binding.symbol)
            || self.bound.container(binding.declaration) != Some(self.plan.container)
            || self.bound.block_scope_container(binding.declaration) != Some(binding.clause)
            || !self.plan.points.contains_key(&binding.clause)
            || !self.plan.points.contains_key(&binding.name)
            || (self.plan.assignments.contains_key(&binding.declaration)
                != binding.initializer.is_some())
            || store.type_payload(declared_type).is_none()
            || self.base.type_of(binding.symbol).is_some()
            || self.declared_types.contains_key(&binding.symbol)
        {
            return Err(invalid().into());
        }
        let scope = SourceCatchFlowScope {
            symbol: binding.symbol,
            base: self.base.type_of(binding.symbol),
            declared: self.declared_types.insert(binding.symbol, declared_type),
        };
        self.base = self.base.with_type(binding.symbol, declared_type);
        self.memo.clear();
        Ok(scope)
    }

    #[allow(clippy::needless_pass_by_value)] // Consume the token to prevent a second restore.
    pub(super) fn restore_catch_binding(&mut self, scope: SourceCatchFlowScope) {
        let types = Arc::make_mut(&mut self.base.types);
        match scope.base {
            Some(type_) => {
                types.insert(scope.symbol, type_);
            }
            None => {
                types.remove(&scope.symbol);
            }
        }
        match scope.declared {
            Some(type_) => {
                self.declared_types.insert(scope.symbol, type_);
            }
            None => {
                self.declared_types.remove(&scope.symbol);
            }
        }
        self.memo.clear();
    }

    fn catch_symbol_is_inactive(&self, symbol: SemanticSymbolId) -> bool {
        !self.declared_types.contains_key(&symbol)
            && self.plan.statement_list.as_ref().is_some_and(|syntax| {
                syntax
                    .catch_bindings()
                    .iter()
                    .any(|binding| binding.symbol == symbol)
            })
    }

    fn uses_callable_loop_queries(&self) -> bool {
        self.plan
            .statement_list
            .as_ref()
            .is_some_and(|syntax| syntax.contains_for_of() || syntax.contains_counted_for())
    }

    fn callable_for_of_symbol_is_visible(
        &self,
        store: &CanonicalTypeMapperStore,
        point: NodeRef,
        symbol: SemanticSymbolId,
    ) -> Result<bool, SourceFlowError> {
        let record = store
            .symbol(symbol)
            .ok_or(SourceFlowInvariant::MissingCurrentType(symbol))?;
        let Some(declaration) = record.value_declaration() else {
            return Ok(true);
        };
        if !record.flags().intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE)
            || self.bound.container(declaration) != Some(self.plan.container)
        {
            return Ok(true);
        }
        let expected = self
            .bound
            .block_scope_container(declaration)
            .ok_or(SourceFlowInvariant::InvalidParameterAssignment(declaration))?;
        let mut scope = self.bound.block_scope_container(point);
        let mut seen = HashSet::new();
        while let Some(current) = scope {
            if current == expected {
                return Ok(true);
            }
            if current == self.plan.container {
                return Ok(false);
            }
            if !seen.insert(current) {
                return Err(SourceFlowInvariant::InvalidParameterAssignment(declaration).into());
            }
            scope = self.bound.block_scope_container(current);
        }
        Err(SourceFlowInvariant::InvalidParameterAssignment(declaration).into())
    }

    /// Query existing visible entries separately so unrelated pending loop locals are not demands.
    fn snapshot_callable_for_of_at(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        point: NodeRef,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        let mut symbols = self.base.types().keys().copied().collect::<Vec<_>>();
        for (declaration, state) in &self.assignment_states {
            if matches!(state, SourceFlowAssignmentState::Resolved(_)) {
                symbols.push(
                    self.plan
                        .assignments
                        .get(declaration)
                        .ok_or(SourceFlowInvariant::UnknownAssignment(*declaration))?
                        .symbol,
                );
            }
        }
        symbols.sort_unstable();
        symbols.dedup();
        let mut visible = Vec::with_capacity(symbols.len());
        for symbol in symbols {
            if self.callable_for_of_symbol_is_visible(store, point, symbol)? {
                visible.push(symbol);
            }
        }
        let snapshot = self.snapshot_for_symbols_at(store, globals, point, visible.iter().copied())?;
        let types = snapshot
            .types()
            .iter()
            .filter(|(symbol, _)| visible.binary_search(symbol).is_ok())
            .map(|(&symbol, &type_)| (symbol, type_))
            .collect();
        Ok(SourceFlowSnapshot {
            types: Arc::new(types),
            ..snapshot
        })
    }

    /// Keeps a local's declared type and initial flow type without an assignment node.
    pub(super) fn enter_uninitialized_local(
        &mut self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        declaration: NodeRef,
        symbol: SemanticSymbolId,
        declared_type: TypeId,
        initial_type: TypeId,
    ) -> Result<(), SourceFlowError> {
        let invalid = || SourceFlowInvariant::InvalidParameterAssignment(declaration);
        let (arena, _) = host.source(declaration).ok_or_else(invalid)?;
        let (name, _) = annotated_uninitialized_local(
            arena,
            self.bound,
            store,
            self.plan.container,
            declaration,
            symbol,
        )?;
        if self.plan.region.is_some()
            || self.plan.class_body.is_some()
            || !self.plan.points.contains_key(&name)
            || self.plan.assignments.contains_key(&declaration)
            || store.type_payload(declared_type).is_none()
            || store.type_payload(initial_type).is_none()
            || self.declared_types.contains_key(&symbol)
            || self.base.type_of(symbol).is_some()
        {
            return Err(invalid().into());
        }
        self.declared_types.insert(symbol, declared_type);
        self.base = self.base.with_type(symbol, initial_type);
        self.memo.clear();
        Ok(())
    }

    pub(super) fn set_source_declared_entry_types(
        &mut self,
        store: &CanonicalTypeMapperStore,
        types: &SourceFlowTypes,
    ) -> Result<(), SourceFlowError> {
        if self.plan.region.is_none() {
            return Err(SourceFlowInvariant::InvalidSourceRegion(self.plan.container).into());
        }
        for (&symbol, &type_) in types {
            if self.base.type_of(symbol).is_some() {
                if store.symbol(symbol).is_none() || store.type_payload(type_).is_none() {
                    return Err(SourceFlowInvariant::MissingCurrentType(symbol).into());
                }
                self.declared_types.insert(symbol, type_);
            }
        }
        Ok(())
    }

    pub(super) fn complete_condition_value(
        &mut self,
        node: NodeRef,
        type_: TypeId,
    ) -> Result<(), SourceFlowError> {
        if !self.plan.conditions.values().any(|condition| {
            matches!(condition, SourceFlowCondition::Equality(condition) if condition.value == node)
        }) || self.condition_values.insert(node, type_).is_some() {
            return Err(SourceFlowInvariant::UnknownCondition(node).into());
        }
        if self.uses_callable_loop_queries() {
            self.memo.clear();
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)] // Keep the binder proof and the source caller together.
    pub(super) fn complete_in_condition(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        globals: &CanonicalGlobalTypes,
        session: &mut InstantiationSession,
        condition: SourceInCondition,
        input: TypeId,
    ) -> Result<(), SourceFlowError> {
        let invalid = || SourceFlowInvariant::UnknownCondition(condition.expression);
        let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
        let instanceof = match self.plan.conditions.get(&condition.expression) {
            Some(SourceFlowCondition::In(actual)) if *actual == condition => false,
            Some(SourceFlowCondition::InstanceOf(actual)) if *actual == condition => true,
            _ => return Err(invalid().into()),
        };
        if self.in_conditions.contains_key(&condition.expression)
            || store.type_node_links(condition.expression)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(bootstrap.boolean_type),
                    ..TypeNodeLinks::default()
                })
            || store
                .type_node_links(condition.receiver)
                .and_then(|links| links.resolved_type)
                != Some(input)
            || own_class_flow_reference_symbol(store, host, self.bound, condition.receiver)?
                != Some(condition.symbol)
        {
            return Err(invalid().into());
        }
        let key = store
            .type_node_links(condition.key)
            .and_then(|links| links.resolved_type)
            .ok_or_else(invalid)?;
        let [when_true, when_false] = if instanceof {
            narrow_source_instanceof_type(
                store, host, globals, session, condition.expression, input, key,
            )?
        } else {
            narrow_source_in_type(store, globals, session, condition.expression, input, key)?
        };
        self.in_conditions.insert(
            condition.expression,
            CompletedInCondition {
                input,
                key,
                when_true,
                when_false,
            },
        );
        self.memo.clear();
        Ok(())
    }

    pub(super) fn complete_source_declaration(
        &mut self,
        host: &DeclaredTypeHost<'_>,
        declaration: NodeRef,
        symbol: SemanticSymbolId,
        declared_type: TypeId,
        current_type: TypeId,
    ) -> Result<(), SourceFlowError> {
        if self.plan.region.is_none()
            || self.bound.symbol(declaration) != Some(symbol)
            || self.bound.container(declaration) != Some(self.plan.container)
        {
            return Err(SourceFlowInvariant::InvalidParameterAssignment(declaration).into());
        }
        let record = host
            .node(declaration)
            .ok_or(SourceFlowInvariant::UnknownAssignment(declaration))?;
        let NodeData::VariableDeclaration(variable) = &record.data else {
            return Err(SourceFlowInvariant::UnknownAssignment(declaration).into());
        };
        if self.declared_types.insert(symbol, declared_type).is_some() {
            return Err(SourceFlowInvariant::AssignmentAlreadyCompleted(declaration).into());
        }
        if self.plan.assignments.contains_key(&declaration) {
            self.complete_assignment(declaration, symbol, current_type)?;
        } else if variable.initializer.is_none() {
            self.base = self.base.with_type(symbol, current_type);
        } else {
            let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
            if self.plan.points.get(&name).copied() != Some(self.graph.nodes().unreachable()) {
                return Err(SourceFlowInvariant::UnknownAssignment(declaration).into());
            }
        }
        self.memo.clear();
        Ok(())
    }

    /// Queries only the requested references. Unrelated pending writes are not demands.
    pub(super) fn snapshot_for_symbols_at(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        node: NodeRef,
        symbols: impl IntoIterator<Item = SemanticSymbolId>,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        let flow = *self
            .plan
            .points
            .get(&node)
            .ok_or(SourceFlowInvariant::MissingFlowPoint(node))?;
        self.snapshot_for_symbols(store, globals, flow, symbols)
    }

    pub(super) fn snapshot_for_symbols_at_end(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        symbols: impl IntoIterator<Item = SemanticSymbolId>,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        let flow = self
            .plan
            .end
            .ok_or(SourceFlowInvariant::MissingFlowPoint(self.plan.container))?;
        self.snapshot_for_symbols(store, globals, flow, symbols)
    }

    fn snapshot_for_symbols(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        flow: FlowRef,
        symbols: impl IntoIterator<Item = SemanticSymbolId>,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        let mut result = self.base.clone();
        for symbol in symbols {
            let previous = self.reference.replace(symbol);
            let snapshot = self.resolve_flow(store, globals, flow, 0);
            self.reference = previous;
            let snapshot = snapshot?;
            if snapshot.incomplete {
                return Err(SourceFlowInvariant::Cycle(flow).into());
            }
            let type_ = (if snapshot.reachable {
                snapshot.type_of(symbol)
            } else {
                self.declared_types
                    .get(&symbol)
                    .copied()
                    .or_else(|| snapshot.type_of(symbol))
            })
            .ok_or(SourceFlowInvariant::MissingCurrentType(symbol))?;
            result = result.with_type(
                symbol,
                Self::finalize_flow_type(store, globals, flow, type_)?,
            );
            result.reachable &= snapshot.reachable;
        }
        Ok(result)
    }

    /// Effects signatures are resolved without publishing a provisional argument type.
    pub(super) fn complete_call_effect(
        &mut self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        call: NodeRef,
        effect: SourceFlowCallEffect,
    ) -> Result<(), SourceFlowError> {
        if !self.plan.calls.contains_key(&call) || self.call_effects.contains_key(&call) {
            return Err(SourceFlowInvariant::InvalidCallEffect(call).into());
        }
        validate_source_call_effect(store, host, self.bound, call, effect)?;
        self.call_effects.insert(call, effect);
        if self.plan.nullish_calls.contains_key(&call) {
            self.memo.clear();
        }
        Ok(())
    }

    fn query_base(&self) -> SourceFlowSnapshot {
        match self.reference {
            Some(symbol) => SourceFlowSnapshot::new(
                self.base
                    .type_of(symbol)
                    .map(|type_| (symbol, type_))
                    .into_iter()
                    .collect(),
            ),
            None => self.base.clone(),
        }
    }

    /// Returns the immutable current-type map at one cold-preflighted AST
    /// point, memoizing completed flow nodes for the rest of this invocation.
    pub(super) fn snapshot_at(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        node: NodeRef,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        if self.uses_callable_loop_queries() {
            return self.snapshot_callable_for_of_at(store, globals, node);
        }
        let flow = self
            .plan
            .points
            .get(&node)
            .copied()
            .ok_or(SourceFlowInvariant::MissingFlowPoint(node))?;
        let snapshot = self.resolve_flow(store, globals, flow, 0)?;
        let mut finalized = None;
        for (&symbol, &type_) in snapshot.types() {
            let value = Self::finalize_flow_type(store, globals, flow, type_)?;
            if value != type_ {
                finalized
                    .get_or_insert_with(|| snapshot.types().clone())
                    .insert(symbol, value);
            }
        }
        Ok(finalized.map_or(snapshot, SourceFlowSnapshot::new))
    }

    pub(super) fn raw_type_at(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        node: NodeRef,
        symbol: SemanticSymbolId,
    ) -> Result<TypeId, SourceFlowError> {
        let flow = *self
            .plan
            .points
            .get(&node)
            .ok_or(SourceFlowInvariant::MissingFlowPoint(node))?;
        self.resolve_flow(store, globals, flow, 0)?
            .type_of(symbol)
            .ok_or_else(|| SourceFlowInvariant::MissingCurrentType(symbol).into())
    }

    fn finalize_flow_type(
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        flow: FlowRef,
        type_: TypeId,
    ) -> Result<TypeId, SourceFlowError> {
        if !store.type_payload(type_).is_some_and(|record| {
            record
                .object_flags()
                .intersects(ObjectFlags::EVOLVING_ARRAY)
        }) {
            return Ok(type_);
        }
        let element = store.evolving_array_element_type(type_)?;
        let array = if let Some(TypeData::Union(union)) =
            store.type_payload(element).map(TypeRecord::data)
        {
            let elements = union.union.types.clone();
            let reduced = store
                .expression_union_type_with_global_types(
                    globals,
                    &elements,
                    UnionReduction::Subtype,
                )
                .map_err(|error| SourceFlowError::Join { flow, error })?;
            store.create_evolving_array_type(reduced)?
        } else {
            type_
        };
        Ok(store.finalize_evolving_array_type(globals, array)?)
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
                if self.plan.nullish_assignments.contains_key(&declaration) {
                    self.memo.clear();
                }
                if self.uses_callable_loop_queries() {
                    self.memo.clear();
                }
                Ok(())
            }
            SourceFlowAssignmentState::Resolved(_)
            | SourceFlowAssignmentState::Update
            | SourceFlowAssignmentState::ReadonlyUpdate => {
                Err(SourceFlowInvariant::AssignmentAlreadyCompleted(declaration).into())
            }
        }
    }

    /// Updates use the retained antecedent type. Completion proves that the header was checked.
    pub(super) fn complete_callable_update(
        &mut self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        expression: NodeRef,
        update: SourceFlowUpdate,
    ) -> Result<(), SourceFlowError> {
        let invalid = || SourceFlowInvariant::InvalidUpdate(update.target);
        let syntax = self.plan.statement_list.as_ref().ok_or_else(invalid)?;
        let (arena, _) = host.source(self.plan.container).ok_or_else(invalid)?;
        if validate_callable_update(arena, self.bound, store, host, syntax, update)? != expression
            || self.plan.updates.get(&update.target) != Some(&update)
            || self.plan.assignment_declarations.get(&update.target) != Some(&update.declaration)
            || !matches!(
                self.assignment_states.get(&update.target),
                Some(SourceFlowAssignmentState::Update)
            )
            || [expression, update.target].into_iter().any(|node| {
                store
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type)
                    .is_none()
            })
        {
            return Err(invalid().into());
        }
        if !self.completed_callable_updates.insert(update.target) {
            return Err(SourceFlowInvariant::AssignmentAlreadyCompleted(update.target).into());
        }
        Ok(())
    }

    pub(super) fn finish_callable_updates(&self) -> Result<(), SourceFlowError> {
        for target in self.plan.updates.keys() {
            if !self.completed_callable_updates.contains(target) {
                return Err(SourceFlowInvariant::InvalidUpdate(*target).into());
            }
        }
        Ok(())
    }

    /// Compound writes widen the real antecedent, not the checked result type.
    pub(super) fn complete_compound_assignment(
        &mut self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        assignment: SourceFlowParameterAssignment,
        expression: NodeRef,
        operator: SyntaxKind,
    ) -> Result<(), SourceFlowError> {
        let invalid = || SourceFlowInvariant::InvalidParameterAssignment(assignment.target);
        let syntax = self.plan.statement_list.as_ref().ok_or_else(invalid)?;
        let (arena, _) = host.source(self.plan.container).ok_or_else(invalid)?;
        if !expression.is_for(arena.id(), self.bound.file_id()) || !self.bound.contains(expression)
        {
            return Err(invalid().into());
        }
        validate_statement_list_source(arena, self.bound, store, host, syntax)?;
        validate_parameter_assignment_in_list(
            arena,
            self.bound,
            store,
            Some(host),
            self.plan.container,
            assignment,
            Some(syntax),
        )?;
        let planned = self
            .plan
            .assignments
            .get(&assignment.target)
            .ok_or_else(invalid)?;
        let record = host.node(expression).ok_or_else(invalid)?;
        let NodeData::BinaryExpression(binary) = &record.data else {
            return Err(invalid().into());
        };
        let right = NodeRef::new(expression.arena, expression.file, binary.right);
        if planned.declaration != assignment.target
            || planned.symbol != assignment.symbol
            || self.plan.assignment_declarations.get(&assignment.target)
                != Some(&assignment.parameter)
            || host.node(assignment.target).and_then(|node| node.parent) != Some(expression.node)
            || arena.get(binary.operator_token).map(|node| node.kind) != Some(operator)
            || super::primitive_operators::compound_assignment_binary_operator(operator).is_none()
            || host.node(right).and_then(|node| node.parent) != Some(expression.node)
            || [assignment.target, right, expression]
                .into_iter()
                .any(|node| {
                    store
                        .type_node_links(node)
                        .and_then(|links| links.resolved_type)
                        .is_none()
                })
        {
            return Err(invalid().into());
        }
        let state = self
            .assignment_states
            .get_mut(&assignment.target)
            .ok_or_else(invalid)?;
        if !matches!(state, SourceFlowAssignmentState::Pending) {
            return Err(SourceFlowInvariant::AssignmentAlreadyCompleted(assignment.target).into());
        }
        *state = SourceFlowAssignmentState::Update;
        self.memo.clear();
        Ok(())
    }

    fn resolve_flow(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        flow: FlowRef,
        depth: usize,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        let key = (flow, self.reference);
        if self.plan.region.is_some_and(|region| region.entry == flow) {
            let mut snapshot = self.query_base();
            if flow == self.graph.nodes().unreachable() {
                snapshot.reachable = false;
            }
            return Ok(snapshot);
        }
        if let Some(snapshot) = self.loop_snapshots.get(&key) {
            let mut snapshot = snapshot.clone();
            snapshot.incomplete = true;
            return Ok(snapshot);
        }
        if let Some(snapshot) = self.memo.get(&key) {
            return Ok(snapshot.clone());
        }
        if depth > FLOW_DEPTH_LIMIT {
            return Err(SourceFlowInvariant::DepthLimit(flow).into());
        }
        if !self.visiting.insert(key) {
            return Err(SourceFlowInvariant::Cycle(flow).into());
        }
        let result = self.resolve_flow_uncached(store, globals, flow, depth);
        let removed = self.visiting.remove(&key);
        debug_assert!(removed);
        if let Ok(snapshot) = &result
            && self.loop_snapshots.is_empty()
            && !snapshot.incomplete
        {
            self.memo.insert(key, snapshot.clone());
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
                if self.plan.region.is_none() {
                    return Ok(self.base.clone());
                }
                let mut snapshot = match self.reference {
                    Some(symbol) => SourceFlowSnapshot::new(
                        self.declared_types
                            .get(&symbol)
                            .copied()
                            .map(|type_| (symbol, type_))
                            .into_iter()
                            .collect(),
                    ),
                    None => self.base.clone(),
                };
                snapshot.reachable = false;
                Ok(snapshot)
            }
            SourceFlowKind::Start => {
                validate_start_node(self.plan, flow, &node)?;
                Ok(self.query_base())
            }
            SourceFlowKind::Assignment | SourceFlowKind::ArrayMutation => {
                let antecedent = linear_antecedent(flow, &node)?;
                let declaration = ast_payload(flow, &node)?;
                if let Some(proof) = self.plan.member_assignments.get(&declaration).copied() {
                    let prior = self.resolve_flow(store, globals, antecedent, depth + 1)?;
                    if !prior.reachable
                        || self.reference.is_some_and(|symbol| symbol != proof.receiver_symbol)
                    {
                        return Ok(prior);
                    }
                    let declared = self
                        .declared_types
                        .get(&proof.receiver_symbol)
                        .copied()
                        .ok_or(SourceFlowInvariant::MissingCurrentType(proof.receiver_symbol))?;
                    return Ok(prior.with_type(proof.receiver_symbol, declared));
                }
                if let Some(proof) = self.plan.nullish_assignments.get(&declaration).copied()
                    && proof.assignment.symbol.is_none()
                {
                    let prior = self.resolve_flow(store, globals, antecedent, depth + 1)?;
                    if proof.assignment.readonly || !prior.reachable {
                        return Ok(prior);
                    }
                    let Some(receiver) = proof.receiver else {
                        return Ok(prior);
                    };
                    if self.reference.is_some_and(|symbol| symbol != receiver) {
                        return Ok(prior);
                    }
                    let declared = self
                        .declared_types
                        .get(&receiver)
                        .copied()
                        .ok_or(SourceFlowInvariant::MissingCurrentType(receiver))?;
                    // A real member write invalidates receiver refinements only on its branch.
                    return Ok(prior.with_type(receiver, declared));
                }
                if self.plan.property_assignments.contains_key(&declaration) {
                    return self.resolve_flow(store, globals, antecedent, depth + 1);
                }
                let assignment = *self
                    .plan
                    .assignments
                    .get(&declaration)
                    .ok_or(SourceFlowInvariant::UnknownAssignment(declaration))?;
                if self.uses_callable_loop_queries()
                    && self.reference == Some(assignment.symbol)
                    && source_flow_kind(flow, node.flags)? == SourceFlowKind::Assignment
                    && let Some(SourceFlowAssignmentState::Resolved(current_type)) =
                        self.assignment_states.get(&declaration)
                {
                    // This source path rejects unreachable statements and effect-changing calls.
                    // A checked simple assignment already has its assignment-reduced current type.
                    if source_flow_kind(antecedent, flow_node(self.graph, antecedent)?.flags)?
                        == SourceFlowKind::Unreachable
                    {
                        return Err(
                            SourceFlowInvariant::InvalidParameterAssignment(declaration).into()
                        );
                    }
                    return Ok(self.query_base().with_type(assignment.symbol, *current_type));
                }
                let prior = self.resolve_flow(store, globals, antecedent, depth + 1)?;
                if self
                    .reference
                    .is_some_and(|symbol| symbol != assignment.symbol)
                    || !prior.reachable
                    || self.catch_symbol_is_inactive(assignment.symbol)
                {
                    return Ok(prior);
                }
                let current_type = match self.assignment_states.get(&declaration) {
                    Some(SourceFlowAssignmentState::Resolved(type_)) => *type_,
                    Some(SourceFlowAssignmentState::ReadonlyUpdate) => return Ok(prior),
                    Some(SourceFlowAssignmentState::Update) => {
                        let current = prior
                            .type_of(assignment.symbol)
                            .ok_or(SourceFlowInvariant::MissingCurrentType(assignment.symbol))?;
                        store
                            .validate_union_constituent_with_global_types(globals, current)
                            .map_err(|error| SourceFlowError::Join { flow, error })?;
                        base_type_of_literal_type(store, Some(globals), current).map_err(
                            |error| SourceFlowError::Narrowing {
                                condition: declaration,
                                error,
                            },
                        )?
                    }
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
                let prior = self.resolve_flow(store, globals, antecedent, depth + 1)?;
                let Some(effect) = self.call_effects.get(&call).copied() else {
                    return if self.plan.region.is_some()
                        || self.plan.nullish_calls.contains_key(&call)
                    {
                        Err(SourceFlowInvariant::InvalidCallEffect(call).into())
                    } else {
                        Ok(prior)
                    };
                };
                if !prior.reachable {
                    return Ok(prior);
                }
                match effect {
                    SourceFlowCallEffect::Unchanged
                    | SourceFlowCallEffect::AssertionNoReference { .. } => Ok(prior),
                    SourceFlowCallEffect::Never(_)
                    | SourceFlowCallEffect::AssertionFalse { .. } => {
                        let mut result = prior;
                        result.reachable = false;
                        Ok(result)
                    }
                    SourceFlowCallEffect::Assertion {
                        signature, symbol, ..
                    } => {
                        if self.reference.is_some_and(|reference| reference != symbol) {
                            return Ok(prior);
                        }
                        let current = prior
                            .type_of(symbol)
                            .ok_or(SourceFlowInvariant::MissingCurrentType(symbol))?;
                        let predicate = store
                            .signature(signature)
                            .and_then(super::signatures::Signature::resolved_type_predicate)
                            .and_then(|predicate| store.type_predicate(predicate))
                            .ok_or(SourceFlowInvariant::InvalidCallEffect(call))?;
                        let narrowed = match predicate.type_id() {
                            Some(asserted) => narrow_source_assertion_type(
                                store, globals, flow, call, current, asserted,
                            )?,
                            None => narrow_by_truthiness(
                                store,
                                Some(globals),
                                current,
                                TruthinessAssumption::Truthy,
                            )
                            .map_err(|error| {
                                SourceFlowError::Narrowing {
                                    condition: call,
                                    error,
                                }
                            })?,
                        };
                        Ok(prior.with_type(symbol, narrowed))
                    }
                }
            }
            kind @ (SourceFlowKind::TrueCondition | SourceFlowKind::FalseCondition) => {
                let antecedent = linear_antecedent(flow, &node)?;
                let condition_node = ast_payload(flow, &node)?;
                let condition = *self
                    .plan
                    .conditions
                    .get(&condition_node)
                    .ok_or(SourceFlowInvariant::UnknownCondition(condition_node))?;
                if self
                    .plan
                    .class_expression_conditions
                    .get(&condition_node)
                    .is_some_and(|proof| {
                        proof.source.kind == SourceClassExpressionConditionKind::Call
                    })
                    && !self.completed_expression_calls.contains(&condition_node)
                {
                    return Err(SourceFlowInvariant::UnreachedCondition(condition_node).into());
                }
                let prior = self.resolve_flow(store, globals, antecedent, depth + 1)?;
                let Some(symbol) = condition.symbol() else {
                    return Ok(prior);
                };
                if self.reference.is_some_and(|reference| reference != symbol)
                    || !prior.reachable
                    || self.catch_symbol_is_inactive(symbol)
                {
                    return Ok(prior);
                }
                let current = prior
                    .type_of(symbol)
                    .ok_or(SourceFlowInvariant::MissingCurrentType(symbol))?;
                let assume_true = match kind {
                    SourceFlowKind::TrueCondition => true,
                    SourceFlowKind::FalseCondition => false,
                    SourceFlowKind::Unreachable
                    | SourceFlowKind::Start
                    | SourceFlowKind::Assignment
                    | SourceFlowKind::ArrayMutation
                    | SourceFlowKind::Call
                    | SourceFlowKind::BranchLabel
                    | SourceFlowKind::LoopLabel => unreachable!(),
                };
                let narrowed = match condition {
                    SourceFlowCondition::ClassExpression(_)
                    | SourceFlowCondition::Unchanged(_)
                    | SourceFlowCondition::ClassPropertyTruthiness(_)
                    | SourceFlowCondition::ClassPropertyEquality(_)
                    | SourceFlowCondition::ClassPropertyPredicate(_) => unreachable!(),
                    SourceFlowCondition::Nullish(_) => {
                        let null = store
                            .intrinsic_bootstrap()
                            .ok_or(SourceFlowInvariant::EqualityNarrowing(
                                SourceEqualityNarrowingError::MissingBootstrap,
                            ))?
                            .null_type;
                        narrow_by_equality(store, globals, current, null, false, !assume_true, None)
                            .map_err(|error| match error {
                                SourceEqualityNarrowingError::Union(error) => {
                                    SourceFlowError::Join { flow, error }
                                }
                                error => SourceFlowInvariant::EqualityNarrowing(error).into(),
                            })?
                    }
                    SourceFlowCondition::Truthiness(condition) => narrow_by_truthiness(
                        store,
                        Some(globals),
                        current,
                        if assume_true == condition.negated {
                            TruthinessAssumption::Falsy
                        } else {
                            TruthinessAssumption::Truthy
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
                        let value = self
                            .condition_values
                            .get(&condition.value)
                            .copied()
                            .or_else(|| {
                                store
                                    .type_node_links(condition.value)
                                    .and_then(|links| links.resolved_type)
                            })
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
                    SourceFlowCondition::In(condition)
                    | SourceFlowCondition::InstanceOf(condition) => {
                        let completed = self.in_conditions.get(&condition.expression).ok_or(
                            SourceFlowInvariant::UnreachedCondition(condition.expression),
                        )?;
                        if completed.input != current {
                            return Err(SourceFlowUnsupported::InNarrowing {
                                condition: condition.expression,
                                type_: current,
                            }
                            .into());
                        }
                        if store
                            .type_node_links(condition.key)
                            .and_then(|links| links.resolved_type)
                            != Some(completed.key)
                        {
                            return Err(SourceFlowInvariant::UnknownCondition(
                                condition.expression,
                            )
                            .into());
                        }
                        if assume_true {
                            completed.when_true
                        } else {
                            completed.when_false
                        }
                    }
                };
                Ok(prior.with_type(symbol, narrowed))
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
        let declared = self
            .reference
            .filter(|_| self.uses_callable_loop_queries())
            .and_then(|symbol| {
                self.declared_types
                    .get(&symbol)
                    .copied()
                    .map(|type_| (symbol, type_))
            });
        if declared.is_some_and(|(symbol, type_)| current.type_of(symbol) == Some(type_)) {
            return Ok(current);
        }
        let first_incomplete = current.incomplete;
        let key = (flow, self.reference);
        let previous = self.loop_snapshots.insert(key, current.clone());
        debug_assert!(previous.is_none());

        let result = (|| {
            for antecedent in &antecedents[1..] {
                let reference_loop = self.reference.is_some()
                    && (self.plan.region.is_some() || self.uses_callable_loop_queries());
                let next = if reference_loop {
                    // The backedge can repeat the demand's prefix before reaching this loop.
                    let outer_visiting = std::mem::take(&mut self.visiting);
                    let result = self.resolve_flow(store, globals, *antecedent, depth + 1);
                    self.visiting = outer_visiting;
                    result
                } else {
                    self.resolve_flow(store, globals, *antecedent, depth + 1)
                }?;
                current = self.join_snapshots(store, globals, flow, &current, &next)?;
                self.loop_snapshots.insert(key, current.clone());
                if declared.is_some_and(|(symbol, type_)| current.type_of(symbol) == Some(type_)) {
                    break;
                }
            }
            current.incomplete = first_incomplete;
            Ok(current)
        })();
        let removed = self.loop_snapshots.remove(&key);
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
        if !then_snapshot.reachable {
            return Ok(else_snapshot.clone());
        }
        if !else_snapshot.reachable {
            return Ok(then_snapshot.clone());
        }
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
            } else if [then_type, else_type].iter().all(|type_| {
                store.type_payload(*type_).is_some_and(|record| {
                    record
                        .object_flags()
                        .intersects(ObjectFlags::EVOLVING_ARRAY)
                })
            }) {
                let left = store.evolving_array_element_type(then_type)?;
                let right = store.evolving_array_element_type(else_type)?;
                let element = store
                    .expression_union_type_with_global_types(
                        globals,
                        &[left, right],
                        UnionReduction::Literal,
                    )
                    .map_err(|error| SourceFlowError::Join { flow, error })?;
                store.create_evolving_array_type(element)?
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
        let mut result = SourceFlowSnapshot::new(joined);
        result.incomplete = then_snapshot.incomplete || else_snapshot.incomplete;
        Ok(result)
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

fn class_predicate_scalar_leaves(
    store: &CanonicalTypeMapperStore,
    call: NodeRef,
    type_: TypeId,
) -> Result<Vec<TypeId>, SourceFlowError> {
    let mut leaves = Vec::new();
    collect_source_equality_leaves(store, type_, &mut leaves, &mut HashSet::new())
        .map_err(SourceFlowInvariant::EqualityNarrowing)?;
    for &leaf in &leaves {
        let flags = store
            .type_payload(leaf)
            .ok_or(SourceFlowInvariant::InvalidCallEffect(call))?
            .flags();
        if !flags.intersects(
            TypeFlags::STRING
                | TypeFlags::STRING_LITERAL
                | TypeFlags::NUMBER
                | TypeFlags::NUMBER_LITERAL
                | TypeFlags::BOOLEAN
                | TypeFlags::BOOLEAN_LITERAL
                | TypeFlags::BIG_INT
                | TypeFlags::BIG_INT_LITERAL
                | TypeFlags::ES_SYMBOL
                | TypeFlags::UNIQUE_ES_SYMBOL
                | TypeFlags::NULLABLE
                | TypeFlags::NEVER,
        ) || flags.intersects(TypeFlags::ENUM | TypeFlags::ENUM_LITERAL) {
            return Err(SourceFlowUnsupported::Call(call).into());
        }
    }
    Ok(leaves)
}

/// Uses the predicate's canonical target, including the complement on a false edge.
#[allow(clippy::too_many_arguments)]
fn narrow_class_property_predicate_type(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    flow: FlowRef,
    call: NodeRef,
    current: TypeId,
    predicate: TypeId,
    assume_true: bool,
) -> Result<TypeId, SourceFlowError> {
    let current_leaves = class_predicate_scalar_leaves(store, call, current)?;
    let predicate_leaves = class_predicate_scalar_leaves(store, call, predicate)?;
    let mut positive = Vec::new();
    for candidate in predicate_leaves {
        for &leaf in &current_leaves {
            for (source, target) in [(leaf, candidate), (candidate, leaf)] {
                if store
                    .is_type_related_to_with_session(
                        source,
                        target,
                        RelationKind::Subtype,
                        Some(globals),
                        None,
                        session,
                    )
                    .map_err(SourceFlowError::Relation)?
                {
                    positive.push(source);
                    break;
                }
            }
        }
    }
    let positive = store
        .expression_union_type_with_global_types_and_session(
            globals,
            &positive,
            UnionReduction::Subtype,
            session,
        )
        .map_err(|error| SourceFlowError::Join { flow, error })?;
    if assume_true {
        return Ok(positive);
    }
    let mut negative = Vec::new();
    for leaf in current_leaves {
        if !store
            .is_type_related_to_with_session(
                leaf,
                positive,
                RelationKind::Subtype,
                Some(globals),
                None,
                session,
            )
            .map_err(SourceFlowError::Relation)?
        {
            negative.push(leaf);
        }
    }
    store
        .expression_union_type_with_global_types_and_session(
            globals,
            &negative,
            UnionReduction::Subtype,
            session,
        )
        .map_err(|error| SourceFlowError::Join { flow, error })
}

fn narrow_source_assertion_type(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    flow: FlowRef,
    call: NodeRef,
    current: TypeId,
    asserted: TypeId,
) -> Result<TypeId, SourceFlowError> {
    let record = store
        .type_payload(current)
        .ok_or(SourceFlowError::Relation(RelationUnavailable::Type(
            current,
        )))?;
    if record.flags().intersects(TypeFlags::ANY)
        && (asserted == globals.object_type || asserted == globals.function_type)
    {
        return Ok(current);
    }
    if record.flags().intersects(TypeFlags::ANY_OR_UNKNOWN) {
        return Ok(asserted);
    }
    if matches!(record.data(), TypeData::Union(_)) {
        let mut constituents = Vec::new();
        collect_source_equality_leaves(store, current, &mut constituents, &mut HashSet::new())
            .map_err(SourceFlowInvariant::EqualityNarrowing)?;
        let narrowed = constituents
            .into_iter()
            .map(|type_| narrow_source_assertion_type(store, globals, flow, call, type_, asserted))
            .collect::<Result<Vec<_>, _>>()?;
        return store
            .expression_union_type_with_global_types(globals, &narrowed, UnionReduction::Subtype)
            .map_err(|error| SourceFlowError::Join { flow, error });
    }
    if store
        .is_type_assignable_to_with_global_types(current, asserted, globals)
        .map_err(SourceFlowError::Relation)?
    {
        return Ok(current);
    }
    if store
        .is_type_assignable_to_with_global_types(asserted, current, globals)
        .map_err(SourceFlowError::Relation)?
    {
        return Ok(asserted);
    }
    store
        .canonical_intersection_type(&[current, asserted], None)
        .map_err(|error| {
            use super::intersection_types::IntersectionTypeError;
            match error {
                IntersectionTypeError::UnsupportedConstituent(_)
                | IntersectionTypeError::UnsupportedPropertyType(_) => {
                    SourceFlowUnsupported::Call(call).into()
                }
                _ => SourceFlowInvariant::InvalidCallEffect(call).into(),
            }
        })
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

/// Follows only completed, non-generic class base identities.
fn source_class_derives_from(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    condition: NodeRef,
    mut source: TypeId,
    target: TypeId,
) -> Result<bool, SourceFlowError> {
    let mut visited = HashSet::new();
    loop {
        if source == target {
            return Ok(true);
        }
        if !visited.insert(source) {
            return Err(SourceFlowInvariant::UnknownCondition(condition).into());
        }
        let members = super::in_operators::instanceof_class_members(store, host, source, false)
            .map_err(SourceFlowError::Relation)?
            .ok_or(SourceFlowUnsupported::InNarrowing {
                condition,
                type_: source,
            })?;
        let Some(base) = members.base() else {
            return Ok(false);
        };
        if base.applied_instance_type() != base.instance_type() {
            return Err(SourceFlowUnsupported::InNarrowing {
                condition,
                type_: source,
            }
            .into());
        }
        source = base.instance_type();
    }
}

/// Uses class base identities, as the native instanceof flow check does.
fn narrow_source_instanceof_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    condition: NodeRef,
    input: TypeId,
    constructor: TypeId,
) -> Result<[TypeId; 2], SourceFlowError> {
    let invalid = || SourceFlowInvariant::UnknownCondition(condition);
    let unavailable = |type_| SourceFlowUnsupported::InNarrowing { condition, type_ };
    let cache_error = |error| SourceFlowError::Narrowing {
        condition,
        error: LogicalBinaryError::Literal(error),
    };
    store
        .validate_union_constituent_with_global_types(globals, input)
        .map_err(cache_error)?;
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let (any, error, unknown, never) = (
        bootstrap.any_type,
        bootstrap.error_type,
        bootstrap.unknown_type,
        bootstrap.never_type,
    );
    let members = super::in_operators::instanceof_class_members(store, host, constructor, true)
        .map_err(SourceFlowError::Relation)?
        .ok_or_else(|| unavailable(constructor))?;
    let instance = members.shells().instance_type();
    if input == any || input == error || input == unknown {
        return Ok([instance, input]);
    }
    if input == never {
        return Ok([input, input]);
    }
    let (leaves, has_origin) = match store.type_payload(input).ok_or_else(invalid)?.data() {
        TypeData::Union(union) => (union.union.types.clone(), union.origin.is_some()),
        _ => (vec![input], false),
    };
    let mut present = Vec::with_capacity(leaves.len());
    let mut absent = Vec::with_capacity(leaves.len());
    for &leaf in &leaves {
        let flags = store.type_payload(leaf).ok_or_else(invalid)?.flags();
        if flags.intersects(TypeFlags::PRIMITIVE) {
            absent.push(leaf);
            continue;
        }
        let derived = source_class_derives_from(store, host, condition, leaf, instance)?;
        if derived {
            present.push(leaf);
        } else if source_class_derives_from(store, host, condition, instance, leaf)?
            && !present.contains(&instance)
        {
            present.push(instance);
        }
        if !derived {
            absent.push(leaf);
        }
    }
    if present.is_empty() {
        // Unrelated object types need the native intersection result.
        return Err(unavailable(input).into());
    }
    if has_origin && (present != leaves || absent != leaves) {
        return Err(unavailable(input).into());
    }
    let mut branches = [input, input];
    for (branch, retained) in branches.iter_mut().zip([present, absent]) {
        if retained == leaves {
            continue;
        }
        *branch = match retained.as_slice() {
            [] => never,
            [only] => *only,
            _ => store
                .expression_union_type_with_global_types_and_session(
                    globals,
                    &retained,
                    UnionReduction::Literal,
                    session,
                )
                .map_err(cache_error)?,
        };
    }
    Ok(branches)
}

/// Checks both membership edges before the flow frame records either result.
fn narrow_source_in_type(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    condition: NodeRef,
    input: TypeId,
    key: TypeId,
) -> Result<[TypeId; 2], SourceFlowError> {
    let invalid = || SourceFlowInvariant::UnknownCondition(condition);
    let unavailable = |type_| SourceFlowUnsupported::InNarrowing { condition, type_ };
    let cache_error = |error| SourceFlowError::Narrowing {
        condition,
        error: LogicalBinaryError::Literal(error),
    };
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let (any, error, never) = (
        bootstrap.any_type,
        bootstrap.error_type,
        bootstrap.never_type,
    );
    store
        .validate_union_constituent_with_global_types(globals, input)
        .map_err(cache_error)?;
    store
        .validate_union_constituent_with_global_types(globals, key)
        .map_err(cache_error)?;
    let key_record = store.type_payload(key).ok_or_else(invalid)?;
    let name = match key_record.data() {
        TypeData::Literal(literal) => match &literal.value {
            LiteralValue::String(value)
                if key_record.flags().intersects(TypeFlags::STRING_LITERAL) =>
            {
                EscapedName::source(value)
            }
            LiteralValue::Number(value)
                if key_record.flags().intersects(TypeFlags::NUMBER_LITERAL) =>
            {
                EscapedName::source(&value.to_string())
            }
            _ => return Ok([input, input]),
        },
        TypeData::UniqueEsSymbol(_) => return Err(unavailable(key).into()),
        _ => return Ok([input, input]),
    };
    if input == any || input == error || input == never {
        return Ok([input, input]);
    }
    let (leaves, has_origin) = match store.type_payload(input).ok_or_else(invalid)?.data() {
        TypeData::Union(union) => (union.union.types.clone(), union.origin.is_some()),
        _ => (vec![input], false),
    };
    let mut present = Vec::with_capacity(leaves.len());
    let mut absent = Vec::with_capacity(leaves.len());
    for &leaf in &leaves {
        if store.type_payload(leaf).ok_or_else(invalid)?.flags() != TypeFlags::OBJECT {
            return Err(unavailable(leaf).into());
        }
        let [can_be_present, can_be_absent] = store
            .in_operator_property_presence(leaf, name.as_ref(), globals, session)
            .map_err(SourceFlowError::Relation)?;
        if can_be_present {
            present.push(leaf);
        }
        if can_be_absent {
            absent.push(leaf);
        }
    }
    if present.is_empty() {
        // Unknown properties need the real Record<K, unknown> intersection.
        return Err(unavailable(input).into());
    }
    if has_origin && (present != leaves || absent != leaves) {
        // A changed subset must retain the source union's nested alias origin.
        return Err(unavailable(input).into());
    }
    let mut branches = [input, input];
    for (branch, retained) in branches.iter_mut().zip([present, absent]) {
        if retained == leaves {
            continue;
        }
        *branch = match retained.as_slice() {
            [] => never,
            [only] => *only,
            _ => store
                .expression_union_type_with_global_types_and_session(
                    globals,
                    &retained,
                    UnionReduction::Literal,
                    session,
                )
                .map_err(cache_error)?,
        };
    }
    Ok(branches)
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
    narrow_by_equality_worker(
        store,
        globals,
        input,
        value,
        strict,
        require_match,
        discriminant,
        None,
    )
}

#[allow(clippy::too_many_arguments)] // Class reads keep the existing source caller's session.
fn narrow_by_equality_worker(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    input: TypeId,
    value: TypeId,
    strict: bool,
    require_match: bool,
    discriminant: Option<&str>,
    mut session: Option<&mut InstantiationSession>,
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
    let mut leaves = Vec::new();
    if !strict && matches!(value_kind, SourceEqualityValueKind::Literal(_)) {
        if discriminant.is_some() {
            return Err(SourceEqualityNarrowingError::UnsupportedType(value));
        }
        collect_source_loose_numeric_equality_leaves(store, globals, input, value, &mut leaves)?;
    } else {
        collect_source_equality_leaves(store, input, &mut leaves, &mut HashSet::new())?;
    }
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
                match session.as_deref_mut() {
                    Some(session) => store.expression_union_type_with_global_types_and_session(
                        globals,
                        &[property.type_, undefined],
                        UnionReduction::Literal,
                        session,
                    ),
                    None => store.expression_union_type_with_global_types(
                        globals,
                        &[property.type_, undefined],
                        UnionReduction::Literal,
                    ),
                }
                .map_err(SourceEqualityNarrowingError::Union)?
            } else {
                property.type_
            };
            let narrowed = narrow_by_equality_worker(
                store,
                globals,
                property_type,
                value,
                strict,
                require_match,
                None,
                session.as_deref_mut(),
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
        _ => match session {
            Some(session) => store.expression_union_type_with_global_types_and_session(
                globals,
                &retained,
                UnionReduction::Literal,
                session,
            ),
            None => store.expression_union_type_with_global_types(
                globals,
                &retained,
                UnionReduction::Literal,
            ),
        }
        .map_err(SourceEqualityNarrowingError::Union),
    }
}

/// Same-domain numbers need no loose-equality coercion. Check every input before filtering.
fn collect_source_loose_numeric_equality_leaves(
    store: &CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    input: TypeId,
    value: TypeId,
    leaves: &mut Vec<TypeId>,
) -> Result<(), SourceEqualityNarrowingError> {
    let numeric_literal = |record: &TypeRecord| {
        record.flags() == TypeFlags::NUMBER_LITERAL
            && matches!(record.data(), TypeData::Literal(literal)
                if matches!(&literal.value, LiteralValue::Number(_)))
    };
    if !store.type_payload(value).is_some_and(numeric_literal) {
        return Err(SourceEqualityNarrowingError::UnsupportedType(value));
    }
    collect_source_equality_leaves(store, input, leaves, &mut HashSet::new())?;
    if leaves.is_empty()
        || !leaves.iter().all(|leaf| {
            store.type_payload(*leaf).is_some_and(|record| {
                numeric_literal(record)
                    || record.flags() == TypeFlags::NUMBER
                        && matches!(record.data(), TypeData::Intrinsic(_))
            })
        })
    {
        return Err(SourceEqualityNarrowingError::UnsupportedType(value));
    }
    store
        .validate_union_constituent_with_global_types(globals, value)
        .map_err(SourceEqualityNarrowingError::Union)?;
    store
        .validate_union_constituent_with_global_types(globals, input)
        .map_err(SourceEqualityNarrowingError::Union)
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

fn source_region_point_flow(
    arena: &NodeArena,
    bound: &BoundFile,
    point: NodeRef,
    region: Option<SourceFlowRegion>,
) -> Result<FlowRef, SourceFlowError> {
    validate_bound_node(bound, bound.flow_graph(), point)?;
    if let Some(region) = region
        && point == region.statement
        && region.entry_node != point
        && source_node_is_descendant_of(arena, region.entry_node, point.node)
        && bound.flow_at(region.entry_node) == Some(region.entry)
        && bound.flow_container(region.entry_node) == Some(bound.source_file())
    {
        return Ok(region.entry);
    }
    if let Some(flow) = bound.flow_at(point) {
        if bound.flow_container(point) != Some(bound.source_file()) {
            return Err(SourceFlowInvariant::MissingFlowPoint(point).into());
        }
        return Ok(flow);
    }
    let mut current = point;
    let mut visited = HashSet::new();
    while visited.insert(current) {
        if region.is_some_and(|region| region.unreachable_incrementor == Some(current))
            && bound.container(point) == Some(bound.source_file())
        {
            return Ok(bound.flow_graph().nodes().unreachable());
        }
        if bound.flow_graph().is_unreachable(current) == Some(true)
            && bound.flow_container(current) == Some(bound.source_file())
        {
            return Ok(bound.flow_graph().nodes().unreachable());
        }
        let Some(parent) = arena.get(current.node).and_then(|record| record.parent) else {
            break;
        };
        current = NodeRef::new(point.arena, point.file, parent);
    }
    Err(SourceFlowInvariant::MissingFlowPoint(point).into())
}

fn source_nullish_statement_flow_region(
    arena: &NodeArena,
    bound: &BoundFile,
    statement: NodeRef,
    assignments: &[SourceFlowNullishAssignment],
) -> Result<SourceFlowRegion, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidSourceRegion(statement);
    let source = bound.source_file();
    if arena.id() != bound.node_arena_id()
        || arena.revision() != bound.node_arena_revision()
        || !statement.is_for(arena.id(), bound.file_id())
        || bound.flow_container(statement) != Some(source)
        || assignments.is_empty()
    {
        return Err(invalid().into());
    }
    let record = arena.get(statement.node).ok_or_else(invalid)?;
    if record.parent != Some(source.node)
        || !matches!(
            record.kind,
            SyntaxKind::ExpressionStatement | SyntaxKind::VariableStatement
        )
        || assignments.iter().any(|assignment| {
            !source_node_is_descendant_of(arena, assignment.expression, statement.node)
        })
    {
        return Err(invalid().into());
    }
    let NodeData::SourceFile(file) = &arena.get(source.node).ok_or_else(invalid)?.data else {
        return Err(invalid().into());
    };
    let index = file
        .statements
        .nodes
        .iter()
        .position(|node| *node == statement.node)
        .ok_or_else(invalid)?;
    let entry = source_following_statement_entry(arena, bound, statement)?.ok_or_else(invalid)?;
    let entry_node = arena
        .iter()
        .find_map(|(id, _)| {
            let node = NodeRef::new(arena.id(), bound.file_id(), id);
            (source_node_is_descendant_of(arena, node, statement.node)
                && bound.flow_container(node) == Some(source)
                && bound.flow_at(node) == Some(entry))
            .then_some(node)
        })
        .ok_or_else(invalid)?;
    let mut exit = None;
    for following in &file.statements.nodes[index + 1..] {
        exit = source_following_statement_entry(
            arena,
            bound,
            NodeRef::new(arena.id(), bound.file_id(), *following),
        )?;
        if exit.is_some() {
            break;
        }
    }
    Ok(SourceFlowRegion {
        statement,
        entry_node,
        entry,
        exit: exit
            .or_else(|| bound.flow_graph().container_end(source))
            .ok_or_else(invalid)?,
        unreachable_incrementor: None,
    })
}

fn source_statement_flow_region(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<SourceFlowRegion, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidSourceRegion(statement);
    let source = bound.source_file();
    if arena.id() != bound.node_arena_id()
        || arena.revision() != bound.node_arena_revision()
        || !statement.is_for(arena.id(), bound.file_id())
        || bound.flow_container(statement) != Some(source)
    {
        return Err(invalid().into());
    }
    let NodeData::SourceFile(file) = &arena.get(source.node).ok_or_else(invalid)?.data else {
        return Err(invalid().into());
    };
    let index = file
        .statements
        .nodes
        .iter()
        .position(|node| *node == statement.node)
        .ok_or_else(invalid)?;
    let entry = source_region_point_flow(arena, bound, statement, None)?;
    let syntax =
        plan_source_for_statement_syntax(arena, bound, store, statement).map_err(|_| invalid())?;
    let literal_false_body = syntax.control.condition.is_some_and(|condition| {
        arena
            .get(condition.node)
            .is_some_and(|record| record.kind == SyntaxKind::FalseKeyword)
    });
    let has_reachable_continue = syntax
        .statements
        .iter()
        .filter_map(|statement| match statement {
            SourceCapturedIterationStatementSyntax::ConditionalJump { jump, .. } => Some(*jump),
            _ => None,
        })
        .chain(syntax.terminal_jump)
        .any(|jump| {
            arena
                .get(jump.node)
                .is_some_and(|record| record.kind == SyntaxKind::ContinueStatement)
                && bound.flow_at(jump).is_some()
        });
    let ends_with_break = syntax.terminal_jump.is_some_and(|jump| {
        arena.get(jump.node).is_some_and(|record| record.kind == SyntaxKind::BreakStatement)
    }) || syntax.statements.iter().any(|statement| {
        matches!(statement, SourceCapturedIterationStatementSyntax::ConditionalJump { condition, jump }
            if arena.get(condition.node).is_some_and(|record| record.kind == SyntaxKind::TrueKeyword)
            && arena.get(jump.node).is_some_and(|record| record.kind == SyntaxKind::BreakStatement))
    });
    // The syntax proof owns these jumps. A terminal break and no live continue
    // leave the binder's pre-incrementor join with no reachable antecedent.
    let unreachable_incrementor = syntax
        .control
        .incrementor
        .filter(|_| literal_false_body || ends_with_break && !has_reachable_continue);
    let mut exit = None;
    for following in &file.statements.nodes[index + 1..] {
        let node = NodeRef::new(arena.id(), bound.file_id(), *following);
        exit = source_following_statement_entry(arena, bound, node)?;
        if exit.is_some() {
            break;
        }
    }
    let exit = exit
        .or_else(|| bound.flow_graph().container_end(source))
        .ok_or_else(invalid)?;
    Ok(SourceFlowRegion {
        statement,
        entry_node: statement,
        entry,
        exit,
        unreachable_incrementor,
    })
}

/// Finds an entry before the next declaration can evaluate a key or initializer.
fn source_following_statement_entry(
    arena: &NodeArena,
    bound: &BoundFile,
    statement: NodeRef,
) -> Result<Option<FlowRef>, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidSourceRegion(statement);
    let mut pending = vec![statement];
    let mut visited = HashSet::new();
    while let Some(node) = pending.pop() {
        if !visited.insert(node) {
            return Err(invalid().into());
        }
        validate_bound_node(bound, bound.flow_graph(), node)?;
        let record = arena.get(node.node).ok_or_else(invalid)?;
        if matches!(
            record.kind,
            SyntaxKind::FunctionDeclaration
                | SyntaxKind::InterfaceDeclaration
                | SyntaxKind::TypeAliasDeclaration
                | SyntaxKind::EmptyStatement
        ) {
            continue;
        }
        if bound.flow_container(node) == Some(bound.source_file()) {
            if let Some(flow) = bound.flow_at(node) {
                return Ok(Some(flow));
            }
            if bound.flow_graph().is_unreachable(node) == Some(true) {
                return Ok(Some(bound.flow_graph().nodes().unreachable()));
            }
        }
        match &record.data {
            NodeData::Block(block) => {
                pending.extend(
                    block
                        .statements
                        .nodes
                        .iter()
                        .rev()
                        .map(|node| NodeRef::new(statement.arena, statement.file, *node)),
                );
            }
            NodeData::ClassDeclaration(class) => {
                if class.modifiers.as_ref().is_some_and(|modifiers| {
                    modifiers.list.nodes.iter().any(|modifier| {
                        arena
                            .get(*modifier)
                            .is_none_or(|record| !matches!(record.data, NodeData::Token(_)))
                    })
                }) {
                    return Err(invalid().into());
                }
                let name = class.name.ok_or_else(invalid)?;
                if arena.get(name).is_none_or(|record| {
                    record.kind != SyntaxKind::Identifier || record.parent != Some(node.node)
                }) {
                    return Err(invalid().into());
                }
                return source_region_point_flow(
                    arena,
                    bound,
                    NodeRef::new(node.arena, node.file, name),
                    None,
                )
                .map(Some);
            }
            NodeData::EnumDeclaration(enumeration) => {
                let name = enumeration.name;
                if arena.get(name).is_none_or(|record| {
                    record.kind != SyntaxKind::Identifier || record.parent != Some(node.node)
                }) {
                    return Err(invalid().into());
                }
                return source_region_point_flow(
                    arena,
                    bound,
                    NodeRef::new(node.arena, node.file, name),
                    None,
                )
                .map(Some);
            }
            _ => return Err(invalid().into()),
        }
    }
    Ok(None)
}

fn validate_source_reference(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(), SourceFlowError> {
    validate_reference_in_container(arena, bound, store, host, bound.source_file(), node, symbol)
}

#[allow(clippy::too_many_arguments)]
fn validate_reference_in_container(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    container: NodeRef,
    node: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidUpdate(node);
    let record = host.node(node).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &record.data else {
        return Err(invalid().into());
    };
    if record.kind != SyntaxKind::Identifier
        || record.flags.0 != 0
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || bound.flow_container(node) != Some(container)
        || store
            .symbol_node_links(node)
            .is_some_and(|links| links.resolved_symbol.is_some_and(|actual| actual != symbol))
    {
        return Err(invalid().into());
    }
    let mut callback_host = host.name_resolver_host(store).map_err(|_| invalid())?;
    let resolved =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
            .map_err(|_| invalid())?
            .resolve(
                Some(CanonicalResolutionLocation::Bound(node)),
                &identifier.text,
                SymbolFlags::VALUE,
                None,
                false,
                false,
            )
            .map_err(|_| invalid())?;
    if resolved != Some(symbol) {
        return Err(invalid().into());
    }
    Ok(())
}

fn validate_source_update(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    update: SourceFlowUpdate,
) -> Result<(), SourceFlowError> {
    validate_update_in_container(arena, bound, store, host, bound.source_file(), update)
}

fn validate_update_in_container(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    container: NodeRef,
    update: SourceFlowUpdate,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidUpdate(update.target);
    validate_reference_in_container(
        arena, bound, store, host, container, update.target, update.symbol,
    )?;
    let declaration = host.node(update.declaration).ok_or_else(invalid)?;
    let NodeData::VariableDeclaration(variable) = &declaration.data else {
        return Err(invalid().into());
    };
    let list = declaration
        .parent
        .and_then(|node| arena.get(node))
        .ok_or_else(invalid)?;
    let NodeData::VariableDeclarationList(declarations) = &list.data else {
        return Err(invalid().into());
    };
    let target = host.node(update.target).ok_or_else(invalid)?;
    let expression = target
        .parent
        .and_then(|node| arena.get(node))
        .ok_or_else(invalid)?;
    let (operand, operator) = match &expression.data {
        NodeData::PrefixUnaryExpression(unary)
            if expression.kind == SyntaxKind::PrefixUnaryExpression =>
        {
            (unary.operand, unary.operator)
        }
        NodeData::PostfixUnaryExpression(unary)
            if expression.kind == SyntaxKind::PostfixUnaryExpression =>
        {
            (unary.operand, unary.operator)
        }
        _ => return Err(invalid().into()),
    };
    if declaration.kind != SyntaxKind::VariableDeclaration
        || arena
            .get(variable.name)
            .is_none_or(|name| name.kind != SyntaxKind::Identifier)
        || bound.symbol(update.declaration) != Some(update.symbol)
        || store
            .symbol(update.symbol)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            != Some(update.declaration)
        || list.kind != SyntaxKind::VariableDeclarationList
        || !matches!(list.flags.0, 0..=2)
        || !declarations
            .declarations
            .nodes
            .contains(&update.declaration.node)
        || update.readonly != (list.flags.0 == 2)
        || operand != update.target.node
        || !matches!(
            operator,
            SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken
        )
    {
        return Err(invalid().into());
    }
    Ok(())
}

/// Header updates have a loop parent, not an expression-statement parent.
fn validate_callable_update(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    syntax: &SourceCallableStatementListSyntax,
    update: SourceFlowUpdate,
) -> Result<NodeRef, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidUpdate(update.target);
    let loops = syntax.counted_for_loops();
    let iteration = loops
        .iter()
        .find(|iteration| iteration.update_target == update.target)
        .ok_or_else(invalid)?;
    let control = &iteration.control;
    let initializer = iteration.initializer;
    let incrementor = control.incrementor.ok_or_else(invalid)?;
    let record = host.node(control.statement).ok_or_else(invalid)?;
    let NodeData::ForStatement(statement) = &record.data else {
        return Err(invalid().into());
    };
    let container = syntax.callable.declaration;
    if record.kind != SyntaxKind::ForStatement
        || record.flags.0 != 0
        || statement.initializer != control.initializer.map(|node| node.node)
        || statement.condition != control.condition.map(|node| node.node)
        || statement.incrementor != Some(incrementor.node)
        || statement.statement != control.body.node
        || update.readonly
        || initializer.binding != VariableBindingKind::Let
        || initializer.declaration != update.declaration
        || initializer.symbol != update.symbol
        || initializer.initializer.is_none()
        || host.node(incrementor).and_then(|node| node.parent) != Some(control.statement.node)
        || host.node(update.target).and_then(|node| node.parent) != Some(incrementor.node)
        || [
            control.statement,
            incrementor,
            update.target,
            update.declaration,
        ]
        .into_iter()
        .any(|node| bound.container(node) != Some(container))
        || [incrementor, update.target, update.declaration]
            .into_iter()
            .any(|node| bound.block_scope_container(node) != Some(control.statement))
    {
        return Err(invalid().into());
    }
    validate_update_in_container(arena, bound, store, host, container, update)?;
    Ok(incrementor)
}

fn validate_source_statement_call(
    arena: &NodeArena,
    bound: &BoundFile,
    call: NodeRef,
) -> Result<NodeRef, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCall(call);
    if !call.is_for(arena.id(), bound.file_id())
        || !bound.contains(call)
        || bound.container(call) != Some(bound.source_file())
    {
        return Err(invalid().into());
    }
    let record = arena.get(call.node).ok_or_else(invalid)?;
    let NodeData::CallExpression(data) = &record.data else {
        return Err(invalid().into());
    };
    let statement = NodeRef::new(call.arena, call.file, record.parent.ok_or_else(invalid)?);
    let statement_record = arena.get(statement.node).ok_or_else(invalid)?;
    if record.kind != SyntaxKind::CallExpression
        || record.flags.0 != 0
        || data.question_dot_token.is_some()
        || data.symbol.is_some()
        || data.facts != 0
        || statement_record.kind != SyntaxKind::ExpressionStatement
        || !matches!(&statement_record.data, NodeData::ExpressionStatement(expression) if expression.expression == call.node && expression.flow_node.is_none())
        || bound.flow_container(statement) != Some(bound.source_file())
        || bound.block_scope_container(call) != bound.block_scope_container(statement)
        || arena.get(data.expression).is_none_or(|callee| {
            !matches!(
                callee.kind,
                SyntaxKind::Identifier | SyntaxKind::PropertyAccessExpression
            ) || callee.parent != Some(call.node)
        })
    {
        return Err(invalid().into());
    }
    Ok(statement)
}

fn validate_source_call_effect(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    bound: &BoundFile,
    call: NodeRef,
    effect: SourceFlowCallEffect,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCallEffect(call);
    let cached = store
        .signature_links(call)
        .map(|links| links.effects_signature)
        .ok_or_else(invalid)?;
    let signature = match effect {
        SourceFlowCallEffect::Unchanged => {
            let no_effect = cached == EffectsSignatureState::NoEffects
                || cached
                    .signature()
                    .and_then(|signature| store.signature(signature))
                    .is_some_and(|signature| {
                        signature
                            .resolved_type_predicate()
                            .and_then(|predicate| store.type_predicate(predicate))
                            .is_some_and(|predicate| {
                                matches!(
                                    predicate.kind(),
                                    TypePredicateKind::Identifier | TypePredicateKind::This
                                )
                            })
                            && signature
                                .resolved_return_type()
                                .and_then(|type_| store.type_payload(type_))
                                .is_some_and(|record| !record.flags().intersects(TypeFlags::NEVER))
                    });
            return if no_effect {
                Ok(())
            } else {
                Err(invalid().into())
            };
        }
        SourceFlowCallEffect::Never(signature)
        | SourceFlowCallEffect::Assertion { signature, .. }
        | SourceFlowCallEffect::AssertionNoReference { signature, .. }
        | SourceFlowCallEffect::AssertionFalse { signature, .. } => signature,
    };
    if cached != EffectsSignatureState::Resolved(signature) {
        return Err(invalid().into());
    }
    let signature = store.signature(signature).ok_or_else(invalid)?;
    match effect {
        SourceFlowCallEffect::Unchanged => unreachable!(),
        SourceFlowCallEffect::Never(_) => {
            if signature
                .resolved_return_type()
                .and_then(|type_| store.type_payload(type_))
                .is_none_or(|record| !record.flags().intersects(TypeFlags::NEVER))
            {
                return Err(invalid().into());
            }
        }
        SourceFlowCallEffect::Assertion {
            argument, symbol, ..
        } => {
            let predicate = signature
                .resolved_type_predicate()
                .and_then(|predicate| store.type_predicate(predicate))
                .ok_or_else(invalid)?;
            let NodeData::CallExpression(data) = &host.node(call).ok_or_else(invalid)?.data else {
                return Err(invalid().into());
            };
            let index = usize::try_from(predicate.parameter_index()).map_err(|_| invalid())?;
            let mut actual_argument = data
                .arguments
                .nodes
                .get(index)
                .copied()
                .ok_or_else(invalid)?;
            let mut visited = HashSet::new();
            while visited.insert(actual_argument) {
                let node = NodeRef::new(call.arena, call.file, actual_argument);
                let Some(NodeData::ParenthesizedExpression(parenthesized)) =
                    host.node(node).map(|record| &record.data)
                else {
                    break;
                };
                actual_argument = parenthesized.expression;
            }
            if predicate.kind() != TypePredicateKind::AssertsIdentifier
                || actual_argument != argument.node
            {
                return Err(invalid().into());
            }
            let (arena, actual_bound) = host.source(call).ok_or_else(invalid)?;
            if actual_bound.node_arena_revision() != bound.node_arena_revision() {
                return Err(invalid().into());
            }
            validate_source_reference(arena, bound, store, host, argument, symbol)
                .map_err(|_| invalid())?;
        }
        SourceFlowCallEffect::AssertionNoReference { .. }
        | SourceFlowCallEffect::AssertionFalse { .. } => {
            let predicate = signature
                .resolved_type_predicate()
                .and_then(|predicate| store.type_predicate(predicate))
                .ok_or_else(invalid)?;
            if predicate.kind() != TypePredicateKind::AssertsIdentifier {
                return Err(invalid().into());
            }
            let NodeData::CallExpression(data) = &host.node(call).ok_or_else(invalid)?.data else {
                return Err(invalid().into());
            };
            let index = usize::try_from(predicate.parameter_index()).map_err(|_| invalid())?;
            let actual = data
                .arguments
                .nodes
                .get(index)
                .map(|node| NodeRef::new(call.arena, call.file, *node));
            let actual = actual
                .map(|mut node| {
                    let mut visited = HashSet::new();
                    loop {
                        if !visited.insert(node) {
                            return Err(invalid());
                        }
                        match &host.node(node).ok_or_else(invalid)?.data {
                            NodeData::ParenthesizedExpression(inner) => {
                                node.node = inner.expression;
                            }
                            _ => return Ok(node),
                        }
                    }
                })
                .transpose()?;
            let expected = match effect {
                SourceFlowCallEffect::AssertionNoReference { argument, .. } => argument,
                SourceFlowCallEffect::AssertionFalse { argument, .. } => Some(argument),
                _ => unreachable!(),
            };
            if actual != expected {
                return Err(invalid().into());
            }
            if let Some(argument) = actual {
                let record = host.node(argument).ok_or_else(invalid)?;
                if matches!(effect, SourceFlowCallEffect::AssertionFalse { .. }) {
                    if record.kind != SyntaxKind::FalseKeyword || predicate.type_id().is_some() {
                        return Err(invalid().into());
                    }
                } else if !(matches!(
                    record.kind,
                    SyntaxKind::StringLiteral
                        | SyntaxKind::NumericLiteral
                        | SyntaxKind::BigIntLiteral
                        | SyntaxKind::TrueKeyword
                        | SyntaxKind::NullKeyword
                ) || record.kind == SyntaxKind::FalseKeyword
                    && predicate.type_id().is_some())
                {
                    return Err(SourceFlowUnsupported::Call(call).into());
                }
            }
        }
    }
    Ok(())
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

/// Rechecks source and binder ownership before a nullish write enters flow.
pub(super) fn validate_source_nullish_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    container: NodeRef,
    assignment: SourceFlowNullishAssignment,
) -> Result<(), SourceFlowError> {
    source_nullish_assignment_proof(arena, bound, store, host, container, assignment).map(|_| ())
}

#[allow(clippy::too_many_lines)] // Match the AST, lexical owner and retained mutation together.
pub(super) fn source_member_assignment_proof(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: NodeRef,
) -> Result<Option<SourceMemberAssignmentProof>, SourceFlowError> {
    let (arena, bound) = host
        .source(expression)
        .ok_or(SourceFlowInvariant::ForeignNode(expression))?;
    let record = own_class_flow_node(store, host, expression)?;
    let NodeData::BinaryExpression(binary) = &record.data else {
        return Ok(None);
    };
    let reference = |node| NodeRef::new(expression.arena, expression.file, node);
    let target = reference(binary.left);
    let target_record = own_class_flow_node(store, host, target)?;
    let NodeData::PropertyAccessExpression(property) = &target_record.data else {
        return Ok(None);
    };
    let operator = reference(binary.operator_token);
    let operator_record = own_class_flow_node(store, host, operator)?;
    if operator_record.kind != SyntaxKind::EqualsToken {
        return Ok(None);
    }
    let Some(statement) = record.parent.map(reference) else {
        return Ok(None);
    };
    let statement_record = own_class_flow_node(store, host, statement)?;
    let NodeData::ExpressionStatement(statement_data) = &statement_record.data else {
        return Ok(None);
    };
    let Some(container) = bound.container(statement) else {
        return Err(SourceFlowInvariant::ForeignNode(statement).into());
    };
    if own_class_flow_node(store, host, container)?.kind != SyntaxKind::ArrowFunction {
        return Ok(None);
    }
    let invalid = || SourceFlowInvariant::InvalidParameterAssignment(target);
    let receiver = reference(property.expression);
    let name = reference(property.name);
    let right = reference(binary.right);
    let receiver_record = own_class_flow_node(store, host, receiver)?;
    let name_record = own_class_flow_node(store, host, name)?;
    let right_record = own_class_flow_node(store, host, right)?;
    if record.kind != SyntaxKind::BinaryExpression
        || record.flags.0 != 0
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.modifiers.is_some()
        || binary.facts != 0
        || statement_record.kind != SyntaxKind::ExpressionStatement
        || statement_record.flags.0 != 0
        || statement_data.expression != expression.node
        || statement_data.flow_node.is_some()
        || target_record.kind != SyntaxKind::PropertyAccessExpression
        || target_record.flags.0 != 0
        || target_record.parent != Some(expression.node)
        || property.question_dot_token.is_some()
        || property.flow_node.is_some()
        || property.facts != 0
        || receiver_record.kind != SyntaxKind::Identifier
        || !matches!(&receiver_record.data, NodeData::Identifier(identifier)
            if !identifier.text.is_empty() && identifier.flow_node.is_none())
        || receiver_record.parent != Some(target.node)
        || receiver_record.flags.0 != 0
        || name_record.kind != SyntaxKind::Identifier
        || !matches!(&name_record.data, NodeData::Identifier(identifier)
            if !identifier.text.is_empty() && identifier.flow_node.is_none())
        || name_record.parent != Some(target.node)
        || name_record.flags.0 != 0
        || operator_record.parent != Some(expression.node)
        || operator_record.flags.0 != 0
        || !matches!(operator_record.data, NodeData::Token(_))
        || right_record.parent != Some(expression.node)
    {
        return Err(SourceFlowUnsupported::PropertyWrite(target).into());
    }
    if arena.id() != bound.node_arena_id()
        || arena.revision() != bound.node_arena_revision()
        || bound.flow_graph().container_is_complete(container) != Some(true)
        || bound.symbol(container) != store.source_declaration_symbol(container)
        || bound.symbol(container).is_none()
        || record.range.start > target_record.range.start
        || target_record.range.end > operator_record.range.start
        || operator_record.range.end > right_record.range.start
        || right_record.range.end > record.range.end
        || target_record.range.start > receiver_record.range.start
        || receiver_record.range.end > name_record.range.start
        || name_record.range.end > target_record.range.end
    {
        return Err(invalid().into());
    }
    let scope = bound.block_scope_container(statement);
    for node in [statement, expression, target, receiver, name, operator, right] {
        validate_bound_node(bound, bound.flow_graph(), node)?;
        if bound.container(node) != Some(container) || bound.block_scope_container(node) != scope {
            return Err(invalid().into());
        }
    }
    validate_nullish_structural_owner(arena, bound, container, expression)?;
    validate_node_container(bound, bound.flow_graph(), container, target)?;
    let receiver_symbol = own_class_flow_symbol(store, host, bound, receiver)?;
    let symbol = store.symbol(receiver_symbol).ok_or_else(invalid)?;
    let declaration = symbol.value_declaration().ok_or_else(invalid)?;
    if !symbol.flags().intersects(SymbolFlags::VARIABLE)
        || bound.container(declaration) != Some(container)
        || bound.symbol(declaration) != Some(receiver_symbol)
    {
        return Err(SourceFlowUnsupported::PropertyWrite(target).into());
    }
    let mut assignment_flow = None;
    for (index, node) in bound.flow_graph().nodes().iter().enumerate() {
        if node.flags.intersects(FlowFlags::ASSIGNMENT)
            && node.payload == Some(FlowNodePayload::Ast(target))
        {
            let flow = FlowRef::new(
                arena.id(),
                bound.file_id(),
                FlowNodeId(u32::try_from(index).map_err(|_| invalid())?),
            );
            if assignment_flow.replace(flow).is_some()
                || source_flow_kind(flow, node.flags)? != SourceFlowKind::Assignment
            {
                return Err(invalid().into());
            }
            linear_antecedent(flow, node)?;
        }
    }
    Ok(Some(SourceMemberAssignmentProof {
        expression,
        target,
        receiver,
        right,
        receiver_symbol,
        container,
        flow: assignment_flow.ok_or_else(invalid)?,
        revision: arena.revision(),
    }))
}

#[allow(clippy::too_many_lines)] // Match the AST, lexical owner and retained mutation together.
fn source_nullish_assignment_proof(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    container: NodeRef,
    assignment: SourceFlowNullishAssignment,
) -> Result<SourceNullishAssignmentProof, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidParameterAssignment(assignment.target);
    if arena.id() != bound.node_arena_id()
        || arena.revision() != bound.node_arena_revision()
        || !container.is_for(arena.id(), bound.file_id())
    {
        return Err(invalid().into());
    }
    for node in [assignment.expression, assignment.target] {
        validate_bound_node(bound, bound.flow_graph(), node)?;
        if bound.container(node) != Some(container) {
            return Err(invalid().into());
        }
    }
    validate_nullish_structural_owner(arena, bound, container, assignment.expression)
        .map_err(|_| invalid())?;
    let expression = arena.get(assignment.expression.node).ok_or_else(invalid)?;
    let NodeData::BinaryExpression(binary) = &expression.data else {
        return Err(invalid().into());
    };
    let target = arena.get(assignment.target.node).ok_or_else(invalid)?;
    let operator = arena.get(binary.operator_token).ok_or_else(invalid)?;
    let right = arena.get(binary.right).ok_or_else(invalid)?;
    if expression.kind != SyntaxKind::BinaryExpression
        || expression.flags.0 != 0
        || binary.left != assignment.target.node
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.modifiers.is_some()
        || binary.facts != 0
        || target.parent != Some(assignment.expression.node)
        || target.flags.0 != 0
        || operator.kind != SyntaxKind::QuestionQuestionEqualsToken
        || operator.parent != Some(assignment.expression.node)
        || operator.flags.0 != 0
        || !matches!(operator.data, NodeData::Token(_))
        || right.parent != Some(assignment.expression.node)
        || expression.range.start > target.range.start
        || target.range.end > operator.range.start
        || operator.range.end > right.range.start
        || right.range.end > expression.range.end
    {
        return Err(invalid().into());
    }

    let receiver = match (&target.data, assignment.declaration, assignment.symbol) {
        (NodeData::Identifier(_), Some(declaration), Some(symbol))
            if target.kind == SyntaxKind::Identifier =>
        {
            validate_bound_node(bound, bound.flow_graph(), declaration)?;
            if bound.container(declaration) != Some(container)
                || bound.symbol(declaration) != Some(symbol)
                || store
                    .symbol(symbol)
                    .and_then(ts_binder::semantic::Symbol::value_declaration)
                    != Some(declaration)
                || own_class_flow_symbol(store, host, bound, assignment.target)? != symbol
            {
                return Err(invalid().into());
            }
            let record = arena.get(declaration.node).ok_or_else(invalid)?;
            let (name, readonly) = match &record.data {
                NodeData::VariableDeclaration(variable)
                    if record.kind == SyntaxKind::VariableDeclaration =>
                {
                    let list = record
                        .parent
                        .and_then(|node| arena.get(node))
                        .ok_or_else(invalid)?;
                    let NodeData::VariableDeclarationList(declarations) = &list.data else {
                        return Err(invalid().into());
                    };
                    if list.kind != SyntaxKind::VariableDeclarationList
                        || !matches!(list.flags.0, 0..=2)
                        || declarations
                            .declarations
                            .nodes
                            .iter()
                            .filter(|node| **node == declaration.node)
                            .count()
                            != 1
                    {
                        return Err(invalid().into());
                    }
                    (variable.name, list.flags.0 == 2)
                }
                NodeData::ParameterDeclaration(parameter)
                    if record.kind == SyntaxKind::Parameter
                        && record.parent == Some(container.node) =>
                {
                    (parameter.name, false)
                }
                _ => return Err(invalid().into()),
            };
            if assignment.readonly != readonly
                || arena.get(name).is_none_or(|name| {
                    name.kind != SyntaxKind::Identifier || name.parent != Some(declaration.node)
                })
            {
                return Err(invalid().into());
            }
            None
        }
        (NodeData::PropertyAccessExpression(_), None, None)
        | (NodeData::ElementAccessExpression(_), None, None) => {
            nullish_member_receiver(arena, bound, store, host, container, assignment.target)?
        }
        _ => return Err(invalid().into()),
    };
    if assignment.symbol.is_some() || receiver.is_some() {
        validate_node_container(bound, bound.flow_graph(), container, assignment.target)?;
        if bound.flow_at(assignment.target).is_none() {
            return Err(invalid().into());
        }
    } else {
        validate_nullish_structural_owner(arena, bound, container, assignment.target)
            .map_err(|_| invalid())?;
    }
    let mut flow = None;
    for (index, node) in bound.flow_graph().nodes().iter().enumerate() {
        if node.flags.intersects(FlowFlags::ASSIGNMENT)
            && node.payload == Some(FlowNodePayload::Ast(assignment.target))
        {
            let actual = FlowRef::new(
                arena.id(),
                bound.file_id(),
                FlowNodeId(u32::try_from(index).map_err(|_| invalid())?),
            );
            if flow.replace(actual).is_some()
                || source_flow_kind(actual, node.flags)? != SourceFlowKind::Assignment
            {
                return Err(invalid().into());
            }
            linear_antecedent(actual, node)?;
        }
    }
    if flow.is_none() && assignment.symbol.is_some() {
        return Err(invalid().into());
    }
    if flow.is_some() && assignment.symbol.is_none() && receiver.is_none() {
        return Err(SourceFlowUnsupported::PropertyWrite(assignment.target).into());
    }
    Ok(SourceNullishAssignmentProof {
        assignment,
        receiver,
        flow,
        revision: arena.revision(),
    })
}

/// Structural nodes use a real enclosing flow point, not a fabricated node entry.
fn validate_nullish_structural_owner(
    arena: &NodeArena,
    bound: &BoundFile,
    container: NodeRef,
    node: NodeRef,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidParameterAssignment(node);
    if arena.id() != bound.node_arena_id()
        || arena.revision() != bound.node_arena_revision()
        || !container.is_for(arena.id(), bound.file_id())
    {
        return Err(invalid().into());
    }
    let graph = bound.flow_graph();
    let scope = bound.block_scope_container(node);
    let mut current = node;
    let mut visited = HashSet::new();
    while visited.insert(current) && visited.len() <= FLOW_DEPTH_LIMIT {
        validate_bound_node(bound, graph, current)?;
        let record = arena.get(current.node).ok_or_else(invalid)?;
        if bound.container(current) != Some(container)
            || bound.block_scope_container(current) != scope
        {
            return Err(invalid().into());
        }
        if bound.flow_container(current).is_some() {
            validate_node_container(bound, graph, container, current)?;
            let flow = bound.flow_at(current).ok_or_else(invalid)?;
            flow_node(graph, flow)?;
            return Ok(());
        }
        if !matches!(
            record.kind,
            SyntaxKind::BinaryExpression
                | SyntaxKind::CallExpression
                | SyntaxKind::PropertyAccessExpression
                | SyntaxKind::ElementAccessExpression
                | SyntaxKind::ParenthesizedExpression
                | SyntaxKind::VariableDeclaration
                | SyntaxKind::VariableDeclarationList
        ) {
            return Err(invalid().into());
        }
        let parent = NodeRef::new(node.arena, node.file, record.parent.ok_or_else(invalid)?);
        let parent_record = arena.get(parent.node).ok_or_else(invalid)?;
        let child_matches = match &parent_record.data {
            NodeData::BinaryExpression(binary)
                if parent_record.kind == SyntaxKind::BinaryExpression =>
            {
                binary.left == current.node || binary.right == current.node
            }
            NodeData::CallExpression(call) if parent_record.kind == SyntaxKind::CallExpression => {
                call.expression == current.node
                    || call
                        .arguments
                        .nodes
                        .iter()
                        .filter(|child| **child == current.node)
                        .count()
                        == 1
            }
            NodeData::PropertyAccessExpression(access)
                if parent_record.kind == SyntaxKind::PropertyAccessExpression =>
            {
                access.expression == current.node
            }
            NodeData::ElementAccessExpression(access)
                if parent_record.kind == SyntaxKind::ElementAccessExpression =>
            {
                access.expression == current.node || access.argument_expression == current.node
            }
            NodeData::ParenthesizedExpression(wrapper)
                if parent_record.kind == SyntaxKind::ParenthesizedExpression =>
            {
                wrapper.expression == current.node
            }
            NodeData::VariableDeclaration(variable)
                if parent_record.kind == SyntaxKind::VariableDeclaration =>
            {
                variable.initializer == Some(current.node)
            }
            NodeData::VariableDeclarationList(list)
                if parent_record.kind == SyntaxKind::VariableDeclarationList =>
            {
                list.declarations
                    .nodes
                    .iter()
                    .filter(|child| **child == current.node)
                    .count()
                    == 1
            }
            NodeData::VariableStatement(statement)
                if parent_record.kind == SyntaxKind::VariableStatement =>
            {
                statement.declaration_list == current.node
            }
            NodeData::ExpressionStatement(statement)
                if parent_record.kind == SyntaxKind::ExpressionStatement =>
            {
                statement.expression == current.node
            }
            NodeData::ReturnStatement(statement)
                if parent_record.kind == SyntaxKind::ReturnStatement =>
            {
                statement.expression == Some(current.node)
            }
            _ => false,
        };
        if !child_matches
            || record.range.start < parent_record.range.start
            || record.range.end > parent_record.range.end
        {
            return Err(invalid().into());
        }
        current = parent;
    }
    Err(invalid().into())
}

fn nullish_member_receiver(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    container: NodeRef,
    target: NodeRef,
) -> Result<Option<SemanticSymbolId>, SourceFlowError> {
    let invalid = || SourceFlowUnsupported::PropertyWrite(target);
    let mut current = target;
    let mut visited = HashSet::new();
    while visited.insert(current) && visited.len() <= FLOW_DEPTH_LIMIT {
        let record = arena.get(current.node).ok_or_else(invalid)?;
        let receiver = match &record.data {
            NodeData::PropertyAccessExpression(access)
                if record.kind == SyntaxKind::PropertyAccessExpression
                    && access.question_dot_token.is_none() =>
            {
                access.expression
            }
            NodeData::ElementAccessExpression(access)
                if record.kind == SyntaxKind::ElementAccessExpression
                    && access.question_dot_token.is_none() =>
            {
                access.expression
            }
            NodeData::Identifier(_) if record.kind == SyntaxKind::Identifier => {
                let symbol = own_class_flow_symbol(store, host, bound, current)?;
                let declaration = store
                    .symbol(symbol)
                    .and_then(ts_binder::semantic::Symbol::value_declaration)
                    .ok_or_else(invalid)?;
                if bound.container(declaration) != Some(container) {
                    return Err(invalid().into());
                }
                return Ok(Some(symbol));
            }
            NodeData::CallExpression(_) if record.kind == SyntaxKind::CallExpression => {
                return Ok(None);
            }
            _ => return Err(invalid().into()),
        };
        let receiver = NodeRef::new(target.arena, target.file, receiver);
        if arena
            .get(receiver.node)
            .is_none_or(|record| record.parent != Some(current.node))
        {
            return Err(invalid().into());
        }
        validate_nullish_structural_owner(arena, bound, container, receiver)
            .map_err(|_| invalid())?;
        current = receiver;
    }
    Err(invalid().into())
}

fn validate_nullish_call(
    arena: &NodeArena,
    bound: &BoundFile,
    container: NodeRef,
    call: NodeRef,
    assignments: &[SourceFlowNullishAssignment],
) -> Result<Option<(NodeRef, FlowRef)>, SourceFlowError> {
    if !assignments
        .iter()
        .any(|assignment| source_node_is_descendant_of(arena, call, assignment.expression.node))
    {
        return Ok(None);
    }
    let invalid = || SourceFlowInvariant::InvalidCall(call);
    validate_bound_node(bound, bound.flow_graph(), call)?;
    let record = arena.get(call.node).ok_or_else(invalid)?;
    let NodeData::CallExpression(data) = &record.data else {
        return Err(invalid().into());
    };
    if record.kind != SyntaxKind::CallExpression
        || record.flags.0 != 0
        || data.question_dot_token.is_some()
        || data.symbol.is_some()
        || data.facts != 0
        || bound.container(call) != Some(container)
        || arena.get(data.expression).is_none_or(|callee| {
            callee.parent != Some(call.node)
                || !matches!(
                    callee.kind,
                    SyntaxKind::Identifier | SyntaxKind::PropertyAccessExpression
                )
        })
    {
        return Err(invalid().into());
    }
    validate_nullish_structural_owner(arena, bound, container, call).map_err(|_| invalid())?;
    let mut statement = call;
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(statement) || visited.len() > FLOW_DEPTH_LIMIT {
            return Err(invalid().into());
        }
        let record = arena.get(statement.node).ok_or_else(invalid)?;
        if bound.container(statement) != Some(container)
            || bound
                .flow_container(statement)
                .is_some_and(|owner| owner != container)
            || bound.block_scope_container(statement) != bound.block_scope_container(call)
        {
            return Err(invalid().into());
        }
        if matches!(
            record.kind,
            SyntaxKind::ExpressionStatement
                | SyntaxKind::VariableStatement
                | SyntaxKind::ReturnStatement
        ) {
            break;
        }
        statement = NodeRef::new(call.arena, call.file, record.parent.ok_or_else(invalid)?);
    }
    let mut antecedent = None;
    for (index, node) in bound.flow_graph().nodes().iter().enumerate() {
        if node.flags.intersects(FlowFlags::CALL)
            && node.payload == Some(FlowNodePayload::Ast(call))
        {
            let flow = FlowRef::new(
                arena.id(),
                bound.file_id(),
                FlowNodeId(u32::try_from(index).map_err(|_| invalid())?),
            );
            if source_flow_kind(flow, node.flags)? != SourceFlowKind::Call
                || antecedent.replace(linear_antecedent(flow, node)?).is_some()
            {
                return Err(invalid().into());
            }
        }
    }
    Ok(Some((statement, antecedent.ok_or_else(invalid)?)))
}

fn prepare_nullish_call(
    arena: &NodeArena,
    bound: &BoundFile,
    container: NodeRef,
    call: NodeRef,
    assignments: &[SourceFlowNullishAssignment],
    effects: &mut SourceFlowEffects,
) -> Result<Option<NodeRef>, SourceFlowError> {
    let Some((statement, antecedent)) =
        validate_nullish_call(arena, bound, container, call, assignments)?
    else {
        return Ok(None);
    };
    if effects.nullish_calls.insert(call, antecedent).is_some() {
        return Err(SourceFlowInvariant::DuplicateCall(call).into());
    }
    Ok(Some(statement))
}

#[allow(clippy::too_many_arguments)]
fn prepare_nullish_assignments(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    container: NodeRef,
    nullish_assignments: impl IntoIterator<Item = SourceFlowNullishAssignment>,
    assignments: &mut Vec<SourceFlowAssignment>,
    conditions: &mut Vec<SourceFlowCondition>,
    effects: &mut SourceFlowEffects,
) -> Result<(), SourceFlowError> {
    for assignment in nullish_assignments {
        let host = host.ok_or(SourceFlowInvariant::InvalidParameterAssignment(
            assignment.target,
        ))?;
        let proof =
            source_nullish_assignment_proof(arena, bound, store, host, container, assignment)?;
        if effects
            .nullish_assignments
            .insert(assignment.target, proof)
            .is_some()
            || effects
                .assignment_declarations
                .contains_key(&assignment.target)
            || effects.captured_origins.contains_key(&assignment.target)
            || effects
                .property_assignments
                .contains_key(&assignment.target)
        {
            return Err(SourceFlowInvariant::DuplicateAssignment(assignment.target).into());
        }
        if let (Some(declaration), Some(symbol)) = (assignment.declaration, assignment.symbol) {
            effects
                .assignment_declarations
                .insert(assignment.target, declaration);
            assignments.push(SourceFlowAssignment {
                declaration: assignment.target,
                symbol,
            });
        }
        for condition in [
            SourceFlowCondition::Nullish(SourceNullishCondition {
                expression: assignment.target,
                symbol: assignment.symbol,
            }),
            match assignment.symbol.filter(|_| !assignment.readonly) {
                Some(symbol) => SourceFlowCondition::Truthiness(SourceTruthinessCondition {
                    expression: assignment.expression,
                    symbol,
                    negated: false,
                }),
                None => SourceFlowCondition::Unchanged(assignment.expression),
            },
        ] {
            if bound.flow_graph().nodes().iter().any(|node| {
                node.flags
                    .intersects(FlowFlags::TRUE_CONDITION | FlowFlags::FALSE_CONDITION)
                    && node.payload == Some(FlowNodePayload::Ast(condition.expression()))
            }) {
                conditions.push(condition);
            }
        }
    }
    Ok(())
}

fn parameter_assignment_declaration_and_name(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
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
            if pattern_record.kind == SyntaxKind::ObjectBindingPattern {
                return super::variables::plan_function_object_parameter_bindings(
                    arena, bound, store, container, parameter,
                )
                .ok()?
                .into_iter()
                .find(|binding| binding.element == declaration)
                .map(|binding| (parameter, binding.name));
            }
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

fn validate_class_local_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    body: &ClassBodyPlan,
    assignment: SourceFlowParameterAssignment,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidParameterAssignment(assignment.target);
    if !matches!(
        body.kind,
        ClassBodyKind::Constructor | ClassBodyKind::Method { .. }
    ) || bound.symbol(assignment.parameter) != Some(assignment.symbol)
        || bound.container(assignment.parameter) != Some(body.declaration)
        || bound.flow_container(assignment.target) != Some(body.declaration)
    {
        return Err(invalid().into());
    }
    let target_record = host.node(assignment.target).ok_or_else(invalid)?;
    let NodeData::Identifier(target) = &target_record.data else {
        return Err(invalid().into());
    };
    let binding = target_record
        .parent
        .map(|node| NodeRef::new(assignment.target.arena, assignment.target.file, node))
        .ok_or_else(invalid)?;
    let pattern = host
        .node(binding)
        .and_then(|record| record.parent)
        .map(|node| NodeRef::new(binding.arena, binding.file, node))
        .ok_or_else(invalid)?;
    let expression = host
        .node(pattern)
        .and_then(|record| record.parent)
        .map(|node| NodeRef::new(binding.arena, binding.file, node))
        .ok_or_else(invalid)?;
    let NodeData::BinaryExpression(binary) = &host.node(expression).ok_or_else(invalid)?.data
    else {
        return Err(invalid().into());
    };
    let receiver = NodeRef::new(binding.arena, binding.file, binary.right);
    let plan =
        super::source_properties::plan_class_binding_property(store, host, binding, receiver)
            .map_err(|_| invalid())?;
    if plan.target() != assignment.target
        || !source_node_is_descendant_of(arena, expression, body.body.node)
    {
        return Err(invalid().into());
    }
    let declaration = host.node(assignment.parameter).ok_or_else(invalid)?;
    let name = match &declaration.data {
        NodeData::BindingElement(element) => element.name,
        NodeData::VariableDeclaration(variable) => Some(variable.name),
        _ => None,
    }
    .ok_or_else(invalid)?;
    let Some(NodeData::Identifier(name)) = arena.get(name).map(|record| &record.data) else {
        return Err(invalid().into());
    };
    if target_record.flags.0 != 0 || target.flow_node.is_some() || target.text != name.text {
        return Err(invalid().into());
    }
    let mut callback_host = host.name_resolver_host(store).map_err(|_| invalid())?;
    let mut resolver =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
            .map_err(|_| invalid())?;
    let symbol = resolver
        .resolve(
            Some(CanonicalResolutionLocation::Bound(assignment.target)),
            &target.text,
            SymbolFlags::VALUE,
            None,
            false,
            false,
        )
        .map_err(|_| invalid())?;
    if symbol != Some(assignment.symbol) {
        return Err(invalid().into());
    }
    Ok(())
}

/// Rechecks the real declaration and mutable binding used by a local flow entry.
fn annotated_uninitialized_local(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    container: NodeRef,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(NodeRef, NodeRef), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidParameterAssignment(declaration);
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || !container.is_for(arena.id(), bound.file_id())
        || !bound.contains(container)
        || !declaration.is_for(arena.id(), bound.file_id())
        || !bound.contains(declaration)
        || bound.container(declaration) != Some(container)
    {
        return Err(invalid().into());
    }
    let reference = |node| NodeRef::new(declaration.arena, declaration.file, node);
    let callable = arena.get(container.node).ok_or_else(invalid)?;
    let body = match &callable.data {
        NodeData::FunctionDeclaration(function)
            if callable.kind == SyntaxKind::FunctionDeclaration =>
        {
            function.body.map(reference).ok_or_else(invalid)?
        }
        NodeData::FunctionExpression(_) if callable.kind == SyntaxKind::FunctionExpression => {
            validate_source_function_expression_owner(arena, bound, store, container)
                .map_err(|_| invalid())?
        }
        NodeData::ArrowFunction(_) if callable.kind == SyntaxKind::ArrowFunction => {
            validate_source_arrow_owner(arena, bound, store, container)?
        }
        NodeData::MethodDeclaration(method)
            if callable.kind == SyntaxKind::MethodDeclaration
                && bound.symbol(container).is_some_and(|owner| {
                    store.source_object_literal_method_owner_is_exact(container, owner)
                }) =>
        {
            method.body.map(reference).ok_or_else(invalid)?
        }
        _ => return Err(invalid().into()),
    };
    let body_record = arena.get(body.node).ok_or_else(invalid)?;
    if body_record.kind != SyntaxKind::Block
        || body_record.parent != Some(container.node)
        || !matches!(body_record.data, NodeData::Block(_))
    {
        return Err(invalid().into());
    }
    let record = arena.get(declaration.node).ok_or_else(invalid)?;
    let NodeData::VariableDeclaration(variable) = &record.data else {
        return Err(invalid().into());
    };
    let name = reference(variable.name);
    let name_record = arena.get(name.node).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid().into());
    };
    let annotation = variable
        .type_
        .and_then(|node| arena.get(node))
        .ok_or_else(invalid)?;
    let list = record
        .parent
        .and_then(|node| arena.get(node))
        .ok_or_else(invalid)?;
    let NodeData::VariableDeclarationList(declarations) = &list.data else {
        return Err(invalid().into());
    };
    let binding = match list.flags.0 {
        0 => VariableBindingKind::Var,
        1 => VariableBindingKind::Let,
        _ => return Err(invalid().into()),
    };
    let statement = list.parent.map(reference).ok_or_else(invalid)?;
    let statement_record = arena.get(statement.node).ok_or_else(invalid)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(invalid().into());
    };
    let scope = bound
        .block_scope_container(declaration)
        .ok_or_else(invalid)?;
    let locals_scope = if binding == VariableBindingKind::Var {
        container
    } else {
        scope
    };
    if record.kind != SyntaxKind::VariableDeclaration
        || record.flags.0 != 0
        || variable.initializer.is_some()
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || annotation.parent != Some(declaration.node)
        || list.kind != SyntaxKind::VariableDeclarationList
        || declarations
            .declarations
            .nodes
            .iter()
            .filter(|node| **node == declaration.node)
            .count()
            != 1
        || declarations.declarations.has_trailing_comma
        || declarations.facts != 0
        || statement_record.kind != SyntaxKind::VariableStatement
        || statement_record.flags.0 != 0
        || Some(statement_data.declaration_list) != record.parent
        || statement_data.modifiers.is_some()
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || !source_node_is_descendant_of(arena, statement, body.node)
        || bound.block_scope_container(name) != Some(scope)
        || bound.block_scope_container(statement) != Some(scope)
        || bound
            .locals(locals_scope)
            .and_then(|table| store.symbol_table(table))
            .and_then(|table| table.get_source(&identifier.text))
            != Some(symbol)
        || plan_top_level_variable(
            bound,
            store,
            declaration,
            name,
            &identifier.text,
            binding,
            false,
        )
        .map_err(|_| invalid())?
            != symbol
    {
        return Err(invalid().into());
    }
    Ok((name, body))
}

/// Reads the written type only after matching the local and its actual bound read.
pub(super) fn annotated_uninitialized_local_read_annotation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    read: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<Option<NodeRef>, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidParameterAssignment(read);
    let (arena, bound) = host.source(read).ok_or_else(invalid)?;
    let declaration = store
        .symbol(symbol)
        .and_then(ts_binder::semantic::Symbol::value_declaration)
        .ok_or_else(invalid)?;
    let container = bound.container(declaration).ok_or_else(invalid)?;
    if container == bound.source_file() {
        return Ok(None);
    }
    if bound.container(read) != Some(container)
        || bound.flow_container(read) != Some(container)
        || own_class_flow_symbol(store, host, bound, read)? != symbol
    {
        return Err(invalid().into());
    }
    annotated_uninitialized_local(arena, bound, store, container, declaration, symbol)?;
    let NodeData::VariableDeclaration(variable) =
        &arena.get(declaration.node).ok_or_else(invalid)?.data
    else {
        return Err(invalid().into());
    };
    variable
        .type_
        .map(|node| Some(NodeRef::new(declaration.arena, declaration.file, node)))
        .ok_or_else(|| invalid().into())
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)] // Keep the local, scope and actual write proof together.
fn validate_annotated_local_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    container: NodeRef,
    assignment: SourceFlowParameterAssignment,
    statement_list: Option<&SourceCallableStatementListSyntax>,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidParameterAssignment(assignment.target);
    let (name, body) = annotated_uninitialized_local(
        arena,
        bound,
        store,
        container,
        assignment.parameter,
        assignment.symbol,
    )?;
    let target = arena.get(assignment.target.node).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &target.data else {
        return Err(invalid().into());
    };
    let expression = target
        .parent
        .and_then(|node| arena.get(node))
        .ok_or_else(invalid)?;
    let NodeData::BinaryExpression(binary) = &expression.data else {
        return Err(invalid().into());
    };
    let operator = arena.get(binary.operator_token).ok_or_else(invalid)?;
    let statement = expression
        .parent
        .and_then(|node| arena.get(node))
        .ok_or_else(invalid)?;
    let NodeData::ExpressionStatement(statement_data) = &statement.data else {
        return Err(invalid().into());
    };
    let statement_ref = NodeRef::new(
        container.arena,
        container.file,
        expression.parent.ok_or_else(invalid)?,
    );
    let scope = if let Some(syntax) = statement_list {
        let expression_ref = NodeRef::new(
            container.arena,
            container.file,
            target.parent.ok_or_else(invalid)?,
        );
        validate_statement_list_expression(arena, bound, syntax, statement_ref, expression_ref)?;
        if syntax.callable.declaration != container || syntax.callable.body != body {
            return Err(invalid().into());
        }
        syntax
            .linear_statement_scope(statement_ref)
            .or_else(|| syntax.for_of_statement_scope(statement_ref))
            .ok_or_else(invalid)?
    } else {
        if statement.parent != Some(body.node) {
            return Err(invalid().into());
        }
        container
    };
    let resolved_symbol = if statement_list.is_some() {
        Some(
            own_class_flow_symbol(store, host.ok_or_else(invalid)?, bound, assignment.target)
                .map_err(|_| invalid())?,
        )
    } else {
        bound
            .locals(container)
            .and_then(|table| store.symbol_table(table))
            .and_then(|table| table.get_source(&identifier.text))
    };
    if !assignment.target.is_for(arena.id(), bound.file_id())
        || !bound.contains(assignment.target)
        || bound.container(assignment.target) != Some(container)
        || bound.block_scope_container(assignment.target) != Some(scope)
        || bound.flow_container(assignment.target) != Some(container)
        || resolved_symbol != Some(assignment.symbol)
        || target.kind != SyntaxKind::Identifier
        || target.flags.0 != 0
        || identifier.flow_node.is_some()
        || arena.get(name.node).is_none_or(|record| {
            !matches!(&record.data, NodeData::Identifier(name) if name.text == identifier.text)
        })
        || expression.kind != SyntaxKind::BinaryExpression
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
        || arena.get(binary.right).is_none_or(|right| right.parent != target.parent)
        || statement.kind != SyntaxKind::ExpressionStatement
        || statement.flags.0 != 0
        || Some(statement_data.expression) != target.parent
        || statement_data.flow_node.is_some()
    {
        return Err(invalid().into());
    }
    Ok(())
}

fn validate_statement_list_source(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    syntax: &SourceCallableStatementListSyntax,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCall(syntax.callable.declaration);
    let callable = super::source_callables::plan_source_callable(
        store,
        host,
        syntax.callable.declaration,
        syntax.callable.owner_symbol,
        syntax.callable.array_targets,
    )
    .map_err(|_| invalid())?;
    if callable != syntax.callable {
        return Err(invalid().into());
    }
    let actual = plan_source_callable_statement_list_syntax(arena, bound, store, &syntax.callable)
        .map_err(|_| invalid())?;
    if actual != *syntax {
        return Err(invalid().into());
    }
    Ok(())
}

fn validate_statement_list_expression(
    arena: &NodeArena,
    bound: &BoundFile,
    syntax: &SourceCallableStatementListSyntax,
    statement: NodeRef,
    expression: NodeRef,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCall(expression);
    let scope = syntax.statement_scope(statement).ok_or_else(invalid)?;
    let container = syntax.callable.declaration;
    if syntax.expression_scope(expression) != Some(scope)
        || [statement, expression, scope, container]
            .into_iter()
            .any(|node| !node.is_for(arena.id(), bound.file_id()) || !bound.contains(node))
        || bound.container(statement) != Some(container)
        || bound.container(expression) != Some(container)
        || bound.block_scope_container(statement) != Some(scope)
        || bound.block_scope_container(expression) != Some(scope)
    {
        return Err(invalid().into());
    }
    let record = arena.get(statement.node).ok_or_else(invalid)?;
    let NodeData::ExpressionStatement(data) = &record.data else {
        return Err(invalid().into());
    };
    let expression_record = arena.get(expression.node).ok_or_else(invalid)?;
    if record.kind != SyntaxKind::ExpressionStatement
        || record.flags.0 != 0
        || data.expression != expression.node
        || data.flow_node.is_some()
        || expression_record.parent != Some(statement.node)
        || expression_record.flags.0 != 0
        || expression_record.range.start < record.range.start
        || expression_record.range.end > record.range.end
    {
        return Err(invalid().into());
    }
    validate_node_container(bound, bound.flow_graph(), container, statement)
}

fn validate_statement_list_call(
    arena: &NodeArena,
    bound: &BoundFile,
    syntax: &SourceCallableStatementListSyntax,
    expression: NodeRef,
) -> Result<NodeRef, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCall(expression);
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
        || !matches!(
            callee.kind,
            SyntaxKind::Identifier | SyntaxKind::PropertyAccessExpression
        )
        || callee.parent != Some(expression.node)
        || callee.range.start < record.range.start
        || callee.range.end > record.range.end
    {
        return Err(invalid().into());
    }
    let statement = NodeRef::new(
        expression.arena,
        expression.file,
        record.parent.ok_or_else(invalid)?,
    );
    validate_statement_list_expression(arena, bound, syntax, statement, expression)?;
    Ok(statement)
}
fn validate_parameter_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    container: NodeRef,
    assignment: SourceFlowParameterAssignment,
) -> Result<(), SourceFlowError> {
    validate_parameter_assignment_in_list(arena, bound, store, host, container, assignment, None)
}

fn initialized_statement_local(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    syntax: &SourceCallableStatementListSyntax,
    declaration: NodeRef,
) -> Result<Option<(NodeRef, SemanticSymbolId)>, SourceFlowError> {
    let mut pending = syntax.statements.iter().collect::<Vec<_>>();
    while let Some(statement) = pending.pop() {
        match statement {
            SourceCallableStatementSyntax::Leaf(SourceLinearFunctionStatementSyntax::Local(
                local,
            )) if local.declaration == declaration && local.initializer.is_some() => {
                return Ok(Some((local.name, local.symbol)));
            }
            SourceCallableStatementSyntax::ObjectBinding(binding)
                if arena.get(declaration.node).is_some_and(|record| {
                    record.kind == SyntaxKind::BindingElement
                        && record.parent == Some(binding.pattern.node)
                }) =>
            {
                let invalid = || SourceFlowInvariant::InvalidParameterAssignment(declaration);
                let (kind, element) = super::variables::plan_callable_object_binding_element(
                    arena,
                    bound,
                    store,
                    declaration,
                    syntax.callable.declaration,
                )
                .map_err(|_| invalid())?;
                if kind != binding.binding
                    || bound.block_scope_container(declaration) != Some(binding.block_scope)
                {
                    return Err(invalid().into());
                }
                return Ok(Some((element.name, element.symbol)));
            }
            SourceCallableStatementSyntax::Block { statements, .. } => {
                pending.extend(statements);
            }
            SourceCallableStatementSyntax::If(branch) => {
                pending.extend(&branch.then_statements);
                pending.extend(&branch.else_statements);
            }
            SourceCallableStatementSyntax::ForOf(iteration) => {
                pending.extend(&iteration.statements);
            }
            _ => {}
        }
    }
    Ok(None)
}

fn initialized_local_write_statement(
    syntax: &SourceCallableStatementListSyntax,
    wanted: NodeRef,
) -> bool {
    let mut pending = syntax.statements.iter().collect::<Vec<_>>();
    while let Some(statement) = pending.pop() {
        match statement {
            SourceCallableStatementSyntax::Leaf(
                SourceLinearFunctionStatementSyntax::Expression { statement, .. },
            ) if *statement == wanted => return true,
            SourceCallableStatementSyntax::Block { statements, .. } => {
                pending.extend(statements);
            }
            SourceCallableStatementSyntax::If(branch) => {
                pending.extend(&branch.then_statements);
                pending.extend(&branch.else_statements);
            }
            SourceCallableStatementSyntax::ForOf(iteration) => {
                pending.extend(&iteration.statements);
            }
            _ => {}
        }
    }
    false
}

fn validate_initialized_local_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    container: NodeRef,
    assignment: SourceFlowParameterAssignment,
    syntax: &SourceCallableStatementListSyntax,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidParameterAssignment(assignment.target);
    let (name, symbol) =
        initialized_statement_local(arena, bound, store, syntax, assignment.parameter)?
            .ok_or_else(invalid)?;
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || syntax.callable.declaration != container
        || symbol != assignment.symbol
        || [
            container,
            assignment.target,
            assignment.parameter,
            name,
        ]
        .into_iter()
        .any(|node| !node.is_for(arena.id(), bound.file_id()) || !bound.contains(node))
        || bound.symbol(assignment.parameter) != Some(assignment.symbol)
        || bound.container(assignment.parameter) != Some(container)
        || bound.container(assignment.target) != Some(container)
        || bound.flow_container(assignment.target) != Some(container)
        || own_class_flow_symbol(store, host, bound, assignment.target).map_err(|_| invalid())?
            != assignment.symbol
    {
        return Err(invalid().into());
    }
    let target = arena.get(assignment.target.node).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &target.data else {
        return Err(invalid().into());
    };
    let expression_ref = NodeRef::new(
        container.arena,
        container.file,
        target.parent.ok_or_else(invalid)?,
    );
    let expression = arena.get(expression_ref.node).ok_or_else(invalid)?;
    let NodeData::BinaryExpression(binary) = &expression.data else {
        return Err(invalid().into());
    };
    let operator = arena.get(binary.operator_token).ok_or_else(invalid)?;
    let statement = NodeRef::new(
        container.arena,
        container.file,
        expression.parent.ok_or_else(invalid)?,
    );
    validate_statement_list_expression(arena, bound, syntax, statement, expression_ref)?;
    if !initialized_local_write_statement(syntax, statement)
        || bound.block_scope_container(assignment.target) != syntax.statement_scope(statement)
        || target.kind != SyntaxKind::Identifier
        || target.flags.0 != 0
        || identifier.flow_node.is_some()
        || arena.get(name.node).is_none_or(|record| {
            !matches!(&record.data, NodeData::Identifier(name) if name.text == identifier.text)
        })
        || expression.kind != SyntaxKind::BinaryExpression
        || expression.flags.0 != 0
        || binary.left != assignment.target.node
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.facts != 0
        || binary.modifiers.is_some()
        || operator.kind != SyntaxKind::EqualsToken
        || operator.flags.0 != 0
        || operator.parent != Some(expression_ref.node)
        || !matches!(operator.data, NodeData::Token(_))
        || target.range.start < expression.range.start
        || target.range.end > expression.range.end
        || operator.range.start < target.range.end
        || operator.range.end > expression.range.end
        || arena.get(binary.right).is_none_or(|right| {
            right.parent != Some(expression_ref.node)
                || right.range.start < operator.range.end
                || right.range.end > expression.range.end
        })
    {
        return Err(invalid().into());
    }
    Ok(())
}

fn validate_parameter_assignment_in_list(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    container: NodeRef,
    assignment: SourceFlowParameterAssignment,
    statement_list: Option<&SourceCallableStatementListSyntax>,
) -> Result<(), SourceFlowError> {
    if arena
        .get(assignment.parameter.node)
        .is_some_and(|record| record.kind == SyntaxKind::BindingElement)
    {
        return validate_initialized_local_assignment(
            arena,
            bound,
            store,
            host.ok_or(SourceFlowInvariant::InvalidParameterAssignment(assignment.target))?,
            container,
            assignment,
            statement_list.ok_or(SourceFlowInvariant::InvalidParameterAssignment(
                assignment.target,
            ))?,
        );
    }
    if arena
        .get(assignment.parameter.node)
        .is_some_and(|record| record.kind == SyntaxKind::VariableDeclaration)
    {
        if arena.get(assignment.parameter.node).is_some_and(|record| {
            matches!(&record.data, NodeData::VariableDeclaration(variable) if variable.initializer.is_some())
        }) {
            return validate_initialized_local_assignment(
                arena,
                bound,
                store,
                host.ok_or(SourceFlowInvariant::InvalidParameterAssignment(assignment.target))?,
                container,
                assignment,
                statement_list.ok_or(SourceFlowInvariant::InvalidParameterAssignment(
                    assignment.target,
                ))?,
            );
        }
        return validate_annotated_local_assignment(
            arena,
            bound,
            store,
            host,
            container,
            assignment,
            statement_list,
        );
    }
    let invalid = || SourceFlowInvariant::InvalidParameterAssignment(assignment.target);
    if !assignment.target.is_for(arena.id(), bound.file_id())
        || !assignment.parameter.is_for(arena.id(), bound.file_id())
        || !bound.contains(assignment.target)
        || !bound.contains(assignment.parameter)
        || bound.symbol(assignment.parameter) != Some(assignment.symbol)
        || bound.container(assignment.parameter) != Some(container)
        || bound.container(assignment.target) != Some(container)
        || statement_list.is_none()
            && bound.block_scope_container(assignment.target) != Some(container)
        || bound.flow_container(assignment.target) != Some(container)
    {
        return Err(invalid().into());
    }

    let function = arena.get(container.node).ok_or_else(invalid)?;
    let (parameters, function_body) = match &function.data {
        NodeData::FunctionDeclaration(function_data)
            if function.kind == SyntaxKind::FunctionDeclaration =>
        {
            (&function_data.parameters, function_data.body)
        }
        NodeData::FunctionExpression(function_data)
            if function.kind == SyntaxKind::FunctionExpression
                && statement_list.is_some_and(|syntax| {
                    syntax.callable.declaration == container
                        && syntax.callable.family
                            == super::source_callables::SourceCallableFamily::ArrowFunction
                        && syntax.callable.body.node == function_data.body
                        && bound.symbol(container) == Some(syntax.callable.owner_symbol)
                }) =>
        {
            (&function_data.parameters, Some(function_data.body))
        }
        NodeData::MethodDeclaration(method)
            if function.kind == SyntaxKind::MethodDeclaration
                && method.asterisk_token.is_none()
                && method.modifiers.is_none()
                && method.type_parameters.is_none()
                && method.postfix_token.is_none()
                && bound.symbol(container).is_some_and(|owner| {
                    store.source_object_literal_method_owner_is_exact(container, owner)
                }) =>
        {
            (&method.parameters, method.body)
        }
        _ => return Err(invalid().into()),
    };
    let (parameter_declaration, parameter_name) = parameter_assignment_declaration_and_name(
        arena,
        bound,
        store,
        container,
        assignment.parameter,
    )
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
    if parameter.kind != SyntaxKind::Parameter
        || parameter.parent != Some(container.node)
        || function.kind == SyntaxKind::MethodDeclaration
            && parameter_declaration != assignment.parameter
        || parameters
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
    let compound = statement_list.is_some()
        && matches!(
            function.kind,
            SyntaxKind::FunctionDeclaration | SyntaxKind::FunctionExpression
        )
        && parameter_declaration == assignment.parameter
        && super::primitive_operators::compound_assignment_binary_operator(operator.kind).is_some();
    if expression.kind != SyntaxKind::BinaryExpression
        || expression.flags.0 != 0
        || binary.left != assignment.target.node
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.facts != 0
        || binary.modifiers.is_some()
        || operator.kind != SyntaxKind::EqualsToken && !compound
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
        || statement_list.is_none()
            && (body.kind != SyntaxKind::Block
                || body.parent != Some(container.node)
                || function_body != statement.parent)
    {
        return Err(invalid().into());
    }
    if let Some(syntax) = statement_list {
        let expression_ref = NodeRef::new(
            container.arena,
            container.file,
            target.parent.ok_or_else(invalid)?,
        );
        let statement_ref = NodeRef::new(
            container.arena,
            container.file,
            expression.parent.ok_or_else(invalid)?,
        );
        validate_statement_list_expression(arena, bound, syntax, statement_ref, expression_ref)?;
        if function_body != Some(syntax.callable.body.node)
            || bound.block_scope_container(assignment.target)
                != syntax.statement_scope(statement_ref)
        {
            return Err(invalid().into());
        }
    }
    Ok(())
}

fn validate_arrow_statement(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    container: NodeRef,
    statement: NodeRef,
) -> Result<(), SourceFlowError> {
    let body = validate_source_arrow_owner(arena, bound, store, container)?;
    validate_callable_expression_statement(arena, bound, container, body, statement)
}

fn validate_callable_expression_statement(
    arena: &NodeArena,
    bound: &BoundFile,
    container: NodeRef,
    body: NodeRef,
    statement: NodeRef,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCall(statement);
    if !statement.is_for(arena.id(), bound.file_id())
        || !bound.contains(statement)
        || bound.container(statement) != Some(container)
        || bound.block_scope_container(statement) != Some(container)
    {
        return Err(invalid().into());
    }
    let record = arena.get(statement.node).ok_or_else(invalid)?;
    let NodeData::ExpressionStatement(data) = &record.data else {
        return Err(invalid().into());
    };
    let body_record = arena.get(body.node).ok_or_else(invalid)?;
    let NodeData::Block(block) = &body_record.data else {
        return Err(invalid().into());
    };
    let expression = arena.get(data.expression).ok_or_else(invalid)?;
    if record.kind != SyntaxKind::ExpressionStatement
        || record.flags.0 != 0
        || record.parent != Some(body.node)
        || data.flow_node.is_some()
        || block
            .statements
            .nodes
            .iter()
            .filter(|node| **node == statement.node)
            .count()
            != 1
        || record.range.start < body_record.range.start
        || record.range.end > body_record.range.end
        || expression.parent != Some(statement.node)
        || expression.range.start < record.range.start
        || expression.range.end > record.range.end
    {
        return Err(invalid().into());
    }
    validate_node_container(bound, bound.flow_graph(), container, statement)
}

fn validate_linear_direct_call(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    container: NodeRef,
    expression: NodeRef,
) -> Result<NodeRef, SourceFlowError> {
    if arena
        .get(container.node)
        .is_none_or(|record| record.kind != SyntaxKind::ArrowFunction)
    {
        return validate_direct_call(arena, bound, container, expression);
    }
    let invalid = || SourceFlowInvariant::InvalidCall(expression);
    if !expression.is_for(arena.id(), bound.file_id())
        || !bound.contains(expression)
        || bound.container(expression) != Some(container)
        || bound.block_scope_container(expression) != Some(container)
    {
        return Err(invalid().into());
    }
    let record = arena.get(expression.node).ok_or_else(invalid)?;
    let NodeData::CallExpression(call) = &record.data else {
        return Err(invalid().into());
    };
    let callee = arena.get(call.expression).ok_or_else(invalid)?;
    let statement = NodeRef::new(
        expression.arena,
        expression.file,
        record.parent.ok_or_else(invalid)?,
    );
    if record.kind != SyntaxKind::CallExpression
        || record.flags.0 != 0
        || call.question_dot_token.is_some()
        || call.symbol.is_some()
        || call.facts != 0
        || !matches!(
            callee.kind,
            SyntaxKind::Identifier | SyntaxKind::PropertyAccessExpression
        )
        || callee.parent != Some(expression.node)
        || callee.range.start < record.range.start
        || callee.range.end > record.range.end
        || !matches!(&arena.get(statement.node).ok_or_else(invalid)?.data,
            NodeData::ExpressionStatement(data) if data.expression == expression.node)
    {
        return Err(invalid().into());
    }
    validate_arrow_statement(arena, bound, store, container, statement)?;
    Ok(statement)
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
    let body_id = statement.parent.ok_or_else(invalid)?;
    let body = arena.get(body_id).ok_or_else(invalid)?;
    let function = arena.get(container.node).ok_or_else(invalid)?;
    let function_body = match &function.data {
        NodeData::FunctionDeclaration(function_data)
            if function.kind == SyntaxKind::FunctionDeclaration =>
        {
            function_data.body
        }
        NodeData::MethodDeclaration(method)
            if function.kind == SyntaxKind::MethodDeclaration
                && function
                    .parent
                    .and_then(|parent| arena.get(parent))
                    .is_some_and(|parent| parent.kind == SyntaxKind::ObjectLiteralExpression) =>
        {
            method.body
        }
        _ => return Err(invalid().into()),
    }
    .ok_or_else(invalid)?;
    let scope = if body_id == function_body {
        container
    } else {
        NodeRef::new(arena.id(), bound.file_id(), body_id)
    };
    let statement_ref = NodeRef::new(arena.id(), bound.file_id(), statement_id);
    if statement.kind != SyntaxKind::ExpressionStatement
        || statement.flags.0 != 0
        || statement_data.expression != expression.node
        || statement_data.flow_node.is_some()
        || body.kind != SyntaxKind::Block
        || arena.get(function_body).is_none_or(|body| {
            body.kind != SyntaxKind::Block || body.parent != Some(container.node)
        })
        || !source_node_is_descendant_of(arena, statement_ref, function_body)
        || bound.block_scope_container(expression) != Some(scope)
        || bound.block_scope_container(statement_ref) != Some(scope)
    {
        return Err(invalid().into());
    }
    validate_node_container(bound, bound.flow_graph(), container, statement_ref)?;
    Ok(statement_ref)
}

fn validate_array_mutation(
    arena: &NodeArena,
    bound: &BoundFile,
    container: NodeRef,
    mutation: SourceFlowArrayMutation,
) -> Result<(), SourceFlowError> {
    validate_array_mutation_in_list(arena, bound, container, mutation, None)
}

fn validate_array_mutation_in_list(
    arena: &NodeArena,
    bound: &BoundFile,
    container: NodeRef,
    mutation: SourceFlowArrayMutation,
    statement_list: Option<&SourceCallableStatementListSyntax>,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidArrayMutation(mutation.call);
    match statement_list {
        Some(syntax) => validate_statement_list_call(arena, bound, syntax, mutation.call)?,
        None => validate_direct_call(arena, bound, container, mutation.call)?,
    };
    if bound.symbol(mutation.declaration) != Some(mutation.symbol)
        || bound.container(mutation.declaration) != Some(container)
        || bound.container(mutation.receiver) != Some(container)
    {
        return Err(invalid().into());
    }
    let call = arena.get(mutation.call.node).ok_or_else(invalid)?;
    let NodeData::CallExpression(call) = &call.data else {
        return Err(invalid().into());
    };
    let property = arena.get(call.expression).ok_or_else(invalid)?;
    let NodeData::PropertyAccessExpression(access) = &property.data else {
        return Err(invalid().into());
    };
    let name = arena.get(access.name).ok_or_else(invalid)?;
    let receiver = arena.get(mutation.receiver.node).ok_or_else(invalid)?;
    if property.kind != SyntaxKind::PropertyAccessExpression
        || property.flags.0 != 0
        || access.expression != mutation.receiver.node
        || access.question_dot_token.is_some()
        || access.flow_node.is_some()
        || access.facts != 0
        || name.parent != Some(call.expression)
        || name.flags.0 != 0
        || !matches!(&name.data, NodeData::Identifier(name) if matches!(name.text.as_str(), "push" | "unshift"))
        || receiver.kind != SyntaxKind::Identifier
        || receiver.flags.0 != 0
        || receiver.parent != Some(call.expression)
    {
        return Err(invalid().into());
    }
    Ok(())
}

fn validate_call_container(
    bound: &BoundFile,
    container: NodeRef,
    call: NodeRef,
    statement: NodeRef,
    antecedent: FlowRef,
) -> Result<(), SourceFlowError> {
    let entry = match bound.flow_graph().nodes().get(antecedent) {
        Some(node)
            if node.flags.bits() & !FLOW_METADATA_BITS == FlowFlags::ARRAY_MUTATION.bits()
                && node.payload == Some(FlowNodePayload::Ast(call))
                && node.antecedents.is_empty() =>
        {
            node.antecedent
        }
        _ => Some(antecedent),
    };
    if !bound.contains(call)
        || bound.container(call) != Some(container)
        || bound.container(statement) != Some(container)
        || bound.block_scope_container(call).is_none()
        || bound.block_scope_container(call) != bound.block_scope_container(statement)
        || bound.flow_container(statement) != Some(container)
        || bound.flow_at(statement) != entry
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
    if let Some(expected) = plan.nullish_calls.get(&call) {
        if *expected != antecedent
            || !bound.contains(call)
            || bound.container(call) != Some(plan.container)
            || bound
                .flow_container(call)
                .is_some_and(|owner| owner != plan.container)
            || bound.container(statement) != Some(plan.container)
            || bound.flow_container(statement) != Some(plan.container)
            || bound.flow_at(statement).is_none()
            || bound.block_scope_container(call) != bound.block_scope_container(statement)
            || plan.calls.get(&call) != Some(&statement)
        {
            return Err(SourceFlowInvariant::InvalidCall(call).into());
        }
        return Ok(());
    }
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

fn class_flow_source_node<'host>(
    store: &CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<&'host ts_ast::Node, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidClassProperty(node);
    let record = super::declared::preflight_node(store, host, node).map_err(|_| invalid())?;
    let parent = record
        .parent
        .map_or(super::store::SourceNodeParent::Root, |parent| {
            super::store::SourceNodeParent::Parent(NodeRef::new(node.arena, node.file, parent))
        });
    if store.source_node_kind(node) != Some(record.kind)
        || store.source_node_parent(node) != Some(parent)
    {
        return Err(invalid().into());
    }
    Ok(record)
}

fn validate_class_property_flow_condition(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    bound: &BoundFile,
    body: &ClassBodyPlan,
    condition: SourceFlowCondition,
) -> Result<(ClassPropertyTruthinessSource, [FlowRef; 2]), SourceFlowError> {
    match condition {
        SourceFlowCondition::ClassPropertyTruthiness(condition) => {
            validate_class_property_condition(store, host, bound, body, condition)
        }
        SourceFlowCondition::ClassPropertyEquality(condition) => {
            validate_class_property_equality_condition(store, host, bound, body, condition)
        }
        SourceFlowCondition::ClassPropertyPredicate(condition) => {
            validate_class_property_predicate_condition(store, host, bound, body, condition)
        }
        _ => Err(SourceFlowInvariant::InvalidClassProperty(condition.expression()).into()),
    }
}

/// Equality keeps the ordinary field proof and resolves undefined at its written location.
pub(super) fn validate_class_property_equality_condition(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    bound: &BoundFile,
    body: &ClassBodyPlan,
    condition: SourceClassPropertyEqualityCondition,
) -> Result<(ClassPropertyTruthinessSource, [FlowRef; 2]), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidClassProperty(condition.access);
    let (arena, binding) = host.source(condition.expression).ok_or_else(invalid)?;
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || binding.source_file() != bound.source_file()
        || !condition.access.is_for(arena.id(), bound.file_id())
        || !condition.value.is_for(arena.id(), bound.file_id())
    {
        return Err(invalid().into());
    }
    let root = class_flow_source_node(store, host, condition.expression)?;
    let NodeData::BinaryExpression(binary) = &root.data else {
        return Err(invalid().into());
    };
    let operator = NodeRef::new(
        condition.expression.arena,
        condition.expression.file,
        binary.operator_token,
    );
    let operator_record = class_flow_source_node(store, host, operator)?;
    let expected_operator = match condition.comparison {
        SourceTypeofComparison::Equal => SyntaxKind::EqualsEqualsEqualsToken,
        SourceTypeofComparison::NotEqual => SyntaxKind::ExclamationEqualsEqualsToken,
    };
    let operands_match = [binary.left, binary.right] == [condition.access.node, condition.value.node]
        || [binary.left, binary.right] == [condition.value.node, condition.access.node];
    let access = class_flow_source_node(store, host, condition.access)?;
    let value = class_flow_source_node(store, host, condition.value)?;
    let (left, right) = if binary.left == condition.access.node {
        (access, value)
    } else {
        (value, access)
    };
    if root.kind != SyntaxKind::BinaryExpression
        || root.flags.0 != 0
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.modifiers.is_some()
        || binary.facts != 0
        || !operands_match
        || access.parent != Some(condition.expression.node)
        || value.parent != Some(condition.expression.node)
        || value.kind != SyntaxKind::Identifier
        || value.flags.0 != 0
        || !matches!(&value.data, NodeData::Identifier(identifier)
            if identifier.text == "undefined" && identifier.flow_node.is_none())
        || operator_record.parent != Some(condition.expression.node)
        || operator_record.kind != expected_operator
        || operator_record.flags.0 != 0
        || !matches!(operator_record.data, NodeData::Token(_))
        || left.range.start < root.range.start
        || left.range.end > operator_record.range.start
        || operator_record.range.end > right.range.start
        || right.range.end > root.range.end
    {
        return Err(invalid().into());
    }
    let statement = NodeRef::new(
        condition.expression.arena,
        condition.expression.file,
        root.parent.ok_or_else(invalid)?,
    );
    let statement_record = class_flow_source_node(store, host, statement)?;
    if statement_record.kind != SyntaxKind::IfStatement
        || statement_record.flags.0 != 0
        || !matches!(&statement_record.data, NodeData::IfStatement(branch)
            if branch.expression == condition.expression.node && branch.facts == 0 && branch.flow_node.is_none())
        || !source_node_is_descendant_of(arena, statement, body.body.node)
    {
        return Err(invalid().into());
    }
    let undefined = store
        .intrinsic_bootstrap()
        .ok_or_else(invalid)?
        .undefined_symbol;
    let mut callbacks = host.name_resolver_host(store).map_err(|_| invalid())?;
    let resolved = CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callbacks)
        .map_err(|_| invalid())?
        .resolve(
            Some(CanonicalResolutionLocation::Bound(condition.value)),
            "undefined",
            SymbolFlags::VALUE,
            None,
            false,
            false,
        )
        .map_err(|_| invalid())?;
    if resolved.and_then(|symbol| store.get_merged_symbol(symbol)) != Some(undefined) {
        return Err(invalid().into());
    }
    let source = plan_class_property_truthiness(store, host, body, condition.access)
        .map_err(|_| invalid())?;
    let edges = class_property_condition_edges(bound, condition.expression, condition.access)?;
    Ok((source, edges))
}

fn validate_class_property_condition(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    bound: &BoundFile,
    body: &ClassBodyPlan,
    condition: SourceClassPropertyTruthinessCondition,
) -> Result<(ClassPropertyTruthinessSource, [FlowRef; 2]), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidClassProperty(condition.access);
    let (arena, binding) = host.source(condition.expression).ok_or_else(invalid)?;
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || binding.source_file() != bound.source_file()
        || !condition.access.is_for(arena.id(), bound.file_id())
    {
        return Err(invalid().into());
    }
    let root = class_flow_source_node(store, host, condition.expression)?;
    let statement = NodeRef::new(
        condition.expression.arena,
        condition.expression.file,
        root.parent.ok_or_else(invalid)?,
    );
    let statement_record = class_flow_source_node(store, host, statement)?;
    if statement_record.flags.0 != 0
        || !matches!(&statement_record.data, NodeData::IfStatement(branch)
            if branch.expression == condition.expression.node && branch.facts == 0 && branch.flow_node.is_none())
        || !source_node_is_descendant_of(arena, statement, body.body.node)
    {
        return Err(invalid().into());
    }
    let mut current = condition.expression;
    let mut negated = false;
    let mut visited = HashSet::new();
    while current != condition.access {
        if !visited.insert(current) {
            return Err(invalid().into());
        }
        let record = class_flow_source_node(store, host, current)?;
        if record.flags.0 != 0 {
            return Err(invalid().into());
        }
        let child = match &record.data {
            NodeData::ParenthesizedExpression(parenthesized)
                if record.kind == SyntaxKind::ParenthesizedExpression =>
            {
                parenthesized.expression
            }
            NodeData::PrefixUnaryExpression(prefix)
                if record.kind == SyntaxKind::PrefixUnaryExpression
                    && prefix.operator == SyntaxKind::ExclamationToken =>
            {
                negated = !negated;
                prefix.operand
            }
            _ => return Err(invalid().into()),
        };
        let child = NodeRef::new(current.arena, current.file, child);
        if class_flow_source_node(store, host, child)?.parent != Some(current.node) {
            return Err(invalid().into());
        }
        current = child;
    }
    if negated != condition.negated {
        return Err(invalid().into());
    }
    let source = plan_class_property_truthiness(store, host, body, condition.access)
        .map_err(|_| invalid())?;
    let edges = class_property_condition_edges(bound, condition.expression, condition.access)?;
    Ok((source, edges))
}

fn class_property_condition_edges(
    bound: &BoundFile,
    expression: NodeRef,
    access: NodeRef,
) -> Result<[FlowRef; 2], SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidClassProperty(access);
    let entry = bound.flow_at(access).ok_or_else(invalid)?;
    let mut edges = 0;
    let mut edge_flows = [None, None];
    for (index, row) in bound.flow_graph().nodes().iter().enumerate() {
        if row.payload != Some(FlowNodePayload::Ast(expression)) {
            continue;
        }
        let flow = FlowRef::new(
            bound.node_arena_id(),
            bound.file_id(),
            FlowNodeId(u32::try_from(index).map_err(|_| invalid())?),
        );
        let edge = match source_flow_kind(flow, row.flags)? {
            SourceFlowKind::TrueCondition => TRUE_CONDITION_EDGE,
            SourceFlowKind::FalseCondition => FALSE_CONDITION_EDGE,
            _ => return Err(invalid().into()),
        };
        if edges & edge != 0 || linear_antecedent(flow, row)? != entry {
            return Err(invalid().into());
        }
        edges |= edge;
        edge_flows[usize::from(edge == FALSE_CONDITION_EDGE)] = Some(flow);
    }
    if edges != BOTH_CONDITION_EDGES {
        return Err(SourceFlowInvariant::MissingConditionEdge {
            condition: expression,
            true_edge: edges & TRUE_CONDITION_EDGE != 0,
            false_edge: edges & FALSE_CONDITION_EDGE != 0,
        }
        .into());
    }
    Ok([
        edge_flows[0].ok_or_else(invalid)?,
        edge_flows[1].ok_or_else(invalid)?,
    ])
}

#[allow(clippy::too_many_lines)] // The call and both binder edges share one source proof.
fn validate_class_property_predicate_condition(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    bound: &BoundFile,
    body: &ClassBodyPlan,
    condition: SourceClassPropertyPredicateCondition,
) -> Result<(ClassPropertyTruthinessSource, [FlowRef; 2]), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidCallEffect(condition.call);
    let (arena, binding) = host.source(condition.expression).ok_or_else(invalid)?;
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || binding.source_file() != bound.source_file()
        || !condition.call.is_for(arena.id(), bound.file_id())
        || !condition.access.is_for(arena.id(), bound.file_id())
        || bound.container(condition.call) != Some(body.declaration)
    {
        return Err(invalid().into());
    }
    let root = class_flow_source_node(store, host, condition.expression)?;
    let statement = NodeRef::new(
        condition.expression.arena,
        condition.expression.file,
        root.parent.ok_or_else(invalid)?,
    );
    let statement_record = class_flow_source_node(store, host, statement)?;
    if statement_record.flags.0 != 0
        || !matches!(&statement_record.data, NodeData::IfStatement(branch)
            if branch.expression == condition.expression.node && branch.facts == 0 && branch.flow_node.is_none())
        || !source_node_is_descendant_of(arena, statement, body.body.node)
    {
        return Err(invalid().into());
    }
    let mut current = condition.expression;
    let mut negated = false;
    let mut visited = HashSet::new();
    while current != condition.call {
        if !visited.insert(current) {
            return Err(invalid().into());
        }
        let record = class_flow_source_node(store, host, current)?;
        if record.flags.0 != 0 {
            return Err(invalid().into());
        }
        let child = match &record.data {
            NodeData::ParenthesizedExpression(parenthesized)
                if record.kind == SyntaxKind::ParenthesizedExpression =>
            {
                parenthesized.expression
            }
            NodeData::PrefixUnaryExpression(prefix)
                if record.kind == SyntaxKind::PrefixUnaryExpression
                    && prefix.operator == SyntaxKind::ExclamationToken =>
            {
                negated = !negated;
                prefix.operand
            }
            _ => return Err(invalid().into()),
        };
        let child = NodeRef::new(current.arena, current.file, child);
        if class_flow_source_node(store, host, child)?.parent != Some(current.node) {
            return Err(invalid().into());
        }
        current = child;
    }
    if negated != condition.negated {
        return Err(invalid().into());
    }
    let call_record = class_flow_source_node(store, host, condition.call)?;
    let NodeData::CallExpression(call) = &call_record.data else {
        return Err(invalid().into());
    };
    let syntax =
        plan_direct_source_call_syntax(arena, store, condition.call).map_err(|_| invalid())?;
    if call.type_arguments.is_some()
        || syntax.arguments() != [condition.access]
        || class_flow_source_node(store, host, syntax.callee())?.kind != SyntaxKind::Identifier
    {
        return Err(SourceFlowUnsupported::Call(condition.call).into());
    }
    let source = plan_class_property_truthiness(store, host, body, condition.access)
        .map_err(|_| invalid())?;
    let entry = bound.flow_at(condition.access).ok_or_else(invalid)?;
    let mut edge_flows = [None, None];
    for (index, row) in bound.flow_graph().nodes().iter().enumerate() {
        if row.payload != Some(FlowNodePayload::Ast(condition.expression)) {
            continue;
        }
        let flow = FlowRef::new(
            arena.id(),
            bound.file_id(),
            FlowNodeId(u32::try_from(index).map_err(|_| invalid())?),
        );
        let edge = match source_flow_kind(flow, row.flags)? {
            SourceFlowKind::TrueCondition => 0,
            SourceFlowKind::FalseCondition => 1,
            _ => return Err(invalid().into()),
        };
        if edge_flows[edge].replace(flow).is_some() || linear_antecedent(flow, row)? != entry {
            return Err(invalid().into());
        }
    }
    let [Some(true_edge), Some(false_edge)] = edge_flows else {
        return Err(SourceFlowInvariant::MissingConditionEdge {
            condition: condition.expression,
            true_edge: edge_flows[0].is_some(),
            false_edge: edge_flows[1].is_some(),
        }
        .into());
    };
    Ok((source, [true_edge, false_edge]))
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
    if class_destructuring_write_assignment(host, target).is_some() {
        return true;
    }
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
    if !matches!(
        body.kind,
        ClassBodyKind::Constructor | ClassBodyKind::Method { .. }
    ) || !source_node_is_descendant_of(arena, target, body.body.node)
        || bound.flow_container(target) != Some(body.declaration)
    {
        return Err(invalid().into());
    }
    let plan = if class_destructuring_write_assignment(host, target).is_some() {
        plan_class_destructuring_property_write(store, host, target)
    } else {
        let expression = NodeRef::new(
            target.arena,
            target.file,
            host.node(target)
                .and_then(|record| record.parent)
                .ok_or_else(invalid)?,
        );
        plan_class_property_write(store, host, expression)
    }
    .map_err(|error| match error {
        SourcePropertyError::Unsupported(_) => {
            SourceFlowError::Unsupported(SourceFlowUnsupported::PropertyWrite(target))
        }
        _ => invalid().into(),
    })?;
    let expression = plan.node();
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

fn preflight_logical_statement(
    arena: &NodeArena,
    bound: &BoundFile,
    container: NodeRef,
    syntax: SourceLinearLogicalStatementSyntax,
) -> Result<SourceLogicalStatementFlow, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidLogicalStatement(syntax.statement);
    let actual =
        plan_source_linear_logical_statement_syntax(arena, bound, syntax.statement, container)
            .map_err(|_| invalid())?;
    if actual != syntax || syntax.container != container {
        return Err(invalid().into());
    }
    let entry = bound.flow_at(syntax.statement).ok_or_else(invalid)?;
    let rows = logical_statement_rows(bound.flow_graph().nodes(), &syntax, entry)?;
    let block_scope = bound
        .block_scope_container(syntax.statement)
        .ok_or_else(invalid)?;
    let mut source_points = vec![
        (syntax.statement, Some(entry)),
        (syntax.expression, None),
        (syntax.left, Some(entry)),
        (syntax.left_receiver, Some(entry)),
        (syntax.left_name, Some(entry)),
        (syntax.operator, None),
        (syntax.right, None),
        (syntax.callee, Some(rows.left_true)),
        (syntax.right_receiver, Some(rows.left_true)),
        (syntax.right_name, Some(rows.left_true)),
    ];
    for &argument in &syntax.arguments {
        let record = arena.get(argument.node).ok_or_else(invalid)?;
        source_points.push((
            argument,
            (record.kind == SyntaxKind::Identifier).then_some(rows.left_true),
        ));
    }
    let proof = SourceLogicalStatementFlow {
        syntax,
        revision: arena.revision(),
        block_scope,
        entry,
        rows,
        source_points,
    };
    validate_logical_statement(bound, container, &proof)?;
    Ok(proof)
}

fn validate_logical_statement(
    bound: &BoundFile,
    container: NodeRef,
    proof: &SourceLogicalStatementFlow,
) -> Result<(), SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidLogicalStatement(proof.syntax.statement);
    let graph = bound.flow_graph();
    if proof.syntax.container != container
        || bound.node_arena_revision() != proof.revision
        || !container.is_for(bound.node_arena_id(), bound.file_id())
        || !bound.contains(container)
    {
        return Err(invalid().into());
    }
    validate_container(graph, container)?;
    for &(node, flow) in &proof.source_points {
        validate_bound_node(bound, graph, node)?;
        if bound.container(node) != Some(container)
            || bound.block_scope_container(node) != Some(proof.block_scope)
            || bound.flow_at(node) != flow
        {
            return Err(invalid().into());
        }
        if flow.is_some() {
            validate_node_container(bound, graph, container, node)?;
        } else if bound.flow_container(node).is_some() {
            return Err(invalid().into());
        }
    }
    if bound.flow_at(proof.syntax.statement) != Some(proof.entry)
        || logical_statement_rows(graph.nodes(), &proof.syntax, proof.entry)? != proof.rows
    {
        return Err(invalid().into());
    }
    Ok(())
}

/// Recover labels by their complete source-bound edges, never by allocation IDs.
fn logical_statement_rows(
    nodes: &FlowNodeArena,
    syntax: &SourceLinearLogicalStatementSyntax,
    entry: FlowRef,
) -> Result<SourceLogicalStatementRows, SourceFlowError> {
    let invalid = || SourceFlowInvariant::InvalidLogicalStatement(syntax.statement);
    if nodes.get(entry).is_none() || !syntax.statement.is_for(nodes.node_arena(), nodes.file()) {
        return Err(invalid().into());
    }
    let condition_pair = |expression: NodeRef, antecedent: FlowRef| {
        let mut true_edge = None;
        let mut false_edge = None;
        for (index, row) in nodes.iter().enumerate() {
            if row.payload != Some(FlowNodePayload::Ast(expression)) {
                continue;
            }
            let flow = FlowRef::new(
                nodes.node_arena(),
                nodes.file(),
                FlowNodeId(u32::try_from(index).map_err(|_| invalid())?),
            );
            let slot = match source_flow_kind(flow, row.flags)? {
                SourceFlowKind::TrueCondition => &mut true_edge,
                SourceFlowKind::FalseCondition => &mut false_edge,
                _ => return Err(invalid().into()),
            };
            if linear_antecedent(flow, row)? != antecedent || slot.replace(flow).is_some() {
                return Err(invalid().into());
            }
        }
        Ok::<_, SourceFlowError>((
            true_edge.ok_or_else(invalid)?,
            false_edge.ok_or_else(invalid)?,
        ))
    };
    let (left_true, left_false) = condition_pair(syntax.left, entry)?;
    let (right_true, right_false) = condition_pair(syntax.right, left_true)?;
    let label = |antecedents: &[FlowRef]| -> Result<FlowRef, SourceFlowError> {
        let mut matched = None;
        for (index, row) in nodes.iter().enumerate() {
            if row.antecedents != antecedents {
                continue;
            }
            let flow = FlowRef::new(
                nodes.node_arena(),
                nodes.file(),
                FlowNodeId(u32::try_from(index).map_err(|_| invalid())?),
            );
            if source_flow_kind(flow, row.flags)? != SourceFlowKind::BranchLabel
                || row.payload.is_some()
                || row.antecedent.is_some()
                || matched.replace(flow).is_some()
            {
                return Err(invalid().into());
            }
        }
        matched.ok_or_else(|| invalid().into())
    };
    Ok(SourceLogicalStatementRows {
        left_true,
        left_false,
        right_true,
        right_false,
        pre_right: label(&[left_true])?,
        join: label(&[left_false, right_true, right_false])?,
    })
}

#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn prepare_class_expression_conditions(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    body: &ClassBodyPlan,
    container: NodeRef,
    points: &[NodeRef],
    conditions: Vec<SourceFlowCondition>,
) -> Result<
    (
        Vec<SourceFlowCondition>,
        HashMap<NodeRef, SourceClassExpressionConditionProof>,
    ),
    SourceFlowError,
> {
    let mut proofs = HashMap::new();
    if !conditions
        .iter()
        .any(|condition| matches!(condition, SourceFlowCondition::ClassExpression(_)))
    {
        return Ok((conditions, proofs));
    }
    let end = if matches!(
        body.kind,
        ClassBodyKind::Constructor | ClassBodyKind::StaticBlock
    ) {
        Some(
            bound
                .flow_graph()
                .container_return(body.declaration)
                .ok_or(SourceFlowInvariant::InvalidClassBody(body.declaration))?,
        )
    } else {
        bound.flow_graph().container_end(container)
    };
    let retained = retained_condition_edges(bound, container, points, end)?;
    let mut result = Vec::new();
    let mut seen = HashSet::new();
    for condition in conditions {
        if !seen.insert(condition.expression()) {
            return Err(SourceFlowInvariant::DuplicateCondition(condition.expression()).into());
        }
        let SourceFlowCondition::ClassExpression(source) = condition else {
            result.push(condition);
            continue;
        };
        let Some(&edges) = retained.get(&source.expression) else {
            continue;
        };
        let checked = validate_class_expression_condition(arena, bound, store, host, body, source)?;
        proofs.insert(
            source.expression,
            SourceClassExpressionConditionProof { source, edges },
        );
        result.push(checked);
    }
    Ok((result, proofs))
}

#[allow(clippy::too_many_lines)] // Keep source ownership and binding checks together.
fn validate_class_expression_condition(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    body: &ClassBodyPlan,
    source: SourceClassExpressionCondition,
) -> Result<SourceFlowCondition, SourceFlowError> {
    let invalid = || SourceFlowInvariant::UnknownCondition(source.expression);
    let owner = class_flow_source_node(store, host, source.owner).map_err(|_| invalid())?;
    let expression =
        class_flow_source_node(store, host, source.expression).map_err(|_| invalid())?;
    if !source.owner.is_for(arena.id(), bound.file_id())
        || expression.parent != Some(source.owner.node)
        || owner.flags.0 != 0
        || !source_node_is_descendant_of(arena, source.owner, body.body.node)
        || bound.flow_container(source.expression) != Some(body.declaration)
    {
        return Err(invalid().into());
    }
    let nullish = match &owner.data {
        NodeData::BinaryExpression(binary) if owner.kind == SyntaxKind::BinaryExpression => {
            let token = arena.get(binary.operator_token).ok_or_else(invalid)?;
            if token.parent != Some(source.owner.node)
                || token.flags.0 != 0
                || !matches!(token.data, NodeData::Token(_))
                || !matches!(
                    token.kind,
                    SyntaxKind::AmpersandAmpersandToken
                        | SyntaxKind::BarBarToken
                        | SyntaxKind::QuestionQuestionToken
                )
                || source.expression.node != binary.left && source.expression.node != binary.right
            {
                return Err(invalid().into());
            }
            token.kind == SyntaxKind::QuestionQuestionToken && source.expression.node == binary.left
        }
        NodeData::ConditionalExpression(conditional)
            if owner.kind == SyntaxKind::ConditionalExpression
                && conditional.condition == source.expression.node
                && super::source_calls::conditional_call_argument_syntax(arena, source.owner)
                    .is_some() =>
        {
            false
        }
        _ => return Err(invalid().into()),
    };
    if nullish != matches!(source.kind, SourceClassExpressionConditionKind::Nullish(_)) {
        return Err(invalid().into());
    }
    let mut reference = source.expression;
    let mut negated = false;
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(reference) || visited.len() > FLOW_DEPTH_LIMIT {
            return Err(invalid().into());
        }
        let record = class_flow_source_node(store, host, reference).map_err(|_| invalid())?;
        let child = match &record.data {
            NodeData::ParenthesizedExpression(wrapper)
                if record.kind == SyntaxKind::ParenthesizedExpression =>
            {
                wrapper.expression
            }
            NodeData::PrefixUnaryExpression(prefix)
                if !nullish
                    && record.kind == SyntaxKind::PrefixUnaryExpression
                    && prefix.operator == SyntaxKind::ExclamationToken =>
            {
                negated = !negated;
                prefix.operand
            }
            _ => break,
        };
        let child = NodeRef::new(reference.arena, reference.file, child);
        let child_record = class_flow_source_node(store, host, child).map_err(|_| invalid())?;
        if record.flags.0 != 0
            || child_record.parent != Some(reference.node)
            || child_record.range.start < record.range.start
            || child_record.range.end > record.range.end
        {
            return Err(invalid().into());
        }
        reference = child;
    }
    match source.kind {
        SourceClassExpressionConditionKind::Nullish(symbol)
        | SourceClassExpressionConditionKind::Truthiness(symbol, _) => {
            let parameter = body
                .parameters
                .iter()
                .find(|parameter| parameter.symbol == symbol)
                .ok_or_else(invalid)?;
            let record = class_flow_source_node(store, host, parameter.declaration)
                .map_err(|_| invalid())?;
            let NodeData::ParameterDeclaration(parameter_data) = &record.data else {
                return Err(invalid().into());
            };
            if record.kind != SyntaxKind::Parameter
                || record.parent != Some(body.declaration.node)
                || parameter_data.name != parameter.name_node.node
                || parameter_data
                    .type_
                    .map(|node| NodeRef::new(reference.arena, reference.file, node))
                    != parameter.annotation
                || bound.container(parameter.declaration) != Some(body.declaration)
                || bound
                    .symbol(parameter.declaration)
                    .and_then(|raw| store.get_merged_symbol(raw))
                    != Some(symbol)
                || own_class_flow_reference_symbol(store, host, bound, reference)? != Some(symbol)
                || !matches!(
                    arena
                        .get(reference.node)
                        .map(|node| (&node.kind, &node.data)),
                    Some((SyntaxKind::Identifier, NodeData::Identifier(_)))
                )
                || matches!(source.kind, SourceClassExpressionConditionKind::Truthiness(_, expected) if expected != negated)
            {
                return Err(invalid().into());
            }
            Ok(if nullish {
                SourceFlowCondition::Nullish(SourceNullishCondition {
                    expression: source.expression,
                    symbol: Some(symbol),
                })
            } else {
                SourceFlowCondition::Truthiness(SourceTruthinessCondition {
                    expression: source.expression,
                    symbol,
                    negated,
                })
            })
        }
        SourceClassExpressionConditionKind::Call => {
            let NodeData::CallExpression(call) = &expression.data else {
                return Err(invalid().into());
            };
            let syntax = plan_direct_source_call_syntax(arena, store, source.expression)
                .map_err(|_| invalid())?;
            if expression.kind != SyntaxKind::CallExpression
                || expression.flags.0 != 0
                || reference != source.expression
                || negated
                || call.question_dot_token.is_some()
                || call.type_arguments.is_some()
                || call.symbol.is_some()
                || call.facts != 0
                || !syntax.arguments().is_empty()
            {
                return Err(invalid().into());
            }
            Ok(SourceFlowCondition::Unchanged(source.expression))
        }
    }
}

/// The binder drops logical joins without flow effects. Candidate syntax does not
/// make those discarded edges part of a callable's retained flow plan.
fn retained_linear_truthiness_conditions(
    arena: &NodeArena,
    bound: &BoundFile,
    container: NodeRef,
    points: &[NodeRef],
    conditions: Vec<SourceTruthinessCondition>,
) -> Result<Vec<SourceFlowCondition>, SourceFlowError> {
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || !container.is_for(arena.id(), bound.file_id())
    {
        return Err(SourceFlowInvariant::ForeignNode(container).into());
    }
    let graph = bound.flow_graph();
    validate_container(graph, container)?;
    let mut seen = HashSet::new();
    for condition in &conditions {
        let expression = condition.expression;
        validate_bound_node(bound, graph, expression)?;
        if !seen.insert(expression) {
            return Err(SourceFlowInvariant::DuplicateCondition(expression).into());
        }
        let mut reference = expression;
        let mut wrappers = HashSet::new();
        let mut negated = false;
        loop {
            if !wrappers.insert(reference) {
                return Err(SourceFlowInvariant::UnknownCondition(expression).into());
            }
            let inner = match arena
                .get(reference.node)
                .map(|record| (&record.kind, &record.data))
            {
                Some((
                    SyntaxKind::ParenthesizedExpression,
                    NodeData::ParenthesizedExpression(parenthesized),
                )) => parenthesized.expression,
                Some((
                    SyntaxKind::PrefixUnaryExpression,
                    NodeData::PrefixUnaryExpression(prefix),
                )) if prefix.operator == SyntaxKind::ExclamationToken => {
                    negated = !negated;
                    prefix.operand
                }
                _ => break,
            };
            reference = NodeRef::new(reference.arena, reference.file, inner);
        }
        if condition.negated != negated
            || !arena.get(reference.node).is_some_and(|record| {
                record.kind == SyntaxKind::Identifier
                    && matches!(record.data, NodeData::Identifier(_))
            })
        {
            return Err(SourceFlowInvariant::UnknownCondition(expression).into());
        }
        validate_node_container(bound, graph, container, reference)?;
    }

    let retained = retained_condition_edges(bound, container, points, graph.container_end(container))?;
    Ok(conditions
        .into_iter()
        .filter(|condition| retained.contains_key(&condition.expression))
        .map(SourceFlowCondition::Truthiness)
        .collect())
}

fn retained_condition_edges(
    bound: &BoundFile,
    container: NodeRef,
    points: &[NodeRef],
    end: Option<FlowRef>,
) -> Result<HashMap<NodeRef, u8>, SourceFlowError> {
    let graph = bound.flow_graph();
    validate_container(graph, container)?;
    let mut point_flows = HashMap::new();
    let mut point_order = Vec::new();
    for &point in points {
        insert_flow_point(
            bound,
            graph,
            container,
            &mut point_flows,
            &mut point_order,
            point,
            true,
        )?;
    }
    let mut pending = point_order
        .iter()
        .map(|point| point_flows[point])
        .chain(end)
        .collect::<Vec<_>>();
    let mut visited = HashSet::new();
    let mut retained = HashMap::new();
    while let Some(flow) = pending.pop() {
        if !visited.insert(flow) {
            continue;
        }
        let node = flow_node(graph, flow)?;
        match source_flow_kind(flow, node.flags)? {
            SourceFlowKind::Unreachable => validate_unreachable_node(graph, flow, &node)?,
            SourceFlowKind::Start => {}
            kind @ (SourceFlowKind::TrueCondition | SourceFlowKind::FalseCondition) => {
                *retained.entry(ast_payload(flow, &node)?).or_default() |=
                    if kind == SourceFlowKind::TrueCondition {
                        TRUE_CONDITION_EDGE
                    } else {
                        FALSE_CONDITION_EDGE
                    };
                pending.push(linear_antecedent(flow, &node)?);
            }
            SourceFlowKind::Assignment | SourceFlowKind::ArrayMutation | SourceFlowKind::Call => {
                pending.push(linear_antecedent(flow, &node)?);
            }
            SourceFlowKind::BranchLabel | SourceFlowKind::LoopLabel => {
                pending.extend(label_antecedents(flow, &node)?);
            }
        }
    }
    Ok(retained)
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
        .or_else(|| {
            (graph.is_unreachable(point) == Some(true)).then(|| graph.nodes().unreachable())
        })
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
    if semantic == FlowFlags::ARRAY_MUTATION.bits() {
        return Ok(SourceFlowKind::ArrayMutation);
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
    let minimum = match source_flow_kind(flow, node.flags)? {
        SourceFlowKind::LoopLabel => 1,
        SourceFlowKind::BranchLabel => 2,
        _ => return Err(SourceFlowInvariant::InvalidAntecedents(flow).into()),
    };
    // A terminal break can leave the binder's loop label with only its entry edge.
    if node.antecedents.len() < minimum {
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
#[path = "source_flow_counted_loop_tests.rs"]
mod counted_loop_cycle_tests;

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

    fn captured_variable(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let declaration_name = match &record.data {
                    NodeData::VariableDeclaration(data) => data.name,
                    NodeData::ParameterDeclaration(data) => data.name,
                    _ => return None,
                };
                matches!(&parsed.arena.get(declaration_name)?.data,
                NodeData::Identifier(identifier) if identifier.text == name)
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap()
    }

    const SOURCE_LOOP_BACKEDGE_INPUT: &str = concat!(
        "for (var count: 0 | 1 = 0; count < 2; ++count) { ",
        "const unrelated = true; const inside: number = count; }",
    );

    struct SourceLoopBackedgeFixture {
        plan: SourceFlowPlan,
        count: SourceFlowAssignment,
        unrelated: SourceFlowAssignment,
        inside: SourceFlowAssignment,
        annotation: NodeRef,
        initial_annotation: NodeRef,
        header_read: NodeRef,
        body_read: NodeRef,
        label: FlowRef,
        prefix: FlowRef,
    }

    fn source_loop_backedge_fixture(
        parsed: &ParseResult,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
    ) -> SourceLoopBackedgeFixture {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = bound.file_id();
        let reference = |node| NodeRef::new(parsed.arena.id(), file, node);
        let assignment = |name| {
            let declaration = captured_variable(parsed, file, name);
            SourceFlowAssignment {
                declaration,
                symbol: bound.symbol(declaration).unwrap(),
            }
        };
        let count = assignment("count");
        let unrelated = assignment("unrelated");
        let inside = assignment("inside");
        let (statement, iteration) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| match &record.data {
                NodeData::ForStatement(iteration) => Some((reference(node), iteration)),
                _ => None,
            })
            .unwrap();
        let NodeData::BinaryExpression(condition) =
            &parsed.arena.get(iteration.condition.unwrap()).unwrap().data
        else {
            panic!("expected the count comparison")
        };
        let header_read = reference(condition.left);
        let NodeData::PrefixUnaryExpression(update) = &parsed
            .arena
            .get(iteration.incrementor.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected the count update")
        };
        let NodeData::VariableDeclaration(count_data) =
            &parsed.arena.get(count.declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let NodeData::NumericLiteral(initializer) = &parsed
            .arena
            .get(count_data.initializer.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected the written zero initializer")
        };
        assert_eq!(initializer.text, "0");
        let annotation = reference(count_data.type_.unwrap());
        let NodeData::UnionTypeNode(union) = &parsed.arena.get(annotation.node).unwrap().data
        else {
            panic!("expected the written count union")
        };
        let initial_annotation = reference(union.types.nodes[0]);
        let NodeData::VariableDeclaration(inside_data) =
            &parsed.arena.get(inside.declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let body_read = reference(inside_data.initializer.unwrap());
        validate_source_reference(&parsed.arena, bound, store, host, body_read, count.symbol)
            .unwrap();
        let label = bound.flow_at(header_read).unwrap();
        let prefix = bound.flow_at(body_read).unwrap();
        assert_eq!(
            source_flow_kind(label, flow_node(bound.flow_graph(), label).unwrap().flags),
            Ok(SourceFlowKind::LoopLabel)
        );
        let prefix_node = flow_node(bound.flow_graph(), prefix).unwrap();
        assert_eq!(
            source_flow_kind(prefix, prefix_node.flags),
            Ok(SourceFlowKind::Assignment)
        );
        assert_eq!(ast_payload(prefix, &prefix_node), Ok(unrelated.declaration));
        let mut points = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let node = reference(node);
                (record.kind == SyntaxKind::Identifier
                    && source_node_is_descendant_of(&parsed.arena, node, statement.node)
                    && bound.flow_at(node).is_some())
                .then_some(node)
            })
            .collect::<Vec<_>>();
        points.sort_unstable();
        let plan = SourceFlowPlan::preflight_source_statement(
            &parsed.arena,
            bound,
            store,
            host,
            statement,
            points,
            [],
            [count, unrelated, inside],
            [SourceFlowUpdate {
                target: reference(update.operand),
                declaration: count.declaration,
                symbol: count.symbol,
                readonly: false,
            }],
            [],
        )
        .unwrap();
        assert_ne!(prefix, plan.region.unwrap().entry);
        SourceLoopBackedgeFixture {
            plan,
            count,
            unrelated,
            inside,
            annotation,
            initial_annotation,
            header_read,
            body_read,
            label,
            prefix,
        }
    }

    fn source_loop_backedge_types(
        context: &mut CanonicalCheckerContext<'_>,
        fixture: &SourceLoopBackedgeFixture,
    ) -> (TypeId, TypeId, TypeId, TypeId) {
        let declared = context.get_type_from_type_node(fixture.annotation).unwrap();
        let initial = context
            .get_type_from_type_node(fixture.initial_annotation)
            .unwrap();
        assert_eq!(context.type_to_string(initial).unwrap(), "0");
        let TypeData::Union(union) = context.store().type_payload(declared).unwrap().data() else {
            panic!("expected the declared union")
        };
        assert!(union.union.types.contains(&initial));
        let mut members = union
            .union
            .types
            .iter()
            .map(|type_| context.type_to_string(*type_).unwrap())
            .collect::<Vec<_>>();
        members.sort_unstable();
        assert_eq!(members, ["0", "1"]);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        assert_ne!(declared, number);
        assert_ne!(initial, declared);
        (declared, initial, number, bootstrap.regular_true_type)
    }

    #[test]
    fn source_loop_backedge_revisits_assignments_after_completion_invalidates_memo() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(SOURCE_LOOP_BACKEDGE_INPUT);
        let file = FileId::new(32_260);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let fixture = source_loop_backedge_fixture(&parsed, &bound, context.store(), &host);
        let (declared, initial, number, true_type) =
            source_loop_backedge_types(&mut context, &fixture);
        let mut frame = fixture
            .plan
            .frame_with_captured_locals(context.store(), &host, &bound, HashMap::new())
            .unwrap();
        frame
            .complete_source_declaration(
                &host,
                fixture.count.declaration,
                fixture.count.symbol,
                declared,
                initial,
            )
            .unwrap();
        let header = frame
            .snapshot_for_symbols_at(
                context.store_mut_for_test(),
                &globals,
                fixture.header_read,
                [fixture.count.symbol],
            )
            .unwrap();
        assert_eq!(header.type_of(fixture.count.symbol), Some(number));
        assert!(
            frame
                .memo
                .contains_key(&(fixture.label, Some(fixture.count.symbol)))
        );
        frame
            .complete_source_declaration(
                &host,
                fixture.unrelated.declaration,
                fixture.unrelated.symbol,
                true_type,
                true_type,
            )
            .unwrap();
        assert!(frame.memo.is_empty());
        let body = frame
            .snapshot_for_symbols_at(
                context.store_mut_for_test(),
                &globals,
                fixture.body_read,
                [fixture.count.symbol],
            )
            .unwrap();
        assert_eq!(body.type_of(fixture.count.symbol), Some(number));
        assert_eq!(frame.declared_types[&fixture.count.symbol], declared);
        assert_eq!(
            frame.assignment_states[&fixture.inside.declaration],
            SourceFlowAssignmentState::Pending
        );
        let memo = frame.memo.clone();
        let before = (
            context.store().type_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for _ in 0..2 {
            assert_eq!(
                frame.snapshot_for_symbols_at(
                    context.store_mut_for_test(),
                    &globals,
                    fixture.body_read,
                    [fixture.count.symbol],
                ),
                Ok(body.clone())
            );
            assert_eq!(frame.memo, memo);
            assert!(frame.visiting.is_empty());
            assert!(frame.loop_snapshots.is_empty());
            assert_eq!(frame.reference, None);
        }
        assert_eq!(
            (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
        frame
            .complete_source_declaration(
                &host,
                fixture.inside.declaration,
                fixture.inside.symbol,
                number,
                number,
            )
            .unwrap();
        assert!(frame.memo.is_empty());
        let exit = frame
            .snapshot_for_symbols_at_end(
                context.store_mut_for_test(),
                &globals,
                [fixture.count.symbol],
            )
            .unwrap();
        assert_eq!(exit.type_of(fixture.count.symbol), Some(number));
        assert_eq!(frame.declared_types[&fixture.count.symbol], declared);
        assert_eq!(
            context
                .store()
                .type_node_links(fixture.annotation)
                .unwrap()
                .resolved_type,
            Some(declared)
        );
    }

    #[test]
    fn source_loop_backedge_revisits_a_real_false_condition_prefix() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(concat!(
            "declare const stop: boolean; for (;;) { ",
            "if (stop) { break; } const inside: false = stop; continue; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(32_261);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let reference = |node| NodeRef::new(parsed.arena.id(), file, node);
        let statement = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ForStatement).then_some(reference(node))
            })
            .unwrap();
        let condition = parsed
            .arena
            .iter()
            .find_map(|(_, record)| match &record.data {
                NodeData::IfStatement(data) => Some(reference(data.expression)),
                _ => None,
            })
            .unwrap();
        let stop = bound
            .symbol(captured_variable(&parsed, file, "stop"))
            .unwrap();
        let declaration = captured_variable(&parsed, file, "inside");
        let inside = bound.symbol(declaration).unwrap();
        let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let read = reference(data.initializer.unwrap());
        validate_source_reference(&parsed.arena, &bound, context.store(), &host, read, stop)
            .unwrap();
        let prefix = bound.flow_at(read).unwrap();
        let prefix_node = flow_node(bound.flow_graph(), prefix).unwrap();
        assert_eq!(
            source_flow_kind(prefix, prefix_node.flags),
            Ok(SourceFlowKind::FalseCondition)
        );
        assert_eq!(ast_payload(prefix, &prefix_node), Ok(condition));
        let plan = SourceFlowPlan::preflight_source_statement(
            &parsed.arena,
            &bound,
            context.store(),
            &host,
            statement,
            [condition, reference(data.name), read],
            [SourceFlowCondition::Truthiness(SourceTruthinessCondition {
                expression: condition,
                symbol: stop,
                negated: false,
            })],
            [SourceFlowAssignment {
                declaration,
                symbol: inside,
            }],
            [],
            [],
        )
        .unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (boolean, false_type, true_type) = (
            bootstrap.boolean_type,
            bootstrap.regular_false_type,
            bootstrap.regular_true_type,
        );
        let mut frame = plan
            .frame_with_captured_locals(
                context.store(),
                &host,
                &bound,
                [(stop, boolean)].into_iter().collect(),
            )
            .unwrap();
        assert!(frame.memo.is_empty());
        let body = frame
            .snapshot_for_symbols_at(context.store_mut_for_test(), &globals, read, [stop])
            .unwrap();
        assert_eq!(body.type_of(stop), Some(false_type));
        assert_eq!(frame.declared_types[&stop], boolean);
        assert_eq!(
            frame.assignment_states[&declaration],
            SourceFlowAssignmentState::Pending
        );
        frame
            .complete_source_declaration(&host, declaration, inside, false_type, false_type)
            .unwrap();
        assert!(frame.memo.is_empty());
        assert_eq!(
            frame.snapshot_for_symbols_at(context.store_mut_for_test(), &globals, read, [stop]),
            Ok(body)
        );
        let exit = frame
            .snapshot_for_symbols_at_end(context.store_mut_for_test(), &globals, [stop])
            .unwrap();
        assert_eq!(exit.type_of(stop), Some(true_type));
        assert!(frame.visiting.is_empty());
        assert!(frame.loop_snapshots.is_empty());
        assert_eq!(frame.reference, None);
    }

    #[test]
    fn source_loop_backedge_restores_outer_guards_before_success_and_pending_errors() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(SOURCE_LOOP_BACKEDGE_INPUT);
        let file = FileId::new(32_262);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let fixture = source_loop_backedge_fixture(&parsed, &bound, context.store(), &host);
        let (declared, initial, number, _) = source_loop_backedge_types(&mut context, &fixture);
        let mut frame = fixture
            .plan
            .frame_with_captured_locals(context.store(), &host, &bound, HashMap::new())
            .unwrap();
        frame
            .complete_source_declaration(
                &host,
                fixture.count.declaration,
                fixture.count.symbol,
                declared,
                initial,
            )
            .unwrap();
        let state = |frame: &SourceFlowFrame<'_, '_>| {
            (
                frame.base.clone(),
                frame.declared_types.clone(),
                frame.assignment_states.clone(),
                frame.condition_values.clone(),
                frame.call_effects.clone(),
                frame.reference,
            )
        };
        let node = flow_node(bound.flow_graph(), fixture.label).unwrap();
        frame.reference = Some(fixture.count.symbol);
        frame.visiting = [
            (fixture.prefix, frame.reference),
            (fixture.label, frame.reference),
        ]
        .into_iter()
        .collect();
        let outer = frame.visiting.clone();
        let before = state(&frame);
        let result = frame
            .resolve_loop_label(
                context.store_mut_for_test(),
                &globals,
                fixture.label,
                &node,
                0,
            )
            .unwrap();
        assert_eq!(result.type_of(fixture.count.symbol), Some(number));
        assert!(!result.incomplete);
        assert_eq!(frame.visiting, outer);
        assert!(frame.loop_snapshots.is_empty());
        assert_eq!(state(&frame), before);

        frame.reference = Some(fixture.inside.symbol);
        frame.visiting = [
            (fixture.prefix, frame.reference),
            (fixture.label, frame.reference),
        ]
        .into_iter()
        .collect();
        let outer = frame.visiting.clone();
        let before = state(&frame);
        for _ in 0..2 {
            assert_eq!(
                frame.resolve_loop_label(
                    context.store_mut_for_test(),
                    &globals,
                    fixture.label,
                    &node,
                    0
                ),
                Err(SourceFlowInvariant::PendingAssignment(fixture.inside.declaration).into())
            );
            assert_eq!(frame.visiting, outer);
            assert!(frame.loop_snapshots.is_empty());
            assert_eq!(state(&frame), before);
            assert!(frame.memo.values().all(|snapshot| !snapshot.incomplete));
        }
        assert!(!frame.memo.contains_key(&(fixture.label, frame.reference)));
        assert!(!frame.memo.contains_key(&(fixture.prefix, frame.reference)));
        frame.reference = None;
        frame.visiting = [(fixture.plan.region.unwrap().entry, None)]
            .into_iter()
            .collect();
        let outer = frame.visiting.clone();
        assert_eq!(
            frame.snapshot_for_symbols_at(
                context.store_mut_for_test(),
                &globals,
                fixture.body_read,
                [fixture.inside.symbol]
            ),
            Err(SourceFlowInvariant::PendingAssignment(fixture.inside.declaration).into())
        );
        assert_eq!(frame.reference, None);
        assert_eq!(frame.visiting, outer);
        assert!(frame.loop_snapshots.is_empty());
    }

    #[test]
    fn source_loop_backedge_keeps_active_non_label_first_entry_and_depth_guards() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(SOURCE_LOOP_BACKEDGE_INPUT);
        let file = FileId::new(32_263);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let fixture = source_loop_backedge_fixture(&parsed, &bound, context.store(), &host);
        let (declared, initial, _, _) = source_loop_backedge_types(&mut context, &fixture);
        let mut frame = fixture
            .plan
            .frame_with_captured_locals(context.store(), &host, &bound, HashMap::new())
            .unwrap();
        frame
            .complete_source_declaration(
                &host,
                fixture.count.declaration,
                fixture.count.symbol,
                declared,
                initial,
            )
            .unwrap();
        frame.reference = Some(fixture.count.symbol);
        let key = (fixture.prefix, frame.reference);
        assert!(frame.memo.is_empty());
        assert!(frame.loop_snapshots.is_empty());
        assert!(frame.visiting.insert(key));
        // This is an active-key check on a real assignment, not a fabricated graph.
        assert_eq!(
            frame.resolve_flow(context.store_mut_for_test(), &globals, fixture.prefix, 0),
            Err(SourceFlowInvariant::Cycle(fixture.prefix).into())
        );
        assert_eq!(frame.visiting, [key].into_iter().collect());
        let node = flow_node(bound.flow_graph(), fixture.label).unwrap();
        let entry = node.antecedents[0];
        assert_ne!(entry, fixture.plan.region.unwrap().entry);
        assert_eq!(
            ast_payload(entry, &flow_node(bound.flow_graph(), entry).unwrap()),
            Ok(fixture.count.declaration)
        );
        frame.visiting = [(entry, frame.reference)].into_iter().collect();
        assert_eq!(
            frame.resolve_loop_label(
                context.store_mut_for_test(),
                &globals,
                fixture.label,
                &node,
                0
            ),
            Err(SourceFlowInvariant::Cycle(entry).into())
        );
        assert_eq!(
            frame.visiting,
            [(entry, frame.reference)].into_iter().collect()
        );
        assert!(frame.memo.is_empty());
        assert!(frame.loop_snapshots.is_empty());

        frame.visiting = [key, (fixture.label, frame.reference)]
            .into_iter()
            .collect();
        let outer = frame.visiting.clone();
        let first = frame
            .resolve_flow(context.store_mut_for_test(), &globals, entry, 0)
            .unwrap();
        assert_eq!(first.type_of(fixture.count.symbol), Some(initial));
        let memo = frame.memo.clone();
        let backedge = node.antecedents[1];
        let target =
            ast_payload(backedge, &flow_node(bound.flow_graph(), backedge).unwrap()).unwrap();
        assert_eq!(fixture.plan.updates[&target].symbol, fixture.count.symbol);
        assert!(!memo.contains_key(&(backedge, frame.reference)));
        assert_eq!(
            frame.resolve_loop_label(
                context.store_mut_for_test(),
                &globals,
                fixture.label,
                &node,
                FLOW_DEPTH_LIMIT
            ),
            Err(SourceFlowInvariant::DepthLimit(backedge).into())
        );
        assert_eq!(frame.visiting, outer);
        assert_eq!(frame.memo, memo);
        assert!(frame.loop_snapshots.is_empty());
        assert_eq!(frame.reference, Some(fixture.count.symbol));
        assert_eq!(frame.declared_types[&fixture.count.symbol], declared);
    }

    #[test]
    fn ordinary_source_regions_prove_dead_updates_and_pre_class_exits() {
        for (body, dead_update) in [
            ("break;", true),
            ("if (stop) { continue; } break;", false),
            ("if (true) { break; }", true),
        ] {
            let source = format!(
                "declare const stop: boolean; let count = 0; for (;; ++count) {{ {body} }} class Tail {{}}"
            );
            let parsed = parse_source_file(&source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(32_205);
            let context = loop_context(&parsed, file);
            let bound = context.file(file).unwrap().1;
            let (node, data) = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    if let NodeData::ForStatement(data) = &record.data {
                        Some((node, data))
                    } else {
                        None
                    }
                })
                .unwrap();
            let statement = NodeRef::new(parsed.arena.id(), file, node);
            let incrementor = data.incrementor.unwrap();
            let NodeData::PrefixUnaryExpression(update) =
                &parsed.arena.get(incrementor).unwrap().data
            else {
                unreachable!()
            };
            let operand = NodeRef::new(parsed.arena.id(), file, update.operand);
            let class_name = parsed
                .arena
                .iter()
                .find_map(|(_, record)| match &record.data {
                    NodeData::ClassDeclaration(class) => class.name,
                    _ => None,
                })
                .unwrap();
            let class_name = NodeRef::new(parsed.arena.id(), file, class_name);
            let before = (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths(),
            );
            let region =
                source_statement_flow_region(&parsed.arena, bound, context.store(), statement)
                    .unwrap();
            assert_eq!(region.exit, bound.flow_at(class_name).unwrap());
            assert_eq!(
                region.unreachable_incrementor,
                dead_update.then_some(NodeRef::new(parsed.arena.id(), file, incrementor))
            );
            let actual =
                source_region_point_flow(&parsed.arena, bound, operand, Some(region)).unwrap();
            if dead_update {
                assert_eq!(bound.flow_at(operand), None);
                assert_eq!(actual, bound.flow_graph().nodes().unreachable());
                assert_eq!(
                    source_region_point_flow(&parsed.arena, bound, operand, None),
                    Err(SourceFlowInvariant::MissingFlowPoint(operand).into())
                );
            } else {
                assert_eq!(Some(actual), bound.flow_at(operand));
                assert_ne!(actual, bound.flow_graph().nodes().unreachable());
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before
            );
        }
    }

    #[test]
    fn ordinary_assertion_effects_reject_changed_arguments_and_cache_identity() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(concat!(
            "declare function assertString(value: unknown): asserts value is string; ",
            "declare const value: unknown; ",
            "for (;;) { assertString(value); break; }",
        ));
        let file = FileId::new(32_206);
        let mut context = loop_context(&parsed, file);
        context.check_source_file(file).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let (call, argument) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                if let NodeData::CallExpression(call) = &record.data {
                    Some((
                        NodeRef::new(parsed.arena.id(), file, node),
                        NodeRef::new(parsed.arena.id(), file, call.arguments.nodes[0]),
                    ))
                } else {
                    None
                }
            })
            .unwrap();
        let symbol = bound
            .symbol(captured_variable(&parsed, file, "value"))
            .unwrap();
        let signature = context
            .store()
            .signature_links(call)
            .unwrap()
            .effects_signature
            .signature()
            .unwrap();
        let effect = SourceFlowCallEffect::Assertion {
            signature,
            argument,
            symbol,
        };
        assert_eq!(
            validate_source_call_effect(context.store(), &host, &bound, call, effect),
            Ok(())
        );
        let before = (
            context.store().type_len(),
            context.store().checker_link_allocated_lengths(),
        );
        assert_eq!(
            validate_source_call_effect(
                context.store(),
                &host,
                &bound,
                call,
                SourceFlowCallEffect::AssertionNoReference {
                    signature,
                    argument: None
                }
            ),
            Err(SourceFlowInvariant::InvalidCallEffect(call).into())
        );
        assert_eq!(
            validate_source_call_effect(
                context.store(),
                &host,
                &bound,
                call,
                SourceFlowCallEffect::Assertion {
                    signature,
                    argument: call,
                    symbol
                }
            ),
            Err(SourceFlowInvariant::InvalidCallEffect(call).into())
        );
        let mut links = context.store().signature_links(call).unwrap().clone();
        links.effects_signature = EffectsSignatureState::NoEffects;
        assert!(
            context
                .store_mut_for_test()
                .set_signature_links(call, links)
        );
        for _ in 0..2 {
            assert_eq!(
                validate_source_call_effect(context.store(), &host, &bound, call, effect),
                Err(SourceFlowInvariant::InvalidCallEffect(call).into())
            );
        }
        assert_eq!(
            (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
    }

    #[test]
    fn own_class_property_flow_keeps_receiver_identity_and_invalidation() {
        let parsed = parse_source_file(concat!(
            "declare const text: string; ",
            "class Model { value: string | null = null; static value: string | null = null; } ",
            "let model = new Model(); const other = new Model(); ",
            "model.value = text; const narrowed: string = model.value; ",
            "const wrapped: string = (model).value; const separate: string | null = other.value; ",
            "Model.value = text; const staticRead: string = Model.value; ",
            "model.value = null; const secondWrite: null = model.value; ",
            "model = other; const reset: string | null = model.value;",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(202_615);
        let mut context = loop_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let null = bootstrap.null_type;
        let declared = context
            .store()
            .symbol_table(context.globals())
            .unwrap()
            .get_source("Model")
            .unwrap();
        let field = context
            .store()
            .symbol(declared)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("value"))
            .unwrap();
        let union = context
            .store()
            .value_symbol_links(field)
            .unwrap()
            .resolved_type
            .unwrap();
        for (name, expected) in [
            ("narrowed", string),
            ("wrapped", string),
            ("separate", union),
            ("staticRead", string),
            ("secondWrite", null),
            ("reset", union),
        ] {
            let declaration = captured_variable(&parsed, file, name);
            let NodeData::VariableDeclaration(variable) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!();
            };
            let read = NodeRef::new(parsed.arena.id(), file, variable.initializer.unwrap());
            assert_eq!(
                context.get_type_at_location(read).unwrap(),
                expected,
                "{name}"
            );
        }
        assert_eq!(
            context
                .store()
                .value_symbol_links(field)
                .unwrap()
                .resolved_type,
            Some(union)
        );
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().mapper_len(),
            context.store().relation_state_snapshot(),
        );
        context.recheck_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().relation_state_snapshot()
            ),
            before
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the actual checked write and both cache restore paths.
    fn own_class_property_flow_rechecks_written_expression_caches() {
        use crate::semantic::source_properties::plan_own_class_property_write;
        use crate::semantic::{SymbolNodeLinks, TypeNodeLinks, production::GlobalMergeCompletion};

        let parsed = parse_source_file(concat!(
            "declare const text: string; class Model { value: string | null = null; } ",
            "const model = new Model(); model.value = text; const after: string = model.value;",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(202_616);
        let mut context = loop_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let assignments = captured_assignment_syntax(&parsed, file);
        let [(statement, expression, _)] = assignments.as_slice() else {
            panic!("one actual assignment")
        };
        let statement = *statement;
        let expression = *expression;
        let assignment = super::super::assignment::plan_own_class_property_assignment(
            &parsed.arena,
            &bound,
            context.store(),
            &host,
            statement,
        )
        .unwrap()
        .unwrap();
        let plan = plan_own_class_property_write(context.store(), &host, &assignment).unwrap();
        let declaration = captured_variable(&parsed, file, "after");
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!();
        };
        let access = NodeRef::new(parsed.arena.id(), file, variable.initializer.unwrap());
        let receiver = context
            .store()
            .type_node_links(assignment.receiver)
            .unwrap()
            .resolved_type
            .unwrap();
        let assigned = context.store().type_node_links(expression).unwrap().clone();
        let flow_type = context
            .store()
            .type_node_links(access)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            flow_type,
            context.store().intrinsic_bootstrap().unwrap().string_type
        );
        let declared = context
            .store()
            .value_symbol_links(plan.member_source().symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        let options = context.options();
        let mut flow = OwnClassPropertyFlow::default();
        flow.complete_assignment(
            context.store(),
            &host,
            options,
            &plan,
            receiver,
            assigned.resolved_type.unwrap(),
            flow_type,
        )
        .unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let symbols = context
            .store()
            .symbol_node_links(assignment.receiver)
            .unwrap()
            .clone();
        for corrupt_symbol in [false, true] {
            if corrupt_symbol {
                assert!(context.store_mut_for_test().set_symbol_node_links(
                    assignment.receiver,
                    SymbolNodeLinks {
                        resolved_symbol: Some(assignment.class_symbol)
                    }
                ));
            } else {
                assert!(context.store_mut_for_test().set_type_node_links(
                    expression,
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        ..assigned.clone()
                    }
                ));
            }
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().relation_state_snapshot(),
            );
            for _ in 0..2 {
                assert!(
                    matches!(flow.read_type(context.store(), &host, options, access, assignment.receiver_symbol, receiver, plan.member_source().symbol, declared),
                    Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidClassProperty(node))) if node == assignment.left)
                );
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.store().relation_state_snapshot()
                    ),
                    before
                );
                assert!(context.diagnostics().is_empty());
            }
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_node_links(expression, assigned.clone())
            );
            assert!(
                context
                    .store_mut_for_test()
                    .set_symbol_node_links(assignment.receiver, symbols.clone())
            );
            assert_eq!(
                flow.read_type(
                    context.store(),
                    &host,
                    options,
                    access,
                    assignment.receiver_symbol,
                    receiver,
                    plan.member_source().symbol,
                    declared
                ),
                Ok(Some(flow_type))
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep each wrapper's source type, exact diagnostic, and replay together.
    fn own_class_property_flow_matches_real_reference_wrappers() {
        use crate::semantic::{CanonicalCheckerDiagnostic, production::GlobalMergeCompletion};
        use ts_diagnostics::{Diagnostic, message_by_code};

        let parsed = parse_source_file(concat!(
            "declare const text: string; ",
            "class Model { value: string | null = null; static value: string | null = null; } ",
            "const model = new Model(); model.value = text; Model.value = text; ",
            "const nonNull: string = model!.value; ",
            "const satisfied: string = (model satisfies Model).value; ",
            "const staticRead: string = Model!.value; ",
            "const comma = (model.value, model);",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(202_619);
        let mut context = loop_context(&parsed, file);
        context.check_source_file(file).unwrap();
        let satisfied = captured_variable(&parsed, file, "satisfied");
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(satisfied.node).unwrap().data
        else {
            unreachable!()
        };
        let name = NodeRef::new(parsed.arena.id(), file, variable.name);
        let range = parsed.arena.get(name.node).unwrap().range;
        assert_eq!(
            &parsed.arena.source_text().unwrap()[usize::try_from(range.start.get()).unwrap()
                ..usize::try_from(range.end.get()).unwrap()],
            "satisfied"
        );
        let mut diagnostic =
            Diagnostic::with_arguments(message_by_code(2322).unwrap(), ["string | null", "string"]);
        diagnostic
            .details
            .push("  Type 'null' is not assignable to type 'string'.".to_owned());
        let expected_diagnostic = CanonicalCheckerDiagnostic {
            node: Some(name),
            range_override: None,
            diagnostic,
            related_information: Vec::new(),
        };
        assert_eq!(
            expected_diagnostic.diagnostic.render().unwrap(),
            concat!(
                "Type 'string | null' is not assignable to type 'string'.\n",
                "  Type 'null' is not assignable to type 'string'."
            )
        );
        assert_eq!(
            context.diagnostics().as_slice(),
            std::slice::from_ref(&expected_diagnostic)
        );
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let null = context.store().intrinsic_bootstrap().unwrap().null_type;
        let class = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(record.data, NodeData::ClassDeclaration(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let class = context.file(file).unwrap().1.symbol(class).unwrap();
        let property = context
            .store()
            .symbol(class)
            .unwrap()
            .members()
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("value"))
            .unwrap();
        let declaration = context
            .store()
            .symbol(property)
            .unwrap()
            .value_declaration()
            .unwrap();
        let NodeData::PropertyDeclaration(property_node) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let annotation = NodeRef::new(parsed.arena.id(), file, property_node.type_.unwrap());
        let declared = context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            context
                .store()
                .type_node_links(annotation)
                .unwrap()
                .resolved_type,
            Some(declared)
        );
        let TypeData::Union(union) = context.store().type_payload(declared).unwrap().data() else {
            panic!("the instance field must keep its canonical nullable union")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&string));
        assert!(union.union.types.contains(&null));
        let mut reads = Vec::new();
        for name in ["nonNull", "satisfied", "staticRead"] {
            let declaration = captured_variable(&parsed, file, name);
            let NodeData::VariableDeclaration(variable) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!();
            };
            let read = NodeRef::new(parsed.arena.id(), file, variable.initializer.unwrap());
            let expected = if name == "satisfied" {
                declared
            } else {
                string
            };
            assert_eq!(
                context.get_type_at_location(read).unwrap(),
                expected,
                "{name}"
            );
            reads.push((read, expected));
        }
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let comma = captured_variable(&parsed, file, "comma");
        let NodeData::VariableDeclaration(variable) = &parsed.arena.get(comma.node).unwrap().data
        else {
            unreachable!();
        };
        let receiver = NodeRef::new(parsed.arena.id(), file, variable.initializer.unwrap());
        let model = bound
            .symbol(captured_variable(&parsed, file, "model"))
            .unwrap();
        assert_eq!(
            own_class_flow_reference_symbol(context.store(), &host, &bound, receiver),
            Ok(Some(model))
        );
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().mapper_len(),
            context.store().checker_link_allocated_lengths(),
            context.store().relation_state_snapshot(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            context.diagnostics().as_slice(),
            std::slice::from_ref(&expected_diagnostic)
        );
        for (read, expected) in reads {
            assert_eq!(context.get_type_at_location(read).unwrap(), expected);
        }
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().relation_state_snapshot()
            ),
            before
        );
    }

    #[test]
    fn own_class_property_flow_keeps_affected_object_bindings_unavailable() {
        use crate::semantic::source::{SourceCheckError, UnsupportedSourceSyntax};
        use crate::semantic::variables::VariableUnsupported;

        let parsed = parse_source_file(
            "declare const text: string; class Model { value: string | null = null; } const model = new Model(); model.value = text; const { value } = model; const after: string = value;",
        );
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(202_620);
        let mut context = loop_context(&parsed, file);
        let (element, name, pattern) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::BindingElement(binding) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, binding.name?),
                    NodeRef::new(parsed.arena.id(), file, record.parent?),
                ))
            })
            .unwrap();
        let symbol = context.file(file).unwrap().1.symbol(element).unwrap();
        for _ in 0..2 {
            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Variable(VariableUnsupported::BindingPattern(pattern))
                ))
            );
            assert!(context.diagnostics().is_empty());
            assert!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .is_none_or(|links| { links == &crate::semantic::ValueSymbolLinks::default() })
            );
            for node in [element, name] {
                assert!(
                    context
                        .store()
                        .type_node_links(node)
                        .is_none_or(|links| { links == &TypeNodeLinks::default() })
                );
            }
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .is_none_or(|links| !links.type_checked)
            );
        }
    }

    #[test]
    fn own_class_property_flow_preserves_unaffected_object_bindings() {
        let parsed = parse_source_file(concat!(
            "declare const text: string; ",
            "class Model { value: string | null = null; other = 0; } ",
            "const model = new Model(); const second = new Model(); model.value = text; ",
            "const { other } = model; const numeric: number = other; ",
            "const { value: separate } = second; const nullable: string | null = separate;",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(202_621);
        let mut context = loop_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        for (name, expected) in [("numeric", "number"), ("nullable", "string | null")] {
            let declaration = captured_variable(&parsed, file, name);
            let NodeData::VariableDeclaration(variable) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!();
            };
            let read = NodeRef::new(parsed.arena.id(), file, variable.initializer.unwrap());
            let type_ = context.get_type_at_location(read).unwrap();
            assert_eq!(context.type_to_string(type_).unwrap(), expected);
        }
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
            context.store().relation_state_snapshot(),
        );
        context.recheck_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().relation_state_snapshot()
            ),
            before
        );
    }

    #[test]
    fn own_class_property_flow_keeps_unknown_calls_unavailable() {
        use crate::semantic::source::{SourceCheckError, UnsupportedSourceSyntax};

        let parsed = parse_source_file(concat!(
            "declare function visit(): void; declare const text: string; ",
            "class Model { value: string | null = null; } ",
            "const model = new Model(); model.value = text; visit(); ",
            "const after: string = model.value;",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(202_617);
        let mut context = loop_context(&parsed, file);
        let declaration = captured_variable(&parsed, file, "after");
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!();
        };
        let access = NodeRef::new(parsed.arena.id(), file, variable.initializer.unwrap());
        for _ in 0..2 {
            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Class(access)
                ))
            );
            assert!(context.diagnostics().is_empty());
            assert!(
                context
                    .store()
                    .type_node_links(access)
                    .is_none_or(|links| links.resolved_type.is_none())
            );
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .is_none_or(|links| !links.type_checked)
            );
        }
    }

    #[test]
    fn own_class_property_flow_keeps_computed_reads_unavailable() {
        use crate::semantic::source::{SourceCheckError, UnsupportedSourceSyntax};

        let parsed = parse_source_file(concat!(
            "declare const text: string; class Model { value: string | null = null; } ",
            "const model = new Model(); model.value = text; ",
            "const after: string = model['value'];",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(202_618);
        let mut context = loop_context(&parsed, file);
        let declaration = captured_variable(&parsed, file, "after");
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!();
        };
        let access = NodeRef::new(parsed.arena.id(), file, variable.initializer.unwrap());
        let unsupported = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Element(access));
        for _ in 0..2 {
            assert_eq!(context.check_source_file(file), Err(unsupported));
            assert!(context.diagnostics().is_empty());
            assert!(
                context
                    .store()
                    .type_node_links(access)
                    .is_none_or(|links| { links == &TypeNodeLinks::default() })
            );
            assert!(
                context
                    .store()
                    .symbol_node_links(access)
                    .is_none_or(|links| { links == &crate::semantic::SymbolNodeLinks::default() })
            );
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .is_none_or(|links| !links.type_checked)
            );
        }
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            access,
            TypeNodeLinks {
                resolved_type: Some(string),
                ..TypeNodeLinks::default()
            }
        ));
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for _ in 0..2 {
            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Class(access))
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before
            );
            assert!(context.diagnostics().is_empty());
        }
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(access, TypeNodeLinks::default())
        );
        assert_eq!(context.check_source_file(file), Err(unsupported));
        assert!(context.diagnostics().is_empty());
    }

    fn captured_assignment_syntax(
        parsed: &ParseResult,
        file: FileId,
    ) -> Vec<(NodeRef, NodeRef, NodeRef)> {
        let mut assignments = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::BinaryExpression(binary) = &record.data else {
                    return None;
                };
                if parsed.arena.get(binary.operator_token)?.kind != SyntaxKind::EqualsToken {
                    return None;
                }
                Some((
                    NodeRef::new(parsed.arena.id(), file, record.parent?),
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, binary.left),
                ))
            })
            .collect::<Vec<_>>();
        assignments.sort_by_key(|(_, expression, _)| {
            parsed.arena.get(expression.node).unwrap().range.start
        });
        assignments
    }

    fn captured_arrow_statements(
        parsed: &ParseResult,
        file: FileId,
        arrow: NodeRef,
    ) -> Vec<NodeRef> {
        let NodeData::ArrowFunction(data) = &parsed.arena.get(arrow.node).unwrap().data else {
            panic!("expected an arrow")
        };
        let NodeData::Block(body) = &parsed.arena.get(data.body).unwrap().data else {
            panic!("expected an arrow block")
        };
        body.statements
            .nodes
            .iter()
            .map(|node| NodeRef::new(parsed.arena.id(), file, *node))
            .collect()
    }

    #[test]
    fn captured_local_proof_rechecks_enclosing_owner_and_cached_binding() {
        use crate::semantic::{SymbolNodeLinks, production::GlobalMergeCompletion};

        let parsed = parse_source_file(concat!(
            "function outer() { let value: number = 0; let other: number = 0; ",
            "const reset = () => { value = 1; }; ",
            "const nested = () => { return { reset: () => { value = 2; } }; }; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(32_201);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let declaration = captured_variable(&parsed, file, "value");
        let other = bound
            .symbol(captured_variable(&parsed, file, "other"))
            .unwrap();
        let symbol = bound.symbol(declaration).unwrap();
        let declaring_callable = bound.container(declaration).unwrap();
        let value_links = context.store().value_symbol_links(symbol).cloned();
        assert!(
            value_links
                .as_ref()
                .is_none_or(|links| links.resolved_type.is_none())
        );
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        let syntax = captured_assignment_syntax(&parsed, file);
        assert_eq!(syntax.len(), 2);
        let proofs = syntax
            .iter()
            .map(|(_, _, target)| {
                let writer = bound.flow_container(*target).unwrap();
                let local =
                    plan_source_captured_local(context.store(), &host, writer, *target, symbol)
                        .unwrap()
                        .unwrap();
                assert_eq!(local.target(), *target);
                assert_eq!(local.declaration(), declaration);
                assert_eq!(local.symbol(), symbol);
                assert_eq!(local.declaring_callable(), declaring_callable);
                assert_eq!(local.writing_callable(), writer);
                let NodeData::VariableDeclaration(data) =
                    &parsed.arena.get(declaration.node).unwrap().data
                else {
                    panic!("expected the captured let")
                };
                assert_eq!(local.annotation().node, data.type_.unwrap());
                assert_eq!(
                    host.node(local.annotation()).unwrap().parent,
                    Some(declaration.node)
                );
                assert_ne!(bound.symbol(writer), Some(symbol));
                local
            })
            .collect::<Vec<_>>();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
        assert_eq!(
            context.store().value_symbol_links(symbol).cloned(),
            value_links
        );

        for local in proofs {
            for _ in 0..2 {
                assert_eq!(
                    validate_source_captured_local(context.store(), &host, &local),
                    Ok(())
                );
            }
            for (change, mut changed) in [local; 4].into_iter().enumerate() {
                match change {
                    0 => changed.annotation = declaration,
                    1 => changed.declaring_callable = local.writing_callable,
                    2 => changed.writing_callable = declaring_callable,
                    3 => changed.symbol = other,
                    _ => unreachable!(),
                }
                assert_eq!(
                    validate_source_captured_local(context.store(), &host, &changed),
                    Err(SourceFlowInvariant::InvalidCapturedLocal(local.target).into())
                );
            }
            let arrow_symbol = bound.symbol(local.writing_callable).unwrap();
            assert!(context.store_mut_for_test().set_symbol_declarations(
                arrow_symbol,
                Some(vec![local.writing_callable]),
                Some(declaring_callable),
            ));
            let poisoned = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            for _ in 0..2 {
                assert_eq!(
                    validate_source_captured_local(context.store(), &host, &local),
                    Err(SourceFlowInvariant::InvalidCapturedLocal(local.target).into())
                );
            }
            assert_eq!(
                context
                    .store()
                    .symbol(arrow_symbol)
                    .unwrap()
                    .value_declaration(),
                Some(declaring_callable)
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                poisoned
            );
            assert!(context.store_mut_for_test().set_symbol_declarations(
                arrow_symbol,
                Some(vec![local.writing_callable]),
                Some(local.writing_callable),
            ));
            assert_eq!(
                validate_source_captured_local(context.store(), &host, &local),
                Ok(())
            );

            // The cache carries an existing binder symbol, not a new declaration.
            assert!(context.store_mut_for_test().set_symbol_node_links(
                local.target,
                SymbolNodeLinks {
                    resolved_symbol: Some(symbol)
                }
            ));
            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert_eq!(
                validate_source_captured_local(context.store(), &host, &local),
                Ok(())
            );
            assert!(context.store_mut_for_test().set_symbol_node_links(
                local.target,
                SymbolNodeLinks {
                    resolved_symbol: Some(other)
                }
            ));
            for _ in 0..2 {
                assert_eq!(
                    validate_source_captured_local(context.store(), &host, &local),
                    Err(SourceFlowInvariant::InvalidCapturedLocal(local.target).into())
                );
            }
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(local.target)
                    .unwrap()
                    .resolved_symbol,
                Some(other)
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                warm
            );
            assert!(context.store_mut_for_test().set_symbol_node_links(
                local.target,
                SymbolNodeLinks {
                    resolved_symbol: Some(symbol)
                }
            ));
            assert_eq!(
                plan_source_captured_local(
                    context.store(),
                    &host,
                    local.writing_callable,
                    local.target,
                    symbol
                ),
                Ok(Some(local))
            );
        }
        assert_eq!(
            context.store().value_symbol_links(symbol).cloned(),
            value_links
        );
    }

    #[test]
    fn captured_declaring_callable_owner_is_checked_on_cold_and_retained_plans() {
        use crate::semantic::production::GlobalMergeCompletion;

        for (index, source) in [
            "function outer() { let value: number = 0; const write = () => { value = 1; }; }",
            "const outer = () => { let value: number = 0; const write = () => { value = 1; }; };",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(32_220 + u32::try_from(index).unwrap());
            let mut context = loop_context(&parsed, file);
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(context.options().name_resolution),
            )
            .unwrap();
            let declaration = captured_variable(&parsed, file, "value");
            let symbol = bound.symbol(declaration).unwrap();
            let syntax = captured_assignment_syntax(&parsed, file);
            let [(statement, expression, target)] = syntax.as_slice() else {
                panic!("expected one write");
            };
            let writer = bound.flow_container(*target).unwrap();
            let local = plan_source_captured_local(context.store(), &host, writer, *target, symbol)
                .unwrap()
                .unwrap();
            let declaring = local.declaring_callable;
            let owner = bound.symbol(declaring).unwrap();
            let declarations = context
                .store()
                .symbol(owner)
                .unwrap()
                .declarations()
                .unwrap()
                .to_vec();
            let value = context.store().symbol(owner).unwrap().value_declaration();
            let input = context.store().intrinsic_bootstrap().unwrap().number_type;
            let assignment = SourceFlowCapturedAssignment {
                statement: *statement,
                expression: *expression,
                local,
            };
            let plan = SourceFlowPlan::preflight_linear_with_captured_effects(
                &parsed.arena,
                &bound,
                context.store(),
                &host,
                writer,
                [*statement],
                [],
                [],
                [],
                [],
                [assignment],
                [],
            )
            .unwrap();
            for _ in 0..2 {
                assert!(context.store_mut_for_test().set_symbol_declarations(
                    owner,
                    Some(declarations.clone()),
                    Some(writer)
                ));
                let before = (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                );
                assert_eq!(
                    plan_source_captured_local(context.store(), &host, writer, *target, symbol),
                    Err(SourceFlowInvariant::InvalidCapturedLocal(*target).into())
                );
                assert!(
                    matches!(plan.frame_with_captured_locals(context.store(), &host, &bound,
                    [(symbol, input)].into_iter().collect()),
                    Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidCapturedLocal(node))) if node == *target)
                );
                assert_eq!(
                    context.store().symbol(owner).unwrap().value_declaration(),
                    Some(writer)
                );
                assert_eq!(
                    context.store().symbol(owner).unwrap().declarations(),
                    Some(declarations.as_slice())
                );
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().signature_len(),
                        context.store().checker_link_allocated_lengths()
                    ),
                    before
                );
                assert!(context.store_mut_for_test().set_symbol_declarations(
                    owner,
                    Some(declarations.clone()),
                    value
                ));
                assert_eq!(
                    plan_source_captured_local(context.store(), &host, writer, *target, symbol),
                    Ok(Some(local))
                );
                assert!(
                    plan.frame_with_captured_locals(
                        context.store(),
                        &host,
                        &bound,
                        [(symbol, input)].into_iter().collect()
                    )
                    .is_ok()
                );
            }
        }
    }

    #[test]
    fn captured_local_proof_excludes_unapproved_binding_and_writer_shapes() {
        use crate::semantic::production::GlobalMergeCompletion;

        for (index, source) in [
            "function outer(value: number) { const write = () => { value = 1; }; }",
            "function outer() { var value: number = 0; const write = () => { value = 1; }; }",
            "function outer() { const value: number = 0; const write = () => { value = 1; }; }",
            "function outer() { let value = 0; const write = () => { value = 1; }; }",
            "let value: number = 0; const write = () => { value = 1; };",
            "function outer() { const write = () => { let value: number = 0; value = 1; }; }",
            "function outer() { const write = () => { value = 1; }; let value: number = 0; }",
            "function outer() { let value: number = 0; (() => { value = 1; })(); }",
            "function outer() { let value: number = 0; const write = function () { value = 1; }; }",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(32_210 + u32::try_from(index).unwrap());
            let context = loop_context(&parsed, file);
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(context.options().name_resolution),
            )
            .unwrap();
            let declaration = captured_variable(&parsed, file, "value");
            let symbol = bound.symbol(declaration).unwrap();
            let syntax = captured_assignment_syntax(&parsed, file);
            let [(_, _, target)] = syntax.as_slice() else {
                panic!("expected one write");
            };
            let writer = bound.flow_container(*target).unwrap();
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            for _ in 0..2 {
                assert_eq!(
                    plan_source_captured_local(context.store(), &host, writer, *target, symbol),
                    Ok(None),
                    "{source}"
                );
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the method, capture, and retained flow damage checks together.
    fn object_method_captured_write_rechecks_owner_binding_and_flow() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(concat!(
            "function outer() { let value: string | number = 'old'; let other: number = 0; ",
            "let values: number[] = []; ",
            "const object = { write(): void { value = 1; value; }, ",
            "append(): void { values.push(1); } }; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(202_940);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let declaration = captured_variable(&parsed, file, "value");
        let symbol = bound.symbol(declaration).unwrap();
        let other = bound
            .symbol(captured_variable(&parsed, file, "other"))
            .unwrap();
        let syntax = captured_assignment_syntax(&parsed, file);
        let [(statement, expression, target)] = syntax.as_slice() else {
            panic!("expected one captured write");
        };
        let (statement, expression, target) = (*statement, *expression, *target);
        let writer = bound.flow_container(target).unwrap();
        let owner = bound.symbol(writer).unwrap();
        let local = plan_source_captured_local(context.store(), &host, writer, target, symbol)
            .unwrap()
            .unwrap();
        assert_eq!(local.declaration(), declaration);
        assert_eq!(local.writing_callable(), writer);
        assert_eq!(
            local.declaring_callable(),
            bound.container(declaration).unwrap()
        );
        let NodeData::MethodDeclaration(method) = &parsed.arena.get(writer.node).unwrap().data
        else {
            panic!("expected the real object method");
        };
        let NodeData::Block(block) = &parsed.arena.get(method.body.unwrap()).unwrap().data else {
            panic!("expected the method block");
        };
        let points = block
            .statements
            .nodes
            .iter()
            .map(|node| NodeRef::new(writer.arena, file, *node))
            .collect::<Vec<_>>();
        let [before, after] = points.as_slice() else {
            panic!("expected the write and following read");
        };
        assert_eq!(*before, statement);
        let assignment = SourceFlowCapturedAssignment {
            statement,
            expression,
            local,
        };
        let plan = SourceFlowPlan::preflight_linear_with_captured_effects(
            &parsed.arena,
            &bound,
            context.store(),
            &host,
            writer,
            points.clone(),
            [],
            [],
            [],
            [],
            [assignment],
            [],
        )
        .unwrap();
        assert_eq!(plan.start_payload, Some(writer));
        assert_eq!(plan.end, bound.flow_graph().container_end(writer));
        assert!(plan.assignment_declarations.is_empty());
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (input, number) = (bootstrap.string_or_number_type, bootstrap.number_type);
        let outer = [(symbol, input), (other, number)]
            .into_iter()
            .collect::<SourceFlowTypes>();
        for _ in 0..2 {
            let mut frame = plan
                .frame_with_captured_locals(context.store(), &host, &bound, outer.clone())
                .unwrap();
            assert_eq!(
                frame
                    .snapshot_at(context.store_mut_for_test(), &globals, statement)
                    .unwrap()
                    .types(),
                &outer
            );
            assert_eq!(
                frame.snapshot_at(context.store_mut_for_test(), &globals, *after),
                Err(SourceFlowInvariant::PendingAssignment(target).into())
            );
            frame.complete_assignment(target, symbol, number).unwrap();
            let result = frame
                .snapshot_at(context.store_mut_for_test(), &globals, *after)
                .unwrap();
            assert_eq!(result.type_of(symbol), Some(number));
            assert_eq!(result.type_of(other), Some(number));
            assert_eq!(outer.get(&symbol), Some(&input));
        }
        let reject = |store: &CanonicalTypeMapperStore| {
            let before = format!("{store:?}");
            for _ in 0..2 {
                assert_eq!(
                    validate_source_captured_local(store, &host, &local),
                    Err(SourceFlowInvariant::InvalidCapturedLocal(target).into())
                );
                assert!(
                    matches!(plan.frame_with_captured_locals(store, &host, &bound, outer.clone()),
                    Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidCapturedLocal(node))) if node == target)
                );
                assert_eq!(format!("{store:?}"), before);
            }
        };
        let store = context.store_mut_for_test();
        let parent = store.symbol(owner).unwrap().parent().unwrap();
        let name = store.symbol(owner).unwrap().name().to_owned();
        let members = store.symbol(parent).unwrap().members().unwrap();
        let flags = store.symbol(owner).unwrap().flags();
        let checks = store.symbol(owner).unwrap().check_flags();
        for warm in [false, true] {
            if warm {
                assert!(store.set_symbol_node_links(
                    target,
                    SymbolNodeLinks {
                        resolved_symbol: Some(symbol)
                    }
                ));
            }
            assert_eq!(validate_source_captured_local(store, &host, &local), Ok(()));
            assert!(store.set_symbol_relationships(owner, None, None, None, None));
            reject(store);
            assert!(store.set_symbol_relationships(owner, None, None, Some(parent), None));
            assert_eq!(validate_source_captured_local(store, &host, &local), Ok(()));
            assert!(store.set_symbol_flags(owner, SymbolFlags::PROPERTY, checks));
            reject(store);
            assert!(store.set_symbol_flags(owner, flags, checks));
            assert_eq!(validate_source_captured_local(store, &host, &local), Ok(()));
            assert_eq!(
                store.insert_symbol(members, name.clone(), other),
                Some(Some(owner))
            );
            reject(store);
            assert_eq!(
                store.insert_symbol(members, name.clone(), owner),
                Some(Some(other))
            );
            assert_eq!(validate_source_captured_local(store, &host, &local), Ok(()));
        }
        assert!(store.set_symbol_node_links(
            target,
            SymbolNodeLinks {
                resolved_symbol: Some(other)
            }
        ));
        reject(store);
        assert!(store.set_symbol_node_links(
            target,
            SymbolNodeLinks {
                resolved_symbol: Some(symbol)
            }
        ));
        assert_eq!(validate_source_captured_local(store, &host, &local), Ok(()));
        assert!(
            plan.frame_with_captured_locals(store, &host, &bound, outer.clone())
                .is_ok()
        );
        for (index, mut changed) in [local; 3].into_iter().enumerate() {
            match index {
                0 => changed.annotation = declaration,
                1 => changed.symbol = other,
                2 => changed.writing_callable = local.declaring_callable,
                _ => unreachable!(),
            }
            assert_eq!(
                validate_source_captured_local(store, &host, &changed),
                Err(SourceFlowInvariant::InvalidCapturedLocal(target).into())
            );
        }
        let values = captured_variable(&parsed, file, "values");
        let values_symbol = bound.symbol(values).unwrap();
        let (call, receiver) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::CallExpression(call) = &record.data else {
                    return None;
                };
                let NodeData::PropertyAccessExpression(property) =
                    &parsed.arena.get(call.expression)?.data
                else {
                    return None;
                };
                Some((
                    NodeRef::new(writer.arena, file, node),
                    NodeRef::new(writer.arena, file, property.expression),
                ))
            })
            .unwrap();
        let append = bound.flow_container(receiver).unwrap();
        assert_ne!(append, writer);
        let captured = plan_source_captured_local(store, &host, append, receiver, values_symbol)
            .unwrap()
            .unwrap();
        let origin = SourceCapturedFlowOrigin::ArrayMutation(SourceFlowCapturedArrayMutation {
            mutation: SourceFlowArrayMutation {
                call,
                receiver,
                declaration: values,
                symbol: values_symbol,
            },
            local: captured,
        });
        let before = format!("{store:?}");
        for _ in 0..2 {
            assert_eq!(
                validate_captured_flow_origin(
                    &parsed.arena,
                    &bound,
                    store,
                    &host,
                    append,
                    origin,
                    None,
                ),
                Err(SourceFlowInvariant::InvalidArrayMutation(call).into())
            );
            assert_eq!(format!("{store:?}"), before);
        }
    }

    #[test]
    fn captured_assignment_flow_keeps_child_state_and_revalidates_origins() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(concat!(
            "function outer() { let value: string | number = 'old'; let other: number = 0; ",
            "const reset = () => { value = 1; value; }; ",
            "const nested = () => { return { reset: () => { value = 2; value; } }; }; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(32_202);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let declaration = captured_variable(&parsed, file, "value");
        let symbol = bound.symbol(declaration).unwrap();
        let other = bound
            .symbol(captured_variable(&parsed, file, "other"))
            .unwrap();
        let (input, number) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_or_number_type, bootstrap.number_type)
        };
        let outer = [(symbol, input), (other, number)]
            .into_iter()
            .collect::<SourceFlowTypes>();
        let value_links = context.store().value_symbol_links(symbol).cloned();
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for (statement, expression, target) in captured_assignment_syntax(&parsed, file) {
            let writer = bound.flow_container(target).unwrap();
            let local = plan_source_captured_local(context.store(), &host, writer, target, symbol)
                .unwrap()
                .unwrap();
            let assignment = SourceFlowCapturedAssignment {
                statement,
                expression,
                local,
            };
            let statements = captured_arrow_statements(&parsed, file, writer);
            assert_eq!(statements.len(), 2);
            let after = statements[1];
            let plan = SourceFlowPlan::preflight_linear_with_captured_effects(
                &parsed.arena,
                &bound,
                context.store(),
                &host,
                writer,
                statements,
                [],
                [],
                [],
                [],
                [assignment],
                [],
            )
            .unwrap();
            assert_eq!(plan.start_payload, Some(writer));
            assert_eq!(plan.end, bound.flow_graph().container_end(writer));
            assert!(plan.assignment_declarations.is_empty());
            assert_eq!(
                plan.captured_origins.get(&target),
                Some(&SourceCapturedFlowOrigin::Assignment(assignment))
            );
            assert!(matches!(plan.frame(&bound, outer.clone()),
                Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidCapturedLocal(node))) if node == target));
            assert!(
                matches!(plan.frame_with_captured_locals(context.store(), &host, &bound, HashMap::new()),
                Err(SourceFlowError::Invariant(SourceFlowInvariant::MissingCurrentType(actual))) if actual == symbol)
            );
            assert!(matches!(SourceFlowPlan::preflight_linear(
                &parsed.arena, &bound, context.store(), writer, [], [],
                [SourceFlowParameterAssignment { target, parameter: declaration, symbol }], [],
            ), Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidParameterAssignment(node))) if node == target));

            for _ in 0..2 {
                let mut frame = plan
                    .frame_with_captured_locals(context.store(), &host, &bound, outer.clone())
                    .unwrap();
                assert_eq!(
                    frame
                        .snapshot_at(context.store_mut_for_test(), &globals, statement)
                        .unwrap()
                        .types(),
                    &outer
                );
                assert_eq!(
                    frame.snapshot_at(context.store_mut_for_test(), &globals, after),
                    Err(SourceFlowInvariant::PendingAssignment(target).into())
                );
                frame.complete_assignment(target, symbol, number).unwrap();
                let after_write = frame
                    .snapshot_at(context.store_mut_for_test(), &globals, after)
                    .unwrap();
                assert_eq!(after_write.type_of(symbol), Some(number));
                assert_eq!(after_write.type_of(other), Some(number));
                assert_eq!(outer.get(&symbol), Some(&input));
                assert_eq!(
                    frame
                        .snapshot_at(context.store_mut_for_test(), &globals, after)
                        .unwrap(),
                    after_write
                );
            }
            let flow = bound
                .flow_graph()
                .nodes()
                .iter()
                .enumerate()
                .find_map(|(index, node)| {
                    (node.payload == Some(FlowNodePayload::Ast(target))
                        && node.flags.bits() & !FLOW_METADATA_BITS == FlowFlags::ASSIGNMENT.bits())
                    .then(|| {
                        bound
                            .flow_graph()
                            .nodes()
                            .flow_ref(FlowNodeId(u32::try_from(index).unwrap()))
                            .unwrap()
                    })
                })
                .unwrap();
            let row = bound.flow_graph().nodes().get(flow).unwrap();
            let origin = SourceCapturedFlowOrigin::Assignment(assignment);
            assert_eq!(
                validate_captured_origin_flow_node(origin, flow, row),
                Ok(())
            );
            for change in 0..3 {
                let mut damaged = row.clone();
                match change {
                    0 => damaged.flags = FlowFlags::ARRAY_MUTATION,
                    1 => damaged.payload = Some(FlowNodePayload::Ast(declaration)),
                    2 => damaged.antecedent = None,
                    _ => unreachable!(),
                }
                for _ in 0..2 {
                    assert!(validate_captured_origin_flow_node(origin, flow, &damaged).is_err());
                }
                assert_eq!(
                    validate_captured_origin_flow_node(origin, flow, row),
                    Ok(())
                );
            }
            for change in 0..5 {
                let mut damaged = plan.clone();
                match change {
                    0 => {
                        let SourceCapturedFlowOrigin::Assignment(origin) =
                            damaged.captured_origins.get_mut(&target).unwrap()
                        else {
                            unreachable!()
                        };
                        origin.local.annotation = declaration;
                    }
                    1 => {
                        damaged.assignment_declarations.insert(target, declaration);
                    }
                    2 => {
                        damaged.assignments.get_mut(&target).unwrap().symbol = other;
                    }
                    3 => {
                        damaged.end = Some(damaged.start);
                    }
                    4 => {
                        damaged.captured_origins.remove(&target);
                    }
                    _ => unreachable!(),
                }
                for _ in 0..2 {
                    let result = damaged.frame_with_captured_locals(
                        context.store(),
                        &host,
                        &bound,
                        outer.clone(),
                    );
                    assert!(result.is_err(), "change {change}");
                }
                assert!(
                    plan.frame_with_captured_locals(context.store(), &host, &bound, outer.clone())
                        .is_ok()
                );
            }
        }
        assert_eq!(
            context.store().value_symbol_links(symbol).cloned(),
            value_links
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
    }

    #[test]
    fn captured_array_flow_requires_mutation_and_call_but_not_an_assignment_rhs_call() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(concat!(
            "function outer() { let values: number[] = []; ",
            "const append = () => { values.push(1); values; }; ",
            "const reset = () => { values = values.filter((value: number): boolean => true); values; }; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(32_203);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let declaration = captured_variable(&parsed, file, "values");
        let symbol = bound.symbol(declaration).unwrap();
        let (call, receiver) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::CallExpression(call) = &record.data else {
                    return None;
                };
                let NodeData::PropertyAccessExpression(property) =
                    &parsed.arena.get(call.expression)?.data
                else {
                    return None;
                };
                matches!(&parsed.arena.get(property.name)?.data,
                NodeData::Identifier(identifier) if identifier.text == "push")
                .then_some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, property.expression),
                ))
            })
            .unwrap();
        let writer = bound.flow_container(receiver).unwrap();
        let local = plan_source_captured_local(context.store(), &host, writer, receiver, symbol)
            .unwrap()
            .unwrap();
        let mutation = SourceFlowCapturedArrayMutation {
            mutation: SourceFlowArrayMutation {
                call,
                receiver,
                declaration,
                symbol,
            },
            local,
        };
        let statements = captured_arrow_statements(&parsed, file, writer);
        assert_eq!(statements.len(), 2);
        let statement = statements[0];
        let after = statements[1];
        let plan = SourceFlowPlan::preflight_linear_with_captured_effects(
            &parsed.arena,
            &bound,
            context.store(),
            &host,
            writer,
            statements.clone(),
            [],
            [],
            [call],
            [],
            [],
            [mutation],
        )
        .unwrap();
        assert!(plan.assignment_declarations.is_empty());
        assert_eq!(plan.calls.get(&call), Some(&statement));
        assert_eq!(
            plan.captured_origins.get(&call),
            Some(&SourceCapturedFlowOrigin::ArrayMutation(mutation))
        );
        let nodes = bound.flow_graph().nodes();
        let call_flow = nodes
            .iter()
            .enumerate()
            .find_map(|(index, row)| {
                (row.payload == Some(FlowNodePayload::Ast(call))
                    && row.flags.bits() & !FLOW_METADATA_BITS == FlowFlags::CALL.bits())
                .then(|| {
                    nodes
                        .flow_ref(FlowNodeId(u32::try_from(index).unwrap()))
                        .unwrap()
                })
            })
            .unwrap();
        let mutation_flow = nodes.get(call_flow).unwrap().antecedent.unwrap();
        let row = nodes.get(mutation_flow).unwrap();
        assert_eq!(
            row.flags.bits() & !FLOW_METADATA_BITS,
            FlowFlags::ARRAY_MUTATION.bits()
        );
        assert_eq!(row.payload, Some(FlowNodePayload::Ast(call)));
        assert_eq!(row.antecedent, Some(plan.start));
        assert_eq!(plan.end, Some(call_flow));
        assert!(
            matches!(SourceFlowPlan::preflight_linear_with_captured_effects(
            &parsed.arena, &bound, context.store(), &host, writer,
            statements.clone(), [], [], [], [], [], [mutation],
        ), Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidArrayMutation(node))) if node == call)
        );
        assert!(
            matches!(SourceFlowPlan::preflight_linear_with_captured_effects(
            &parsed.arena, &bound, context.store(), &host, writer,
            statements, [], [], [call], [], [], [],
        ), Err(SourceFlowError::Unsupported(SourceFlowUnsupported::FlowKind { flow, .. })) if flow == mutation_flow)
        );

        // These checks use an opaque entry type. Source checking owns Array relations.
        let input = context.store().intrinsic_bootstrap().unwrap().unknown_type;
        let outer = [(symbol, input)].into_iter().collect::<SourceFlowTypes>();
        let value_links = context.store().value_symbol_links(symbol).cloned();
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for _ in 0..2 {
            let mut frame = plan
                .frame_with_captured_locals(context.store(), &host, &bound, outer.clone())
                .unwrap();
            let entry = frame
                .snapshot_at(context.store_mut_for_test(), &globals, statement)
                .unwrap();
            assert_eq!(
                frame.snapshot_at(context.store_mut_for_test(), &globals, after),
                Err(SourceFlowInvariant::PendingAssignment(call).into())
            );
            frame.complete_assignment(call, symbol, input).unwrap();
            assert_eq!(
                frame
                    .snapshot_at(context.store_mut_for_test(), &globals, after)
                    .unwrap(),
                entry
            );
            assert_eq!(outer.get(&symbol), Some(&input));
        }
        let origin = SourceCapturedFlowOrigin::ArrayMutation(mutation);
        assert_eq!(
            validate_captured_origin_flow_node(origin, mutation_flow, row),
            Ok(())
        );
        let mut damaged_row = row.clone();
        damaged_row.flags = FlowFlags::ASSIGNMENT;
        assert_eq!(
            validate_captured_origin_flow_node(origin, mutation_flow, &damaged_row),
            Err(SourceFlowInvariant::InvalidPayload(mutation_flow).into())
        );
        let mut missing_call = plan.clone();
        missing_call.calls.remove(&call);
        assert!(
            matches!(missing_call.frame_with_captured_locals(context.store(), &host, &bound, outer.clone()),
            Err(SourceFlowError::Unsupported(SourceFlowUnsupported::Call(node))) if node == call)
        );
        assert!(
            plan.frame_with_captured_locals(context.store(), &host, &bound, outer.clone())
                .is_ok()
        );

        let syntax = captured_assignment_syntax(&parsed, file);
        let [(statement, expression, target)] = syntax.as_slice() else {
            panic!("expected one reset assignment");
        };
        let reset = bound.flow_container(*target).unwrap();
        let local = plan_source_captured_local(context.store(), &host, reset, *target, symbol)
            .unwrap()
            .unwrap();
        let assignment = SourceFlowCapturedAssignment {
            statement: *statement,
            expression: *expression,
            local,
        };
        let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.node).unwrap().data
        else {
            unreachable!()
        };
        let rhs = NodeRef::new(parsed.arena.id(), file, binary.right);
        assert_eq!(
            parsed.arena.get(rhs.node).unwrap().kind,
            SyntaxKind::CallExpression
        );
        assert!(
            nodes
                .iter()
                .all(|row| row.payload != Some(FlowNodePayload::Ast(rhs))
                    || row.flags.bits() & !FLOW_METADATA_BITS != FlowFlags::CALL.bits())
        );
        let reset_plan = SourceFlowPlan::preflight_linear_with_captured_effects(
            &parsed.arena,
            &bound,
            context.store(),
            &host,
            reset,
            captured_arrow_statements(&parsed, file, reset),
            [],
            [],
            [],
            [],
            [assignment],
            [],
        )
        .unwrap();
        assert!(reset_plan.calls.is_empty());
        assert!(
            matches!(SourceFlowPlan::preflight_linear_with_captured_effects(
            &parsed.arena, &bound, context.store(), &host, reset,
            [], [], [], [rhs], [], [assignment], [],
        ), Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidCall(node))) if node == rhs)
        );
        assert!(
            reset_plan
                .frame_with_captured_locals(context.store(), &host, &bound, outer)
                .is_ok()
        );
        assert_eq!(
            context.store().value_symbol_links(symbol).cloned(),
            value_links
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
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

    #[test]
    fn class_property_branch_unions_keep_spent_and_active_caller_demand_errors() {
        super::super::logical_operators::property_flow_test_support::assert_borrowed_union_preparation(
            |store, globals, _, flow, array, sentinel, caller| {
                ClassPropertyFlowTypes::Read { store, globals: Some(globals), session: Some(caller) }
                    .join(flow, FlowFlags::BRANCH_LABEL, &[array, sentinel], array)
                    .map_err(|error| match error {
                        SourceFlowError::Join { error, .. } => error,
                        other => panic!("expected the actual branch union preparation error: {other:?}"),
                    })
            },
        );
    }

    fn class_truthiness_test_plan(
        parsed: &ParseResult,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        body: &ClassBodyPlan,
    ) -> (SourceFlowPlan, SourceClassPropertyTruthinessCondition) {
        let reference = |node| NodeRef::new(parsed.arena.id(), bound.file_id(), node);
        let points = parsed
            .arena
            .iter()
            .filter_map(|(node, _)| {
                let node = reference(node);
                (bound.flow_container(node) == Some(body.declaration)
                    && bound.flow_at(node).is_some())
                .then_some(node)
            })
            .collect::<Vec<_>>();
        let conditions = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::IfStatement(branch) = &record.data else {
                    return None;
                };
                source_node_is_descendant_of(&parsed.arena, reference(node), body.body.node)
                    .then_some(SourceClassPropertyTruthinessCondition {
                        expression: reference(branch.expression),
                        access: reference(branch.expression),
                        negated: false,
                    })
            })
            .collect::<Vec<_>>();
        let [condition] = conditions.as_slice() else {
            panic!("expected one real property guard")
        };
        let calls = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let node = reference(node);
                (record.kind == SyntaxKind::CallExpression
                    && bound.container(node) == Some(body.declaration))
                .then_some(node)
            })
            .collect::<Vec<_>>();
        let plan = SourceFlowPlan::preflight_class_body_with_conditions(
            &parsed.arena,
            bound,
            store,
            host,
            body,
            points,
            conditions
                .iter()
                .copied()
                .map(SourceFlowCondition::ClassPropertyTruthiness),
            [],
            [],
            calls,
        )
        .unwrap();
        (plan, *condition)
    }

    #[test]
    fn class_property_condition_receipts_reject_warm_caches_and_changed_source_proofs() {
        use crate::semantic::instantiate::InstantiationLimits;
        use crate::semantic::{classes, production::GlobalMergeCompletion};

        let parsed = parse_source_file(concat!(
            "class First { value?: 0 | 1; other?: 0 | 1; ",
            "read(): void { if (this.value) { this.value; this.value = 0; this.value; } ",
            "else { this.value; } this.value; } otherBody(): void {} } ",
            "class Second { value?: 0 | 1; read(): void {} }",
        ));
        let file = FileId::new(202_675);
        let mut context = loop_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let options = context.options();
        let owner = |name| {
            context
                .store()
                .symbol_table(context.globals())
                .unwrap()
                .get_source(name)
                .unwrap()
        };
        let first =
            classes::plan_source_class_members(context.store(), &host, owner("First")).unwrap();
        let second =
            classes::plan_source_class_members(context.store(), &host, owner("Second")).unwrap();
        let body = &first.bodies()[0];
        let (plan, condition) =
            class_truthiness_test_plan(&parsed, &bound, context.store(), &host, body);
        let prepared =
            classes::prepare_source_class_members(context.store_mut_for_test(), &host, &first)
                .unwrap();
        let access = prepared.body_access(context.store(), &host, body).unwrap();
        let other_body_access = prepared
            .body_access(context.store(), &host, &first.bodies()[1])
            .unwrap();
        let prepared_other =
            classes::prepare_source_class_members(context.store_mut_for_test(), &host, &second)
                .unwrap();
        let other_class_access = prepared_other
            .body_access(context.store(), &host, &second.bodies()[0])
            .unwrap();
        let source =
            plan_class_property_truthiness(context.store(), &host, body, condition.access).unwrap();
        let member = class_member_source(context.store(), &host, source.member).unwrap();
        let other = context
            .store()
            .symbol(body.class_symbol)
            .unwrap()
            .members()
            .unwrap();
        let other = context
            .store()
            .symbol_table(other)
            .unwrap()
            .get_source("other")
            .unwrap();
        let other_member = class_member_source(context.store(), &host, other).unwrap();
        let declared = context
            .store()
            .type_node_links(condition.access)
            .unwrap()
            .resolved_type
            .unwrap();
        let mut reads = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let node = NodeRef::new(parsed.arena.id(), file, node);
                (record.kind == SyntaxKind::PropertyAccessExpression
                    && bound.flow_container(node) == Some(body.declaration)
                    && record
                        .parent
                        .and_then(|parent| parsed.arena.get(parent))
                        .is_some_and(|parent| parent.kind == SyntaxKind::ExpressionStatement))
                .then_some(node)
            })
            .collect::<Vec<_>>();
        reads.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
        let [truthy, after_write, falsy, _joined] = reads.as_slice() else {
            panic!("expected the four source reads")
        };
        let write = plan
            .property_assignments
            .values()
            .find_map(|assignment| assignment.write.as_ref())
            .unwrap();
        let mut frame =
            ClassInitializationFrame::new(body, &plan, &bound, access, HashMap::new()).unwrap();
        let mut caller = InstantiationSession::new(InstantiationLimits::default());
        let query_context = |store: &CanonicalTypeMapperStore, node| {
            plan_class_property_truthiness(store, &host, body, node)
                .unwrap()
                .context
        };
        let context_ = query_context(context.store(), *truthy);
        let before = format!("{:?}", context.store());
        for _ in 0..2 {
            assert!(matches!(frame.property_read_with_session(
                context.store_mut_for_test(), &host, Some(&globals),
                &context_,
                *truthy, &member, declared, options, &mut caller,
            ), Err(SourceFlowError::Invariant(SourceFlowInvariant::UnreachedCondition(node))) if node == condition.expression));
            assert_eq!(format!("{:?}", context.store()), before);
        }
        let checked_guard = frame
            .property_read_with_session(
                context.store_mut_for_test(),
                &host,
                Some(&globals),
                &source.context,
                condition.access,
                &member,
                declared,
                options,
                &mut caller,
            )
            .unwrap();
        assert_eq!(checked_guard.type_(), declared);
        frame
            .complete_property_condition(
                context.store(),
                &host,
                condition,
                checked_guard.type_(),
                checked_guard.type_(),
            )
            .unwrap();
        let completed = frame.property_conditions[&condition.expression].clone();
        for read in [*truthy, *falsy] {
            let expected = context
                .store()
                .type_node_links(read)
                .unwrap()
                .resolved_type
                .unwrap();
            let context_ = query_context(context.store(), read);
            assert_eq!(
                frame
                    .property_read_with_session(
                        context.store_mut_for_test(),
                        &host,
                        Some(&globals),
                        &context_,
                        read,
                        &member,
                        declared,
                        options,
                        &mut caller,
                    )
                    .unwrap()
                    .type_(),
                expected
            );
        }
        let context_ = query_context(context.store(), *after_write);
        assert_eq!(
            frame.property_read_with_session(
                context.store_mut_for_test(),
                &host,
                Some(&globals),
                &context_,
                *after_write,
                &member,
                declared,
                options,
                &mut caller,
            ),
            Err(SourceFlowInvariant::PendingAssignment(write.plan.target()).into())
        );
        for damage in 0..8 {
            let mut changed = completed.clone();
            match damage {
                0 => changed.access = other_body_access.clone(),
                1 => changed.access = other_class_access.clone(),
                2 => changed.member = other_member.clone(),
                3 => changed.member.readonly = !changed.member.readonly,
                4 => changed.flow = plan.end.unwrap(),
                5 => changed.edges.swap(0, 1),
                6 => changed.edges[0] = plan.start,
                7 => changed.type_ = context.store().intrinsic_bootstrap().unwrap().string_type,
                _ => unreachable!(),
            }
            frame
                .property_conditions
                .insert(condition.expression, changed);
            let before = format!("{:?}", context.store());
            let caller_before = format!("{caller:?}");
            let context_ = query_context(context.store(), *truthy);
            for _ in 0..2 {
                assert_eq!(
                    frame.property_read_with_session(
                        context.store_mut_for_test(),
                        &host,
                        Some(&globals),
                        &context_,
                        *truthy,
                        &member,
                        declared,
                        options,
                        &mut caller,
                    ),
                    Err(SourceFlowInvariant::InvalidClassProperty(condition.access).into()),
                    "damage {damage}"
                );
                assert_eq!(format!("{:?}", context.store()), before);
                assert_eq!(format!("{caller:?}"), caller_before);
            }
        }
        frame
            .property_conditions
            .insert(condition.expression, completed);
        let original = context
            .store()
            .type_node_links(condition.access)
            .unwrap()
            .clone();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            condition.access,
            TypeNodeLinks {
                resolved_type: Some(string),
                ..original.clone()
            }
        ));
        let context_ = query_context(context.store(), *truthy);
        let before = format!("{:?}", context.store());
        assert_eq!(
            frame.property_read_with_session(
                context.store_mut_for_test(),
                &host,
                Some(&globals),
                &context_,
                *truthy,
                &member,
                declared,
                options,
                &mut caller,
            ),
            Err(SourceFlowInvariant::InvalidClassProperty(condition.access).into())
        );
        assert_eq!(format!("{:?}", context.store()), before);
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(condition.access, original)
        );
        let mut changed = condition;
        changed.negated = true;
        assert!(
            matches!(validate_class_property_condition(context.store(), &host, &bound, body, changed), Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidClassProperty(node))) if node == condition.access)
        );
        let symbol = context.store().symbol(member.symbol).unwrap();
        let flags = symbol.flags();
        let check_flags = symbol.check_flags();
        assert!(context.store_mut_for_test().set_symbol_flags(
            member.symbol,
            flags.without(SymbolFlags::OPTIONAL),
            check_flags
        ));
        let before = format!("{:?}", context.store());
        assert_eq!(
            plan_class_property_truthiness(context.store(), &host, body, condition.access),
            Err(SourcePropertyError::InvalidCache(condition.access))
        );
        assert_eq!(format!("{:?}", context.store()), before);
        assert!(
            context
                .store_mut_for_test()
                .set_symbol_flags(member.symbol, flags, check_flags)
        );
    }

    #[test]
    fn class_property_flow_requires_current_run_ordinary_call_proofs() {
        use crate::semantic::instantiate::InstantiationLimits;
        use crate::semantic::{classes, production::GlobalMergeCompletion};

        let parsed = parse_source_file(concat!(
            "declare function touch(): void; ",
            "class Guard { value?: number; read(): void { touch(); ",
            "if (this.value) { this.value; } else { this.value; } } }",
        ));
        let file = FileId::new(202_676);
        let mut context = loop_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let owner = context
            .store()
            .symbol_table(context.globals())
            .unwrap()
            .get_source("Guard")
            .unwrap();
        let class = classes::plan_source_class_members(context.store(), &host, owner).unwrap();
        let body = &class.bodies()[0];
        let (plan, condition) =
            class_truthiness_test_plan(&parsed, &bound, context.store(), &host, body);
        assert_eq!(plan.calls.len(), 1);
        let call = *plan.calls.keys().next().unwrap();
        let links = context.store().signature_links(call).unwrap();
        assert!(links.resolved_signature.signature().is_some());
        assert_eq!(links.effects_signature, EffectsSignatureState::Unresolved);
        let prepared =
            classes::prepare_source_class_members(context.store_mut_for_test(), &host, &class)
                .unwrap();
        let token = prepared.body_access(context.store(), &host, body).unwrap();
        let source =
            plan_class_property_truthiness(context.store(), &host, body, condition.access).unwrap();
        let member = class_member_source(context.store(), &host, source.member).unwrap();
        let declared = context
            .store()
            .type_node_links(condition.access)
            .unwrap()
            .resolved_type
            .unwrap();
        let globals = context.global_types().clone();
        let options = context.options();
        let mut caller = InstantiationSession::new(InstantiationLimits::default());
        let mut frame =
            ClassInitializationFrame::new(body, &plan, &bound, token, HashMap::new()).unwrap();
        let before = format!("{:?}", context.store());
        let caller_before = format!("{caller:?}");
        for _ in 0..2 {
            assert_eq!(
                frame.property_read_with_session(
                    context.store_mut_for_test(),
                    &host,
                    Some(&globals),
                    &source.context,
                    condition.access,
                    &member,
                    declared,
                    options,
                    &mut caller,
                ),
                Err(SourceFlowInvariant::InvalidCallEffect(call).into())
            );
            assert_eq!(format!("{:?}", context.store()), before);
            assert_eq!(format!("{caller:?}"), caller_before);
            assert!(frame.ordinary_calls.is_empty());
            assert!(frame.property_conditions.is_empty());
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
    #[allow(clippy::too_many_lines)] // Check the real entry, initializer, and later join together.
    fn catch_scope_restores_both_type_maps_and_excludes_expired_flow_facts() {
        let parsed = parse_source_file(concat!(
            "function run(value: number) { try {} catch (error = value) { ",
            "if (typeof error === 'string') {} } return value; }",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(58_572);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(context.options().name_resolution),
        ).unwrap();
        let reference = |node| NodeRef::new(parsed.arena.id(), file, node);
        let declaration = parsed.arena.iter().find_map(|(node, record)| {
            (record.kind == SyntaxKind::FunctionDeclaration).then_some(reference(node))
        }).unwrap();
        let callable = super::super::source_callables::plan_source_callable(
            context.store(), &host, declaration, bound.symbol(declaration).unwrap(),
            Some(CanonicalArrayTargets::from_global_types(&globals)),
        ).unwrap();
        let syntax = plan_source_callable_statement_list_syntax(
            &parsed.arena, &bound, context.store(), &callable,
        ).unwrap();
        let binding = *syntax.catch_bindings()[0];
        let catch_block = match &parsed.arena.get(binding.clause.node).unwrap().data {
            NodeData::CatchClause(caught) => reference(caught.block),
            _ => unreachable!(),
        };
        let condition = parsed.arena.iter().find_map(|(_, record)| {
            if let NodeData::IfStatement(branch) = &record.data {
                Some(reference(branch.expression))
            } else { None }
        }).unwrap();
        let returned = parsed.arena.iter().find_map(|(node, record)| {
            (record.kind == SyntaxKind::ReturnStatement).then_some(reference(node))
        }).unwrap();
        let points = parsed.arena.iter().filter_map(|(node, _)| {
            let node = reference(node);
            (bound.flow_container(node) == Some(declaration) && bound.flow_at(node).is_some())
                .then_some(node)
        }).collect::<Vec<_>>();
        let plan = SourceFlowPlan::preflight_statement_list(
            &parsed.arena, &bound, context.store(), &host, &syntax, points,
            [SourceFlowCondition::Typeof(SourceTypeofCondition {
                expression: condition, symbol: binding.symbol, tag: SourceTypeofTag::String,
                comparison: SourceTypeofComparison::Equal,
            })],
            Vec::new(),
            [SourceFlowAssignment { declaration: binding.declaration, symbol: binding.symbol }],
            [], [], [], [],
        ).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let unknown = bootstrap.unknown_type;
        let parameter = callable.parameters[0].symbol;
        let mut frame = plan.frame_with_captured_locals(
            context.store(), &host, &bound, [(parameter, number)].into_iter().collect(),
        ).unwrap();
        let base = frame.base.clone();
        let declared = frame.declared_types.clone();
        let mut wrong = binding;
        wrong.symbol = parameter;
        assert!(matches!(frame.enter_catch_binding(context.store(), &wrong, unknown),
            Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidParameterAssignment(node)))
                if node == binding.declaration));
        assert_eq!(frame.base, base);
        assert_eq!(frame.declared_types, declared);
        let scope = frame.enter_catch_binding(context.store(), &binding, unknown).unwrap();
        assert_eq!(frame.declared_types.get(&binding.symbol), Some(&unknown));
        assert_eq!(frame.snapshot_at(context.store_mut_for_test(), &globals, binding.name).unwrap().type_of(binding.symbol), Some(unknown));
        frame.complete_assignment(binding.declaration, binding.symbol, number).unwrap();
        assert_eq!(frame.snapshot_at(context.store_mut_for_test(), &globals, catch_block).unwrap().type_of(binding.symbol), Some(number));
        assert!(!frame.memo.is_empty());
        frame.restore_catch_binding(scope);
        assert_eq!(frame.base, base);
        assert_eq!(frame.declared_types, declared);
        assert!(frame.memo.is_empty());
        assert_eq!(frame.assignment_states.get(&binding.declaration), Some(&SourceFlowAssignmentState::Resolved(number)));
        let after = frame.snapshot_at(context.store_mut_for_test(), &globals, returned).unwrap();
        assert_eq!(after.type_of(parameter), Some(number));
        assert_eq!(after.type_of(binding.symbol), None);
        assert_eq!(frame.snapshot_at(context.store_mut_for_test(), &globals, returned), Ok(after));
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
            assignment_declarations: HashMap::new(),
            captured_origins: HashMap::new(),
            calls: HashMap::new(),
            logical_statements: Vec::new(),
            class_body: None,
            statement_list: None,
            property_assignments: HashMap::new(),
            region: None,
            updates: HashMap::new(),
            nullish_assignments: HashMap::new(),
            member_assignments: HashMap::new(),
            nullish_calls: HashMap::new(),
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

    const SINGLE_EDGE_LOOP_SOURCE: &str = "declare const value: number; for (;;) { value; break; }";

    fn single_edge_loop_nodes(parsed: &ParseResult, file: FileId) -> (NodeRef, NodeRef, NodeRef) {
        let reference = |node| NodeRef::new(parsed.arena.id(), file, node);
        let (statement, body) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| match &record.data {
                NodeData::ForStatement(iteration) => Some((node, iteration.statement)),
                _ => None,
            })
            .unwrap();
        let NodeData::Block(block) = &parsed.arena.get(body).unwrap().data else {
            panic!("expected the actual loop body")
        };
        let [expression, jump] = block.statements.nodes.as_slice() else {
            panic!("expected the source read and terminal break")
        };
        let NodeData::ExpressionStatement(expression) =
            &parsed.arena.get(*expression).unwrap().data
        else {
            panic!("expected the source expression statement")
        };
        assert_eq!(
            parsed.arena.get(*jump).unwrap().kind,
            SyntaxKind::BreakStatement
        );
        (
            reference(statement),
            reference(expression.expression),
            reference(*jump),
        )
    }

    #[test]
    fn single_edge_loop_label_checks_the_real_terminal_break_and_replays() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(SINGLE_EDGE_LOOP_SOURCE);
        let file = FileId::new(32_209);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let (statement, read, jump) = single_edge_loop_nodes(&parsed, file);
        let entry = bound.flow_at(statement).unwrap();
        let label = bound.flow_at(read).unwrap();
        let row = flow_node(bound.flow_graph(), label).unwrap();
        assert_eq!(
            source_flow_kind(label, row.flags),
            Ok(SourceFlowKind::LoopLabel)
        );
        assert_eq!(label_antecedents(label, &row), Ok([entry].as_slice()));
        assert_eq!(bound.flow_at(jump), Some(label));
        assert_eq!(
            bound.flow_graph().container_end(bound.source_file()),
            Some(label)
        );
        let plan = SourceFlowPlan::preflight_source_statement(
            &parsed.arena,
            &bound,
            context.store(),
            &host,
            statement,
            [statement, read, jump],
            [],
            [],
            [],
            [],
        )
        .unwrap();
        assert_eq!(plan.end, Some(label));
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let owner = bound
            .symbol(captured_variable(&parsed, file, "value"))
            .unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            context
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        assert_eq!(context.get_type_at_location(read), Ok(number));
        let globals = context.global_types().clone();
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().relation_state_snapshot(),
                context.store().type_node_links(read).cloned(),
                context.store().value_symbol_links(owner).cloned(),
                context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned(),
                context.diagnostics().clone(),
            )
        };
        let before = snapshot(&context);
        for _ in 0..2 {
            let mut frame = plan
                .frame_with_captured_locals(
                    context.store(),
                    &host,
                    &bound,
                    [(owner, number)].into(),
                )
                .unwrap();
            for point in [read, jump, read] {
                let actual = frame
                    .snapshot_for_symbols_at(context.store_mut_for_test(), &globals, point, [owner])
                    .unwrap();
                assert_eq!(actual.type_of(owner), Some(number));
                assert!(actual.reachable);
                assert!(!actual.incomplete);
            }
            let exit = frame
                .snapshot_for_symbols_at_end(context.store_mut_for_test(), &globals, [owner])
                .unwrap();
            assert_eq!(exit.type_of(owner), Some(number));
            assert!(exit.reachable);
            assert!(!exit.incomplete);
            assert!(frame.visiting.is_empty());
            assert!(frame.loop_snapshots.is_empty());
            context.recheck_source_file(file).unwrap();
            assert_eq!(snapshot(&context), before);
        }
    }

    #[test]
    fn single_edge_loop_label_rejects_changed_kind_and_shape() {
        let parsed = parse_source_file(SINGLE_EDGE_LOOP_SOURCE);
        let file = FileId::new(32_210);
        let context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1;
        let (statement, read, _) = single_edge_loop_nodes(&parsed, file);
        let label = bound.flow_at(read).unwrap();
        let entry = bound.flow_at(statement).unwrap();
        let original = flow_node(bound.flow_graph(), label).unwrap();
        assert_eq!(label_antecedents(label, &original), Ok([entry].as_slice()));
        let before = (
            context.store().type_len(),
            context.store().checker_link_allocated_lengths(),
        );
        let mut empty = original.clone();
        empty.antecedents.clear();
        let mut duplicate = original.clone();
        duplicate.antecedents.push(entry);
        let mut linear = original.clone();
        linear.antecedent = Some(entry);
        let mut payload = original.clone();
        payload.payload = Some(FlowNodePayload::Ast(statement));
        let mut branch = original.clone();
        branch.flags = FlowFlags::BRANCH_LABEL;
        let mut wrong_kind = original.clone();
        wrong_kind.flags = FlowFlags::START;
        wrong_kind.antecedents.push(label);
        for changed in [empty, duplicate, linear, payload, branch, wrong_kind] {
            assert_eq!(
                label_antecedents(label, &changed),
                Err(SourceFlowInvariant::InvalidAntecedents(label).into())
            );
            assert_eq!(label_antecedents(label, &original), Ok([entry].as_slice()));
        }
        let mut composite = original.clone();
        composite.flags = FlowFlags::LOOP_LABEL | FlowFlags::BRANCH_LABEL;
        assert_eq!(
            label_antecedents(label, &composite),
            Err(SourceFlowInvariant::InvalidFlowFlags {
                flow: label,
                flags: composite.flags
            }
            .into())
        );
        for metadata in [
            FlowFlags::REFERENCED,
            FlowFlags::SHARED,
            FlowFlags::REFERENCED | FlowFlags::SHARED,
        ] {
            let mut annotated = original.clone();
            annotated.flags = FlowFlags::LOOP_LABEL | metadata;
            assert_eq!(label_antecedents(label, &annotated), Ok([entry].as_slice()));
        }
        assert_eq!(flow_node(bound.flow_graph(), label).unwrap(), original);
        assert_eq!(
            (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before
        );
    }

    #[test]
    fn single_edge_loop_label_keeps_foreign_flow_and_source_owner_rejection() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(SINGLE_EDGE_LOOP_SOURCE);
        let file = FileId::new(32_211);
        let context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1;
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let (statement, read, jump) = single_edge_loop_nodes(&parsed, file);
        let plan = SourceFlowPlan::preflight_source_statement(
            &parsed.arena,
            bound,
            context.store(),
            &host,
            statement,
            [statement, read, jump],
            [],
            [],
            [],
            [],
        )
        .unwrap();
        let foreign = parse_source_file(SINGLE_EDGE_LOOP_SOURCE);
        let foreign_file = FileId::new(32_212);
        let foreign_context = loop_context(&foreign, foreign_file);
        let foreign_bound = foreign_context.file(foreign_file).unwrap().1;
        let (_, foreign_read, _) = single_edge_loop_nodes(&foreign, foreign_file);
        let foreign_flow = foreign_bound.flow_at(foreign_read).unwrap();
        let mut foreign_point = plan.clone();
        foreign_point.points.insert(read, foreign_flow);
        let mut foreign_exit = plan.clone();
        foreign_exit.end = Some(foreign_flow);
        let before = (
            context.store().type_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for changed in [foreign_point, foreign_exit] {
            assert_eq!(
                changed.validate_flow_paths(bound),
                Err(SourceFlowInvariant::ForeignFlow(foreign_flow).into())
            );
            assert_eq!(plan.validate_flow_paths(bound), Ok(()));
        }
        let mut wrong_owner = plan.clone();
        wrong_owner.region.as_mut().unwrap().statement = read;
        assert!(matches!(
            wrong_owner.frame_with_captured_locals(context.store(), &host, bound, HashMap::new()),
            Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidSourceRegion(node))) if node == read
        ));
        plan.frame_with_captured_locals(context.store(), &host, bound, HashMap::new())
            .unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before
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

    fn source_numeric_equality_types(
        context: &mut CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        file: FileId,
    ) -> (TypeId, [TypeId; 3]) {
        let declaration = captured_variable(parsed, file, "choices");
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let annotation = NodeRef::new(parsed.arena.id(), file, variable.type_.unwrap());
        let NodeData::UnionTypeNode(union) = &parsed.arena.get(annotation.node).unwrap().data
        else {
            panic!("expected the written numeric union")
        };
        let [zero, one, two] = union.types.nodes.as_slice() else {
            panic!("expected three written numeric members")
        };
        let literals = [*zero, *one, *two].map(|node| {
            context
                .get_type_from_type_node(NodeRef::new(parsed.arena.id(), file, node))
                .unwrap()
        });
        let choices = context.get_type_from_type_node(annotation).unwrap();
        let mut expected = literals;
        expected.sort_unstable();
        assert_eq!(
            union_constituents(context.store(), choices),
            Some(expected.as_slice())
        );
        (choices, literals)
    }

    #[test]
    fn loose_numeric_equality_keeps_written_literals_and_cold_warm_results() {
        let parsed = parse_source_file("declare const choices: 0 | 1 | 2;");
        let file = FileId::new(32_270);
        let mut context = loop_context(&parsed, file);
        let globals = context.global_types().clone();
        let (choices, [zero, one, two]) =
            source_numeric_equality_types(&mut context, &parsed, file);
        let fresh_one = context.store().fresh_type_of_literal_type(one).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, never) = (bootstrap.number_type, bootstrap.never_type);

        let rejected = narrow_by_equality(
            context.store_mut_for_test(),
            &globals,
            choices,
            fresh_one,
            false,
            false,
            None,
        )
        .unwrap();
        let mut remaining = [zero, two];
        remaining.sort_unstable();
        assert_eq!(
            union_constituents(context.store(), rejected),
            Some(remaining.as_slice()),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .expression_union_type_with_global_types(
                    &globals,
                    &remaining,
                    UnionReduction::Literal,
                ),
            Ok(rejected),
        );

        for (input, value, require_match, expected) in [
            (zero, one, true, never),
            (zero, one, false, zero),
            (one, fresh_one, true, one),
            (one, fresh_one, false, never),
            (fresh_one, one, true, fresh_one),
            (fresh_one, one, false, never),
            (number, fresh_one, true, one),
            (number, fresh_one, false, number),
            (choices, one, true, one),
            (choices, one, false, rejected),
            (choices, fresh_one, true, one),
            (choices, fresh_one, false, rejected),
        ] {
            assert_eq!(
                narrow_by_equality(
                    context.store_mut_for_test(),
                    &globals,
                    input,
                    value,
                    false,
                    require_match,
                    None,
                ),
                Ok(expected),
            );
            let warm = (
                context.store().type_len(),
                context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .union_cache_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().relation_state_snapshot(),
            );
            for _ in 0..2 {
                assert_eq!(
                    narrow_by_equality(
                        context.store_mut_for_test(),
                        &globals,
                        input,
                        value,
                        false,
                        require_match,
                        None,
                    ),
                    Ok(expected),
                );
                assert_eq!(
                    (
                        context.store().type_len(),
                        context
                            .store()
                            .intrinsic_bootstrap()
                            .unwrap()
                            .union_cache_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.store().relation_state_snapshot(),
                    ),
                    warm,
                );
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Each damage case restores the same checked numeric inputs.
    fn loose_numeric_equality_rejects_mixed_foreign_and_damaged_inputs_before_filtering() {
        use crate::semantic::type_records::RegularLiteralLink;

        let parsed = parse_source_file("declare const choices: 0 | 1 | 2;");
        let file = FileId::new(32_271);
        let mut context = loop_context(&parsed, file);
        let globals = context.global_types().clone();
        let (choices, [zero, one, two]) =
            source_numeric_equality_types(&mut context, &parsed, file);
        let fresh_one = context.store().fresh_type_of_literal_type(one).unwrap();
        let fresh_two = context.store().fresh_type_of_literal_type(two).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, unknown, null, regular_true) = (
            bootstrap.number_type,
            bootstrap.unknown_type,
            bootstrap.null_type,
            bootstrap.regular_true_type,
        );
        let text = context
            .store_mut_for_test()
            .regular_string_literal_type("1".to_owned())
            .unwrap();
        let mixed = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[zero, text],
                UnionReduction::Literal,
            )
            .unwrap();
        let nullable = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[zero, null],
                UnionReduction::Literal,
            )
            .unwrap();
        let foreign = loop_context(&parsed, FileId::new(32_272));
        let foreign_number = foreign.store().intrinsic_bootstrap().unwrap().number_type;
        let value = match context.store().type_payload(one).unwrap().data() {
            TypeData::Literal(literal) => literal.value.clone(),
            _ => unreachable!(),
        };
        let copied_one = context
            .store_mut_for_test()
            .alloc_literal_type(
                TypeFlags::NUMBER_LITERAL,
                value,
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let copied_number = context
            .store_mut_for_test()
            .alloc_intrinsic_type(TypeFlags::NUMBER, "number")
            .unwrap();
        let snapshot = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            )
        };
        for (input, value, expected) in [
            (
                mixed,
                one,
                SourceEqualityNarrowingError::UnsupportedType(one),
            ),
            (
                unknown,
                one,
                SourceEqualityNarrowingError::UnsupportedType(one),
            ),
            (
                nullable,
                one,
                SourceEqualityNarrowingError::UnsupportedType(one),
            ),
            (
                choices,
                text,
                SourceEqualityNarrowingError::UnsupportedType(text),
            ),
            (
                zero,
                regular_true,
                SourceEqualityNarrowingError::UnsupportedType(regular_true),
            ),
            (
                foreign_number,
                one,
                SourceEqualityNarrowingError::InvalidType(foreign_number),
            ),
            (
                one,
                foreign_number,
                SourceEqualityNarrowingError::InvalidType(foreign_number),
            ),
            (
                choices,
                copied_one,
                SourceEqualityNarrowingError::Union(LiteralTypeCacheError::InvalidCachedLiteral(
                    copied_one,
                )),
            ),
            (
                copied_number,
                one,
                SourceEqualityNarrowingError::Union(
                    LiteralTypeCacheError::UnsupportedUnionConstituent(copied_number),
                ),
            ),
        ] {
            let before = snapshot(context.store());
            for require_match in [true, false] {
                assert_eq!(
                    narrow_by_equality(
                        context.store_mut_for_test(),
                        &globals,
                        input,
                        value,
                        false,
                        require_match,
                        None,
                    ),
                    Err(expected),
                );
                assert_eq!(snapshot(context.store()), before);
            }
        }

        let before = snapshot(context.store());
        assert_eq!(
            narrow_by_equality(
                context.store_mut_for_test(),
                &globals,
                choices,
                one,
                false,
                true,
                Some("kind"),
            ),
            Err(SourceEqualityNarrowingError::UnsupportedType(one)),
        );
        assert_eq!(snapshot(context.store()), before);

        // Warm the result before damaging a leaf that a match would remove.
        assert_eq!(
            narrow_by_equality(
                context.store_mut_for_test(),
                &globals,
                choices,
                fresh_one,
                false,
                true,
                None,
            ),
            Ok(one),
        );
        assert!(
            context
                .store_mut_for_test()
                .set_literal_links(two, Some(two), two)
        );
        let before = snapshot(context.store());
        assert_eq!(
            narrow_by_equality(
                context.store_mut_for_test(),
                &globals,
                choices,
                fresh_one,
                false,
                true,
                None,
            ),
            Err(SourceEqualityNarrowingError::Union(
                LiteralTypeCacheError::InvalidCachedLiteral(two)
            )),
        );
        assert_eq!(snapshot(context.store()), before);
        assert!(
            context
                .store_mut_for_test()
                .set_literal_links(two, Some(fresh_two), two)
        );

        assert!(
            context
                .store_mut_for_test()
                .set_literal_links(fresh_one, None, one)
        );
        let before = snapshot(context.store());
        assert_eq!(
            narrow_by_equality(
                context.store_mut_for_test(),
                &globals,
                number,
                fresh_one,
                false,
                true,
                None,
            ),
            Err(SourceEqualityNarrowingError::Union(
                LiteralTypeCacheError::InvalidCachedLiteral(fresh_one)
            )),
        );
        assert_eq!(snapshot(context.store()), before);
        assert!(
            context
                .store_mut_for_test()
                .set_literal_links(fresh_one, Some(fresh_one), one)
        );

        let owner = context
            .file(file)
            .unwrap()
            .1
            .symbol(captured_variable(&parsed, file, "choices"))
            .unwrap();
        assert!(
            context
                .store_mut_for_test()
                .set_type_symbol(choices, Some(owner))
        );
        let before = snapshot(context.store());
        assert_eq!(
            narrow_by_equality(
                context.store_mut_for_test(),
                &globals,
                choices,
                fresh_one,
                false,
                true,
                None,
            ),
            Err(SourceEqualityNarrowingError::Union(
                LiteralTypeCacheError::InvalidCachedUnion(choices)
            )),
        );
        assert_eq!(snapshot(context.store()), before);
        assert!(context.store_mut_for_test().set_type_symbol(choices, None));
        let restored = snapshot(context.store());
        for _ in 0..2 {
            assert_eq!(
                narrow_by_equality(
                    context.store_mut_for_test(),
                    &globals,
                    choices,
                    fresh_one,
                    false,
                    true,
                    None,
                ),
                Ok(one),
            );
            assert_eq!(snapshot(context.store()), restored);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // The source and frame checks share the exact const-loop graph.
    fn loose_numeric_equality_keeps_the_real_const_loop_and_reference_replay() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(concat!(
            "for (const fixed = 0; fixed < 1; ++fixed) {\n",
            "  const current: 0 = fixed;\n",
            "  if (fixed == 1) { break; }\n",
            "  if (fixed == 2) { continue; }\n",
            "}\n",
        ));
        let file = FileId::new(32_273);
        let mut context = loop_context(&parsed, file);
        // The unchanged source must check before any test supplies frame values.
        context.check_source_file(file).unwrap();
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2588, 2367, 2367],
        );
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let reference = |node| NodeRef::new(parsed.arena.id(), file, node);
        let assignment = |name| {
            let declaration = captured_variable(&parsed, file, name);
            SourceFlowAssignment {
                declaration,
                symbol: bound.symbol(declaration).unwrap(),
            }
        };
        let fixed = assignment("fixed");
        let current = assignment("current");
        assert_ne!(fixed.symbol, current.symbol);
        let (statement, iteration) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| match &record.data {
                NodeData::ForStatement(iteration) => Some((reference(node), iteration)),
                _ => None,
            })
            .unwrap();
        let NodeData::BinaryExpression(header) =
            &parsed.arena.get(iteration.condition.unwrap()).unwrap().data
        else {
            panic!("expected the original header comparison")
        };
        let header_read = reference(header.left);
        let NodeData::PrefixUnaryExpression(update) = &parsed
            .arena
            .get(iteration.incrementor.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected the original prefix update")
        };
        let update_target = reference(update.operand);
        let NodeData::VariableDeclaration(current_data) =
            &parsed.arena.get(current.declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let body_read = reference(current_data.initializer.unwrap());
        let mut conditions = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::BinaryExpression(binary) = &record.data else {
                    return None;
                };
                (parsed.arena.get(binary.operator_token).unwrap().kind
                    == SyntaxKind::EqualsEqualsToken)
                    .then_some((
                        reference(node),
                        reference(binary.left),
                        reference(binary.right),
                    ))
            })
            .collect::<Vec<_>>();
        conditions.sort_by_key(|(node, _, _)| parsed.arena.get(node.node).unwrap().range.start);
        let [first, second] = conditions.as_slice() else {
            panic!("expected both original loose comparisons")
        };
        let second_flow = bound.flow_at(second.1).unwrap();
        let second_row = flow_node(bound.flow_graph(), second_flow).unwrap();
        assert_eq!(
            source_flow_kind(second_flow, second_row.flags),
            Ok(SourceFlowKind::FalseCondition)
        );
        assert_eq!(ast_payload(second_flow, &second_row), Ok(first.0));
        let label = bound.flow_at(header_read).unwrap();
        assert_eq!(
            source_flow_kind(label, flow_node(bound.flow_graph(), label).unwrap().flags),
            Ok(SourceFlowKind::LoopLabel)
        );
        for read in [header_read, update_target, body_read, first.1, second.1] {
            validate_source_reference(
                &parsed.arena,
                &bound,
                context.store(),
                &host,
                read,
                fixed.symbol,
            )
            .unwrap();
        }
        let mut points = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let node = reference(node);
                (record.kind == SyntaxKind::Identifier
                    && source_node_is_descendant_of(&parsed.arena, node, statement.node)
                    && bound.flow_at(node).is_some())
                .then_some(node)
            })
            .collect::<Vec<_>>();
        points.sort_unstable();
        let plan = SourceFlowPlan::preflight_source_statement(
            &parsed.arena,
            &bound,
            context.store(),
            &host,
            statement,
            points,
            conditions.iter().map(|(expression, _, value)| {
                SourceFlowCondition::Equality(SourceEqualityCondition {
                    expression: *expression,
                    symbol: fixed.symbol,
                    value: *value,
                    comparison: SourceTypeofComparison::Equal,
                    strict: false,
                    discriminant: None,
                })
            }),
            [fixed, current],
            [SourceFlowUpdate {
                target: update_target,
                declaration: fixed.declaration,
                symbol: fixed.symbol,
                readonly: true,
            }],
            [],
        )
        .unwrap();
        let value_type = |symbol| {
            context
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type
                .unwrap()
        };
        let zero = value_type(fixed.symbol);
        let current_type = value_type(current.symbol);
        assert!(matches!(
            context.store().type_payload(zero).unwrap().data(),
            TypeData::Literal(_)
        ));
        assert!(matches!(
            context.store().type_payload(current_type).unwrap().data(),
            TypeData::Literal(_)
        ));
        let mut frame = plan
            .frame_with_captured_locals(context.store(), &host, &bound, HashMap::new())
            .unwrap();
        for (_, _, value) in &conditions {
            frame
                .complete_condition_value(
                    *value,
                    context
                        .store()
                        .type_node_links(*value)
                        .unwrap()
                        .resolved_type
                        .unwrap(),
                )
                .unwrap();
        }
        // The checked non-union declared types are also the post-assignment flow types.
        frame
            .complete_source_declaration(&host, fixed.declaration, fixed.symbol, zero, zero)
            .unwrap();
        assert_eq!(
            frame.assignment_states[&update_target],
            SourceFlowAssignmentState::ReadonlyUpdate
        );
        assert_eq!(
            frame.assignment_states[&current.declaration],
            SourceFlowAssignmentState::Pending
        );
        for read in [header_read, update_target, body_read] {
            let snapshot = frame
                .snapshot_for_symbols_at(
                    context.store_mut_for_test(),
                    &globals,
                    read,
                    [fixed.symbol],
                )
                .unwrap();
            assert_eq!(snapshot.type_of(fixed.symbol), Some(zero));
            assert!(snapshot.reachable);
            assert!(!snapshot.incomplete);
        }
        assert!(frame.memo.contains_key(&(label, Some(fixed.symbol))));
        frame
            .complete_source_declaration(
                &host,
                current.declaration,
                current.symbol,
                current_type,
                current_type,
            )
            .unwrap();
        assert!(frame.memo.is_empty());
        for read in [first.1, second.1] {
            assert_eq!(
                frame
                    .snapshot_for_symbols_at(
                        context.store_mut_for_test(),
                        &globals,
                        read,
                        [fixed.symbol]
                    )
                    .unwrap()
                    .type_of(fixed.symbol),
                Some(zero)
            );
        }
        let memo = frame.memo.clone();
        let before = (
            context.store().type_len(),
            context.store().checker_link_allocated_lengths(),
            context.store().relation_state_snapshot(),
        );
        for _ in 0..2 {
            assert_eq!(
                frame
                    .snapshot_for_symbols_at(
                        context.store_mut_for_test(),
                        &globals,
                        second.1,
                        [fixed.symbol]
                    )
                    .unwrap()
                    .type_of(fixed.symbol),
                Some(zero)
            );
            assert_eq!(frame.memo, memo);
            assert!(frame.visiting.is_empty());
            assert!(frame.loop_snapshots.is_empty());
            assert_eq!(frame.reference, None);
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.store().relation_state_snapshot()
                ),
                before
            );
        }
        let diagnostics = context.diagnostics().clone();
        for _ in 0..2 {
            context.recheck_source_file(file).unwrap();
            assert_eq!(context.diagnostics(), &diagnostics);
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.store().relation_state_snapshot()
                ),
                before
            );
        }
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
                negated: false,
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
    fn logical_statement_flow_keeps_detached_conditions_and_replays_read_points() {
        for (index, argument) in ["value", "1", "'text'", "true", "null"]
            .into_iter()
            .enumerate()
        {
            let parsed = parse_source_file(&format!(
                "function emit(observer: {{next: (value: number) => void}}, value: number): void {{\n\
                   observer.next && observer.next({argument});\n\
                   value;\n\
                 }}",
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(2_410 + u32::try_from(index).unwrap());
            let mut context = loop_context(&parsed, file);
            let bound = context.file(file).unwrap().1.clone();
            let globals = context.global_types().clone();
            let (function, parameter, statements) = linear_function_nodes(&parsed, file, "emit");
            let [statement, after] = statements.as_slice() else {
                panic!("expected a logical statement and a following read")
            };
            let syntax = plan_source_linear_logical_statement_syntax(
                &parsed.arena,
                &bound,
                *statement,
                function,
            )
            .unwrap();
            assert!(matches!(
                SourceFlowPlan::preflight_linear(
                    &parsed.arena, &bound, context.store(), function,
                    [*statement, syntax.callee, *after], [], [], [],
                ),
                Err(SourceFlowError::Invariant(SourceFlowInvariant::UnknownCondition(node)))
                    if node == syntax.left
            ));
            assert!(matches!(
                SourceFlowPlan::preflight_linear(
                    &parsed.arena, &bound, context.store(), function,
                    [*statement, *after], [], [], [syntax.right],
                ),
                Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidCall(node)))
                    if node == syntax.right
            ));
            let plan = SourceFlowPlan::preflight_linear_with_logical_statements(
                &parsed.arena,
                &bound,
                context.store(),
                function,
                [*statement, *after],
                [],
                [],
                [],
                [syntax.clone()],
            )
            .unwrap();
            let proof = &plan.logical_statements[0];
            assert_eq!(plan.end, Some(plan.start));
            assert_eq!(proof.entry, plan.start);
            assert!(plan.calls.is_empty());
            assert_eq!(bound.flow_at(syntax.right), None);
            assert_eq!(
                bound
                    .flow_graph()
                    .nodes()
                    .get(proof.rows.pre_right)
                    .unwrap()
                    .antecedents,
                [proof.rows.left_true],
            );
            assert_eq!(
                bound
                    .flow_graph()
                    .nodes()
                    .get(proof.rows.join)
                    .unwrap()
                    .antecedents,
                [
                    proof.rows.left_false,
                    proof.rows.right_true,
                    proof.rows.right_false
                ],
            );
            for condition in [syntax.left, syntax.right] {
                assert_eq!(
                    plan.conditions.get(&condition),
                    Some(&SourceFlowCondition::Unchanged(condition))
                );
            }
            let symbol = bound.symbol(parameter).unwrap();
            let input = context.store().intrinsic_bootstrap().unwrap().unknown_type;
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            for _ in 0..2 {
                let mut frame = plan
                    .frame(&bound, [(symbol, input)].into_iter().collect())
                    .unwrap();
                let entry = frame
                    .snapshot_at(context.store_mut_for_test(), &globals, *statement)
                    .unwrap();
                for &(point, flow) in &proof.source_points {
                    if flow.is_some() {
                        assert_eq!(
                            frame
                                .snapshot_at(context.store_mut_for_test(), &globals, point)
                                .unwrap(),
                            entry,
                        );
                    }
                }
                assert_eq!(
                    frame
                        .snapshot_at(context.store_mut_for_test(), &globals, *after)
                        .unwrap(),
                    entry
                );
                assert_eq!(entry.type_of(symbol), Some(input));
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before,
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One bound graph checks retained, discarded, and damaged condition facts.
    fn linear_logical_conditions_keep_exact_reachable_edges() {
        for (index, (right, retained)) in [
            ("{ now: value }", false),
            ("{ now: value, get read() { return value && 1; } }", true),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(&format!(
                "function choose(value: number | false): number | false {{ \
                 const result = (value) && {right}; return value; }}",
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(2_450 + u32::try_from(index).unwrap());
            let context = loop_context(&parsed, file);
            let bound = context.file(file).unwrap().1;
            let node_ref = |node| NodeRef::new(parsed.arena.id(), file, node);
            let (function, parameter, statements) = linear_function_nodes(&parsed, file, "choose");
            let [_, returned] = statements.as_slice() else {
                panic!("one local precedes the outer return");
            };
            let (declaration, local) = parsed
                .arena
                .iter()
                .find_map(|(node, record)| match &record.data {
                    NodeData::VariableDeclaration(local) => Some((node_ref(node), local)),
                    _ => None,
                })
                .unwrap();
            let NodeData::BinaryExpression(binary) =
                &parsed.arena.get(local.initializer.unwrap()).unwrap().data
            else {
                panic!("the local has a logical initializer");
            };
            let condition = node_ref(binary.left);
            assert_eq!(
                parsed.arena.get(condition.node).unwrap().kind,
                SyntaxKind::ParenthesizedExpression,
            );
            let eager = parsed
                .arena
                .iter()
                .find_map(|(_, record)| match &record.data {
                    NodeData::PropertyAssignment(property) => Some(node_ref(property.initializer)),
                    _ => None,
                })
                .unwrap();
            let points = [node_ref(local.name), *returned];
            let assignment = SourceFlowAssignment {
                declaration,
                symbol: bound.symbol(declaration).unwrap(),
            };
            let fact = SourceTruthinessCondition {
                expression: condition,
                symbol: bound.symbol(parameter).unwrap(),
                negated: false,
            };
            let before = (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().relation_state_snapshot(),
            );
            let original = SourceFlowPlan::preflight_linear(
                &parsed.arena,
                bound,
                context.store(),
                function,
                points,
                [assignment],
                [],
                [],
            );
            if retained {
                assert_eq!(
                    original.unwrap_err(),
                    SourceFlowInvariant::UnknownCondition(condition).into(),
                );
            } else {
                assert!(original.unwrap().conditions.is_empty());
            }
            let prepare =
                |conditions: Vec<SourceTruthinessCondition>, points: Vec<NodeRef>, assign: bool| {
                    SourceFlowPlan::preflight_linear_with_conditions(
                        &parsed.arena,
                        bound,
                        context.store(),
                        function,
                        points,
                        conditions,
                        assign.then_some(assignment),
                        [],
                        [],
                    )
                };
            for _ in 0..2 {
                let plan = prepare(vec![fact], points.to_vec(), true).unwrap();
                assert_eq!(plan.conditions.len(), usize::from(retained));
                assert_eq!(
                    plan.conditions.get(&condition),
                    retained.then_some(&SourceFlowCondition::Truthiness(fact)),
                );
                plan.validate_flow_paths(bound).unwrap();
            }
            assert_eq!(
                prepare(vec![fact, fact], points.to_vec(), true).unwrap_err(),
                SourceFlowInvariant::DuplicateCondition(condition).into(),
            );
            assert_eq!(
                prepare(vec![fact], vec![points[0], points[0]], true).unwrap_err(),
                SourceFlowInvariant::DuplicatePoint(points[0]).into(),
            );
            let foreign = SourceTruthinessCondition {
                expression: NodeRef::new(condition.arena, FileId::new(2_499), condition.node),
                ..fact
            };
            assert_eq!(
                prepare(vec![foreign], points.to_vec(), true).unwrap_err(),
                SourceFlowInvariant::ForeignNode(foreign.expression).into(),
            );
            if retained {
                assert_eq!(
                    prepare(Vec::new(), points.to_vec(), true).unwrap_err(),
                    SourceFlowInvariant::UnknownCondition(condition).into(),
                );
                assert_eq!(bound.flow_graph().container_end(function), None);
                assert_eq!(
                    prepare(vec![fact], vec![eager], false).unwrap_err(),
                    SourceFlowInvariant::MissingConditionEdge {
                        condition,
                        true_edge: true,
                        false_edge: false,
                    }
                    .into(),
                );
                let getter = parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        (record.kind == SyntaxKind::GetAccessor).then_some(node_ref(node))
                    })
                    .unwrap();
                let nested = parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        let NodeData::Identifier(identifier) = &record.data else {
                            return None;
                        };
                        (identifier.text == "value"
                            && bound.flow_container(node_ref(node)) == Some(getter))
                        .then_some(node_ref(node))
                    })
                    .unwrap();
                assert_eq!(
                    prepare(
                        vec![SourceTruthinessCondition {
                            expression: nested,
                            ..fact
                        }],
                        points.to_vec(),
                        true,
                    )
                    .unwrap_err(),
                    SourceFlowInvariant::ContainerMismatch {
                        node: nested,
                        expected: function,
                        actual: getter,
                    }
                    .into(),
                );
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.store().relation_state_snapshot(),
                ),
                before,
            );
        }
    }

    #[test]
    fn logical_statement_flow_rejects_changed_rows_and_retained_proofs_without_writes() {
        let parsed = parse_source_file(concat!(
            "function emit(observer: {next: (value: number) => void}, value: number): void {\n",
            "  observer.next && observer.next(value);\n",
            "  value;\n",
            "}\n",
            "function other(observer: {next: (value: number) => void}, value: number): void {\n",
            "  observer.next && observer.next(value);\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_415);
        let context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let (function, _, statements) = linear_function_nodes(&parsed, file, "emit");
        let (other, _, _) = linear_function_nodes(&parsed, file, "other");
        let syntax = plan_source_linear_logical_statement_syntax(
            &parsed.arena,
            &bound,
            statements[0],
            function,
        )
        .unwrap();
        let plan = SourceFlowPlan::preflight_linear_with_logical_statements(
            &parsed.arena,
            &bound,
            context.store(),
            function,
            statements,
            [],
            [],
            [],
            [syntax.clone()],
        )
        .unwrap();
        let proof = &plan.logical_statements[0];
        let original_nodes = bound.flow_graph().nodes();
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for change in 0..8 {
            let mut nodes = original_nodes.clone();
            match change {
                0 => {
                    nodes.get_mut(proof.rows.left_false).unwrap().payload =
                        Some(FlowNodePayload::Ast(syntax.callee));
                }
                1 => nodes.get_mut(proof.rows.right_true).unwrap().antecedent = Some(proof.entry),
                2 => nodes.get_mut(proof.rows.right_false).unwrap().flags = FlowFlags::CALL,
                3 => {
                    nodes.get_mut(proof.rows.join).unwrap().antecedents.pop();
                }
                4 => nodes
                    .get_mut(proof.rows.join)
                    .unwrap()
                    .antecedents
                    .swap(0, 1),
                5 => {
                    nodes.get_mut(proof.rows.pre_right).unwrap().antecedents =
                        vec![proof.rows.left_false];
                }
                6 => {
                    nodes
                        .alloc(nodes.get(proof.rows.left_true).unwrap().clone())
                        .unwrap();
                }
                7 => {
                    nodes
                        .alloc(nodes.get(proof.rows.join).unwrap().clone())
                        .unwrap();
                }
                _ => unreachable!(),
            }
            for _ in 0..2 {
                assert!(
                    logical_statement_rows(&nodes, &syntax, proof.entry).is_err(),
                    "change {change}"
                );
            }
            nodes = original_nodes.clone();
            assert_eq!(
                logical_statement_rows(&nodes, &syntax, proof.entry),
                Ok(proof.rows)
            );
        }
        for change in 0..6 {
            let mut changed = plan.clone();
            let changed_proof = &mut changed.logical_statements[0];
            match change {
                0 => changed_proof.syntax.container = other,
                1 => changed_proof.rows.join = changed_proof.rows.pre_right,
                2 => {
                    let point = changed_proof
                        .source_points
                        .iter_mut()
                        .find(|(node, _)| *node == syntax.right_receiver)
                        .unwrap();
                    point.1 = Some(changed_proof.entry);
                }
                3 => {
                    changed.points.insert(syntax.right_receiver, proof.entry);
                }
                4 => {
                    changed.conditions.remove(&syntax.right);
                }
                5 => changed.end = Some(proof.rows.join),
                _ => unreachable!(),
            }
            for _ in 0..2 {
                assert!(
                    changed.frame(&bound, HashMap::new()).is_err(),
                    "change {change}"
                );
            }
            changed = plan.clone();
            assert!(changed.frame(&bound, HashMap::new()).is_ok());
        }
        let mut forged = syntax.clone();
        forged.right_receiver = syntax.left_receiver;
        assert!(
            SourceFlowPlan::preflight_linear_with_logical_statements(
                &parsed.arena,
                &bound,
                context.store(),
                function,
                [],
                [],
                [],
                [],
                [forged],
            )
            .is_err()
        );
        assert!(
            matches!(SourceFlowPlan::preflight_linear_with_logical_statements(
            &parsed.arena, &bound, context.store(), function,
            [], [], [], [], [syntax.clone(), syntax.clone()],
        ), Err(SourceFlowError::Invariant(SourceFlowInvariant::DuplicateCondition(node))) if node == syntax.left)
        );
        let mut missing_root = plan.clone();
        missing_root.logical_statements.clear();
        assert!(matches!(missing_root.validate_flow_paths(&bound),
            Err(SourceFlowError::Invariant(SourceFlowInvariant::MissingConditionEdge {condition, ..}))
                if condition == syntax.left
        ));
        assert!(plan.frame(&bound, HashMap::new()).is_ok());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths()
            ),
            before,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the mixed graph, rejected joins, and replay together.
    fn mixed_linear_conditions_keep_eager_facts_from_automatic_logical_points() {
        let parsed = parse_source_file(concat!(
            "function choose(value: number | false, observer: {next: (value: number | false) => void}): void { ",
            "const result = (value) && { now: value, get read() { return value && 1; } }; ",
            "observer.next && observer.next(value); return; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_451);
        let context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1;
        let reference = |node| NodeRef::new(parsed.arena.id(), file, node);
        let (function, parameter, statements) = linear_function_nodes(&parsed, file, "choose");
        let [_, logical_statement, _] = statements.as_slice() else {
            panic!("one initializer precedes the logical statement and return");
        };
        let (declaration, local) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| match &record.data {
                NodeData::VariableDeclaration(local) => Some((reference(node), local)),
                _ => None,
            })
            .unwrap();
        let NodeData::BinaryExpression(initializer) =
            &parsed.arena.get(local.initializer.unwrap()).unwrap().data
        else {
            panic!("the initializer keeps its eager logical condition");
        };
        let fact = SourceTruthinessCondition {
            expression: reference(initializer.left),
            symbol: bound.symbol(parameter).unwrap(),
            negated: false,
        };
        let assignment = SourceFlowAssignment {
            declaration,
            symbol: bound.symbol(declaration).unwrap(),
        };
        let syntax = plan_source_linear_logical_statement_syntax(
            &parsed.arena,
            bound,
            *logical_statement,
            function,
        )
        .unwrap();
        let getter = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::GetAccessor).then_some(reference(node))
            })
            .unwrap();
        let deferred_condition = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::BinaryExpression(binary) = &record.data else {
                    return None;
                };
                let left = reference(binary.left);
                (bound.flow_container(left) == Some(getter)).then_some(left)
            })
            .unwrap();
        let prepare = |points: Vec<NodeRef>,
                       facts: Vec<SourceTruthinessCondition>,
                       logical: Vec<SourceLinearLogicalStatementSyntax>| {
            SourceFlowPlan::preflight_linear_with_conditions_and_logical_statements(
                &parsed.arena,
                bound,
                context.store(),
                function,
                points,
                facts,
                [assignment],
                [],
                [],
                logical,
            )
        };
        assert_eq!(bound.flow_graph().container_end(function), None);
        assert!(
            retained_linear_truthiness_conditions(&parsed.arena, bound, function, &[], vec![fact],)
                .unwrap()
                .is_empty()
        );
        let before = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
            context.store().relation_state_snapshot(),
        );
        for _ in 0..2 {
            let plan = prepare(Vec::new(), vec![fact], vec![syntax.clone()]).unwrap();
            assert_eq!(plan.end, None);
            assert_eq!(plan.logical_statements.len(), 1);
            assert!(plan.calls.is_empty());
            assert_eq!(plan.conditions.len(), 3);
            assert_eq!(
                plan.conditions.get(&fact.expression),
                Some(&SourceFlowCondition::Truthiness(fact))
            );
            assert!(!plan.conditions.contains_key(&deferred_condition));
            for condition in [syntax.left, syntax.right] {
                assert_eq!(
                    plan.conditions.get(&condition),
                    Some(&SourceFlowCondition::Unchanged(condition))
                );
            }
            let proof = &plan.logical_statements[0];
            assert_eq!(plan.points.get(logical_statement), Some(&proof.entry));
            assert_eq!(
                plan.points.get(&syntax.right_receiver),
                Some(&proof.rows.left_true)
            );
            plan.validate_flow_paths(bound).unwrap();
            assert!(plan.frame(bound, HashMap::new()).is_ok());
            let mut damaged = plan.clone();
            damaged.conditions.remove(&fact.expression);
            assert_eq!(
                damaged.frame(bound, HashMap::new()).err(),
                Some(SourceFlowInvariant::UnknownCondition(fact.expression).into())
            );
            damaged = plan.clone();
            damaged.logical_statements[0].rows.join = proof.rows.pre_right;
            assert!(damaged.frame(bound, HashMap::new()).is_err());
            damaged = plan.clone();
            assert!(damaged.frame(bound, HashMap::new()).is_ok());
        }
        assert_eq!(
            prepare(Vec::new(), Vec::new(), vec![syntax.clone()]).unwrap_err(),
            SourceFlowInvariant::UnknownCondition(fact.expression).into()
        );
        assert_eq!(
            prepare(Vec::new(), vec![fact, fact], vec![syntax.clone()]).unwrap_err(),
            SourceFlowInvariant::DuplicateCondition(fact.expression).into()
        );
        assert_eq!(
            prepare(Vec::new(), vec![fact], vec![syntax.clone(), syntax.clone()]).unwrap_err(),
            SourceFlowInvariant::DuplicateCondition(syntax.left).into()
        );
        assert_eq!(
            prepare(
                Vec::new(),
                vec![
                    fact,
                    SourceTruthinessCondition {
                        expression: syntax.left,
                        ..fact
                    }
                ],
                vec![syntax.clone()]
            )
            .unwrap_err(),
            SourceFlowInvariant::DuplicateCondition(syntax.left).into()
        );
        assert_eq!(
            prepare(
                vec![*logical_statement, *logical_statement],
                vec![fact],
                vec![syntax.clone()]
            )
            .unwrap_err(),
            SourceFlowInvariant::DuplicatePoint(*logical_statement).into()
        );
        let foreign = SourceTruthinessCondition {
            expression: NodeRef::new(
                fact.expression.arena,
                FileId::new(2_499),
                fact.expression.node,
            ),
            ..fact
        };
        assert_eq!(
            prepare(Vec::new(), vec![foreign], vec![syntax.clone()]).unwrap_err(),
            SourceFlowInvariant::ForeignNode(foreign.expression).into()
        );
        assert!(prepare(vec![*logical_statement], vec![fact], vec![syntax]).is_ok());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().relation_state_snapshot()
            ),
            before,
        );
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
            context.store(),
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
    fn nullish_assignment_flow_keeps_nested_writes_conditional_and_replays() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(
            "function effects(value: number | undefined, side: number | undefined): void { \
             value ??= (side ??= 1); value; side; }",
        );
        let file = FileId::new(32_291);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let (function, _, statements) = linear_function_nodes(&parsed, file, "effects");
        let assignment = |name: &str| {
            let declaration = captured_variable(&parsed, file, name);
            let (expression, target) = parsed
                .arena
                .iter()
                .find_map(|(id, record)| {
                    let NodeData::BinaryExpression(binary) = &record.data else {
                        return None;
                    };
                    matches!(&parsed.arena.get(binary.left)?.data,
                    NodeData::Identifier(identifier) if identifier.text == name)
                    .then_some((
                        NodeRef::new(parsed.arena.id(), file, id),
                        NodeRef::new(parsed.arena.id(), file, binary.left),
                    ))
                })
                .unwrap();
            SourceFlowNullishAssignment {
                expression,
                target,
                declaration: Some(declaration),
                symbol: bound.symbol(declaration),
                readonly: false,
            }
        };
        let value = assignment("value");
        let side = assignment("side");
        let value_symbol = value.symbol.unwrap();
        let side_symbol = side.symbol.unwrap();
        let plan = SourceFlowPlan::preflight_linear_with_nullish_assignments(
            &parsed.arena,
            &bound,
            context.store(),
            &host,
            function,
            statements
                .iter()
                .copied()
                .chain([value.target, side.target]),
            [],
            [],
            [],
            [],
            [],
            [],
            [],
            [value, side],
        )
        .unwrap();
        let (number, undefined) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.undefined_type)
        };
        let optional = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[number, undefined],
                UnionReduction::Literal,
            )
            .unwrap();
        let base: SourceFlowTypes = [(value_symbol, optional), (side_symbol, optional)]
            .into_iter()
            .collect();
        for _ in 0..2 {
            let mut frame = plan
                .frame_with_captured_locals(context.store(), &host, &bound, base.clone())
                .unwrap();
            let right = frame
                .snapshot_at(context.store_mut_for_test(), &globals, side.target)
                .unwrap();
            assert_eq!(right.type_of(value_symbol), Some(undefined));
            assert_eq!(right.type_of(side_symbol), Some(optional));
            assert!(
                frame
                    .snapshot_at(context.store_mut_for_test(), &globals, statements[1])
                    .is_err()
            );
            frame
                .complete_assignment(side.target, side_symbol, number)
                .unwrap();
            assert!(frame.memo.is_empty());
            frame
                .complete_assignment(value.target, value_symbol, number)
                .unwrap();
            let after = frame
                .snapshot_at(context.store_mut_for_test(), &globals, statements[1])
                .unwrap();
            assert_eq!(after.type_of(value_symbol), Some(number));
            assert_eq!(after.type_of(side_symbol), Some(optional));
            assert_eq!(frame.declared_types, base);
            assert_eq!(
                frame.complete_assignment(value.target, value_symbol, number),
                Err(SourceFlowInvariant::AssignmentAlreadyCompleted(value.target).into())
            );
        }
        for changed in [
            SourceFlowNullishAssignment {
                declaration: side.declaration,
                ..value
            },
            SourceFlowNullishAssignment {
                symbol: side.symbol,
                ..value
            },
            SourceFlowNullishAssignment {
                readonly: true,
                ..value
            },
            SourceFlowNullishAssignment {
                expression: side.expression,
                ..value
            },
        ] {
            assert!(
                validate_source_nullish_assignment(
                    &parsed.arena,
                    &bound,
                    context.store(),
                    &host,
                    function,
                    changed,
                )
                .is_err()
            );
        }
    }

    #[test]
    fn nullish_assignment_flow_keeps_falsy_values_on_the_non_nullish_edge() {
        use crate::semantic::production::GlobalMergeCompletion;

        let parsed = parse_source_file(
            "function effects(value: string | number | boolean | undefined): void { \
             value ??= 1; value; }",
        );
        let file = FileId::new(32_292);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let (function, parameter, statements) = linear_function_nodes(&parsed, file, "effects");
        let expression = expression_statement_expression(&parsed, file, statements[0]);
        let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.node).unwrap().data
        else {
            panic!("expected nullish assignment")
        };
        let target = NodeRef::new(parsed.arena.id(), file, binary.left);
        let symbol = bound.symbol(parameter).unwrap();
        let assignment = SourceFlowNullishAssignment {
            expression,
            target,
            declaration: Some(parameter),
            symbol: Some(symbol),
            readonly: false,
        };
        let plan = SourceFlowPlan::preflight_linear_with_nullish_assignments(
            &parsed.arena,
            &bound,
            context.store(),
            &host,
            function,
            statements.iter().copied(),
            [],
            [],
            [],
            [],
            [],
            [],
            [],
            [assignment],
        )
        .unwrap();
        let (undefined, false_type, number) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.regular_false_type,
                bootstrap.number_type,
            )
        };
        let zero = context
            .store_mut_for_test()
            .regular_number_literal_type(ts_jsnum::Number::new(0.0))
            .unwrap();
        let empty = context
            .store_mut_for_test()
            .regular_string_literal_type(String::new())
            .unwrap();
        let present = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[zero, empty, false_type],
                UnionReduction::Literal,
            )
            .unwrap();
        let input = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[present, undefined],
                UnionReduction::Literal,
            )
            .unwrap();
        let edge = |wanted| {
            bound
                .flow_graph()
                .nodes()
                .iter()
                .enumerate()
                .find_map(|(index, node)| {
                    (node.flags.intersects(wanted)
                        && node.payload == Some(FlowNodePayload::Ast(target)))
                    .then(|| {
                        bound
                            .flow_graph()
                            .nodes()
                            .flow_ref(FlowNodeId(u32::try_from(index).unwrap()))
                            .unwrap()
                    })
                })
                .unwrap()
        };
        let mut frame = plan
            .frame(&bound, [(symbol, input)].into_iter().collect())
            .unwrap();
        assert_eq!(
            frame
                .resolve_flow(
                    context.store_mut_for_test(),
                    &globals,
                    edge(FlowFlags::TRUE_CONDITION),
                    0
                )
                .unwrap()
                .type_of(symbol),
            Some(present)
        );
        assert_eq!(
            frame
                .resolve_flow(
                    context.store_mut_for_test(),
                    &globals,
                    edge(FlowFlags::FALSE_CONDITION),
                    0
                )
                .unwrap()
                .type_of(symbol),
            Some(undefined)
        );
        frame.complete_assignment(target, symbol, number).unwrap();
        assert!(frame.memo.is_empty());
    }

    #[test]
    fn nullish_source_statement_keeps_readonly_assignment_state() {
        use crate::semantic::production::GlobalMergeCompletion;

        for readonly in [false, true] {
            let input = if readonly {
                "const value: number | undefined = undefined; value ??= 1; value;"
            } else {
                "let value: number | undefined; value ??= 1; value;"
            };
            let parsed = parse_source_file(input);
            let file = FileId::new(32_293);
            let mut context = loop_context(&parsed, file);
            let bound = context.file(file).unwrap().1.clone();
            let globals = context.global_types().clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(context.options().name_resolution),
            )
            .unwrap();
            let declaration = captured_variable(&parsed, file, "value");
            let symbol = bound.symbol(declaration).unwrap();
            let (expression, binary) = parsed
                .arena
                .iter()
                .find_map(|(id, record)| match &record.data {
                    NodeData::BinaryExpression(binary) => {
                        Some((NodeRef::new(parsed.arena.id(), file, id), binary))
                    }
                    _ => None,
                })
                .unwrap();
            let target = NodeRef::new(parsed.arena.id(), file, binary.left);
            let statement = NodeRef::new(
                parsed.arena.id(),
                file,
                parsed.arena.get(expression.node).unwrap().parent.unwrap(),
            );
            let assignment = SourceFlowNullishAssignment {
                expression,
                target,
                declaration: Some(declaration),
                symbol: Some(symbol),
                readonly,
            };
            let plan = SourceFlowPlan::preflight_source_statement_with_nullish_assignments(
                &parsed.arena,
                &bound,
                context.store(),
                &host,
                statement,
                [target],
                [],
                [],
                [],
                [],
                [assignment],
            )
            .unwrap();
            let (number, undefined) = {
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                (bootstrap.number_type, bootstrap.undefined_type)
            };
            let mut frame = plan
                .frame_with_captured_locals(
                    context.store(),
                    &host,
                    &bound,
                    [(symbol, undefined)].into_iter().collect(),
                )
                .unwrap();
            if readonly {
                assert_eq!(
                    frame.assignment_states[&target],
                    SourceFlowAssignmentState::ReadonlyUpdate
                );
                assert_eq!(
                    frame.complete_assignment(target, symbol, number),
                    Err(SourceFlowInvariant::AssignmentAlreadyCompleted(target).into())
                );
            } else {
                frame.complete_assignment(target, symbol, number).unwrap();
            }
            let after = frame
                .snapshot_for_symbols_at_end(context.store_mut_for_test(), &globals, [symbol])
                .unwrap();
            assert_eq!(
                after.type_of(symbol),
                Some(if readonly { undefined } else { number })
            );
        }
    }

    #[test]
    fn nullish_structural_owners_keep_real_entries_and_call_antecedents() {
        use crate::semantic::production::GlobalMergeCompletion;

        let state = |context: &CanonicalCheckerContext<'_>, parsed: &ParseResult, file: FileId| {
            let store = context.store();
            (
                [
                    store.type_len(),
                    store.type_alias_len(),
                    store.mapper_len(),
                    store.signature_len(),
                    store.symbol_len(),
                    store.symbol_store().symbol_table_len(),
                    store.index_info_len(),
                    store.type_resolution_len(),
                ],
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
                parsed
                    .arena
                    .iter()
                    .map(|(id, _)| {
                        let node = NodeRef::new(parsed.arena.id(), file, id);
                        (
                            node,
                            store.node_links(node).cloned(),
                            store.type_node_links(node).cloned(),
                            store.symbol_node_links(node).cloned(),
                            store.signature_links(node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                store
                    .symbol_store()
                    .symbols()
                    .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
                    .collect::<Vec<_>>(),
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned(),
                context.file(file).unwrap().1.flow_graph().clone(),
                context.diagnostics().clone(),
            )
        };
        let parsed = parse_source_file(concat!(
            "declare function effect(): number;\n",
            "function owner(value: number | undefined): void {\n",
            "  value ??= (effect(), 1); value;\n",
            "}\n",
            "function foreign(other: number | undefined): void { other; }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(32_294);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let (owner, declaration, statements) = linear_function_nodes(&parsed, file, "owner");
        let (foreign, _, _) = linear_function_nodes(&parsed, file, "foreign");
        let expression = expression_statement_expression(&parsed, file, statements[0]);
        let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.node).unwrap().data
        else {
            panic!("expected the actual nullish assignment");
        };
        let target = NodeRef::new(parsed.arena.id(), file, binary.left);
        let assignment = SourceFlowNullishAssignment {
            expression,
            target,
            declaration: Some(declaration),
            symbol: bound.symbol(declaration),
            readonly: false,
        };
        let call = parsed
            .arena
            .iter()
            .find_map(|(id, node)| {
                (node.kind == SyntaxKind::CallExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    id,
                ))
            })
            .unwrap();
        assert_eq!(bound.flow_container(expression), None);
        assert_eq!(bound.flow_at(expression), None);
        assert_eq!(bound.container(expression), Some(owner));
        assert_eq!(bound.flow_container(target), Some(owner));
        assert!(bound.flow_at(target).is_some());
        assert_eq!(bound.flow_container(call), None);
        let call_rows = bound
            .flow_graph()
            .nodes()
            .iter()
            .filter(|node| {
                node.flags.contains(FlowFlags::CALL)
                    && node.payload == Some(FlowNodePayload::Ast(call))
            })
            .collect::<Vec<_>>();
        assert_eq!(call_rows.len(), 1);
        let antecedent = call_rows[0].antecedent.unwrap();
        let globals = context.global_types().clone();
        let (number, undefined) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.undefined_type)
        };
        let optional = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[number, undefined],
                UnionReduction::Literal,
            )
            .unwrap();
        let before = state(&context, &parsed, file);
        let mut plan = SourceFlowPlan::preflight_linear_with_nullish_assignments(
            &parsed.arena,
            &bound,
            context.store(),
            &host,
            owner,
            statements.iter().copied().chain([target]),
            [],
            [],
            [],
            [call],
            [],
            [],
            [],
            [assignment],
        )
        .unwrap();
        assert_eq!(plan.nullish_calls.get(&call), Some(&antecedent));
        {
            let symbol = assignment.symbol.unwrap();
            let frame = plan
                .frame_with_captured_locals(
                    context.store(),
                    &host,
                    &bound,
                    [(symbol, optional)].into_iter().collect(),
                )
                .unwrap();
            assert_eq!(frame.declared_types.get(&symbol), Some(&optional));
        }
        assert_eq!(state(&context, &parsed, file), before);
        assert_eq!(
            validate_nullish_call(&parsed.arena, &bound, owner, call, &[assignment]),
            Ok(Some((statements[0], antecedent))),
        );
        assert_eq!(state(&context, &parsed, file), before);
        for wrong_owner in [foreign, bound.source_file()] {
            assert_eq!(
                validate_source_nullish_assignment(
                    &parsed.arena,
                    &bound,
                    context.store(),
                    &host,
                    wrong_owner,
                    assignment,
                ),
                Err(SourceFlowInvariant::InvalidParameterAssignment(target).into()),
            );
            assert_eq!(
                validate_nullish_call(&parsed.arena, &bound, wrong_owner, call, &[assignment]),
                Err(SourceFlowInvariant::InvalidCall(call).into()),
            );
            assert_eq!(state(&context, &parsed, file), before);
        }
        let other_target = expression_statement_expression(&parsed, file, statements[1]);
        assert_eq!(
            validate_source_nullish_assignment(
                &parsed.arena,
                &bound,
                context.store(),
                &host,
                owner,
                SourceFlowNullishAssignment {
                    target: other_target,
                    ..assignment
                },
            ),
            Err(SourceFlowInvariant::InvalidParameterAssignment(other_target).into()),
        );
        assert_eq!(state(&context, &parsed, file), before);
        let wrong_antecedent = bound.flow_at(target).unwrap();
        assert_ne!(wrong_antecedent, antecedent);
        plan.nullish_calls.insert(call, wrong_antecedent);
        assert_eq!(
            plan.frame_with_captured_locals(context.store(), &host, &bound, SourceFlowTypes::new())
                .err(),
            Some(SourceFlowInvariant::InvalidCall(call).into()),
        );
        assert_eq!(state(&context, &parsed, file), before);

        // A literal key retains a mutation even on a temporary receiver. A call key does not.
        for (index, key) in ["index()", "'x'"].into_iter().enumerate() {
            let parsed = parse_source_file(&format!(
                "declare function receiver(): {{ [key: string]: number | undefined }}; \
                 declare function index(): string; \
                 function owner(unused: number): void {{ receiver()[{key}] ??= 1; }}",
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(32_295 + u32::try_from(index).unwrap());
            let context = loop_context(&parsed, file);
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(context.options().name_resolution),
            )
            .unwrap();
            let (owner, _, statements) = linear_function_nodes(&parsed, file, "owner");
            let expression = expression_statement_expression(&parsed, file, statements[0]);
            let NodeData::BinaryExpression(binary) =
                &parsed.arena.get(expression.node).unwrap().data
            else {
                panic!("expected the actual member assignment");
            };
            let target = NodeRef::new(parsed.arena.id(), file, binary.left);
            let NodeData::ElementAccessExpression(element) =
                &parsed.arena.get(target.node).unwrap().data
            else {
                panic!("expected the actual element target");
            };
            let receiver = NodeRef::new(parsed.arena.id(), file, element.expression);
            let assignment = SourceFlowNullishAssignment {
                expression,
                target,
                declaration: None,
                symbol: None,
                readonly: false,
            };
            assert_eq!(bound.flow_container(expression), None);
            assert_eq!(bound.flow_container(receiver), None);
            let writes = bound
                .flow_graph()
                .nodes()
                .iter()
                .filter(|node| {
                    node.flags.contains(FlowFlags::ASSIGNMENT)
                        && node.payload == Some(FlowNodePayload::Ast(target))
                })
                .count();
            assert_eq!(writes, index);
            assert_eq!(bound.flow_container(target), (index == 1).then_some(owner));
            let before = state(&context, &parsed, file);
            assert_eq!(
                validate_source_nullish_assignment(
                    &parsed.arena,
                    &bound,
                    context.store(),
                    &host,
                    owner,
                    assignment,
                ),
                if index == 0 {
                    Ok(())
                } else {
                    Err(SourceFlowUnsupported::PropertyWrite(target).into())
                },
            );
            assert_eq!(state(&context, &parsed, file), before);
            assert_eq!(
                validate_nullish_call(&parsed.arena, &bound, owner, receiver, &[assignment]),
                Err(SourceFlowInvariant::InvalidCall(receiver).into()),
            );
            assert_eq!(state(&context, &parsed, file), before);
        }
    }

    #[test]
    fn parameter_assignment_flow_updates_only_its_authenticated_symbol() {
        for (index, parameters) in [
            "value: string | number, other: number",
            "[, value, , other]: (string | number)[]",
            "{ value, other }: { value: string | number; other: number }",
            "{ item: value, other }: { item: string | number; other: number }",
            "{ ['item']: value, other }: { item: string | number; other: number }",
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
                context.store(),
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
            let mut base = [(symbol, union), (bound.symbol(other).unwrap(), number)]
                .into_iter()
                .collect::<SourceFlowTypes>();
            let parent_symbol = bound.symbol(first_parameter).unwrap();
            base.entry(parent_symbol).or_insert(union);
            if first_parameter != parameter {
                assert_ne!(parent_symbol, symbol);
            }
            let mut expected = base.clone();
            expected.insert(symbol, number);
            for _ in 0..2 {
                let mut frame = plan.frame(&bound, base.clone()).unwrap();
                let before = frame
                    .snapshot_at(
                        context.store_mut_for_test(),
                        &globals,
                        *assignment_statement,
                    )
                    .unwrap();
                assert_eq!(before.types(), &base);
                assert_eq!(
                    frame.snapshot_at(context.store_mut_for_test(), &globals, *after_statement),
                    Err(SourceFlowInvariant::PendingAssignment(target).into()),
                );
                frame.complete_assignment(target, symbol, number).unwrap();
                let after = frame
                    .snapshot_at(context.store_mut_for_test(), &globals, *after_statement)
                    .unwrap();
                assert_eq!(after.types(), &expected);
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
                        context.store(),
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
    fn object_method_parameter_assignment_keeps_its_owner_and_flow_state() {
        let parsed = parse_source_file(concat!(
            "const object = { update(value: string | number, other: number): void { ",
            "value = 1; value; } };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(202_330);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let globals = context.global_types().clone();
        let (method, data) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| match &record.data {
                NodeData::MethodDeclaration(data) => {
                    Some((NodeRef::new(parsed.arena.id(), file, node), data))
                }
                _ => None,
            })
            .unwrap();
        let [parameter, other] = data.parameters.nodes.as_slice() else {
            panic!("the method must keep both parameters")
        };
        let parameter = NodeRef::new(parsed.arena.id(), file, *parameter);
        let other = NodeRef::new(parsed.arena.id(), file, *other);
        let symbol = bound.symbol(parameter).unwrap();
        let other_symbol = bound.symbol(other).unwrap();
        let owner = bound.symbol(method).unwrap();
        assert!(
            context
                .store()
                .source_object_literal_method_owner_is_exact(method, owner)
        );
        let NodeData::Block(body) = &parsed.arena.get(data.body.unwrap()).unwrap().data else {
            panic!("the method must keep its block")
        };
        let [before, after] = body.statements.nodes.as_slice() else {
            panic!("the method must keep its assignment and following read")
        };
        let before = NodeRef::new(parsed.arena.id(), file, *before);
        let after = NodeRef::new(parsed.arena.id(), file, *after);
        let expression = expression_statement_expression(&parsed, file, before);
        let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.node).unwrap().data
        else {
            panic!("the first statement must assign the parameter")
        };
        let target = NodeRef::new(parsed.arena.id(), file, binary.left);
        let assignment = SourceFlowParameterAssignment {
            target,
            parameter,
            symbol,
        };
        let (union, number) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_or_number_type, bootstrap.number_type)
        };
        let base = [(symbol, union), (other_symbol, number)]
            .into_iter()
            .collect::<SourceFlowTypes>();
        let mut expected = base.clone();
        expected.insert(symbol, number);
        for _ in 0..2 {
            let plan = SourceFlowPlan::preflight_linear(
                &parsed.arena,
                &bound,
                context.store(),
                method,
                [before, after],
                [],
                [assignment],
                [],
            )
            .unwrap();
            assert_eq!(plan.container, method);
            assert_eq!(plan.assignment_declarations.get(&target), Some(&parameter));
            let mut frame = plan.frame(&bound, base.clone()).unwrap();
            assert_eq!(
                frame
                    .snapshot_at(context.store_mut_for_test(), &globals, before)
                    .unwrap()
                    .types(),
                &base,
            );
            assert_eq!(
                frame.snapshot_at(context.store_mut_for_test(), &globals, after),
                Err(SourceFlowInvariant::PendingAssignment(target).into()),
            );
            frame.complete_assignment(target, symbol, number).unwrap();
            let checked = frame
                .snapshot_at(context.store_mut_for_test(), &globals, after)
                .unwrap();
            assert_eq!(checked.types(), &expected);
            assert_eq!(
                frame
                    .snapshot_at(context.store_mut_for_test(), &globals, after)
                    .unwrap(),
                checked,
            );
            assert_eq!(
                frame.complete_assignment(target, symbol, number),
                Err(SourceFlowInvariant::AssignmentAlreadyCompleted(target).into()),
            );
            assert_eq!(bound.symbol(parameter), Some(symbol));
            assert_eq!(bound.symbol(other), Some(other_symbol));
            assert!(
                context
                    .store()
                    .source_object_literal_method_owner_is_exact(method, owner)
            );
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn object_method_parameter_assignment_rejects_changed_owner_and_parameter_proofs() {
        let parsed = parse_source_file(concat!(
            "const object = { update(value: number, other: number): void { ",
            "value = 1; value; } };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(202_331);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let (method, data) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| match &record.data {
                NodeData::MethodDeclaration(data) => {
                    Some((NodeRef::new(parsed.arena.id(), file, node), data))
                }
                _ => None,
            })
            .unwrap();
        let [parameter, other] = data.parameters.nodes.as_slice() else {
            panic!("the method must keep both parameters")
        };
        let parameter = NodeRef::new(parsed.arena.id(), file, *parameter);
        let other = NodeRef::new(parsed.arena.id(), file, *other);
        let symbol = bound.symbol(parameter).unwrap();
        let other_symbol = bound.symbol(other).unwrap();
        let owner = bound.symbol(method).unwrap();
        let NodeData::Block(body) = &parsed.arena.get(data.body.unwrap()).unwrap().data else {
            panic!("the method must keep its block")
        };
        let [before, after] = body.statements.nodes.as_slice() else {
            panic!("the method must keep its assignment and following read")
        };
        let before = NodeRef::new(parsed.arena.id(), file, *before);
        let after = NodeRef::new(parsed.arena.id(), file, *after);
        let expression = expression_statement_expression(&parsed, file, before);
        let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.node).unwrap().data
        else {
            panic!("the first statement must assign the parameter")
        };
        let target = NodeRef::new(parsed.arena.id(), file, binary.left);
        let assignment = SourceFlowParameterAssignment {
            target,
            parameter,
            symbol,
        };
        let preflight = |store: &CanonicalTypeMapperStore, assignment| {
            SourceFlowPlan::preflight_linear(
                &parsed.arena,
                &bound,
                store,
                method,
                [before, after],
                [],
                [assignment],
                [],
            )
        };
        let reject = |store: &CanonicalTypeMapperStore, assignment| {
            let before = format!("{store:?}");
            for _ in 0..2 {
                assert!(matches!(
                    preflight(store, assignment),
                    Err(SourceFlowError::Invariant(
                        SourceFlowInvariant::InvalidParameterAssignment(node)
                    )) if node == target
                ));
                assert_eq!(format!("{store:?}"), before);
            }
        };
        let store = context.store_mut_for_test();
        assert!(preflight(store, assignment).is_ok());
        let parent = store.symbol(owner).unwrap().parent().unwrap();
        let name = store.symbol(owner).unwrap().name().to_owned();
        let members = store.symbol(parent).unwrap().members().unwrap();
        let flags = store.symbol(owner).unwrap().flags();
        let checks = store.symbol(owner).unwrap().check_flags();
        assert!(store.set_symbol_relationships(owner, None, None, None, None));
        reject(store, assignment);
        assert!(store.set_symbol_relationships(owner, None, None, Some(parent), None));
        assert!(preflight(store, assignment).is_ok());
        assert!(store.set_symbol_flags(owner, SymbolFlags::PROPERTY, checks));
        reject(store, assignment);
        assert!(store.set_symbol_flags(owner, flags, checks));
        assert!(preflight(store, assignment).is_ok());
        assert_eq!(
            store.insert_symbol(members, name.clone(), other_symbol),
            Some(Some(owner))
        );
        reject(store, assignment);
        assert_eq!(
            store.insert_symbol(members, name, owner),
            Some(Some(other_symbol))
        );
        assert!(preflight(store, assignment).is_ok());
        for forged in [
            SourceFlowParameterAssignment {
                symbol: other_symbol,
                ..assignment
            },
            SourceFlowParameterAssignment {
                parameter: other,
                symbol: other_symbol,
                ..assignment
            },
        ] {
            reject(store, forged);
        }
        assert!(preflight(store, assignment).is_ok());
        assert_eq!(bound.symbol(parameter), Some(symbol));
        assert_eq!(bound.symbol(other), Some(other_symbol));
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn object_parameter_assignment_flow_rejects_changed_binding_scope() {
        let parsed = parse_source_file(concat!(
            "function effects({ value, other }: { value: number; other: number }): void { ",
            "value = 1; value; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_408);
        let mut context = loop_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let (function, _, statements) = linear_function_nodes(&parsed, file, "effects");
        let locals = bound.locals(function).unwrap();
        let [symbol, other] = ["value", "other"].map(|name| {
            context
                .store()
                .symbol_table(locals)
                .unwrap()
                .get_source(name)
                .unwrap()
        });
        let parameter = context
            .store()
            .symbol(symbol)
            .unwrap()
            .value_declaration()
            .unwrap();
        let [assignment_statement, after_statement] = statements.as_slice() else {
            panic!("expected one assignment and one following statement")
        };
        let expression = expression_statement_expression(&parsed, file, *assignment_statement);
        let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.node).unwrap().data
        else {
            panic!("expected an assignment expression")
        };
        let target = NodeRef::new(parsed.arena.id(), file, binary.left);
        let assignment = SourceFlowParameterAssignment {
            target,
            parameter,
            symbol,
        };
        assert!(
            SourceFlowPlan::preflight_linear(
                &parsed.arena,
                &bound,
                context.store(),
                function,
                [*assignment_statement, *after_statement],
                [],
                [assignment],
                [],
            )
            .is_ok()
        );

        assert_eq!(
            context.store_mut_for_test().insert_symbol(
                locals,
                EscapedName::source("other"),
                symbol,
            ),
            Some(Some(other)),
        );
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        assert!(matches!(
            SourceFlowPlan::preflight_linear(
                &parsed.arena,
                &bound,
                context.store(),
                function,
                [*assignment_statement, *after_statement],
                [],
                [assignment],
                [],
            ),
            Err(SourceFlowError::Invariant(
                SourceFlowInvariant::InvalidParameterAssignment(node)
            )) if node == target
        ));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
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
