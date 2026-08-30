//! Exact source integration for direct and chained property reads.
//!
//! The recursively planned receiver must already have a canonical `any` type,
//! a published enum value, a validated class constructor, an imported
//! namespace, an authenticated published scalar-wrapper or `Math.random`
//! method, an exact global array reference with a published member, or belong
//! to the validated own-property object domain in `relater`. Ordinary reads can
//! query one source member before an interface's member table is ready.
//! Enum values reuse
//! their published
//! member identities. Class
//! constructors read their validated static member tables without treating
//! construct signatures as property-only objects. Namespace reexports retain
//! their export alias while reading the final value symbol. Validated class
//! getter/setter pairs expose their shared accessor symbol. Private class
//! members retain their owner-branded symbols and exact access diagnostics.
//! Class bodies use an AST-derived receiver context and an authenticated body
//! token for pending class headers. Initialization reads retain their binder
//! flow evidence separately from accessibility diagnostics.
//! Constructor writes use a separate target plan and keep read and write types distinct.
//! Top-level own-field writes validate the completed class without a body token.
//! Keyword-private and protected reads retain their declared types after an access error.
//! Exact
//! two-constituent
//! unions of source-declared type literals reuse the canonical union-property
//! adapter. A property missing from any union constituent recovers with
//! `errorType` plus a deferred TS2339 or stable-common-candidate TS2551
//! descriptor. A shared global `Object` member keeps its declaration symbol
//! when both constituents lack an own member. Mixed own/global members,
//! comparator-dependent suggestion ties, and apparent/index members stay
//! fail-closed. Optional members and optional
//! property chains retain their pinned `undefined` result. A member call is
//! admitted only when its exact
//! enclosing call grants callee capability and deliberately does not use the
//! union read adapter.

use std::cmp::Ordering;

use ts_ast::{FlowRef, Node, NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, EscapedNameRef, SemanticSymbolId, SymbolFlags};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    CanonicalCheckerRelatedInformation, CanonicalGlobalTypes, CanonicalTypeFormatFlags,
    CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable, SymbolNodeLinks,
    TypeDisplayUnavailable, TypeId, TypeNodeLinks, ValueSymbolLinks,
    array_types::CanonicalArrayTargets,
    bootstrap::UnionReduction,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    classes::{
        self, ClassConstructorVisibility, ClassHeritageMembersValidation, ClassMemberOrigin,
        ClassMemberSource, ClassPropertySide, ClassPropertyTypeDemand,
    },
    declared::preflight_node,
    enums,
    formatter::type_to_string_with_host_global_types_and_flags,
    instantiate::InstantiationSession,
    member_resolution::UnionPropertyError,
    relater::ResolvedOwnProperty,
    source::{PlannedExpression, PlannedExpressionKind, SourceCheckError},
    source_callables::{
        SourceCallableFamily, StoredSourceCallableValidation,
        source_arrow_owner_expando_exports_are_valid,
        source_function_owner_expando_exports_are_valid, validate_stored_source_callable,
    },
    source_flow::{ClassInitializationFrame, ClassPropertyFlowRead, SourceFlowError},
    source_imports::{source_file_namespace_wrapper_member, validated_source_file_namespace_owner},
    spelling::get_spelling_suggestion,
    store::SourceNodeParent,
    type_records::{StructuredTypeData, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

/// A source property form outside the dependency-closed read slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourcePropertyUnsupported {
    Access(NodeRef),
    Receiver(NodeRef),
    MemberCall(NodeRef),
    MissingOwnProperty {
        node: NodeRef,
        receiver_type: TypeId,
    },
    OptionalProperty {
        node: NodeRef,
        property: SemanticSymbolId,
    },
    ApparentObjectProperty {
        node: NodeRef,
        receiver_type: TypeId,
    },
    AmbiguousPropertySuggestion {
        node: NodeRef,
        receiver_type: TypeId,
    },
}

/// Exact property planning/execution failure without a fallback result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourcePropertyError {
    Unsupported(SourcePropertyUnsupported),
    PendingClassProperty(ClassPropertyTypeDemand),
    InvalidCache(NodeRef),
    Union {
        node: NodeRef,
        error: UnionPropertyError,
    },
    Relation(RelationUnavailable),
    Display(TypeDisplayUnavailable),
    Capacity(NodeRef),
    MissingDiagnostic(u32),
    Flow(SourceFlowError),
}

impl From<SourceFlowError> for SourcePropertyError {
    fn from(error: SourceFlowError) -> Self {
        Self::Flow(error)
    }
}

impl From<RelationUnavailable> for SourcePropertyError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

impl From<TypeDisplayUnavailable> for SourcePropertyError {
    fn from(error: TypeDisplayUnavailable) -> Self {
        Self::Display(error)
    }
}

impl std::fmt::Display for SourcePropertyError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(error) => {
                write!(formatter, "source property is unsupported: {error:?}")
            }
            Self::PendingClassProperty(demand) => {
                write!(
                    formatter,
                    "class property type is pending at {:?}",
                    demand.declaration()
                )
            }
            Self::InvalidCache(node) => {
                write!(formatter, "source property cache is invalid at {node:?}")
            }
            Self::Union { error, .. } => error.fmt(formatter),
            Self::Relation(error) => write!(formatter, "{error}"),
            Self::Display(error) => error.fmt(formatter),
            Self::Capacity(node) => {
                write!(
                    formatter,
                    "source property staging exhausted capacity at {node:?}"
                )
            }
            Self::MissingDiagnostic(code) => {
                write!(formatter, "source property diagnostic TS{code} is missing")
            }
            Self::Flow(error) => write!(formatter, "source property flow failed: {error:?}"),
        }
    }
}

impl std::error::Error for SourcePropertyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Relation(error) => Some(error),
            Self::Display(error) => Some(error),
            Self::Unsupported(_)
            | Self::PendingClassProperty(_)
            | Self::InvalidCache(_)
            | Self::Union { .. }
            | Self::Capacity(_)
            | Self::MissingDiagnostic(_)
            | Self::Flow(_) => None,
        }
    }
}

/// Keeps source-query errors separate from property access errors.
#[derive(Debug)]
pub(super) enum SourcePropertyQueryError {
    Property(SourcePropertyError),
    Source(SourceCheckError),
}

impl From<SourcePropertyError> for SourcePropertyQueryError {
    fn from(error: SourcePropertyError) -> Self {
        Self::Property(error)
    }
}

impl From<RelationUnavailable> for SourcePropertyQueryError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Property(SourcePropertyError::Relation(error))
    }
}

/// Fully proven property syntax plus its source-planned receiver.
#[derive(Clone, Debug)]
pub(super) struct SourcePropertyPlan {
    pub(super) node: NodeRef,
    pub(super) receiver: PlannedExpression,
    name_node: NodeRef,
    name: String,
    privacy: SourcePropertyPrivacy,
    position: SourcePropertyPosition,
    optional: bool,
    class_access: Option<ClassAccessContext>,
}

/// Class receiver facts proven from the registered source and binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ClassAccessContext {
    receiver: NodeRef,
    class_symbol: SemanticSymbolId,
    class_declaration: NodeRef,
    body_declaration: NodeRef,
    kind: ClassReceiverKind,
    side: ClassPropertySide,
    phase: ClassAccessPhase,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ClassReceiverKind {
    This,
    SuperProperty,
    SuperCall,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ClassAccessPhase {
    Constructor,
    PropertyInitializer,
    StaticBlock,
    Method,
    Deferred,
}

impl ClassAccessContext {
    pub(super) const fn receiver(&self) -> NodeRef {
        self.receiver
    }

    pub(super) const fn class_symbol(&self) -> SemanticSymbolId {
        self.class_symbol
    }

    pub(super) const fn class_declaration(&self) -> NodeRef {
        self.class_declaration
    }

    pub(super) const fn body_declaration(&self) -> NodeRef {
        self.body_declaration
    }

    pub(super) const fn is_deferred(&self) -> bool {
        matches!(self.phase, ClassAccessPhase::Deferred)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ClassBindingPropertyPlan {
    binding: NodeRef,
    property: NodeRef,
    target: NodeRef,
    name: String,
    context: ClassAccessContext,
}

impl ClassBindingPropertyPlan {
    pub(super) const fn target(&self) -> NodeRef {
        self.target
    }
    pub(super) const fn property(&self) -> NodeRef {
        self.property
    }
    pub(super) const fn receiver(&self) -> NodeRef {
        self.context.receiver
    }
}

/// Retains the real binding or assignment property. No property-access node is synthesized.
pub(super) fn plan_class_binding_property(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    binding: NodeRef,
    receiver: NodeRef,
) -> Result<ClassBindingPropertyPlan, SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(binding);
    let record = class_access_node(store, host, binding)?;
    let parent = NodeRef::new(
        binding.arena,
        binding.file,
        record.parent.ok_or_else(invalid)?,
    );
    let parent_record = class_access_node(store, host, parent)?;
    let (property, target) = match &record.data {
        NodeData::BindingElement(element)
            if record.kind == SyntaxKind::BindingElement
                && element.initializer.is_none()
                && element.dot_dot_dot_token.is_none()
                && element.flow_node.is_none()
                && element.facts == 0 =>
        {
            let NodeData::BindingPattern(pattern) = &parent_record.data else {
                return Err(invalid());
            };
            let declaration = NodeRef::new(
                binding.arena,
                binding.file,
                parent_record.parent.ok_or_else(invalid)?,
            );
            let NodeData::VariableDeclaration(variable) =
                &class_access_node(store, host, declaration)?.data
            else {
                return Err(invalid());
            };
            if parent_record.kind != SyntaxKind::ObjectBindingPattern
                || !pattern.elements.nodes.contains(&binding.node)
                || variable.name != parent.node
                || variable.initializer != Some(receiver.node)
                || variable.type_.is_some()
            {
                return Err(unsupported_access(binding));
            }
            let target = element.name.ok_or_else(invalid)?;
            (element.property_name.unwrap_or(target), target)
        }
        NodeData::PropertyAssignment(property)
            if record.kind == SyntaxKind::PropertyAssignment && property.facts == 0 =>
        {
            (property.name, property.initializer)
        }
        NodeData::ShorthandPropertyAssignment(property)
            if record.kind == SyntaxKind::ShorthandPropertyAssignment
                && property.object_assignment_initializer.is_none()
                && property.facts == 0 =>
        {
            (property.name, property.name)
        }
        _ => return Err(unsupported_access(binding)),
    };
    if !matches!(record.data, NodeData::BindingElement(_)) {
        let NodeData::ObjectLiteralExpression(object) = &parent_record.data else {
            return Err(invalid());
        };
        let assignment = NodeRef::new(
            binding.arena,
            binding.file,
            parent_record.parent.ok_or_else(invalid)?,
        );
        let assignment_record = class_access_node(store, host, assignment)?;
        let NodeData::BinaryExpression(binary) = &assignment_record.data else {
            return Err(invalid());
        };
        if parent_record.kind != SyntaxKind::ObjectLiteralExpression
            || !object.properties.nodes.contains(&binding.node)
            || binary.left != parent.node
            || binary.right != receiver.node
            || class_access_node(
                store,
                host,
                NodeRef::new(binding.arena, binding.file, binary.operator_token),
            )?
            .kind
                != SyntaxKind::EqualsToken
        {
            return Err(unsupported_access(binding));
        }
    }
    let target = NodeRef::new(binding.arena, binding.file, target);
    let property = NodeRef::new(binding.arena, binding.file, property);
    let target_record = class_access_node(store, host, target)?;
    let property_record = class_access_node(store, host, property)?;
    let name = match &property_record.data {
        NodeData::Identifier(identifier)
            if property_record.kind == SyntaxKind::Identifier && identifier.flow_node.is_none() =>
        {
            identifier.text.clone()
        }
        NodeData::StringLiteral(literal)
            if property_record.kind == SyntaxKind::StringLiteral && literal.token_flags.0 == 0 =>
        {
            literal.text.clone()
        }
        _ => return Err(unsupported_access(property)),
    };
    if record.flags.0 != 0
        || parent_record.flags.0 != 0
        || target_record.kind != SyntaxKind::Identifier
        || target_record.flags.0 != 0
        || target_record.parent != Some(binding.node)
        || property_record.parent != Some(binding.node)
        || property_record.flags.0 != 0
        || name.is_empty()
    {
        return Err(invalid());
    }
    let context = plan_class_access_context(store, host, receiver)?
        .ok_or_else(|| unsupported_access(receiver))?;
    if context.kind != ClassReceiverKind::This {
        return Err(unsupported_access(receiver));
    }
    Ok(ClassBindingPropertyPlan {
        binding,
        property,
        target,
        name,
        context,
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_class_binding_property(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &ClassBindingPropertyPlan,
    receiver_type: TypeId,
    flow: &mut ClassInitializationFrame<'_, '_>,
) -> Result<CheckedSourceProperty, SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(plan.property);
    if plan_class_binding_property(store, host, plan.binding, plan.receiver())? != *plan {
        return Err(invalid());
    }
    let identities = class_receiver_identities(store, host, &plan.context, Some(flow))?;
    if identities.receiver_type(&plan.context)? != receiver_type {
        return Err(invalid());
    }
    let lookup_type = identities.lookup_type(&plan.context)?;
    let symbol = store
        .type_payload(lookup_type)
        .and_then(|record| record.data().structured())
        .and_then(|structured| structured.members)
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source(&plan.name))
        .ok_or_else(|| unsupported_access(plan.property))?;
    let (property, member) = class_context_member_for_symbol(
        store,
        host,
        plan.property,
        lookup_type,
        &plan.context,
        identities,
        symbol,
    )?;
    let kind = class_accessibility_diagnostic(
        store,
        host,
        &plan.context,
        &member,
        SourcePropertyPrivacy::Identifier,
    )?;
    let diagnostics = kind
        .into_iter()
        .map(|kind| SourcePropertyDiagnostic {
            name_node: plan.property,
            receiver_type,
            missing_type: None,
            suggestion: None,
            private_owner: None,
            accessibility: Some(ClassPropertyAccessDiagnostic::Class {
                context: plan.context,
                property: symbol,
                lookup_type,
                kind,
                binding: Some(plan.binding),
            }),
        })
        .collect();
    let type_ = if property.optional && options.intrinsic.strict_null_checks {
        let undefined = store
            .intrinsic_bootstrap()
            .ok_or_else(invalid)?
            .undefined_or_missing_type;
        property_union_type(
            store,
            Some(globals),
            plan.property,
            &[property.type_, undefined],
            Some(symbol),
        )?
    } else {
        property.type_
    };
    Ok(CheckedSourceProperty { type_, diagnostics })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CheckedClassReceiver {
    pub(super) type_: TypeId,
    pub(super) diagnostics: Vec<SourcePropertyDiagnostic>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourcePropertyPrivacy {
    Identifier,
    Private { enclosing_class: Option<NodeRef> },
}

/// The exact source position for which a property access was proven.
///
/// Retaining this capability in both syntax and finished plans prevents an
/// ordinary read plan from being repurposed as a member-call callee.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourcePropertyPosition {
    Read,
    CallCallee(NodeRef),
    WriteTarget(NodeRef),
}

/// Property-access syntax proven before recursive source planning starts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectSourcePropertySyntax {
    node: NodeRef,
    receiver: NodeRef,
    name_node: NodeRef,
    name: String,
    privacy: SourcePropertyPrivacy,
    position: SourcePropertyPosition,
    optional: bool,
}

impl DirectSourcePropertySyntax {
    pub(super) fn receiver(&self) -> NodeRef {
        self.receiver
    }

    pub(super) fn name_node(&self) -> NodeRef {
        self.name_node
    }
}

/// An own-field write outside class bodies. It cannot authorize `this` access.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct OwnClassPropertyWritePlan {
    assignment: super::assignment::OwnClassPropertyAssignmentPlan,
    property: DirectSourcePropertySyntax,
    member: ClassMemberSource,
}

impl OwnClassPropertyWritePlan {
    pub(super) const fn assignment(&self) -> &super::assignment::OwnClassPropertyAssignmentPlan {
        &self.assignment
    }

    pub(super) const fn member_source(&self) -> &ClassMemberSource {
        &self.member
    }

    pub(super) fn name(&self) -> &str {
        &self.property.name
    }
}

pub(super) struct CheckedOwnClassPropertyWrite {
    pub(super) type_: TypeId,
    pub(super) declared_type: TypeId,
    pub(super) diagnostic: Option<CanonicalCheckerDiagnostic>,
}

/// Retains the binder's own field and rejects unsupported members before execution.
#[allow(clippy::too_many_lines)] // The source member, side, and receiver form one write proof.
pub(super) fn plan_own_class_property_write(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    assignment: &super::assignment::OwnClassPropertyAssignmentPlan,
) -> Result<OwnClassPropertyWritePlan, SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(assignment.left);
    let (arena, bound) = host.source(assignment.statement).ok_or_else(invalid)?;
    if super::assignment::plan_own_class_property_assignment(
        arena,
        bound,
        store,
        host,
        assignment.statement,
    )
    .map_err(|_| invalid())?
        != Some(*assignment)
    {
        return Err(invalid());
    }
    for node in [
        assignment.statement,
        assignment.expression,
        assignment.left,
        assignment.right,
        assignment.receiver,
        assignment.class_declaration,
    ] {
        class_access_node(store, host, node)?;
    }
    let property = plan_direct_source_property_syntax_at(
        arena,
        store,
        assignment.left,
        SourcePropertyPosition::WriteTarget(assignment.expression),
    )?;
    if property.receiver != assignment.receiver
        || property.privacy != SourcePropertyPrivacy::Identifier
        || property.optional
    {
        return Err(unsupported_access(assignment.left));
    }
    class_access_node(store, host, property.name_node)?;
    if let Some(instance) = store
        .declared_type_links(assignment.class_symbol)
        .and_then(|links| links.declared_type)
        && store.type_payload(instance).is_some_and(|record| {
            record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        })
        && classes::validate_class_heritage_members(store, instance)
            != ClassHeritageMembersValidation::Valid
    {
        return Err(invalid());
    }
    let owner = store.symbol(assignment.class_symbol).ok_or_else(invalid)?;
    let table = match assignment.side {
        ClassPropertySide::Instance => owner.members(),
        ClassPropertySide::Static => owner.exports(),
    }
    .and_then(|table| store.symbol_table(table))
    .ok_or_else(invalid)?;
    let symbol = table
        .get_source(&property.name)
        .ok_or_else(|| unsupported_access(assignment.left))?;
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    if record.flags() != SymbolFlags::PROPERTY {
        return Err(unsupported_access(assignment.left));
    }
    let declaration = record.value_declaration().ok_or_else(invalid)?;
    let declaration_record = class_access_node(store, host, declaration)?;
    let NodeData::PropertyDeclaration(field) = &declaration_record.data else {
        return Err(unsupported_access(assignment.left));
    };
    if classes::class_member_visibility(store, declaration) != ClassConstructorVisibility::Public
        || ts_binder::canonical_has_syntactic_modifier(
            arena,
            declaration.node,
            SyntaxKind::AccessorKeyword,
        )
        || ts_binder::canonical_has_syntactic_modifier(
            arena,
            declaration.node,
            SyntaxKind::AbstractKeyword,
        )
    {
        return Err(unsupported_access(assignment.left));
    }
    let NodeData::ClassDeclaration(class) =
        &class_access_node(store, host, assignment.class_declaration)?.data
    else {
        return Err(invalid());
    };
    let readonly = ts_binder::canonical_has_syntactic_modifier(
        arena,
        declaration.node,
        SyntaxKind::ReadonlyKeyword,
    );
    if record.parent() != Some(assignment.class_symbol)
        || record.declarations() != Some(&[declaration])
        || record.name().as_utf8() != Some(property.name.as_str())
        || record.check_flags() != CheckFlags::NONE
            && (!readonly || record.check_flags() != CheckFlags::READONLY)
        || store.get_merged_symbol(symbol) != Some(symbol)
        || bound.symbol(declaration) != Some(symbol)
        || declaration_record.parent != Some(assignment.class_declaration.node)
        || !class.members.nodes.contains(&declaration.node)
        || class_member_side(store, host, declaration, field.modifiers.as_ref())? != assignment.side
    {
        return Err(invalid());
    }
    Ok(OwnClassPropertyWritePlan {
        assignment: *assignment,
        property,
        member: ClassMemberSource {
            symbol,
            declaring_class: assignment.class_symbol,
            declaration,
            origin: ClassMemberOrigin::Field {
                initializer: field
                    .initializer
                    .map(|node| NodeRef::new(declaration.arena, declaration.file, node)),
            },
            side: assignment.side,
            visibility: ClassConstructorVisibility::Public,
            readonly,
            abstract_: false,
        },
    })
}

/// Checks a completed class and publishes the exact write target, without a body token.
pub(super) fn check_own_class_property_write_target(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    options: CanonicalCheckerOptions,
    plan: &OwnClassPropertyWritePlan,
    receiver_type: TypeId,
) -> Result<CheckedOwnClassPropertyWrite, SourcePropertyError> {
    let checked =
        validate_own_class_property_write_target(store, host, options, plan, receiver_type)?;
    publish_property_links(
        store,
        plan.assignment.left,
        Some(plan.member.symbol),
        checked.type_,
    )?;
    Ok(checked)
}

#[allow(clippy::too_many_lines)] // Validate the completed class and both sides of the write together.
pub(super) fn validate_own_class_property_write_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    options: CanonicalCheckerOptions,
    plan: &OwnClassPropertyWritePlan,
    receiver_type: TypeId,
) -> Result<CheckedOwnClassPropertyWrite, SourcePropertyError> {
    let assignment = plan.assignment();
    let invalid = || SourcePropertyError::InvalidCache(assignment.left);
    let replay =
        plan_own_class_property_write(store, host, assignment).map_err(|error| match error {
            SourcePropertyError::Unsupported(_) => invalid(),
            error => error,
        })?;
    if replay != *plan {
        return Err(invalid());
    }
    let instance = store
        .declared_type_links(assignment.class_symbol)
        .and_then(|links| links.declared_type)
        .ok_or_else(|| unsupported_access(assignment.left))?;
    if classes::validate_class_heritage_members(store, instance)
        != ClassHeritageMembersValidation::Valid
    {
        return Err(invalid());
    }
    let expected_receiver = match assignment.side {
        ClassPropertySide::Instance => instance,
        ClassPropertySide::Static => store
            .value_symbol_links(assignment.class_symbol)
            .and_then(|links| links.resolved_type)
            .ok_or_else(invalid)?,
    };
    if receiver_type != expected_receiver {
        return Err(SourcePropertyError::Unsupported(
            SourcePropertyUnsupported::Receiver(assignment.receiver),
        ));
    }
    if store.type_node_links(assignment.receiver)
        != Some(&TypeNodeLinks {
            resolved_type: Some(receiver_type),
            ..TypeNodeLinks::default()
        })
        || store
            .symbol_node_links(assignment.receiver)
            .and_then(|links| links.resolved_symbol)
            .is_some_and(|symbol| symbol != assignment.receiver_symbol)
        || classes::class_member_source(store, host, plan.member.symbol).map_err(|_| invalid())?
            != plan.member
    {
        return Err(invalid());
    }
    let structured = store
        .type_payload(receiver_type)
        .and_then(|record| record.data().structured())
        .ok_or_else(invalid)?;
    if structured
        .members
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source(&plan.property.name))
        != Some(plan.member.symbol)
        || structured
            .properties
            .as_deref()
            .is_none_or(|properties| !properties.contains(&plan.member.symbol))
    {
        return Err(invalid());
    }
    let links = store
        .value_symbol_links(plan.member.symbol)
        .ok_or_else(invalid)?;
    let declared = links.resolved_type.ok_or_else(invalid)?;
    if links
        != &(ValueSymbolLinks {
            resolved_type: Some(declared),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(invalid());
    }
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    if bootstrap.options != options.intrinsic {
        return Err(invalid());
    }
    let type_ = if plan.member.readonly {
        bootstrap.error_type
    } else {
        declared
    };
    let diagnostic = plan
        .member
        .readonly
        .then(|| {
            Ok::<_, SourcePropertyError>(CanonicalCheckerDiagnostic {
                node: Some(plan.property.name_node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(2540).ok_or(SourcePropertyError::MissingDiagnostic(2540))?,
                    [plan.property.name.clone()],
                ),
                related_information: Vec::new(),
            })
        })
        .transpose()?;
    validate_property_link_targets(store, assignment.left, Some(plan.member.symbol), type_)?;
    Ok(CheckedOwnClassPropertyWrite {
        type_,
        declared_type: declared,
        diagnostic,
    })
}

/// Applies checked source-file writes before publishing a later own-field read.
#[allow(clippy::too_many_lines)] // Keep class ownership, read position, and flow publication together.
pub(super) fn check_own_class_property_flow_read(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    options: CanonicalCheckerOptions,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
    flow: &super::source_flow::OwnClassPropertyFlow,
) -> Result<Option<CheckedSourceProperty>, SourcePropertyError> {
    let Some(receiver_symbol) = flow.matching_receiver_symbol(store, host, plan.receiver.node)?
    else {
        return Ok(None);
    };
    if !flow.has_reference(receiver_symbol, &plan.name) {
        return Ok(None);
    }
    let invalid = || SourcePropertyError::InvalidCache(plan.node);
    let (arena, _) = host.source(plan.node).ok_or_else(invalid)?;
    class_access_node(store, host, plan.node)?;
    let syntax = plan_direct_source_property_syntax_at(arena, store, plan.node, plan.position)?;
    if syntax.receiver != plan.receiver.node
        || syntax.name_node != plan.name_node
        || syntax.name != plan.name
        || syntax.privacy != plan.privacy
        || syntax.optional != plan.optional
    {
        return Err(invalid());
    }
    if !plan.is_read() || plan.optional || plan.privacy != SourcePropertyPrivacy::Identifier {
        return Err(unsupported_access(plan.node));
    }
    let receiver = store.type_payload(receiver_type).ok_or_else(invalid)?;
    let owner = receiver
        .symbol()
        .ok_or_else(|| unsupported_access(plan.node))?;
    let instance = store
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .ok_or_else(|| unsupported_access(plan.node))?;
    if classes::validate_class_heritage_members(store, instance)
        != ClassHeritageMembersValidation::Valid
    {
        return Err(invalid());
    }
    let side = if receiver_type == instance {
        ClassPropertySide::Instance
    } else if store
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        == Some(receiver_type)
    {
        ClassPropertySide::Static
    } else {
        return Err(unsupported_access(plan.node));
    };
    let structured = receiver.data().structured().ok_or_else(invalid)?;
    let member = structured
        .members
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source(&plan.name))
        .ok_or_else(|| unsupported_access(plan.node))?;
    if structured
        .properties
        .as_deref()
        .is_none_or(|properties| !properties.contains(&member))
    {
        return Err(invalid());
    }
    let source = classes::class_member_source(store, host, member).map_err(|_| invalid())?;
    if source.declaring_class != owner
        || source.side != side
        || source.visibility != ClassConstructorVisibility::Public
        || !matches!(source.origin, ClassMemberOrigin::Field { .. })
        || store
            .symbol(member)
            .is_none_or(|symbol| symbol.flags() != SymbolFlags::PROPERTY)
    {
        return Err(unsupported_access(plan.node));
    }
    let declared = store
        .value_symbol_links(member)
        .and_then(|links| links.resolved_type)
        .ok_or_else(invalid)?;
    let Some(type_) = flow.read_type(
        store,
        host,
        options,
        plan.node,
        receiver_symbol,
        receiver_type,
        member,
        declared,
    )?
    else {
        return Ok(None);
    };
    publish_property_links(store, plan.node, Some(member), type_)?;
    Ok(Some(CheckedSourceProperty {
        type_,
        diagnostics: Vec::new(),
    }))
}

/// A class field assignment with a separate left-hand-side position proof.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceClassPropertyWritePlan {
    statement: NodeRef,
    assignment: NodeRef,
    value: NodeRef,
    property: DirectSourcePropertySyntax,
    context: ClassAccessContext,
    member: SemanticSymbolId,
    declaration: NodeRef,
    origin: ClassMemberOrigin,
    readonly: bool,
}

impl SourceClassPropertyWritePlan {
    pub(super) const fn statement(&self) -> NodeRef {
        self.statement
    }

    pub(super) const fn node(&self) -> NodeRef {
        self.assignment
    }

    pub(super) const fn target(&self) -> NodeRef {
        self.property.node
    }

    pub(super) const fn receiver(&self) -> NodeRef {
        self.property.receiver
    }

    pub(super) const fn value(&self) -> NodeRef {
        self.value
    }

    pub(super) const fn context(&self) -> &ClassAccessContext {
        &self.context
    }

    pub(super) const fn member(&self) -> SemanticSymbolId {
        self.member
    }

    pub(super) fn name(&self) -> &str {
        &self.property.name
    }
}

/// The real class body token and field types used for one assignment check.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CheckedClassPropertyWriteTarget {
    plan: SourceClassPropertyWritePlan,
    access: classes::ClassBodyAccessToken,
    member: ClassMemberSource,
    read_type: TypeId,
    write_type: TypeId,
}

impl CheckedClassPropertyWriteTarget {
    pub(super) const fn plan(&self) -> &SourceClassPropertyWritePlan {
        &self.plan
    }

    pub(super) const fn access_token(&self) -> &classes::ClassBodyAccessToken {
        &self.access
    }

    pub(super) const fn member_source(&self) -> &ClassMemberSource {
        &self.member
    }

    pub(super) const fn read_type(&self) -> TypeId {
        self.read_type
    }

    pub(super) const fn write_type(&self) -> TypeId {
        self.write_type
    }
}

pub(super) fn plan_class_property_write(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    assignment: NodeRef,
) -> Result<SourceClassPropertyWritePlan, SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(assignment);
    let record = class_access_node(store, host, assignment)?;
    let NodeData::BinaryExpression(binary) = &record.data else {
        return Err(unsupported_access(assignment));
    };
    let target = NodeRef::new(assignment.arena, assignment.file, binary.left);
    let value = NodeRef::new(assignment.arena, assignment.file, binary.right);
    let operator = NodeRef::new(assignment.arena, assignment.file, binary.operator_token);
    let operator_record = class_access_node(store, host, operator)?;
    let value_record = class_access_node(store, host, value)?;
    if record.kind != SyntaxKind::BinaryExpression
        || record.flags.0 != 0
        || binary.facts != 0
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.modifiers.is_some()
        || operator_record.kind != SyntaxKind::EqualsToken
    {
        return Err(unsupported_access(assignment));
    }
    if operator_record.parent != Some(assignment.node)
        || operator_record.flags.0 != 0
        || !matches!(operator_record.data, NodeData::Token(_))
        || value_record.parent != Some(assignment.node)
        || value_record.flags.0 != 0
    {
        return Err(invalid());
    }
    let (arena, bound) = host.source(assignment).ok_or_else(invalid)?;
    let property = plan_direct_source_property_syntax_at(
        arena,
        store,
        target,
        SourcePropertyPosition::WriteTarget(assignment),
    )?;
    let target_record = class_access_node(store, host, target)?;
    if target_record.range.end > operator_record.range.start
        || operator_record.range.end > value_record.range.start
        || value_record.range.end > record.range.end
    {
        return Err(invalid());
    }
    let context = plan_class_access_context(store, host, property.receiver)?
        .ok_or_else(|| unsupported_access(target))?;
    if context.kind != ClassReceiverKind::This
        || context.side != ClassPropertySide::Instance
        || !matches!(
            context.phase,
            ClassAccessPhase::Constructor | ClassAccessPhase::Method
        )
    {
        return Err(unsupported_access(target));
    }
    let declaration = class_access_node(store, host, context.body_declaration)?;
    let body = match &declaration.data {
        NodeData::ConstructorDeclaration(constructor) => constructor.body,
        NodeData::MethodDeclaration(method) => method.body,
        _ => return Err(invalid()),
    };
    let body = body.ok_or_else(invalid)?;
    let statement = NodeRef::new(
        assignment.arena,
        assignment.file,
        record.parent.ok_or_else(invalid)?,
    );
    let statement_record = class_access_node(store, host, statement)?;
    if !matches!(&statement_record.data, NodeData::ExpressionStatement(data)
        if data.expression == assignment.node && data.flow_node.is_none())
        || statement_record.flags.0 != 0
    {
        return Err(unsupported_access(assignment));
    }
    let mut child = statement;
    let mut visited = std::collections::HashSet::new();
    loop {
        if !visited.insert(child) {
            return Err(invalid());
        }
        let parent = class_access_node(store, host, child)?
            .parent
            .ok_or_else(invalid)?;
        let parent = NodeRef::new(assignment.arena, assignment.file, parent);
        let parent_record = class_access_node(store, host, parent)?;
        let valid_parent = match &parent_record.data {
            NodeData::Block(block) => {
                block.statements.nodes.contains(&child.node)
                    && block.flow_node.is_none()
                    && block.facts == 0
            }
            NodeData::IfStatement(branch) => {
                (branch.then_statement == child.node || branch.else_statement == Some(child.node))
                    && branch.flow_node.is_none()
                    && branch.facts == 0
            }
            _ => return Err(unsupported_access(assignment)),
        };
        if parent_record.flags.0 != 0 || !valid_parent {
            return Err(invalid());
        }
        if parent.node == body {
            break;
        }
        child = parent;
    }
    let owner = store.symbol(context.class_symbol).ok_or_else(invalid)?;
    let members = owner
        .members()
        .and_then(|members| store.symbol_table(members))
        .ok_or_else(|| unsupported_access(target))?;
    let member = match property.privacy {
        SourcePropertyPrivacy::Identifier => members.get_source(&property.name),
        SourcePropertyPrivacy::Private { enclosing_class }
            if enclosing_class == Some(context.class_declaration) =>
        {
            members.iter().find_map(|(_, symbol)| {
                (classes::authenticated_private_class_symbol_name(
                    store,
                    context.class_symbol,
                    symbol,
                ) == Some(property.name.as_str()))
                .then_some(symbol)
            })
        }
        SourcePropertyPrivacy::Private { .. } => None,
    }
    .ok_or_else(|| unsupported_access(target))?;
    let member_record = store.symbol(member).ok_or_else(invalid)?;
    if !member_record.flags().contains(SymbolFlags::PROPERTY)
        || member_record.parent() != Some(context.class_symbol)
        || store.get_merged_symbol(member) != Some(member)
    {
        return Err(unsupported_access(target));
    }
    let declaration = member_record.value_declaration().ok_or_else(invalid)?;
    let declaration_record = class_access_node(store, host, declaration)?;
    if bound.symbol(declaration) != Some(member) {
        return Err(invalid());
    }
    let origin = match &declaration_record.data {
        NodeData::PropertyDeclaration(field)
            if declaration_record.parent == Some(context.class_declaration.node)
                && class_member_side(store, host, declaration, field.modifiers.as_ref())?
                    == ClassPropertySide::Instance
                && !ts_binder::canonical_has_syntactic_modifier(
                    arena,
                    declaration.node,
                    SyntaxKind::AccessorKeyword,
                ) =>
        {
            ClassMemberOrigin::Field {
                initializer: field
                    .initializer
                    .map(|node| NodeRef::new(declaration.arena, declaration.file, node)),
            }
        }
        NodeData::ParameterDeclaration(_)
            if declaration_record.parent == Some(context.body_declaration.node) =>
        {
            ClassMemberOrigin::ParameterProperty {
                parameter: declaration,
            }
        }
        _ => return Err(unsupported_access(target)),
    };
    let readonly = ts_binder::canonical_has_syntactic_modifier(
        arena,
        declaration.node,
        SyntaxKind::ReadonlyKeyword,
    );
    if readonly && context.phase != ClassAccessPhase::Constructor {
        return Err(unsupported_access(target));
    }
    Ok(SourceClassPropertyWritePlan {
        statement,
        assignment,
        value,
        property,
        context,
        member,
        declaration,
        origin,
        readonly,
    })
}

pub(super) fn validate_class_property_write_access(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceClassPropertyWritePlan,
    access: &classes::ClassBodyAccessToken,
) -> Result<(classes::ClassBodyIdentities, ClassMemberSource), SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(plan.target());
    if plan_class_property_write(store, host, plan.node())? != *plan {
        return Err(invalid());
    }
    let identities = classes::class_body_identities(store, host, access).map_err(|_| invalid())?;
    if identities.class_symbol != plan.context.class_symbol
        || identities.class_declaration != plan.context.class_declaration
        || identities.body_declaration != plan.context.body_declaration
    {
        return Err(invalid());
    }
    let member = classes::class_member_source(store, host, plan.member).map_err(|_| invalid())?;
    if member.declaring_class != identities.class_symbol
        || member.declaration != plan.declaration
        || member.origin != plan.origin
        || member.side != ClassPropertySide::Instance
        || member.readonly != plan.readonly
    {
        return Err(invalid());
    }
    Ok((identities, member))
}

pub(super) fn class_property_write_diagnostics(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    target: &CheckedClassPropertyWriteTarget,
    receiver_type: TypeId,
) -> Result<Vec<SourcePropertyDiagnostic>, SourcePropertyError> {
    let plan = target.plan();
    let (identities, member) =
        validate_class_property_write_access(store, host, plan, target.access_token())?;
    if receiver_type != identities.this_type {
        return Err(SourcePropertyError::InvalidCache(plan.target()));
    }
    let kind =
        class_accessibility_diagnostic(store, host, &plan.context, &member, plan.property.privacy)?;
    Ok(kind
        .into_iter()
        .map(|kind| SourcePropertyDiagnostic {
            name_node: plan.property.name_node,
            receiver_type,
            missing_type: None,
            suggestion: None,
            private_owner: None,
            accessibility: Some(ClassPropertyAccessDiagnostic::Class {
                context: plan.context,
                property: plan.member,
                lookup_type: identities.instance_type,
                kind,
                binding: None,
            }),
        })
        .collect())
}

pub(super) fn check_class_property_write_target(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceClassPropertyWritePlan,
    receiver_type: TypeId,
    access: &classes::ClassBodyAccessToken,
) -> Result<CheckedClassPropertyWriteTarget, SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(plan.target());
    let (identities, member) = validate_class_property_write_access(store, host, plan, access)?;
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    if bootstrap.options != options.intrinsic || receiver_type != identities.this_type {
        return Err(invalid());
    }
    let strict = bootstrap.options.strict_null_checks;
    let exact = bootstrap.options.exact_optional_property_types;
    let sentinel = bootstrap.undefined_or_missing_type;
    let receiver_symbol = store
        .type_payload(receiver_type)
        .and_then(TypeRecord::symbol)
        .ok_or_else(invalid)?;
    if store.type_node_links(plan.receiver())
        != Some(&TypeNodeLinks {
            resolved_type: Some(receiver_type),
            ..TypeNodeLinks::default()
        })
    {
        return Err(invalid());
    }
    validate_property_link_targets(store, plan.receiver(), Some(receiver_symbol), receiver_type)?;
    let property = store.symbol(plan.member).ok_or_else(invalid)?;
    let optional = property.flags().contains(SymbolFlags::OPTIONAL);
    let links = store.value_symbol_links(plan.member).ok_or_else(invalid)?;
    let declared = links.resolved_type.ok_or_else(invalid)?;
    if links
        != &(ValueSymbolLinks {
            resolved_type: Some(declared),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(invalid());
    }
    // Reject stale target links before allocating an optional read union.
    if store.symbol_node_links(plan.target()).is_some_and(|links| {
        links
            .resolved_symbol
            .is_some_and(|symbol| symbol != plan.member)
    }) {
        return Err(invalid());
    }
    if let Some(cached) = store
        .type_node_links(plan.target())
        .and_then(|links| links.resolved_type)
    {
        let expected = if strict && optional && !exact {
            store
                .cached_literal_union_type_with_alias(
                    &[declared, sentinel],
                    None,
                    Some(CanonicalArrayTargets::from_global_types(globals)),
                )
                .map_err(|error| SourcePropertyError::Union {
                    node: plan.target(),
                    error: UnionPropertyError::TypeCache(error),
                })?
        } else {
            Some(declared)
        };
        if expected != Some(cached) {
            return Err(invalid());
        }
    }
    let read_type = if strict && optional {
        property_union_type(
            store,
            Some(globals),
            plan.target(),
            &[declared, sentinel],
            Some(plan.member),
        )?
    } else {
        declared
    };
    let write_type = if strict && optional && !exact {
        read_type
    } else {
        declared
    };
    publish_property_links(store, plan.target(), Some(plan.member), write_type)?;
    Ok(CheckedClassPropertyWriteTarget {
        plan: plan.clone(),
        access: access.clone(),
        member,
        read_type,
        write_type,
    })
}

fn class_access_node<'host>(
    store: &CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<&'host Node, SourcePropertyError> {
    let record =
        preflight_node(store, host, node).map_err(|_| SourcePropertyError::InvalidCache(node))?;
    let parent = record.parent.map_or(SourceNodeParent::Root, |parent| {
        SourceNodeParent::Parent(NodeRef::new(node.arena, node.file, parent))
    });
    if store.source_node_kind(node) != Some(record.kind)
        || store.source_node_parent(node) != Some(parent)
    {
        return Err(SourcePropertyError::InvalidCache(node));
    }
    Ok(record)
}

fn class_member_side(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    member: NodeRef,
    modifiers: Option<&ts_ast::ModifierList>,
) -> Result<ClassPropertySide, SourcePropertyError> {
    let mut side = ClassPropertySide::Instance;
    if let Some(modifiers) = modifiers {
        for &modifier in &modifiers.list.nodes {
            let modifier = NodeRef::new(member.arena, member.file, modifier);
            let record = class_access_node(store, host, modifier)?;
            if record.parent != Some(member.node) {
                return Err(SourcePropertyError::InvalidCache(member));
            }
            if record.kind == SyntaxKind::StaticKeyword {
                side = ClassPropertySide::Static;
            }
        }
    }
    Ok(side)
}

/// Finds the lexical class receiver without accepting caller-provided flags.
#[allow(clippy::too_many_lines)]
pub(super) fn plan_class_access_context(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    receiver: NodeRef,
) -> Result<Option<ClassAccessContext>, SourcePropertyError> {
    let record = class_access_node(store, host, receiver)?;
    let kind = match (&record.data, record.kind) {
        (NodeData::KeywordExpression(keyword), SyntaxKind::ThisKeyword)
            if record.flags.0 == 0 && keyword.flow_node.is_none() =>
        {
            ClassReceiverKind::This
        }
        (NodeData::KeywordExpression(keyword), SyntaxKind::SuperKeyword)
            if record.flags.0 == 0 && keyword.flow_node.is_none() =>
        {
            let parent = record.parent.ok_or_else(|| unsupported_access(receiver))?;
            let parent = NodeRef::new(receiver.arena, receiver.file, parent);
            match &class_access_node(store, host, parent)?.data {
                NodeData::PropertyAccessExpression(access)
                    if access.expression == receiver.node =>
                {
                    ClassReceiverKind::SuperProperty
                }
                NodeData::CallExpression(call) if call.expression == receiver.node => {
                    ClassReceiverKind::SuperCall
                }
                _ => return Err(unsupported_access(receiver)),
            }
        }
        _ => return Ok(None),
    };
    let mut child = receiver;
    let mut deferred = false;
    let mut parameter_initializer = None;
    let mut visited = std::collections::HashSet::new();
    while visited.insert(child) {
        let record = class_access_node(store, host, child)?;
        let Some(parent) = record.parent else {
            return Ok(None);
        };
        let parent = NodeRef::new(receiver.arena, receiver.file, parent);
        let parent_record = class_access_node(store, host, parent)?;
        let (body, parameters, side, phase) = match &parent_record.data {
            NodeData::ParameterDeclaration(parameter) => {
                if parameter.initializer != Some(child.node) {
                    return Err(unsupported_access(receiver));
                }
                parameter_initializer = Some(parent);
                child = parent;
                continue;
            }
            NodeData::ArrowFunction(_) => {
                deferred = true;
                child = parent;
                continue;
            }
            NodeData::FunctionDeclaration(_)
            | NodeData::FunctionExpression(_)
            | NodeData::ClassDeclaration(_)
            | NodeData::ClassExpression(_) => return Ok(None),
            NodeData::ConstructorDeclaration(constructor) => (
                constructor.body,
                Some(&constructor.parameters),
                ClassPropertySide::Instance,
                ClassAccessPhase::Constructor,
            ),
            NodeData::MethodDeclaration(method) => (
                method.body,
                Some(&method.parameters),
                class_member_side(store, host, parent, method.modifiers.as_ref())?,
                ClassAccessPhase::Method,
            ),
            NodeData::GetAccessorDeclaration(accessor) => (
                accessor.body,
                None,
                class_member_side(store, host, parent, accessor.modifiers.as_ref())?,
                ClassAccessPhase::Method,
            ),
            NodeData::SetAccessorDeclaration(accessor) => (
                accessor.body,
                None,
                class_member_side(store, host, parent, accessor.modifiers.as_ref())?,
                ClassAccessPhase::Method,
            ),
            NodeData::PropertyDeclaration(property) => (
                property.initializer,
                None,
                class_member_side(store, host, parent, property.modifiers.as_ref())?,
                ClassAccessPhase::PropertyInitializer,
            ),
            NodeData::ClassStaticBlockDeclaration(block) => (
                Some(block.body),
                None,
                ClassPropertySide::Static,
                ClassAccessPhase::StaticBlock,
            ),
            _ => {
                child = parent;
                continue;
            }
        };
        let in_body = body == Some(child.node);
        let in_parameter = body.is_some()
            && parameter_initializer == Some(child)
            && parameters.is_some_and(|parameters| parameters.nodes.contains(&child.node));
        if !in_body && !in_parameter {
            return Err(unsupported_access(receiver));
        }
        let Some(class) = parent_record.parent else {
            return Err(SourcePropertyError::InvalidCache(receiver));
        };
        let class_declaration = NodeRef::new(receiver.arena, receiver.file, class);
        let class_record = class_access_node(store, host, class_declaration)?;
        let NodeData::ClassDeclaration(class) = &class_record.data else {
            return Ok(None);
        };
        if !class.members.nodes.contains(&parent.node)
            || kind == ClassReceiverKind::SuperCall
                && (phase != ClassAccessPhase::Constructor || deferred || !in_body)
        {
            return Err(unsupported_access(receiver));
        }
        let class_symbol = host
            .bound_file(class_declaration)
            .and_then(|bound| bound.symbol(class_declaration))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .ok_or(SourcePropertyError::InvalidCache(class_declaration))?;
        let owner = store
            .symbol(class_symbol)
            .ok_or(SourcePropertyError::InvalidCache(class_declaration))?;
        if !owner.flags().contains(SymbolFlags::CLASS)
            || owner.value_declaration() != Some(class_declaration)
            || !host.symbol_matches(store, class_declaration, class_symbol)
        {
            return Err(SourcePropertyError::InvalidCache(class_declaration));
        }
        preflight_property_links(store, receiver)?;
        return Ok(Some(ClassAccessContext {
            receiver,
            class_symbol,
            class_declaration,
            body_declaration: parent,
            kind,
            side,
            phase: if deferred {
                ClassAccessPhase::Deferred
            } else {
                phase
            },
        }));
    }
    Err(SourcePropertyError::InvalidCache(receiver))
}

pub(super) fn attach_class_access_context(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &mut SourcePropertyPlan,
) -> Result<(), SourcePropertyError> {
    let context = plan_class_access_context(store, host, plan.receiver.node)?;
    if plan.class_access.is_some() && plan.class_access != context {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    plan.class_access = context;
    Ok(())
}

#[derive(Clone, Copy)]
struct ClassReceiverIdentities {
    instance: TypeId,
    this_type: TypeId,
    value: TypeId,
    base: Option<(TypeId, TypeId)>,
    instance_super: Option<classes::ClassInstanceSuperView>,
}

impl ClassReceiverIdentities {
    fn receiver_type(self, context: &ClassAccessContext) -> Result<TypeId, SourcePropertyError> {
        match context.kind {
            ClassReceiverKind::This => Ok(if context.side == ClassPropertySide::Static {
                self.value
            } else {
                self.this_type
            }),
            ClassReceiverKind::SuperProperty if context.side == ClassPropertySide::Instance => self
                .instance_super
                .map(classes::ClassInstanceSuperView::receiver_type)
                .ok_or_else(|| unsupported_access(context.receiver)),
            ClassReceiverKind::SuperProperty | ClassReceiverKind::SuperCall => self
                .base
                .map(|(_, value)| value)
                .ok_or_else(|| unsupported_access(context.receiver)),
        }
    }

    fn lookup_type(self, context: &ClassAccessContext) -> Result<TypeId, SourcePropertyError> {
        match (context.kind, context.side) {
            (ClassReceiverKind::This, ClassPropertySide::Instance) => Ok(self.instance),
            (ClassReceiverKind::SuperProperty, ClassPropertySide::Instance) => self
                .instance_super
                .map(classes::ClassInstanceSuperView::lookup_type)
                .ok_or_else(|| unsupported_access(context.receiver)),
            _ => self.receiver_type(context),
        }
    }
}

fn class_receiver_identities(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    context: &ClassAccessContext,
    flow: Option<&ClassInitializationFrame<'_, '_>>,
) -> Result<ClassReceiverIdentities, SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(context.receiver);
    if plan_class_access_context(store, host, context.receiver)? != Some(*context) {
        return Err(invalid());
    }
    let mut result = if let Some(flow) = flow {
        let identities = classes::class_body_identities(store, host, flow.access_token())
            .map_err(|_| invalid())?;
        if identities.class_declaration != context.class_declaration
            || identities.class_symbol != context.class_symbol
            || identities.body_declaration != context.body_declaration
        {
            return Err(invalid());
        }
        ClassReceiverIdentities {
            instance: identities.instance_type,
            this_type: identities.this_type,
            value: identities.value_type,
            base: identities
                .base
                .map(|base| (base.instance_type(), base.value_type())),
            instance_super: None,
        }
    } else {
        let instance = store
            .declared_type_links(context.class_symbol)
            .and_then(|links| links.declared_type)
            .ok_or_else(|| unsupported_access(context.receiver))?;
        if classes::validate_class_heritage_members(store, instance)
            != ClassHeritageMembersValidation::Valid
        {
            return Err(unsupported_access(context.receiver));
        }
        let TypeData::Interface(class) = store.type_payload(instance).ok_or_else(invalid)?.data()
        else {
            return Err(invalid());
        };
        let this_type = class.this_type.ok_or_else(invalid)?;
        let value = store
            .value_symbol_links(context.class_symbol)
            .and_then(|links| links.resolved_type)
            .ok_or_else(invalid)?;
        let base = store
            .direct_class_heritage_provenance(instance)
            .map(|base| (base.base_instance_type, base.base_value_type));
        ClassReceiverIdentities {
            instance,
            this_type,
            value,
            base,
            instance_super: None,
        }
    };
    if context.kind == ClassReceiverKind::SuperProperty
        && context.side == ClassPropertySide::Instance
    {
        let base = result
            .base
            .ok_or_else(|| unsupported_access(context.receiver))?
            .0;
        let symbol = store
            .type_payload(base)
            .and_then(TypeRecord::symbol)
            .ok_or_else(invalid)?;
        if store
            .symbol_node_links(context.receiver)
            .is_some_and(|links| links.resolved_symbol.is_some_and(|cached| cached != symbol))
        {
            return Err(invalid());
        }
        let access = flow.map(ClassInitializationFrame::access_token);
        let retained = store.type_node_links(context.receiver);
        let view = if let Some(links) = retained.filter(|links| *links != &TypeNodeLinks::default())
        {
            if links.outer_type_parameters.is_some() {
                return Err(invalid());
            }
            classes::validate_class_instance_super_view(
                store,
                host,
                context.class_symbol,
                access,
                links.resolved_type.ok_or_else(invalid)?,
            )
            .map_err(|_| invalid())?
        } else {
            classes::prepare_class_instance_super_view(store, host, context.class_symbol, access)
                .map_err(|_| invalid())?
        };
        result.instance_super = Some(view);
    }
    Ok(result)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_class_receiver(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    _globals: &CanonicalGlobalTypes,
    _options: CanonicalCheckerOptions,
    context: &ClassAccessContext,
    flow: Option<&mut ClassInitializationFrame<'_, '_>>,
) -> Result<CheckedClassReceiver, SourcePropertyError> {
    let identities = class_receiver_identities(store, host, context, flow.map(|frame| &*frame))?;
    let type_ = identities.receiver_type(context)?;
    let symbol = store
        .type_payload(type_)
        .and_then(TypeRecord::symbol)
        .ok_or(SourcePropertyError::InvalidCache(context.receiver))?;
    publish_property_links(store, context.receiver, Some(symbol), type_)?;
    Ok(CheckedClassReceiver {
        type_,
        diagnostics: Vec::new(),
    })
}

impl SourcePropertyPlan {
    pub(super) fn is_call_callee_for(&self, call: NodeRef, name: NodeRef) -> bool {
        self.name_node == name && self.position == SourcePropertyPosition::CallCallee(call)
    }

    pub(super) fn is_read(&self) -> bool {
        self.position == SourcePropertyPosition::Read
    }

    pub(super) const fn class_access_context(&self) -> Option<&ClassAccessContext> {
        self.class_access.as_ref()
    }
}

/// Unrendered public or private property recovery retained until source
/// checking supplies its diagnostic host and options.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourcePropertyDiagnostic {
    name_node: NodeRef,
    receiver_type: TypeId,
    missing_type: Option<TypeId>,
    suggestion: Option<SemanticSymbolId>,
    private_owner: Option<SemanticSymbolId>,
    accessibility: Option<ClassPropertyAccessDiagnostic>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ClassPropertyAccessDiagnostic {
    Private {
        property: SemanticSymbolId,
        owner: SemanticSymbolId,
    },
    Protected {
        property: SemanticSymbolId,
        owner: SemanticSymbolId,
    },
    ProtectedReceiver {
        property: SemanticSymbolId,
        enclosing_class: TypeId,
    },
    Class {
        context: ClassAccessContext,
        property: SemanticSymbolId,
        lookup_type: TypeId,
        kind: ClassAccessDiagnosticKind,
        binding: Option<NodeRef>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ClassAccessDiagnosticKind {
    AbstractProperty,
    AbstractSuper,
    SuperField,
    Private,
    PrivateIdentifier,
    UsedBeforeInitialization,
    UsedBeforeAssignment(ClassPropertyFlowRead),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CheckedSourceProperty {
    pub(super) type_: TypeId,
    pub(super) diagnostics: Vec<SourcePropertyDiagnostic>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CopiedSourcePropertySuggestion {
    Unavailable,
    None,
    Candidate(SemanticSymbolId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CopiedMissingUnionProperty {
    Unavailable,
    PresentEverywhere,
    Missing(TypeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NamespaceProperty {
    Present {
        symbol: SemanticSymbolId,
        type_: TypeId,
    },
    Missing,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ClassStaticProperty {
    Present(ResolvedOwnProperty),
    Missing,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ClassInstanceProperty {
    Present(ResolvedOwnProperty),
    Missing,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CanonicalArrayProperty {
    Present(ResolvedOwnProperty),
    Missing,
}

/// Proves property syntax and existing access caches before recursive receiver
/// planning can publish semantic state.
pub(super) fn plan_direct_source_property_syntax(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<DirectSourcePropertySyntax, SourcePropertyError> {
    plan_direct_source_property_syntax_at(arena, store, node, SourcePropertyPosition::Read)
}

/// Proves a property access specifically as the callee of `call`.
pub(super) fn plan_direct_source_property_call_syntax(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    call: NodeRef,
) -> Result<DirectSourcePropertySyntax, SourcePropertyError> {
    plan_direct_source_property_syntax_at(
        arena,
        store,
        node,
        SourcePropertyPosition::CallCallee(call),
    )
}

fn plan_direct_source_property_syntax_at(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    position: SourcePropertyPosition,
) -> Result<DirectSourcePropertySyntax, SourcePropertyError> {
    let Some(record) = arena.get(node.node) else {
        return Err(unsupported_access(node));
    };
    let NodeData::PropertyAccessExpression(access) = &record.data else {
        return Err(unsupported_access(node));
    };
    if record.kind != SyntaxKind::PropertyAccessExpression
        || record.flags.0 != 0
        || access.flow_node.is_some()
        || access.facts != 0
    {
        return Err(unsupported_access(node));
    }

    match position {
        SourcePropertyPosition::Read => {
            if let Some(parent) = record.parent
                && let Some(parent_record) = arena.get(parent)
                && match &parent_record.data {
                    NodeData::CallExpression(call) => call.expression == node.node,
                    NodeData::TaggedTemplateExpression(tagged) => tagged.tag == node.node,
                    _ => false,
                }
            {
                return Err(SourcePropertyError::Unsupported(
                    SourcePropertyUnsupported::MemberCall(NodeRef::new(
                        node.arena, node.file, parent,
                    )),
                ));
            }
        }
        SourcePropertyPosition::CallCallee(call_node) => {
            let exact_call = call_node.arena == node.arena
                && call_node.file == node.file
                && record.parent == Some(call_node.node)
                && arena.get(call_node.node).is_some_and(|call_record| {
                    matches!(
                        (&call_record.data, call_record.kind),
                        (NodeData::CallExpression(call), SyntaxKind::CallExpression)
                            if call.expression == node.node
                    ) || matches!(
                        (&call_record.data, call_record.kind),
                        (
                            NodeData::TaggedTemplateExpression(tagged),
                            SyntaxKind::TaggedTemplateExpression,
                        ) if tagged.tag == node.node
                    )
                });
            if !exact_call {
                return Err(SourcePropertyError::Unsupported(
                    SourcePropertyUnsupported::MemberCall(call_node),
                ));
            }
        }
        SourcePropertyPosition::WriteTarget(assignment) => {
            let exact_assignment = assignment.is_for(node.arena, node.file)
                && record.parent == Some(assignment.node)
                && arena.get(assignment.node).is_some_and(|record| {
                    matches!(&record.data, NodeData::BinaryExpression(binary)
                        if binary.left == node.node
                            && arena.get(binary.operator_token)
                                .is_some_and(|operator| operator.kind == SyntaxKind::EqualsToken))
                });
            if !exact_assignment || access.question_dot_token.is_some() {
                return Err(unsupported_access(node));
            }
        }
    }

    let receiver = NodeRef::new(node.arena, node.file, access.expression);
    let Some(receiver_record) = arena.get(access.expression) else {
        return Err(unsupported_access(node));
    };
    if receiver_record.parent != Some(node.node)
        || matches!(
            &receiver_record.data,
            NodeData::Identifier(identifier)
                if receiver_record.flags.0 != 0 || identifier.flow_node.is_some()
        )
    {
        return Err(SourcePropertyError::Unsupported(
            SourcePropertyUnsupported::Receiver(receiver),
        ));
    }

    let name_node = NodeRef::new(node.arena, node.file, access.name);
    let Some(name_record) = arena.get(access.name) else {
        return Err(unsupported_access(node));
    };
    if name_record.parent != Some(node.node) || name_record.flags.0 != 0 {
        return Err(unsupported_access(node));
    }
    let (name, privacy) = match &name_record.data {
        NodeData::Identifier(identifier)
            if name_record.kind == SyntaxKind::Identifier
                && identifier.flow_node.is_none()
                && !identifier.text.is_empty() =>
        {
            (identifier.text.clone(), SourcePropertyPrivacy::Identifier)
        }
        NodeData::PrivateIdentifier(identifier)
            if name_record.kind == SyntaxKind::PrivateIdentifier
                && identifier.text.starts_with('#')
                && identifier.text.len() > 1
                && access.question_dot_token.is_none() =>
        {
            (
                identifier.text.clone(),
                SourcePropertyPrivacy::Private {
                    enclosing_class: enclosing_private_source_class(arena, store, node)?,
                },
            )
        }
        _ => return Err(unsupported_access(node)),
    };

    let optional = if let Some(token_id) = access.question_dot_token {
        let Some(token) = arena.get(token_id) else {
            return Err(unsupported_access(node));
        };
        if token.kind != SyntaxKind::QuestionDotToken
            || token.parent != Some(node.node)
            || token.flags.0 != 0
            || token.range.start < receiver_record.range.end
            || token.range.end > name_record.range.start
            || !matches!(position, SourcePropertyPosition::Read)
        {
            return Err(unsupported_access(node));
        }
        true
    } else {
        receiver_continues_optional_chain(arena, receiver_record)
    };
    if optional && matches!(privacy, SourcePropertyPrivacy::Private { .. }) {
        return Err(unsupported_access(node));
    }

    preflight_property_links(store, node)?;
    Ok(DirectSourcePropertySyntax {
        node,
        receiver,
        name_node,
        name,
        privacy,
        position,
        optional,
    })
}

fn enclosing_private_source_class(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<Option<NodeRef>, SourcePropertyError> {
    let mut current = node;
    loop {
        let record = arena
            .get(current.node)
            .ok_or(SourcePropertyError::InvalidCache(node))?;
        if store.source_node_kind(current) != Some(record.kind) {
            return Err(SourcePropertyError::InvalidCache(node));
        }
        let Some(parent) = record.parent else {
            if store.source_node_parent(current) != Some(super::store::SourceNodeParent::Root) {
                return Err(SourcePropertyError::InvalidCache(node));
            }
            return Ok(None);
        };
        let parent = NodeRef::new(node.arena, node.file, parent);
        if store.source_node_parent(current) != Some(super::store::SourceNodeParent::Parent(parent))
        {
            return Err(SourcePropertyError::InvalidCache(node));
        }
        let record = arena
            .get(parent.node)
            .ok_or(SourcePropertyError::InvalidCache(node))?;
        if store.source_node_kind(parent) != Some(record.kind) {
            return Err(SourcePropertyError::InvalidCache(node));
        }
        match record.kind {
            SyntaxKind::ClassDeclaration => return Ok(Some(parent)),
            SyntaxKind::ClassExpression => return Err(unsupported_access(node)),
            _ => current = parent,
        }
    }
}

pub(super) fn finish_direct_source_property_plan(
    syntax: &DirectSourcePropertySyntax,
    receiver: PlannedExpression,
) -> Result<SourcePropertyPlan, SourcePropertyError> {
    if receiver.node != syntax.receiver {
        return Err(SourcePropertyError::Unsupported(
            SourcePropertyUnsupported::Receiver(syntax.receiver),
        ));
    }
    Ok(SourcePropertyPlan {
        node: syntax.node,
        receiver,
        name_node: syntax.name_node,
        name: syntax.name.clone(),
        privacy: syntax.privacy,
        position: syntax.position,
        optional: syntax.optional,
        class_access: None,
    })
}

/// Resolves an already-typed receiver and atomically publishes the access's
/// exact symbol/type cache pair. Canonical `any` publishes only its type cache.
#[cfg(test)]
pub(super) fn check_direct_source_property(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<CheckedSourceProperty, SourcePropertyError> {
    let mut session = InstantiationSession::new(super::instantiate::InstantiationLimits::default());
    check_direct_source_property_with_session(
        store,
        global_types,
        plan,
        receiver_type,
        &mut session,
    )
}

pub(super) fn check_direct_source_property_with_session(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
    session: &mut InstantiationSession,
) -> Result<CheckedSourceProperty, SourcePropertyError> {
    check_direct_source_property_worker(
        store,
        global_types,
        plan,
        receiver_type,
        session,
        |store, receiver, name, session| {
            resolve_direct_source_own_property(store, global_types, receiver, name, session)
        },
    )
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)] // Uses the caller's source query for unresolved members.
pub(super) fn check_direct_source_property_with_source(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<CheckedSourceProperty, SourcePropertyQueryError> {
    if matches!(plan.position, SourcePropertyPosition::WriteTarget(_)) {
        return check_direct_source_property_with_session(
            store,
            Some(global_types),
            plan,
            receiver_type,
            session,
        )
        .map_err(SourcePropertyQueryError::Property);
    }
    check_direct_source_property_worker(
        store,
        Some(global_types),
        plan,
        receiver_type,
        session,
        |store, receiver, name, session| {
            let property_alias =
                super::object_aliases::property_object_alias_projection(store, receiver)?.is_some();
            let target = store
                .type_payload(receiver)
                .and_then(|record| match record.data() {
                    TypeData::TypeReference(reference) => reference.object.target,
                    TypeData::Interface(interface)
                        if record.object_flags().contains(ObjectFlags::REFERENCE) =>
                    {
                        interface.reference.object.target
                    }
                    TypeData::Interface(_) => Some(receiver),
                    _ => None,
                });
            let cold_interface = target
                .and_then(|target| store.type_payload(target))
                .is_some_and(|record| {
                    matches!(record.data(), TypeData::Interface(interface)
                        if !interface.declared_members_resolved
                            && !record.object_flags().contains(ObjectFlags::CLASS))
                });
            if !property_alias
                && !cold_interface
                && !is_cold_direct_nongeneric_interface(store, receiver)
            {
                return resolve_direct_source_own_property(
                    store,
                    Some(global_types),
                    receiver,
                    name,
                    session,
                )
                .map_err(SourcePropertyQueryError::Property);
            }
            if let Some(owner) = cold_inherited_interface_owner(store, host, receiver, name)
                .map_err(SourcePropertyQueryError::Source)?
            {
                let resolved =
                    super::type_nodes::CanonicalTypeQuery::new_with_global_types_and_session(
                        store,
                        host,
                        global_types,
                        options,
                        session,
                        diagnostics,
                    )
                    .and_then(|mut query| query.get_declared_interface_for_source_check(owner))
                    .map_err(|error| SourcePropertyQueryError::Source(error.into()))?;
                if resolved != receiver {
                    return Err(RelationUnavailable::InvalidStructuredMembers(receiver).into());
                }
                return resolve_direct_source_own_property(
                    store,
                    Some(global_types),
                    receiver,
                    name,
                    session,
                )
                .map_err(SourcePropertyQueryError::Property);
            }
            super::object_members::resolve_object_property_by_key_with_source(
                store,
                host,
                global_types,
                options,
                receiver,
                EscapedNameRef::source(name),
                session,
                diagnostics,
            )
            .map_err(SourcePropertyQueryError::Source)
        },
    )
}

/// Full member resolution is needed only after an exact own-name miss with heritage.
fn cold_inherited_interface_owner(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    receiver: TypeId,
    name: &str,
) -> Result<Option<SemanticSymbolId>, SourceCheckError> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(receiver);
    let record = store.type_payload(receiver).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = record.data() else {
        return Ok(None);
    };
    if interface.declared_members_resolved
        || record
            .object_flags()
            .intersects(ObjectFlags::CLASS | ObjectFlags::MEMBERS_RESOLVED)
        || record.object_flags().contains(ObjectFlags::REFERENCE)
            && super::reference_types::validate_nongeneric_interface_argument_origin(
                store, receiver,
            )
            .is_err()
        || interface
            .reference
            .resolved_type_arguments
            .as_ref()
            .is_some_and(|arguments| !arguments.is_empty())
    {
        return Ok(None);
    }
    let owner = record.symbol().ok_or_else(invalid)?;
    let symbol = store.symbol(owner).ok_or_else(invalid)?;
    let members = symbol
        .members()
        .map(|members| store.symbol_table(members).ok_or_else(invalid))
        .transpose()?;
    if !symbol.declarations().is_some_and(|declarations| {
        declarations.iter().any(|declaration| {
            store.source_node_kind(*declaration) == Some(SyntaxKind::InterfaceDeclaration)
                && store
                    .source_child_with_kind(*declaration, SyntaxKind::HeritageClause)
                    .is_some()
        })
    }) {
        return Ok(None);
    }
    if super::declared::cached_interface_type(store, owner)? != Some(receiver)
        || interface.declared_members.is_some()
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || interface.declared_index_infos.is_some()
        || interface.base_types_resolved
        || interface.resolved_base_types.is_some()
        || interface.resolved_base_constructor_type.is_some()
        || interface.reference.object.structured != StructuredTypeData::default()
    {
        return Err(invalid().into());
    }
    if members.is_some_and(|members| members.get_source(name).is_some()) {
        return Ok(None);
    }
    let planned = super::object_members::plan_interface(store, host, owner).map_err(|error| {
        use super::object_members::PropertyObjectError;
        match error {
            PropertyObjectError::UnsupportedMember { node, kind } => {
                SourceCheckError::DeclaredType(super::DeclaredTypeError::TypeNodeUnavailable(
                    super::type_nodes::TypeNodeUnavailable::UnsupportedSyntax { node, kind },
                ))
            }
            PropertyObjectError::Capacity(_) => {
                SourceCheckError::DeclaredType(super::DeclaredTypeError::TypeNodeUnavailable(
                    super::type_nodes::TypeNodeUnavailable::LiteralTypeCapacity,
                ))
            }
            _ => invalid().into(),
        }
    })?;
    if planned.heritage.is_none() {
        return Err(invalid().into());
    }
    for property in &planned.properties {
        let key = super::object_members::planned_declared_property_key(store, property)
            .ok_or(RelationUnavailable::UnsupportedStructuredType(receiver))?;
        if key == EscapedNameRef::source(name) {
            return Ok(None);
        }
    }
    Ok(Some(owner))
}

pub(super) fn is_cold_direct_nongeneric_interface(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
) -> bool {
    let Some(record) = store.type_payload(receiver) else {
        return false;
    };
    let TypeData::Interface(interface) = record.data() else {
        return false;
    };
    if record
        .object_flags()
        .intersects(ObjectFlags::CLASS | ObjectFlags::MEMBERS_RESOLVED)
        || interface.declared_members_resolved
        || interface
            .reference
            .resolved_type_arguments
            .as_ref()
            .is_some_and(|arguments| !arguments.is_empty())
        || interface.outer_type_parameter_count != 0
        || interface.resolved_base_types.is_some()
        || interface.resolved_base_constructor_type.is_some()
        || store
            .direct_interface_heritage_provenance(receiver)
            .is_some()
    {
        return false;
    }
    let Some(owner) = record.symbol() else {
        return false;
    };
    let Some(symbol) = store.symbol(owner) else {
        return false;
    };
    let Some(declarations) = symbol.declarations() else {
        return false;
    };
    symbol.flags().contains(SymbolFlags::INTERFACE)
        && !symbol.flags().contains(SymbolFlags::CLASS)
        && store.source_computed_member_count(owner) == Some(0)
        && declarations.iter().any(|declaration| {
            store.source_node_kind(*declaration) == Some(SyntaxKind::InterfaceDeclaration)
        })
        && declarations
            .iter()
            .all(|declaration| match store.source_node_kind(*declaration) {
                Some(SyntaxKind::InterfaceDeclaration) => store
                    .source_child_with_kind(*declaration, SyntaxKind::HeritageClause)
                    .is_none(),
                Some(SyntaxKind::VariableDeclaration) => symbol
                    .flags()
                    .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE),
                _ => false,
            })
}

fn resolve_direct_source_own_property(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    receiver: TypeId,
    name: &str,
    session: &mut InstantiationSession,
) -> Result<Option<ResolvedOwnProperty>, SourcePropertyError> {
    if store
        .direct_interface_heritage_provenance(receiver)
        .is_some()
        || store
            .object_literal_getter_origin_for_type(receiver)
            .is_some()
        || store.derived_object_literal_has_getter_origin(receiver)
    {
        super::object_members::resolve_object_property_by_key(
            store,
            global_types,
            receiver,
            EscapedNameRef::source(name),
            session,
        )
    } else {
        store.resolved_own_property(receiver, name)
    }
    .map_err(SourcePropertyError::from)
}

fn check_direct_source_property_worker<E>(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
    session: &mut InstantiationSession,
    mut resolve_own_property: impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        &str,
        &mut InstantiationSession,
    ) -> Result<Option<ResolvedOwnProperty>, E>,
) -> Result<CheckedSourceProperty, E>
where
    E: From<SourcePropertyError> + From<RelationUnavailable>,
{
    if plan.class_access.is_some() {
        return Err(unsupported_access(plan.node).into());
    }
    let (any, error_type, undefined) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(RelationUnavailable::MissingBootstrap)?;
        (
            bootstrap.any_type,
            bootstrap.error_type,
            bootstrap.undefined_type,
        )
    };
    if let SourcePropertyPrivacy::Private { enclosing_class } = plan.privacy {
        return check_private_source_property(
            store,
            plan,
            receiver_type,
            error_type,
            enclosing_class,
        )
        .map_err(E::from);
    }
    let (receiver_type, propagate_undefined) = if plan.optional && receiver_type != any {
        optional_property_receiver(store, global_types, plan, receiver_type)?
    } else {
        (receiver_type, false)
    };
    let union_read = plan.is_read()
        && store
            .type_payload(receiver_type)
            .is_some_and(|record| record.flags().intersects(TypeFlags::UNION));
    let union_constituents = if union_read {
        copied_union_constituents(store, receiver_type)
    } else {
        None
    };
    let missing_union_property = union_constituents
        .map_or(CopiedMissingUnionProperty::Unavailable, |constituents| {
            copied_first_missing_union_constituent(store, plan, constituents)
        });
    let global_union_property = match (missing_union_property, union_constituents, global_types) {
        (CopiedMissingUnionProperty::Missing(_), Some(constituents), Some(global_types)) => {
            resolve_common_global_object_property(
                store,
                global_types,
                constituents,
                &plan.name,
                session,
            )?
        }
        _ => None,
    };
    let union_suggestion = if matches!(
        missing_union_property,
        CopiedMissingUnionProperty::Missing(_)
    ) && global_union_property.is_none()
    {
        if let Some(global_types) = global_types
            && global_object_affects_missing_property(
                store,
                global_types,
                plan.node,
                &plan.name,
                session,
            )?
        {
            return Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::ApparentObjectProperty {
                    node: plan.node,
                    receiver_type,
                },
            )
            .into());
        }
        match union_constituents
            .map(|constituents| {
                copied_common_union_property_candidates(store, plan.node, constituents)
            })
            .transpose()?
            .flatten()
        {
            Some(candidates) => {
                match stable_property_spelling_suggestion(store, &plan.name, &candidates) {
                    Ok(Some(candidate)) => CopiedSourcePropertySuggestion::Candidate(candidate),
                    Ok(None) => CopiedSourcePropertySuggestion::None,
                    Err(()) => {
                        return Err(SourcePropertyError::Unsupported(
                            SourcePropertyUnsupported::AmbiguousPropertySuggestion {
                                node: plan.node,
                                receiver_type,
                            },
                        )
                        .into());
                    }
                }
            }
            None => CopiedSourcePropertySuggestion::Unavailable,
        }
    } else {
        CopiedSourcePropertySuggestion::Unavailable
    };
    let declared_property = match resolve_enum_property(store, plan, receiver_type)? {
        Some(property) => Some(property),
        None => resolve_namespace_property(store, plan, receiver_type)?,
    };
    let (type_, property, diagnostic) = if let Some(declared_property) = declared_property {
        match declared_property {
            NamespaceProperty::Present { symbol, type_ } => (type_, Some(symbol), None),
            NamespaceProperty::Missing if plan.is_read() => (
                error_type,
                None,
                Some(SourcePropertyDiagnostic {
                    name_node: plan.name_node,
                    receiver_type,
                    missing_type: None,
                    suggestion: None,
                    private_owner: None,
                    accessibility: None,
                }),
            ),
            NamespaceProperty::Missing => {
                return Err(SourcePropertyError::Unsupported(
                    SourcePropertyUnsupported::MissingOwnProperty {
                        node: plan.node,
                        receiver_type,
                    },
                )
                .into());
            }
        }
    } else if receiver_type == any || receiver_type == error_type {
        (receiver_type, None, None)
    } else if let Some(property) = global_union_property {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(RelationUnavailable::MissingBootstrap)?;
        let type_ = if property.optional && bootstrap.options.strict_null_checks {
            let sentinel = bootstrap.undefined_or_missing_type;
            property_union_type(
                store,
                global_types,
                plan.node,
                &[property.type_, sentinel],
                Some(property.symbol),
            )?
        } else {
            property.type_
        };
        (type_, Some(property.symbol), None)
    } else if union_read {
        if let Some(property) = store
            .resolved_union_property(receiver_type, &plan.name)
            .map_err(|error| SourcePropertyError::Union {
                node: plan.node,
                error,
            })?
        {
            (property.type_id(), Some(property.symbol()), None)
        } else {
            let CopiedMissingUnionProperty::Missing(missing_type) = missing_union_property else {
                return Err(SourcePropertyError::InvalidCache(plan.node).into());
            };
            let suggestion = match union_suggestion {
                CopiedSourcePropertySuggestion::Candidate(candidate) => Some(candidate),
                CopiedSourcePropertySuggestion::None => None,
                CopiedSourcePropertySuggestion::Unavailable => {
                    return Err(SourcePropertyError::InvalidCache(plan.node).into());
                }
            };
            (
                error_type,
                None,
                Some(SourcePropertyDiagnostic {
                    name_node: plan.name_node,
                    receiver_type,
                    missing_type: Some(missing_type),
                    suggestion,
                    private_owner: None,
                    accessibility: None,
                }),
            )
        }
    } else if let Some(property) =
        resolve_published_source_callable_expando_property(store, plan, receiver_type)?
    {
        (property.type_, Some(property.symbol), None)
    } else if let Some(property) = match resolve_class_static_property(store, plan, receiver_type)?
    {
        Some(ClassStaticProperty::Present(property)) => Some(property),
        Some(ClassStaticProperty::Missing) => None,
        None => match resolve_class_instance_member(store, plan, receiver_type)? {
            Some(ClassInstanceProperty::Present(member)) => Some(member),
            Some(ClassInstanceProperty::Missing) => None,
            None => match resolve_published_scalar_wrapper_method(
                store,
                global_types,
                plan,
                receiver_type,
            )? {
                Some(method) => Some(method),
                None => match resolve_published_global_math_random_method(
                    store,
                    global_types,
                    plan,
                    receiver_type,
                )? {
                    Some(method) => Some(method),
                    None => match resolve_published_global_object_constructor_method(
                        store,
                        global_types,
                        plan,
                        receiver_type,
                    )? {
                        Some(method) => Some(method),
                        None => match resolve_published_canonical_array_property(
                            store,
                            global_types,
                            plan,
                            receiver_type,
                            session,
                        )? {
                            Some(CanonicalArrayProperty::Present(property)) => Some(property),
                            Some(CanonicalArrayProperty::Missing) => None,
                            None => {
                                resolve_own_property(store, receiver_type, &plan.name, session)?
                            }
                        },
                    },
                },
            },
        },
    } {
        let diagnostic =
            class_property_accessibility(store, plan.name_node, receiver_type, property.symbol)?
                .map(|accessibility| SourcePropertyDiagnostic {
                    name_node: plan.name_node,
                    receiver_type,
                    missing_type: None,
                    suggestion: None,
                    private_owner: None,
                    accessibility: Some(accessibility),
                });
        if property.optional {
            if !plan.is_read() {
                return Err(SourcePropertyError::Unsupported(
                    SourcePropertyUnsupported::OptionalProperty {
                        node: plan.node,
                        property: property.symbol,
                    },
                )
                .into());
            }
            let bootstrap = store
                .intrinsic_bootstrap()
                .ok_or(RelationUnavailable::MissingBootstrap)?;
            if bootstrap.options.strict_null_checks {
                let sentinel = bootstrap.undefined_or_missing_type;
                let type_ = property_union_type(
                    store,
                    global_types,
                    plan.node,
                    &[property.type_, sentinel],
                    Some(property.symbol),
                )?;
                (type_, Some(property.symbol), diagnostic)
            } else {
                (property.type_, Some(property.symbol), diagnostic)
            }
        } else {
            (property.type_, Some(property.symbol), diagnostic)
        }
    } else {
        if !plan.is_read() {
            return Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::MissingOwnProperty {
                    node: plan.node,
                    receiver_type,
                },
            )
            .into());
        }
        (
            error_type,
            None,
            Some(SourcePropertyDiagnostic {
                name_node: plan.name_node,
                receiver_type,
                missing_type: None,
                suggestion: direct_property_spelling_suggestion(store, plan, receiver_type)?,
                private_owner: None,
                accessibility: None,
            }),
        )
    };

    let type_ = if propagate_undefined && type_ != any && type_ != error_type {
        property_union_type(
            store,
            global_types,
            plan.node,
            &[type_, undefined],
            property,
        )?
    } else {
        type_
    };

    publish_property_links(store, plan.node, property, type_)?;
    Ok(CheckedSourceProperty {
        type_,
        diagnostics: diagnostic.into_iter().collect(),
    })
}

fn class_context_member(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourcePropertyPlan,
    lookup_type: TypeId,
    context: &ClassAccessContext,
    identities: ClassReceiverIdentities,
) -> Result<Option<(ResolvedOwnProperty, ClassMemberSource)>, SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(plan.node);
    let structured = store
        .type_payload(lookup_type)
        .and_then(|record| record.data().structured())
        .ok_or_else(invalid)?;
    let Some(members) = structured.members else {
        return Ok(None);
    };
    let members = store.symbol_table(members).ok_or_else(invalid)?;
    let symbol = match plan.privacy {
        SourcePropertyPrivacy::Identifier => members.get_source(&plan.name),
        SourcePropertyPrivacy::Private { enclosing_class } => {
            let mut lexical = None;
            let mut candidates = Vec::new();
            for (name, symbol) in members.iter() {
                if !name.is_private_identifier() {
                    continue;
                }
                let owner = store
                    .symbol(symbol)
                    .and_then(ts_binder::semantic::Symbol::parent)
                    .ok_or_else(invalid)?;
                if classes::authenticated_private_class_symbol_name(store, owner, symbol)
                    != Some(plan.name.as_str())
                {
                    continue;
                }
                candidates.push(symbol);
                if store
                    .symbol(owner)
                    .and_then(ts_binder::semantic::Symbol::value_declaration)
                    == enclosing_class
                {
                    lexical = Some(symbol);
                    break;
                }
            }
            if lexical.is_some() {
                lexical
            } else {
                let container = store
                    .type_payload(lookup_type)
                    .and_then(TypeRecord::symbol)
                    .ok_or_else(invalid)?;
                let mut selected = None;
                for candidate in candidates {
                    let select = match selected {
                        Some(previous) => {
                            compare_private_fallback_members(
                                store, host, plan.node, container, candidate, previous,
                            )? == Ordering::Less
                        }
                        None => true,
                    };
                    if select {
                        selected = Some(candidate);
                    }
                }
                selected
            }
        }
    };
    let Some(symbol) = symbol else {
        return Ok(None);
    };
    class_context_member_for_symbol(
        store,
        host,
        plan.node,
        lookup_type,
        context,
        identities,
        symbol,
    )
    .map(Some)
}

#[allow(clippy::too_many_arguments)]
fn class_context_member_for_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    lookup_type: TypeId,
    context: &ClassAccessContext,
    identities: ClassReceiverIdentities,
    symbol: SemanticSymbolId,
) -> Result<(ResolvedOwnProperty, ClassMemberSource), SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(node);
    let structured = store
        .type_payload(lookup_type)
        .and_then(|record| record.data().structured())
        .ok_or_else(invalid)?;
    let source = classes::class_member_source(store, host, symbol).map_err(|_| invalid())?;
    let property = store.symbol(symbol).ok_or_else(invalid)?;
    if store
        .value_symbol_links(symbol)
        .is_none_or(|links| links.resolved_type.is_none())
        && let Some(demand) = classes::pending_source_class_property_type(store, host, &source)
            .map_err(|_| invalid())?
    {
        return Err(SourcePropertyError::PendingClassProperty(demand));
    }
    let links = store.value_symbol_links(symbol).ok_or_else(invalid)?;
    let type_ = links
        .resolved_type
        .filter(|type_| store.type_payload(*type_).is_some())
        .ok_or_else(invalid)?;
    if source.symbol != symbol
        || !class_context_has_member_owner(store, context, identities, source.declaring_class)
        || property.parent() != Some(source.declaring_class)
        || property.value_declaration() != Some(source.declaration)
        || store.get_merged_symbol(symbol) != Some(symbol)
        || structured
            .properties
            .as_deref()
            .is_none_or(|properties| !properties.contains(&symbol))
        || links
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(invalid());
    }
    Ok((
        ResolvedOwnProperty {
            symbol,
            type_,
            optional: property.flags().contains(SymbolFlags::OPTIONAL),
            readonly: source.readonly,
        },
        source,
    ))
}

/// Mirrors getNamedMembers: own declarations first, then pinned symbol order.
fn compare_private_fallback_members(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    access: NodeRef,
    container: SemanticSymbolId,
    left: SemanticSymbolId,
    right: SemanticSymbolId,
) -> Result<Ordering, SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(access);
    let left_record = store.symbol(left).ok_or_else(invalid)?;
    let right_record = store.symbol(right).ok_or_else(invalid)?;
    let container = store.symbol(container).ok_or_else(invalid)?;
    let declarations = container.declarations().ok_or_else(invalid)?;
    let is_contained = |symbol: SemanticSymbolId| -> Result<bool, SourcePropertyError> {
        let declaration = store
            .symbol(symbol)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .ok_or_else(invalid)?;
        let range = class_access_node(store, host, declaration)?.range;
        for declaration in declarations {
            let owner_range = class_access_node(store, host, *declaration)?.range;
            if owner_range.start <= range.start && range.end <= owner_range.end {
                return Ok(true);
            }
        }
        Ok(false)
    };
    let containment_order = is_contained(right)?.cmp(&is_contained(left)?);
    if containment_order != Ordering::Equal {
        return Ok(containment_order);
    }
    let first_declaration = |symbol: SemanticSymbolId| {
        store
            .symbol(symbol)
            .and_then(|record| record.declarations())
            .and_then(|declarations| declarations.first())
            .copied()
    };
    let declaration_order = match (first_declaration(left), first_declaration(right)) {
        (Some(left), Some(right)) => {
            // This provider does not receive the Program's cross-file ordering.
            if left.file != right.file {
                return Err(unsupported_access(access));
            }
            class_access_node(store, host, left)?
                .range
                .start
                .cmp(&class_access_node(store, host, right)?.range.start)
        }
        (Some(_), None) => Ordering::Less,
        (None, Some(_)) => Ordering::Greater,
        (None, None) => Ordering::Equal,
    };
    Ok(declaration_order
        .then_with(|| {
            left_record
                .name()
                .as_bytes()
                .cmp(right_record.name().as_bytes())
        })
        .then_with(|| left.cmp(&right)))
}

fn class_context_has_member_owner(
    store: &CanonicalTypeMapperStore,
    context: &ClassAccessContext,
    identities: ClassReceiverIdentities,
    owner: SemanticSymbolId,
) -> bool {
    if context.kind == ClassReceiverKind::This && owner == context.class_symbol {
        return true;
    }
    let mut base = identities.base.map(|(instance, _)| instance);
    let mut derived = identities.instance;
    let mut visited = std::collections::HashSet::new();
    while let Some(instance) = base {
        if !visited.insert(instance) {
            return false;
        }
        if let Some(matches) =
            classes::source_constructor_base_member_owner(store, derived, context.side, owner)
        {
            return matches;
        }
        if store.type_payload(instance).and_then(TypeRecord::symbol) == Some(owner) {
            return true;
        }
        derived = instance;
        base = store
            .direct_class_heritage_provenance(instance)
            .map(|base| base.base_instance_type);
    }
    false
}

fn class_access_diagnostic(
    plan: &SourcePropertyPlan,
    context: ClassAccessContext,
    receiver_type: TypeId,
    lookup_type: TypeId,
    property: SemanticSymbolId,
    kind: ClassAccessDiagnosticKind,
) -> SourcePropertyDiagnostic {
    SourcePropertyDiagnostic {
        name_node: plan.name_node,
        receiver_type,
        missing_type: None,
        suggestion: None,
        private_owner: None,
        accessibility: Some(ClassPropertyAccessDiagnostic::Class {
            context,
            property,
            lookup_type,
            kind,
            binding: None,
        }),
    }
}

fn class_accessibility_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    context: &ClassAccessContext,
    member: &ClassMemberSource,
    privacy: SourcePropertyPrivacy,
) -> Result<Option<ClassAccessDiagnosticKind>, SourcePropertyError> {
    if let SourcePropertyPrivacy::Private { enclosing_class } = privacy {
        let declaration = store
            .symbol(member.declaring_class)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .ok_or(SourcePropertyError::InvalidCache(member.declaration))?;
        return Ok((enclosing_class != Some(declaration))
            .then_some(ClassAccessDiagnosticKind::PrivateIdentifier));
    }
    if context.kind == ClassReceiverKind::SuperProperty {
        if member.abstract_ {
            return Ok(Some(ClassAccessDiagnosticKind::AbstractSuper));
        }
        if member.side == ClassPropertySide::Instance
            && matches!(
                member.origin,
                ClassMemberOrigin::Field { .. } | ClassMemberOrigin::JavaScriptAssignment { .. }
            )
        {
            return Ok(Some(ClassAccessDiagnosticKind::SuperField));
        }
    }
    if context.kind == ClassReceiverKind::This
        && member.abstract_
        && !matches!(member.origin, ClassMemberOrigin::Method)
        && matches!(
            context.phase,
            ClassAccessPhase::Constructor | ClassAccessPhase::PropertyInitializer
        )
    {
        return Ok(Some(ClassAccessDiagnosticKind::AbstractProperty));
    }
    if member.visibility == ClassConstructorVisibility::Private {
        let declaration = store
            .symbol(member.declaring_class)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .ok_or(SourcePropertyError::InvalidCache(member.declaration))?;
        let mut current = context.receiver;
        while let Some(parent) = class_access_node(store, host, current)?.parent {
            current = NodeRef::new(current.arena, current.file, parent);
            if current == declaration {
                return Ok(None);
            }
        }
        return Ok(Some(ClassAccessDiagnosticKind::Private));
    }
    // A direct this receiver has the enclosing class's constraint. Super already
    // selects the base table, so protected members need no receiver restriction.
    Ok(None)
}

#[allow(clippy::too_many_lines)] // Keep the declaration-order exceptions together.
fn class_property_used_before_initialization(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    context: &ClassAccessContext,
    name_node: NodeRef,
    member: &ClassMemberSource,
) -> Result<bool, SourcePropertyError> {
    if host
        .bound_file(context.receiver)
        .and_then(|bound| bound.source_facts())
        .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file)
    {
        return Ok(false);
    }
    if context.phase == ClassAccessPhase::PropertyInitializer
        && member.declaring_class == context.class_symbol
        && matches!(member.origin, ClassMemberOrigin::ParameterProperty { .. })
    {
        // Parameter-property ordering depends on the unavailable field emit option.
        return Err(unsupported_access(name_node));
    }
    if !matches!(
        context.phase,
        ClassAccessPhase::PropertyInitializer | ClassAccessPhase::StaticBlock
    ) || member.declaring_class != context.class_symbol
        || !matches!(
            member.origin,
            ClassMemberOrigin::Field { .. } | ClassMemberOrigin::AutoAccessor { .. }
        )
    {
        return Ok(false);
    }
    let declaration = class_access_node(store, host, member.declaration)?;
    let NodeData::PropertyDeclaration(property) = &declaration.data else {
        return Err(SourcePropertyError::InvalidCache(member.declaration));
    };
    if matches!(member.origin, ClassMemberOrigin::Field { .. })
        && property.postfix_token.is_some_and(|token| {
            host.node(NodeRef::new(
                member.declaration.arena,
                member.declaration.file,
                token,
            ))
            .is_some_and(|token| token.kind == SyntaxKind::QuestionToken)
        })
    {
        return Ok(false);
    }
    let definite = property.postfix_token.is_some_and(|token| {
        host.node(NodeRef::new(
            member.declaration.arena,
            member.declaration.file,
            token,
        ))
        .is_some_and(|token| token.kind == SyntaxKind::ExclamationToken)
    });
    let uninitialized_property = context.phase == ClassAccessPhase::PropertyInitializer
        && context.kind == ClassReceiverKind::This
        && property.initializer.is_none()
        && !definite;
    let usage_start = class_access_node(store, host, name_node)?.range.start;
    let used_before = uninitialized_property
        || member.declaration == context.body_declaration
        || declaration.range.start > usage_start;
    if !used_before {
        return Ok(false);
    }
    if context.phase == ClassAccessPhase::PropertyInitializer
        && context.side == ClassPropertySide::Static
    {
        let NodeData::ClassDeclaration(class) =
            &class_access_node(store, host, context.class_declaration)?.data
        else {
            return Err(SourcePropertyError::InvalidCache(context.class_declaration));
        };
        if class.members.nodes.iter().any(|member| {
            host.node(NodeRef::new(
                context.class_declaration.arena,
                context.class_declaration.file,
                *member,
            ))
            .is_some_and(|member| {
                member.kind == SyntaxKind::ClassStaticBlockDeclaration
                    && member.range.start < usage_start
            })
        }) {
            return Err(unsupported_access(name_node));
        }
    }
    let instance = store
        .declared_type_links(context.class_symbol)
        .and_then(|links| links.declared_type)
        .ok_or(SourcePropertyError::InvalidCache(context.receiver))?;
    if let Some(base) = store.direct_class_heritage_provenance(instance) {
        let name = store
            .symbol(member.symbol)
            .map(|symbol| symbol.name())
            .ok_or(SourcePropertyError::InvalidCache(member.declaration))?;
        let base_type = if member.side == ClassPropertySide::Static {
            base.base_value_type
        } else {
            base.base_instance_type
        };
        if store
            .type_payload(base_type)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(name))
            .is_some()
        {
            // The checker options do not yet retain useDefineForClassFields.
            return Err(unsupported_access(name_node));
        }
    }
    Ok(true)
}

fn class_property_needs_initialization_flow(
    context: &ClassAccessContext,
    member: &ClassMemberSource,
    options: CanonicalCheckerOptions,
) -> bool {
    options.intrinsic.strict_null_checks
        && match member.origin {
            ClassMemberOrigin::Field { initializer: None }
            | ClassMemberOrigin::AutoAccessor { initializer: None } => {
                options.strict_property_initialization
                    && !member.abstract_
                    && context.kind == ClassReceiverKind::This
                    && context.phase == ClassAccessPhase::Constructor
                    && member.side == ClassPropertySide::Instance
                    && member.declaring_class == context.class_symbol
            }
            ClassMemberOrigin::JavaScriptAssignment { .. } => true,
            _ => false,
        }
}

/// Checks the authenticated class view before publishing the selected member.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(super) fn check_direct_source_property_with_class_context(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: Option<&CanonicalGlobalTypes>,
    options: CanonicalCheckerOptions,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
    flow: Option<&mut ClassInitializationFrame<'_, '_>>,
) -> Result<CheckedSourceProperty, SourcePropertyError> {
    let mut session = InstantiationSession::new(super::instantiate::InstantiationLimits::default());
    check_direct_source_property_with_class_context_and_session(
        store,
        host,
        globals,
        options,
        plan,
        receiver_type,
        &mut session,
        flow,
    )
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
pub(super) fn check_direct_source_property_with_class_context_and_session(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: Option<&CanonicalGlobalTypes>,
    options: CanonicalCheckerOptions,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
    session: &mut InstantiationSession,
    flow: Option<&mut ClassInitializationFrame<'_, '_>>,
) -> Result<CheckedSourceProperty, SourcePropertyError> {
    if plan_class_access_context(store, host, plan.receiver.node)? != plan.class_access {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let Some(context) = plan.class_access else {
        if let Some(flow) = flow.as_deref()
            && let Some(checked) = check_prepared_class_instance_property(
                store,
                host,
                globals,
                plan,
                receiver_type,
                flow,
            )?
        {
            return Ok(checked);
        }
        return check_direct_source_property_with_session(
            store,
            globals,
            plan,
            receiver_type,
            session,
        );
    };
    let (arena, _) = host
        .source(plan.node)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let syntax = plan_direct_source_property_syntax_at(arena, store, plan.node, plan.position)?;
    if syntax.receiver != plan.receiver.node
        || syntax.name_node != plan.name_node
        || syntax.name != plan.name
        || syntax.privacy != plan.privacy
        || syntax.optional != plan.optional
        || context.kind == ClassReceiverKind::SuperCall
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    // The receiver query owns cold preparation. A read must use its existing reference.
    if context.kind == ClassReceiverKind::SuperProperty
        && context.side == ClassPropertySide::Instance
    {
        classes::validate_class_instance_super_view(
            store,
            host,
            context.class_symbol,
            flow.as_deref().map(ClassInitializationFrame::access_token),
            receiver_type,
        )
        .map_err(|_| SourcePropertyError::InvalidCache(plan.receiver.node))?;
    }
    let identities = class_receiver_identities(store, host, &context, flow.as_deref())?;
    if identities.receiver_type(&context)? != receiver_type {
        return Err(SourcePropertyError::InvalidCache(plan.receiver.node));
    }
    let receiver_symbol = store
        .type_payload(receiver_type)
        .and_then(TypeRecord::symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.receiver.node))?;
    validate_property_link_targets(
        store,
        plan.receiver.node,
        Some(receiver_symbol),
        receiver_type,
    )?;
    let lookup_type = identities.lookup_type(&context)?;
    let Some((property, member)) =
        class_context_member(store, host, plan, lookup_type, &context, identities)?
    else {
        if !plan.is_read() || matches!(plan.privacy, SourcePropertyPrivacy::Private { .. }) {
            return Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::MissingOwnProperty {
                    node: plan.node,
                    receiver_type,
                },
            ));
        }
        let error_type = store
            .intrinsic_bootstrap()
            .ok_or(RelationUnavailable::MissingBootstrap)?
            .error_type;
        let diagnostic = SourcePropertyDiagnostic {
            name_node: plan.name_node,
            receiver_type: lookup_type,
            missing_type: None,
            suggestion: direct_property_spelling_suggestion(store, plan, lookup_type)?,
            private_owner: None,
            accessibility: None,
        };
        publish_property_links(store, plan.node, None, error_type)?;
        return Ok(CheckedSourceProperty {
            type_: error_type,
            diagnostics: vec![diagnostic],
        });
    };
    if member.side != context.side {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let accessibility =
        class_accessibility_diagnostic(store, host, &context, &member, plan.privacy)?;
    let mut diagnostics = Vec::new();
    let mut push = |kind| {
        diagnostics.push(class_access_diagnostic(
            plan,
            context,
            receiver_type,
            lookup_type,
            property.symbol,
            kind,
        ));
    };
    if class_property_used_before_initialization(store, host, &context, plan.name_node, &member)? {
        push(ClassAccessDiagnosticKind::UsedBeforeInitialization);
    }
    if let Some(accessibility) = accessibility {
        push(accessibility);
    }
    let private_error = accessibility == Some(ClassAccessDiagnosticKind::PrivateIdentifier);
    let expected_symbol = SymbolNodeLinks {
        resolved_symbol: (!private_error).then_some(property.symbol),
    };
    if store
        .symbol_node_links(plan.node)
        .is_some_and(|links| links != &SymbolNodeLinks::default() && links != &expected_symbol)
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let mut declared_type = property.type_;
    if !private_error && let Some(view) = identities.instance_super {
        if store
            .type_node_links(plan.node)
            .is_some_and(|links| links != &TypeNodeLinks::default())
            && view.requires_member_instantiation()
            && store
                .class_instance_super_member(view.receiver_type(), property.symbol)
                .is_none()
        {
            return Err(SourcePropertyError::InvalidCache(plan.node));
        }
        declared_type = classes::prepare_class_instance_super_member_type(
            store,
            host,
            globals,
            view,
            property.symbol,
        )
        .map_err(|error| match error {
            classes::ClassError::Unsupported(_) => unsupported_access(plan.node),
            _ => SourcePropertyError::InvalidCache(plan.node),
        })?;
    }
    if property.optional && !private_error {
        if !plan.is_read() {
            return Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::OptionalProperty {
                    node: plan.node,
                    property: property.symbol,
                },
            ));
        }
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(RelationUnavailable::MissingBootstrap)?;
        if bootstrap.options.strict_null_checks {
            let undefined = bootstrap.undefined_or_missing_type;
            declared_type = property_union_type(
                store,
                globals,
                plan.node,
                &[declared_type, undefined],
                Some(property.symbol),
            )?;
        }
    }
    let mut type_ = declared_type;
    if !private_error && !matches!(member.origin, ClassMemberOrigin::Method) {
        if let Some(flow) = flow.filter(|_| !context.is_deferred()) {
            let read = flow.property_read(
                store,
                host,
                &context,
                plan.node,
                &member,
                declared_type,
                options,
            )?;
            validate_class_property_flow_read(store, host, plan.node, &read)?;
            if read.used_before_assignment() {
                push(ClassAccessDiagnosticKind::UsedBeforeAssignment(read));
            } else {
                type_ = read.type_();
            }
        } else if class_property_needs_initialization_flow(&context, &member, options) {
            return Err(unsupported_access(plan.node));
        }
    }
    let symbol = if private_error {
        type_ = store
            .intrinsic_bootstrap()
            .ok_or(RelationUnavailable::MissingBootstrap)?
            .error_type;
        None
    } else {
        Some(property.symbol)
    };
    publish_property_links(store, plan.node, symbol, type_)?;
    Ok(CheckedSourceProperty { type_, diagnostics })
}

fn check_prepared_class_instance_property(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: Option<&CanonicalGlobalTypes>,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
    flow: &ClassInitializationFrame<'_, '_>,
) -> Result<Option<CheckedSourceProperty>, SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(plan.node);
    let identities =
        classes::class_body_identities(store, host, flow.access_token()).map_err(|_| invalid())?;
    if receiver_type != identities.instance_type {
        return Ok(None);
    }
    let (arena, _) = host.source(plan.node).ok_or_else(invalid)?;
    let syntax = plan_direct_source_property_syntax_at(arena, store, plan.node, plan.position)?;
    if syntax.receiver != plan.receiver.node
        || syntax.name_node != plan.name_node
        || syntax.name != plan.name
        || syntax.privacy != plan.privacy
        || syntax.optional != plan.optional
    {
        return Err(invalid());
    }
    if plan.privacy != SourcePropertyPrivacy::Identifier || plan.optional {
        return Ok(None);
    }
    let structured = store
        .type_payload(receiver_type)
        .and_then(|record| record.data().structured())
        .ok_or_else(invalid)?;
    let Some(symbol) = structured
        .members
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source(&plan.name))
    else {
        return Ok(None);
    };
    if structured
        .properties
        .as_deref()
        .is_none_or(|properties| !properties.contains(&symbol))
    {
        return Err(invalid());
    }
    let member = classes::class_member_source(store, host, symbol).map_err(|_| invalid())?;
    if member.side != ClassPropertySide::Instance
        || member.visibility != ClassConstructorVisibility::Public
    {
        return Ok(None);
    }
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    if store
        .value_symbol_links(symbol)
        .is_none_or(|links| links.resolved_type.is_none())
        && let Some(demand) = classes::pending_source_class_property_type(store, host, &member)
            .map_err(|_| invalid())?
    {
        return Err(SourcePropertyError::PendingClassProperty(demand));
    }
    let links = store.value_symbol_links(symbol).ok_or_else(invalid)?;
    let mut type_ = links
        .resolved_type
        .filter(|type_| store.type_payload(*type_).is_some())
        .ok_or_else(invalid)?;
    if record.parent() != Some(member.declaring_class)
        || record.value_declaration() != Some(member.declaration)
        || links
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(invalid());
    }
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    if record.flags().contains(SymbolFlags::OPTIONAL) && bootstrap.options.strict_null_checks {
        let undefined = bootstrap.undefined_or_missing_type;
        type_ = property_union_type(store, globals, plan.node, &[type_, undefined], Some(symbol))?;
    }
    publish_property_links(store, plan.node, Some(symbol), type_)?;
    Ok(Some(CheckedSourceProperty {
        type_,
        diagnostics: Vec::new(),
    }))
}

fn validate_class_property_flow_read(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    access: NodeRef,
    read: &ClassPropertyFlowRead,
) -> Result<(), SourcePropertyError> {
    validate_class_property_flow_identity(host, access, read.access(), read.flow())?;
    if store.type_payload(read.type_()).is_none() {
        return Err(SourcePropertyError::InvalidCache(access));
    }
    Ok(())
}

fn validate_class_property_flow_identity(
    host: &DeclaredTypeHost<'_>,
    access: NodeRef,
    observed_access: NodeRef,
    observed_flow: FlowRef,
) -> Result<(), SourcePropertyError> {
    if observed_access != access
        || host
            .bound_file(access)
            .and_then(|bound| bound.flow_at(access))
            != Some(observed_flow)
    {
        return Err(SourcePropertyError::InvalidCache(access));
    }
    Ok(())
}

fn class_property_accessibility(
    store: &CanonicalTypeMapperStore,
    name_node: NodeRef,
    receiver_type: TypeId,
    property: SemanticSymbolId,
) -> Result<Option<ClassPropertyAccessDiagnostic>, SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(name_node);
    let property_record = store.symbol(property).ok_or_else(invalid)?;
    let Some(owner) = property_record.parent() else {
        return Ok(None);
    };
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    if !owner_record.flags().contains(SymbolFlags::CLASS) {
        return Ok(None);
    }
    let Some(declaration) = property_record.value_declaration() else {
        return Ok(None);
    };
    let visibility = classes::class_member_visibility(store, declaration);
    if visibility == ClassConstructorVisibility::Public {
        return Ok(None);
    }
    let declaring_class = store
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .ok_or_else(invalid)?;
    let declaring_declaration = owner_record.value_declaration().ok_or_else(invalid)?;
    let receiver = store.type_payload(receiver_type).ok_or_else(invalid)?;
    let receiver_owner = receiver.symbol().ok_or_else(invalid)?;
    let receiver_class = store
        .declared_type_links(receiver_owner)
        .and_then(|links| links.declared_type)
        .ok_or_else(invalid)?;
    let static_side = store
        .value_symbol_links(receiver_owner)
        .and_then(|links| links.resolved_type)
        == Some(receiver_type);
    if store.source_node_kind(name_node) != Some(SyntaxKind::Identifier)
        || !static_side && receiver_type != receiver_class
        || classes::validated_class_derives_from(store, receiver_class, declaring_class)
            != Some(true)
        || receiver
            .data()
            .structured()
            .and_then(|structured| structured.properties.as_deref())
            .is_none_or(|properties| !properties.contains(&property))
        || receiver
            .data()
            .structured()
            .and_then(|structured| structured.members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(property_record.name()))
            != Some(property)
    {
        return Err(invalid());
    }

    let mut current = name_node;
    loop {
        match store.source_node_parent(current).ok_or_else(invalid)? {
            SourceNodeParent::Root => break,
            SourceNodeParent::Parent(parent) => current = parent,
        }
        if !matches!(
            store.source_node_kind(current),
            Some(SyntaxKind::ClassDeclaration | SyntaxKind::ClassExpression)
        ) {
            continue;
        }
        if visibility == ClassConstructorVisibility::Private {
            if current == declaring_declaration {
                return Ok(None);
            }
            continue;
        }
        let enclosing_class = store
            .types()
            .find_map(|(type_, record)| {
                let owner = record.symbol()?;
                (record.object_flags().contains(ObjectFlags::CLASS)
                    && matches!(record.data(), TypeData::Interface(_))
                    && store.symbol(owner)?.value_declaration() == Some(current)
                    && store.declared_type_links(owner)?.declared_type == Some(type_))
                .then_some(type_)
            })
            .ok_or_else(|| unsupported_access(name_node))?;
        if !classes::validated_class_derives_from(store, enclosing_class, declaring_class)
            .ok_or_else(invalid)?
        {
            continue;
        }
        if static_side
            || classes::validated_class_derives_from(store, receiver_class, enclosing_class)
                .ok_or_else(invalid)?
        {
            return Ok(None);
        }
        return Ok(Some(ClassPropertyAccessDiagnostic::ProtectedReceiver {
            property,
            enclosing_class,
        }));
    }
    Ok(Some(match visibility {
        ClassConstructorVisibility::Private => {
            ClassPropertyAccessDiagnostic::Private { property, owner }
        }
        ClassConstructorVisibility::Protected => {
            ClassPropertyAccessDiagnostic::Protected { property, owner }
        }
        ClassConstructorVisibility::Public => unreachable!("public members returned earlier"),
    }))
}

fn check_private_source_property(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
    error_type: TypeId,
    enclosing_class: Option<NodeRef>,
) -> Result<CheckedSourceProperty, SourcePropertyError> {
    let receiver = store
        .type_payload(receiver_type)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let owner = receiver
        .symbol()
        .and_then(|owner| store.get_merged_symbol(owner))
        .ok_or(SourcePropertyError::Unsupported(
            SourcePropertyUnsupported::MissingOwnProperty {
                node: plan.node,
                receiver_type,
            },
        ))?;
    let class = store
        .symbol(owner)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let instance = store
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .ok_or(SourcePropertyError::Unsupported(
            SourcePropertyUnsupported::MissingOwnProperty {
                node: plan.node,
                receiver_type,
            },
        ))?;
    let static_side = store
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        == Some(receiver_type);
    if !class.flags().contains(SymbolFlags::CLASS) || !static_side && instance != receiver_type {
        return Err(SourcePropertyError::Unsupported(
            SourcePropertyUnsupported::MissingOwnProperty {
                node: plan.node,
                receiver_type,
            },
        ));
    }
    if classes::validate_class_heritage_members(store, instance)
        != ClassHeritageMembersValidation::Valid
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let structured = receiver
        .data()
        .structured()
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let members = structured
        .members
        .and_then(|members| store.symbol_table(members))
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let properties = structured
        .properties
        .as_deref()
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let mut matching_property = None;
    for symbol in properties.iter().copied() {
        let property = store
            .symbol(symbol)
            .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
        if !property.name().is_private_identifier() {
            continue;
        }
        let private_owner = property
            .parent()
            .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
        let private_class = store
            .symbol(private_owner)
            .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
        let private_name =
            classes::authenticated_private_class_symbol_name(store, private_owner, symbol)
                .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
        if !private_class.flags().contains(SymbolFlags::CLASS)
            || members.get(property.name()) != Some(symbol)
        {
            return Err(SourcePropertyError::InvalidCache(plan.node));
        }
        if private_name != plan.name.as_str() {
            continue;
        }
        let declaration = private_class
            .value_declaration()
            .filter(|declaration| {
                store.source_node_kind(*declaration) == Some(SyntaxKind::ClassDeclaration)
            })
            .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
        let candidate = (symbol, private_owner, declaration);
        if enclosing_class == Some(declaration) {
            matching_property = Some(candidate);
            break;
        }
        if matching_property.is_none() {
            matching_property = Some(candidate);
        }
    }
    let Some((symbol, private_owner, declaration)) = matching_property else {
        return Err(SourcePropertyError::Unsupported(
            SourcePropertyUnsupported::MissingOwnProperty {
                node: plan.node,
                receiver_type,
            },
        ));
    };
    let property = store
        .symbol(symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let flags = property.flags();
    let valid_flags = flags == SymbolFlags::PROPERTY
        || flags == SymbolFlags::METHOD
        || flags == SymbolFlags::ACCESSOR;
    let valid_checks = if flags == SymbolFlags::PROPERTY {
        matches!(
            property.check_flags(),
            CheckFlags::NONE | CheckFlags::READONLY
        )
    } else {
        property.check_flags() == CheckFlags::NONE
    };
    let declared_members = store.symbol(private_owner).and_then(|owner| {
        if static_side {
            owner.exports()
        } else {
            owner.members()
        }
    });
    let links = store
        .value_symbol_links(symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let type_ = links
        .resolved_type
        .filter(|type_| store.type_payload(*type_).is_some())
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if !valid_flags
        || !valid_checks
        || property.parent() != Some(private_owner)
        || store.get_merged_symbol(symbol) != Some(symbol)
        || declared_members
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(property.name()))
            != Some(symbol)
        || links
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }

    let (type_, property, diagnostic) = if enclosing_class == Some(declaration) {
        (type_, Some(symbol), None)
    } else {
        (
            error_type,
            None,
            Some(SourcePropertyDiagnostic {
                name_node: plan.name_node,
                receiver_type,
                missing_type: None,
                suggestion: None,
                private_owner: Some(private_owner),
                accessibility: None,
            }),
        )
    };
    publish_property_links(store, plan.node, property, type_)?;
    Ok(CheckedSourceProperty {
        type_,
        diagnostics: diagnostic.into_iter().collect(),
    })
}

/// Reads an already-published method without expanding its global interface.
fn resolve_published_scalar_wrapper_method(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<Option<ResolvedOwnProperty>, SourcePropertyError> {
    let Some(global_types) = global_types else {
        return Ok(None);
    };
    let receiver = store
        .type_payload(receiver_type)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let (wrapper_type, wrapper_name, expected_parameters) = match receiver.flags() {
        flags
            if (flags == TypeFlags::STRING || flags == TypeFlags::STRING_LITERAL)
                && plan.name == "toLowerCase" =>
        {
            (global_types.string_type, "String", 0)
        }
        flags
            if (flags == TypeFlags::NUMBER || flags == TypeFlags::NUMBER_LITERAL)
                && plan.name == "toFixed" =>
        {
            (global_types.number_type, "Number", 1)
        }
        _ => return Ok(None),
    };
    let wrapper = store
        .type_payload(wrapper_type)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let TypeData::Interface(interface) = wrapper.data() else {
        return Ok(None);
    };
    let owner = wrapper
        .symbol()
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let owner_record = store
        .symbol(owner)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if wrapper.flags() != TypeFlags::OBJECT
        || !wrapper.object_flags().contains(ObjectFlags::INTERFACE)
        || wrapper
            .object_flags()
            .intersects(ObjectFlags::CLASS | ObjectFlags::REFERENCE)
        || wrapper.alias().is_some()
        || !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record.name().as_utf8() != Some(wrapper_name)
        || store.get_merged_symbol(owner) != Some(owner)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(wrapper_type)
        || interface
            .all_type_parameters
            .as_ref()
            .is_some_and(|parameters| !parameters.is_empty())
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let Some(members) = owner_record.members() else {
        return Ok(None);
    };
    let members = store
        .symbol_table(members)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let Some(symbol) = members.get_source(&plan.name) else {
        return Ok(None);
    };
    let Some((authenticated_wrapper, declaration)) =
        store.authenticated_global_interface_method(symbol)
    else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    if authenticated_wrapper != wrapper_type {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }

    let Some(links) = store.value_symbol_links(symbol) else {
        return Err(RelationUnavailable::UnresolvedPropertyType(symbol).into());
    };
    let Some(type_) = links.resolved_type else {
        return if links == &ValueSymbolLinks::default() {
            Err(RelationUnavailable::UnresolvedPropertyType(symbol).into())
        } else {
            Err(SourcePropertyError::InvalidCache(plan.node))
        };
    };
    if links
        != &(ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        })
        || store.type_payload(type_).is_none()
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let StoredCallableSetValidation::Valid { projection, .. } =
        validate_stored_callable_set(store, type_)
    else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let [callable] = projection.call_signatures.as_ref() else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let string_type = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?
        .string_type;
    if projection.owner != type_
        || !projection.construct_signatures.is_empty()
        || callable.owner != type_
        || callable.parameters.len() != expected_parameters
        || callable.min_argument_count != 0
        || callable.return_type != Some(string_type)
        || store
            .signature(callable.signature)
            .and_then(super::signatures::Signature::declaration)
            != Some(declaration)
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }

    Ok(Some(ResolvedOwnProperty {
        symbol,
        type_,
        optional: false,
        readonly: false,
    }))
}

fn resolve_published_global_math_random_method(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<Option<ResolvedOwnProperty>, SourcePropertyError> {
    if global_types.is_none()
        || plan.name != "random"
        || !matches!(plan.position, SourcePropertyPosition::CallCallee(_))
    {
        return Ok(None);
    }
    let receiver = store
        .type_payload(receiver_type)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let TypeData::Interface(interface) = receiver.data() else {
        return Ok(None);
    };
    let Some(owner) = receiver
        .symbol()
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    let Some(owner_record) = store.symbol(owner) else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    if owner_record.name().as_utf8() != Some("Math") {
        return Ok(None);
    }
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return Err(RelationUnavailable::MissingBootstrap.into());
    };
    let global = store
        .symbol_table(bootstrap.globals)
        .and_then(|globals| globals.get_source("Math"))
        .and_then(|symbol| store.get_merged_symbol(symbol));
    let allowed =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    let Some(members) = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
    else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let Some(symbol) = members
        .get_source("random")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let Some(method) = store.symbol(symbol) else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let Some([declaration]) = method.declarations() else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let declaration = *declaration;
    if receiver.flags() != TypeFlags::OBJECT
        || receiver.object_flags() != ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
        || receiver.alias().is_some()
        || !owner_record
            .flags()
            .contains(SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        || owner_record.flags().without(allowed) != SymbolFlags::NONE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || global != Some(owner)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(receiver_type)
        || !interface.base_types_resolved
        || !interface.declared_members_resolved
        || interface.declared_members != owner_record.members()
        || interface.reference.object.structured.members != owner_record.members()
        || interface
            .reference
            .object
            .structured
            .properties
            .as_deref()
            .is_none_or(|properties| !properties.contains(&symbol))
        || method.flags() != SymbolFlags::METHOD
        || method.check_flags() != CheckFlags::NONE
        || method.name().as_utf8() != Some("random")
        || method.value_declaration() != Some(declaration)
        || store.source_node_kind(declaration) != Some(SyntaxKind::MethodSignature)
        || store.authenticated_interface_method_owner(symbol) != Some((owner, receiver_type))
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }

    let Some(links) = store.value_symbol_links(symbol) else {
        return Err(RelationUnavailable::UnresolvedPropertyType(symbol).into());
    };
    let Some(type_) = links.resolved_type else {
        return if links == &ValueSymbolLinks::default() {
            Err(RelationUnavailable::UnresolvedPropertyType(symbol).into())
        } else {
            Err(SourcePropertyError::InvalidCache(plan.node))
        };
    };
    if links
        != &(ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let StoredCallableSetValidation::Valid { projection, .. } =
        validate_stored_callable_set(store, type_)
    else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let [callable] = projection.call_signatures.as_ref() else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let Some(signature) = store.signature(callable.signature) else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    if projection.owner != type_
        || !projection.construct_signatures.is_empty()
        || callable.owner != type_
        || !callable.parameters.is_empty()
        || callable.min_argument_count != 0
        || callable.return_type != Some(bootstrap.number_type)
        || !signature.type_parameters().is_empty()
        || signature.this_parameter().is_some()
        || signature.has_rest_parameter()
        || signature.declaration() != Some(declaration)
        || signature.resolved_return_type() != Some(bootstrap.number_type)
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }

    Ok(Some(ResolvedOwnProperty {
        symbol,
        type_,
        optional: false,
        readonly: false,
    }))
}

/// Reads an authenticated, already-published global `Object` factory method.
fn resolve_published_global_object_constructor_method(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<Option<ResolvedOwnProperty>, SourcePropertyError> {
    let Some(global_types) = global_types else {
        return Ok(None);
    };
    if !matches!(plan.name.as_str(), "entries" | "keys" | "values")
        || !matches!(plan.position, SourcePropertyPosition::CallCallee(_))
    {
        return Ok(None);
    }
    let PlannedExpressionKind::Identifier(receiver) = &plan.receiver.unparenthesized().kind else {
        return Ok(None);
    };
    let invalid = || SourcePropertyError::InvalidCache(plan.node);
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    let globals = store.symbol_table(bootstrap.globals).ok_or_else(invalid)?;
    let Some(global_object) = globals
        .get_source("Object")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    if receiver.value_symbol != global_object {
        return Ok(None);
    }
    let Some(owner) = globals
        .get_source("ObjectConstructor")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    let receiver_record = store.type_payload(receiver_type).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = receiver_record.data() else {
        return Err(invalid());
    };
    let allowed_owner_flags = SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT;
    if receiver_record.flags() != TypeFlags::OBJECT
        || !receiver_record
            .object_flags()
            .contains(ObjectFlags::INTERFACE)
        || receiver_record
            .object_flags()
            .intersects(ObjectFlags::CLASS)
        || receiver_record.alias().is_some()
        || receiver_record.symbol() != Some(owner)
        || owner_record.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
        || owner_record.flags().without(allowed_owner_flags) != SymbolFlags::NONE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some("ObjectConstructor")
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(receiver_type)
        || interface
            .all_type_parameters
            .as_ref()
            .is_some_and(|parameters| !parameters.is_empty())
    {
        return Err(invalid());
    }
    let members = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .ok_or_else(invalid)?;
    let Some(symbol) = members
        .get_source(&plan.name)
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    let method = store.symbol(symbol).ok_or_else(invalid)?;
    if method.flags() != SymbolFlags::METHOD
        || method.check_flags() != CheckFlags::NONE
        || method.name().as_utf8() != Some(plan.name.as_str())
        || store.authenticated_interface_method_owner(symbol) != Some((owner, receiver_type))
    {
        return Err(invalid());
    }
    let links = store
        .value_symbol_links(symbol)
        .ok_or(RelationUnavailable::UnresolvedPropertyType(symbol))?;
    let Some(type_) = links.resolved_type else {
        return if links == &ValueSymbolLinks::default() {
            Err(RelationUnavailable::UnresolvedPropertyType(symbol).into())
        } else {
            Err(invalid())
        };
    };
    if links
        != &(ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(invalid());
    }
    let StoredCallableSetValidation::Valid { projection, .. } =
        validate_stored_callable_set(store, type_)
    else {
        return Err(invalid());
    };
    if projection.owner != type_
        || !projection.construct_signatures.is_empty()
        || projection.call_signatures.is_empty()
    {
        return Err(invalid());
    }
    for signature in &projection.call_signatures {
        let return_type = signature.return_type.ok_or_else(invalid)?;
        let array = store
            .canonical_array_reference(global_types, return_type)
            .map_err(|_| invalid())?
            .ok_or_else(invalid)?;
        if signature.owner != type_
            || signature.parameters.len() != 1
            || signature.min_argument_count != 1
            || signature.rest_parameter.is_some()
            || array.readonly
            || match plan.name.as_str() {
                "keys" => array.element_type != bootstrap.string_type,
                "entries" => store
                    .canonical_tuple_shape(array.element_type)
                    .map_err(|_| invalid())?
                    .is_none_or(|tuple| {
                        tuple.element_types().len() != 2
                            || tuple.element_types()[0] != bootstrap.string_type
                    }),
                "values" => false,
                _ => unreachable!("only authenticated Object factory methods are admitted"),
            }
        {
            return Err(invalid());
        }
    }

    Ok(Some(ResolvedOwnProperty {
        symbol,
        type_,
        optional: false,
        readonly: false,
    }))
}

/// Reads a published member from the exact global target of a canonical array.
fn resolve_published_canonical_array_property(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
    session: &mut InstantiationSession,
) -> Result<Option<CanonicalArrayProperty>, SourcePropertyError> {
    let Some(global_types) = global_types else {
        return Ok(None);
    };
    let receiver = store
        .type_payload(receiver_type)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let candidate_target = match receiver.data() {
        TypeData::TypeReference(reference) => reference.object.target,
        TypeData::Interface(interface) => interface.reference.object.target,
        _ => return Ok(None),
    };
    if candidate_target != Some(global_types.array_type)
        && candidate_target != Some(global_types.readonly_array_type)
    {
        return Ok(None);
    }
    let array = store
        .canonical_array_reference(global_types, receiver_type)
        .map_err(|_| SourcePropertyError::InvalidCache(plan.node))?
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let (target, owner_name) = if array.readonly {
        (global_types.readonly_array_type, "ReadonlyArray")
    } else {
        (global_types.array_type, "Array")
    };
    let target_record = store
        .type_payload(target)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let TypeData::Interface(interface) = target_record.data() else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let owner = target_record
        .symbol()
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let owner_record = store
        .symbol(owner)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let global_owner = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source(owner_name))
        .and_then(|symbol| store.get_merged_symbol(symbol));
    let allowed_owner_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    if target_record.flags() != TypeFlags::OBJECT
        || !target_record
            .object_flags()
            .contains(ObjectFlags::INTERFACE)
        || target_record.object_flags().intersects(ObjectFlags::CLASS)
        || target_record.alias().is_some()
        || owner_record.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
        || owner_record.flags().without(allowed_owner_flags) != SymbolFlags::NONE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some(owner_name)
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || global_owner != Some(owner)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(target)
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }

    let members = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let Some(symbol) = members.get_source(&plan.name) else {
        if global_object_affects_missing_property(
            store,
            global_types,
            plan.node,
            &plan.name,
            session,
        )? {
            return Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::ApparentObjectProperty {
                    node: plan.node,
                    receiver_type,
                },
            ));
        }
        return Ok(Some(CanonicalArrayProperty::Missing));
    };
    let symbol = store
        .get_merged_symbol(symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let member = store
        .symbol(symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let Some(declarations) = member
        .declarations()
        .filter(|declarations| !declarations.is_empty())
    else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let owner_declarations = owner_record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let flags = member.flags();
    let is_method = flags == SymbolFlags::METHOD;
    let is_property =
        flags == SymbolFlags::PROPERTY || flags == (SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL);
    let allowed_checks = if is_method {
        CheckFlags::NONE
    } else {
        CheckFlags::READONLY
    };
    if (!is_method && !is_property)
        || member.check_flags().bits() & !allowed_checks.bits() != 0
        || member.name().as_utf8() != Some(plan.name.as_str())
        || member.members().is_some()
        || member.exports().is_some()
        || member.export_symbol().is_some()
        || member
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(owner)
        || member
            .value_declaration()
            .is_none_or(|declaration| !declarations.contains(&declaration))
        || declarations.iter().any(|declaration| {
            let valid_kind = if is_method {
                store.source_node_kind(*declaration) == Some(SyntaxKind::MethodSignature)
            } else {
                matches!(
                    store.source_node_kind(*declaration),
                    Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
                )
            };
            !valid_kind
                || !matches!(
                    store.source_node_parent(*declaration),
                    Some(super::store::SourceNodeParent::Parent(parent))
                        if owner_declarations.contains(&parent)
                )
        })
        || interface.declared_members.is_some_and(|declared| {
            store.symbol_table(declared).is_none_or(|declared| {
                declared
                    .get_source(&plan.name)
                    .is_some_and(|declared| store.get_merged_symbol(declared) != Some(symbol))
            })
        })
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }

    let Some(links) = store.value_symbol_links(symbol) else {
        return Err(RelationUnavailable::UnresolvedPropertyType(symbol).into());
    };
    let Some(type_) = links.resolved_type else {
        return if links == &ValueSymbolLinks::default() {
            Err(RelationUnavailable::UnresolvedPropertyType(symbol).into())
        } else {
            Err(SourcePropertyError::InvalidCache(plan.node))
        };
    };
    if links
        != &(ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        })
        || store.type_payload(type_).is_none()
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let readonly = member.check_flags().contains(CheckFlags::READONLY);
    if is_method {
        validate_published_canonical_array_method(store, plan.node, symbol, declarations, type_)?;
    }
    let instantiation = if is_method {
        let requires = super::instantiated_members::published_method_requires_instantiation(
            store,
            global_types,
            symbol,
        );
        Some(requires.and_then(|requires| {
            if requires {
                super::instantiated_members::instantiate_published_generic_interface_method_with_session(
                    store,
                    global_types,
                    receiver_type,
                    symbol,
                    session,
                )
            } else {
                Ok(type_)
            }
        }))
    } else if is_property && store.type_has_function_type_provenance(type_) {
        Some(
            super::instantiated_members::instantiate_published_generic_array_property_callable(
                store,
                global_types,
                receiver_type,
                symbol,
            ),
        )
    } else {
        None
    };
    let type_ = if let Some(instantiation) = instantiation {
        instantiation.map_err(|error| match error {
            super::instantiated_members::GenericInterfaceMemberError::Capacity(_) => {
                SourcePropertyError::Capacity(plan.node)
            }
            super::instantiated_members::GenericInterfaceMemberError::UnsupportedTarget(_)
            | super::instantiated_members::GenericInterfaceMemberError::UnsupportedMember(_)
            | super::instantiated_members::GenericInterfaceMemberError::UnsupportedPropertyType(
                _,
            ) => SourcePropertyError::Unsupported(SourcePropertyUnsupported::Access(plan.node)),
            super::instantiated_members::GenericInterfaceMemberError::Reference(_)
            | super::instantiated_members::GenericInterfaceMemberError::InvalidTarget(_)
            | super::instantiated_members::GenericInterfaceMemberError::InvalidMember(_)
            | super::instantiated_members::GenericInterfaceMemberError::InvalidCachedMembers(_)
            | super::instantiated_members::GenericInterfaceMemberError::InvalidCachedProperty(
                _,
            ) => SourcePropertyError::InvalidCache(plan.node),
        })?
    } else {
        type_
    };

    Ok(Some(CanonicalArrayProperty::Present(ResolvedOwnProperty {
        symbol,
        type_,
        optional: flags.contains(SymbolFlags::OPTIONAL),
        readonly,
    })))
}

fn validate_published_canonical_array_method(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    method: SemanticSymbolId,
    declarations: &[NodeRef],
    type_: TypeId,
) -> Result<(), SourcePropertyError> {
    let record = store
        .type_payload(type_)
        .ok_or(SourcePropertyError::InvalidCache(node))?;
    let TypeData::Object(callable) = record.data() else {
        return Err(SourcePropertyError::InvalidCache(node));
    };
    let Some(signatures) = callable
        .structured
        .signatures
        .as_deref()
        .filter(|signatures| !signatures.is_empty())
    else {
        return Err(SourcePropertyError::InvalidCache(node));
    };
    if record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(method)
        || record.alias().is_some()
        || callable.structured.call_signature_count != signatures.len()
        || signatures.len() != declarations.len()
        || declarations.iter().any(|declaration| {
            signatures
                .iter()
                .filter(|signature| {
                    store
                        .signature(**signature)
                        .and_then(super::signatures::Signature::declaration)
                        == Some(*declaration)
                })
                .count()
                != 1
        })
        || signatures.iter().any(|signature| {
            let Some(record) = store.signature(*signature) else {
                return true;
            };
            let Some(declaration) = record.declaration() else {
                return true;
            };
            store
                .signature_links(declaration)
                .and_then(|links| links.resolved_signature.signature())
                != Some(*signature)
                || record
                    .resolved_return_type()
                    .is_some_and(|return_type| store.type_payload(return_type).is_none())
                || record.parameters().iter().any(|parameter| {
                    let Some(parameter) = store.symbol(*parameter) else {
                        return true;
                    };
                    let Some([parameter_declaration]) = parameter.declarations() else {
                        return true;
                    };
                    store.source_node_kind(*parameter_declaration) != Some(SyntaxKind::Parameter)
                        || store.source_node_parent(*parameter_declaration)
                            != Some(super::store::SourceNodeParent::Parent(declaration))
                })
                || record
                    .type_parameters()
                    .iter()
                    .any(|parameter| store.type_payload(*parameter).is_none())
        })
    {
        return Err(SourcePropertyError::InvalidCache(node));
    }
    Ok(())
}

fn resolve_published_source_callable_expando_property(
    store: &CanonicalTypeMapperStore,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<Option<ResolvedOwnProperty>, SourcePropertyError> {
    let Some(provenance) = store.source_callable_provenance(receiver_type) else {
        return Ok(None);
    };
    let Some(owner) = store.symbol(provenance.owner_symbol) else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let Some(exports) = owner.exports() else {
        return Ok(None);
    };
    let valid_exports = match provenance.family {
        SourceCallableFamily::ArrowFunction => source_arrow_owner_expando_exports_are_valid(
            store,
            provenance.owner_symbol,
            provenance.declaration,
        ),
        SourceCallableFamily::FunctionDeclaration => {
            source_function_owner_expando_exports_are_valid(
                store,
                provenance.owner_symbol,
                provenance.declaration,
            )
        }
    };
    if !valid_exports
        || !matches!(
            validate_stored_source_callable(store, receiver_type),
            StoredSourceCallableValidation::Valid(_)
        )
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let exports = store
        .symbol_table(exports)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let Some(symbol) = exports.get_source(&plan.name) else {
        return Ok(None);
    };
    let property = store
        .symbol(symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let links = store
        .value_symbol_links(symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let type_ = links
        .resolved_type
        .filter(|type_| store.type_payload(*type_).is_some())
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if property.flags() != SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
        || property.check_flags() != CheckFlags::NONE
        || property.name().as_utf8() != Some(plan.name.as_str())
        || property.parent() != Some(provenance.owner_symbol)
        || property.members().is_some()
        || property.exports().is_some()
        || property.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || links
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    Ok(Some(ResolvedOwnProperty {
        symbol,
        type_,
        optional: false,
        readonly: false,
    }))
}

fn resolve_class_static_property(
    store: &CanonicalTypeMapperStore,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<Option<ClassStaticProperty>, SourcePropertyError> {
    let receiver = store
        .type_payload(receiver_type)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let Some(owner) = receiver.symbol() else {
        return Ok(None);
    };
    let owner = store
        .get_merged_symbol(owner)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let class = store
        .symbol(owner)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if !class.flags().contains(SymbolFlags::CLASS) {
        return Ok(None);
    }
    if store
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        != Some(receiver_type)
    {
        return Ok(None);
    }

    let instance = store
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if classes::validate_class_heritage_members(store, instance)
        != ClassHeritageMembersValidation::Valid
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let TypeData::Object(value) = receiver.data() else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let members = value
        .structured
        .members
        .and_then(|members| store.symbol_table(members))
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let Some(symbol) = members.get_source(&plan.name) else {
        return Ok(Some(ClassStaticProperty::Missing));
    };
    let property = store
        .symbol(symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if value
        .structured
        .properties
        .as_deref()
        .is_none_or(|properties| !properties.contains(&symbol))
        || store.get_merged_symbol(symbol) != Some(symbol)
        || property.name().as_utf8() != Some(plan.name.as_str())
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }

    let flags = property.flags();
    let type_ = if flags == (SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE) {
        if property.parent() != Some(owner) || property.name().as_utf8() != Some("prototype") {
            return Err(SourcePropertyError::InvalidCache(plan.node));
        }
        instance
    } else {
        if flags != SymbolFlags::PROPERTY
            && flags != SymbolFlags::METHOD
            && flags != (SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
        {
            return Err(SourcePropertyError::InvalidCache(plan.node));
        }
        let links = store
            .value_symbol_links(symbol)
            .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
        let type_ = links
            .resolved_type
            .filter(|type_| store.type_payload(*type_).is_some())
            .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
        if links
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
        {
            return Err(SourcePropertyError::InvalidCache(plan.node));
        }
        type_
    };

    Ok(Some(ClassStaticProperty::Present(ResolvedOwnProperty {
        symbol,
        type_,
        optional: flags.contains(SymbolFlags::OPTIONAL),
        readonly: property.check_flags().contains(CheckFlags::READONLY),
    })))
}

fn resolve_class_instance_member(
    store: &CanonicalTypeMapperStore,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<Option<ClassInstanceProperty>, SourcePropertyError> {
    let receiver = store
        .type_payload(receiver_type)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let Some(owner) = receiver.symbol() else {
        return Ok(None);
    };
    let owner = store
        .get_merged_symbol(owner)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let class = store
        .symbol(owner)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if !class.flags().contains(SymbolFlags::CLASS)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(receiver_type)
    {
        return Ok(None);
    }

    let structured = receiver
        .data()
        .structured()
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let members = structured
        .members
        .and_then(|members| store.symbol_table(members))
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let private_surface = members.iter().any(|(name, _)| name.is_private_identifier());
    if private_surface
        && classes::validate_class_heritage_members(store, receiver_type)
            != ClassHeritageMembersValidation::Valid
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let Some(symbol) = members.get_source(&plan.name) else {
        return Ok(private_surface.then_some(ClassInstanceProperty::Missing));
    };
    let member = store
        .symbol(symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let flags = member.flags();
    let accessor = flags.intersects(SymbolFlags::ACCESSOR);
    if !accessor && !private_surface {
        return Ok(None);
    }
    let supported_flags = if accessor {
        flags == SymbolFlags::ACCESSOR
    } else {
        flags == SymbolFlags::PROPERTY
            || flags == (SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
            || flags == SymbolFlags::METHOD
    };
    let valid_parent = if accessor {
        member.parent() == Some(owner)
    } else {
        member
            .parent()
            .and_then(|parent| store.symbol(parent))
            .is_some_and(|parent| parent.flags().contains(SymbolFlags::CLASS))
    };
    if classes::validate_class_heritage_members(store, receiver_type)
        != ClassHeritageMembersValidation::Valid
        || !supported_flags
        || !valid_parent
        || member.name().as_utf8() != Some(plan.name.as_str())
        || store.get_merged_symbol(symbol) != Some(symbol)
        || structured
            .properties
            .as_deref()
            .is_none_or(|properties| !properties.contains(&symbol))
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }

    let links = store
        .value_symbol_links(symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let type_ = links
        .resolved_type
        .filter(|type_| store.type_payload(*type_).is_some())
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if links
        != &(ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }

    Ok(Some(ClassInstanceProperty::Present(ResolvedOwnProperty {
        symbol,
        type_,
        optional: flags.contains(SymbolFlags::OPTIONAL),
        readonly: member.check_flags().contains(CheckFlags::READONLY),
    })))
}

fn resolve_enum_property(
    store: &CanonicalTypeMapperStore,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<Option<NamespaceProperty>, SourcePropertyError> {
    let receiver = store
        .type_payload(receiver_type)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let Some(owner) = receiver.symbol() else {
        return Ok(None);
    };
    let owner = store
        .get_merged_symbol(owner)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let record = store
        .symbol(owner)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if !record.flags().intersects(SymbolFlags::ENUM) {
        return Ok(None);
    }
    if store
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        != Some(receiver_type)
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let member = match record.exports() {
        Some(exports) => store
            .symbol_table(exports)
            .ok_or(SourcePropertyError::InvalidCache(plan.node))?
            .get_source(&plan.name),
        None => None,
    };
    let Some(member) = member else {
        return Ok(Some(NamespaceProperty::Missing));
    };
    let (symbol, type_) = enums::enum_value_member_type(store, receiver_type, &plan.name)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if store.get_merged_symbol(member) != Some(symbol) {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    Ok(Some(NamespaceProperty::Present { symbol, type_ }))
}

fn resolve_namespace_property(
    store: &CanonicalTypeMapperStore,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<Option<NamespaceProperty>, SourcePropertyError> {
    let receiver = store
        .type_payload(receiver_type)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let receiver_module = match validated_source_file_namespace_owner(store, receiver_type)
        .map_err(|_| SourcePropertyError::InvalidCache(plan.node))?
    {
        Some(module) if store.get_merged_symbol(module) == Some(module) => Some(module),
        Some(_) => return Err(SourcePropertyError::InvalidCache(plan.node)),
        None => receiver
            .symbol()
            .map(|symbol| {
                store
                    .get_merged_symbol(symbol)
                    .ok_or(SourcePropertyError::InvalidCache(plan.node))
            })
            .transpose()?
            .filter(|symbol| {
                store
                    .symbol(*symbol)
                    .is_some_and(|record| record.flags().intersects(SymbolFlags::MODULE))
            }),
    };
    let alias_module = if let PlannedExpressionKind::Identifier(read) = &plan.receiver.kind {
        let receiver_symbol = store
            .symbol(read.value_symbol)
            .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
        if receiver_symbol.flags().contains(SymbolFlags::ALIAS) {
            let links = store
                .alias_symbol_links(read.value_symbol)
                .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
            if links.type_only_declaration.is_some() {
                return Err(SourcePropertyError::InvalidCache(plan.node));
            }
            links.alias_target.symbol()
        } else if receiver_symbol.flags().intersects(SymbolFlags::MODULE) {
            Some(read.value_symbol)
        } else {
            None
        }
    } else {
        None
    };
    let module = match (receiver_module, alias_module) {
        (Some(owner), Some(alias)) if owner != alias => {
            return Err(SourcePropertyError::InvalidCache(plan.node));
        }
        (Some(owner), _) => owner,
        (None, Some(alias)) => alias,
        (None, None) => return Ok(None),
    };
    let owner = store
        .symbol(module)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if !owner.flags().intersects(SymbolFlags::MODULE) {
        return Ok(None);
    }
    let TypeData::Object(object) = receiver.data() else {
        let merged_interface_namespace = owner.flags()
            == SymbolFlags::INTERFACE | SymbolFlags::NAMESPACE_MODULE
            && owner.check_flags() == CheckFlags::NONE
            && owner.value_declaration().is_none()
            && owner.parent().is_none()
            && owner.members().is_some()
            && owner.exports().is_some()
            && store.get_merged_symbol(module) == Some(module)
            && owner.declarations().is_some_and(|declarations| {
                declarations.len() == 2
                    && declarations.iter().any(|declaration| {
                        store.source_node_kind(*declaration)
                            == Some(SyntaxKind::InterfaceDeclaration)
                    })
                    && declarations.iter().any(|declaration| {
                        store.source_node_kind(*declaration) == Some(SyntaxKind::ModuleDeclaration)
                    })
            });
        if merged_interface_namespace
            && matches!(receiver.data(), TypeData::Interface(_))
            && receiver.symbol() == Some(module)
            && store
                .declared_type_links(module)
                .and_then(|links| links.declared_type)
                == Some(receiver_type)
        {
            let members = owner
                .members()
                .and_then(|members| store.symbol_table(members))
                .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
            let Some(symbol) = members.get_source(&plan.name) else {
                return Ok(None);
            };
            let symbol = store
                .get_merged_symbol(symbol)
                .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
            let method = store
                .symbol(symbol)
                .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
            if method.flags() != SymbolFlags::METHOD {
                return Ok(None);
            }
            let links = store
                .value_symbol_links(symbol)
                .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
            let type_ = links
                .resolved_type
                .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
            if store.authenticated_interface_method_owner(symbol) != Some((module, receiver_type))
                || links
                    != &(ValueSymbolLinks {
                        resolved_type: Some(type_),
                        ..ValueSymbolLinks::default()
                    })
                || !matches!(
                    validate_stored_callable_set(store, type_),
                    StoredCallableSetValidation::Valid { ref projection, .. }
                        if projection.construct_signatures.is_empty()
                            && !projection.call_signatures.is_empty()
                )
            {
                return Err(SourcePropertyError::InvalidCache(plan.node));
            }
            return Ok(Some(NamespaceProperty::Present { symbol, type_ }));
        }
        if merged_interface_namespace
            && alias_module == Some(module)
            && store
                .intrinsic_bootstrap()
                .is_some_and(|bootstrap| receiver_type == bootstrap.error_type)
        {
            return Ok(None);
        }
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    if store
        .source_file_namespace_wrapper_for_module(module)
        .is_some()
    {
        if receiver.symbol() != Some(module) {
            return Err(SourcePropertyError::InvalidCache(plan.node));
        }
        let member = source_file_namespace_wrapper_member(store, receiver_type, &plan.name)
            .map_err(|_| SourcePropertyError::InvalidCache(plan.node))?;
        return Ok(Some(match member {
            Some((symbol, type_)) => NamespaceProperty::Present { symbol, type_ },
            None => NamespaceProperty::Missing,
        }));
    }
    let exports = store
        .module_symbol_links(module)
        .and_then(|links| links.resolved_exports)
        .or_else(|| owner.exports())
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let export_table = store
        .symbol_table(exports)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let Some(symbol) = export_table.get_source(&plan.name) else {
        return Ok(Some(NamespaceProperty::Missing));
    };
    let symbol = store
        .get_merged_symbol(symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let record = store
        .symbol(symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let value_symbol = if record.flags().contains(SymbolFlags::ALIAS) {
        let links = store
            .alias_symbol_links(symbol)
            .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
        if links.type_only_declaration.is_some() {
            return Ok(Some(NamespaceProperty::Missing));
        }
        links
            .alias_target
            .symbol()
            .and_then(|target| store.get_merged_symbol(target))
            .ok_or(SourcePropertyError::InvalidCache(plan.node))?
    } else {
        symbol
    };
    let value_record = store
        .symbol(value_symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if !value_record.flags().intersects(SymbolFlags::VALUE) {
        return Ok(Some(NamespaceProperty::Missing));
    }
    let projected = match object.structured.members {
        Some(members) if members != exports => {
            let table = store
                .symbol_table(members)
                .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
            let property = table
                .get_source(&plan.name)
                .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
            let projected = store
                .symbol(property)
                .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
            let links = store
                .value_symbol_links(property)
                .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
            if projected.flags() != SymbolFlags::PROPERTY
                || links.target.is_some_and(|target| target != symbol)
                || object
                    .structured
                    .properties
                    .as_deref()
                    .is_none_or(|properties| !properties.contains(&property))
            {
                return Err(SourcePropertyError::InvalidCache(plan.node));
            }
            Some(
                links
                    .resolved_type
                    .ok_or(SourcePropertyError::InvalidCache(plan.node))?,
            )
        }
        _ => None,
    };
    let cached = store
        .value_symbol_links(value_symbol)
        .and_then(|links| links.resolved_type);
    let callable = store.source_callable_type_for_owner(value_symbol);
    if cached
        .zip(callable)
        .is_some_and(|(cached, callable)| cached != callable)
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    if projected
        .zip(cached.or(callable))
        .is_some_and(|(projected, target)| projected != target)
    {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    let type_ = cached
        .or(callable)
        .or(projected)
        .ok_or(SourcePropertyError::Unsupported(
            SourcePropertyUnsupported::MissingOwnProperty {
                node: plan.node,
                receiver_type,
            },
        ))?;
    if store.type_payload(type_).is_none() {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    }
    Ok(Some(NamespaceProperty::Present { symbol, type_ }))
}

fn receiver_continues_optional_chain(arena: &NodeArena, receiver: &ts_ast::Node) -> bool {
    match &receiver.data {
        NodeData::PropertyAccessExpression(access) => {
            access.question_dot_token.is_some()
                || arena
                    .get(access.expression)
                    .is_some_and(|parent| receiver_continues_optional_chain(arena, parent))
        }
        NodeData::ElementAccessExpression(access) => {
            access.question_dot_token.is_some()
                || arena
                    .get(access.expression)
                    .is_some_and(|parent| receiver_continues_optional_chain(arena, parent))
        }
        _ => false,
    }
}

fn optional_property_receiver(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<(TypeId, bool), SourcePropertyError> {
    let strict = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?
        .options
        .strict_null_checks;
    if !strict {
        return Ok((receiver_type, false));
    }
    let Some(record) = store.type_payload(receiver_type) else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    if !record.flags().intersects(TypeFlags::UNION) {
        if record.flags().intersects(TypeFlags::NULLABLE) {
            return Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::Receiver(plan.receiver.node),
            ));
        }
        return Ok((receiver_type, false));
    }
    let TypeData::Union(union) = record.data() else {
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
    let constituents = union.union.types.clone();
    let mut retained = Vec::with_capacity(constituents.len());
    for constituent in constituents.iter().copied() {
        let flags = store
            .type_payload(constituent)
            .map(TypeRecord::flags)
            .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
        if !flags.intersects(TypeFlags::NULLABLE) {
            retained.push(constituent);
        }
    }
    if retained.len() == constituents.len() {
        return Ok((receiver_type, false));
    }
    let Some(first) = retained.first().copied() else {
        return Err(SourcePropertyError::Unsupported(
            SourcePropertyUnsupported::Receiver(plan.receiver.node),
        ));
    };
    let receiver = if retained.len() == 1 {
        first
    } else {
        property_union_type(store, global_types, plan.node, &retained, None)?
    };
    Ok((receiver, true))
}

fn property_union_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    node: NodeRef,
    types: &[TypeId],
    property: Option<SemanticSymbolId>,
) -> Result<TypeId, SourcePropertyError> {
    if let Some(global_types) = global_types {
        return store
            .expression_union_type_with_global_types(global_types, types, UnionReduction::Literal)
            .map_err(|error| SourcePropertyError::Union {
                node,
                error: UnionPropertyError::TypeCache(error),
            });
    }
    #[cfg(test)]
    {
        let _ = property;
        store
            .expression_union_type(types, UnionReduction::Literal)
            .map_err(|error| SourcePropertyError::Union {
                node,
                error: UnionPropertyError::TypeCache(error),
            })
    }
    #[cfg(not(test))]
    {
        let Some(property) = property else {
            return Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::Access(node),
            ));
        };
        Err(SourcePropertyError::Unsupported(
            SourcePropertyUnsupported::OptionalProperty { node, property },
        ))
    }
}

fn copied_union_constituents(
    store: &CanonicalTypeMapperStore,
    receiver_type: TypeId,
) -> Option<[TypeId; 2]> {
    let Some(TypeData::Union(union)) = store.type_payload(receiver_type).map(TypeRecord::data)
    else {
        return None;
    };
    let [left, right] = union.union.types.as_slice() else {
        return None;
    };
    Some([*left, *right])
}

fn copied_first_missing_union_constituent(
    store: &CanonicalTypeMapperStore,
    plan: &SourcePropertyPlan,
    constituents: [TypeId; 2],
) -> CopiedMissingUnionProperty {
    let mut first_missing = None;
    for constituent in constituents {
        let Some(structured) = store
            .type_payload(constituent)
            .and_then(|record| record.data().structured())
        else {
            return CopiedMissingUnionProperty::Unavailable;
        };
        let present = match structured.members {
            Some(members) => {
                let Some(members) = store.symbol_table(members) else {
                    return CopiedMissingUnionProperty::Unavailable;
                };
                members.get_source(&plan.name).is_some()
            }
            None => false,
        };
        if !present && first_missing.is_none() {
            first_missing = Some(constituent);
        }
    }
    first_missing.map_or(
        CopiedMissingUnionProperty::PresentEverywhere,
        CopiedMissingUnionProperty::Missing,
    )
}

fn copied_common_union_property_candidates(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    constituents: [TypeId; 2],
) -> Result<Option<Vec<SemanticSymbolId>>, SourcePropertyError> {
    let Some(left) = store
        .type_payload(constituents[0])
        .and_then(|record| record.data().structured())
    else {
        return Ok(None);
    };
    let Some(right) = store
        .type_payload(constituents[1])
        .and_then(|record| record.data().structured())
    else {
        return Ok(None);
    };
    let Some(left_members) = left.members else {
        return Ok(Some(Vec::new()));
    };
    let Some(right_members) = right.members else {
        return Ok(Some(Vec::new()));
    };
    let Some(left_members) = store.symbol_table(left_members) else {
        return Ok(None);
    };
    let Some(right_members) = store.symbol_table(right_members) else {
        return Ok(None);
    };
    let mut candidates = Vec::new();
    candidates
        .try_reserve_exact(left_members.len())
        .map_err(|_| SourcePropertyError::Capacity(node))?;
    for (name, property) in left_members.iter() {
        if name
            .as_utf8()
            .is_some_and(|name| right_members.get_source(name).is_some())
        {
            candidates.push(property);
        }
    }
    Ok(Some(candidates))
}

fn stable_property_spelling_suggestion(
    store: &CanonicalTypeMapperStore,
    name: &str,
    candidates: &[SemanticSymbolId],
) -> Result<Option<SemanticSymbolId>, ()> {
    let candidate_name = |candidate: &SemanticSymbolId| {
        store
            .symbol(*candidate)
            .and_then(|record| record.name().as_utf8())
    };
    let ascending = get_spelling_suggestion(
        name,
        candidates.iter().copied(),
        candidate_name,
        |left, right| {
            candidate_name(left)
                .expect("an eligible property candidate retains its source name")
                .cmp(
                    candidate_name(right)
                        .expect("an eligible property candidate retains its source name"),
                )
        },
    );
    let descending = get_spelling_suggestion(
        name,
        candidates.iter().copied(),
        candidate_name,
        |left, right| {
            candidate_name(right)
                .expect("an eligible property candidate retains its source name")
                .cmp(
                    candidate_name(left)
                        .expect("an eligible property candidate retains its source name"),
                )
        },
    );
    match (ascending, descending) {
        (None, None) => Ok(None),
        (Some(ascending), Some(descending)) if ascending == descending => Ok(Some(ascending)),
        _ => Err(()),
    }
}

fn direct_property_spelling_suggestion(
    store: &CanonicalTypeMapperStore,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<Option<SemanticSymbolId>, SourcePropertyError> {
    let Some(members) = store
        .type_payload(receiver_type)
        .and_then(|record| record.data().structured())
        .and_then(|structured| structured.members)
    else {
        return Ok(None);
    };
    let members = store
        .symbol_table(members)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    let mut candidates = Vec::new();
    candidates
        .try_reserve_exact(members.len())
        .map_err(|_| SourcePropertyError::Capacity(plan.node))?;
    candidates.extend(
        members
            .iter()
            .filter_map(|(name, symbol)| name.as_utf8().map(|_| symbol)),
    );
    stable_property_spelling_suggestion(store, &plan.name, &candidates).map_err(|()| {
        SourcePropertyError::Unsupported(SourcePropertyUnsupported::AmbiguousPropertySuggestion {
            node: plan.node,
            receiver_type,
        })
    })
}

fn resolve_common_global_object_property(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    constituents: [TypeId; 2],
    name: &str,
    session: &mut InstantiationSession,
) -> Result<Option<ResolvedOwnProperty>, SourcePropertyError> {
    for constituent in constituents {
        if store.resolved_own_property(constituent, name)?.is_some() {
            return Ok(None);
        }
    }
    super::object_members::resolve_object_property_by_key(
        store,
        Some(global_types),
        global_types.object_type,
        EscapedNameRef::source(name),
        session,
    )
    .map_err(Into::into)
}

fn global_object_affects_missing_property(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    node: NodeRef,
    name: &str,
    session: &mut InstantiationSession,
) -> Result<bool, SourcePropertyError> {
    if super::object_members::resolve_object_property_by_key(
        store,
        Some(global_types),
        global_types.object_type,
        EscapedNameRef::source(name),
        session,
    )?
    .is_some()
    {
        return Ok(true);
    }
    let record = store
        .type_payload(global_types.object_type)
        .ok_or(SourcePropertyError::InvalidCache(node))?;
    let structured = record
        .data()
        .structured()
        .ok_or(SourcePropertyError::InvalidCache(node))?;
    // The provider validated the member table even when its types remain cold.
    let members = structured.members.or_else(|| {
        record
            .symbol()
            .and_then(|symbol| store.symbol(symbol))
            .and_then(ts_binder::semantic::Symbol::members)
    });
    let Some(members) = members else {
        return Ok(false);
    };
    let members = store
        .symbol_table(members)
        .ok_or(SourcePropertyError::InvalidCache(node))?;
    if members.get_source(name).is_some() {
        return Ok(true);
    }
    Ok(get_spelling_suggestion(
        name,
        members
            .iter()
            .filter_map(|(candidate, _)| candidate.as_utf8()),
        |candidate| Some(*candidate),
        Ord::cmp,
    )
    .is_some())
}

/// Renders exact public or private property diagnostics after recursive
/// expression execution reaches the source-owned diagnostic staging boundary.
pub(super) fn prepare_source_property_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    deferred: &SourcePropertyDiagnostic,
) -> Result<CanonicalCheckerDiagnostic, SourcePropertyError> {
    let mut flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
    if options.no_error_truncation {
        flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
    }
    let (name, private_name) = match host.node(deferred.name_node) {
        Some(node)
            if node.kind == SyntaxKind::StringLiteral
                && matches!(
                    deferred.accessibility,
                    Some(ClassPropertyAccessDiagnostic::Class {
                        binding: Some(_),
                        ..
                    })
                ) =>
        {
            let NodeData::StringLiteral(literal) = &node.data else {
                return Err(SourcePropertyError::InvalidCache(deferred.name_node));
            };
            (literal.text.as_str(), false)
        }
        Some(node) if node.kind == SyntaxKind::Identifier => match &node.data {
            NodeData::Identifier(identifier) if !identifier.text.is_empty() => {
                (identifier.text.as_str(), false)
            }
            _ => return Err(SourcePropertyError::InvalidCache(deferred.name_node)),
        },
        Some(node) if node.kind == SyntaxKind::PrivateIdentifier => match &node.data {
            NodeData::PrivateIdentifier(identifier)
                if identifier.text.starts_with('#') && identifier.text.len() > 1 =>
            {
                (identifier.text.as_str(), true)
            }
            _ => return Err(SourcePropertyError::InvalidCache(deferred.name_node)),
        },
        _ => return Err(SourcePropertyError::InvalidCache(deferred.name_node)),
    };
    if let Some(ClassPropertyAccessDiagnostic::Class {
        context,
        property,
        lookup_type,
        kind,
        binding,
    }) = deferred.accessibility
    {
        return prepare_class_access_diagnostic(
            store,
            host,
            global_types,
            options,
            deferred,
            name,
            private_name,
            &context,
            property,
            lookup_type,
            kind,
            binding,
        );
    }
    if let Some(accessibility) = deferred.accessibility {
        let property = match accessibility {
            ClassPropertyAccessDiagnostic::Private { property, .. }
            | ClassPropertyAccessDiagnostic::Protected { property, .. }
            | ClassPropertyAccessDiagnostic::ProtectedReceiver { property, .. } => property,
            ClassPropertyAccessDiagnostic::Class { .. } => {
                unreachable!("class diagnostics returned earlier")
            }
        };
        if private_name
            || deferred.private_owner.is_some()
            || deferred.missing_type.is_some()
            || deferred.suggestion.is_some()
            || store
                .symbol(property)
                .and_then(|record| record.name().as_utf8())
                != Some(name)
            || class_property_accessibility(
                store,
                deferred.name_node,
                deferred.receiver_type,
                property,
            )? != Some(accessibility)
        {
            return Err(SourcePropertyError::InvalidCache(deferred.name_node));
        }
        let (code, class, include_receiver) = match accessibility {
            ClassPropertyAccessDiagnostic::Private { owner, .. }
            | ClassPropertyAccessDiagnostic::Protected { owner, .. } => {
                let class = store
                    .declared_type_links(owner)
                    .and_then(|links| links.declared_type)
                    .ok_or(SourcePropertyError::InvalidCache(deferred.name_node))?;
                let code = if matches!(accessibility, ClassPropertyAccessDiagnostic::Private { .. })
                {
                    2341
                } else {
                    2445
                };
                (code, class, false)
            }
            ClassPropertyAccessDiagnostic::ProtectedReceiver {
                enclosing_class, ..
            } => (2446, enclosing_class, true),
            ClassPropertyAccessDiagnostic::Class { .. } => {
                unreachable!("class diagnostics returned earlier")
            }
        };
        let class = type_to_string_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            class,
            flags,
        )?;
        let mut arguments = vec![name.to_owned(), class];
        if include_receiver {
            arguments.push(type_to_string_with_host_global_types_and_flags(
                store,
                host,
                global_types,
                deferred.receiver_type,
                flags,
            )?);
        }
        return Ok(CanonicalCheckerDiagnostic {
            node: Some(deferred.name_node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(code).ok_or(SourcePropertyError::MissingDiagnostic(code))?,
                arguments,
            ),
            related_information: Vec::new(),
        });
    }
    if let Some(private_owner) = deferred.private_owner {
        if !private_name || deferred.missing_type.is_some() || deferred.suggestion.is_some() {
            return Err(SourcePropertyError::InvalidCache(deferred.name_node));
        }
        let owner = store
            .symbol(private_owner)
            .ok_or(SourcePropertyError::InvalidCache(deferred.name_node))?;
        let owner_name = owner
            .name()
            .as_utf8()
            .ok_or(SourcePropertyError::InvalidCache(deferred.name_node))?;
        let receiver = store
            .type_payload(deferred.receiver_type)
            .ok_or(SourcePropertyError::InvalidCache(deferred.name_node))?;
        let receiver_owner = receiver
            .symbol()
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .ok_or(SourcePropertyError::InvalidCache(deferred.name_node))?;
        let instance = store
            .declared_type_links(receiver_owner)
            .and_then(|links| links.declared_type)
            .ok_or(SourcePropertyError::InvalidCache(deferred.name_node))?;
        let valid_receiver = deferred.receiver_type == instance
            || store
                .value_symbol_links(receiver_owner)
                .and_then(|links| links.resolved_type)
                == Some(deferred.receiver_type);
        if !owner.flags().contains(SymbolFlags::CLASS)
            || !valid_receiver
            || classes::validate_class_heritage_members(store, instance)
                != ClassHeritageMembersValidation::Valid
            || receiver
                .data()
                .structured()
                .and_then(|structured| structured.properties.as_deref())
                .is_none_or(|properties| {
                    !properties.iter().copied().any(|symbol| {
                        classes::authenticated_private_class_symbol_name(
                            store,
                            private_owner,
                            symbol,
                        ) == Some(name)
                            && store
                                .symbol(symbol)
                                .and_then(ts_binder::semantic::Symbol::parent)
                                == Some(private_owner)
                    })
                })
        {
            return Err(SourcePropertyError::InvalidCache(deferred.name_node));
        }
        return Ok(CanonicalCheckerDiagnostic {
            node: Some(deferred.name_node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(18_013).ok_or(SourcePropertyError::MissingDiagnostic(18_013))?,
                [name, owner_name],
            ),
            related_information: Vec::new(),
        });
    }
    if private_name {
        return Err(SourcePropertyError::InvalidCache(deferred.name_node));
    }
    let suggestion = match deferred.suggestion {
        Some(suggestion) => Some(
            store
                .symbol(suggestion)
                .and_then(|record| record.name().as_utf8())
                .ok_or(SourcePropertyError::InvalidCache(deferred.name_node))?,
        ),
        None => None,
    };
    let receiver = type_to_string_with_host_global_types_and_flags(
        store,
        host,
        global_types,
        deferred.receiver_type,
        flags,
    )?;
    let mut diagnostic = match suggestion {
        Some(suggestion) => Diagnostic::with_arguments(
            message_by_code(2551).ok_or(SourcePropertyError::MissingDiagnostic(2551))?,
            [name, receiver.as_str(), suggestion],
        ),
        None => Diagnostic::with_arguments(
            message_by_code(2339).ok_or(SourcePropertyError::MissingDiagnostic(2339))?,
            [name, receiver.as_str()],
        ),
    };
    if let Some(missing_type) = deferred.missing_type {
        let missing = type_to_string_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            missing_type,
            flags,
        )?;
        let detail = Diagnostic::with_arguments(
            message_by_code(2339).ok_or(SourcePropertyError::MissingDiagnostic(2339))?,
            [name, missing.as_str()],
        )
        .render()
        .expect("the pinned property diagnostic detail has complete arguments");
        diagnostic = diagnostic.with_details([format!("  {detail}")]);
    }
    Ok(CanonicalCheckerDiagnostic {
        node: Some(deferred.name_node),
        range_override: None,
        diagnostic,
        related_information: Vec::new(),
    })
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prepare_class_access_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    deferred: &SourcePropertyDiagnostic,
    name: &str,
    private_name: bool,
    context: &ClassAccessContext,
    property: SemanticSymbolId,
    lookup_type: TypeId,
    kind: ClassAccessDiagnosticKind,
    binding: Option<NodeRef>,
) -> Result<CanonicalCheckerDiagnostic, SourcePropertyError> {
    let invalid = || SourcePropertyError::InvalidCache(deferred.name_node);
    if deferred.missing_type.is_some()
        || deferred.private_owner.is_some()
        || deferred.suggestion.is_some()
        || plan_class_access_context(store, host, context.receiver)? != Some(*context)
    {
        return Err(invalid());
    }
    let access = if let Some(binding) = binding {
        let plan = plan_class_binding_property(store, host, binding, context.receiver)?;
        if plan.property != deferred.name_node
            || plan.name != name
            || plan.context != *context
            || private_name
        {
            return Err(invalid());
        }
        binding
    } else {
        let name_record = class_access_node(store, host, deferred.name_node)?;
        let access = NodeRef::new(
            context.receiver.arena,
            context.receiver.file,
            name_record.parent.ok_or_else(invalid)?,
        );
        let NodeData::PropertyAccessExpression(access_data) =
            &class_access_node(store, host, access)?.data
        else {
            return Err(invalid());
        };
        if access_data.expression != context.receiver.node
            || access_data.name != deferred.name_node.node
        {
            return Err(invalid());
        }
        access
    };
    let member = classes::class_member_source(store, host, property).map_err(|_| invalid())?;
    let record = store.symbol(property).ok_or_else(invalid)?;
    let structured = store
        .type_payload(lookup_type)
        .and_then(|record| record.data().structured())
        .ok_or_else(invalid)?;
    if record.parent() != Some(member.declaring_class)
        || record.value_declaration() != Some(member.declaration)
        || member.side != context.side
        || structured
            .properties
            .as_deref()
            .is_none_or(|properties| !properties.contains(&property))
        || structured
            .members
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(record.name()))
            != Some(property)
    {
        return Err(invalid());
    }
    let privacy = if private_name {
        if classes::authenticated_private_class_symbol_name(store, member.declaring_class, property)
            != Some(name)
        {
            return Err(invalid());
        }
        let (arena, _) = host.source(access).ok_or_else(invalid)?;
        SourcePropertyPrivacy::Private {
            enclosing_class: enclosing_private_source_class(arena, store, access)?,
        }
    } else {
        if record.name().as_utf8() != Some(name) {
            return Err(invalid());
        }
        SourcePropertyPrivacy::Identifier
    };
    match kind {
        ClassAccessDiagnosticKind::UsedBeforeInitialization => {
            if !class_property_used_before_initialization(
                store,
                host,
                context,
                deferred.name_node,
                &member,
            )? {
                return Err(invalid());
            }
        }
        ClassAccessDiagnosticKind::UsedBeforeAssignment(read) => {
            let bound = host.bound_file(access).ok_or_else(invalid)?;
            if !options.intrinsic.strict_null_checks
                || !read.used_before_assignment()
                || read.access() != access
                || store.type_payload(read.type_()).is_none()
                || bound.flow_at(access) != Some(read.flow())
            {
                return Err(invalid());
            }
        }
        _ => {
            if class_accessibility_diagnostic(store, host, context, &member, privacy)? != Some(kind)
            {
                return Err(invalid());
            }
        }
    }
    if kind == ClassAccessDiagnosticKind::UsedBeforeInitialization {
        let NodeData::PropertyDeclaration(property) =
            &class_access_node(store, host, member.declaration)?.data
        else {
            return Err(invalid());
        };
        let declaration_name = NodeRef::new(
            member.declaration.arena,
            member.declaration.file,
            property.name,
        );
        return class_used_before_initialization_diagnostic(
            deferred.name_node,
            declaration_name,
            name,
        );
    }
    let mut arguments = vec![name.to_owned()];
    let code = match kind {
        ClassAccessDiagnosticKind::AbstractProperty => {
            arguments.push(
                store
                    .symbol(member.declaring_class)
                    .and_then(|owner| owner.name().as_utf8())
                    .ok_or_else(invalid)?
                    .to_owned(),
            );
            2715
        }
        ClassAccessDiagnosticKind::AbstractSuper | ClassAccessDiagnosticKind::Private => {
            let declaring_type = store
                .declared_type_links(member.declaring_class)
                .and_then(|links| links.declared_type)
                .ok_or_else(invalid)?;
            let mut flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
            if options.no_error_truncation {
                flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
            }
            arguments.push(type_to_string_with_host_global_types_and_flags(
                store,
                host,
                globals,
                declaring_type,
                flags,
            )?);
            if kind == ClassAccessDiagnosticKind::AbstractSuper {
                2513
            } else {
                2341
            }
        }
        ClassAccessDiagnosticKind::PrivateIdentifier => {
            arguments.push(
                store
                    .symbol(member.declaring_class)
                    .and_then(|owner| owner.name().as_utf8())
                    .ok_or_else(invalid)?
                    .to_owned(),
            );
            18_013
        }
        ClassAccessDiagnosticKind::SuperField => 2855,
        ClassAccessDiagnosticKind::UsedBeforeInitialization => {
            unreachable!("initialization diagnostic returned earlier")
        }
        ClassAccessDiagnosticKind::UsedBeforeAssignment(_) => 2565,
    };
    Ok(CanonicalCheckerDiagnostic {
        node: Some(deferred.name_node),
        range_override: None,
        diagnostic: Diagnostic::with_arguments(
            message_by_code(code).ok_or(SourcePropertyError::MissingDiagnostic(code))?,
            arguments,
        ),
        related_information: Vec::new(),
    })
}

fn class_used_before_initialization_diagnostic(
    name_node: NodeRef,
    declaration_name: NodeRef,
    name: &str,
) -> Result<CanonicalCheckerDiagnostic, SourcePropertyError> {
    Ok(CanonicalCheckerDiagnostic {
        node: Some(name_node),
        range_override: None,
        diagnostic: Diagnostic::with_arguments(
            message_by_code(2729).ok_or(SourcePropertyError::MissingDiagnostic(2729))?,
            [name],
        ),
        related_information: vec![CanonicalCheckerRelatedInformation {
            node: Some(declaration_name),
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2728).ok_or(SourcePropertyError::MissingDiagnostic(2728))?,
                [name],
            ),
        }],
    })
}

fn unsupported_access(node: NodeRef) -> SourcePropertyError {
    SourcePropertyError::Unsupported(SourcePropertyUnsupported::Access(node))
}

fn preflight_property_links(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<(), SourcePropertyError> {
    if let Some(links) = store.type_node_links(node) {
        let expected = TypeNodeLinks {
            resolved_type: links.resolved_type,
            ..TypeNodeLinks::default()
        };
        if links != &expected
            || links
                .resolved_type
                .is_some_and(|type_| store.type_payload(type_).is_none())
        {
            return Err(SourcePropertyError::InvalidCache(node));
        }
    }
    if let Some(links) = store.symbol_node_links(node)
        && links
            .resolved_symbol
            .is_some_and(|symbol| store.symbol(symbol).is_none())
    {
        return Err(SourcePropertyError::InvalidCache(node));
    }
    Ok(())
}

fn publish_property_links(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    property: Option<SemanticSymbolId>,
    type_: TypeId,
) -> Result<(), SourcePropertyError> {
    validate_property_link_targets(store, node, property, type_)?;
    let expected_type = TypeNodeLinks {
        resolved_type: Some(type_),
        ..TypeNodeLinks::default()
    };
    let expected_symbol = SymbolNodeLinks {
        resolved_symbol: property,
    };
    if property.is_some() && !store.set_symbol_node_links(node, expected_symbol) {
        return Err(SourcePropertyError::InvalidCache(node));
    }
    if !store.set_type_node_links(node, expected_type) {
        return Err(SourcePropertyError::InvalidCache(node));
    }
    Ok(())
}

fn validate_property_link_targets(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    property: Option<SemanticSymbolId>,
    type_: TypeId,
) -> Result<(), SourcePropertyError> {
    let expected_type = TypeNodeLinks {
        resolved_type: Some(type_),
        ..TypeNodeLinks::default()
    };
    let expected_symbol = SymbolNodeLinks {
        resolved_symbol: property,
    };
    if store
        .type_node_links(node)
        .is_some_and(|links| links != &TypeNodeLinks::default() && links != &expected_type)
        || store
            .symbol_node_links(node)
            .is_some_and(|links| links != &SymbolNodeLinks::default() && links != &expected_symbol)
    {
        return Err(SourcePropertyError::InvalidCache(node));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SemanticSymbolId, SymbolData, SymbolFlags,
    };
    use ts_jsnum::Number;
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, DeclaredTypeError,
        IntrinsicBootstrapOptions, ResolvedSignatureState, SignatureLinks,
        instantiate::{InstantiationLimits, instantiate_type_with_session},
        signatures::{ElementFlags, SignatureFlags},
        source::{PlannedExpressionKind, PlannedIdentifierRead, PlannedIdentifierReadKind},
        tuple_types::CanonicalTupleTypeRequest,
        type_nodes::TypeNodeUnavailable,
        types::ObjectFlags,
    };

    fn parsed(text: &str) -> ParseResult {
        let parsed = parse_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn registered_store(parsed: &ParseResult, file: FileId) -> CanonicalTypeMapperStore {
        let mut store = CanonicalTypeMapperStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            })
            .unwrap();
        store
    }

    fn class_body_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/class-body.ts\""),
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
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                strict_property_initialization: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    #[derive(Debug, Eq, PartialEq)]
    struct ClassPropertyCacheState {
        type_count: usize,
        symbol_count: usize,
        signature_count: usize,
        allocations: Vec<usize>,
        links: Vec<(NodeRef, Option<TypeNodeLinks>, Option<SymbolNodeLinks>)>,
    }

    fn class_property_cache_state(
        context: &CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        file: FileId,
    ) -> ClassPropertyCacheState {
        let store = context.store();
        ClassPropertyCacheState {
            type_count: store.type_len(),
            symbol_count: store.symbol_len(),
            signature_count: store.signature_len(),
            allocations: store.checker_link_allocated_lengths().to_vec(),
            links: parsed
                .arena
                .iter()
                .map(|(node, _)| {
                    let node = NodeRef::new(parsed.arena.id(), file, node);
                    (
                        node,
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                    )
                })
                .collect(),
        }
    }

    fn own_class_write_plans(
        context: &CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        host: &DeclaredTypeHost<'_>,
        file: FileId,
    ) -> Vec<OwnClassPropertyWritePlan> {
        let bound = context.file(file).unwrap().1;
        let mut statements = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::ExpressionStatement).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        statements.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
        statements
            .into_iter()
            .map(|statement| {
                let assignment = super::super::assignment::plan_own_class_property_assignment(
                    &parsed.arena,
                    bound,
                    context.store(),
                    host,
                    statement,
                )
                .unwrap()
                .unwrap();
                plan_own_class_property_write(context.store(), host, &assignment).unwrap()
            })
            .collect()
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep source admission, cold-cache replay, and damage restoration together.
    fn own_class_property_writes_resolve_unpublished_receiver_symbols_and_reject_foreign_caches() {
        let parsed = parsed(concat!(
            "class Model { value = 0; } ",
            "const model = new Model(); const other = new Model(); ",
            "model.value = 1; other.value = 2;",
        ));
        let file = FileId::new(202_622);
        let mut context = class_body_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(
                context.options().name_resolution,
            ),
        )
        .unwrap();
        let cold = class_property_cache_state(&context, &parsed, file);
        let plans = own_class_write_plans(&context, &parsed, &host, file);
        assert_eq!(plans.len(), 2);
        assert_ne!(
            plans[0].assignment().receiver_symbol,
            plans[1].assignment().receiver_symbol
        );
        for plan in &plans {
            assert!(
                context
                    .store()
                    .symbol_node_links(plan.assignment().receiver)
                    .is_none()
            );
        }
        assert_eq!(class_property_cache_state(&context, &parsed, file), cold);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let options = context.options();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        for (index, plan) in plans.iter().enumerate() {
            let assignment = plan.assignment();
            let original = context
                .store()
                .symbol_node_links(assignment.receiver)
                .unwrap()
                .clone();
            assert_eq!(original.resolved_symbol, Some(assignment.receiver_symbol));
            let receiver_type = context
                .store()
                .type_node_links(assignment.receiver)
                .unwrap()
                .resolved_type
                .unwrap();
            assert!(
                context
                    .store_mut_for_test()
                    .set_symbol_node_links(assignment.receiver, SymbolNodeLinks::default(),)
            );
            let unpublished = class_property_cache_state(&context, &parsed, file);
            let relations = context.store().relation_state_snapshot();
            for _ in 0..2 {
                let checked = validate_own_class_property_write_target(
                    context.store(),
                    &host,
                    options,
                    plan,
                    receiver_type,
                )
                .unwrap();
                assert_eq!(checked.type_, number);
                assert!(checked.diagnostic.is_none());
                assert_eq!(
                    class_property_cache_state(&context, &parsed, file),
                    unpublished
                );
                assert_eq!(context.store().relation_state_snapshot(), relations);
            }
            assert!(context.store_mut_for_test().set_symbol_node_links(
                assignment.receiver,
                SymbolNodeLinks {
                    resolved_symbol: Some(plans[1 - index].assignment().receiver_symbol)
                },
            ));
            let poisoned = class_property_cache_state(&context, &parsed, file);
            for _ in 0..2 {
                assert!(matches!(
                    validate_own_class_property_write_target(context.store(), &host, options, plan, receiver_type),
                    Err(SourcePropertyError::InvalidCache(node)) if node == assignment.left
                ));
                assert_eq!(
                    class_property_cache_state(&context, &parsed, file),
                    poisoned
                );
                assert_eq!(context.store().relation_state_snapshot(), relations);
            }
            assert!(
                context
                    .store_mut_for_test()
                    .set_symbol_node_links(assignment.receiver, original)
            );
            let restored = class_property_cache_state(&context, &parsed, file);
            assert_eq!(
                validate_own_class_property_write_target(
                    context.store(),
                    &host,
                    options,
                    plan,
                    receiver_type,
                )
                .unwrap()
                .type_,
                number
            );
            assert_eq!(
                class_property_cache_state(&context, &parsed, file),
                restored
            );
        }
        let warm = class_property_cache_state(&context, &parsed, file);
        context.recheck_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        assert_eq!(class_property_cache_state(&context, &parsed, file), warm);
    }

    #[test]
    fn own_class_property_writes_plan_readonly_fields_before_class_publication() {
        let parsed = parsed(concat!(
            "class Model { readonly value: string = ''; static readonly value: string = ''; } ",
            "const model = new Model(); model.value = 1; Model.value = 1;",
        ));
        let file = FileId::new(202_611);
        let mut context = class_body_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(
                context.options().name_resolution,
            ),
        )
        .unwrap();
        let cold = class_property_cache_state(&context, &parsed, file);
        let plans = own_class_write_plans(&context, &parsed, &host, file);
        assert_eq!(plans.len(), 2);
        for plan in &plans {
            assert!(plan.member.readonly);
            assert_eq!(
                context
                    .store()
                    .symbol(plan.member.symbol)
                    .unwrap()
                    .check_flags(),
                CheckFlags::NONE,
            );
            assert!(
                context
                    .store()
                    .value_symbol_links(plan.member.symbol)
                    .is_none()
            );
        }
        assert_eq!(class_property_cache_state(&context, &parsed, file), cold);
        context.check_source_file(file).unwrap();
        assert_eq!(context.diagnostics().len(), 2);
        for (diagnostic, plan) in context.diagnostics().as_slice().iter().zip(&plans) {
            assert_eq!(diagnostic.node, Some(plan.property.name_node));
            assert_eq!(diagnostic.diagnostic.code(), 2540);
        }
        assert_eq!(own_class_write_plans(&context, &parsed, &host, file), plans);
        let warm = class_property_cache_state(&context, &parsed, file);
        let diagnostics = context.diagnostics().clone();
        context.recheck_source_file(file).unwrap();
        assert_eq!(class_property_cache_state(&context, &parsed, file), warm);
        assert_eq!(context.diagnostics(), &diagnostics);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Poison each actual published cache, then restore the same source.
    fn own_class_property_writes_reject_changed_target_and_receiver_caches() {
        let parsed = parsed(concat!(
            "class Model { value = 0; static value = 0; } ",
            "const model = new Model(); model.value = 1; Model.value = 1;",
        ));
        let file = FileId::new(202_612);
        let mut context = class_body_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(
                context.options().name_resolution,
            ),
        )
        .unwrap();
        let plans = own_class_write_plans(&context, &parsed, &host, file);
        assert_eq!(plans.len(), 2);
        let options = context.options();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        for (index, plan) in plans.iter().enumerate() {
            let assignment = plan.assignment();
            let left_type = context
                .store()
                .type_node_links(assignment.left)
                .unwrap()
                .clone();
            let left_symbol = context
                .store()
                .symbol_node_links(assignment.left)
                .unwrap()
                .clone();
            let receiver = context
                .store()
                .type_node_links(assignment.receiver)
                .unwrap()
                .clone();
            let receiver_type = receiver.resolved_type.unwrap();
            let field = context
                .store()
                .value_symbol_links(plan.member.symbol)
                .unwrap()
                .clone();
            for corruption in 0..4 {
                match corruption {
                    0 => assert!(context.store_mut_for_test().set_type_node_links(
                        assignment.left,
                        TypeNodeLinks {
                            resolved_type: Some(string),
                            ..left_type.clone()
                        },
                    )),
                    1 => assert!(context.store_mut_for_test().set_type_node_links(
                        assignment.receiver,
                        TypeNodeLinks {
                            resolved_type: Some(string),
                            ..receiver.clone()
                        },
                    )),
                    2 => assert!(context.store_mut_for_test().set_symbol_node_links(
                        assignment.left,
                        SymbolNodeLinks {
                            resolved_symbol: Some(plans[1 - index].member.symbol)
                        },
                    )),
                    3 => assert!(context.store_mut_for_test().set_value_symbol_links(
                        plan.member.symbol,
                        ValueSymbolLinks {
                            resolved_type: Some(string),
                            ..field.clone()
                        },
                    )),
                    _ => unreachable!(),
                }
                let before = class_property_cache_state(&context, &parsed, file);
                let field_before = context
                    .store()
                    .value_symbol_links(plan.member.symbol)
                    .cloned();
                let relations = context.store().relation_state_snapshot();
                for _ in 0..2 {
                    assert!(matches!(
                        check_own_class_property_write_target(
                            context.store_mut_for_test(), &host, options, plan, receiver_type,
                        ),
                        Err(SourcePropertyError::InvalidCache(node)) if node == assignment.left
                    ));
                    assert_eq!(class_property_cache_state(&context, &parsed, file), before);
                    assert_eq!(
                        context.store().value_symbol_links(plan.member.symbol),
                        field_before.as_ref()
                    );
                    assert_eq!(context.store().relation_state_snapshot(), relations);
                    assert!(context.diagnostics().is_empty());
                }
                assert!(
                    context
                        .store_mut_for_test()
                        .set_type_node_links(assignment.left, left_type.clone())
                );
                assert!(
                    context
                        .store_mut_for_test()
                        .set_symbol_node_links(assignment.left, left_symbol.clone())
                );
                assert!(
                    context
                        .store_mut_for_test()
                        .set_type_node_links(assignment.receiver, receiver.clone())
                );
                assert!(
                    context
                        .store_mut_for_test()
                        .set_value_symbol_links(plan.member.symbol, field.clone())
                );
                let restored = class_property_cache_state(&context, &parsed, file);
                let checked = check_own_class_property_write_target(
                    context.store_mut_for_test(),
                    &host,
                    options,
                    plan,
                    receiver_type,
                )
                .unwrap();
                assert_eq!(checked.type_, number);
                assert!(checked.diagnostic.is_none());
                assert_eq!(
                    class_property_cache_state(&context, &parsed, file),
                    restored
                );
            }
        }
    }

    #[test]
    fn own_class_property_writes_keep_source_owner_and_side_proofs() {
        let parsed = parsed(concat!(
            "class First { value = 0; static value = 0; } ",
            "class Second { value = 0; static value = 0; } ",
            "declare const first: First; declare const second: Second; ",
            "first.value = 1; First.value = 1; second.value = 1;",
        ));
        let file = FileId::new(202_613);
        let mut context = class_body_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(
                context.options().name_resolution,
            ),
        )
        .unwrap();
        let plans = own_class_write_plans(&context, &parsed, &host, file);
        assert_eq!(plans.len(), 3);
        let options = context.options();
        let original = &plans[0];
        let receiver = context
            .store()
            .type_node_links(original.assignment.receiver)
            .unwrap()
            .resolved_type
            .unwrap();
        for corruption in 0..3 {
            let mut forged = original.clone();
            match corruption {
                0 => forged.assignment.class_symbol = plans[2].assignment.class_symbol,
                1 => forged.member = plans[2].member.clone(),
                2 => forged.assignment.side = ClassPropertySide::Static,
                _ => unreachable!(),
            }
            let before = class_property_cache_state(&context, &parsed, file);
            for _ in 0..2 {
                assert!(matches!(
                    check_own_class_property_write_target(context.store_mut_for_test(), &host, options, &forged, receiver),
                    Err(SourcePropertyError::InvalidCache(node)) if node == original.assignment.left
                ));
                assert_eq!(class_property_cache_state(&context, &parsed, file), before);
                assert!(context.diagnostics().is_empty());
            }
        }
        let before = class_property_cache_state(&context, &parsed, file);
        check_own_class_property_write_target(
            context.store_mut_for_test(),
            &host,
            options,
            original,
            receiver,
        )
        .unwrap();
        assert_eq!(class_property_cache_state(&context, &parsed, file), before);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep all damaged owner states beside their restore checks.
    fn own_class_property_writes_reject_changed_field_kind_and_member_table() {
        let parsed =
            parsed("class Model { value = 0; } const model = new Model(); model.value = 1;");
        let file = FileId::new(202_614);
        let mut context = class_body_context(&parsed, file);
        context.check_source_file(file).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(
                context.options().name_resolution,
            ),
        )
        .unwrap();
        let plans = own_class_write_plans(&context, &parsed, &host, file);
        let [plan] = plans.as_slice() else {
            panic!("one actual write")
        };
        let owner = context
            .store()
            .symbol(plan.assignment.class_symbol)
            .unwrap();
        let relationships = (
            owner.members(),
            owner.exports(),
            owner.parent(),
            owner.export_symbol(),
        );
        let empty = context.store_mut_for_test().alloc_symbol_table();
        let receiver = context
            .store()
            .type_node_links(plan.assignment.receiver)
            .unwrap()
            .resolved_type
            .unwrap();
        let options = context.options();
        for corruption in 0..3 {
            match corruption {
                0 | 1 => assert!(context.store_mut_for_test().set_symbol_flags(
                    plan.member.symbol,
                    if corruption == 0 {
                        SymbolFlags::METHOD
                    } else {
                        SymbolFlags::GET_ACCESSOR
                    },
                    CheckFlags::NONE,
                )),
                2 => assert!(context.store_mut_for_test().set_symbol_relationships(
                    plan.assignment.class_symbol,
                    Some(empty),
                    relationships.1,
                    relationships.2,
                    relationships.3,
                )),
                _ => unreachable!(),
            }
            let before = class_property_cache_state(&context, &parsed, file);
            for _ in 0..2 {
                assert!(matches!(
                    check_own_class_property_write_target(context.store_mut_for_test(), &host, options, plan, receiver),
                    Err(SourcePropertyError::InvalidCache(node)) if node == plan.assignment.left
                ));
                assert_eq!(class_property_cache_state(&context, &parsed, file), before);
                assert!(context.diagnostics().is_empty());
            }
            assert!(context.store_mut_for_test().set_symbol_flags(
                plan.member.symbol,
                SymbolFlags::PROPERTY,
                CheckFlags::NONE
            ));
            assert!(context.store_mut_for_test().set_symbol_relationships(
                plan.assignment.class_symbol,
                relationships.0,
                relationships.1,
                relationships.2,
                relationships.3,
            ));
            let restored = class_property_cache_state(&context, &parsed, file);
            check_own_class_property_write_target(
                context.store_mut_for_test(),
                &host,
                options,
                plan,
                receiver,
            )
            .unwrap();
            assert_eq!(
                class_property_cache_state(&context, &parsed, file),
                restored
            );
        }
    }

    fn source_property_context<'arena>(
        files: &[(FileId, &'arena ParseResult)],
        declaration_count: usize,
    ) -> CanonicalCheckerContext<'arena> {
        let mut binder = CanonicalBinder::new();
        for (index, &(file, source)) in files.iter().enumerate() {
            binder
                .bind_source_file_with_facts(
                    &source.arena,
                    source.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!(
                            "\"/project/cold-merged-property-{index}.ts\""
                        )),
                        CanonicalSourceLanguage::TypeScript,
                        index < declaration_count,
                        index == 0,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for &(file, source) in files {
            binder
                .bind_typescript_declaration_slice(&source.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .iter()
                .map(|(file, source)| (*file, &source.arena))
                .collect(),
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
    #[allow(clippy::too_many_lines)] // Check the same getter through its original and derived receivers.
    fn object_literal_getter_reads_keep_caller_array_targets_and_session() {
        use crate::semantic::instantiate::{
            InstantiationLimits, instantiate_type_with_vector_and_session,
        };

        let library = parsed("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parsed(concat!(
            "declare const captured: number[]; ",
            "const box = { get value() { return captured; }, eager: 1 }; ",
            "const selected = box.value;",
        ));
        let file = FileId::new(202_210);
        let files = [(FileId::new(202_209), &library), (file, &source)];
        let mut context = source_property_context(&files, 1);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let object = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ObjectLiteralExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let getter = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::GetAccessor).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let raw = context.file(file).unwrap().1.symbol(getter).unwrap();
        let original = context
            .store()
            .type_node_links(object)
            .unwrap()
            .resolved_type
            .unwrap();
        let globals = context.global_types().clone();
        let read_type = context
            .store()
            .value_symbol_links(raw)
            .unwrap()
            .resolved_type
            .unwrap();
        let selected = property_access(&source, file);
        assert_eq!(
            context
                .store()
                .symbol_node_links(selected)
                .unwrap()
                .resolved_symbol,
            Some(raw)
        );
        assert_eq!(
            context
                .store()
                .type_node_links(selected)
                .unwrap()
                .resolved_type,
            Some(read_type)
        );
        let regular = context
            .store_mut_for_test()
            .get_regular_type_of_object_literal(original)
            .unwrap();
        let widened = context
            .store_mut_for_test()
            .get_widened_type_with_global_types(original, &globals)
            .unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let error = context.store().intrinsic_bootstrap().unwrap().error_type;
        let TypeData::Interface(array) = context
            .store()
            .type_payload(globals.array_type)
            .unwrap()
            .data()
        else {
            unreachable!();
        };
        let parameter = array.reference.resolved_type_arguments.as_ref().unwrap()[0];
        let mut session = InstantiationSession::new_recovering(
            context.store(),
            InstantiationLimits {
                max_depth: 100,
                max_count: 1,
            },
            error,
        )
        .unwrap();
        for expected in [number, error] {
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    context.store_mut_for_test(),
                    parameter,
                    &[parameter],
                    &[number],
                    Some(CanonicalArrayTargets::from_global_types(&globals)),
                    &mut session,
                ),
                Ok(expected)
            );
        }
        assert_eq!(session.query_count(), 1);
        assert_eq!(session.limit_event_count(), 1);
        let session_before = (
            session.query_count(),
            session.total_count(),
            session.limit_event_mark(),
        );
        let before = class_property_cache_state(&context, &source, file);
        let mut wrong_globals = globals.clone();
        wrong_globals.array_type = globals.readonly_array_type;
        for receiver in [original, regular, widened] {
            assert_eq!(
                resolve_direct_source_own_property(
                    context.store_mut_for_test(),
                    Some(&globals),
                    receiver,
                    "value",
                    &mut session,
                ),
                Ok(Some(ResolvedOwnProperty {
                    symbol: raw,
                    type_: read_type,
                    readonly: true,
                    optional: false,
                }))
            );
            assert!(
                resolve_direct_source_own_property(
                    context.store_mut_for_test(),
                    None,
                    receiver,
                    "value",
                    &mut session,
                )
                .is_err()
            );
            assert!(
                resolve_direct_source_own_property(
                    context.store_mut_for_test(),
                    Some(&wrong_globals),
                    receiver,
                    "value",
                    &mut session,
                )
                .is_err()
            );
            assert_eq!(class_property_cache_state(&context, &source, file), before);
            assert_eq!(
                (
                    session.query_count(),
                    session.total_count(),
                    session.limit_event_mark()
                ),
                session_before
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep cold, warm, and poisoned reads in one source fixture.
    fn cold_merged_interface_property_reads_leave_siblings_unresolved() {
        let library = parsed(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Packet { value: number; }",
        ));
        let added = parsed("interface Packet { unused: Missing; }");
        let consumer =
            parsed("declare const packet: Packet; const selected: number = packet.value;");
        let consumer_file = FileId::new(28_612);
        let files = [
            (FileId::new(28_610), &library),
            (FileId::new(28_611), &added),
            (consumer_file, &consumer),
        ];
        let mut context = source_property_context(&files, 2);
        let (owner, selected, sibling, sibling_annotation) = {
            let store = context.store();
            let owner = store
                .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                .unwrap()
                .get_source("Packet")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            assert_eq!(
                store.symbol(owner).unwrap().declarations().unwrap().len(),
                2
            );
            let members = store
                .symbol_table(store.symbol(owner).unwrap().members().unwrap())
                .unwrap();
            let selected = members.get_source("value").unwrap();
            let sibling = members.get_source("unused").unwrap();
            let sibling_annotation = store
                .source_direct_type_annotation(
                    store.symbol(sibling).unwrap().value_declaration().unwrap(),
                )
                .unwrap();
            assert!(store.value_symbol_links(selected).is_none());
            assert!(store.value_symbol_links(sibling).is_none());
            assert!(store.type_node_links(sibling_annotation).is_none());
            (owner, selected, sibling, sibling_annotation)
        };
        let receiver = context.get_declared_type_of_symbol(owner).unwrap();
        let record = context.store().type_payload(receiver).unwrap();
        assert!(
            !record
                .object_flags()
                .intersects(ObjectFlags::REFERENCE | ObjectFlags::CLASS)
        );
        let TypeData::Interface(interface) = record.data() else {
            panic!("Packet must retain its direct interface type")
        };
        assert!(!interface.declared_members_resolved);
        assert!(interface.declared_members.is_none());
        let access = property_access(&consumer, consumer_file);
        context.check_source_file(consumer_file).unwrap();
        assert!(context.diagnostics().is_empty());
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            context
                .store()
                .type_node_links(access)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .unwrap()
                .resolved_symbol,
            Some(selected)
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(selected)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        assert!(context.store().value_symbol_links(sibling).is_none());
        assert!(
            context
                .store()
                .type_node_links(sibling_annotation)
                .is_none()
        );
        let TypeData::Interface(interface) = context.store().type_payload(receiver).unwrap().data()
        else {
            unreachable!()
        };
        assert!(!interface.declared_members_resolved);
        assert!(interface.declared_members.is_none());
        assert_eq!(
            interface.reference.object.structured,
            StructuredTypeData::default()
        );

        let state = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            let record = store.type_payload(receiver).unwrap();
            let TypeData::Interface(interface) = record.data() else {
                unreachable!()
            };
            (
                (
                    store.type_len(),
                    store.type_alias_len(),
                    store.mapper_len(),
                    store.signature_len(),
                    store.index_info_len(),
                    store.symbol_len(),
                    store.symbol_store().symbol_table_len(),
                    store.checker_link_allocated_lengths(),
                ),
                files
                    .iter()
                    .flat_map(|(file, source)| {
                        source.arena.iter().map(move |(node, _)| {
                            let node = NodeRef::new(source.arena.id(), *file, node);
                            (
                                node,
                                store.type_node_links(node).cloned(),
                                store.symbol_node_links(node).cloned(),
                            )
                        })
                    })
                    .collect::<Vec<_>>(),
                [selected, sibling].map(|symbol| {
                    (
                        store.value_symbol_links(symbol).cloned(),
                        store.declared_value_provenance(symbol),
                    )
                }),
                (record.flags(), record.object_flags(), interface.clone()),
            )
        };
        let warm = state(&context);
        for _ in 0..2 {
            context.recheck_source_file(consumer_file).unwrap();
            assert_eq!(
                context.get_declared_type_of_symbol(owner).unwrap(),
                receiver
            );
            assert_eq!(state(&context), warm);
            assert!(context.diagnostics().is_empty());
        }

        let mut poisoned = context
            .store()
            .value_symbol_links(selected)
            .unwrap()
            .clone();
        poisoned.resolved_type = Some(context.store().intrinsic_bootstrap().unwrap().string_type);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(selected, poisoned)
        );
        let before = state(&context);
        for _ in 0..2 {
            assert_eq!(
                context.recheck_source_file(consumer_file),
                Err(SourceCheckError::DeclaredType(
                    DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::InvalidCachedUnionType(receiver)
                    )
                ))
            );
            assert_eq!(state(&context), before);
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check lazy own lookup before full inherited-member resolution.
    fn cold_merged_interface_inherited_reads_preserve_selected_own_properties() {
        use crate::semantic::declared_values::{
            SelectedDeclaredProperty, selected_declared_property,
        };

        let library = parsed(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Packet extends Base { value: number; unread: string; }",
        ));
        let added = parsed(concat!(
            "interface Base { inherited: boolean; } ",
            "interface Packet { added: string; }",
        ));
        let own_source =
            parsed("declare const packet: Packet; const value: number = packet.value;");
        let inherited_source = parsed("const inherited: boolean = packet.inherited;");
        let own_file = FileId::new(28_622);
        let inherited_file = FileId::new(28_623);
        let files = [
            (FileId::new(28_620), &library),
            (FileId::new(28_621), &added),
            (own_file, &own_source),
            (inherited_file, &inherited_source),
        ];
        let mut context = source_property_context(&files, 2);
        let (owner, selected, unread, added_member, inherited, unread_annotation) = {
            let store = context.store();
            let globals = store
                .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                .unwrap();
            let [owner, base] = ["Packet", "Base"].map(|name| {
                store
                    .get_merged_symbol(globals.get_source(name).unwrap())
                    .unwrap()
            });
            let members = store
                .symbol_table(store.symbol(owner).unwrap().members().unwrap())
                .unwrap();
            assert_eq!(
                store.symbol(owner).unwrap().declarations().unwrap().len(),
                2
            );
            assert!(members.get_source("inherited").is_none());
            let [selected, unread, added_member] =
                ["value", "unread", "added"].map(|name| members.get_source(name).unwrap());
            let inherited = store
                .symbol_table(store.symbol(base).unwrap().members().unwrap())
                .unwrap()
                .get_source("inherited")
                .unwrap();
            let unread_annotation = store
                .source_direct_type_annotation(
                    store.symbol(unread).unwrap().value_declaration().unwrap(),
                )
                .unwrap();
            for symbol in [selected, unread, added_member, inherited] {
                assert!(store.value_symbol_links(symbol).is_none());
            }
            (
                owner,
                selected,
                unread,
                added_member,
                inherited,
                unread_annotation,
            )
        };
        let receiver = context.get_declared_type_of_symbol(owner).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
        context.check_source_file(own_file).unwrap();
        let selected_links = context
            .store()
            .value_symbol_links(selected)
            .unwrap()
            .clone();
        let selected_provenance = context.store().declared_value_provenance(selected).unwrap();
        let Some(SelectedDeclaredProperty::Resolved(property)) =
            selected_declared_property(context.store(), receiver, EscapedNameRef::source("value"))
                .unwrap()
        else {
            panic!("the cold interface must retain its selected own property")
        };
        assert_eq!(property.symbol, selected);
        assert_eq!(property.type_, number);
        assert!(matches!(
            selected_declared_property(
                context.store(),
                receiver,
                EscapedNameRef::source("inherited")
            ),
            Ok(None)
        ));
        assert!(context.store().value_symbol_links(unread).is_none());
        assert!(context.store().type_node_links(unread_annotation).is_none());
        assert!(context.store().value_symbol_links(inherited).is_none());
        assert!(context.diagnostics().is_empty());
        let state = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            let record = store.type_payload(receiver).unwrap();
            let TypeData::Interface(interface) = record.data() else {
                panic!("Packet must retain its interface identity")
            };
            (
                files
                    .iter()
                    .map(|(file, source)| class_property_cache_state(context, source, *file))
                    .collect::<Vec<_>>(),
                (
                    store.type_alias_len(),
                    store.mapper_len(),
                    store.index_info_len(),
                    store.symbol_store().symbol_table_len(),
                ),
                [selected, unread, added_member, inherited].map(|symbol| {
                    (
                        store.value_symbol_links(symbol).cloned(),
                        store.declared_value_provenance(symbol),
                    )
                }),
                (record.flags(), record.object_flags(), interface.clone()),
                files
                    .iter()
                    .map(|(file, _)| {
                        store
                            .source_file_links(context.source_file(*file).unwrap())
                            .cloned()
                    })
                    .collect::<Vec<_>>(),
            )
        };
        let own_warm = state(&context);
        let mut poisoned = selected_links.clone();
        poisoned.resolved_type = Some(context.store().intrinsic_bootstrap().unwrap().string_type);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(selected, poisoned)
        );
        let before = state(&context);
        for _ in 0..2 {
            assert_eq!(
                selected_declared_property(
                    context.store(),
                    receiver,
                    EscapedNameRef::source("value")
                )
                .map(|_| ()),
                Err(RelationUnavailable::InvalidStructuredMembers(receiver))
            );
            assert_eq!(state(&context), before);
            assert!(context.diagnostics().is_empty());
        }
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(selected, selected_links.clone())
        );
        context.recheck_source_file(own_file).unwrap();
        assert_eq!(state(&context), own_warm);

        let own_access = property_access(&own_source, own_file);
        let syntax =
            plan_direct_source_property_syntax(&own_source.arena, context.store(), own_access)
                .unwrap();
        let packet = context
            .store()
            .symbol_table(context.store().intrinsic_bootstrap().unwrap().globals)
            .unwrap()
            .get_source("packet")
            .and_then(|symbol| context.store().get_merged_symbol(symbol))
            .unwrap();
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, packet))
                .unwrap();
        let bound = files
            .iter()
            .map(|(file, _)| context.file(*file).unwrap().1.clone())
            .collect::<Vec<_>>();
        let globals = context.global_types().clone();
        let options = context.options();
        let host = DeclaredTypeHost::new_after_global_merge(
            files
                .iter()
                .zip(&bound)
                .map(|((_, source), bound)| (&source.arena, bound)),
            crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let mut session = InstantiationSession::new_recovering(
            context.store(),
            crate::semantic::instantiate::InstantiationLimits::default(),
            context.store().intrinsic_bootstrap().unwrap().error_type,
        )
        .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(
            context
                .store_mut_for_test()
                .set_interface_base_resolution(receiver, true, None, None)
        );
        let before = state(&context);
        for _ in 0..2 {
            assert_eq!(
                selected_declared_property(
                    context.store(),
                    receiver,
                    EscapedNameRef::source("value")
                )
                .map(|_| ()),
                Err(RelationUnavailable::InvalidStructuredMembers(receiver))
            );
            assert!(matches!(
                check_direct_source_property_with_source(
                    context.store_mut_for_test(),
                    &host,
                    &globals,
                    options,
                    &plan,
                    receiver,
                    &mut session,
                    &mut diagnostics,
                ),
                Err(SourcePropertyQueryError::Source(SourceCheckError::RelationUnavailable(
                    RelationUnavailable::InvalidStructuredMembers(type_)
                ))) if type_ == receiver
            ));
            assert_eq!(state(&context), before);
            assert!(diagnostics.is_empty());
            assert!(context.diagnostics().is_empty());
        }
        assert!(
            context
                .store_mut_for_test()
                .set_interface_base_resolution(receiver, false, None, None)
        );
        context.recheck_source_file(own_file).unwrap();
        assert_eq!(state(&context), own_warm);

        let access = property_access(&inherited_source, inherited_file);
        let inherited_syntax =
            plan_direct_source_property_syntax(&inherited_source.arena, context.store(), access)
                .unwrap();
        let packet_declaration = context
            .store()
            .symbol(packet)
            .unwrap()
            .value_declaration()
            .unwrap();
        let bound_packet = context
            .file(own_file)
            .unwrap()
            .1
            .symbol(packet_declaration)
            .unwrap();
        assert_eq!(
            context.store().get_merged_symbol(bound_packet),
            Some(packet)
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(packet)
                .and_then(|links| links.resolved_type),
            Some(receiver)
        );
        context.check_source_file(inherited_file).unwrap();
        assert_eq!(
            context.store().type_node_links(access),
            Some(&TypeNodeLinks {
                resolved_type: Some(boolean),
                outer_type_parameters: None,
            })
        );
        assert_eq!(
            context.store().symbol_node_links(access),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(inherited),
            })
        );
        assert!(
            context
                .store()
                .source_file_links(context.source_file(inherited_file).unwrap())
                .is_some_and(|links| links.type_checked)
        );
        assert!(context.diagnostics().is_empty());

        let inherited_plan = finish_direct_source_property_plan(
            &inherited_syntax,
            identifier_receiver(&inherited_syntax, packet),
        )
        .unwrap();
        let read_inherited =
            |context: &mut CanonicalCheckerContext<'_>,
             session: &mut InstantiationSession,
             diagnostics: &mut CanonicalCheckerDiagnostics| {
                let checked = check_direct_source_property_with_source(
                    context.store_mut_for_test(),
                    &host,
                    &globals,
                    options,
                    &inherited_plan,
                    receiver,
                    session,
                    diagnostics,
                )
                .unwrap();
                assert_eq!(checked.type_, boolean);
                assert!(checked.diagnostics.is_empty());
            };
        read_inherited(&mut context, &mut session, &mut diagnostics);
        assert_eq!(
            context
                .store()
                .type_node_links(access)
                .unwrap()
                .resolved_type,
            Some(boolean)
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .unwrap()
                .resolved_symbol,
            Some(inherited)
        );
        assert_eq!(
            context.store().value_symbol_links(selected),
            Some(&selected_links)
        );
        assert_eq!(
            context.store().declared_value_provenance(selected),
            Some(selected_provenance)
        );
        let TypeData::Interface(interface) = context.store().type_payload(receiver).unwrap().data()
        else {
            unreachable!()
        };
        assert!(interface.declared_members_resolved);
        assert!(interface.base_types_resolved);
        let members = context
            .store()
            .symbol_table(interface.reference.object.structured.members.unwrap())
            .unwrap();
        assert_eq!(members.get_source("value"), Some(selected));
        assert_eq!(members.get_source("unread"), Some(unread));
        assert_eq!(members.get_source("inherited"), Some(inherited));
        let warm = state(&context);
        for _ in 0..2 {
            context.recheck_source_file(own_file).unwrap();
            context.recheck_source_file(inherited_file).unwrap();
            read_inherited(&mut context, &mut session, &mut diagnostics);
            assert_eq!(
                context.get_declared_type_of_symbol(owner).unwrap(),
                receiver
            );
            assert_eq!(state(&context), warm);
            assert!(diagnostics.is_empty());
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep lexical cases beside their expected contexts.
    fn class_access_context_authenticates_lexical_receiver_and_initialization_boundaries() {
        for (text, expected) in [
            (
                "class Box { constructor() { this; } }",
                Some((
                    ClassPropertySide::Instance,
                    ClassAccessPhase::Constructor,
                    ClassReceiverKind::This,
                )),
            ),
            (
                "class Box { read() { this; } }",
                Some((
                    ClassPropertySide::Instance,
                    ClassAccessPhase::Method,
                    ClassReceiverKind::This,
                )),
            ),
            (
                "class Box { static read() { this; } }",
                Some((
                    ClassPropertySide::Static,
                    ClassAccessPhase::Method,
                    ClassReceiverKind::This,
                )),
            ),
            (
                "class Box { value = 1; read(input: number = this.value) {} }",
                Some((
                    ClassPropertySide::Instance,
                    ClassAccessPhase::Method,
                    ClassReceiverKind::This,
                )),
            ),
            (
                "class Box { static value = 1; static read(input: number = this.value) {} }",
                Some((
                    ClassPropertySide::Static,
                    ClassAccessPhase::Method,
                    ClassReceiverKind::This,
                )),
            ),
            (
                "class Box { value = 1; constructor(input: number = this.value) {} }",
                Some((
                    ClassPropertySide::Instance,
                    ClassAccessPhase::Constructor,
                    ClassReceiverKind::This,
                )),
            ),
            (
                "class Box { read() { function own(input: number = this.value) {} } }",
                None,
            ),
            (
                "class Box { static { this; } }",
                Some((
                    ClassPropertySide::Static,
                    ClassAccessPhase::StaticBlock,
                    ClassReceiverKind::This,
                )),
            ),
            (
                "class Box { value = this; }",
                Some((
                    ClassPropertySide::Instance,
                    ClassAccessPhase::PropertyInitializer,
                    ClassReceiverKind::This,
                )),
            ),
            (
                "class Box { static value = this; }",
                Some((
                    ClassPropertySide::Static,
                    ClassAccessPhase::PropertyInitializer,
                    ClassReceiverKind::This,
                )),
            ),
            (
                "class Box { constructor() { const later = () => this; } }",
                Some((
                    ClassPropertySide::Instance,
                    ClassAccessPhase::Deferred,
                    ClassReceiverKind::This,
                )),
            ),
            (
                "class Box { value = () => this; }",
                Some((
                    ClassPropertySide::Instance,
                    ClassAccessPhase::Deferred,
                    ClassReceiverKind::This,
                )),
            ),
            (
                "class Box { read() { function local() { return this; } } }",
                None,
            ),
            (
                "class Box { read() { const local = { read() { return this; } }; } }",
                None,
            ),
            (
                "class Base {} class Box extends Base { constructor() { super(); } }",
                Some((
                    ClassPropertySide::Instance,
                    ClassAccessPhase::Constructor,
                    ClassReceiverKind::SuperCall,
                )),
            ),
            (
                "class Base {} class Box extends Base { read() { super.value; } }",
                Some((
                    ClassPropertySide::Instance,
                    ClassAccessPhase::Method,
                    ClassReceiverKind::SuperProperty,
                )),
            ),
            (
                "class Base {} class Box extends Base { static read() { super.value; } }",
                Some((
                    ClassPropertySide::Static,
                    ClassAccessPhase::Method,
                    ClassReceiverKind::SuperProperty,
                )),
            ),
        ] {
            let parsed = parsed(text);
            let file = FileId::new(25_132);
            let context = class_body_context(&parsed, file);
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let receiver = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(
                        record.kind,
                        SyntaxKind::ThisKeyword | SyntaxKind::SuperKeyword
                    )
                    .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
            let before = class_property_cache_state(&context, &parsed, file);
            let actual = plan_class_access_context(context.store(), &host, receiver).unwrap();
            assert_eq!(
                actual.map(|context| (context.side, context.phase, context.kind)),
                expected,
                "{text}"
            );
            if let Some(access) = actual {
                assert_eq!(access.receiver(), receiver);
                assert!(host.symbol_matches(
                    context.store(),
                    access.class_declaration(),
                    access.class_symbol()
                ));
                assert_eq!(
                    host.node(access.body_declaration()).unwrap().parent,
                    Some(access.class_declaration().node)
                );
                assert_eq!(
                    plan_class_access_context(context.store(), &host, receiver),
                    Ok(Some(access))
                );
            }
            assert_eq!(class_property_cache_state(&context, &parsed, file), before);
        }
    }

    #[test]
    fn class_access_context_keeps_parameter_defaults_separate_from_invalid_member_locations() {
        for text in [
            "class Box { [this.value]() {} }",
            "class Base {} class Box extends Base { constructor(value = super()) {} }",
            "class Base {} class Box extends Base { constructor() { const run = () => super(); } }",
        ] {
            let parsed = parsed(text);
            let file = FileId::new(25_140);
            let context = class_body_context(&parsed, file);
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let receiver = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(
                        record.kind,
                        SyntaxKind::ThisKeyword | SyntaxKind::SuperKeyword
                    )
                    .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
            let before = class_property_cache_state(&context, &parsed, file);
            assert!(
                plan_class_access_context(context.store(), &host, receiver).is_err(),
                "{text}"
            );
            assert_eq!(class_property_cache_state(&context, &parsed, file), before);
        }
    }

    #[test]
    fn class_missing_properties_use_the_lookup_type_without_replacing_synthetic_this() {
        for (name, code) in [("missing", 2339), ("valu", 2551)] {
            let parsed = parsed(&format!(
                "class MissingThisProperty {{ value = 1; read() {{ return this.{name}; }} }}"
            ));
            let file = FileId::new(25_141);
            let mut context = class_body_context(&parsed, file);
            context.check_source_file(file).unwrap();
            let access = property_access(&parsed, file);
            let NodeData::PropertyAccessExpression(property) =
                &parsed.arena.get(access.node).unwrap().data
            else {
                unreachable!()
            };
            let receiver = NodeRef::new(parsed.arena.id(), file, property.expression);
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let access_context = plan_class_access_context(context.store(), &host, receiver)
                .unwrap()
                .unwrap();
            let instance = context
                .store()
                .declared_type_links(access_context.class_symbol())
                .unwrap()
                .declared_type
                .unwrap();
            let TypeData::Interface(class) = context.store().type_payload(instance).unwrap().data()
            else {
                unreachable!()
            };
            let synthetic = class.this_type.unwrap();
            assert_ne!(synthetic, instance);
            assert_eq!(
                context
                    .store()
                    .type_node_links(receiver)
                    .unwrap()
                    .resolved_type,
                Some(synthetic)
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(access)
                    .unwrap()
                    .resolved_type,
                Some(context.store().intrinsic_bootstrap().unwrap().error_type)
            );
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("{:?}", context.diagnostics())
            };
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.diagnostic.arguments[0], name);
            assert_eq!(diagnostic.diagnostic.arguments[1], "MissingThisProperty");
            if code == 2551 {
                assert_eq!(diagnostic.diagnostic.arguments[2], "value");
            }
            let diagnostics = context.diagnostics().clone();
            let before = class_property_cache_state(&context, &parsed, file);
            context.recheck_source_file(file).unwrap();
            assert_eq!(context.diagnostics(), &diagnostics);
            assert_eq!(class_property_cache_state(&context, &parsed, file), before);
        }
    }

    #[test]
    fn class_private_fallback_has_pinned_order_in_independent_stores() {
        for _ in 0..8 {
            let parsed = parsed(concat!(
                "class PrivateFirst { #same = 1; } ",
                "class PrivateSecond extends PrivateFirst { #same = 2; } ",
                "class PrivateThird extends PrivateSecond { read() { return this.#same; } }",
            ));
            let file = FileId::new(25_142);
            let mut context = class_body_context(&parsed, file);
            context.check_source_file(file).unwrap();
            let access = property_access(&parsed, file);
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("{:?}", context.diagnostics())
            };
            assert_eq!(diagnostic.diagnostic.code(), 18_013);
            assert_eq!(diagnostic.diagnostic.arguments, ["#same", "PrivateFirst"]);
            assert_eq!(
                context
                    .store()
                    .type_node_links(access)
                    .unwrap()
                    .resolved_type,
                Some(context.store().intrinsic_bootstrap().unwrap().error_type)
            );
            assert!(
                context
                    .store()
                    .symbol_node_links(access)
                    .is_none_or(|links| links.resolved_symbol.is_none())
            );
            let diagnostics = context.diagnostics().clone();
            let before = class_property_cache_state(&context, &parsed, file);
            context.recheck_source_file(file).unwrap();
            assert_eq!(context.diagnostics(), &diagnostics);
            assert_eq!(class_property_cache_state(&context, &parsed, file), before);
        }
    }

    #[test]
    fn constructor_property_writes_reject_cold_target_caches_before_union_creation() {
        let parsed = parsed("class Model { value?: number; constructor() { this.value = 1; } }");
        let file = FileId::new(25_150);
        let mut context = class_body_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(
                context.options().name_resolution,
            ),
        )
        .unwrap();
        let assignment = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(record.data, NodeData::BinaryExpression(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let write = plan_class_property_write(context.store(), &host, assignment).unwrap();
        let class = classes::plan_source_class_members(
            context.store(),
            &host,
            write.context().class_symbol(),
        )
        .unwrap();
        let body = &class.bodies()[0];
        let flow = crate::semantic::source_flow::SourceFlowPlan::preflight_class_body(
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
        let prepared =
            classes::prepare_source_class_members(context.store_mut_for_test(), &host, &class)
                .unwrap();
        let access = prepared.body_access(context.store(), &host, body).unwrap();
        let mut frame = ClassInitializationFrame::new(
            body,
            &flow,
            &bound,
            access.clone(),
            std::collections::HashMap::new(),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let options = context.options();
        let receiver = check_class_receiver(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            write.context(),
            Some(&mut frame),
        )
        .unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let types = [number, bootstrap.undefined_or_missing_type];
        assert_eq!(
            context.store().cached_literal_union_type_with_alias(
                &types,
                None,
                Some(CanonicalArrayTargets::from_global_types(&globals)),
            ),
            Ok(None)
        );
        for corrupt_symbol in [false, true] {
            if corrupt_symbol {
                assert!(context.store_mut_for_test().set_symbol_node_links(
                    write.target(),
                    SymbolNodeLinks {
                        resolved_symbol: Some(write.context().class_symbol()),
                    },
                ));
            } else {
                assert!(context.store_mut_for_test().set_type_node_links(
                    write.target(),
                    TypeNodeLinks {
                        resolved_type: Some(string),
                        ..TypeNodeLinks::default()
                    },
                ));
            }
            let before = class_property_cache_state(&context, &parsed, file);
            for _ in 0..2 {
                assert_eq!(
                    check_class_property_write_target(
                        context.store_mut_for_test(),
                        &host,
                        &globals,
                        options,
                        &write,
                        receiver.type_,
                        &access,
                    ),
                    Err(SourcePropertyError::InvalidCache(write.target()))
                );
                assert_eq!(class_property_cache_state(&context, &parsed, file), before);
            }
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_node_links(write.target(), TypeNodeLinks::default())
            );
            assert!(
                context
                    .store_mut_for_test()
                    .set_symbol_node_links(write.target(), SymbolNodeLinks::default())
            );
        }
        let checked = check_class_property_write_target(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &write,
            receiver.type_,
            &access,
        )
        .unwrap();
        assert_eq!(checked.read_type(), checked.write_type());
        assert_eq!(
            context.type_to_string(checked.read_type()).unwrap(),
            "number | undefined"
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(write.member())
                .unwrap()
                .resolved_type,
            Some(number)
        );
    }

    #[test]
    fn constructor_property_writes_reject_wrong_tokens_and_receiver_caches() {
        let parsed = parsed(concat!(
            "class First { value?: number; constructor() { this.value = 1; } } ",
            "class Second { value?: number; constructor() { this.value = 2; } }",
        ));
        let file = FileId::new(25_151);
        let mut context = class_body_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(
                context.options().name_resolution,
            ),
        )
        .unwrap();
        let mut assignments = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                matches!(record.data, NodeData::BinaryExpression(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        assignments.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
        let write = plan_class_property_write(context.store(), &host, assignments[0]).unwrap();
        let first = classes::plan_source_class_members(
            context.store(),
            &host,
            write.context().class_symbol(),
        )
        .unwrap();
        let prepared =
            classes::prepare_source_class_members(context.store_mut_for_test(), &host, &first)
                .unwrap();
        let access = prepared
            .body_access(context.store(), &host, &first.bodies()[0])
            .unwrap();
        let identities = classes::class_body_identities(context.store(), &host, &access).unwrap();
        let second_write =
            plan_class_property_write(context.store(), &host, assignments[1]).unwrap();
        let second = classes::plan_source_class_members(
            context.store(),
            &host,
            second_write.context().class_symbol(),
        )
        .unwrap();
        let second_prepared =
            classes::prepare_source_class_members(context.store_mut_for_test(), &host, &second)
                .unwrap();
        let wrong_access = second_prepared
            .body_access(context.store(), &host, &second.bodies()[0])
            .unwrap();
        let globals = context.global_types().clone();
        let options = context.options();
        let declared = context.store().value_symbol_links(write.member()).cloned();
        let checked = check_class_property_write_target(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &write,
            identities.this_type,
            &access,
        )
        .unwrap();
        assert_eq!(checked.plan(), &write);
        assert_eq!(checked.access_token(), &access);
        assert_eq!(
            context.type_to_string(checked.read_type()).unwrap(),
            "number | undefined"
        );
        for (token, receiver) in [
            (&wrong_access, identities.this_type),
            (&access, identities.instance_type),
        ] {
            let before = class_property_cache_state(&context, &parsed, file);
            assert!(
                check_class_property_write_target(
                    context.store_mut_for_test(),
                    &host,
                    &globals,
                    options,
                    &write,
                    receiver,
                    token,
                )
                .is_err()
            );
            assert_eq!(class_property_cache_state(&context, &parsed, file), before);
            assert_eq!(
                context.store().value_symbol_links(write.member()),
                declared.as_ref()
            );
        }
        let mut wrong_target = write.clone();
        wrong_target.property.node = second_write.target();
        let before = class_property_cache_state(&context, &parsed, file);
        assert!(matches!(
            check_class_property_write_target(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &wrong_target,
                identities.this_type,
                &access,
            ),
            Err(SourcePropertyError::InvalidCache(node)) if node == second_write.target()
        ));
        assert_eq!(class_property_cache_state(&context, &parsed, file), before);
        assert_eq!(
            context.store().value_symbol_links(write.member()),
            declared.as_ref()
        );
        let original = context
            .store()
            .type_node_links(write.receiver())
            .cloned()
            .unwrap();
        assert!(context.store_mut_for_test().set_type_node_links(
            write.receiver(),
            TypeNodeLinks {
                resolved_type: Some(identities.instance_type),
                ..TypeNodeLinks::default()
            },
        ));
        let poisoned = class_property_cache_state(&context, &parsed, file);
        assert!(
            check_class_property_write_target(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &write,
                identities.this_type,
                &access,
            )
            .is_err()
        );
        assert_eq!(
            class_property_cache_state(&context, &parsed, file),
            poisoned
        );
        assert_eq!(
            context.store().value_symbol_links(write.member()),
            declared.as_ref()
        );
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(write.receiver(), original)
        );
        context.recheck_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn optional_class_property_assignment_keeps_the_real_flow_type() {
        let parsed = parsed(concat!(
            "class OptionalPropertyAfterAssignment { value?: number; constructor() { ",
            "this.value = 1; const result: number = this.value; } }",
        ));
        let file = FileId::new(25_143);
        let mut context = class_body_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let access = parsed.arena.iter().find_map(|(node, record)| {
            let NodeData::PropertyAccessExpression(_) = &record.data else { return None; };
            let parent = parsed.arena.get(record.parent?)?;
            matches!(&parent.data, NodeData::VariableDeclaration(variable) if variable.initializer == Some(node))
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
        }).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            context
                .store()
                .type_node_links(access)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        let symbol = context
            .store()
            .symbol_node_links(access)
            .unwrap()
            .resolved_symbol
            .unwrap();
        let before = class_property_cache_state(&context, &parsed, file);
        context.recheck_source_file(file).unwrap();
        assert_eq!(class_property_cache_state(&context, &parsed, file), before);
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .unwrap()
                .resolved_symbol,
            Some(symbol)
        );
    }

    #[test]
    fn optional_class_property_guards_are_narrowed_or_fail_closed() {
        let parsed = parsed(concat!(
            "class OptionalPropertyAfterNarrowing { value?: number; read() { ",
            "if (this.value !== undefined) { const result: number = this.value; return result; } } }",
        ));
        let file = FileId::new(25_144);
        let mut context = class_body_context(&parsed, file);
        match context.check_source_file(file) {
            Ok(()) => {
                assert!(
                    context.diagnostics().is_empty(),
                    "{:?}",
                    context.diagnostics()
                );
                let access = parsed.arena.iter().find_map(|(node, record)| {
                    let NodeData::PropertyAccessExpression(_) = &record.data else { return None; };
                    let parent = parsed.arena.get(record.parent?)?;
                    matches!(&parent.data, NodeData::VariableDeclaration(variable) if variable.initializer == Some(node))
                        .then_some(NodeRef::new(parsed.arena.id(), file, node))
                }).unwrap();
                assert_eq!(
                    context
                        .store()
                        .type_node_links(access)
                        .unwrap()
                        .resolved_type,
                    Some(context.store().intrinsic_bootstrap().unwrap().number_type)
                );
                let before = class_property_cache_state(&context, &parsed, file);
                context.recheck_source_file(file).unwrap();
                assert_eq!(class_property_cache_state(&context, &parsed, file), before);
            }
            Err(crate::semantic::source::SourceCheckError::Unsupported(_)) => {
                assert!(context.diagnostics().is_empty());
                for (node, record) in parsed.arena.iter() {
                    if record.kind == SyntaxKind::PropertyAccessExpression {
                        let node = NodeRef::new(parsed.arena.id(), file, node);
                        assert!(
                            context
                                .store()
                                .type_node_links(node)
                                .is_none_or(|links| links == &TypeNodeLinks::default())
                        );
                    }
                }
            }
            Err(error) => panic!("guard must be checked or remain unsupported: {error:?}"),
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn class_flow_identity_is_checked_for_real_reads_with_and_without_ts2565() {
        use crate::semantic::source_flow::{SourceFlowPlan, SourceFlowTypes};

        let parsed = parsed(
            "class FlowIdentity { value: number; constructor() { this.value; } read() { this.value; } }",
        );
        let file = FileId::new(25_145);
        let mut context = class_body_context(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let accesses = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::PropertyAccessExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        assert_eq!(accesses.len(), 2);
        let contexts = accesses
            .iter()
            .map(|access| {
                let NodeData::PropertyAccessExpression(property) =
                    &parsed.arena.get(access.node).unwrap().data
                else {
                    unreachable!()
                };
                plan_class_access_context(
                    context.store(),
                    &host,
                    NodeRef::new(parsed.arena.id(), file, property.expression),
                )
                .unwrap()
                .unwrap()
            })
            .collect::<Vec<_>>();
        let class =
            classes::plan_source_class_members(context.store(), &host, contexts[0].class_symbol())
                .unwrap();
        let plans = contexts
            .iter()
            .zip(&accesses)
            .map(|(access_context, access)| {
                let body = class
                    .bodies()
                    .iter()
                    .find(|body| body.declaration == access_context.body_declaration())
                    .unwrap();
                SourceFlowPlan::preflight_class_body(
                    &parsed.arena,
                    &bound,
                    context.store(),
                    &host,
                    body,
                    [*access],
                    [],
                    [],
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let prepared =
            classes::prepare_source_class_members(context.store_mut_for_test(), &host, &class)
                .unwrap();
        let owner = context.store().symbol(class.symbol()).unwrap();
        let member = owner
            .members()
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("value"))
            .unwrap();
        let member = classes::class_member_source(context.store(), &host, member).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let options = context.options();
        assert!(options.strict_property_initialization);
        let mut reads = Vec::new();
        for ((access_context, access), plan) in contexts.iter().zip(&accesses).zip(&plans) {
            let body = class
                .bodies()
                .iter()
                .find(|body| body.declaration == access_context.body_declaration())
                .unwrap();
            let token = prepared.body_access(context.store(), &host, body).unwrap();
            let mut flow =
                ClassInitializationFrame::new(body, plan, &bound, token, SourceFlowTypes::new())
                    .unwrap();
            let read = flow
                .property_read(
                    context.store_mut_for_test(),
                    &host,
                    access_context,
                    *access,
                    &member,
                    number,
                    options,
                )
                .unwrap();
            validate_class_property_flow_read(context.store(), &host, *access, &read).unwrap();
            reads.push(read);
        }
        assert!(reads[0].used_before_assignment());
        assert!(!reads[1].used_before_assignment());
        assert_ne!(reads[0].flow(), reads[1].flow());
        let before = class_property_cache_state(&context, &parsed, file);
        for index in 0..2 {
            let access = reads[index].access();
            assert_eq!(
                validate_class_property_flow_identity(
                    &host,
                    access,
                    access,
                    reads[1 - index].flow()
                ),
                Err(SourcePropertyError::InvalidCache(access))
            );
            assert_eq!(class_property_cache_state(&context, &parsed, file), before);
            assert!(
                context
                    .store()
                    .type_node_links(access)
                    .is_none_or(|links| links == &TypeNodeLinks::default())
            );
            assert!(
                context
                    .store()
                    .symbol_node_links(access)
                    .is_none_or(|links| links == &SymbolNodeLinks::default())
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn static_this_initialization_uses_owned_declarations_and_preserves_related_information() {
        for (source, expected) in [
            (
                "class StaticBeforeInitialization { static first: number; static second = this.first; }",
                Some(true),
            ),
            (
                "class StaticBeforeInitialization { static first!: number; static second = this.first; }",
                Some(false),
            ),
            (
                "class StaticBeforeInitialization { static first?: number; static second = this.first; }",
                Some(false),
            ),
            (
                "class StaticBeforeInitialization { static first = 1; static second = this.first; }",
                Some(false),
            ),
            (
                "class StaticBeforeInitialization { static first: number; static { this.first = 1; } static second = this.first; }",
                None,
            ),
        ] {
            let parsed = parsed(source);
            let file = FileId::new(25_146);
            let mut context = class_body_context(&parsed, file);
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let access = parsed.arena.iter().find_map(|(node, record)| {
                let NodeData::PropertyAccessExpression(_) = &record.data else { return None; };
                let parent = parsed.arena.get(record.parent?)?;
                matches!(&parent.data, NodeData::PropertyDeclaration(field) if field.initializer == Some(node))
                    .then_some(NodeRef::new(parsed.arena.id(), file, node))
            }).unwrap();
            let NodeData::PropertyAccessExpression(property) =
                &parsed.arena.get(access.node).unwrap().data
            else {
                unreachable!()
            };
            let receiver = NodeRef::new(parsed.arena.id(), file, property.expression);
            let name = NodeRef::new(parsed.arena.id(), file, property.name);
            let access_context = plan_class_access_context(context.store(), &host, receiver)
                .unwrap()
                .unwrap();
            let declaration = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::PropertyDeclaration(field) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(field.name)?.data else {
                        return None;
                    };
                    (name.text == "first").then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
            let symbol = bound.symbol(declaration).unwrap();
            context
                .store_mut_for_test()
                .get_declared_type_of_symbol(&host, access_context.class_symbol())
                .unwrap();
            let NodeData::PropertyDeclaration(field) = &host.node(declaration).unwrap().data else {
                unreachable!()
            };
            let record = context.store().symbol(symbol).unwrap();
            // This declaration-only test does not prepare an unsupported field initializer.
            let member = ClassMemberSource {
                symbol,
                declaring_class: record.parent().unwrap(),
                declaration: record.value_declaration().unwrap(),
                origin: ClassMemberOrigin::Field {
                    initializer: field
                        .initializer
                        .map(|node| NodeRef::new(declaration.arena, declaration.file, node)),
                },
                side: class_member_side(
                    context.store(),
                    &host,
                    declaration,
                    field.modifiers.as_ref(),
                )
                .unwrap(),
                visibility: classes::class_member_visibility(context.store(), declaration),
                readonly: record.check_flags().contains(CheckFlags::READONLY),
                abstract_: ts_binder::canonical_has_syntactic_modifier(
                    &parsed.arena,
                    declaration.node,
                    SyntaxKind::AbstractKeyword,
                ),
            };
            assert_eq!(member.side, ClassPropertySide::Static);
            let before = class_property_cache_state(&context, &parsed, file);
            let first = class_property_used_before_initialization(
                context.store(),
                &host,
                &access_context,
                name,
                &member,
            );
            match expected {
                Some(value) => assert_eq!(first, Ok(value), "{source}"),
                None => assert_eq!(first, Err(unsupported_access(name))),
            }
            assert_eq!(
                class_property_used_before_initialization(
                    context.store(),
                    &host,
                    &access_context,
                    name,
                    &member
                ),
                first
            );
            if expected == Some(true) {
                let NodeData::PropertyDeclaration(property) = &host.node(declaration).unwrap().data
                else {
                    panic!("expected a class field declaration");
                };
                let declaration_name =
                    NodeRef::new(declaration.arena, declaration.file, property.name);
                let diagnostic =
                    class_used_before_initialization_diagnostic(name, declaration_name, "first")
                        .unwrap();
                assert_eq!(diagnostic.diagnostic.code(), 2729);
                assert_eq!(diagnostic.node, Some(name));
                assert_eq!(diagnostic.related_information.len(), 1);
                assert_eq!(
                    diagnostic.related_information[0].node,
                    Some(declaration_name)
                );
                assert_eq!(diagnostic.related_information[0].diagnostic.code(), 2728);
                assert_eq!(
                    class_used_before_initialization_diagnostic(name, declaration_name, "first")
                        .unwrap(),
                    diagnostic
                );
            }
            assert_eq!(class_property_cache_state(&context, &parsed, file), before);
            assert!(
                context
                    .store()
                    .type_node_links(access)
                    .is_none_or(|links| links == &TypeNodeLinks::default())
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn class_property_reads_use_real_pending_tokens_and_replay_exact_caches() {
        use crate::semantic::source_flow::{SourceFlowPlan, SourceFlowTypes};

        for (text, expected_code) in [
            (
                "class Box { value = 1; read() { this.value; } other() { this.value; } }",
                None,
            ),
            (
                "class Box { private value = 1; read() { this.value; } }",
                None,
            ),
            ("class Box { #value = 1; read() { this.#value; } }", None),
            (
                "abstract class Box { abstract value: string; constructor() { this.value; } }",
                Some(2715),
            ),
        ] {
            let parsed = parsed(text);
            let file = FileId::new(25_133);
            let mut context = class_body_context(&parsed, file);
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let globals = context.global_types().clone();
            let options = context.options();
            let access = property_access(&parsed, file);
            let syntax =
                plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
            let receiver = plan_class_access_context(context.store(), &host, syntax.receiver())
                .unwrap()
                .unwrap();
            let class =
                classes::plan_source_class_members(context.store(), &host, receiver.class_symbol())
                    .unwrap();
            let body = class
                .bodies()
                .iter()
                .find(|body| body.declaration == receiver.body_declaration())
                .unwrap();
            let flow_plan = SourceFlowPlan::preflight_class_body(
                &parsed.arena,
                &bound,
                context.store(),
                &host,
                body,
                [access],
                [],
                [],
            )
            .unwrap();
            let prepared =
                classes::prepare_source_class_members(context.store_mut_for_test(), &host, &class)
                    .unwrap();
            let token = prepared.body_access(context.store(), &host, body).unwrap();
            let mut flow = ClassInitializationFrame::new(
                body,
                &flow_plan,
                &bound,
                token,
                SourceFlowTypes::new(),
            )
            .unwrap();
            let expression = PlannedExpression::new(
                syntax.receiver(),
                PlannedExpressionKind::ClassReceiver(receiver),
            );
            let mut plan = finish_direct_source_property_plan(&syntax, expression).unwrap();
            attach_class_access_context(context.store(), &host, &mut plan).unwrap();
            let mut warm = None;
            for _ in 0..2 {
                let checked_receiver = check_class_receiver(
                    context.store_mut_for_test(),
                    &host,
                    &globals,
                    options,
                    &receiver,
                    Some(&mut flow),
                )
                .unwrap();
                assert!(checked_receiver.diagnostics.is_empty());
                let checked = check_direct_source_property_with_class_context(
                    context.store_mut_for_test(),
                    &host,
                    Some(&globals),
                    options,
                    &plan,
                    checked_receiver.type_,
                    Some(&mut flow),
                )
                .unwrap();
                let codes = checked
                    .diagnostics
                    .iter()
                    .map(|diagnostic| {
                        prepare_source_property_diagnostic(
                            context.store(),
                            &host,
                            &globals,
                            options,
                            diagnostic,
                        )
                        .unwrap()
                        .diagnostic
                        .code()
                    })
                    .collect::<Vec<_>>();
                assert_eq!(
                    codes,
                    expected_code.into_iter().collect::<Vec<_>>(),
                    "{text}"
                );
                let expected_type = if expected_code.is_some() {
                    context.store().intrinsic_bootstrap().unwrap().string_type
                } else {
                    context.store().intrinsic_bootstrap().unwrap().number_type
                };
                assert_eq!(checked.type_, expected_type);
                let state = class_property_cache_state(&context, &parsed, file);
                if let Some(previous) = &warm {
                    assert_eq!(&state, previous);
                }
                warm = Some(state);
            }
            let before = class_property_cache_state(&context, &parsed, file);
            for forged in [
                ClassAccessContext {
                    side: ClassPropertySide::Static,
                    ..receiver
                },
                ClassAccessContext {
                    body_declaration: receiver.class_declaration,
                    ..receiver
                },
                ClassAccessContext {
                    receiver: access,
                    ..receiver
                },
            ] {
                assert!(
                    check_class_receiver(
                        context.store_mut_for_test(),
                        &host,
                        &globals,
                        options,
                        &forged,
                        Some(&mut flow),
                    )
                    .is_err()
                );
                assert_eq!(class_property_cache_state(&context, &parsed, file), before);
            }
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            assert!(
                check_direct_source_property(
                    context.store_mut_for_test(),
                    Some(&globals),
                    &plan,
                    number
                )
                .is_err()
            );
            assert_eq!(class_property_cache_state(&context, &parsed, file), before);
            if let Some(other_body) = class
                .bodies()
                .iter()
                .find(|body| body.declaration != receiver.body_declaration())
            {
                let other_access = parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        let NodeData::PropertyAccessExpression(property) = &record.data else {
                            return None;
                        };
                        let other_receiver =
                            NodeRef::new(parsed.arena.id(), file, property.expression);
                        let context =
                            plan_class_access_context(context.store(), &host, other_receiver)
                                .ok()??;
                        (context.body_declaration() == other_body.declaration)
                            .then_some(NodeRef::new(parsed.arena.id(), file, node))
                    })
                    .unwrap();
                let other_plan = SourceFlowPlan::preflight_class_body(
                    &parsed.arena,
                    &bound,
                    context.store(),
                    &host,
                    other_body,
                    [other_access],
                    [],
                    [],
                )
                .unwrap();
                let other_token = prepared
                    .body_access(context.store(), &host, other_body)
                    .unwrap();
                let mut other_flow = ClassInitializationFrame::new(
                    other_body,
                    &other_plan,
                    &bound,
                    other_token,
                    SourceFlowTypes::new(),
                )
                .unwrap();
                assert!(
                    check_class_receiver(
                        context.store_mut_for_test(),
                        &host,
                        &globals,
                        options,
                        &receiver,
                        Some(&mut other_flow),
                    )
                    .is_err()
                );
                assert_eq!(class_property_cache_state(&context, &parsed, file), before);
            }
        }
    }

    #[test]
    fn class_super_reads_keep_the_base_method_symbol_and_signature() {
        let parsed = parsed(concat!(
            "class Base { value = 1; read(): number { return this.value; } } ",
            "class Derived extends Base { read(): number { return super.read(); } }",
        ));
        let file = FileId::new(25_134);
        let mut context = class_body_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let (access, call, base_member) = {
            let (access, call) = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::PropertyAccessExpression(property) = &record.data else {
                        return None;
                    };
                    (parsed.arena.get(property.expression)?.kind == SyntaxKind::SuperKeyword)
                        .then_some((
                            NodeRef::new(parsed.arena.id(), file, node),
                            NodeRef::new(parsed.arena.id(), file, record.parent?),
                        ))
                })
                .unwrap();
            let base = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::ClassDeclaration(class) = &record.data else {
                        return None;
                    };
                    class.heritage_clauses.is_none().then_some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        node,
                    ))
                })
                .unwrap();
            let owner = context.file(file).unwrap().1.symbol(base).unwrap();
            let member = context
                .store()
                .symbol(owner)
                .unwrap()
                .members()
                .and_then(|members| context.store().symbol_table(members))
                .and_then(|members| members.get_source("read"))
                .unwrap();
            (access, call, member)
        };
        let method_type = context
            .store()
            .value_symbol_links(base_member)
            .unwrap()
            .resolved_type
            .unwrap();
        let signatures = context
            .store()
            .type_payload(method_type)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap();
        assert_eq!(signatures.len(), 1);
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .unwrap()
                .resolved_symbol,
            Some(base_member)
        );
        assert_eq!(
            context
                .store()
                .type_node_links(access)
                .unwrap()
                .resolved_type,
            Some(method_type)
        );
        assert_eq!(
            context
                .store()
                .signature_links(call)
                .unwrap()
                .resolved_signature,
            ResolvedSignatureState::Resolved(signatures[0])
        );
        let before = class_property_cache_state(&context, &parsed, file);
        context.recheck_source_file(file).unwrap();
        assert_eq!(class_property_cache_state(&context, &parsed, file), before);
    }

    fn property_access(parsed: &ParseResult, file: FileId) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::PropertyAccessExpression)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap()
    }

    fn identifier_receiver(
        syntax: &DirectSourcePropertySyntax,
        symbol: SemanticSymbolId,
    ) -> PlannedExpression {
        PlannedExpression::new(
            syntax.receiver(),
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: symbol,
                value_symbol: symbol,
                kind: PlannedIdentifierReadKind::Variable,
            }),
        )
    }

    fn property_object(
        store: &mut CanonicalTypeMapperStore,
        name: &str,
        type_: TypeId,
        optional: bool,
    ) -> (TypeId, SemanticSymbolId) {
        let flags = SymbolFlags::PROPERTY
            | if optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            };
        let property = store
            .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
            .unwrap();
        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        let members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(members, EscapedName::source(name), property),
            Some(None)
        );
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            Some(members),
            Some(vec![property]),
            None,
            None,
            None,
        ));
        (object, property)
    }

    fn namespace_object(
        store: &mut CanonicalTypeMapperStore,
        name: &str,
        type_: TypeId,
        flags: SymbolFlags,
    ) -> (TypeId, SemanticSymbolId, SemanticSymbolId, SemanticSymbolId) {
        let exports = store.alloc_symbol_table();
        let module = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::VALUE_MODULE,
                EscapedName::source("\"/project/values.ts\""),
            ))
            .unwrap();
        assert!(store.set_symbol_relationships(module, None, Some(exports), None, None));
        let member = store
            .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
            .unwrap();
        assert!(store.set_symbol_relationships(member, None, None, Some(module), None));
        assert!(store.set_value_symbol_links(
            member,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            store.insert_symbol(exports, EscapedName::source(name), member),
            Some(None)
        );
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(module))
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            Some(exports),
            Some(vec![member]),
            None,
            None,
            None,
        ));
        let alias = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::ALIAS,
                EscapedName::source("namespace"),
            ))
            .unwrap();
        assert!(store.set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                immediate_target: Some(module),
                alias_target: AliasTargetState::Resolved(module),
                ..AliasSymbolLinks::default()
            },
        ));
        (object, module, member, alias)
    }

    fn published_enum(
        parsed: &ParseResult,
        file: FileId,
    ) -> (
        CanonicalTypeMapperStore,
        SemanticSymbolId,
        TypeId,
        SemanticSymbolId,
        TypeId,
    ) {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/properties.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let bound = files.get(&file).unwrap();
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::EnumDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .expect("fixture has one enum declaration");
        let owner = bound.symbol(declaration).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();
        let enumeration = enums::get_enum_semantics(&mut store, &host, owner).unwrap();
        let member = enumeration.members[0].clone();
        (
            store,
            owner,
            enumeration.value_type,
            member.symbol,
            member.fresh_type,
        )
    }

    fn published_class<'arena>(
        parsed: &'arena ParseResult,
        file: FileId,
        expected: &str,
    ) -> (
        CanonicalCheckerContext<'arena>,
        SemanticSymbolId,
        TypeId,
        TypeId,
    ) {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/class-properties.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(class.name?)?.data else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .expect("fixture contains the requested class declaration");
        let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let members = context.get_nongeneric_class_members(owner).unwrap();
        let instance = members.shells().instance_type();
        let value = members.shells().value_type();
        (context, owner, instance, value)
    }

    fn published_scalar_wrapper_method<'arena>(
        parsed: &'arena ParseResult,
        file: FileId,
        wrapper_name: &str,
        method_name: &str,
    ) -> (CanonicalCheckerContext<'arena>, SemanticSymbolId, TypeId) {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/scalar-properties.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        let global_types = context.global_types().clone();
        let (method, declaration, return_annotation, parameter, string, number, undefined) = {
            let store = context.store();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let owner = store
                .symbol_table(bootstrap.globals)
                .and_then(|globals| globals.get_source(wrapper_name))
                .and_then(|owner| store.get_merged_symbol(owner))
                .unwrap();
            let method = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source(method_name))
                .unwrap();
            let declaration = store.symbol(method).unwrap().declarations().unwrap()[0];
            let NodeData::MethodSignatureDeclaration(method_data) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected one scalar wrapper method declaration")
            };
            let return_annotation = NodeRef::new(
                declaration.arena,
                declaration.file,
                method_data.type_.unwrap(),
            );
            let parameter = method_data.parameters.nodes.first().map(|node| {
                let parameter = NodeRef::new(declaration.arena, declaration.file, *node);
                let NodeData::ParameterDeclaration(parameter_data) =
                    &parsed.arena.get(parameter.node).unwrap().data
                else {
                    panic!("expected the optional numeric method parameter")
                };
                let annotation = NodeRef::new(
                    parameter.arena,
                    parameter.file,
                    parameter_data.type_.unwrap(),
                );
                (
                    context.file(file).unwrap().1.symbol(parameter).unwrap(),
                    annotation,
                )
            });
            (
                method,
                declaration,
                return_annotation,
                parameter,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.undefined_type,
            )
        };
        let store = context.store_mut_for_test();
        assert!(store.set_type_node_links(
            return_annotation,
            TypeNodeLinks {
                resolved_type: Some(string),
                ..TypeNodeLinks::default()
            },
        ));
        if let Some((symbol, annotation)) = parameter {
            let optional_number = store
                .expression_union_type_with_global_types(
                    &global_types,
                    &[number, undefined],
                    UnionReduction::Literal,
                )
                .unwrap();
            assert!(store.set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(number),
                    ..TypeNodeLinks::default()
                },
            ));
            assert!(store.set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(optional_number),
                    ..ValueSymbolLinks::default()
                },
            ));
        }
        let type_ = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
            .unwrap();
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(declaration),
                Vec::new(),
                None,
                parameter.map(|(symbol, _)| symbol).into_iter().collect(),
                Some(string),
                None,
                0,
            )
            .unwrap();
        assert!(store.set_signature_links(
            declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(store.set_value_symbol_links(
            method,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            type_,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));
        (context, method, type_)
    }

    fn array_property_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/array-properties.ts\""),
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
            vec![(file, &parsed.arena)],
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

    fn array_filter_library() -> ParseResult {
        parsed(concat!(
            "interface Array<T> { ",
            "filter<S extends T>(predicate: ",
            "(value: T, index: number, array: T[]) => value is S, thisArg?: any): S[]; ",
            "filter(predicate: ",
            "(value: T, index: number, array: T[]) => unknown, thisArg?: any): T[]; ",
            "} interface ReadonlyArray<T> { ",
            "filter<S extends T>(predicate: ",
            "(value: T, index: number, array: readonly T[]) => value is S, ",
            "thisArg?: any): S[]; ",
            "filter(predicate: ",
            "(value: T, index: number, array: readonly T[]) => unknown, ",
            "thisArg?: any): T[]; }",
        ))
    }

    struct ArrayFilterPropertyFixture<'arena> {
        context: CanonicalCheckerContext<'arena>,
        plan: SourcePropertyPlan,
        receiver: TypeId,
        element: TypeId,
        source_element: TypeId,
        method: SemanticSymbolId,
        template: TypeId,
    }

    #[allow(clippy::too_many_lines)] // Real library declarations publish the source method, but not its receiver copy.
    fn array_filter_property_fixture<'arena>(
        library: &'arena ParseResult,
        source: &'arena ParseResult,
    ) -> ArrayFilterPropertyFixture<'arena> {
        let library_file = FileId::new(45_320);
        let source_file = FileId::new(45_321);
        let files = [(library_file, library), (source_file, source)];
        let mut binder = CanonicalBinder::new();
        for (file, parsed) in files {
            let is_library = file == library_file;
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        is_library,
                        is_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (file, parsed) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed)| (file, &parsed.arena))
                .collect(),
            options,
        )
        .unwrap();
        let bounds = files.map(|(file, _)| context.file(file).unwrap().1.clone());
        let host = DeclaredTypeHost::new_after_global_merge(
            files
                .iter()
                .zip(&bounds)
                .map(|((_, parsed), bound)| (&parsed.arena, bound)),
            crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let access = property_access(source, source_file);
        let call = NodeRef::new(
            source.arena.id(),
            source_file,
            source.arena.get(access.node).unwrap().parent.unwrap(),
        );
        let syntax =
            plan_direct_source_property_call_syntax(&source.arena, context.store(), access, call)
                .unwrap();
        let variable =
            source
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(&record.data, NodeData::VariableDeclaration(_))
                        .then_some(NodeRef::new(source.arena.id(), source_file, node))
                })
                .unwrap();
        let variable = context
            .store()
            .get_merged_symbol(bounds[1].symbol(variable).unwrap())
            .unwrap();
        let globals = context.global_types().clone();
        let mut setup = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let receiver =
            crate::semantic::type_nodes::CanonicalTypeQuery::new_with_global_types_and_session(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut setup,
                &mut diagnostics,
            )
            .unwrap()
            .get_type_of_declared_value(variable)
            .unwrap();
        let array = context
            .store()
            .canonical_array_reference(&globals, receiver)
            .unwrap()
            .unwrap();
        let target = if array.readonly {
            globals.readonly_array_type
        } else {
            globals.array_type
        };
        let TypeData::Interface(interface) = context.store().type_payload(target).unwrap().data()
        else {
            panic!("the receiver must retain the real Array target")
        };
        let [source_element] = interface
            .reference
            .resolved_type_arguments
            .as_deref()
            .unwrap()
        else {
            panic!("the Array target must retain its declared element parameter")
        };
        let source_element = *source_element;
        let template = crate::semantic::source_calls::materialize_global_array_callback_method(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &mut setup,
            &mut diagnostics,
            receiver,
            "filter",
            access,
        )
        .unwrap()
        .unwrap();
        assert!(diagnostics.is_empty());
        assert_eq!(setup.limit_event_count(), 0);
        let method = context
            .store()
            .type_payload(template)
            .unwrap()
            .symbol()
            .unwrap();
        assert!(!context.store().types().any(|(_, record)| {
            matches!(record.data(), TypeData::Object(object) if object.target == Some(template))
        }));
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, variable))
                .unwrap();
        ArrayFilterPropertyFixture {
            context,
            plan,
            receiver,
            element: array.element_type,
            source_element,
            method,
            template,
        }
    }

    fn array_filter_property_counts(store: &CanonicalTypeMapperStore) -> ([usize; 8], [usize; 26]) {
        (
            [
                store.type_len(),
                store.signature_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.type_alias_len(),
                store.type_predicate_len(),
                store.symbol_store().symbol_table_len(),
                store.type_resolution_len(),
            ],
            store.checker_link_allocated_lengths(),
        )
    }

    #[allow(clippy::too_many_lines)] // Check source declarations, method mappers, and both callback copies.
    fn assert_array_filter_property_mapping(
        fixture: &ArrayFilterPropertyFixture<'_>,
        value: TypeId,
    ) {
        let store = fixture.context.store();
        let globals = fixture.context.global_types();
        let receiver = store
            .canonical_array_reference(globals, fixture.receiver)
            .unwrap()
            .unwrap();
        let TypeData::Object(object) = store.type_payload(value).unwrap().data() else {
            panic!("filter must retain its copied method object")
        };
        assert_eq!(object.target, Some(fixture.template));
        assert_eq!(
            store.type_payload(value).unwrap().symbol(),
            Some(fixture.method)
        );
        let target = if receiver.readonly {
            globals.readonly_array_type
        } else {
            globals.array_type
        };
        let TypeData::Interface(interface) = store.type_payload(target).unwrap().data() else {
            unreachable!()
        };
        assert_eq!(
            store.type_mapper_has_exact_endpoints(
                object.mapper.unwrap(),
                &[fixture.source_element, interface.this_type.unwrap()],
                &[fixture.element, fixture.receiver],
            ),
            Some(true)
        );
        let StoredCallableSetValidation::Valid {
            projection: source, ..
        } = validate_stored_callable_set(store, fixture.template)
        else {
            panic!("the source filter overloads must remain valid")
        };
        let StoredCallableSetValidation::Valid {
            projection: mapped, ..
        } = validate_stored_callable_set(store, value)
        else {
            panic!("the mapped filter overloads must remain valid")
        };
        assert_eq!(source.call_signatures.len(), 2);
        assert_eq!(mapped.call_signatures.len(), 2);
        for (source, mapped) in source.call_signatures.iter().zip(&mapped.call_signatures) {
            let original = store.signature(source.signature).unwrap();
            let copied = store.signature(mapped.signature).unwrap();
            assert_eq!(copied.target(), Some(source.signature));
            assert_eq!(copied.declaration(), original.declaration());
            let StoredCallableSetValidation::Valid {
                projection: source_callback,
                ..
            } = validate_stored_callable_set(store, source.parameters[0])
            else {
                panic!("the source callback must keep its FunctionType declaration")
            };
            let StoredCallableSetValidation::Valid {
                projection: mapped_callback,
                ..
            } = validate_stored_callable_set(store, mapped.parameters[0])
            else {
                panic!("the mapped callback must retain the Array method owner")
            };
            let source_callback = &source_callback.call_signatures[0];
            let mapped_callback = &mapped_callback.call_signatures[0];
            assert_eq!(source_callback.parameters[0], fixture.source_element);
            assert_eq!(mapped_callback.parameters[0], fixture.element);
            assert_eq!(mapped_callback.parameters[1], source_callback.parameters[1]);
            let callback_array = store
                .canonical_array_reference(globals, mapped_callback.parameters[2])
                .unwrap()
                .unwrap();
            assert_eq!(callback_array.element_type, fixture.element);
            assert_eq!(callback_array.readonly, receiver.readonly);
            let callback_signature = store.signature(mapped_callback.signature).unwrap();
            assert_eq!(callback_signature.target(), Some(source_callback.signature));
            assert_eq!(callback_signature.mapper(), copied.mapper());
            assert_eq!(
                callback_signature.declaration(),
                store
                    .signature(source_callback.signature)
                    .unwrap()
                    .declaration()
            );
            let TypeData::Object(callback) =
                store.type_payload(mapped.parameters[0]).unwrap().data()
            else {
                unreachable!()
            };
            assert_eq!(callback.target, Some(source.parameters[0]));
            assert_eq!(callback.mapper, copied.mapper());
        }
        let ordinary = &mapped.call_signatures[1];
        let returned = store
            .canonical_array_reference(globals, ordinary.return_type.unwrap())
            .unwrap()
            .unwrap();
        assert_eq!(returned.element_type, fixture.element);
        assert!(!returned.readonly);
        assert_eq!(
            store
                .value_symbol_links(fixture.method)
                .unwrap()
                .resolved_type,
            Some(fixture.template)
        );
    }

    #[test]
    fn canonical_array_filter_properties_use_the_caller_session_cold_and_warm() {
        let library = array_filter_library();
        for (readonly, recovering) in [(false, false), (false, true), (true, false), (true, true)] {
            let source = parsed(&format!(
                "declare const values: {}number[]; values.filter(value => value);",
                if readonly { "readonly " } else { "" },
            ));
            let mut fixture = array_filter_property_fixture(&library, &source);
            let globals = fixture.context.global_types().clone();
            let mut session = if recovering {
                InstantiationSession::new_recovering(
                    fixture.context.store(),
                    InstantiationLimits::default(),
                    fixture
                        .context
                        .store()
                        .intrinsic_bootstrap()
                        .unwrap()
                        .error_type,
                )
                .unwrap()
            } else {
                InstantiationSession::new(InstantiationLimits::default())
            };
            let checked = check_direct_source_property_with_session(
                fixture.context.store_mut_for_test(),
                Some(&globals),
                &fixture.plan,
                fixture.receiver,
                &mut session,
            )
            .unwrap();
            assert!(checked.diagnostics.is_empty());
            assert!(session.query_count() > 0);
            assert_eq!(session.query_count(), session.total_count());
            assert_eq!(session.limit_event_count(), 0);
            assert_array_filter_property_mapping(&fixture, checked.type_);
            let counts = array_filter_property_counts(fixture.context.store());
            let budget = (
                session.query_count(),
                session.total_count(),
                session.limit_event_count(),
            );
            for _ in 0..2 {
                assert_eq!(
                    check_direct_source_property_with_session(
                        fixture.context.store_mut_for_test(),
                        Some(&globals),
                        &fixture.plan,
                        fixture.receiver,
                        &mut session,
                    ),
                    Ok(checked.clone())
                );
                assert_eq!(
                    array_filter_property_counts(fixture.context.store()),
                    counts
                );
                assert_eq!(
                    (
                        session.query_count(),
                        session.total_count(),
                        session.limit_event_count()
                    ),
                    budget
                );
            }
            let mut exhausted = InstantiationSession::new(InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            });
            assert_eq!(
                check_direct_source_property_with_session(
                    fixture.context.store_mut_for_test(),
                    Some(&globals),
                    &fixture.plan,
                    fixture.receiver,
                    &mut exhausted,
                ),
                Ok(checked)
            );
            assert_eq!(
                (
                    exhausted.query_count(),
                    exhausted.total_count(),
                    exhausted.limit_event_count()
                ),
                (0, 0, 0)
            );
            assert_eq!(
                array_filter_property_counts(fixture.context.store()),
                counts
            );
        }
    }

    #[test]
    fn canonical_array_filter_properties_keep_spent_count_and_depth_limits() {
        let library = array_filter_library();
        let source = parsed("declare const values: number[]; values.filter(value => value);");
        for count_limit in [true, false] {
            let mut fixture = array_filter_property_fixture(&library, &source);
            let globals = fixture.context.global_types().clone();
            let targets = Some(CanonicalArrayTargets::from_global_types(&globals));
            let mapper = fixture
                .context
                .store_mut_for_test()
                .new_simple_type_mapper(fixture.source_element, fixture.element)
                .unwrap();
            let limits = if count_limit {
                InstantiationLimits {
                    max_count: 1,
                    ..InstantiationLimits::default()
                }
            } else {
                InstantiationLimits {
                    max_depth: 1,
                    ..InstantiationLimits::default()
                }
            };
            let mut session = InstantiationSession::new(limits);
            if count_limit {
                assert_eq!(
                    instantiate_type_with_session(
                        fixture.context.store_mut_for_test(),
                        fixture.source_element,
                        mapper,
                        targets,
                        &mut session
                    ),
                    Ok(fixture.element)
                );
                assert_eq!(session.query_count(), 1);
            }
            assert_eq!(
                check_direct_source_property_with_session(
                    fixture.context.store_mut_for_test(),
                    Some(&globals),
                    &fixture.plan,
                    fixture.receiver,
                    &mut session,
                ),
                Err(SourcePropertyError::Capacity(fixture.plan.node))
            );
            assert_eq!(session.limit_event_count(), 1);
            assert_eq!(session.query_count(), session.total_count());
            assert!(
                fixture
                    .context
                    .store()
                    .type_node_links(fixture.plan.node)
                    .is_none()
            );
            assert!(
                fixture
                    .context
                    .store()
                    .symbol_node_links(fixture.plan.node)
                    .is_none()
            );
            let total = session.total_count();
            if count_limit {
                assert_eq!(session.query_count(), 1);
                session.reset_query();
            }
            assert_eq!(
                instantiate_type_with_session(
                    fixture.context.store_mut_for_test(),
                    fixture.source_element,
                    mapper,
                    targets,
                    &mut session
                ),
                Ok(fixture.element)
            );
            assert_eq!(session.total_count(), total + 1);
            assert_eq!(session.limit_event_count(), 1);
            let mut retry = InstantiationSession::new(InstantiationLimits::default());
            let checked = check_direct_source_property_with_session(
                fixture.context.store_mut_for_test(),
                Some(&globals),
                &fixture.plan,
                fixture.receiver,
                &mut retry,
            )
            .unwrap();
            assert_array_filter_property_mapping(&fixture, checked.type_);
            assert!(retry.query_count() > 0);
            assert_eq!(retry.limit_event_count(), 0);
        }
    }

    #[test]
    fn canonical_array_filter_properties_reject_warm_callback_damage_without_budget_use() {
        let library = array_filter_library();
        let source = parsed("declare const values: number[]; values.filter(value => value);");
        let mut fixture = array_filter_property_fixture(&library, &source);
        let globals = fixture.context.global_types().clone();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let checked = check_direct_source_property_with_session(
            fixture.context.store_mut_for_test(),
            Some(&globals),
            &fixture.plan,
            fixture.receiver,
            &mut session,
        )
        .unwrap();
        assert_array_filter_property_mapping(&fixture, checked.type_);
        let store = fixture.context.store_mut_for_test();
        let StoredCallableSetValidation::Valid { projection, .. } =
            validate_stored_callable_set(store, checked.type_)
        else {
            unreachable!()
        };
        let callback = projection.call_signatures[1].parameters[0];
        let StoredCallableSetValidation::Valid { projection, .. } =
            validate_stored_callable_set(store, callback)
        else {
            unreachable!()
        };
        let parameter = store
            .signature(projection.call_signatures[0].signature)
            .unwrap()
            .parameters()[0];
        let original = store.value_symbol_links(parameter).unwrap().clone();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        assert!(store.set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..original.clone()
            }
        ));
        let counts = array_filter_property_counts(store);
        let mut exhausted = InstantiationSession::new(InstantiationLimits {
            max_count: 0,
            ..InstantiationLimits::default()
        });
        for _ in 0..2 {
            assert_eq!(
                check_direct_source_property_with_session(
                    fixture.context.store_mut_for_test(),
                    Some(&globals),
                    &fixture.plan,
                    fixture.receiver,
                    &mut exhausted
                ),
                Err(SourcePropertyError::InvalidCache(fixture.plan.node))
            );
            assert_eq!(
                array_filter_property_counts(fixture.context.store()),
                counts
            );
            assert_eq!(
                (
                    exhausted.query_count(),
                    exhausted.total_count(),
                    exhausted.limit_event_count()
                ),
                (0, 0, 0)
            );
        }
        assert!(
            fixture
                .context
                .store_mut_for_test()
                .set_value_symbol_links(parameter, original)
        );
        assert_eq!(
            check_direct_source_property_with_session(
                fixture.context.store_mut_for_test(),
                Some(&globals),
                &fixture.plan,
                fixture.receiver,
                &mut exhausted
            ),
            Ok(checked)
        );
        assert_eq!(
            array_filter_property_counts(fixture.context.store()),
            counts
        );
        assert_eq!(exhausted.limit_event_count(), 0);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the limit event, later caller use, and cache checks in one control.
    fn canonical_array_filter_zero_count_recovery_cannot_publish_an_invalid_method() {
        let library = array_filter_library();
        let source = parsed("declare const values: number[]; values.filter(value => value);");
        let mut fixture = array_filter_property_fixture(&library, &source);
        let globals = fixture.context.global_types().clone();
        let error = fixture
            .context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .error_type;
        let mapper = fixture
            .context
            .store_mut_for_test()
            .new_simple_type_mapper(fixture.source_element, fixture.element)
            .unwrap();
        let mut session = InstantiationSession::new_recovering(
            fixture.context.store(),
            InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            },
            error,
        )
        .unwrap();
        let checked = check_direct_source_property_with_session(
            fixture.context.store_mut_for_test(),
            Some(&globals),
            &fixture.plan,
            fixture.receiver,
            &mut session,
        );
        assert!(session.limit_event_count() > 0);
        assert_eq!((session.query_count(), session.total_count()), (0, 0));
        assert_eq!(session.recovery_error_type(), Some(error));
        let events = session.limit_event_count();
        let targets = Some(CanonicalArrayTargets::from_global_types(&globals));
        assert_eq!(
            instantiate_type_with_session(
                fixture.context.store_mut_for_test(),
                fixture.source_element,
                mapper,
                targets,
                &mut session
            ),
            Ok(error)
        );
        assert_eq!(session.limit_event_count(), events + 1);
        assert_eq!(
            instantiate_type_with_session(
                fixture.context.store_mut_for_test(),
                fixture.element,
                mapper,
                targets,
                &mut session
            ),
            Ok(fixture.element)
        );
        assert_eq!(
            (
                session.query_count(),
                session.total_count(),
                session.limit_event_count()
            ),
            (0, 0, events + 1)
        );
        let store = fixture.context.store();
        for (type_, record) in store.types() {
            if matches!(record.data(), TypeData::Object(object) if object.target == Some(fixture.template))
            {
                assert!(
                    matches!(
                        validate_stored_callable_set(store, type_),
                        StoredCallableSetValidation::Valid { .. }
                    ),
                    "limit recovery must not leave an invalid filter method cache"
                );
            }
        }
        if let Ok(checked) = checked {
            assert!(matches!(
                validate_stored_callable_set(store, checked.type_),
                StoredCallableSetValidation::Valid { .. }
            ));
            let counts = array_filter_property_counts(store);
            let events = session.limit_event_count();
            assert_eq!(
                check_direct_source_property_with_session(
                    fixture.context.store_mut_for_test(),
                    Some(&globals),
                    &fixture.plan,
                    fixture.receiver,
                    &mut session
                ),
                Ok(checked)
            );
            assert_eq!(
                array_filter_property_counts(fixture.context.store()),
                counts
            );
            assert_eq!(
                (
                    session.query_count(),
                    session.total_count(),
                    session.limit_event_count()
                ),
                (0, 0, events)
            );
        } else {
            assert!(
                store
                    .type_node_links(fixture.plan.node)
                    .is_none_or(|links| links == &TypeNodeLinks::default())
            );
            assert!(
                store
                    .symbol_node_links(fixture.plan.node)
                    .is_none_or(|links| links == &SymbolNodeLinks::default())
            );
        }
    }

    fn published_array_concat(
        parsed: &ParseResult,
        file: FileId,
    ) -> (
        CanonicalCheckerContext<'_>,
        SemanticSymbolId,
        TypeId,
        TypeId,
        Vec<super::super::SignatureId>,
    ) {
        let mut context = array_property_context(parsed, file);
        let global_types = context.global_types().clone();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let array = context
            .store_mut_for_test()
            .create_canonical_array_type(&global_types, number, false)
            .unwrap();
        let (method, declarations, parameters) = {
            let store = context.store();
            let owner = store
                .type_payload(global_types.array_type)
                .and_then(TypeRecord::symbol)
                .and_then(|owner| store.get_merged_symbol(owner))
                .unwrap();
            let method = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source("concat"))
                .unwrap();
            let declarations = store
                .symbol(method)
                .unwrap()
                .declarations()
                .unwrap()
                .to_vec();
            let parameters = declarations
                .iter()
                .map(|declaration| {
                    let NodeData::MethodSignatureDeclaration(signature) =
                        &parsed.arena.get(declaration.node).unwrap().data
                    else {
                        panic!("expected an Array.concat overload")
                    };
                    let [parameter] = signature.parameters.nodes.as_slice() else {
                        panic!("expected one Array.concat overload parameter")
                    };
                    let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
                    context.file(file).unwrap().1.symbol(parameter).unwrap()
                })
                .collect::<Vec<_>>();
            (method, declarations, parameters)
        };
        let store = context.store_mut_for_test();
        let callable = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
            .unwrap();
        let mut signatures = Vec::with_capacity(declarations.len());
        for (index, (&declaration, &parameter)) in declarations.iter().zip(&parameters).enumerate()
        {
            let parameter_type = if index == 0 { number } else { array };
            assert!(store.set_value_symbol_links(
                parameter,
                ValueSymbolLinks {
                    resolved_type: Some(parameter_type),
                    ..ValueSymbolLinks::default()
                },
            ));
            let signature = store
                .alloc_signature(
                    SignatureFlags::NONE,
                    Some(declaration),
                    Vec::new(),
                    None,
                    vec![parameter],
                    Some(array),
                    None,
                    1,
                )
                .unwrap();
            assert!(store.set_signature_links(
                declaration,
                SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                },
            ));
            signatures.push(signature);
        }
        assert!(store.set_structured_type_members(
            callable,
            None,
            None,
            Some(signatures.clone()),
            None,
            None,
        ));
        assert!(store.set_value_symbol_links(
            method,
            ValueSymbolLinks {
                resolved_type: Some(callable),
                ..ValueSymbolLinks::default()
            },
        ));
        (context, method, callable, array, signatures)
    }

    type PublishedGenericArrayConcat<'arena> = (
        CanonicalCheckerContext<'arena>,
        SemanticSymbolId,
        TypeId,
        TypeId,
        TypeId,
        Vec<super::super::SignatureId>,
        Vec<(NodeRef, TypeId, NodeRef)>,
    );

    fn published_generic_array_concat(
        parsed: &ParseResult,
        file: FileId,
    ) -> PublishedGenericArrayConcat<'_> {
        let mut context = array_property_context(parsed, file);
        let global_types = context.global_types().clone();
        let (method, concat_owner, type_parameter, declarations) = {
            let store = context.store();
            let globals = store.intrinsic_bootstrap().unwrap().globals;
            let owner = store
                .symbol_table(globals)
                .and_then(|globals| globals.get_source("Array"))
                .and_then(|owner| store.get_merged_symbol(owner))
                .unwrap();
            let concat_owner = store
                .symbol_table(globals)
                .and_then(|globals| globals.get_source("ConcatArray"))
                .and_then(|owner| store.get_merged_symbol(owner))
                .unwrap();
            let method = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source("concat"))
                .unwrap();
            let TypeData::Interface(array) =
                store.type_payload(global_types.array_type).unwrap().data()
            else {
                panic!("Array must retain its global generic interface target")
            };
            let [type_parameter] = array.reference.resolved_type_arguments.as_deref().unwrap()
            else {
                panic!("Array must retain one declared element type parameter")
            };
            (
                method,
                concat_owner,
                *type_parameter,
                store
                    .symbol(method)
                    .unwrap()
                    .declarations()
                    .unwrap()
                    .to_vec(),
            )
        };
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let required = context
            .store()
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let pair = context
            .store_mut_for_test()
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[number, number],
                &[required, required],
                false,
            ))
            .unwrap();
        let concat_target = context.get_declared_type_of_symbol(concat_owner).unwrap();
        let receiver = context
            .store_mut_for_test()
            .create_canonical_array_type(&global_types, pair, false)
            .unwrap();
        let concat_template = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(concat_target, &[type_parameter])
            .unwrap();
        let first_parameter = context
            .store_mut_for_test()
            .create_canonical_array_type(&global_types, concat_template, false)
            .unwrap();
        let union = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &global_types,
                &[type_parameter, concat_template],
                UnionReduction::Literal,
            )
            .unwrap();
        let second_parameter = context
            .store_mut_for_test()
            .create_canonical_array_type(&global_types, union, false)
            .unwrap();
        let plans = declarations
            .iter()
            .copied()
            .zip([first_parameter, second_parameter])
            .map(|(declaration, parameter_type)| {
                let NodeData::MethodSignatureDeclaration(signature) =
                    &parsed.arena.get(declaration.node).unwrap().data
                else {
                    panic!("expected one original Array.concat method overload")
                };
                let [parameter] = signature.parameters.nodes.as_slice() else {
                    panic!("expected one original Array.concat rest parameter")
                };
                let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
                let NodeData::ParameterDeclaration(parameter_data) =
                    &parsed.arena.get(parameter.node).unwrap().data
                else {
                    panic!("expected a binder-owned Array.concat rest parameter")
                };
                (
                    declaration,
                    context.file(file).unwrap().1.symbol(parameter).unwrap(),
                    NodeRef::new(
                        parameter.arena,
                        parameter.file,
                        parameter_data.type_.unwrap(),
                    ),
                    NodeRef::new(
                        declaration.arena,
                        declaration.file,
                        signature.type_.unwrap(),
                    ),
                    parameter_type,
                )
            })
            .collect::<Vec<_>>();

        let store = context.store_mut_for_test();
        let template = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
            .unwrap();
        let mut signatures = Vec::with_capacity(plans.len());
        let mut annotation_caches = Vec::with_capacity(plans.len());
        for &(declaration, parameter, parameter_annotation, return_annotation, parameter_type) in
            &plans
        {
            assert!(store.set_type_node_links(
                parameter_annotation,
                TypeNodeLinks {
                    resolved_type: Some(parameter_type),
                    ..TypeNodeLinks::default()
                },
            ));
            assert!(store.set_type_node_links(
                return_annotation,
                TypeNodeLinks {
                    resolved_type: Some(global_types.array_type),
                    ..TypeNodeLinks::default()
                },
            ));
            assert!(store.set_value_symbol_links(
                parameter,
                ValueSymbolLinks {
                    resolved_type: Some(parameter_type),
                    ..ValueSymbolLinks::default()
                },
            ));
            let signature = store
                .alloc_signature(
                    SignatureFlags::HAS_REST_PARAMETER,
                    Some(declaration),
                    Vec::new(),
                    None,
                    vec![parameter],
                    Some(global_types.array_type),
                    None,
                    0,
                )
                .unwrap();
            assert!(store.set_signature_links(
                declaration,
                SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                },
            ));
            signatures.push(signature);
            annotation_caches.push((parameter_annotation, parameter_type, return_annotation));
        }
        assert!(store.set_value_symbol_links(
            method,
            ValueSymbolLinks {
                resolved_type: Some(template),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            template,
            None,
            None,
            Some(signatures.clone()),
            None,
            None,
        ));
        for (&signature, &(_, _, _, return_annotation, _)) in signatures.iter().zip(&plans) {
            assert!(store.set_function_signature_return_annotation(
                signature,
                return_annotation,
                false,
            ));
        }
        assert!(
            store.set_callable_signature_parameter_types_batch(
                signatures
                    .iter()
                    .copied()
                    .zip(plans.iter().map(|plan| vec![plan.4]))
                    .collect(),
            )
        );
        (
            context,
            method,
            template,
            receiver,
            pair,
            signatures,
            annotation_caches,
        )
    }

    #[test]
    fn required_own_property_publishes_exact_symbol_and_type_cold_and_warm() {
        let parsed = parsed("const result = object.value;");
        let file = FileId::new(501);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let (object, property) = property_object(&mut store, "value", string, false);
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, property))
                .unwrap();

        assert_eq!(
            check_direct_source_property(&mut store, None, &plan, object),
            Ok(CheckedSourceProperty {
                type_: string,
                diagnostics: Vec::new(),
            })
        );
        assert_eq!(
            store
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(string)
        );
        assert_eq!(
            store
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(property)
        );
        assert_eq!(
            check_direct_source_property(&mut store, None, &plan, object),
            Ok(CheckedSourceProperty {
                type_: string,
                diagnostics: Vec::new(),
            })
        );
    }

    #[test]
    fn canonical_any_publishes_only_the_exact_type_cache() {
        let parsed = parsed("const result = value.name;");
        let file = FileId::new(502);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let any = store.intrinsic_bootstrap().unwrap().any_type;
        let receiver_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source("value"),
            ))
            .unwrap();
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan = finish_direct_source_property_plan(
            &syntax,
            identifier_receiver(&syntax, receiver_symbol),
        )
        .unwrap();

        assert_eq!(
            check_direct_source_property(&mut store, None, &plan, any),
            Ok(CheckedSourceProperty {
                type_: any,
                diagnostics: Vec::new(),
            })
        );
        assert_eq!(
            store
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(any)
        );
        assert!(store.symbol_node_links(access).is_none());
    }

    #[test]
    fn scalar_wrapper_methods_publish_exact_symbols_for_primitive_and_literal_receivers() {
        for (index, (source, wrapper_name, method_name)) in [
            (
                concat!(
                    "interface Number { toFixed(fractionDigits?: number): string; } ",
                    "const result = 2..toFixed(0);",
                ),
                "Number",
                "toFixed",
            ),
            (
                concat!(
                    "interface String { toLowerCase(): string; } ",
                    "const result = 'VALUE'.toLowerCase();",
                ),
                "String",
                "toLowerCase",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parsed(source);
            let file = FileId::new(540 + u32::try_from(index).unwrap());
            let access = property_access(&parsed, file);
            let call = NodeRef::new(
                parsed.arena.id(),
                file,
                parsed.arena.get(access.node).unwrap().parent.unwrap(),
            );
            let (mut context, method, callable) =
                published_scalar_wrapper_method(&parsed, file, wrapper_name, method_name);
            let global_types = context.global_types().clone();
            let syntax = plan_direct_source_property_call_syntax(
                &parsed.arena,
                context.store(),
                access,
                call,
            )
            .unwrap();
            let (receiver, wrapper, receiver_types) = if wrapper_name == "Number" {
                let number = context.store().intrinsic_bootstrap().unwrap().number_type;
                let regular = context
                    .store_mut_for_test()
                    .regular_number_literal_type(Number::new(2.0))
                    .unwrap();
                let fresh = context
                    .store_mut_for_test()
                    .fresh_type_of_literal_type(regular)
                    .unwrap();
                (
                    PlannedExpression::new(
                        syntax.receiver(),
                        PlannedExpressionKind::Number {
                            value: Number::new(2.0),
                            unary_operand: None,
                        },
                    ),
                    global_types.number_type,
                    [number, regular, fresh],
                )
            } else {
                let string = context.store().intrinsic_bootstrap().unwrap().string_type;
                let regular = context
                    .store_mut_for_test()
                    .regular_string_literal_type("VALUE".to_owned())
                    .unwrap();
                let fresh = context
                    .store_mut_for_test()
                    .fresh_type_of_literal_type(regular)
                    .unwrap();
                (
                    PlannedExpression::new(
                        syntax.receiver(),
                        PlannedExpressionKind::String("VALUE".to_owned()),
                    ),
                    global_types.string_type,
                    [string, regular, fresh],
                )
            };
            let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

            for receiver_type in receiver_types {
                assert_eq!(
                    check_direct_source_property(
                        context.store_mut_for_test(),
                        Some(&global_types),
                        &plan,
                        receiver_type,
                    ),
                    Ok(CheckedSourceProperty {
                        type_: callable,
                        diagnostics: Vec::new(),
                    }),
                    "method {wrapper_name}.{method_name}",
                );
            }
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(access)
                    .and_then(|links| links.resolved_symbol),
                Some(method),
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(access)
                    .and_then(|links| links.resolved_type),
                Some(callable),
            );
            let TypeData::Interface(wrapper) =
                context.store().type_payload(wrapper).unwrap().data()
            else {
                panic!("expected the configured scalar wrapper interface")
            };
            assert!(!wrapper.declared_members_resolved);
        }
    }

    #[test]
    fn optional_scalar_wrapper_method_reads_restore_undefined() {
        let parsed = parsed(concat!(
            "interface String { toLowerCase(): string; } ",
            "declare let value: string | undefined; ",
            "const result = value?.toLowerCase;",
        ));
        let file = FileId::new(542);
        let access = property_access(&parsed, file);
        let (mut context, method, callable) =
            published_scalar_wrapper_method(&parsed, file, "String", "toLowerCase");
        let global_types = context.global_types().clone();
        let (string, undefined) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.undefined_type)
        };
        let receiver_type = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &global_types,
                &[string, undefined],
                UnionReduction::Literal,
            )
            .unwrap();
        let syntax =
            plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, method))
                .unwrap();

        let checked = check_direct_source_property(
            context.store_mut_for_test(),
            Some(&global_types),
            &plan,
            receiver_type,
        )
        .unwrap();
        let TypeData::Union(result) = context.store().type_payload(checked.type_).unwrap().data()
        else {
            panic!("optional scalar method reads must include undefined")
        };
        assert!(result.union.types.contains(&callable));
        assert!(result.union.types.contains(&undefined));
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(method),
        );
    }

    #[test]
    fn malformed_scalar_wrapper_method_cache_fails_before_property_publication() {
        let parsed = parsed(concat!(
            "interface String { toLowerCase(): string; } ",
            "const result = 'VALUE'.toLowerCase();",
        ));
        let file = FileId::new(543);
        let access = property_access(&parsed, file);
        let call = NodeRef::new(
            parsed.arena.id(),
            file,
            parsed.arena.get(access.node).unwrap().parent.unwrap(),
        );
        let (mut context, method, callable) =
            published_scalar_wrapper_method(&parsed, file, "String", "toLowerCase");
        let global_types = context.global_types().clone();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            method,
            ValueSymbolLinks {
                resolved_type: Some(callable),
                write_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        let syntax =
            plan_direct_source_property_call_syntax(&parsed.arena, context.store(), access, call)
                .unwrap();
        let plan = finish_direct_source_property_plan(
            &syntax,
            PlannedExpression::new(
                syntax.receiver(),
                PlannedExpressionKind::String("VALUE".to_owned()),
            ),
        )
        .unwrap();

        assert_eq!(
            check_direct_source_property(
                context.store_mut_for_test(),
                Some(&global_types),
                &plan,
                string,
            ),
            Err(SourcePropertyError::InvalidCache(access)),
        );
        assert!(context.store().type_node_links(access).is_none());
        assert!(context.store().symbol_node_links(access).is_none());
    }

    #[test]
    fn canonical_array_method_preserves_every_published_overload_cold_and_warm() {
        let parsed = parsed(concat!(
            "interface Array<T> { ",
            "concat(value: T): T[]; concat(values: T[]): T[]; ",
            "} interface ReadonlyArray<T> {} ",
            "const result = values.concat(1);",
        ));
        let file = FileId::new(544);
        let access = property_access(&parsed, file);
        let call = NodeRef::new(
            parsed.arena.id(),
            file,
            parsed.arena.get(access.node).unwrap().parent.unwrap(),
        );
        let (mut context, method, callable, receiver, signatures) =
            published_array_concat(&parsed, file);
        let global_types = context.global_types().clone();
        let syntax =
            plan_direct_source_property_call_syntax(&parsed.arena, context.store(), access, call)
                .unwrap();
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, method))
                .unwrap();
        let signature_count = context.store().signature_len();

        for _ in 0..2 {
            assert_eq!(
                check_direct_source_property(
                    context.store_mut_for_test(),
                    Some(&global_types),
                    &plan,
                    receiver,
                ),
                Ok(CheckedSourceProperty {
                    type_: callable,
                    diagnostics: Vec::new(),
                }),
            );
        }
        assert_eq!(context.store().signature_len(), signature_count);
        assert_eq!(
            context
                .store()
                .type_payload(callable)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.signatures.as_ref()),
            Some(&signatures),
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(method),
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Proves both mapped overloads and their unchanged declarations.
    fn canonical_array_method_specializes_tuple_receivers_and_preserves_generic_annotations() {
        let parsed = parsed(concat!(
            "interface ConcatArray<T> {} ",
            "interface Array<T> { ",
            "concat(...items: ConcatArray<T>[]): T[]; ",
            "concat(...items: (T | ConcatArray<T>)[]): T[]; ",
            "} interface ReadonlyArray<T> {} ",
            "const result = values.concat([[1, 2]]);",
        ));
        let file = FileId::new(548);
        let access = property_access(&parsed, file);
        let call = NodeRef::new(
            parsed.arena.id(),
            file,
            parsed.arena.get(access.node).unwrap().parent.unwrap(),
        );
        let (mut context, method, template, receiver, pair, originals, annotations) =
            published_generic_array_concat(&parsed, file);
        let global_types = context.global_types().clone();
        let syntax =
            plan_direct_source_property_call_syntax(&parsed.arena, context.store(), access, call)
                .unwrap();
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, method))
                .unwrap();

        let checked = check_direct_source_property(
            context.store_mut_for_test(),
            Some(&global_types),
            &plan,
            receiver,
        )
        .unwrap();
        assert_ne!(checked.type_, template);
        assert!(checked.diagnostics.is_empty());
        assert_eq!(
            context
                .store()
                .value_symbol_links(method)
                .and_then(|links| links.resolved_type),
            Some(template),
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(method),
        );
        let TypeData::Object(specialized) =
            context.store().type_payload(checked.type_).unwrap().data()
        else {
            panic!("the specialized method must retain a callable object")
        };
        assert_eq!(specialized.target, Some(template));
        let mapper = specialized.mapper.unwrap();
        let signatures = specialized.structured.signatures.as_ref().unwrap().clone();
        assert_eq!(signatures.len(), originals.len());
        let mut parameter_elements = Vec::new();
        for (&signature, &original) in signatures.iter().zip(&originals) {
            let record = context.store().signature(signature).unwrap();
            assert_eq!(record.target(), Some(original));
            assert_eq!(record.mapper(), Some(mapper));
            assert_eq!(record.resolved_return_type(), Some(receiver));
            let [parameter] = record.parameters() else {
                panic!("the specialized overload must retain one rest parameter")
            };
            let type_ = context
                .store()
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let array = context
                .store()
                .canonical_array_reference(&global_types, type_)
                .unwrap()
                .unwrap();
            parameter_elements.push(array.element_type);
        }
        let first = super::super::reference_types::validate_direct_generic_reference(
            context.store(),
            parameter_elements[0],
        )
        .unwrap();
        assert_eq!(first.type_arguments.as_slice(), &[pair]);
        let TypeData::Union(second) = context
            .store()
            .type_payload(parameter_elements[1])
            .unwrap()
            .data()
        else {
            panic!("the second overload must retain the tuple-or-ConcatArray union")
        };
        assert!(second.union.types.contains(&pair));
        assert!(second.union.types.contains(&parameter_elements[0]));

        for (&original, &(parameter_annotation, parameter_type, return_annotation)) in
            originals.iter().zip(&annotations)
        {
            assert_eq!(
                context
                    .store()
                    .signature_links(
                        context
                            .store()
                            .signature(original)
                            .unwrap()
                            .declaration()
                            .unwrap(),
                    )
                    .and_then(|links| links.resolved_signature.signature()),
                Some(original),
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(parameter_annotation)
                    .and_then(|links| links.resolved_type),
                Some(parameter_type),
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(return_annotation)
                    .and_then(|links| links.resolved_type),
                Some(global_types.array_type),
            );
        }

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );
        assert_eq!(
            check_direct_source_property(
                context.store_mut_for_test(),
                Some(&global_types),
                &plan,
                receiver,
            ),
            Ok(checked),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Preserve the generic method, mapped result, and cache checks.
    fn canonical_array_element_methods_specialize_return_types_cold_and_warm() {
        let parsed = parsed(concat!(
            "interface Array<T> { customMethod(): T; } ",
            "interface ReadonlyArray<T> {} ",
            "const result = values.customMethod();",
        ));
        let file = FileId::new(549);
        let access = property_access(&parsed, file);
        let call = NodeRef::new(
            parsed.arena.id(),
            file,
            parsed.arena.get(access.node).unwrap().parent.unwrap(),
        );
        let mut context = array_property_context(&parsed, file);
        let global_types = context.global_types().clone();
        let (method, declaration, annotation, element) = {
            let store = context.store();
            let owner = store
                .type_payload(global_types.array_type)
                .and_then(TypeRecord::symbol)
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let method = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source("customMethod"))
                .unwrap();
            let declaration = store.symbol(method).unwrap().value_declaration().unwrap();
            let NodeData::MethodSignatureDeclaration(signature) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("the custom method must retain its declaration")
            };
            let annotation = NodeRef::new(
                declaration.arena,
                declaration.file,
                signature.type_.unwrap(),
            );
            let TypeData::Interface(array) =
                store.type_payload(global_types.array_type).unwrap().data()
            else {
                panic!("Array must retain its generic interface target")
            };
            let [element] = array.reference.resolved_type_arguments.as_deref().unwrap() else {
                panic!("Array must retain one generic element")
            };
            (method, declaration, annotation, *element)
        };
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let receiver = context
            .store_mut_for_test()
            .create_canonical_array_type(&global_types, string, false)
            .unwrap();
        let (template, signature) = {
            let store = context.store_mut_for_test();
            assert!(store.set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(element),
                    ..TypeNodeLinks::default()
                },
            ));
            let template = store
                .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
                .unwrap();
            let signature = store
                .alloc_signature(
                    SignatureFlags::NONE,
                    Some(declaration),
                    Vec::new(),
                    None,
                    Vec::new(),
                    Some(element),
                    None,
                    0,
                )
                .unwrap();
            assert!(store.set_signature_links(
                declaration,
                SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                },
            ));
            assert!(store.set_value_symbol_links(
                method,
                ValueSymbolLinks {
                    resolved_type: Some(template),
                    ..ValueSymbolLinks::default()
                },
            ));
            assert!(store.set_structured_type_members(
                template,
                None,
                None,
                Some(vec![signature]),
                None,
                None,
            ));
            assert!(
                store.set_callable_signature_parameter_types_batch(vec![(signature, Vec::new(),)])
            );
            (template, signature)
        };
        let syntax =
            plan_direct_source_property_call_syntax(&parsed.arena, context.store(), access, call)
                .unwrap();
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, method))
                .unwrap();

        let checked = check_direct_source_property(
            context.store_mut_for_test(),
            Some(&global_types),
            &plan,
            receiver,
        )
        .unwrap();
        assert_ne!(checked.type_, template);
        assert!(checked.diagnostics.is_empty());
        let TypeData::Object(callable) =
            context.store().type_payload(checked.type_).unwrap().data()
        else {
            panic!("the concrete array must receive its own method callable")
        };
        let [specialized] = callable.structured.signatures.as_deref().unwrap() else {
            panic!("the custom method must retain one specialized signature")
        };
        let specialized = context.store().signature(*specialized).unwrap();
        assert_eq!(callable.target, Some(template));
        assert_eq!(specialized.target(), Some(signature));
        assert_eq!(specialized.resolved_return_type(), Some(string));
        assert_eq!(
            context
                .store()
                .type_node_links(annotation)
                .and_then(|links| links.resolved_type),
            Some(element),
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(method),
        );

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );
        assert_eq!(
            check_direct_source_property(
                context.store_mut_for_test(),
                Some(&global_types),
                &plan,
                receiver,
            ),
            Ok(checked),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );

        let original = context.store().value_symbol_links(method).unwrap().clone();
        let mut poisoned = original.clone();
        poisoned.write_type = Some(string);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(method, poisoned)
        );
        assert_eq!(
            check_direct_source_property(
                context.store_mut_for_test(),
                Some(&global_types),
                &plan,
                receiver,
            ),
            Err(SourcePropertyError::InvalidCache(access)),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn canonical_array_property_reads_preserve_the_published_member_identity() {
        let parsed = parsed(concat!(
            "interface Array<T> { readonly length: number; } ",
            "interface ReadonlyArray<T> { readonly length: number; } ",
            "const result = values.length;",
        ));
        let file = FileId::new(545);
        let access = property_access(&parsed, file);

        for readonly in [false, true] {
            let mut context = array_property_context(&parsed, file);
            let global_types = context.global_types().clone();
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let target = if readonly {
                global_types.readonly_array_type
            } else {
                global_types.array_type
            };
            let owner = context
                .store()
                .type_payload(target)
                .and_then(TypeRecord::symbol)
                .and_then(|owner| context.store().get_merged_symbol(owner))
                .unwrap();
            let property = context
                .store()
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| context.store().symbol_table(members))
                .and_then(|members| members.get_source("length"))
                .unwrap();
            assert!(context.store_mut_for_test().set_value_symbol_links(
                property,
                ValueSymbolLinks {
                    resolved_type: Some(number),
                    ..ValueSymbolLinks::default()
                },
            ));
            let receiver = context
                .store_mut_for_test()
                .create_canonical_array_type(&global_types, number, readonly)
                .unwrap();
            let literal = (!readonly)
                .then(|| {
                    context
                        .store_mut_for_test()
                        .create_array_literal_type(&global_types, receiver)
                })
                .transpose()
                .unwrap();
            let syntax =
                plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
            let plan =
                finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, property))
                    .unwrap();

            for receiver in std::iter::once(receiver).chain(literal) {
                assert_eq!(
                    check_direct_source_property(
                        context.store_mut_for_test(),
                        Some(&global_types),
                        &plan,
                        receiver,
                    ),
                    Ok(CheckedSourceProperty {
                        type_: number,
                        diagnostics: Vec::new(),
                    }),
                    "readonly={readonly}",
                );
            }
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(access)
                    .and_then(|links| links.resolved_symbol),
                Some(property),
            );
        }
    }

    #[test]
    fn canonical_array_method_rejects_missing_overloads_before_property_publication() {
        let parsed = parsed(concat!(
            "interface Array<T> { ",
            "concat(value: T): T[]; concat(values: T[]): T[]; ",
            "} interface ReadonlyArray<T> {} ",
            "const result = values.concat;",
        ));
        let file = FileId::new(546);
        let access = property_access(&parsed, file);
        let (mut context, method, callable, receiver, signatures) =
            published_array_concat(&parsed, file);
        let global_types = context.global_types().clone();
        assert!(context.store_mut_for_test().set_structured_type_members(
            callable,
            None,
            None,
            Some(vec![signatures[0]]),
            None,
            None,
        ));
        let syntax =
            plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, method))
                .unwrap();

        assert_eq!(
            check_direct_source_property(
                context.store_mut_for_test(),
                Some(&global_types),
                &plan,
                receiver,
            ),
            Err(SourcePropertyError::InvalidCache(access)),
        );
        assert!(context.store().type_node_links(access).is_none());
        assert!(context.store().symbol_node_links(access).is_none());
    }

    #[test]
    fn canonical_array_method_requires_an_existing_published_callable() {
        let parsed = parsed(concat!(
            "interface Array<T> { concat(value: T): T[]; } ",
            "interface ReadonlyArray<T> {} ",
            "const result = values.concat;",
        ));
        let file = FileId::new(547);
        let access = property_access(&parsed, file);
        let mut context = array_property_context(&parsed, file);
        let global_types = context.global_types().clone();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let receiver = context
            .store_mut_for_test()
            .create_canonical_array_type(&global_types, number, false)
            .unwrap();
        let owner = context
            .store()
            .type_payload(global_types.array_type)
            .and_then(TypeRecord::symbol)
            .and_then(|owner| context.store().get_merged_symbol(owner))
            .unwrap();
        let method = context
            .store()
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("concat"))
            .unwrap();
        let syntax =
            plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, method))
                .unwrap();

        assert_eq!(
            check_direct_source_property(
                context.store_mut_for_test(),
                Some(&global_types),
                &plan,
                receiver,
            ),
            Err(SourcePropertyError::Relation(
                RelationUnavailable::UnresolvedPropertyType(method),
            )),
        );
        assert!(context.store().type_node_links(access).is_none());
        assert!(context.store().symbol_node_links(access).is_none());
    }

    #[test]
    fn enum_value_properties_publish_the_exact_member_symbol_and_fresh_type() {
        let parsed = parsed("enum Status { Ready = 1 } const result = Status.Ready;");
        let file = FileId::new(519);
        let access = property_access(&parsed, file);
        let (mut store, owner, value_type, member, fresh_type) = published_enum(&parsed, file);
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let receiver = PlannedExpression::new(
            syntax.receiver(),
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: owner,
                value_symbol: owner,
                kind: PlannedIdentifierReadKind::DeclaredValue,
            }),
        );
        let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

        for _ in 0..2 {
            assert_eq!(
                check_direct_source_property(&mut store, None, &plan, value_type),
                Ok(CheckedSourceProperty {
                    type_: fresh_type,
                    diagnostics: Vec::new(),
                }),
            );
        }
        assert_eq!(
            store
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(member),
        );
        assert_eq!(
            store
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(fresh_type),
        );
    }

    #[test]
    fn private_member_syntax_retains_its_exact_enclosing_class_and_call_capability() {
        let parsed = parsed("class Model { #run() {} call() { return this.#run(); } }");
        let file = FileId::new(580);
        let access = property_access(&parsed, file);
        let call = NodeRef::new(
            parsed.arena.id(),
            file,
            parsed.arena.get(access.node).unwrap().parent.unwrap(),
        );
        let store = registered_store(&parsed, file);
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ClassDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();

        let syntax =
            plan_direct_source_property_call_syntax(&parsed.arena, &store, access, call).unwrap();

        assert_eq!(syntax.name, "#run");
        assert_eq!(
            syntax.privacy,
            SourcePropertyPrivacy::Private {
                enclosing_class: Some(declaration),
            },
        );
    }

    #[test]
    fn private_tagged_template_properties_keep_distinct_tag_and_substitution_capabilities() {
        let parsed = parsed(concat!(
            "class Model { #tag = null as any; #value = 1; ",
            "run() { this.#tag`value ${this.#value}`; } }",
        ));
        let file = FileId::new(595);
        let store = registered_store(&parsed, file);
        let tagged = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TaggedTemplateExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let NodeData::TaggedTemplateExpression(expression) =
            &parsed.arena.get(tagged.node).unwrap().data
        else {
            panic!("the fixture retains one tagged template")
        };
        let tag = NodeRef::new(parsed.arena.id(), file, expression.tag);
        let tag_syntax =
            plan_direct_source_property_call_syntax(&parsed.arena, &store, tag, tagged).unwrap();
        assert_eq!(tag_syntax.name, "#tag");
        assert!(matches!(
            plan_direct_source_property_syntax(&parsed.arena, &store, tag),
            Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::MemberCall(call)
            )) if call == tagged
        ));

        let substitution = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::PropertyAccessExpression(access) = &record.data else {
                    return None;
                };
                matches!(
                    &parsed.arena.get(access.name)?.data,
                    NodeData::PrivateIdentifier(identifier) if identifier.text == "#value"
                )
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let substitution_syntax =
            plan_direct_source_property_syntax(&parsed.arena, &store, substitution).unwrap();
        assert_eq!(substitution_syntax.name, "#value");
    }

    #[test]
    fn private_fields_methods_and_accessors_report_exact_ts18013() {
        for (index, (source, spelling, static_side)) in [
            (
                "class Model { #value = 1; } const result = model.#value;",
                "#value",
                false,
            ),
            (
                "class Model { static #value = 1; } const result = Model.#value;",
                "#value",
                true,
            ),
            (
                "class Model { #run() {} } const result = model.#run;",
                "#run",
                false,
            ),
            (
                "class Model { static #run() {} } const result = Model.#run;",
                "#run",
                true,
            ),
            (
                concat!(
                    "class Model { get #value(): number { return 1; } ",
                    "set #value(next) {} } const result = model.#value;",
                ),
                "#value",
                false,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parsed(source);
            let file = FileId::new(581 + u32::try_from(index).unwrap());
            let access = property_access(&parsed, file);
            let (mut context, owner, instance, value) = published_class(&parsed, file, "Model");
            let receiver_type = if static_side { value } else { instance };
            let error = context.store().intrinsic_bootstrap().unwrap().error_type;
            let syntax =
                plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
            let receiver = identifier_receiver(&syntax, owner);
            let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

            let checked = check_direct_source_property(
                context.store_mut_for_test(),
                None,
                &plan,
                receiver_type,
            )
            .unwrap();

            assert_eq!(checked.type_, error, "{source}");
            assert!(context.store().symbol_node_links(access).is_none());
            let (_, bound) = context.file(file).unwrap();
            let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();
            let diagnostic = prepare_source_property_diagnostic(
                context.store(),
                &host,
                context.global_types(),
                context.options(),
                checked.diagnostics.first().unwrap(),
            )
            .unwrap();
            assert_eq!(diagnostic.diagnostic.code(), 18_013, "{source}");
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!(
                    "Property '{spelling}' is not accessible outside class 'Model' because it has a private identifier."
                ),
                "{source}",
            );
            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert_eq!(
                check_direct_source_property(
                    context.store_mut_for_test(),
                    None,
                    &plan,
                    receiver_type,
                ),
                Ok(checked),
                "{source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn inherited_private_field_diagnostics_name_the_exact_declaring_class() {
        let parsed = parsed(concat!(
            "class Base { #value = 1; } ",
            "class Derived extends Base {} ",
            "const result = derived.#value;",
        ));
        let file = FileId::new(590);
        let access = property_access(&parsed, file);
        let (mut context, owner, instance, _) = published_class(&parsed, file, "Derived");
        let syntax =
            plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
        let receiver = identifier_receiver(&syntax, owner);
        let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

        let checked =
            check_direct_source_property(context.store_mut_for_test(), None, &plan, instance)
                .unwrap();

        let (_, bound) = context.file(file).unwrap();
        let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();
        let diagnostic = prepare_source_property_diagnostic(
            context.store(),
            &host,
            context.global_types(),
            context.options(),
            &checked.diagnostics.into_iter().next().unwrap(),
        )
        .unwrap();
        assert_eq!(diagnostic.diagnostic.code(), 18_013);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Property '#value' is not accessible outside class 'Base' because it has a private identifier.",
        );
    }

    #[test]
    fn private_class_members_do_not_hide_public_or_missing_property_behavior() {
        for (index, (source, member, missing)) in [
            (
                "class Model { #secret = 1; value = 2; } const result = model.value;",
                "value",
                false,
            ),
            (
                concat!(
                    "class Base { value = 2; } ",
                    "class Model extends Base { #secret = 1; } ",
                    "const result = model.value;",
                ),
                "value",
                false,
            ),
            (
                "class Model { #secret = 1; } const result = model.missing;",
                "missing",
                true,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parsed(source);
            let file = FileId::new(591 + u32::try_from(index).unwrap());
            let access = property_access(&parsed, file);
            let (mut context, owner, instance, _) = published_class(&parsed, file, "Model");
            let syntax =
                plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
            let receiver = identifier_receiver(&syntax, owner);
            let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

            let checked =
                check_direct_source_property(context.store_mut_for_test(), None, &plan, instance)
                    .unwrap();

            if missing {
                assert_eq!(
                    checked.type_,
                    context.store().intrinsic_bootstrap().unwrap().error_type,
                );
                assert_eq!(
                    checked
                        .diagnostics
                        .into_iter()
                        .next()
                        .unwrap()
                        .private_owner,
                    None
                );
                assert!(context.store().symbol_node_links(access).is_none());
            } else {
                assert_eq!(
                    checked.type_,
                    context.store().intrinsic_bootstrap().unwrap().number_type,
                );
                assert!(checked.diagnostics.is_empty());
                let symbol = context
                    .store()
                    .type_payload(instance)
                    .and_then(|record| record.data().structured())
                    .and_then(|structured| structured.members)
                    .and_then(|members| context.store().symbol_table(members))
                    .and_then(|members| members.get_source(member))
                    .unwrap();
                assert_eq!(
                    context
                        .store()
                        .symbol_node_links(access)
                        .and_then(|links| links.resolved_symbol),
                    Some(symbol),
                );
            }
        }
    }

    #[test]
    fn poisoned_private_member_links_reject_before_access_publication() {
        let parsed = parsed("class Model { #value = 1; } const result = model.#value;");
        let file = FileId::new(594);
        let access = property_access(&parsed, file);
        let (mut context, owner, instance, _) = published_class(&parsed, file, "Model");
        let property = context
            .store()
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| {
                members
                    .iter()
                    .find_map(|(name, symbol)| name.is_private_identifier().then_some(symbol))
            })
            .unwrap();
        let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            },
        ));
        let syntax =
            plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
        let receiver = identifier_receiver(&syntax, owner);
        let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

        assert_eq!(
            check_direct_source_property(context.store_mut_for_test(), None, &plan, instance),
            Err(SourcePropertyError::InvalidCache(access)),
        );
        assert!(context.store().type_node_links(access).is_none());
        assert!(context.store().symbol_node_links(access).is_none());
    }

    #[test]
    fn keyword_visibility_diagnostics_reject_a_forged_access_reason() {
        let parsed = parsed("class Model { protected value = 1; } const result = model.value;");
        let file = FileId::new(598);
        let access = property_access(&parsed, file);
        let (mut context, owner, instance, _) = published_class(&parsed, file, "Model");
        let syntax =
            plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
        let plan = finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, owner))
            .unwrap();
        let checked =
            check_direct_source_property(context.store_mut_for_test(), None, &plan, instance)
                .unwrap();
        let deferred = checked.diagnostics.into_iter().next().unwrap();
        let Some(ClassPropertyAccessDiagnostic::Protected { property, owner }) =
            deferred.accessibility
        else {
            panic!("the external read retains the protected member's declaring class")
        };
        assert_eq!(
            checked.type_,
            context.store().intrinsic_bootstrap().unwrap().number_type
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(property),
        );
        let (_, bound) = context.file(file).unwrap();
        let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();
        let forged = SourcePropertyDiagnostic {
            accessibility: Some(ClassPropertyAccessDiagnostic::Private { property, owner }),
            ..deferred
        };
        assert_eq!(
            prepare_source_property_diagnostic(
                context.store(),
                &host,
                context.global_types(),
                context.options(),
                &forged,
            ),
            Err(SourcePropertyError::InvalidCache(plan.name_node)),
        );
        assert_eq!(
            prepare_source_property_diagnostic(
                context.store(),
                &host,
                context.global_types(),
                context.options(),
                &deferred,
            )
            .unwrap()
            .diagnostic
            .code(),
            2445,
        );
    }

    #[test]
    fn class_static_properties_preserve_declared_and_inherited_symbols() {
        for (index, (source, owner_name, member_name)) in [
            (
                "class Model { static count: number; } const result = Model.count;",
                "Model",
                "count",
            ),
            (
                "class Model { static count = 123; } const result = Model.count;",
                "Model",
                "count",
            ),
            (
                concat!(
                    "class Base { static count: number; } ",
                    "class Derived extends Base {} ",
                    "const result = Derived.count;",
                ),
                "Derived",
                "count",
            ),
            (
                concat!(
                    "class Base { static count = 123; } ",
                    "class Derived extends Base {} ",
                    "const result = Derived.count;",
                ),
                "Derived",
                "count",
            ),
            (
                "class Model {} const result = Model.prototype;",
                "Model",
                "prototype",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parsed(source);
            let file = FileId::new(522 + u32::try_from(index).unwrap());
            let access = property_access(&parsed, file);
            let (mut context, owner, instance, value) = published_class(&parsed, file, owner_name);
            let member = context
                .store()
                .type_payload(value)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.members)
                .and_then(|members| context.store().symbol_table(members))
                .and_then(|members| members.get_source(member_name))
                .unwrap();
            let expected = if member_name == "prototype" {
                instance
            } else {
                context.store().intrinsic_bootstrap().unwrap().number_type
            };
            let syntax =
                plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
            let receiver = PlannedExpression::new(
                syntax.receiver(),
                PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                    resolved_symbol: owner,
                    value_symbol: owner,
                    kind: PlannedIdentifierReadKind::DeclaredValue,
                }),
            );
            let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

            for _ in 0..2 {
                assert_eq!(
                    check_direct_source_property(context.store_mut_for_test(), None, &plan, value,),
                    Ok(CheckedSourceProperty {
                        type_: expected,
                        diagnostics: Vec::new(),
                    }),
                    "source {source}",
                );
            }
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(access)
                    .and_then(|links| links.resolved_symbol),
                Some(member),
            );
        }
    }

    #[test]
    fn class_static_methods_are_exact_member_call_callees() {
        let parsed = parsed(concat!(
            "class Base { static ready(): any {} } ",
            "class Derived extends Base {} ",
            "const result = Derived.ready();",
        ));
        let file = FileId::new(525);
        let access = property_access(&parsed, file);
        let call = NodeRef::new(
            parsed.arena.id(),
            file,
            parsed.arena.get(access.node).unwrap().parent.unwrap(),
        );
        let (mut context, owner, _, value) = published_class(&parsed, file, "Derived");
        let method = context
            .store()
            .type_payload(value)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("ready"))
            .unwrap();
        let method_type = context
            .store()
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let syntax =
            plan_direct_source_property_call_syntax(&parsed.arena, context.store(), access, call)
                .unwrap();
        let name = syntax.name_node();
        let receiver = PlannedExpression::new(
            syntax.receiver(),
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: owner,
                value_symbol: owner,
                kind: PlannedIdentifierReadKind::DeclaredValue,
            }),
        );
        let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

        assert!(plan.is_call_callee_for(call, name));
        assert_eq!(
            check_direct_source_property(context.store_mut_for_test(), None, &plan, value),
            Ok(CheckedSourceProperty {
                type_: method_type,
                diagnostics: Vec::new(),
            }),
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(method),
        );
    }

    #[test]
    fn paired_class_accessor_reads_publish_the_shared_symbol_cold_and_warm() {
        let parsed = parsed(concat!(
            "class Model { get value(): number { return 1; } set value(next) {} } ",
            "const model = new Model(); const result = model.value;",
        ));
        let file = FileId::new(530);
        let access = property_access(&parsed, file);
        let (mut context, owner, instance, _) = published_class(&parsed, file, "Model");
        let accessor = context
            .store()
            .type_payload(instance)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("value"))
            .unwrap();
        assert_eq!(
            context.store().symbol(accessor).unwrap().flags(),
            SymbolFlags::ACCESSOR,
        );
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let syntax =
            plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
        let receiver = PlannedExpression::new(
            syntax.receiver(),
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: owner,
                value_symbol: owner,
                kind: PlannedIdentifierReadKind::DeclaredValue,
            }),
        );
        let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

        for _ in 0..2 {
            assert_eq!(
                check_direct_source_property(context.store_mut_for_test(), None, &plan, instance),
                Ok(CheckedSourceProperty {
                    type_: number,
                    diagnostics: Vec::new(),
                }),
            );
        }
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(accessor),
        );
        assert_eq!(
            context
                .store()
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(number),
        );
    }

    #[test]
    fn poisoned_class_accessor_links_fail_before_access_publication() {
        let parsed = parsed(concat!(
            "class Model { get value(): number { return 1; } set value(next) {} } ",
            "const model = new Model(); const result = model.value;",
        ));
        let file = FileId::new(531);
        let access = property_access(&parsed, file);
        let (mut context, owner, instance, _) = published_class(&parsed, file, "Model");
        let accessor = context
            .store()
            .type_payload(instance)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("value"))
            .unwrap();
        let poison = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            accessor,
            ValueSymbolLinks {
                resolved_type: Some(poison),
                ..ValueSymbolLinks::default()
            },
        ));
        let syntax =
            plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
        let receiver = PlannedExpression::new(
            syntax.receiver(),
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: owner,
                value_symbol: owner,
                kind: PlannedIdentifierReadKind::DeclaredValue,
            }),
        );
        let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

        assert_eq!(
            check_direct_source_property(context.store_mut_for_test(), None, &plan, instance),
            Err(SourcePropertyError::InvalidCache(access)),
        );
        assert!(context.store().type_node_links(access).is_none());
        assert!(context.store().symbol_node_links(access).is_none());
    }

    #[test]
    fn optional_class_static_properties_include_undefined_without_losing_readonly() {
        let parsed = parsed(concat!(
            "class Model { static readonly count?: number; } ",
            "const result = Model.count;",
        ));
        let file = FileId::new(526);
        let access = property_access(&parsed, file);
        let (mut context, owner, _, value) = published_class(&parsed, file, "Model");
        let syntax =
            plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
        let receiver = PlannedExpression::new(
            syntax.receiver(),
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: owner,
                value_symbol: owner,
                kind: PlannedIdentifierReadKind::DeclaredValue,
            }),
        );
        let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();
        let Some(ClassStaticProperty::Present(property)) =
            resolve_class_static_property(context.store(), &plan, value).unwrap()
        else {
            panic!("expected a validated class static property")
        };
        assert!(property.optional);
        assert!(property.readonly);

        let checked =
            check_direct_source_property(context.store_mut_for_test(), None, &plan, value).unwrap();
        let TypeData::Union(union) = context.store().type_payload(checked.type_).unwrap().data()
        else {
            panic!("strict optional class properties must include undefined")
        };
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert!(union.union.types.contains(&bootstrap.number_type));
        assert!(union.union.types.contains(&bootstrap.undefined_type));
    }

    #[test]
    fn poisoned_class_static_member_cache_fails_before_access_publication() {
        let parsed = parsed("class Model { static count: number; } const result = Model.count;");
        let file = FileId::new(527);
        let access = property_access(&parsed, file);
        let (mut context, owner, _, value) = published_class(&parsed, file, "Model");
        let property = context
            .store()
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| context.store().symbol_table(exports))
            .and_then(|exports| exports.get_source("count"))
            .unwrap();
        let poison = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(poison),
                ..ValueSymbolLinks::default()
            },
        ));
        let syntax =
            plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
        let receiver = PlannedExpression::new(
            syntax.receiver(),
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: owner,
                value_symbol: owner,
                kind: PlannedIdentifierReadKind::DeclaredValue,
            }),
        );
        let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

        assert_eq!(
            check_direct_source_property(context.store_mut_for_test(), None, &plan, value),
            Err(SourcePropertyError::InvalidCache(access)),
        );
        assert!(context.store().type_node_links(access).is_none());
        assert!(context.store().symbol_node_links(access).is_none());
    }

    #[test]
    fn missing_enum_value_properties_recover_without_publishing_a_symbol() {
        let parsed = parsed("enum Status { Ready = 1 } const result = Status.Missing;");
        let file = FileId::new(520);
        let access = property_access(&parsed, file);
        let (mut store, owner, value_type, _, _) = published_enum(&parsed, file);
        let error_type = store.intrinsic_bootstrap().unwrap().error_type;
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let receiver = PlannedExpression::new(
            syntax.receiver(),
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: owner,
                value_symbol: owner,
                kind: PlannedIdentifierReadKind::DeclaredValue,
            }),
        );
        let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

        let checked = check_direct_source_property(&mut store, None, &plan, value_type).unwrap();
        assert_eq!(checked.type_, error_type);
        assert!(!checked.diagnostics.is_empty());
        assert!(store.symbol_node_links(access).is_none());
    }

    #[test]
    fn namespace_exports_publish_the_exact_value_symbol_and_type() {
        let parsed = parsed("const result = namespace.value;");
        let file = FileId::new(515);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let (object, _, member, alias) = namespace_object(
            &mut store,
            "value",
            string,
            SymbolFlags::BLOCK_SCOPED_VARIABLE,
        );
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan = finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, alias))
            .unwrap();

        for _ in 0..2 {
            assert_eq!(
                check_direct_source_property(&mut store, None, &plan, object),
                Ok(CheckedSourceProperty {
                    type_: string,
                    diagnostics: Vec::new(),
                }),
            );
        }
        assert_eq!(
            store
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(member),
        );
        assert_eq!(
            store
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(string),
        );
    }

    #[test]
    fn namespace_function_exports_remain_valid_property_call_callees() {
        let parsed = parsed("const result = namespace.value();");
        let file = FileId::new(516);
        let access = property_access(&parsed, file);
        let call = NodeRef::new(
            parsed.arena.id(),
            file,
            parsed.arena.get(access.node).unwrap().parent.unwrap(),
        );
        let mut store = registered_store(&parsed, file);
        let any = store.intrinsic_bootstrap().unwrap().any_type;
        let (object, _, member, alias) =
            namespace_object(&mut store, "value", any, SymbolFlags::FUNCTION);
        let syntax =
            plan_direct_source_property_call_syntax(&parsed.arena, &store, access, call).unwrap();
        let name = syntax.name_node();
        let plan = finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, alias))
            .unwrap();

        assert!(plan.is_call_callee_for(call, name));
        assert_eq!(
            check_direct_source_property(&mut store, None, &plan, object),
            Ok(CheckedSourceProperty {
                type_: any,
                diagnostics: Vec::new(),
            }),
        );
        assert_eq!(
            store
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(member),
        );
    }

    #[test]
    fn direct_module_namespace_function_exports_preserve_callable_member_identity() {
        let parsed = parsed("Foo.bar();");
        let file = FileId::new(532);
        let access = property_access(&parsed, file);
        let call = NodeRef::new(
            parsed.arena.id(),
            file,
            parsed.arena.get(access.node).unwrap().parent.unwrap(),
        );
        let mut store = registered_store(&parsed, file);
        let any = store.intrinsic_bootstrap().unwrap().any_type;
        let (object, module, member, _) =
            namespace_object(&mut store, "bar", any, SymbolFlags::FUNCTION);
        let syntax =
            plan_direct_source_property_call_syntax(&parsed.arena, &store, access, call).unwrap();
        let name = syntax.name_node();
        let receiver = PlannedExpression::new(
            syntax.receiver(),
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: module,
                value_symbol: module,
                kind: PlannedIdentifierReadKind::DeclaredValue,
            }),
        );
        let plan = finish_direct_source_property_plan(&syntax, receiver).unwrap();

        assert!(plan.is_call_callee_for(call, name));
        for _ in 0..2 {
            assert_eq!(
                check_direct_source_property(&mut store, None, &plan, object),
                Ok(CheckedSourceProperty {
                    type_: any,
                    diagnostics: Vec::new(),
                }),
            );
        }
        assert_eq!(
            store
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(member),
        );
    }

    #[test]
    fn namespace_import_projections_keep_the_original_export_symbol() {
        let parsed = parsed("const result = namespace.value;");
        let file = FileId::new(518);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let (_, _, member, alias) = namespace_object(
            &mut store,
            "value",
            string,
            SymbolFlags::BLOCK_SCOPED_VARIABLE,
        );
        let projection = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source("value"),
            ))
            .unwrap();
        assert!(store.set_value_symbol_links(
            projection,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        let projected_members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(projected_members, EscapedName::source("value"), projection),
            Some(None),
        );
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            Some(projected_members),
            Some(vec![projection]),
            None,
            None,
            None,
        ));
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan = finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, alias))
            .unwrap();

        assert_eq!(
            check_direct_source_property(&mut store, None, &plan, object),
            Ok(CheckedSourceProperty {
                type_: string,
                diagnostics: Vec::new(),
            }),
        );
        assert_eq!(
            store
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(member),
        );
    }

    #[test]
    fn namespace_reexport_properties_keep_the_alias_and_read_the_final_value() {
        let parsed = parsed("const result = namespace.value;");
        let file = FileId::new(521);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let (_, module, target, namespace_alias) = namespace_object(
            &mut store,
            "value",
            string,
            SymbolFlags::BLOCK_SCOPED_VARIABLE,
        );
        let export_alias = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::ALIAS,
                EscapedName::source("value"),
            ))
            .unwrap();
        assert!(store.set_symbol_relationships(export_alias, None, None, Some(module), None));
        assert!(store.set_alias_symbol_links(
            export_alias,
            AliasSymbolLinks {
                immediate_target: Some(target),
                alias_target: AliasTargetState::Resolved(target),
                ..AliasSymbolLinks::default()
            },
        ));
        let exports = store.symbol(module).unwrap().exports().unwrap();
        assert_eq!(
            store.insert_symbol(exports, EscapedName::source("value"), export_alias),
            Some(Some(target)),
        );

        let projection = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source("value"),
            ))
            .unwrap();
        assert!(store.set_value_symbol_links(
            projection,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        let members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(members, EscapedName::source("value"), projection),
            Some(None),
        );
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            Some(members),
            Some(vec![projection]),
            None,
            None,
            None,
        ));
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan = finish_direct_source_property_plan(
            &syntax,
            identifier_receiver(&syntax, namespace_alias),
        )
        .unwrap();

        for _ in 0..2 {
            assert_eq!(
                check_direct_source_property(&mut store, None, &plan, object),
                Ok(CheckedSourceProperty {
                    type_: string,
                    diagnostics: Vec::new(),
                }),
            );
        }
        assert_eq!(
            store
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(export_alias),
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Cold and warm reads share the same real producer and restored caches.
    fn namespace_wrapper_property_cache_changes_fail_before_publication() {
        use crate::semantic::{
            CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
            CanonicalModuleResolutionMode, CanonicalResolvedModuleInput,
        };
        let importer = parsed(
            "import * as ns from './producer.cjs'; export const copied = ns; const picked = ns.default;",
        );
        let producer = parsed("export const value: number = 1;");
        let importer_file = FileId::new(14_010);
        let producer_file = FileId::new(14_011);
        let sources = [
            (importer_file, &importer, "\"/consumer\""),
            (producer_file, &producer, "\"/producer\""),
        ];
        let mut binder = CanonicalBinder::new();
        for (file, source, path) in sources {
            binder
                .bind_source_file_with_facts(
                    &source.arena,
                    source.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
        }
        for (file, source, _) in sources {
            binder
                .bind_typescript_declaration_slice(&source.arena, file)
                .unwrap();
        }
        let import = importer
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ImportDeclaration(import) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(
                    importer.arena.id(),
                    importer_file,
                    import.module_specifier,
                ))
            })
            .unwrap();
        let mut context = CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            [
                (importer_file, &importer.arena),
                (producer_file, &producer.arena),
            ]
            .into_iter()
            .collect(),
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    import,
                    CanonicalResolvedModuleInput::new(
                        producer_file,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                ),
            ]),
        )
        .unwrap();
        context.check_source_file(importer_file).unwrap();
        let binding = importer
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::NamespaceImport).then_some(NodeRef::new(
                    importer.arena.id(),
                    importer_file,
                    node,
                ))
            })
            .unwrap();
        let alias = context
            .file(importer_file)
            .unwrap()
            .1
            .symbol(binding)
            .unwrap();
        let receiver_type = context
            .store()
            .value_symbol_links(alias)
            .unwrap()
            .resolved_type
            .unwrap();
        let wrapper = context
            .store()
            .source_file_namespace_wrapper(alias)
            .cloned()
            .unwrap();
        let bare = context
            .store()
            .value_symbol_links(wrapper.source.module)
            .unwrap()
            .resolved_type
            .unwrap();
        let access = property_access(&importer, importer_file);
        let syntax =
            plan_direct_source_property_syntax(&importer.arena, context.store(), access).unwrap();
        let plan = finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, alias))
            .unwrap();
        let members = context
            .store()
            .type_payload(receiver_type)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .members
            .unwrap();
        let default = context
            .store()
            .symbol_table(members)
            .unwrap()
            .get_source("default")
            .unwrap();
        let alias_value = context.store().value_symbol_links(alias).cloned().unwrap();
        let default_alias = context
            .store()
            .alias_symbol_links(wrapper.default)
            .cloned()
            .unwrap();
        let default_value = context
            .store()
            .value_symbol_links(default)
            .cloned()
            .unwrap();
        let exports = context
            .store()
            .export_type_links(wrapper.namespace)
            .cloned()
            .unwrap();
        let original_type = context.store().type_node_links(access).cloned().unwrap();
        let original_symbol = context.store().symbol_node_links(access).cloned().unwrap();
        let state = |store: &CanonicalTypeMapperStore| {
            (
                (
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                ),
                (
                    store.type_node_links(access).cloned(),
                    store.symbol_node_links(access).cloned(),
                ),
                (
                    store.value_symbol_links(alias).cloned(),
                    store.alias_symbol_links(wrapper.default).cloned(),
                    store.value_symbol_links(default).cloned(),
                    store.export_type_links(wrapper.namespace).cloned(),
                    store.type_payload(receiver_type).unwrap().symbol(),
                ),
                store
                    .source_file_namespace_identity(wrapper.namespace)
                    .cloned(),
            )
        };
        for warm in [false, true] {
            for poison in 0..5 {
                let store = context.store_mut_for_test();
                assert!(store.set_type_node_links(
                    access,
                    if warm {
                        original_type.clone()
                    } else {
                        TypeNodeLinks::default()
                    }
                ));
                assert!(store.set_symbol_node_links(
                    access,
                    if warm {
                        original_symbol.clone()
                    } else {
                        SymbolNodeLinks::default()
                    }
                ));
                match poison {
                    0 => assert!(store.set_type_symbol(receiver_type, None)),
                    1 => {
                        let mut links = default_alias.clone();
                        links.alias_target = AliasTargetState::Resolved(wrapper.namespace);
                        assert!(store.set_alias_symbol_links(wrapper.default, links));
                    }
                    2 => {
                        let mut links = default_value.clone();
                        links.resolved_type =
                            Some(store.intrinsic_bootstrap().unwrap().number_type);
                        assert!(store.set_value_symbol_links(default, links));
                    }
                    3 => {
                        let mut links = alias_value.clone();
                        links.resolved_type = Some(bare);
                        assert!(store.set_value_symbol_links(alias, links));
                    }
                    4 => {
                        let mut links = exports.clone();
                        links.target = Some(wrapper.namespace);
                        assert!(store.set_export_type_links(wrapper.namespace, links));
                    }
                    _ => unreachable!(),
                }
                let before = state(store);
                assert_eq!(
                    check_direct_source_property(store, None, &plan, receiver_type),
                    Err(SourcePropertyError::InvalidCache(access)),
                    "warm={warm}, poison={poison}"
                );
                assert_eq!(state(store), before, "warm={warm}, poison={poison}");
                assert!(store.set_type_symbol(receiver_type, Some(wrapper.namespace)));
                assert!(store.set_alias_symbol_links(wrapper.default, default_alias.clone()));
                assert!(store.set_value_symbol_links(default, default_value.clone()));
                assert!(store.set_value_symbol_links(alias, alias_value.clone()));
                assert!(store.set_export_type_links(wrapper.namespace, exports.clone()));
                assert_eq!(
                    check_direct_source_property(store, None, &plan, receiver_type),
                    Ok(CheckedSourceProperty {
                        type_: bare,
                        diagnostics: Vec::new()
                    })
                );
                assert_eq!(
                    store.symbol_node_links(access).unwrap().resolved_symbol,
                    Some(wrapper.default)
                );
            }
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Read the copied value directly without replaying its import.
    fn namespace_wrapper_invariant_review_copied_reads_reject_changed_owners() {
        use crate::semantic::{
            CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
            CanonicalModuleResolutionMode, CanonicalResolvedModuleInput,
        };
        let importer = parsed(concat!(
            "import * as ns from './producer.cjs'; export const copied = ns; ",
            "const named = copied.value; const fallback = copied.default;",
        ));
        let producer = parsed("export const value: number = 1;");
        let importer_file = FileId::new(14_020);
        let producer_file = FileId::new(14_021);
        let sources = [
            (importer_file, &importer, "\"/consumer\""),
            (producer_file, &producer, "\"/producer\""),
        ];
        let mut binder = CanonicalBinder::new();
        for (file, source, path) in sources {
            binder
                .bind_source_file_with_facts(
                    &source.arena,
                    source.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
        }
        for (file, source, _) in sources {
            binder
                .bind_typescript_declaration_slice(&source.arena, file)
                .unwrap();
        }
        let import = importer
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ImportDeclaration(import) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(
                    importer.arena.id(),
                    importer_file,
                    import.module_specifier,
                ))
            })
            .unwrap();
        let mut context = CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            sources
                .map(|(file, source, _)| (file, &source.arena))
                .into_iter()
                .collect(),
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    import,
                    CanonicalResolvedModuleInput::new(
                        producer_file,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                ),
            ]),
        )
        .unwrap();
        context.check_source_file(importer_file).unwrap();
        assert!(context.diagnostics().is_empty());
        let bound = context.file(importer_file).unwrap().1;
        let importer_module = bound.symbol(bound.source_file()).unwrap();
        let copied = context
            .store()
            .symbol(importer_module)
            .unwrap()
            .exports()
            .and_then(|exports| context.store().symbol_table(exports))
            .unwrap()
            .get_source("copied")
            .unwrap();
        let receiver_type = context
            .store()
            .value_symbol_links(copied)
            .unwrap()
            .resolved_type
            .unwrap();
        let namespace = context
            .store()
            .type_payload(receiver_type)
            .unwrap()
            .symbol()
            .unwrap();
        let wrapper = context
            .store()
            .source_file_namespace_wrapper_for_module(namespace)
            .cloned()
            .unwrap();
        assert!(
            !context
                .store()
                .symbol(copied)
                .unwrap()
                .flags()
                .intersects(SymbolFlags::ALIAS | SymbolFlags::MODULE)
        );
        let accesses = importer.arena.iter().filter_map(|(node, record)| {
            (record.kind == SyntaxKind::PropertyAccessExpression).then_some(NodeRef::new(
                importer.arena.id(),
                importer_file,
                node,
            ))
        });
        let mut failures = Vec::new();
        for access in accesses {
            let syntax =
                plan_direct_source_property_syntax(&importer.arena, context.store(), access)
                    .unwrap();
            let plan =
                finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, copied))
                    .unwrap();
            let original_type = context.store().type_node_links(access).cloned().unwrap();
            let original_symbol = context.store().symbol_node_links(access).cloned().unwrap();
            let state = |store: &CanonicalTypeMapperStore| {
                (
                    [store.type_len(), store.symbol_len(), store.mapper_len()],
                    store.type_node_links(access).cloned(),
                    store.symbol_node_links(access).cloned(),
                    store.type_payload(receiver_type).unwrap().symbol(),
                    store.source_file_namespace_identity(namespace).cloned(),
                    store.value_symbol_links(copied).cloned(),
                    store.relation_state_snapshot(),
                )
            };
            for warm in [false, true] {
                for owner in [None, Some(wrapper.source.module)] {
                    let store = context.store_mut_for_test();
                    assert!(store.set_type_node_links(
                        access,
                        if warm {
                            original_type.clone()
                        } else {
                            TypeNodeLinks::default()
                        }
                    ));
                    assert!(store.set_symbol_node_links(
                        access,
                        if warm {
                            original_symbol.clone()
                        } else {
                            SymbolNodeLinks::default()
                        }
                    ));
                    assert!(store.set_type_symbol(receiver_type, owner));
                    let before = state(store);
                    let result = check_direct_source_property(store, None, &plan, receiver_type);
                    if result.is_ok() || state(store) != before {
                        failures.push(format!(
                            "property={}, warm={warm}, owner={owner:?}, result={result:?}, unchanged={}",
                            syntax.name, state(store) == before,
                        ));
                    }
                    assert!(store.set_type_symbol(receiver_type, Some(namespace)));
                    assert!(store.set_type_node_links(access, original_type.clone()));
                    assert!(store.set_symbol_node_links(access, original_symbol.clone()));
                    assert_eq!(
                        check_direct_source_property(store, None, &plan, receiver_type).unwrap(),
                        CheckedSourceProperty {
                            type_: original_type.resolved_type.unwrap(),
                            diagnostics: Vec::new(),
                        }
                    );
                }
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    }

    #[test]
    fn namespace_alias_cache_mismatches_fail_before_access_publication() {
        let parsed = parsed("const result = namespace.value;");
        let file = FileId::new(517);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let (object, _, _, alias) = namespace_object(
            &mut store,
            "value",
            string,
            SymbolFlags::BLOCK_SCOPED_VARIABLE,
        );
        let other = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::VALUE_MODULE,
                EscapedName::source("\"/project/other.ts\""),
            ))
            .unwrap();
        assert!(store.set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                immediate_target: Some(other),
                alias_target: AliasTargetState::Resolved(other),
                ..AliasSymbolLinks::default()
            },
        ));
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan = finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, alias))
            .unwrap();

        assert_eq!(
            check_direct_source_property(&mut store, None, &plan, object),
            Err(SourcePropertyError::InvalidCache(access)),
        );
        assert!(store.type_node_links(access).is_none());
        assert!(store.symbol_node_links(access).is_none());
    }

    #[test]
    fn existing_error_receivers_preserve_error_type_without_another_diagnostic() {
        let parsed = parsed("const result = missing.value;");
        let file = FileId::new(514);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let error = store.intrinsic_bootstrap().unwrap().error_type;
        let receiver_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source("missing"),
            ))
            .unwrap();
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan = finish_direct_source_property_plan(
            &syntax,
            identifier_receiver(&syntax, receiver_symbol),
        )
        .unwrap();

        assert_eq!(
            check_direct_source_property(&mut store, None, &plan, error),
            Ok(CheckedSourceProperty {
                type_: error,
                diagnostics: Vec::new(),
            }),
        );
        assert_eq!(
            store
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(error),
        );
        assert!(store.symbol_node_links(access).is_none());
    }

    #[test]
    fn missing_own_properties_recover_with_error_type_and_a_deferred_diagnostic() {
        let parsed = parsed("const result = object.value;");
        let file = FileId::new(503);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let (string, error) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.error_type)
        };
        let (object, property) = property_object(&mut store, "other", string, false);
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, property))
                .unwrap();

        for _ in 0..2 {
            let checked = check_direct_source_property(&mut store, None, &plan, object).unwrap();
            assert_eq!(checked.type_, error);
            let diagnostic = checked.diagnostics.into_iter().next().unwrap();
            assert_eq!(diagnostic.receiver_type, object);
            assert_eq!(diagnostic.missing_type, None);
            assert_eq!(diagnostic.suggestion, None);
        }
        assert_eq!(
            store
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(error),
        );
        assert!(store.symbol_node_links(access).is_none());
    }

    #[test]
    fn optional_properties_include_undefined_and_publish_the_property_symbol() {
        let parsed = parsed("const result = object.value;");
        let file = FileId::new(504);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let (string, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.undefined_or_missing_type)
        };
        let (object, property) = property_object(&mut store, "value", string, true);
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, property))
                .unwrap();

        let checked = check_direct_source_property(&mut store, None, &plan, object).unwrap();
        let TypeData::Union(union) = store.type_payload(checked.type_).unwrap().data() else {
            panic!("strict optional property reads must produce a union")
        };
        assert!(union.union.types.contains(&string));
        assert!(union.union.types.contains(&undefined));
        assert_eq!(
            store
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(property),
        );
    }

    #[test]
    fn optional_property_chains_remove_nullish_receivers_and_restore_undefined() {
        let parsed = parsed("const result = object?.value;");
        let file = FileId::new(513);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let (string, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.undefined_type)
        };
        let (object, property) = property_object(&mut store, "value", string, false);
        let nullable = store
            .alloc_union_type(ObjectFlags::NONE, vec![undefined, object])
            .unwrap();
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, property))
                .unwrap();

        let checked = check_direct_source_property(&mut store, None, &plan, nullable).unwrap();
        let TypeData::Union(union) = store.type_payload(checked.type_).unwrap().data() else {
            panic!("optional property access must preserve undefined")
        };
        assert!(union.union.types.contains(&string));
        assert!(union.union.types.contains(&undefined));
        assert_eq!(
            store
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(property),
        );
    }

    #[test]
    fn chained_property_receivers_preserve_each_member_identity() {
        let parsed = parsed("const result = object.inner.value;");
        let file = FileId::new(512);
        let mut accesses = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::PropertyAccessExpression).then_some((
                    record.range.end,
                    NodeRef::new(parsed.arena.id(), file, node),
                ))
            })
            .collect::<Vec<_>>();
        accesses.sort_by_key(|(end, _)| *end);
        let [(_, inner_access), (_, outer_access)] = accesses.as_slice() else {
            panic!("expected inner and outer property accesses")
        };
        let mut store = registered_store(&parsed, file);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let (inner_object, value_property) = property_object(&mut store, "value", string, false);
        let (outer_object, inner_property) =
            property_object(&mut store, "inner", inner_object, false);
        let receiver_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
                EscapedName::source("object"),
            ))
            .unwrap();

        let inner_syntax =
            plan_direct_source_property_syntax(&parsed.arena, &store, *inner_access).unwrap();
        let inner_plan = finish_direct_source_property_plan(
            &inner_syntax,
            identifier_receiver(&inner_syntax, receiver_symbol),
        )
        .unwrap();
        let outer_syntax =
            plan_direct_source_property_syntax(&parsed.arena, &store, *outer_access).unwrap();
        let outer_plan = finish_direct_source_property_plan(
            &outer_syntax,
            PlannedExpression::new(
                *inner_access,
                PlannedExpressionKind::Property(Box::new(inner_plan.clone())),
            ),
        )
        .unwrap();

        assert_eq!(
            check_direct_source_property(&mut store, None, &inner_plan, outer_object),
            Ok(CheckedSourceProperty {
                type_: inner_object,
                diagnostics: Vec::new(),
            }),
        );
        assert_eq!(
            check_direct_source_property(&mut store, None, &outer_plan, inner_object),
            Ok(CheckedSourceProperty {
                type_: string,
                diagnostics: Vec::new(),
            }),
        );
        assert_eq!(
            store
                .symbol_node_links(*inner_access)
                .and_then(|links| links.resolved_symbol),
            Some(inner_property),
        );
        assert_eq!(
            store
                .symbol_node_links(*outer_access)
                .and_then(|links| links.resolved_symbol),
            Some(value_property),
        );
    }

    #[test]
    fn member_calls_and_poisoned_caches_fail_closed() {
        let call = parsed("const result = object.value();");
        let call_file = FileId::new(506);
        let call_access = property_access(&call, call_file);
        let call_store = registered_store(&call, call_file);
        assert!(matches!(
            plan_direct_source_property_syntax(&call.arena, &call_store, call_access),
            Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::MemberCall(_)
            ))
        ));

        let poisoned = parsed("const result = object.value;");
        let poisoned_file = FileId::new(507);
        let poisoned_access = property_access(&poisoned, poisoned_file);
        let mut poisoned_store = registered_store(&poisoned, poisoned_file);
        assert!(poisoned_store.set_type_node_links(
            poisoned_access,
            TypeNodeLinks {
                outer_type_parameters: Some(Vec::new()),
                ..TypeNodeLinks::default()
            },
        ));
        assert_eq!(
            plan_direct_source_property_syntax(&poisoned.arena, &poisoned_store, poisoned_access,),
            Err(SourcePropertyError::InvalidCache(poisoned_access))
        );
    }

    #[test]
    fn member_call_capability_retains_the_exact_call_and_name() {
        let parsed = parsed(concat!(
            "const first = object.value(); ",
            "const second = object.other();",
        ));
        let file = FileId::new(509);
        let mut accesses = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::PropertyAccessExpression).then_some((
                    record.range.start,
                    NodeRef::new(parsed.arena.id(), file, node),
                ))
            })
            .collect::<Vec<_>>();
        accesses.sort_by_key(|(start, _)| *start);
        let [(_, first_access), (_, second_access)] = accesses.as_slice() else {
            panic!("expected two property accesses")
        };
        let first_call = NodeRef::new(
            parsed.arena.id(),
            file,
            parsed.arena.get(first_access.node).unwrap().parent.unwrap(),
        );
        let second_call = NodeRef::new(
            parsed.arena.id(),
            file,
            parsed
                .arena
                .get(second_access.node)
                .unwrap()
                .parent
                .unwrap(),
        );
        let mut store = registered_store(&parsed, file);
        let receiver_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source("object"),
            ))
            .unwrap();

        assert_eq!(
            plan_direct_source_property_syntax(&parsed.arena, &store, *first_access),
            Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::MemberCall(first_call),
            ))
        );
        assert_eq!(
            plan_direct_source_property_call_syntax(
                &parsed.arena,
                &store,
                *first_access,
                second_call,
            ),
            Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::MemberCall(second_call),
            ))
        );

        let syntax = plan_direct_source_property_call_syntax(
            &parsed.arena,
            &store,
            *first_access,
            first_call,
        )
        .unwrap();
        let name = syntax.name_node();
        let plan = finish_direct_source_property_plan(
            &syntax,
            identifier_receiver(&syntax, receiver_symbol),
        )
        .unwrap();
        assert!(plan.is_call_callee_for(first_call, name));
        assert!(!plan.is_call_callee_for(second_call, name));
        assert!(!plan.is_call_callee_for(first_call, syntax.receiver()));
    }

    #[test]
    fn unsupported_union_receivers_fail_before_access_cache_publication() {
        let parsed = parsed("const result = object.value;");
        let file = FileId::new(508);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let union = store.literal_union_type(&[string, number], None).unwrap();
        let receiver_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source("object"),
            ))
            .unwrap();
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan = finish_direct_source_property_plan(
            &syntax,
            identifier_receiver(&syntax, receiver_symbol),
        )
        .unwrap();

        assert!(matches!(
            check_direct_source_property(&mut store, None, &plan, union),
            Err(SourcePropertyError::Union {
                node,
                error: UnionPropertyError::UnsupportedConstituent(type_),
            }) if node == access && [string, number].contains(&type_)
        ));
        assert!(store.type_node_links(access).is_none());
        assert!(store.symbol_node_links(access).is_none());
    }

    #[test]
    fn live_wrong_access_type_rejects_after_safe_union_memo_and_retries_warm() {
        let parsed = parsed("const result = object.value;");
        let file = FileId::new(510);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (left, _) = property_object(&mut store, "value", string, false);
        let (right, _) = property_object(&mut store, "value", number, false);
        let mut constituents = vec![left, right];
        constituents.sort();
        let union = store
            .alloc_union_type(ObjectFlags::NONE, constituents)
            .unwrap();
        let receiver_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source("object"),
            ))
            .unwrap();
        assert!(store.set_type_node_links(
            access,
            TypeNodeLinks {
                resolved_type: Some(string),
                ..TypeNodeLinks::default()
            },
        ));
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan = finish_direct_source_property_plan(
            &syntax,
            identifier_receiver(&syntax, receiver_symbol),
        )
        .unwrap();

        assert_eq!(
            check_direct_source_property(&mut store, None, &plan, union),
            Err(SourcePropertyError::InvalidCache(access))
        );
        let TypeData::Union(union_data) = store.type_payload(union).unwrap().data() else {
            panic!("fixture must remain a union")
        };
        let cache = union_data
            .union
            .property_cache
            .expect("the safe union-property memo survives access-cache rejection");
        assert!(
            store
                .symbol_table(cache)
                .is_some_and(|cache| cache.get_source("value").is_some())
        );
        assert_eq!(
            store
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(string)
        );
        assert!(store.symbol_node_links(access).is_none());
        let cold = (
            store.type_len(),
            store.symbol_store().checker_created_symbol_len(),
            store.symbol_store().symbol_table_len(),
        );

        assert_eq!(
            check_direct_source_property(&mut store, None, &plan, union),
            Err(SourcePropertyError::InvalidCache(access))
        );
        assert_eq!(
            (
                store.type_len(),
                store.symbol_store().checker_created_symbol_len(),
                store.symbol_store().symbol_table_len(),
            ),
            cold
        );
        assert_eq!(
            store
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(string)
        );
        assert!(store.symbol_node_links(access).is_none());
    }
}
