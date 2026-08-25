//! Exact source integration for direct and chained property reads.
//!
//! The recursively planned receiver must already have a canonical `any` type,
//! a published enum value, a validated class constructor, an imported
//! namespace, an authenticated published scalar-wrapper method, an exact global
//! array reference with a published member, or belong to the validated
//! own-property object domain in `relater`. Enum values reuse their published
//! member identities. Class
//! constructors read their validated static member tables without treating
//! construct signatures as property-only objects. Namespace reexports retain
//! their export alias while reading the final value symbol. Validated class
//! getter/setter pairs expose their shared accessor symbol. Exact
//! two-constituent
//! unions of source-declared type literals reuse the canonical union-property
//! adapter. A property missing from any union constituent recovers with
//! `errorType` plus a deferred TS2339 or stable-common-candidate TS2551
//! descriptor. Global `Object` members, comparator-dependent suggestion ties,
//! apparent/index members stay fail-closed. Optional members and optional
//! property chains retain their pinned `undefined` result. A member call is
//! admitted only when its exact
//! enclosing call grants callee capability and deliberately does not use the
//! union read adapter.

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, SemanticSymbolId, SymbolFlags};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeFormatFlags, CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable,
    SymbolNodeLinks, TypeDisplayUnavailable, TypeId, TypeNodeLinks, ValueSymbolLinks,
    bootstrap::UnionReduction,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    classes::{self, ClassHeritageMembersValidation},
    enums,
    formatter::type_to_string_with_host_global_types_and_flags,
    member_resolution::UnionPropertyError,
    relater::ResolvedOwnProperty,
    source::{PlannedExpression, PlannedExpressionKind},
    source_callables::{
        SourceCallableFamily, StoredSourceCallableValidation,
        source_arrow_owner_expando_exports_are_valid,
        source_function_owner_expando_exports_are_valid, validate_stored_source_callable,
    },
    spelling::get_spelling_suggestion,
    type_records::{TypeData, TypeRecord},
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
    InvalidCache(NodeRef),
    Union {
        node: NodeRef,
        error: UnionPropertyError,
    },
    Relation(RelationUnavailable),
    Display(TypeDisplayUnavailable),
    Capacity(NodeRef),
    MissingDiagnostic(u32),
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
        }
    }
}

impl std::error::Error for SourcePropertyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Relation(error) => Some(error),
            Self::Display(error) => Some(error),
            Self::Unsupported(_)
            | Self::InvalidCache(_)
            | Self::Union { .. }
            | Self::Capacity(_)
            | Self::MissingDiagnostic(_) => None,
        }
    }
}

/// Fully proven property syntax plus its source-planned receiver.
#[derive(Clone, Debug)]
pub(super) struct SourcePropertyPlan {
    pub(super) node: NodeRef,
    pub(super) receiver: PlannedExpression,
    name_node: NodeRef,
    name: String,
    position: SourcePropertyPosition,
    optional: bool,
}

/// The exact source position for which a property access was proven.
///
/// Retaining this capability in both syntax and finished plans prevents an
/// ordinary read plan from being repurposed as a member-call callee.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourcePropertyPosition {
    Read,
    CallCallee(NodeRef),
}

/// Property-access syntax proven before recursive source planning starts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectSourcePropertySyntax {
    node: NodeRef,
    receiver: NodeRef,
    name_node: NodeRef,
    name: String,
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

impl SourcePropertyPlan {
    pub(super) fn is_call_callee_for(&self, call: NodeRef, name: NodeRef) -> bool {
        self.name_node == name && self.position == SourcePropertyPosition::CallCallee(call)
    }

    fn is_read(&self) -> bool {
        self.position == SourcePropertyPosition::Read
    }
}

/// Unrendered pinned TS2339 recovery retained through recursive expression
/// execution until the source checker can supply its formatter host/options.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourcePropertyDiagnostic {
    name_node: NodeRef,
    receiver_type: TypeId,
    missing_type: Option<TypeId>,
    suggestion: Option<SemanticSymbolId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CheckedSourceProperty {
    pub(super) type_: TypeId,
    pub(super) diagnostic: Option<SourcePropertyDiagnostic>,
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
                && let NodeData::CallExpression(call) = &parent_record.data
                && call.expression == node.node
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
                    call_record.kind == SyntaxKind::CallExpression
                        && matches!(
                            &call_record.data,
                            NodeData::CallExpression(call) if call.expression == node.node
                        )
                });
            if !exact_call {
                return Err(SourcePropertyError::Unsupported(
                    SourcePropertyUnsupported::MemberCall(call_node),
                ));
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
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported_access(node));
    };
    if name_record.parent != Some(node.node)
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported_access(node));
    }

    let optional = if let Some(token_id) = access.question_dot_token {
        let Some(token) = arena.get(token_id) else {
            return Err(unsupported_access(node));
        };
        if token.kind != SyntaxKind::QuestionDotToken
            || token.parent != Some(node.node)
            || token.flags.0 != 0
            || token.range.start < receiver_record.range.end
            || token.range.end > name_record.range.start
            || matches!(position, SourcePropertyPosition::CallCallee(_))
        {
            return Err(unsupported_access(node));
        }
        true
    } else {
        receiver_continues_optional_chain(arena, receiver_record)
    };

    preflight_property_links(store, node)?;
    Ok(DirectSourcePropertySyntax {
        node,
        receiver,
        name_node,
        name: identifier.text.clone(),
        position,
        optional,
    })
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
        position: syntax.position,
        optional: syntax.optional,
    })
}

/// Resolves an already-typed receiver and atomically publishes the access's
/// exact symbol/type cache pair. Canonical `any` publishes only its type cache.
pub(super) fn check_direct_source_property(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<CheckedSourceProperty, SourcePropertyError> {
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
    let union_suggestion = if matches!(
        missing_union_property,
        CopiedMissingUnionProperty::Missing(_)
    ) {
        if let Some(global_types) = global_types
            && global_object_affects_missing_property(store, global_types, plan.node, &plan.name)?
        {
            return Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::ApparentObjectProperty {
                    node: plan.node,
                    receiver_type,
                },
            ));
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
                        ));
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
                }),
            ),
            NamespaceProperty::Missing => {
                return Err(SourcePropertyError::Unsupported(
                    SourcePropertyUnsupported::MissingOwnProperty {
                        node: plan.node,
                        receiver_type,
                    },
                ));
            }
        }
    } else if receiver_type == any || receiver_type == error_type {
        (receiver_type, None, None)
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
                return Err(SourcePropertyError::InvalidCache(plan.node));
            };
            let suggestion = match union_suggestion {
                CopiedSourcePropertySuggestion::Candidate(candidate) => Some(candidate),
                CopiedSourcePropertySuggestion::None => None,
                CopiedSourcePropertySuggestion::Unavailable => {
                    return Err(SourcePropertyError::InvalidCache(plan.node));
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
        None => match resolve_class_instance_accessor(store, plan, receiver_type)? {
            Some(accessor) => Some(accessor),
            None => match resolve_published_scalar_wrapper_method(
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
                )? {
                    Some(CanonicalArrayProperty::Present(property)) => Some(property),
                    Some(CanonicalArrayProperty::Missing) => None,
                    None => store.resolved_own_property(receiver_type, &plan.name)?,
                },
            },
        },
    } {
        if property.optional {
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
                let sentinel = bootstrap.undefined_or_missing_type;
                let type_ = property_union_type(
                    store,
                    global_types,
                    plan.node,
                    &[property.type_, sentinel],
                    Some(property.symbol),
                )?;
                (type_, Some(property.symbol), None)
            } else {
                (property.type_, Some(property.symbol), None)
            }
        } else {
            (property.type_, Some(property.symbol), None)
        }
    } else {
        if !plan.is_read() {
            return Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::MissingOwnProperty {
                    node: plan.node,
                    receiver_type,
                },
            ));
        }
        (
            error_type,
            None,
            Some(SourcePropertyDiagnostic {
                name_node: plan.name_node,
                receiver_type,
                missing_type: None,
                suggestion: direct_property_spelling_suggestion(store, plan, receiver_type)?,
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
    Ok(CheckedSourceProperty { type_, diagnostic })
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

/// Reads a published member from the exact global target of a canonical array.
fn resolve_published_canonical_array_property(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
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
        if global_object_affects_missing_property(store, global_types, plan.node, &plan.name)? {
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
    let requires_method_instantiation = is_method
        && store
            .type_payload(type_)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .is_some_and(|signatures| {
                signatures.iter().any(|signature| {
                    store
                        .signature(*signature)
                        .and_then(super::signatures::Signature::resolved_return_type)
                        == Some(target)
                })
            });
    let instantiation = if requires_method_instantiation {
        Some(
            super::instantiated_members::instantiate_published_generic_interface_method(
                store,
                global_types,
                receiver_type,
                symbol,
            ),
        )
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

fn resolve_class_instance_accessor(
    store: &CanonicalTypeMapperStore,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<Option<ResolvedOwnProperty>, SourcePropertyError> {
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
    let Some(symbol) = members.get_source(&plan.name) else {
        return Ok(None);
    };
    let accessor = store
        .symbol(symbol)
        .ok_or(SourcePropertyError::InvalidCache(plan.node))?;
    if !accessor.flags().intersects(SymbolFlags::ACCESSOR) {
        return Ok(None);
    }
    if classes::validate_class_heritage_members(store, receiver_type)
        != ClassHeritageMembersValidation::Valid
        || accessor.flags() != SymbolFlags::ACCESSOR
        || accessor.parent() != Some(owner)
        || accessor.name().as_utf8() != Some(plan.name.as_str())
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

    Ok(Some(ResolvedOwnProperty {
        symbol,
        type_,
        optional: false,
        readonly: accessor.check_flags().contains(CheckFlags::READONLY),
    }))
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
    let receiver_module = receiver
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
        });
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
        return Err(SourcePropertyError::InvalidCache(plan.node));
    };
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

fn global_object_affects_missing_property(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    node: NodeRef,
    name: &str,
) -> Result<bool, SourcePropertyError> {
    let structured = store
        .type_payload(global_types.object_type)
        .and_then(|record| record.data().structured())
        .ok_or(SourcePropertyError::InvalidCache(node))?;
    let Some(members) = structured.members else {
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

/// Renders the exact TS2339/TS2551 union diagnostic after recursive expression
/// execution reaches the source-owned diagnostic staging boundary.
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
    let name = match host.node(deferred.name_node) {
        Some(node) if node.kind == SyntaxKind::Identifier => match &node.data {
            NodeData::Identifier(identifier) if !identifier.text.is_empty() => {
                identifier.text.as_str()
            }
            _ => return Err(SourcePropertyError::InvalidCache(deferred.name_node)),
        },
        _ => return Err(SourcePropertyError::InvalidCache(deferred.name_node)),
    };
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
    if property.is_some() && !store.set_symbol_node_links(node, expected_symbol) {
        return Err(SourcePropertyError::InvalidCache(node));
    }
    if !store.set_type_node_links(node, expected_type) {
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
        AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, IntrinsicBootstrapOptions,
        ResolvedSignatureState, SignatureLinks,
        signatures::{ElementFlags, SignatureFlags},
        source::{PlannedExpressionKind, PlannedIdentifierRead, PlannedIdentifierReadKind},
        tuple_types::CanonicalTupleTypeRequest,
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
                diagnostic: None,
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
                diagnostic: None,
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
                diagnostic: None,
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
                        diagnostic: None,
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
                    diagnostic: None,
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
        assert_eq!(checked.diagnostic, None);
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
                        diagnostic: None,
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
                    diagnostic: None,
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
                        diagnostic: None,
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
                diagnostic: None,
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
                    diagnostic: None,
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
        assert!(checked.diagnostic.is_some());
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
                    diagnostic: None,
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
                diagnostic: None,
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
                    diagnostic: None,
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
                diagnostic: None,
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
                    diagnostic: None,
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
                diagnostic: None,
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
            let diagnostic = checked.diagnostic.unwrap();
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
                diagnostic: None,
            }),
        );
        assert_eq!(
            check_direct_source_property(&mut store, None, &outer_plan, inner_object),
            Ok(CheckedSourceProperty {
                type_: string,
                diagnostic: None,
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
