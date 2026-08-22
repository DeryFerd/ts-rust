//! Exact source integration for direct and chained property reads.
//!
//! The recursively planned receiver must already have a canonical `any` type or
//! belong to the validated own-property object domain in `relater`. Exact
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
use ts_binder::SemanticSymbolId;
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeFormatFlags, CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable,
    SymbolNodeLinks, TypeDisplayUnavailable, TypeId, TypeNodeLinks,
    bootstrap::UnionReduction,
    formatter::type_to_string_with_host_global_types_and_flags,
    member_resolution::UnionPropertyError,
    source::PlannedExpression,
    spelling::get_spelling_suggestion,
    type_records::{TypeData, TypeRecord},
    types::TypeFlags,
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
    let (type_, property, diagnostic) = if receiver_type == any || receiver_type == error_type {
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
    } else if let Some(property) = store.resolved_own_property(receiver_type, &plan.name)? {
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
    use ts_binder::{EscapedName, SemanticSymbolId, SymbolData, SymbolFlags};
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, ValueSymbolLinks,
        source::{PlannedExpressionKind, PlannedIdentifierRead, PlannedIdentifierReadKind},
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
