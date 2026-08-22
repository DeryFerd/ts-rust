//! Exact local ambient function overload groups.
//!
//! The binder owns declaration grouping and order. This provider retains that
//! order, publishes one anonymous callable object with one signature per
//! declaration, and validates the complete reverse-map/cache graph before the
//! shared call resolver may observe it.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost, SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    links::{
        DecoratorSignatureState, EffectsSignatureState, ResolvedSignatureState, SignatureLinks,
        ValueSymbolLinks,
    },
    signatures::SignatureFlags,
    source_callables::{
        SourceCallableError, SourceCallablePlan, SourceCallableReturnPlan,
        cached_annotation_identity, plan_source_ambient_overload_declaration, valid_optional_type,
    },
    store::{
        PreparedSourceOverloadParameter, PreparedSourceOverloadPublication,
        PreparedSourceOverloadSignature, SourceNodeParent,
    },
    type_records::{ConstrainedTypeData, TypeCacheState, TypeData},
    types::{ObjectFlags, TypeFlags},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceOverloadPlan {
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) declarations: Vec<SourceCallablePlan>,
    pub(super) array_targets: Option<CanonicalArrayTargets>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResolvedSourceOverloadSignature {
    pub(super) parameter_types: Vec<TypeId>,
    pub(super) return_type: TypeId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct MaterializedSourceOverload {
    pub(super) type_: TypeId,
    pub(super) signatures: Box<[SignatureId]>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum StoredSourceOverloadValidation {
    NotSourceOverload,
    Valid(Vec<TypeId>),
    Malformed,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceOverloadInvariant {
    EmptyGroup,
    Group(NodeRef),
    Cache(NodeRef),
    Publication(NodeRef),
    Capacity(NodeRef),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceOverloadError {
    Unsupported(NodeRef),
    Callable(SourceCallableError),
    Literal(LiteralTypeCacheError),
    Invariant(SourceOverloadInvariant),
}

impl SourceOverloadError {
    pub(super) const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(node) => Some(node),
            Self::Callable(error) => error.node(),
            Self::Literal(_) => None,
            Self::Invariant(
                SourceOverloadInvariant::Group(node)
                | SourceOverloadInvariant::Cache(node)
                | SourceOverloadInvariant::Publication(node)
                | SourceOverloadInvariant::Capacity(node),
            ) => Some(node),
            Self::Invariant(SourceOverloadInvariant::EmptyGroup) => None,
        }
    }
}

impl From<SourceCallableError> for SourceOverloadError {
    fn from(error: SourceCallableError) -> Self {
        Self::Callable(error)
    }
}

impl From<LiteralTypeCacheError> for SourceOverloadError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::Literal(error)
    }
}

pub(super) fn plan_source_ambient_overload_group(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner_symbol: SemanticSymbolId,
    declarations: &[NodeRef],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceOverloadPlan, SourceOverloadError> {
    let Some(first) = declarations.first().copied() else {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::EmptyGroup,
        ));
    };
    if declarations.len() < 2
        || declarations
            .iter()
            .enumerate()
            .any(|(index, declaration)| declarations[..index].contains(declaration))
    {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(first),
        ));
    }
    if declarations
        .iter()
        .any(|declaration| !declaration.is_for(first.arena, first.file))
    {
        return Err(SourceOverloadError::Unsupported(first));
    }
    let owner = store
        .symbol(owner_symbol)
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(first),
        ))?;
    if owner.flags() != SymbolFlags::FUNCTION
        || owner.declarations() != Some(declarations)
        || owner.value_declaration() != Some(first)
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
    {
        return Err(SourceOverloadError::Unsupported(first));
    }
    if owner.check_flags() != CheckFlags::NONE
        || owner.members().is_some()
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
    {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(first),
        ));
    }
    reject_conflicting_top_level_variables(host, first, owner.name().as_utf8())?;
    let mut plans = Vec::with_capacity(declarations.len());
    for declaration in declarations {
        let bound = host
            .bound_file(*declaration)
            .ok_or(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Group(*declaration),
            ))?;
        if bound.symbol(*declaration) != Some(owner_symbol) {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Group(*declaration),
            ));
        }
        if bound.local_symbol(*declaration).is_some() {
            return Err(SourceOverloadError::Unsupported(*declaration));
        }
        plans.push(plan_source_ambient_overload_declaration(
            store,
            host,
            *declaration,
            owner_symbol,
            declarations,
            array_targets,
        )?);
    }
    let plan = SourceOverloadPlan {
        owner_symbol,
        declarations: plans,
        array_targets,
    };
    validate_plan_state(store, &plan)?;
    Ok(plan)
}

fn reject_conflicting_top_level_variables(
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner_name: Option<&str>,
) -> Result<(), SourceOverloadError> {
    let Some(owner_name) = owner_name else {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(declaration),
        ));
    };
    let Some((arena, bound)) = host.source(declaration) else {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(declaration),
        ));
    };
    let source = bound.source_file();
    let Some(NodeData::SourceFile(source)) = arena.get(source.node).map(|node| &node.data) else {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(declaration),
        ));
    };
    for statement in &source.statements.nodes {
        let Some(NodeData::VariableStatement(statement)) =
            arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        let Some(NodeData::VariableDeclarationList(list)) =
            arena.get(statement.declaration_list).map(|node| &node.data)
        else {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Group(declaration),
            ));
        };
        for variable in &list.declarations.nodes {
            let Some(NodeData::VariableDeclaration(variable_data)) =
                arena.get(*variable).map(|node| &node.data)
            else {
                return Err(SourceOverloadError::Invariant(
                    SourceOverloadInvariant::Group(declaration),
                ));
            };
            let Some(NodeData::Identifier(name)) =
                arena.get(variable_data.name).map(|node| &node.data)
            else {
                continue;
            };
            if name.text == owner_name {
                return Err(SourceOverloadError::Unsupported(NodeRef::new(
                    declaration.arena,
                    declaration.file,
                    *variable,
                )));
            }
        }
    }
    Ok(())
}

pub(super) fn prepare_source_overload_publication(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    plan: &SourceOverloadPlan,
    resolved: &[ResolvedSourceOverloadSignature],
) -> Result<PreparedSourceOverloadPublication, SourceOverloadError> {
    let first = plan
        .declarations
        .first()
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::EmptyGroup,
        ))?;
    if plan.declarations.len() != resolved.len() {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Publication(first.declaration),
        ));
    }
    let strict = store
        .intrinsic_bootstrap()
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Capacity(first.declaration),
        ))?
        .options
        .strict_null_checks;
    let undefined = store
        .intrinsic_bootstrap()
        .expect("the bootstrap was checked")
        .undefined_type;
    let optional_count = plan
        .declarations
        .iter()
        .flat_map(|declaration| &declaration.parameters)
        .filter(|parameter| parameter.optional)
        .count();
    let mut prepared_types = store.prepare_type_query_types_with_global_types(
        &[],
        &[],
        &[],
        optional_count,
        0,
        global_types,
    )?;
    let mut signatures = Vec::with_capacity(plan.declarations.len());
    for (declaration, resolved) in plan.declarations.iter().zip(resolved) {
        if declaration.parameters.len() != resolved.parameter_types.len()
            || store.type_payload(resolved.return_type).is_none()
        {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Publication(declaration.declaration),
            ));
        }
        let Some((return_annotation, return_null_literal_identity)) =
            declaration.return_type.annotation_identity()
        else {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Publication(declaration.declaration),
            ));
        };
        if cached_annotation_identity(store, return_annotation, return_null_literal_identity)
            != Some(resolved.return_type)
        {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Cache(return_annotation),
            ));
        }
        let mut parameters = Vec::with_capacity(declaration.parameters.len());
        for (parameter, base_type) in declaration.parameters.iter().zip(&resolved.parameter_types) {
            let (annotation, annotation_null_literal_identity) = parameter.annotation_identity();
            if cached_annotation_identity(store, annotation, annotation_null_literal_identity)
                != Some(*base_type)
            {
                return Err(SourceOverloadError::Invariant(
                    SourceOverloadInvariant::Cache(annotation),
                ));
            }
            let call_type = if strict && parameter.optional {
                store.literal_union_type_prepared_with_global_types(
                    global_types,
                    &[*base_type, undefined],
                    None,
                    &mut prepared_types,
                )?
            } else {
                *base_type
            };
            if (parameter.optional
                && if strict {
                    !valid_optional_type(store, plan.array_targets, *base_type, call_type)
                } else {
                    call_type != *base_type
                })
                || (!parameter.optional && call_type != *base_type)
            {
                return Err(SourceOverloadError::Invariant(
                    SourceOverloadInvariant::Cache(parameter.declaration),
                ));
            }
            parameters.push(PreparedSourceOverloadParameter {
                declaration: parameter.declaration,
                symbol: parameter.symbol,
                annotation,
                annotation_null_literal_identity,
                base_type: *base_type,
                call_type,
                optional: parameter.optional,
            });
        }
        signatures.push(PreparedSourceOverloadSignature {
            declaration: declaration.declaration,
            parameters,
            flags: declaration.flags,
            min_argument_count: declaration.min_argument_count,
            return_annotation,
            return_annotation_null_literal_identity: return_null_literal_identity,
            return_type: resolved.return_type,
        });
    }
    Ok(PreparedSourceOverloadPublication {
        owner_symbol: plan.owner_symbol,
        signatures,
        array_targets: plan.array_targets,
    })
}

pub(super) fn publish_source_overload_batch(
    store: &mut CanonicalTypeMapperStore,
    plans: &[SourceOverloadPlan],
    prepared: &[PreparedSourceOverloadPublication],
) -> Result<Vec<MaterializedSourceOverload>, SourceOverloadError> {
    let first = plans
        .first()
        .and_then(|plan| plan.declarations.first())
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::EmptyGroup,
        ))?;
    if plans.len() != prepared.len() {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Publication(first.declaration),
        ));
    }
    let mut cold = Vec::new();
    for (plan, publication) in plans.iter().zip(prepared) {
        if !prepared_matches_plan(plan, publication) {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Publication(first.declaration),
            ));
        }
        match source_overload_state(store, plan)? {
            SourceOverloadState::Cold => cold.push(publication.clone()),
            SourceOverloadState::Resolved { .. } => {}
        }
    }
    let cold_len = cold.len();
    let published =
        store
            .publish_source_overload_batch(cold)
            .ok_or(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Publication(first.declaration),
            ))?;
    if published.len() != cold_len {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Publication(first.declaration),
        ));
    }
    let mut result = Vec::with_capacity(plans.len());
    for plan in plans {
        let SourceOverloadState::Resolved { type_, signatures } =
            source_overload_state(store, plan)?
        else {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Publication(first.declaration),
            ));
        };
        result.push(MaterializedSourceOverload { type_, signatures });
    }
    Ok(result)
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SourceOverloadState {
    Cold,
    Resolved {
        type_: TypeId,
        signatures: Box<[SignatureId]>,
    },
}

fn validate_plan_state(
    store: &CanonicalTypeMapperStore,
    plan: &SourceOverloadPlan,
) -> Result<(), SourceOverloadError> {
    source_overload_state(store, plan).map(|_| ())
}

fn source_overload_state(
    store: &CanonicalTypeMapperStore,
    plan: &SourceOverloadPlan,
) -> Result<SourceOverloadState, SourceOverloadError> {
    let first = plan
        .declarations
        .first()
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::EmptyGroup,
        ))?;
    let owner_links = store.value_symbol_links(plan.owner_symbol);
    let declarations_cold = plan.declarations.iter().all(|declaration| {
        store
            .signature_links(declaration.declaration)
            .is_none_or(|links| links == &SignatureLinks::default())
            && declaration.parameters.iter().all(|parameter| {
                store
                    .value_symbol_links(parameter.symbol)
                    .is_none_or(|links| links == &ValueSymbolLinks::default())
            })
    });
    let maps_cold = store
        .source_overload_type_for_owner(plan.owner_symbol)
        .is_none()
        && store
            .source_callable_type_for_owner(plan.owner_symbol)
            .is_none()
        && plan.declarations.iter().all(|declaration| {
            store
                .source_overload_type_for_declaration(declaration.declaration)
                .is_none()
                && store
                    .source_callable_type_for_declaration(declaration.declaration)
                    .is_none()
        })
        && !store.source_overload_provenance_claims(
            plan.owner_symbol,
            &plan
                .declarations
                .iter()
                .map(|declaration| declaration.declaration)
                .collect::<Vec<_>>(),
        );
    if owner_links.is_none_or(|links| links == &ValueSymbolLinks::default())
        && declarations_cold
        && maps_cold
    {
        return Ok(SourceOverloadState::Cold);
    }
    let type_ = owner_links
        .and_then(|links| {
            (links
                == &ValueSymbolLinks {
                    resolved_type: links.resolved_type,
                    ..ValueSymbolLinks::default()
                })
                .then_some(links.resolved_type)
                .flatten()
        })
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Cache(first.declaration),
        ))?;
    if store.source_overload_type_for_owner(plan.owner_symbol) != Some(type_)
        || !matches!(
            validate_stored_source_overload(store, type_),
            StoredSourceOverloadValidation::Valid(_)
        )
    {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Cache(first.declaration),
        ));
    }
    let provenance =
        store
            .source_overload_provenance(type_)
            .ok_or(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Cache(first.declaration),
            ))?;
    if provenance.owner_symbol != plan.owner_symbol
        || provenance.array_targets != plan.array_targets
        || provenance.signatures.len() != plan.declarations.len()
    {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Cache(first.declaration),
        ));
    }
    for (declaration, row) in plan.declarations.iter().zip(&provenance.signatures) {
        let Some((return_annotation, return_null_literal_identity)) =
            declaration.return_type.annotation_identity()
        else {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Cache(declaration.declaration),
            ));
        };
        if row.declaration != declaration.declaration
            || row.flags != declaration.flags
            || row.return_annotation != return_annotation
            || row.return_annotation_null_literal_identity != return_null_literal_identity
            || row.parameters.len() != declaration.parameters.len()
        {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Cache(declaration.declaration),
            ));
        }
        for (parameter, stored) in declaration.parameters.iter().zip(&row.parameters) {
            let (annotation, null_literal_identity) = parameter.annotation_identity();
            if stored.declaration != parameter.declaration
                || stored.symbol != parameter.symbol
                || stored.annotation != annotation
                || stored.annotation_null_literal_identity != null_literal_identity
                || stored.optional != parameter.optional
            {
                return Err(SourceOverloadError::Invariant(
                    SourceOverloadInvariant::Cache(parameter.declaration),
                ));
            }
        }
    }
    Ok(SourceOverloadState::Resolved {
        type_,
        signatures: provenance
            .signatures
            .iter()
            .map(|signature| signature.signature)
            .collect(),
    })
}

fn prepared_matches_plan(
    plan: &SourceOverloadPlan,
    prepared: &PreparedSourceOverloadPublication,
) -> bool {
    plan.owner_symbol == prepared.owner_symbol
        && plan.array_targets == prepared.array_targets
        && plan.declarations.len() == prepared.signatures.len()
        && plan
            .declarations
            .iter()
            .zip(&prepared.signatures)
            .all(|(plan, prepared)| {
                plan.declaration == prepared.declaration
                    && plan.flags == prepared.flags
                    && plan.min_argument_count == prepared.min_argument_count
                    && plan.parameters.len() == prepared.parameters.len()
                    && plan
                        .parameters
                        .iter()
                        .zip(&prepared.parameters)
                        .all(|(plan, prepared)| {
                            let (annotation, null_literal_identity) = plan.annotation_identity();
                            plan.declaration == prepared.declaration
                                && plan.symbol == prepared.symbol
                                && annotation == prepared.annotation
                                && null_literal_identity
                                    == prepared.annotation_null_literal_identity
                                && plan.optional == prepared.optional
                        })
                    && matches!(plan.return_type, SourceCallableReturnPlan::Annotated { .. })
            })
}

pub(super) fn validate_stored_source_overload(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredSourceOverloadValidation {
    let provenance = store.source_overload_provenance(type_);
    let malformed_or_not = || {
        if provenance.is_some() {
            StoredSourceOverloadValidation::Malformed
        } else {
            StoredSourceOverloadValidation::NotSourceOverload
        }
    };
    let Some(record) = store.type_payload(type_) else {
        return malformed_or_not();
    };
    let Some(owner_symbol) = record.symbol() else {
        return malformed_or_not();
    };
    let Some(owner) = store.symbol(owner_symbol) else {
        return malformed_or_not();
    };
    let Some(provenance) = provenance else {
        return if store.source_overload_type_for_owner(owner_symbol) == Some(type_) {
            StoredSourceOverloadValidation::Malformed
        } else {
            StoredSourceOverloadValidation::NotSourceOverload
        };
    };
    let declarations = provenance
        .signatures
        .iter()
        .map(|signature| signature.declaration)
        .collect::<Vec<_>>();
    let signatures = provenance
        .signatures
        .iter()
        .map(|signature| signature.signature)
        .collect::<Vec<_>>();
    let TypeData::Object(object) = record.data() else {
        return StoredSourceOverloadValidation::Malformed;
    };
    if provenance.owner_symbol != owner_symbol
        || provenance.signatures.len() < 2
        || owner.flags() != SymbolFlags::FUNCTION
        || owner.check_flags() != CheckFlags::NONE
        || owner.declarations() != Some(declarations.as_slice())
        || owner.value_declaration() != declarations.first().copied()
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
        || store.source_overload_type_for_owner(owner_symbol) != Some(type_)
        || store.value_symbol_links(owner_symbol)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
        || record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.alias().is_some()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.members.is_some()
        || object.structured.properties.is_some()
        || object.structured.signatures.as_deref() != Some(signatures.as_slice())
        || object.structured.call_signature_count != signatures.len()
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || provenance.array_targets.is_some_and(|targets| {
            store.type_payload(targets.array_type()).is_none()
                || store.type_payload(targets.readonly_array_type()).is_none()
        })
    {
        return StoredSourceOverloadValidation::Malformed;
    }

    let mut edges = Vec::new();
    let Some(strict_null_checks) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.options.strict_null_checks)
    else {
        return StoredSourceOverloadValidation::Malformed;
    };
    let mut unique_signatures = HashSet::with_capacity(signatures.len());
    let mut unique_parameters = HashSet::new();
    for row in &provenance.signatures {
        if !unique_signatures.insert(row.signature)
            || store.source_node_kind(row.declaration) != Some(SyntaxKind::FunctionDeclaration)
            || store.source_overload_type_for_declaration(row.declaration) != Some(type_)
            || store.source_overload_type_for_signature(row.signature) != Some(type_)
            || store.signature_links(row.declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(row.signature),
                    effects_signature: EffectsSignatureState::Unresolved,
                    decorator_signature: DecoratorSignatureState::Unresolved,
                })
            || store.function_signature_return_annotation(row.signature)
                != Some((
                    row.return_annotation,
                    row.return_annotation_null_literal_identity,
                ))
            || cached_annotation_identity(
                store,
                row.return_annotation,
                row.return_annotation_null_literal_identity,
            ) != Some(row.return_type)
        {
            return StoredSourceOverloadValidation::Malformed;
        }
        let Some(signature) = store.signature(row.signature) else {
            return StoredSourceOverloadValidation::Malformed;
        };
        let parameter_symbols = row
            .parameters
            .iter()
            .map(|parameter| parameter.symbol)
            .collect::<Vec<_>>();
        let parameter_types = row
            .parameters
            .iter()
            .map(|parameter| parameter.call_type)
            .collect::<Vec<_>>();
        if row.flags.bits() & !SignatureFlags::HAS_LITERAL_TYPES.bits() != 0
            || signature.flags() != row.flags
            || signature.declaration() != Some(row.declaration)
            || !signature.type_parameters().is_empty()
            || signature.this_parameter().is_some()
            || signature.parameters() != parameter_symbols.as_slice()
            || signature.resolved_return_type() != Some(row.return_type)
            || signature.resolved_type_predicate().is_some()
            || signature.min_argument_count() < 0
            || usize::try_from(signature.min_argument_count())
                .map_or(true, |minimum| minimum > row.parameters.len())
            || signature.resolved_min_argument_count() != -1
            || signature.target().is_some()
            || signature.mapper().is_some()
            || signature.isolated_signature_type().is_some()
            || signature.composite().is_some()
            || store.callable_signature_parameter_types(row.signature)
                != Some(parameter_types.as_slice())
        {
            return StoredSourceOverloadValidation::Malformed;
        }
        let minimum =
            usize::try_from(signature.min_argument_count()).expect("the minimum was validated");
        let mut optional_seen = false;
        for (index, parameter) in row.parameters.iter().enumerate() {
            let Some(symbol) = store.symbol(parameter.symbol) else {
                return StoredSourceOverloadValidation::Malformed;
            };
            if !unique_parameters.insert(parameter.symbol)
                || symbol.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                || symbol.check_flags() != CheckFlags::NONE
                || symbol.declarations() != Some(&[parameter.declaration])
                || symbol.value_declaration() != Some(parameter.declaration)
                || symbol.members().is_some()
                || symbol.exports().is_some()
                || symbol.parent().is_some()
                || symbol.export_symbol().is_some()
                || store.get_merged_symbol(parameter.symbol) != Some(parameter.symbol)
                || store.source_node_kind(parameter.declaration) != Some(SyntaxKind::Parameter)
                || store.source_node_parent(parameter.declaration)
                    != Some(SourceNodeParent::Parent(row.declaration))
                || cached_annotation_identity(
                    store,
                    parameter.annotation,
                    parameter.annotation_null_literal_identity,
                ) != Some(parameter.base_type)
                || store.value_symbol_links(parameter.symbol)
                    != Some(&ValueSymbolLinks {
                        resolved_type: Some(parameter.call_type),
                        ..ValueSymbolLinks::default()
                    })
                || parameter.optional
                    && if strict_null_checks {
                        !valid_optional_type(
                            store,
                            provenance.array_targets,
                            parameter.base_type,
                            parameter.call_type,
                        )
                    } else {
                        parameter.call_type != parameter.base_type
                    }
                || !parameter.optional && parameter.call_type != parameter.base_type
                || optional_seen && !parameter.optional
                || parameter.optional != (index >= minimum)
            {
                return StoredSourceOverloadValidation::Malformed;
            }
            optional_seen |= parameter.optional;
            edges.push(parameter.base_type);
            if parameter.call_type != parameter.base_type {
                edges.push(parameter.call_type);
            }
        }
        edges.push(row.return_type);
    }
    StoredSourceOverloadValidation::Valid(edges)
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::parse_source_file;

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
        SourceCheckError, TypeNodeLinks, bootstrap::UnionReduction,
    };

    #[test]
    fn later_bad_callable_provider_preflights_before_overload_publication() {
        let ready = concat!(
            "declare function ready(value: number): number;\n",
            "declare function ready(value: string): string;\n",
        );
        for (index, source) in [
            format!(
                "{ready}{}",
                concat!(
                    "declare function bad(",
                    "this: object, value: number",
                    "): number;\n",
                )
            ),
            format!(
                "{ready}{}",
                concat!(
                    "const bad = (",
                    "{ value }: { value: number }",
                    "): number => 1;\n",
                )
            ),
            format!(
                "{ready}{}",
                concat!(
                    "const bad: (value: number) => void = ",
                    "(value: number) => {};\n",
                )
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(&source);
            assert!(parsed.diagnostics.is_empty());
            let file = FileId::new(2_494 + u32::try_from(index).unwrap());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!(
                            "\"/project/overload-provider-boundary-{index}.ts\""
                        )),
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
                [(file, &parsed.arena)].into_iter().collect(),
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            let mut declarations = parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    matches!(&record.data, NodeData::FunctionDeclaration(_)).then_some((
                        record.range.start,
                        NodeRef::new(parsed.arena.id(), file, node),
                    ))
                })
                .collect::<Vec<_>>();
            declarations.sort_by_key(|(start, _)| *start);
            let [(_, first), (_, second), ..] = declarations.as_slice() else {
                panic!("fixture must retain the ordered overload group")
            };
            let ready = [*first, *second];
            let owner = context
                .file(file)
                .unwrap()
                .1
                .symbol(*first)
                .and_then(|symbol| context.store().get_merged_symbol(symbol))
                .unwrap();
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().source_callable_provenance_lengths(),
            );

            for _ in 0..2 {
                assert!(matches!(
                    context.check_source_file(file),
                    Err(SourceCheckError::Unsupported(_))
                ));
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().signature_len(),
                        context.store().source_callable_provenance_lengths(),
                    ),
                    before
                );
                assert!(context.store().value_symbol_links(owner).is_none());
                assert!(
                    context
                        .store()
                        .source_overload_type_for_owner(owner)
                        .is_none()
                );
                assert!(
                    !context
                        .store()
                        .source_overload_provenance_claims(owner, ready.as_slice())
                );
                assert!(ready.iter().all(|declaration| {
                    context.store().signature_links(*declaration).is_none()
                        && context
                            .store()
                            .source_overload_type_for_declaration(*declaration)
                            .is_none()
                }));
                assert!(declarations.iter().all(|(_, declaration)| {
                    context.store().signature_links(*declaration).is_none()
                }));
            }
        }
    }

    #[test]
    fn literal_signature_flag_poison_rejects_warm_recheck_before_call_publication() {
        let parsed = parse_source_file(concat!(
            "declare function f(value: number): 'broad';\n",
            "declare function f(value: 1): 'literal';\n",
            "const result: 'literal' = f(1);\n",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(2_497);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/overload-flag-poison.ts\""),
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
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let declaration =
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(&record.data, NodeData::FunctionDeclaration(_))
                        .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
        let call = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(&record.data, NodeData::CallExpression(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();

        context.check_source_file(file).unwrap();

        let owner = context
            .file(file)
            .unwrap()
            .1
            .symbol(declaration)
            .and_then(|symbol| context.store().get_merged_symbol(symbol))
            .unwrap();
        let callable = context
            .store()
            .source_overload_type_for_owner(owner)
            .unwrap();
        let provenance = context
            .store()
            .source_overload_provenance(callable)
            .unwrap();
        let [broad, literal] = provenance.signatures.as_ref() else {
            panic!("fixture must retain two overload signatures")
        };
        assert_eq!(broad.flags, SignatureFlags::NONE);
        assert_eq!(literal.flags, SignatureFlags::HAS_LITERAL_TYPES);
        assert_eq!(
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature()),
            Some(literal.signature)
        );
        let literal_signature = literal.signature;

        assert!(
            context
                .store_mut_for_test()
                .set_signature_flags(literal_signature, SignatureFlags::NONE)
        );
        assert!(
            context
                .store_mut_for_test()
                .set_signature_links(call, SignatureLinks::default())
        );
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(call, TypeNodeLinks::default())
        );
        let before = (context.store().type_len(), context.store().signature_len());
        assert!(matches!(
            validate_stored_source_overload(context.store(), callable),
            StoredSourceOverloadValidation::Malformed
        ));

        assert!(matches!(
            context.recheck_source_file(file),
            Err(SourceCheckError::Function(_))
        ));

        assert_eq!(
            (context.store().type_len(), context.store().signature_len()),
            before
        );
        assert_eq!(
            context.store().signature_links(call),
            Some(&SignatureLinks::default())
        );
        assert_eq!(
            context.store().type_node_links(call),
            Some(&TypeNodeLinks::default())
        );
        assert_eq!(
            context
                .store()
                .signature(literal_signature)
                .unwrap()
                .flags(),
            SignatureFlags::NONE
        );
    }

    #[test]
    fn structured_poison_dirties_and_invalidates_a_warm_callable_union() {
        let parsed = parse_source_file(concat!(
            "declare function f(value: number): number;\n",
            "declare function f(value: string): string;\n",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(2_498);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/overload-union-poison.ts\""),
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
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        let declaration =
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(&record.data, NodeData::FunctionDeclaration(_))
                        .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();

        context.check_source_file(file).unwrap();

        let owner = context
            .file(file)
            .unwrap()
            .1
            .symbol(declaration)
            .and_then(|symbol| context.store().get_merged_symbol(symbol))
            .unwrap();
        let callable = context
            .store()
            .source_overload_type_for_owner(owner)
            .unwrap();
        let first_signature = context
            .store()
            .source_overload_provenance(callable)
            .unwrap()
            .signatures[0]
            .signature;
        let (undefined, string, number) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        let callable_union = context
            .store_mut_for_test()
            .expression_union_type(&[callable, undefined], UnionReduction::Literal)
            .unwrap();
        assert_eq!(
            context
                .store_mut_for_test()
                .expression_union_type(&[callable, undefined], UnionReduction::Literal),
            Ok(callable_union),
        );
        let control_union = context
            .store_mut_for_test()
            .expression_union_type(&[string, number], UnionReduction::Literal)
            .unwrap();
        assert_eq!(
            context
                .store_mut_for_test()
                .expression_union_type(&[string, number], UnionReduction::Literal),
            Ok(control_union),
        );
        assert!(!context.store().union_cache_needs_validation);

        let scans = context.store().union_cache_validation_scan_count();
        assert!(context.store_mut_for_test().set_structured_type_members(
            callable,
            None,
            None,
            Some(vec![first_signature]),
            None,
            None,
        ));
        assert!(context.store().union_cache_needs_validation);
        assert!(matches!(
            validate_stored_source_overload(context.store(), callable),
            StoredSourceOverloadValidation::Malformed
        ));
        let validation = context
            .store_mut_for_test()
            .expression_union_type(&[string, number], UnionReduction::Literal);
        assert!(
            matches!(validation, Err(LiteralTypeCacheError::InvalidCachedUnion(type_)) if type_ == callable),
            "poisoned callable union returned {validation:?}; callable={callable:?}, union={callable_union:?}"
        );
        assert_eq!(
            context.store().union_cache_validation_scan_count(),
            scans + 1
        );
    }

    #[test]
    fn missing_reverse_map_poison_fails_closed_without_republication() {
        let parsed = parse_source_file(concat!(
            "declare function f(value: number): number;\n",
            "declare function f(value: string): string;\n",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(2_499);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/overload-poison.ts\""),
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
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let mut declarations = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                matches!(&record.data, NodeData::FunctionDeclaration(_)).then_some((
                    record.range.start,
                    NodeRef::new(parsed.arena.id(), file, node),
                ))
            })
            .collect::<Vec<_>>();
        declarations.sort_by_key(|(start, _)| *start);
        let declarations = declarations
            .into_iter()
            .map(|(_, declaration)| declaration)
            .collect::<Vec<_>>();

        context.check_source_file(file).unwrap();

        let owner = context
            .file(file)
            .unwrap()
            .1
            .symbol(declarations[0])
            .and_then(|symbol| context.store().get_merged_symbol(symbol))
            .unwrap();
        let callable = context
            .store()
            .source_overload_type_for_owner(owner)
            .unwrap();
        assert!(matches!(
            validate_stored_source_overload(context.store(), callable),
            StoredSourceOverloadValidation::Valid(_)
        ));
        assert_eq!(
            context
                .store_mut_for_test()
                .replace_source_overload_type_for_declaration_for_test(declarations[1], None,),
            Some(callable)
        );
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().relation_state_snapshot(),
            context.store().signature_links(declarations[0]).cloned(),
            context.store().signature_links(declarations[1]).cloned(),
        );

        assert!(matches!(
            context.recheck_source_file(file),
            Err(SourceCheckError::Function(_))
        ));

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().relation_state_snapshot(),
                context.store().signature_links(declarations[0]).cloned(),
                context.store().signature_links(declarations[1]).cloned(),
            ),
            before
        );
        assert!(matches!(
            validate_stored_source_overload(context.store(), callable),
            StoredSourceOverloadValidation::Malformed
        ));
    }
}
