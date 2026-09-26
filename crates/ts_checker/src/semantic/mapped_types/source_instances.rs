//! Owned deferred mapped instances. The physical construction proof is separate
//! from the source request that owns an alias or node cache entry.

use super::*;
use crate::semantic::type_nodes::SourceMappedReadRequest;
use crate::semantic::keyof_types::{
    NongenericKeyofPlan, cached_nongeneric_keyof_type_with_source, plan_nongeneric_keyof_type_with_source,
    plan_source_property_object_keyof_type, resolve_nongeneric_keyof_type_with_source,
    plan_nongeneric_keyof_type_with_array_targets,
};
use crate::semantic::instantiated_members::{
    SourcePropertyObjectMemberNames, capture_source_property_object_member_names,
    resolve_property_object_alias_members_with_array_targets,
};

#[derive(Clone, Debug, Eq, PartialEq)]
enum SourceMappedOperands {
    Deferred,
    Ready {
        constraint: TypeId,
        template: TypeId,
        modifiers: TypeId,
        name: Option<TypeId>,
        modifier_names: Option<SourcePropertyObjectMemberNames>,
        constraint_plan: Option<NongenericKeyofPlan>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::semantic) struct SourceMappedInstance {
    projection: SupportedMappedAliasProjection,
    parameter: TypeId,
    original_parameter: TypeId,
    mapper: TypeMapperId,
    outer_mapper: TypeMapperId,
    local_mapper: TypeMapperId,
    key_alias: (SemanticSymbolId, Vec<TypeId>),
    key: CacheHashKey,
    operands: SourceMappedOperands,
    complete_any_request: Option<CompleteAnyRequest>,
}

#[derive(Clone, Debug)]
struct CompleteAnyRequest {
    proof: std::sync::Arc<super::super::type_nodes::SourceMappedAliasRequestProof>,
}

impl PartialEq for CompleteAnyRequest {
    fn eq(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.proof, &other.proof)
    }
}

impl Eq for CompleteAnyRequest {}

impl SourceMappedInstance {
    // Stored operand state only. This does not validate or resolve the instance.
    pub(in crate::semantic) const fn current_query_operands_ready(&self) -> bool {
        matches!(self.operands, SourceMappedOperands::Ready { .. })
    }

    // Copy one stored Selection slot. This does not authenticate its semantic role.
    pub(in crate::semantic) fn current_query_stored_selection_key(&self) -> (bool, usize, Option<TypeId>) {
        let selection = matches!(self.projection.kind, SupportedMappedAliasKind::Selection);
        let key = if selection { self.projection.arguments.get(1).copied() } else { None };
        (selection, self.projection.arguments.len(), key)
    }

    pub(in crate::semantic) const fn type_id(&self) -> TypeId {
        self.projection.type_
    }

    pub(in crate::semantic) fn permits_operand_completion(&self, next: &Self) -> bool {
        self.projection == next.projection
            && self.parameter == next.parameter
            && self.original_parameter == next.original_parameter
            && self.mapper == next.mapper
            && self.outer_mapper == next.outer_mapper
            && self.local_mapper == next.local_mapper
            && self.key_alias == next.key_alias
            && self.key == next.key
            && self.complete_any_request == next.complete_any_request
            && matches!(self.operands, SourceMappedOperands::Deferred)
            && matches!(next.operands, SourceMappedOperands::Ready { .. })
    }
}

fn object_key(
    store: &CanonicalTypeMapperStore,
    arguments: &[TypeId],
    identity: (SemanticSymbolId, &[TypeId]),
) -> Result<CacheHashKey, MappedTypeError> {
    cached_object_key(store, arguments, identity)?
        .ok_or(MappedTypeError::InvalidSymbol(identity.0))
}

fn cached_object_key(
    store: &CanonicalTypeMapperStore,
    arguments: &[TypeId],
    identity: (SemanticSymbolId, &[TypeId]),
) -> Result<Option<CacheHashKey>, MappedTypeError> {
    let symbol = store.symbol(identity.0).ok_or(MappedTypeError::InvalidSymbol(identity.0))?;
    if !symbol.flags().contains(SymbolFlags::TYPE_ALIAS)
        || store.get_merged_symbol(identity.0) != Some(identity.0)
        || arguments.iter().chain(identity.1).any(|type_| store.type_payload(*type_).is_none())
    {
        return Err(MappedTypeError::InvalidSymbol(identity.0));
    }
    Ok(store.symbol_store().assigned_global_symbol_id(identity.0)
        .map(|global| type_alias_instantiation_cache_key(arguments, Some((global, identity.1)))))
}

/// The source declaration supplies the original logical alias. Its raw alias
/// field stays on the existing declaration contract.
pub(super) fn source_mapped_target_cache_is_valid(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    alias: SemanticSymbolId,
    parameters: &[TypeId],
) -> Result<bool, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(target);
    let TypeData::Mapped(mapped) = store.type_payload(target).ok_or_else(invalid)?.data() else {
        return Err(invalid());
    };
    let declaration = mapped.declaration.ok_or_else(invalid)?;
    let links = store.type_node_links(declaration).ok_or_else(invalid)?;
    if links.resolved_type != Some(target) || mapped.object.target.is_some() || mapped.object.mapper.is_some() {
        return Err(invalid());
    }
    let TypeCacheState::Allocated(entries) = &mapped.object.instantiations else {
        return Ok(links.outer_type_parameters.is_none());
    };
    let self_key = object_key(store, parameters, (alias, parameters))?;
    if links.outer_type_parameters.as_deref() != Some(parameters)
        || store.relation_object_instantiation(target, self_key) != Some(target)
    {
        return Err(invalid());
    }
    for (key, result) in entries {
        if *key == self_key {
            continue;
        }
        let proof = store.source_mapped_instance(*result).ok_or_else(invalid)?;
        if proof.key != *key || proof.projection.type_ != *result
            || proof.projection.declared_type != target || proof.projection.alias != alias
            || proof.projection.type_parameters != parameters
            || object_key(store, &proof.projection.arguments, (proof.key_alias.0, &proof.key_alias.1))? != *key
        {
            return Err(invalid());
        }
    }
    Ok(true)
}

fn prepare_target_cache(
    store: &mut CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
) -> Result<(), MappedTypeError> {
    let target = projection.declared_type;
    let invalid = || MappedTypeError::InvalidMappedType(target);
    if !source_mapped_target_cache_is_valid(store, target, projection.alias, &projection.type_parameters)? {
        return Err(invalid());
    }
    let TypeData::Mapped(mapped) = store.type_payload(target).ok_or_else(invalid)?.data() else {
        return Err(invalid());
    };
    if matches!(mapped.object.instantiations, TypeCacheState::Allocated(_)) {
        return store.try_reserve_object_instantiations(target, 1).then_some(())
            .ok_or(MappedTypeError::Capacity);
    }
    let declaration = mapped.declaration.ok_or_else(invalid)?;
    let self_key = object_key(store, &projection.type_parameters, (projection.alias, &projection.type_parameters))?;
    let mut entries = HashMap::new();
    entries.try_reserve(2).map_err(|_| MappedTypeError::Capacity)?;
    entries.insert(self_key, target);
    let mut links = store.type_node_links(declaration).cloned().ok_or_else(invalid)?;
    links.outer_type_parameters = Some(projection.type_parameters.clone());
    if !store.set_object_instantiations(target, TypeCacheState::Allocated(entries))
        || !store.set_type_node_links(declaration, links)
    {
        return Err(invalid());
    }
    Ok(())
}

pub(in crate::semantic) fn source_mapped_target_has_owned_cache(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
) -> Result<bool, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(target);
    let Some(TypeData::Mapped(mapped)) = store.type_payload(target).map(TypeRecord::data) else {
        return Err(invalid());
    };
    let TypeCacheState::Allocated(entries) = &mapped.object.instantiations else {
        return Ok(false);
    };
    let declaration = mapped.declaration.ok_or_else(invalid)?;
    let Some(SourceNodeParent::Parent(owner)) = store.source_node_parent(declaration) else {
        return Ok(false);
    };
    let Some(alias) = source_alias_declaration_symbol(store, owner) else {
        return Ok(false);
    };
    let Some(parameters) = store.type_alias_links(alias).and_then(|links| links.type_parameters.as_deref()) else {
        return Ok(false);
    };
    let Some(self_key) = cached_object_key(store, parameters, (alias, parameters))? else {
        return if entries.values().any(|result| store.source_mapped_instance(*result).is_some()) {
            Err(invalid())
        } else {
            Ok(false)
        };
    };
    if !entries.contains_key(&self_key)
        && !entries.values().any(|result| store.source_mapped_instance(*result).is_some())
    {
        return Ok(false);
    }
    source_mapped_target_cache_is_valid(store, target, alias, parameters)
}

pub(in crate::semantic) fn source_mapped_target_node_has_owned_cache(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    target: TypeId,
) -> Result<bool, MappedTypeError> {
    if !matches!(store.type_payload(target).map(TypeRecord::data),
        Some(TypeData::Mapped(mapped)) if mapped.declaration == Some(node))
    {
        return Err(MappedTypeError::InvalidMappedType(target));
    }
    source_mapped_target_has_owned_cache(store, target)
}

pub(in crate::semantic) enum SourceMappedOperandOutcome {
    Complete,
    LimitRecovery(TypeId),
}

pub(in crate::semantic) fn source_mapped_instance_modifier_input(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
) -> Result<Option<TypeId>, MappedTypeError> {
    if store.source_mapped_instance(type_).is_none() {
        return Ok(None);
    }
    let projection = supported_mapped_alias_projection_with_source(store, type_, array_targets, source)?
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    Ok(Some(projection.arguments[0]))
}

pub(super) fn source_mapped_instance_is_deferred(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> bool {
    store.source_mapped_instance(type_)
        .is_some_and(|proof| matches!(proof.operands, SourceMappedOperands::Deferred))
}

pub(super) fn source_mapped_instance_parameter_owner(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    parameter: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
) -> Result<Option<SemanticSymbolId>, MappedTypeError> {
    let Some(proof) = store.source_mapped_instance(type_) else {
        return Ok(None);
    };
    (if source.is_none() && proof.complete_any_request.is_some() {
        pure_complete_any_projection(store, type_, array_targets)?
    } else {
        supported_mapped_alias_projection_with_source(store, type_, array_targets, source)?
    })
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    if proof.parameter != parameter {
        return Err(MappedTypeError::InvalidTypeParameter(parameter));
    }
    cached_ordinary_type_parameter_owner(store, proof.original_parameter)
        .map(Some).ok_or(MappedTypeError::InvalidTypeParameter(parameter))
}

pub(super) fn source_mapped_instance_template_parameters(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<[TypeId; 2]> {
    let proof = store.source_mapped_instance(type_)?;
    matches!(proof.operands, SourceMappedOperands::Ready { .. })
        .then_some([proof.projection.type_parameters[0], proof.original_parameter])
}

pub(super) fn source_mapped_instance_modifier_properties(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<Vec<SourceProperty>>, MappedTypeError> {
    let Some(proof) = store.source_mapped_instance(type_) else {
        return Ok(None);
    };
    let SourceMappedOperands::Ready { modifier_names: Some(names), .. } = &proof.operands else {
        return Ok(None);
    };
    names.validate(store, array_targets)
        .map_err(|error| modifier_member_error(proof.projection.arguments[0], error))?;
    Ok(Some(names.members().properties.iter().zip(names.source_properties()).map(|(symbol, source)| SourceProperty {
        symbol: *symbol, name: source.name.clone(), optional: source.optional, readonly: source.readonly,
    }).collect()))
}

pub(super) fn modifier_member_error(type_: TypeId, error: super::super::relater::RelationUnavailable) -> MappedTypeError {
    use super::super::relater::RelationUnavailable;
    match error {
        RelationUnavailable::MissingBootstrap => MappedTypeError::BootstrapUninitialized,
        RelationUnavailable::UnionValidationCapacity(_) => MappedTypeError::Capacity,
        RelationUnavailable::UnsupportedStructuredType(_) | RelationUnavailable::UnresolvedStructuredMembers(_) => {
            MappedTypeError::UnsupportedSource(type_)
        }
        RelationUnavailable::Symbol(symbol) | RelationUnavailable::InvalidSymbolMembers(symbol) => MappedTypeError::InvalidSymbol(symbol),
        _ => MappedTypeError::InvalidSource(type_),
    }
}

pub(super) fn validate_source_mapped_instance_operands(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<(), MappedTypeError> {
    let Some(proof) = store.source_mapped_instance(type_) else {
        return Ok(());
    };
    let invalid = || MappedTypeError::InvalidMappedType(type_);
    let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
    supported_mapped_alias_projection_with_source(store, type_, arrays, Some((globals, source)))?
        .ok_or_else(invalid)?;
    validate_ready_source_mapped_operands(store, proof, arrays, Some((globals, source)))
}

fn validate_ready_source_mapped_operands(
    store: &CanonicalTypeMapperStore,
    proof: &SourceMappedInstance,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
) -> Result<(), MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(proof.type_id());
    let SourceMappedOperands::Ready { constraint, modifier_names, constraint_plan, .. } = &proof.operands else {
        return Err(invalid());
    };
    let modifiers = proof.projection.arguments[0];
    if let Some(names) = modifier_names {
        names.validate(store, array_targets).map_err(|error| modifier_member_error(modifiers, error))?;
    }
    let current = match proof.projection.kind {
        SupportedMappedAliasKind::Selection => Some(proof.projection.arguments[1]),
        SupportedMappedAliasKind::Homomorphic(_) => {
            let plan = constraint_plan.as_ref().ok_or_else(invalid)?;
            match source {
                Some((globals, source)) => cached_nongeneric_keyof_type_with_source(store, plan, globals, source),
                None => cached_nongeneric_keyof_type(store, plan),
            }
                .map_err(|error| mapped_keyof_error(modifiers, error))?
        }
    };
    if current != Some(*constraint) {
        return Err(invalid());
    }
    Ok(())
}

/// Validates an owned identity without completing keys or property values.
pub(super) fn validate_owned_source_mapped_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
) -> Result<Option<SupportedMappedAliasProjection>, MappedTypeError> {
    let Some(proof) = store.source_mapped_instance(type_) else {
        return Ok(None);
    };
    if source.is_none() && proof.complete_any_request.is_some() {
        let projection = pure_complete_any_projection(store, type_, array_targets)?.ok_or(
            MappedTypeError::InvalidMappedType(type_),
        )?;
        let request = proof.complete_any_request.as_ref().ok_or(MappedTypeError::InvalidMappedType(type_))?;
        let arrays = request.proof.validate_completed_any_metadata(store, type_, None, None, None)
            .map_err(MappedTypeError::Declared)?;
        validate_ready_source_mapped_operands(store, proof, Some(arrays), None)?;
        store.validate_mapped_type_relation_endpoint_with_source(type_, Some(arrays), None)?;
        return Ok(Some(projection));
    }
    let projection = supported_mapped_alias_projection_with_source(store, type_, array_targets, source)?
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    if matches!(proof.operands, SourceMappedOperands::Ready { .. }) {
        validate_ready_source_mapped_operands(store, proof, array_targets, source)?;
        store.validate_mapped_type_relation_endpoint_with_source(type_, array_targets, source)?;
    }
    Ok(Some(projection))
}

impl CanonicalTypeMapperStore {
    /// Keeps source-less cache replay on the complete owned state boundary.
    pub(in crate::semantic) fn validate_owned_source_mapped_cache_result(
        &self,
        type_: TypeId,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> Result<bool, MappedTypeError> {
        validate_owned_source_mapped_type(self, type_, array_targets, None)
            .map(|projection| projection.is_some())
    }
}

/// Keeps direct utility validation on the instance's original constructor.
pub(super) fn validate_owned_source_mapped_alias_instantiation(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
    declared_type: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    instantiated: TypeId,
    kind: SupportedMappedAliasKind,
) -> Result<bool, MappedTypeError> {
    let Some(projection) = validate_owned_source_mapped_type(store, instantiated, None, None)? else {
        return Ok(false);
    };
    if projection.kind != kind
        || projection.alias != alias
        || projection.declared_type != declared_type
        || projection.type_parameters != parameters
        || projection.arguments != arguments
    {
        return Err(MappedTypeError::InvalidMappedType(instantiated));
    }
    Ok(true)
}

/// The source caller prepares only the reached modifier member names before
/// entering this operation. Named template values remain uninstantiated.
pub(in crate::semantic) fn resolve_source_mapped_instance_operands(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    source: &dyn ConditionalBranchSource,
) -> Result<SourceMappedOperandOutcome, MappedTypeError> {
    let Some(mut proof) = store.source_mapped_instance(type_).cloned() else {
        return Ok(SourceMappedOperandOutcome::Complete);
    };
    let invalid = || MappedTypeError::InvalidMappedType(type_);
    let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
    supported_mapped_alias_projection_with_source(store, type_, arrays, Some((globals, source)))?
        .ok_or_else(invalid)?;
    let projection = &proof.projection;
    let modifiers = projection.arguments[0];
    if matches!(proof.operands, SourceMappedOperands::Ready { .. }) {
        validate_source_mapped_instance_operands(store, type_, globals, source)?;
        return Ok(SourceMappedOperandOutcome::Complete);
    }
    let modifier_names = if super::super::object_aliases::source_property_object_projection(store, modifiers)
        .map_err(|error| modifier_member_error(modifiers, error))?.is_some()
    {
        resolve_property_object_alias_members_with_array_targets(store, modifiers, arrays)
            .map_err(|error| modifier_member_error(modifiers, error))?;
        Some(capture_source_property_object_member_names(store, modifiers, arrays)
            .map_err(|error| modifier_member_error(modifiers, error))?)
    } else {
        None
    };
    let mark = session.limit_event_mark();
    let mut constraint_plan = None;
    let constraint = match projection.kind {
        SupportedMappedAliasKind::Selection => projection.arguments[1],
        SupportedMappedAliasKind::Homomorphic(_) => {
            let plan = match &modifier_names {
                Some(names) => plan_source_property_object_keyof_type(store, names, arrays),
                None => plan_nongeneric_keyof_type_with_source(store, modifiers, globals, source),
            }
                .map_err(|error| mapped_keyof_error(modifiers, error))?;
            let result = resolve_nongeneric_keyof_type_with_source(store, &plan, session, globals, source)
                .map_err(|error| mapped_keyof_error(modifiers, error))?;
            constraint_plan = Some(plan);
            result
        }
    };
    if session.limit_event_occurred_since(mark) {
        return session.recovery_error_type()
            .map(SourceMappedOperandOutcome::LimitRecovery).ok_or_else(invalid);
    }
    let TypeData::Mapped(original) = store.type_payload(projection.declared_type)
        .ok_or_else(invalid)?.data() else {
        return Err(invalid());
    };
    let declaration = original.declaration.ok_or_else(invalid)?;
    let template = original.template_type.ok_or_else(invalid)?;
    if original.name_type.is_some()
        || store.intrinsic_bootstrap().is_none_or(|bootstrap| constraint == bootstrap.error_type)
    {
        return Err(invalid());
    }
    if !store.set_type_parameter_resolution(proof.parameter, Some(constraint),
        Some(proof.original_parameter), Some(proof.mapper), None)
        || !store.set_mapped_type_resolution(type_, Some(declaration), Some(proof.parameter),
            Some(constraint), None, Some(template), Some(modifiers), None, false)
    {
        return Err(invalid());
    }
    proof.operands = SourceMappedOperands::Ready {
        constraint, template, modifiers, name: None, modifier_names, constraint_plan,
    };
    if !store.complete_source_mapped_operands(proof) {
        return Err(invalid());
    }
    supported_mapped_alias_projection_with_source(store, type_, arrays, Some((globals, source)))?
        .ok_or_else(invalid)?;
    Ok(SourceMappedOperandOutcome::Complete)
}

/// Validates the owned construction state without reading named values.
pub(super) fn source_mapped_instance_projection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
    source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
) -> Result<Option<SupportedMappedAliasProjection>, MappedTypeError> {
    source_mapped_instance_projection_worker(store, type_, array_targets, active, source, false)
}

fn source_mapped_instance_projection_worker(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
    source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
    pure_identity: bool,
) -> Result<Option<SupportedMappedAliasProjection>, MappedTypeError> {
    let Some(proof) = store.source_mapped_instance(type_) else {
        return Ok(None);
    };
    let invalid = || MappedTypeError::InvalidMappedType(type_);
    let projection = &proof.projection;
    if let Some(request) = &proof.complete_any_request {
        if !complete_source_homomorphic_any_request_is_supported(store, projection)?
            || !matches!(proof.operands, SourceMappedOperands::Ready {
                name: None, modifier_names: None, constraint_plan: Some(_), ..
            })
        {
            return Err(invalid());
        }
        if pure_identity {
            let expected = request.proof.requested_alias().unwrap_or((projection.alias, &projection.arguments));
            if !request.proof.mapping_matches(projection.declared_type,
                &projection.type_parameters, &projection.arguments)
                || expected != (proof.key_alias.0, proof.key_alias.1.as_slice())
            { return Err(invalid()); }
            let retained = request.proof.validate_completed_any_metadata(store, type_, None, None, None)
                .map_err(MappedTypeError::Declared)?;
            if array_targets.is_some_and(|arrays| arrays != retained) { return Err(invalid()); }
        } else {
            validate_complete_any_request_binding(store, request, projection,
                (proof.key_alias.0, &proof.key_alias.1), source.map(|(_, source)| source))?;
        }
    }
    if projection.type_ != type_
        || projection.declared_type == type_
        || projection.type_parameters.len() != projection.arguments.len()
        || source.is_some_and(|(globals, _)| {
            array_targets != Some(CanonicalArrayTargets::from_global_types(globals))
        })
    {
        return Err(invalid());
    }
    let original = supported_mapped_alias_projection_worker(
        store,
        projection.declared_type,
        array_targets,
        active,
        source,
    )?
    .ok_or_else(invalid)?;
    if original.kind != projection.kind
        || original.alias != projection.alias
        || original.declared_type != projection.declared_type
        || original.type_parameters != projection.type_parameters
        || original.arguments != projection.type_parameters
        || original.identity_symbol != projection.alias
        || original.identity_arguments != projection.type_parameters
        || projection.arguments.iter().any(|argument| store.type_payload(*argument).is_none())
    {
        return Err(invalid());
    }
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(invalid());
    };
    let original_record = store.type_payload(projection.declared_type).ok_or_else(invalid)?;
    let TypeData::Mapped(original_mapped) = original_record.data() else {
        return Err(invalid());
    };
    let owner = cached_ordinary_type_parameter_owner(store, proof.original_parameter)
        .ok_or_else(invalid)?;
    let parameter_record = store.type_payload(proof.parameter).ok_or_else(invalid)?;
    let TypeData::TypeParameter(parameter) = parameter_record.data() else {
        return Err(invalid());
    };
    let computed = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    let (constraint, template, modifiers, name) = match &proof.operands {
        SourceMappedOperands::Deferred => (None, None, None, None),
        SourceMappedOperands::Ready { constraint, template, modifiers, name, .. } => {
            (Some(*constraint), Some(*template), Some(*modifiers), *name)
        }
    };
    if record.flags() != TypeFlags::OBJECT
        || !record.object_flags().contains(ObjectFlags::INSTANTIATED_MAPPED)
        || record.object_flags().bits() & !(ObjectFlags::MEMBERS_RESOLVED | computed).bits()
            != ObjectFlags::INSTANTIATED_MAPPED.bits()
        || record.symbol() != original_record.symbol()
        || mapped.declaration != original_mapped.declaration
        || mapped.type_parameter != Some(proof.parameter)
        || original_mapped.type_parameter != Some(proof.original_parameter)
        || mapped.object.target != Some(projection.declared_type)
        || mapped.object.mapper != Some(proof.mapper)
        || mapped.object.instantiations != TypeCacheState::Unallocated
        || mapped.constraint_type != constraint
        || mapped.template_type != template
        || mapped.modifiers_type != modifiers
        || mapped.name_type != name
        || mapped.resolved_apparent_type.is_some()
        || mapped.contains_error
        || parameter_record.flags() != TypeFlags::TYPE_PARAMETER
        || (parameter_record.object_flags() != ObjectFlags::NONE
            && parameter_record.object_flags() != computed)
        || parameter_record.symbol() != Some(owner)
        || parameter_record.alias().is_some()
        || parameter.target != Some(proof.original_parameter)
        || parameter.mapper != Some(proof.mapper)
        || parameter.constraint != constraint
        || parameter.resolved_default_type.is_some()
        || parameter.is_this_type
        || store.type_mapper_has_exact_endpoints(
            proof.local_mapper, &[proof.original_parameter], &[proof.parameter],
        ) != Some(true)
        || store.type_mapper_has_exact_endpoints(
            proof.outer_mapper, &projection.type_parameters, &projection.arguments,
        ) != Some(true)
        || !matches!(store.mapper_application(proof.mapper, proof.original_parameter),
            Some(TypeMapperApplication::Composite { first, second })
                if first == proof.local_mapper && second == proof.outer_mapper)
    {
        return Err(invalid());
    }
    if !mapped_base_constraint_is_valid(store, type_, mapped.object.structured.constrained.resolved_base_constraint)
        || matches!(proof.operands, SourceMappedOperands::Deferred)
            && record.object_flags().contains(ObjectFlags::MEMBERS_RESOLVED)
        || !record.object_flags().contains(ObjectFlags::MEMBERS_RESOLVED)
            && !unresolved_mapped_structure_is_valid(store, type_, &mapped.object.structured)
    {
        return Err(invalid());
    }
    let identity = record.alias().and_then(|alias| store.type_alias(alias)).ok_or_else(invalid)?;
    let expected_identity = result_identity(original.kind, projection.alias,
        &projection.type_parameters, &projection.arguments, (proof.key_alias.0, &proof.key_alias.1));
    if identity.symbol() != Some(projection.identity_symbol)
        || identity.type_arguments() != Some(projection.identity_arguments.as_slice())
        || expected_identity.0 != projection.identity_symbol
        || expected_identity.1 != projection.identity_arguments
        || object_key(store, &projection.arguments, (proof.key_alias.0, &proof.key_alias.1))? != proof.key
        || store.relation_object_instantiation(projection.declared_type, proof.key) != Some(type_)
    {
        return Err(invalid());
    }
    if projection.identity_symbol != projection.alias
        && forwarded_mapped_alias_arguments(store, projection.declared_type,
            projection.identity_symbol, &projection.identity_arguments, array_targets, source)? != projection.arguments
    {
        return Err(invalid());
    }
    Ok(Some(projection.clone()))
}

struct SourceMappedAliasRequest {
    key: Option<CacheHashKey>,
    cached: Option<TypeId>,
}

fn result_identity<'a>(
    kind: SupportedMappedAliasKind,
    alias: SemanticSymbolId,
    parameters: &[TypeId],
    arguments: &'a [TypeId],
    requested: (SemanticSymbolId, &'a [TypeId]),
) -> (SemanticSymbolId, &'a [TypeId]) {
    if matches!(kind, SupportedMappedAliasKind::Homomorphic(_))
        && arguments.first() != parameters.first()
    {
        (alias, arguments)
    } else {
        requested
    }
}

/// Replays an existing owned row without granting deferred allocation to a
/// structural caller or completing any operand during cache lookup.
pub(super) fn cached_owned_source_mapped_alias_instance(
    store: &CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
    arguments: &[TypeId],
    identity: (SemanticSymbolId, &[TypeId]),
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
) -> Result<Option<TypeId>, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(projection.type_);
    if !source_mapped_target_has_owned_cache(store, projection.declared_type)? {
        return Ok(None);
    }
    let Some(key) = cached_object_key(store, arguments, identity)? else {
        let TypeData::Mapped(target) = store.type_payload(projection.declared_type).ok_or_else(invalid)?.data() else {
            return Err(invalid());
        };
        let TypeCacheState::Allocated(entries) = &target.object.instantiations else {
            return Err(invalid());
        };
        if entries.values().any(|result| store.source_mapped_instance(*result)
            .is_some_and(|proof| proof.key_alias.0 == identity.0))
        {
            return Err(invalid());
        }
        return Ok(None);
    };
    let Some(cached) = store.relation_object_instantiation(projection.declared_type, key)
    else {
        return Ok(None);
    };
    if cached != projection.declared_type && store.source_mapped_instance(cached).is_none() {
        return Err(invalid());
    }
    if arguments.len() != projection.type_parameters.len()
        || arguments.iter().chain(identity.1).any(|type_| store.type_payload(*type_).is_none())
        || source.is_some_and(|(globals, _)| {
            array_targets != Some(CanonicalArrayTargets::from_global_types(globals))
        })
        || supported_mapped_alias_projection_with_source(store, projection.type_, array_targets, source)?
            .as_ref() != Some(projection)
    {
        return Err(invalid());
    }
    if cached == projection.declared_type {
        if arguments != projection.type_parameters || identity.0 != projection.alias
            || identity.1 != projection.type_parameters
        {
            return Err(invalid());
        }
        return Ok(Some(cached));
    }
    let actual = supported_mapped_alias_projection_with_source(store, cached, array_targets, source)?
        .ok_or_else(invalid)?;
    let expected_identity = result_identity(projection.kind, projection.alias,
        &projection.type_parameters, arguments, identity);
    if actual.kind != projection.kind
        || actual.alias != projection.alias
        || actual.declared_type != projection.declared_type
        || actual.type_parameters != projection.type_parameters
        || actual.arguments != arguments
        || actual.identity_symbol != expected_identity.0
        || actual.identity_arguments != expected_identity.1
        || store.source_mapped_instance(cached).is_none_or(|proof| {
            proof.key != key || proof.key_alias.0 != identity.0 || proof.key_alias.1 != identity.1
        })
    {
        return Err(invalid());
    }
    Ok(Some(cached))
}

fn source_mapped_alias_request(
    store: &CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
    arguments: &[TypeId],
    identity: (SemanticSymbolId, &[TypeId]),
    array_targets: Option<CanonicalArrayTargets>,
    source: (&CanonicalGlobalTypes, &dyn ConditionalBranchSource),
) -> Result<Option<SourceMappedAliasRequest>, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(projection.type_);
    if array_targets != Some(CanonicalArrayTargets::from_global_types(source.0))
        || arguments.len() != projection.type_parameters.len()
        || arguments.iter().chain(identity.1).any(|type_| store.type_payload(*type_).is_none())
        || supported_mapped_alias_projection_with_source(
            store, projection.type_, array_targets, Some(source),
        )?.as_ref() != Some(projection)
    {
        return Err(invalid());
    }
    let Some(argument) = arguments.first().and_then(|type_| store.type_payload(*type_)) else {
        return Err(invalid());
    };
    if !matches!(argument.data(), TypeData::Object(_) | TypeData::Interface(_)
        | TypeData::TypeReference(_) | TypeData::Mapped(_) | TypeData::TypeParameter(_))
    {
        return Ok(None);
    }
    if matches!(projection.kind, SupportedMappedAliasKind::Homomorphic(_))
        && (store.canonical_array_reference(source.0, arguments[0])
            .map_err(|_| MappedTypeError::InvalidSource(arguments[0]))?.is_some()
            || store.canonical_tuple_shape(arguments[0])
                .map_err(|_| MappedTypeError::InvalidSource(arguments[0]))?.is_some())
    {
        return Ok(None);
    }
    let key = cached_object_key(store, arguments, identity)?;
    let result = result_identity(projection.kind, projection.alias, &projection.type_parameters, arguments, identity);
    if result.0 != projection.alias
        && forwarded_mapped_alias_arguments(store, projection.declared_type, result.0, result.1,
            array_targets, Some(source))? != arguments
    {
        return Err(invalid());
    }
    let cached = cached_owned_source_mapped_alias_instance(
        store, projection, arguments, identity, array_targets, Some(source),
    )?;
    Ok(Some(SourceMappedAliasRequest { key, cached }))
}

/// The outer option selects this operation. The inner option is its cache hit.
pub(super) fn cached_source_mapped_alias_instance(
    store: &CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
    arguments: &[TypeId],
    identity: (SemanticSymbolId, &[TypeId]),
    array_targets: Option<CanonicalArrayTargets>,
    source: (&CanonicalGlobalTypes, &dyn ConditionalBranchSource),
) -> Result<Option<Option<TypeId>>, MappedTypeError> {
    source_mapped_alias_request(store, projection, arguments, identity, array_targets, source)
        .map(|request| request.map(|request| request.cached))
}

/// Creates only the ordinary object branch. The caller owns the normal
/// instantiation frame and has already mapped effective and requested arguments.
pub(super) fn instantiate_source_mapped_alias_instance(
    store: &mut CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
    arguments: &[TypeId],
    identity: (SemanticSymbolId, &[TypeId]),
    array_targets: Option<CanonicalArrayTargets>,
    source: (&CanonicalGlobalTypes, &dyn ConditionalBranchSource),
) -> Result<Option<TypeId>, MappedTypeError> {
    let Some(request) = source_mapped_alias_request(
        store, projection, arguments, identity, array_targets, source,
    )? else {
        return Ok(None);
    };
    if let Some(cached) = request.cached {
        return Ok(Some(cached));
    }
    // Read-only misses do not assign identities. The checked constructor owns
    // the requested key and the original declaration's alias-present self key.
    store.global_symbol_id(identity.0).ok_or(MappedTypeError::InvalidSymbol(identity.0))?;
    store.global_symbol_id(projection.alias).ok_or(MappedTypeError::InvalidSymbol(projection.alias))?;
    let key = object_key(store, arguments, identity)?;
    if request.key.is_some_and(|requested| requested != key) {
        return Err(MappedTypeError::InvalidMappedType(projection.type_));
    }
    prepare_target_cache(store, projection)?;
    if let Some(cached) = cached_owned_source_mapped_alias_instance(
        store, projection, arguments, identity, array_targets, Some(source),
    )? {
        return Ok(Some(cached));
    }
    let invalid = || MappedTypeError::InvalidMappedType(projection.type_);
    let original_record = store.type_payload(projection.declared_type).ok_or_else(invalid)?;
    let TypeData::Mapped(original) = original_record.data() else {
        return Err(invalid());
    };
    let original = original.clone();
    let symbol = original_record.symbol().ok_or_else(invalid)?;
    let original_parameter = original.type_parameter.ok_or_else(invalid)?;
    let owner = cached_ordinary_type_parameter_owner(store, original_parameter).ok_or_else(invalid)?;
    let declaration = original.declaration.ok_or_else(invalid)?;
    if !store.try_reserve_types(2) || !store.try_reserve_mappers(3)
        || !store.try_reserve_type_aliases(1) || !store.try_reserve_source_mapped_instances()
    {
        return Err(MappedTypeError::Capacity);
    }
    let parameter = store.alloc_type_parameter(Some(owner)).ok_or(MappedTypeError::Capacity)?;
    let outer_mapper = store.new_type_mapper(projection.type_parameters.clone(), arguments.to_vec())
        .ok_or_else(invalid)?;
    let local_mapper = store.new_simple_type_mapper(original_parameter, parameter).ok_or_else(invalid)?;
    let mapper = store.combine_type_mappers(Some(local_mapper), outer_mapper).ok_or_else(invalid)?;
    let result = store.alloc_mapped_type(
        ObjectFlags::INSTANTIATED_MAPPED, Some(symbol), Some(declaration),
    ).ok_or(MappedTypeError::Capacity)?;
    let result_identity = result_identity(projection.kind, projection.alias,
        &projection.type_parameters, arguments, identity);
    let alias = store.alloc_type_alias(Some(result_identity.0)).ok_or(MappedTypeError::Capacity)?;
    if !store.set_type_parameter_resolution(parameter, None, Some(original_parameter), Some(mapper), None)
        || !store.set_object_target_and_mapper(result, Some(projection.declared_type), Some(mapper))
        || !store.set_mapped_type_resolution(result, Some(declaration), Some(parameter),
            None, None, None, None, None, false)
        || !store.set_type_alias_arguments(alias, Some(result_identity.1.to_vec()))
        || !store.set_type_alias(result, Some(alias))
    {
        return Err(invalid());
    }
    let proof = SourceMappedInstance {
        projection: SupportedMappedAliasProjection {
            kind: projection.kind, type_: result, alias: projection.alias,
            declared_type: projection.declared_type,
            type_parameters: projection.type_parameters.clone(), arguments: arguments.to_vec(),
            identity_symbol: result_identity.0, identity_arguments: result_identity.1.to_vec(),
        },
        parameter, original_parameter, mapper, outer_mapper, local_mapper, key,
        key_alias: (identity.0, identity.1.to_vec()),
        operands: SourceMappedOperands::Deferred,
        complete_any_request: None,
    };
    if !store.publish_source_mapped_instance(proof)
        || store.insert_object_instantiation(projection.declared_type, key, result) != Some(result)
    {
        return Err(invalid());
    }
    supported_mapped_alias_projection_with_source(store, result, array_targets, Some(source))?
        .ok_or_else(invalid)?;
    Ok(Some(result))
}

/// Selects the complete, non-union any branch without changing other sources.
pub(super) fn complete_source_homomorphic_any_request_is_supported(
    store: &CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
) -> Result<bool, MappedTypeError> {
    let SupportedMappedAliasKind::Homomorphic(modifiers) = projection.kind else {
        return Ok(false);
    };
    let [formal] = projection.type_parameters.as_slice() else {
        return Ok(false);
    };
    let [argument] = projection.arguments.as_slice() else {
        return Ok(false);
    };
    if store.intrinsic_bootstrap().is_none_or(|bootstrap| *argument != bootstrap.any_type) {
        return Ok(false);
    }
    let owner = cached_ordinary_type_parameter_owner(store, *formal)
        .ok_or(MappedTypeError::InvalidTypeParameter(*formal))?;
    let Some([declaration]) = store.symbol(owner).and_then(|symbol| symbol.declarations()) else {
        return Err(MappedTypeError::InvalidTypeParameter(*formal));
    };
    if store.source_alias_type_parameter_annotations(*declaration)
        .is_none_or(|annotations| annotations.constraint.is_some())
    {
        return Ok(false);
    }
    validate_homomorphic_mapped_alias_request(store, projection.alias,
        projection.declared_type, &projection.type_parameters, &projection.arguments, modifiers)?;
    Ok(true)
}

fn validate_complete_any_request_binding(
    store: &CanonicalTypeMapperStore,
    request: &CompleteAnyRequest,
    projection: &SupportedMappedAliasProjection,
    identity: (SemanticSymbolId, &[TypeId]),
    source: Option<&dyn ConditionalBranchSource>,
) -> Result<(), MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(projection.type_);
    let expected = request.proof.requested_alias()
        .unwrap_or((projection.alias, &projection.arguments));
    if !request.proof.mapping_matches(projection.declared_type,
        &projection.type_parameters, &projection.arguments)
        || expected != identity
    {
        return Err(invalid());
    }
    let Some(source) = source else {
        return Err(MappedTypeError::Declared(
            SourceMappedReadRequest::Members { receiver: projection.type_ }.missing_proof(),
        ));
    };
    source.validate_source_mapped_alias_request(store, &request.proof)
        .map_err(MappedTypeError::Declared)
}

/// Publishes one complete any clone for the caller's physical request key.
pub(in crate::semantic) fn instantiate_complete_source_homomorphic_any_instance(
    store: &mut CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
    request_proof: std::sync::Arc<super::super::type_nodes::SourceMappedAliasRequestProof>,
    identity: (SemanticSymbolId, &[TypeId]),
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    source: &dyn ConditionalBranchSource,
) -> Result<TypeId, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(projection.type_);
    if !complete_source_homomorphic_any_request_is_supported(store, projection)? {
        return Err(invalid());
    }
    let request = CompleteAnyRequest { proof: request_proof };
    validate_complete_any_request_binding(store, &request, projection, identity, Some(source))?;
    let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
    let original = supported_mapped_alias_projection_with_source(store,
        projection.declared_type, arrays, Some((globals, source)))?.ok_or_else(invalid)?;
    if original.alias != projection.alias || original.kind != projection.kind
        || original.type_parameters != projection.type_parameters
    {
        return Err(invalid());
    }
    store.global_symbol_id(identity.0).ok_or(MappedTypeError::InvalidSymbol(identity.0))?;
    store.global_symbol_id(projection.alias).ok_or(MappedTypeError::InvalidSymbol(projection.alias))?;
    let key = object_key(store, &projection.arguments, identity)?;
    prepare_target_cache(store, &original)?;
    if let Some(cached) = cached_owned_source_mapped_alias_instance(store, &original,
        &projection.arguments, identity, arrays, Some((globals, source)))?
    {
        return Ok(cached);
    }
    if !store.try_reserve_type_aliases(1) || !store.try_reserve_source_mapped_instances() {
        return Err(MappedTypeError::Capacity);
    }
    let mark = session.limit_event_mark();
    let result = projection.kind.instantiate(store, projection.alias,
        projection.declared_type, &projection.type_parameters, &projection.arguments, Some(session))?;
    if session.limit_event_occurred_since(mark) { return Ok(result); }
    let TypeData::Mapped(mapped) = store.type_payload(result).ok_or_else(invalid)?.data() else {
        return Err(invalid());
    };
    let mapped = mapped.clone();
    let parameter = mapped.type_parameter.ok_or_else(invalid)?;
    let mapper = mapped.object.mapper.ok_or_else(invalid)?;
    let TypeData::TypeParameter(parameter_data) = store.type_payload(parameter).ok_or_else(invalid)?.data() else {
        return Err(invalid());
    };
    let original_parameter = parameter_data.target.ok_or_else(invalid)?;
    let Some(TypeMapperApplication::Composite { first: local_mapper, second: outer_mapper }) =
        store.mapper_application(mapper, original_parameter) else { return Err(invalid()); };
    let constraint_plan = plan_nongeneric_keyof_type_with_source(
        store, projection.arguments[0], globals, source,
    )
        .map_err(|error| mapped_keyof_error(projection.arguments[0], error))?;
    let alias = store.alloc_type_alias(Some(projection.alias)).ok_or(MappedTypeError::Capacity)?;
    if !store.set_type_alias_arguments(alias, Some(projection.arguments.clone()))
        || !store.set_type_alias(result, Some(alias))
    {
        return Err(invalid());
    }
    let proof = SourceMappedInstance {
        projection: SupportedMappedAliasProjection { type_: result,
            identity_symbol: projection.alias, identity_arguments: projection.arguments.clone(),
            ..projection.clone() },
        parameter, original_parameter, mapper, outer_mapper, local_mapper, key,
        key_alias: (identity.0, identity.1.to_vec()),
        operands: SourceMappedOperands::Ready {
            constraint: mapped.constraint_type.ok_or_else(invalid)?,
            template: mapped.template_type.ok_or_else(invalid)?,
            modifiers: mapped.modifiers_type.ok_or_else(invalid)?,
            name: None, modifier_names: None, constraint_plan: Some(constraint_plan),
        },
        complete_any_request: Some(request),
    };
    if !store.publish_source_mapped_instance(proof)
        || store.insert_object_instantiation(projection.declared_type, key, result) != Some(result)
    {
        return Err(invalid());
    }
    validate_owned_source_mapped_type(store, result, arrays, Some((globals, source)))?
        .ok_or_else(invalid)?;
    Ok(result)
}

/// Pure completed identity reads retain exact request and canonical array facts.
pub(super) fn pure_complete_any_projection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    arrays: Option<CanonicalArrayTargets>,
) -> Result<Option<SupportedMappedAliasProjection>, MappedTypeError> {
    let Some(proof) = store.source_mapped_instance(type_) else { return Ok(None); };
    let Some(request) = &proof.complete_any_request else { return Ok(None); };
    let retained = request.proof.validate_completed_any_metadata(store, type_, None, None, None)
        .map_err(MappedTypeError::Declared)?;
    if arrays.is_some_and(|arrays| arrays != retained) {
        return Err(MappedTypeError::InvalidMappedType(type_));
    }
    let current_plan = plan_nongeneric_keyof_type_with_array_targets(store,
        proof.projection.arguments[0], Some(retained))
        .map_err(|error| mapped_keyof_error(proof.projection.arguments[0], error))?;
    if !matches!(&proof.operands, SourceMappedOperands::Ready { constraint_plan: Some(plan), .. }
        if *plan == current_plan)
    {
        return Err(MappedTypeError::InvalidMappedType(type_));
    }
    let projection = source_mapped_instance_projection_worker(store, type_, Some(retained),
        &mut HashSet::new(), None, true)?.ok_or(MappedTypeError::InvalidMappedType(type_))?;
    validate_ready_source_mapped_operands(store, proof, Some(retained), None)?;
    validate_complete_any_logical_row(store, proof)?;
    Ok(Some(projection))
}

fn validate_complete_any_logical_row(
    store: &CanonicalTypeMapperStore,
    proof: &SourceMappedInstance,
) -> Result<(), MappedTypeError> {
    let projection = &proof.projection;
    let invalid = || MappedTypeError::InvalidMappedType(projection.type_);
    let key = if proof.key_alias.0 == projection.alias && proof.key_alias.1 == projection.arguments {
        type_alias_instantiation_cache_key(&projection.arguments, None)
    } else { proof.key };
    let links = store.type_alias_links(projection.alias).ok_or_else(invalid)?;
    if links.declared_type != Some(projection.declared_type)
        || links.is_constructor_declared_property
        || links.type_parameters.as_deref() != Some(projection.type_parameters.as_slice())
        || links.instantiations.as_ref().and_then(|rows| rows.get(&key)) != Some(&projection.type_)
    { return Err(invalid()); }
    Ok(())
}

impl CanonicalTypeMapperStore {
    /// Matches a retained complete-any result for captured Identity replay.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::semantic) fn complete_any_cached_identity_matches(
        &self,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        parameters: &[TypeId],
        arguments: &[TypeId],
        requested_alias: Option<(SemanticSymbolId, &[TypeId])>,
        result: TypeId,
        arrays: Option<CanonicalArrayTargets>,
    ) -> Result<Option<bool>, MappedTypeError> {
        let Some(proof) = self.source_mapped_instance(result) else {
            return Ok(None);
        };
        let Some(request) = &proof.complete_any_request else {
            return Ok(None);
        };
        let projection = pure_complete_any_projection(self, result, arrays)?
            .ok_or(MappedTypeError::InvalidMappedType(result))?;
        let expected_identity = requested_alias.unwrap_or((alias, arguments));
        Ok(Some(
            request.proof.mapping_matches(
                declared_type,
                parameters,
                arguments,
            ) && request.proof.requested_alias() == requested_alias
                && projection.alias == alias
                && projection.declared_type == declared_type
                && projection.type_parameters.as_slice() == parameters
                && projection.arguments.as_slice() == arguments
                && projection.identity_symbol == alias
                && projection.identity_arguments.as_slice() == arguments
                && (proof.key_alias.0, proof.key_alias.1.as_slice()) == expected_identity,
        ))
    }

    /// This witness is only for a live-validated, complete canonical-any cache row.
    pub(in crate::semantic) fn validated_complete_any_cache_identity(
        &self,
        projection: &SupportedMappedAliasProjection,
        arrays: Option<CanonicalArrayTargets>,
        source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
    ) -> Result<Option<(SemanticSymbolId, Vec<TypeId>)>, MappedTypeError> {
        let Some(proof) = self.source_mapped_instance(projection.type_) else { return Ok(None); };
        if proof.complete_any_request.is_none() { return Ok(None); }
        let Some(source) = source else {
            return Err(MappedTypeError::Declared(SourceMappedReadRequest::Members {
                receiver: projection.type_,
            }.missing_proof()));
        };
        let current = validate_owned_source_mapped_type(self, projection.type_, arrays, Some(source))?
            .ok_or(MappedTypeError::InvalidMappedType(projection.type_))?;
        if &current != projection
            || projection.identity_symbol != projection.alias
            || projection.identity_arguments != projection.arguments
            || !complete_source_homomorphic_any_request_is_supported(self, projection)?
        { return Err(MappedTypeError::InvalidMappedType(projection.type_)); }
        validate_complete_any_logical_row(self, proof)?;
        let original = supported_mapped_alias_projection_with_source(self,
            projection.declared_type, arrays, Some(source))?
            .ok_or(MappedTypeError::InvalidMappedType(projection.type_))?;
        if cached_owned_source_mapped_alias_instance(self, &original, &projection.arguments,
            (proof.key_alias.0, &proof.key_alias.1), arrays, Some(source))? != Some(projection.type_)
        { return Err(MappedTypeError::InvalidMappedType(projection.type_)); }
        Ok(Some(proof.key_alias.clone()))
    }

    /// Readonly checker display uses its actual host, globals and options.
    pub(in crate::semantic) fn complete_any_display_identity(
        &self,
        type_: TypeId,
        host: &DeclaredTypeHost<'_>,
        globals: Option<&CanonicalGlobalTypes>,
        options: Option<super::super::production::CanonicalCheckerOptions>,
        source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
    ) -> Result<Option<MappedAliasDisplayIdentity>, MappedTypeError> {
        let Some(proof) = self.source_mapped_instance(type_) else { return Ok(None); };
        let Some(request) = &proof.complete_any_request else { return Ok(None); };
        let projection = if let Some(source) = source {
            validate_owned_source_mapped_type(self, type_, Some(CanonicalArrayTargets::from_global_types(source.0)),
                Some(source))?.ok_or(MappedTypeError::InvalidMappedType(type_))?
        } else {
            let globals = globals.ok_or(MappedTypeError::InvalidMappedType(type_))?;
            let options = options.ok_or(MappedTypeError::InvalidMappedType(type_))?;
            if self.intrinsic_bootstrap().is_none_or(|bootstrap| bootstrap.options != options.intrinsic) {
                return Err(MappedTypeError::InvalidMappedType(type_));
            }
            let arrays = request.proof.validate_completed_any_metadata(self, type_, Some(host),
                Some(globals), Some(options.into())).map_err(MappedTypeError::Declared)?;
            pure_complete_any_projection(self, type_, Some(arrays))?
                .ok_or(MappedTypeError::InvalidMappedType(type_))?
        };
        validate_complete_any_logical_row(self, proof)?;
        Ok(Some(MappedAliasDisplayIdentity {
            symbol: projection.identity_symbol, arguments: projection.identity_arguments,
            deferred_operands: false,
        }))
    }
}
