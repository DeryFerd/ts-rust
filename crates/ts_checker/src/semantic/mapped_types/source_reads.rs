//! Exact mapped member identities retained by source operations.

use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
struct MappedMemberReplayRow {
    symbol: SemanticSymbolId,
    name: EscapedName,
    flags: SymbolFlags,
    checks: CheckFlags,
    key: TypeId,
    name_type: TypeId,
    origin: Option<SemanticSymbolId>,
    declarations: Option<Vec<NodeRef>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct MappedIndexReplayRow {
    index: IndexInfoId,
    key: TypeId,
    value: TypeId,
    readonly: bool,
}

/// Named value caches are not part of a member-name result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::semantic) struct MappedMembersReplayIdentity {
    members: ResolvedMappedTypeMembers,
    properties: Vec<MappedMemberReplayRow>,
    indexes: Vec<MappedIndexReplayRow>,
    shape: MappedShape,
    index_plans: Vec<PlannedMappedIndex>,
    receiver_symbol: Option<SemanticSymbolId>,
    receiver_alias: Option<(super::super::TypeAliasId, Option<SemanticSymbolId>, Option<Vec<TypeId>>)>,
}

impl MappedMembersReplayIdentity {
    pub(in crate::semantic) fn members(&self) -> &ResolvedMappedTypeMembers {
        &self.members
    }
}

pub(in crate::semantic) fn capture_source_mapped_members_identity(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<MappedMembersReplayIdentity, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidCachedMembers(receiver);
    let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
    source_instances::validate_source_mapped_instance_operands(store, receiver, globals, source)?;
    let source = Some((globals, source));
    validate_mapped_relation_identity_with_source(store, receiver, arrays, source)?;
    validate_mapped_member_dependencies(store, receiver, &mut HashSet::new())?;
    let shape = validate_mapped_shape_with_source(store, receiver, arrays, source)?;
    let modifiers = store.declared_mapped_modifiers(receiver)?;
    let (properties, index_plans) = plan_mapped_members(store, &shape, modifiers)?;
    let members = validate_warm_mapped_members_mode(
        store, &shape, &properties, &index_plans, arrays, source,
        MappedMembersReplay::NamesAndIndexes,
    )?.ok_or_else(invalid)?;
    let mut rows = Vec::with_capacity(members.properties.len());
    for symbol in &members.properties {
        let record = store.symbol(*symbol).ok_or_else(invalid)?;
        let mapped = store.mapped_symbol_links(*symbol).ok_or_else(invalid)?;
        let value = store.value_symbol_links(*symbol).ok_or_else(invalid)?;
        rows.push(MappedMemberReplayRow {
            symbol: *symbol,
            name: record.name().to_owned(),
            flags: record.flags(),
            checks: record.check_flags(),
            key: mapped.key_type.ok_or_else(invalid)?,
            name_type: value.name_type.ok_or_else(invalid)?,
            origin: mapped.synthetic_origin,
            declarations: record.declarations().map(<[NodeRef]>::to_vec),
        });
    }
    let TypeData::Mapped(mapped) = store.type_payload(receiver).ok_or_else(invalid)?.data()
    else {
        return Err(invalid());
    };
    let indexes = mapped.object.structured.index_infos.as_deref().unwrap_or_default()
        .iter().map(|id| {
            let index = store.index_info(*id).ok_or_else(invalid)?;
            Ok(MappedIndexReplayRow {
                index: *id,
                key: index.key_type(),
                value: index.value_type(),
                readonly: index.is_readonly(),
            })
        }).collect::<Result<Vec<_>, MappedTypeError>>()?;
    let record = store.type_payload(receiver).ok_or_else(invalid)?;
    let receiver_symbol = record.symbol();
    let receiver_alias = match record.alias() {
        Some(alias) => {
            let data = store.type_alias(alias).ok_or_else(invalid)?;
            Some((alias, data.symbol(), data.type_arguments().map(<[TypeId]>::to_vec)))
        }
        None => None,
    };
    Ok(MappedMembersReplayIdentity {
        members, properties: rows, indexes, shape, index_plans, receiver_symbol, receiver_alias,
    })
}

pub(in crate::semantic) fn validate_source_mapped_value_identity(
    store: &CanonicalTypeMapperStore,
    identity: &MappedMembersReplayIdentity,
    member: SemanticSymbolId,
    expected: TypeId,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<(), MappedTypeError> {
    let invalid = || MappedTypeError::InvalidCachedProperty(member);
    let receiver = identity.members.type_;
    let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
    let source = Some((globals, source));
    let shape = validate_mapped_shape_with_source(store, receiver, arrays, source)?;
    let modifiers = store.declared_mapped_modifiers(receiver)?;
    let (properties, _) = plan_mapped_members(store, &shape, modifiers)?;
    let position = identity.members.properties.iter().position(|symbol| *symbol == member)
        .ok_or_else(invalid)?;
    let planned = properties.get(position).ok_or_else(invalid)?;
    let key = store.mapped_symbol_links(member).and_then(|links| links.key_type)
        .ok_or_else(invalid)?;
    if store.mapped_property_recovery(member).is_some()
        || store.value_symbol_links(member).and_then(|links| links.resolved_type) != Some(expected)
        || store.intrinsic_bootstrap().is_none_or(|bootstrap| expected == bootstrap.error_type)
        || cached_mapped_property_type(store, &shape, planned, key, arrays, source)? != Some(expected)
    {
        return Err(invalid());
    }
    Ok(())
}

/// Authenticates the published native recovery against the current source shape.
pub(in crate::semantic) fn validate_source_mapped_recovered_value_identity(
    store: &CanonicalTypeMapperStore,
    identity: &MappedMembersReplayIdentity,
    member: SemanticSymbolId,
    expected: TypeId,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<(), MappedTypeError> {
    let invalid = || MappedTypeError::InvalidCachedProperty(member);
    let receiver = identity.members.type_;
    let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
    let shape = validate_mapped_shape_with_source(store, receiver, arrays, Some((globals, source)))?;
    let (containing_type, key, cached) = validate_mapped_property_header(store, member)?;
    let modifiers = store.declared_mapped_modifiers(receiver)?;
    let (properties, _) = plan_mapped_members(store, &shape, modifiers)?;
    let position = identity.members.properties.iter().position(|symbol| *symbol == member)
        .ok_or_else(invalid)?;
    let planned = properties.get(position).ok_or_else(invalid)?;
    if containing_type != receiver
        || cached != Some(expected)
        || !keys_match(store, Some(key), &planned.keys)
        || store.mapped_property_recovery(member).is_none_or(|recovery| {
            !recovery.matches(store, member, &shape, key, expected, arrays)
        })
    {
        return Err(invalid());
    }
    Ok(())
}

impl MappedMembersReplayIdentity {
    /// Checks the current publication against the independently captured source plan.
    pub(in crate::semantic) fn recovered_index_is_current(
        &self,
        store: &CanonicalTypeMapperStore,
        index: IndexInfoId,
        globals: &CanonicalGlobalTypes,
    ) -> bool {
        let Some(bootstrap) = store.intrinsic_bootstrap() else { return false; };
        let ([row], [plan]) = (self.indexes.as_slice(), self.index_plans.as_slice()) else { return false; };
        let Some(TypeData::Mapped(mapped)) = store.type_payload(self.members.type_).map(TypeRecord::data)
        else { return false; };
        let record = store.type_payload(self.members.type_).expect("the mapped payload was checked");
        let alias_is_current = match &self.receiver_alias {
            Some((id, symbol, arguments)) => record.alias() == Some(*id)
                && store.type_alias(*id).is_some_and(|alias| {
                    alias.symbol() == *symbol && alias.type_arguments() == arguments.as_deref()
                }),
            None => record.alias().is_none(),
        };
        record.symbol() == self.receiver_symbol
            && alias_is_current
            && self.properties.is_empty()
            && self.members.properties.is_empty()
            && row.index == index
            && row.key == bootstrap.string_type
            && !row.readonly
            && plan.key_type == row.key
            && !plan.readonly
            && plan.value_type == PlannedMappedIndexValue::Template
            && mapped.type_parameter == Some(self.shape.type_parameter)
            && mapped.constraint_type == Some(self.shape.constraint_type)
            && mapped.template_type == Some(self.shape.template_type)
            && mapped.modifiers_type == Some(self.shape.modifiers_type)
            && mapped.name_type == self.shape.name_type
            && mapped.object.structured.members == Some(self.members.members)
            && mapped.object.structured.properties.as_deref()
                == (!self.members.properties.is_empty()).then_some(self.members.properties.as_slice())
            && mapped.object.structured.index_infos.as_deref() == Some(&[index])
            && store.index_info(index).is_some_and(|info| {
                info.id() == index && info.key_type() == row.key && info.value_type() == row.value
                    && info.is_readonly() == row.readonly && info.declaration().is_none()
                    && info.index_symbol().is_none() && info.components().is_empty()
            })
            && store.mapped_index_recovery(index).is_some_and(|recovery| {
                recovery.matches(store, index, &self.shape, plan,
                    Some(CanonicalArrayTargets::from_global_types(globals)))
            })
    }
}

/// Returns the actual native recovered index only for the complete source any branch.
pub(in crate::semantic) fn validate_source_mapped_recovered_index_identity(
    store: &CanonicalTypeMapperStore,
    identity: &MappedMembersReplayIdentity,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<Option<IndexInfoId>, MappedTypeError> {
    let receiver = identity.members.type_;
    let invalid = || MappedTypeError::InvalidCachedMembers(receiver);
    let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
    let Some(projection) = supported_mapped_alias_projection_with_source(
        store, receiver, arrays, Some((globals, source)),
    )? else { return Ok(None); };
    if !source_instances::complete_source_homomorphic_any_request_is_supported(store, &projection)?
        || projection.kind != SupportedMappedAliasKind::Homomorphic(MappedTypeModifiers::NONE)
        || identity.shape.name_type.is_some()
        || !identity.shape.source_properties.is_empty()
    {
        return Ok(None);
    }
    if capture_source_mapped_members_identity(store, receiver, globals, source)? != *identity {
        return Err(invalid());
    }
    let [row] = identity.indexes.as_slice() else { return Ok(None); };
    if store.mapped_index_recovery(row.index).is_none() {
        return Ok(None);
    }
    if !identity.recovered_index_is_current(store, row.index, globals) {
        return Err(invalid());
    }
    Ok(Some(row.index))
}
