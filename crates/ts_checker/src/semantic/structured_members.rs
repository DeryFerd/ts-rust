//! Structured-member publication for direct interface bases.
//!
//! One or two direct bases preserve declaration and source-base order. A
//! single base can also provide authenticated index or call signatures.
//! Shared base properties or methods must have identical types and modifiers.
//! Compatible derived members replace inherited members; incompatible
//! overrides remain unsupported until TS2430 is ported.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, EscapedNameRef, InternalSymbolName, SemanticSymbolId, SymbolFlags,
    SymbolTableId, semantic::PreparedSymbolTable,
};

use super::{
    CanonicalTypeMapperStore, IndexInfoId, SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    declared::cached_ordinary_type_parameter_owner,
    instantiated_members::validate_generic_interface_members,
    links::{
        MembersOrExportsResolutionKind, ResolvedSignatureState, SignatureLinks, ValueSymbolLinks,
    },
    object_members::{
        DirectInterfaceDeclaredState, PlannedComputedMemberKey, PropertyObjectError,
        PropertyObjectKind, PropertyObjectPlan, PropertyObjectState, ResolvedCallSignatureTypes,
        StoredDeclaredCallSetValidation, planned_declared_property_key,
        prepare_direct_interface_declared_properties, publish_declared_members,
        publish_prepared_direct_interface_declared_properties, resolved_computed_member_key,
        valid_declared_property_check_flags, validate_stored_declared_call_set,
    },
    reference_types::{
        validate_direct_generic_reference, validate_nongeneric_interface_argument_origin,
    },
    relater::ResolvedOwnProperty,
    signatures::{IndexInfo, SignatureFlags},
    store::{DirectInterfaceHeritageProvenance, SourceNodeParent},
    type_records::{ConstrainedTypeData, InterfaceTypeData, TypeCacheState, TypeData},
    types::{ObjectFlags, TypeFlags},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum InterfaceHeritageMembersValidation {
    NotHeritage,
    Valid,
    Malformed,
}

struct ValidatedInterfaceSurface {
    owner: SemanticSymbolId,
    declared_properties: Vec<SemanticSymbolId>,
    properties: Vec<SemanticSymbolId>,
    index_infos: Vec<IndexInfoId>,
    declared_call_signatures: Vec<SignatureId>,
    call_signatures: Vec<SignatureId>,
}

struct ValidatedDeclaredMembers {
    properties: Vec<SemanticSymbolId>,
    index_symbol: Option<SemanticSymbolId>,
    index_infos: Vec<IndexInfoId>,
    call_symbol: Option<SemanticSymbolId>,
    call_signatures: Vec<SignatureId>,
}

fn invalid(plan: &PropertyObjectPlan, type_: TypeId) -> PropertyObjectError {
    PropertyObjectError::InvalidCachedInterface {
        symbol: plan.symbol,
        type_,
    }
}

fn capacity(plan: &PropertyObjectPlan) -> PropertyObjectError {
    PropertyObjectError::Capacity(plan.node)
}

fn planned_base_matches(
    store: &CanonicalTypeMapperStore,
    planned: &super::interface_heritage::DirectInterfaceBasePlan,
    type_: TypeId,
) -> bool {
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    if record.symbol() != Some(planned.symbol) {
        return false;
    }
    if planned.type_arguments.is_empty() {
        return store
            .declared_type_links(planned.symbol)
            .and_then(|links| links.declared_type)
            == Some(type_)
            && matches!(record.data(), TypeData::Interface(interface)
                if interface.reference.resolved_type_arguments.as_deref().is_none_or(<[TypeId]>::is_empty));
    }
    validate_direct_generic_reference(store, type_).is_ok_and(|reference| {
        reference.type_arguments.len() == planned.type_arguments.len()
            && reference
                .type_arguments
                .iter()
                .zip(&planned.type_arguments)
                .all(|(argument, node)| {
                    super::object_members::cached_planned_type_identity(store, *node)
                        == Some(*argument)
                })
            && planned.defaults.iter().all(|default| {
                super::interface_heritage::validate_heritage_default_cache(store, default, true)
                    .is_ok()
            })
    })
}

fn matching_inherited_property_contract(
    store: &CanonicalTypeMapperStore,
    first: SemanticSymbolId,
    second: SemanticSymbolId,
) -> bool {
    let Some(first_record) = store.symbol(first) else {
        return false;
    };
    let Some(second_record) = store.symbol(second) else {
        return false;
    };
    let Some(first_links) = store.value_symbol_links(first) else {
        return false;
    };
    let Some(first_type) = first_links.resolved_type else {
        return false;
    };
    let Some(second_links) = store.value_symbol_links(second) else {
        return false;
    };
    let Some(second_type) = second_links.resolved_type else {
        return false;
    };
    first_record.name() == second_record.name()
        && first_record.flags() == second_record.flags()
        && first_record.check_flags() == second_record.check_flags()
        && first_links.write_type == second_links.write_type
        && (first_type == second_type
            || first_record.flags().contains(SymbolFlags::METHOD)
                && matching_interface_method_contract(store, first, second))
}

/// The callers authenticate the property key and retained index before this check.
/// Applicable properties keep the required-property and exact-type boundary.
fn inherited_index_property_compatible(
    store: &CanonicalTypeMapperStore,
    index: IndexInfoId,
    name: EscapedNameRef<'_>,
    property_type: TypeId,
    optional: bool,
) -> Option<bool> {
    let info = store.index_info(index)?;
    let bootstrap = store.intrinsic_bootstrap()?;
    store.type_payload(property_type)?;
    store.type_payload(info.value_type())?;
    let string_index = info.key_type() == bootstrap.string_type;
    if !string_index && info.key_type() != bootstrap.number_type {
        return Some(false);
    }
    let applies = match name.as_utf8() {
        Some(name) => string_index || ts_jsnum::from_string(name).to_string() == name,
        None if name.is_late_bound() => false,
        None => return None,
    };
    Some(!applies || !optional && property_type == info.value_type())
}

/// Resolves and publishes one or two direct interface bases.
///
/// `base_types` must match the canonical symbols retained by the syntax plan.
/// Generic bases retain their instantiated property symbols and lazy types.
/// One direct base may also provide authenticated index signatures.
/// All allocations and sparse-link slots are staged before semantic mutation.
pub(super) fn resolve_direct_interface_members(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
    property_types: &[TypeId],
    base_types: &[TypeId],
) -> Result<TypeId, PropertyObjectError> {
    resolve_direct_interface_members_with_array_targets(
        store,
        plan,
        type_,
        property_types,
        base_types,
        None,
    )
}

/// Keeps the caller's array targets while validating direct bases.
pub(super) fn resolve_direct_interface_members_with_array_targets(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
    property_types: &[TypeId],
    base_types: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<TypeId, PropertyObjectError> {
    let Some(heritage) = plan.heritage.as_ref() else {
        return Err(invalid(plan, type_));
    };
    if !matches!(heritage.bases.as_slice(), [_] | [_, _])
        || heritage.bases.len() != base_types.len()
    {
        return Err(invalid(plan, type_));
    }
    let planned_base = &heritage.bases[0];
    let base_type = base_types[0];
    let second_base = heritage
        .bases
        .get(1)
        .zip(base_types.get(1))
        .map(|(base, type_)| (base.symbol, *type_));
    if second_base
        .is_some_and(|(symbol, type_)| symbol == planned_base.symbol || type_ == base_type)
    {
        return Err(invalid(plan, type_));
    }
    if plan.kind != PropertyObjectKind::Interface
        || !plan.indexes.is_empty()
        || !plan.call_signatures.is_empty()
    {
        return Err(invalid(plan, type_));
    }

    let mut base_surfaces = Vec::new();
    base_surfaces
        .try_reserve_exact(base_types.len())
        .map_err(|_| capacity(plan))?;
    for (planned, base) in heritage.bases.iter().zip(base_types.iter().copied()) {
        let base_record = store
            .type_payload(base)
            .ok_or_else(|| invalid(plan, type_))?;
        if !planned_base_matches(store, planned, base) {
            return Err(invalid(plan, type_));
        }
        if base_record.data().structured().is_some_and(|structured| {
            structured.call_signature_count != 0
                || structured
                    .signatures
                    .as_ref()
                    .is_some_and(|set| !set.is_empty())
        }) {
            return Err(PropertyObjectError::UnsupportedMember {
                node: planned.node,
                kind: SyntaxKind::ExpressionWithTypeArguments,
            });
        }
        let inherited_base = store.direct_interface_heritage_provenance(base).is_some();
        let surface = if !planned.type_arguments.is_empty() {
            validate_generic_base_property_interface(store, base, array_targets)
        } else if inherited_base {
            validate_direct_heritage_property_interface(store, base, array_targets)
        } else {
            validate_no_heritage_property_interface(store, base, array_targets)
        }
        .ok_or_else(|| invalid(plan, type_))?;
        if surface.owner != planned.symbol {
            return Err(invalid(plan, type_));
        }
        if second_base.is_some() && !surface.index_infos.is_empty() {
            return Err(PropertyObjectError::UnsupportedMember {
                node: planned.node,
                kind: SyntaxKind::ExpressionWithTypeArguments,
            });
        }
        base_surfaces.push(surface);
    }

    let inherited_index_infos = base_surfaces
        .first()
        .filter(|_| second_base.is_none())
        .map(|surface| surface.index_infos.as_slice())
        .unwrap_or_default();
    let declared_state =
        prepare_direct_interface_declared_properties(store, plan, type_, property_types)?;
    let total_properties = base_surfaces
        .iter()
        .try_fold(plan.properties.len(), |count, base| {
            count.checked_add(base.properties.len())
        })
        .ok_or_else(|| capacity(plan))?;
    let mut expected_properties = Vec::new();
    let mut expected_entries = Vec::new();
    let mut seen_names = HashSet::new();
    let mut inherited_by_name = HashMap::new();
    expected_properties
        .try_reserve_exact(total_properties)
        .map_err(|_| capacity(plan))?;
    expected_entries
        .try_reserve_exact(total_properties)
        .map_err(|_| capacity(plan))?;
    seen_names
        .try_reserve(total_properties)
        .map_err(|_| capacity(plan))?;
    inherited_by_name
        .try_reserve(total_properties)
        .map_err(|_| capacity(plan))?;

    for (property, property_type) in plan.properties.iter().zip(property_types) {
        let record = store
            .symbol(property.symbol)
            .ok_or_else(|| invalid(plan, type_))?;
        if planned_declared_property_key(store, property) != Some(record.name())
            || record.parent() != Some(plan.symbol)
            || !inherited_index_infos.is_empty()
                && (record.flags().contains(SymbolFlags::OPTIONAL) != property.optional
                    || record.flags().contains(SymbolFlags::METHOD)
                        && valid_interface_method_value(store, property.symbol, *property_type)
                            .is_none())
        {
            return Err(invalid(plan, type_));
        }
        for &index in inherited_index_infos {
            if !inherited_index_property_compatible(
                store,
                index,
                record.name(),
                *property_type,
                property.optional,
            )
            .ok_or_else(|| invalid(plan, type_))?
            {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: plan.node,
                    kind: SyntaxKind::InterfaceDeclaration,
                });
            }
        }
        let name = record.name().to_owned();
        if !seen_names.insert(name.clone()) {
            return Err(invalid(plan, type_));
        }
        expected_entries.push((name, property.symbol));
        expected_properties.push(property.symbol);
    }
    for (planned, surface) in heritage.bases.iter().zip(&base_surfaces) {
        for &property in &surface.properties {
            let record = store.symbol(property).ok_or_else(|| invalid(plan, type_))?;
            let name = record.name().to_owned();
            if let Some(previous) = inherited_by_name.get(&name).copied() {
                if !matching_inherited_property_contract(store, previous, property) {
                    return Err(PropertyObjectError::UnsupportedMember {
                        node: planned.node,
                        kind: SyntaxKind::ExpressionWithTypeArguments,
                    });
                }
                continue;
            }
            inherited_by_name.insert(name.clone(), property);
            if seen_names.insert(name.clone()) {
                expected_entries.push((name, property));
                expected_properties.push(property);
            }
        }
    }

    for (index, property) in plan.properties.iter().enumerate() {
        let Some(base_property) = inherited_by_name
            .get(
                &planned_declared_property_key(store, property)
                    .ok_or_else(|| invalid(plan, type_))?
                    .to_owned(),
            )
            .copied()
        else {
            continue;
        };
        let own_type = *property_types
            .get(index)
            .ok_or_else(|| invalid(plan, type_))?;
        let base_type = store
            .value_symbol_links(base_property)
            .and_then(|links| links.resolved_type)
            .ok_or_else(|| invalid(plan, type_))?;
        let base_optional = store
            .symbol(base_property)
            .is_some_and(|record| record.flags().contains(SymbolFlags::OPTIONAL));
        let own_method = store
            .symbol(property.symbol)
            .is_some_and(|record| record.flags().contains(SymbolFlags::METHOD));
        let base_method = store
            .symbol(base_property)
            .is_some_and(|record| record.flags().contains(SymbolFlags::METHOD));
        let compatible = if own_method && base_method {
            matching_interface_method_contract(store, property.symbol, base_property)
        } else if own_method || base_method {
            false
        } else {
            store.is_type_assignable_to(own_type, base_type) == Ok(true)
        };
        if property.optional && !base_optional || !compatible {
            return Err(PropertyObjectError::UnsupportedMember {
                node: property.declaration,
                kind: store
                    .source_node_kind(property.declaration)
                    .unwrap_or(SyntaxKind::PropertySignature),
            });
        }
    }

    if declared_state == DirectInterfaceDeclaredState::Resolved {
        let TypeData::Interface(interface) = store
            .type_payload(type_)
            .ok_or_else(|| invalid(plan, type_))?
            .data()
        else {
            return Err(invalid(plan, type_));
        };
        if interface.resolved_base_types.as_deref() != Some(base_types)
            || !validate_planned_interface_heritage_members_with_array_targets(
                store,
                plan,
                type_,
                array_targets,
            )
            || interface.reference.object.structured.properties.as_deref()
                != (!expected_properties.is_empty()).then_some(expected_properties.as_slice())
            || interface.reference.object.structured.index_infos.as_deref()
                != (!inherited_index_infos.is_empty()).then_some(inherited_index_infos)
            || !exact_member_table(
                store,
                &expected_entries,
                interface.reference.object.structured.members,
            )
        {
            return Err(invalid(plan, type_));
        }
        return Ok(type_);
    }

    let mut staged_base_types = Vec::new();
    staged_base_types
        .try_reserve_exact(base_types.len())
        .map_err(|_| capacity(plan))?;
    staged_base_types.extend_from_slice(base_types);
    let mut staged_index_infos = Vec::new();
    staged_index_infos
        .try_reserve_exact(inherited_index_infos.len())
        .map_err(|_| capacity(plan))?;
    staged_index_infos.extend_from_slice(inherited_index_infos);
    let prepared_members = if expected_entries.is_empty() {
        None
    } else {
        Some(PreparedSymbolTable::new(expected_entries.len()).ok_or_else(|| capacity(plan))?)
    };
    let missing_value_links = plan
        .properties
        .iter()
        .filter(|property| store.value_symbol_links(property.symbol).is_none())
        .count();
    let missing_accessor_links = plan
        .accessors
        .iter()
        .filter_map(|accessor| accessor.parameter)
        .filter(|parameter| store.value_symbol_links(parameter.symbol).is_none())
        .count();
    let missing_value_links = missing_value_links
        .checked_add(missing_accessor_links)
        .ok_or_else(|| capacity(plan))?;
    if !store.try_reserve_checker_symbol_allocations(0, usize::from(prepared_members.is_some()))
        || !store.try_reserve_value_symbol_links(missing_value_links)
        || !store.try_reserve_direct_interface_heritage_provenance(1)
    {
        return Err(capacity(plan));
    }

    // Every allocation and fallible semantic check precedes this point. The
    // prepared table owns entry capacity, the table arena, sparse value-link
    // map, and heritage-provenance map are reserved, and the base/property
    // vectors are already staged.
    let members = prepared_members.map(|prepared| store.alloc_prepared_symbol_table(prepared));
    if let Some(members) = members {
        for (name, property) in expected_entries {
            assert_eq!(store.insert_symbol(members, name, property), Some(None));
        }
    }
    assert!(store.publish_direct_interface_heritage_provenance(
        type_,
        DirectInterfaceHeritageProvenance {
            owner_symbol: plan.symbol,
            base_symbol: planned_base.symbol,
            base_type,
            second_base,
        },
    ));
    publish_prepared_direct_interface_declared_properties(
        store,
        plan,
        type_,
        property_types,
        declared_state,
    );
    assert!(store.set_interface_base_resolution(type_, true, None, Some(staged_base_types),));
    assert!(store.set_structured_type_members(
        type_,
        members,
        (!expected_properties.is_empty()).then_some(expected_properties),
        None,
        None,
        (!staged_index_infos.is_empty()).then_some(staged_index_infos),
    ));
    Ok(type_)
}

/// Publishes one callable interface and its single callable base.
///
/// The derived declaration owns its `__call` symbol and declared signatures.
/// Its final callable list contains those signatures first, followed by the
/// base's existing signature identities.
pub(super) fn resolve_direct_interface_callable_members(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
    call_types: &[ResolvedCallSignatureTypes],
    base_types: &[TypeId],
) -> Result<TypeId, PropertyObjectError> {
    let Some(heritage) = plan.heritage.as_ref() else {
        return Err(invalid(plan, type_));
    };
    let [planned_base] = heritage.bases.as_slice() else {
        return Err(invalid(plan, type_));
    };
    let [base_type] = base_types else {
        return Err(invalid(plan, type_));
    };
    let base_type = *base_type;
    let Some(first) = plan.call_signatures.first() else {
        return Err(invalid(plan, type_));
    };
    if plan.kind != PropertyObjectKind::Interface
        || !plan.properties.is_empty()
        || !plan.indexes.is_empty()
        || plan.call_signatures.len() != call_types.len()
        || plan.call_signatures.iter().any(|signature| {
            signature.symbol != first.symbol
                || store.source_node_kind(signature.declaration) != Some(SyntaxKind::CallSignature)
        })
    {
        return Err(invalid(plan, type_));
    }

    let Some(owner) = store.symbol(plan.symbol) else {
        return Err(invalid(plan, type_));
    };
    let Some(call_symbol) = store.symbol(first.symbol) else {
        return Err(invalid(plan, type_));
    };
    let Some(declared_members) = plan.members.and_then(|members| store.symbol_table(members))
    else {
        return Err(invalid(plan, type_));
    };
    if owner.members() != plan.members
        || declared_members.len() != 1
        || declared_members.get(InternalSymbolName::Call.as_ref()) != Some(first.symbol)
        || call_symbol.flags() != SymbolFlags::SIGNATURE
        || call_symbol.check_flags() != CheckFlags::NONE
        || call_symbol.name() != InternalSymbolName::Call.as_ref()
        || call_symbol.parent() != Some(plan.symbol)
        || call_symbol.value_declaration().is_some()
        || call_symbol.members().is_some()
        || call_symbol.exports().is_some()
        || call_symbol.export_symbol().is_some()
        || store.get_merged_symbol(first.symbol) != Some(first.symbol)
        || call_symbol.declarations().is_none_or(|declarations| {
            !declarations.iter().copied().eq(plan
                .call_signatures
                .iter()
                .map(|signature| signature.declaration))
        })
    {
        return Err(invalid(plan, type_));
    }

    let Some(base_record) = store.type_payload(base_type) else {
        return Err(invalid(plan, type_));
    };
    let TypeData::Interface(base) = base_record.data() else {
        return Err(invalid(plan, type_));
    };
    let Some(base_calls) = base.declared_call_signatures.as_deref() else {
        return Err(invalid(plan, type_));
    };
    if base_record.symbol() != Some(planned_base.symbol)
        || base_type == type_
        || base_calls.is_empty()
        || base.resolved_base_types.is_some()
        || base.reference.object.structured.properties.is_some()
        || base.reference.object.structured.index_infos.is_some()
        || !matches!(
            validate_stored_declared_call_set(store, base_type),
            StoredDeclaredCallSetValidation::Valid(_)
        )
    {
        return Err(invalid(plan, type_));
    }

    let mut inherited_calls = Vec::new();
    inherited_calls
        .try_reserve_exact(base_calls.len())
        .map_err(|_| capacity(plan))?;
    inherited_calls.extend_from_slice(base_calls);
    let Some(record) = store.type_payload(type_) else {
        return Err(invalid(plan, type_));
    };
    if record.object_flags() == ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED {
        if !validate_planned_interface_heritage_members(store, plan, type_)
            || super::object_members::validate_resolved_declared_member_types(
                store,
                plan,
                &[],
                &[],
                call_types,
            )
            .is_err()
        {
            return Err(invalid(plan, type_));
        }
        return Ok(type_);
    }

    let state = super::object_members::interface_state(store, plan, type_)?;
    if state != PropertyObjectState::Shell(type_)
        || store.direct_interface_heritage_provenance(type_).is_some()
    {
        return Err(invalid(plan, type_));
    }
    let total_calls = plan
        .call_signatures
        .len()
        .checked_add(inherited_calls.len())
        .ok_or_else(|| capacity(plan))?;
    let mut all_calls = Vec::new();
    all_calls
        .try_reserve_exact(total_calls)
        .map_err(|_| capacity(plan))?;
    let mut resolved_bases = Vec::new();
    resolved_bases
        .try_reserve_exact(1)
        .map_err(|_| capacity(plan))?;
    resolved_bases.push(base_type);
    let prepared_members = PreparedSymbolTable::new(1).ok_or_else(|| capacity(plan))?;
    if !store.try_reserve_checker_symbol_allocations(0, 1)
        || !store.try_reserve_direct_interface_heritage_provenance(1)
    {
        return Err(capacity(plan));
    }

    publish_declared_members(store, plan, state, &[], &[], call_types)?;
    let TypeData::Interface(interface) = store
        .type_payload(type_)
        .expect("declared-call publication preserves its interface")
        .data()
    else {
        unreachable!("declared-call publication preserves its interface")
    };
    all_calls.extend_from_slice(
        interface
            .declared_call_signatures
            .as_deref()
            .expect("declared-call publication creates source signatures"),
    );
    all_calls.extend_from_slice(&inherited_calls);
    let members = store.alloc_prepared_symbol_table(prepared_members);
    assert_eq!(
        store.insert_symbol(
            members,
            EscapedName::internal(InternalSymbolName::Call),
            first.symbol,
        ),
        Some(None)
    );
    assert!(store.publish_direct_interface_heritage_provenance(
        type_,
        DirectInterfaceHeritageProvenance {
            owner_symbol: plan.symbol,
            base_symbol: planned_base.symbol,
            base_type,
            second_base: None,
        },
    ));
    assert!(store.set_interface_base_resolution(type_, true, None, Some(resolved_bases)));
    assert!(store.set_structured_type_members(
        type_,
        Some(members),
        None,
        Some(all_calls),
        None,
        None,
    ));
    Ok(type_)
}

/// Plan-aware warm-cache proof used by contextual typing and diagnostics.
///
/// In addition to exact final member reconstruction, this verifies that the
/// cached base types and canonical symbols exactly match the syntax plan.
pub(super) fn validate_planned_interface_heritage_members(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
) -> bool {
    validate_planned_interface_heritage_members_with_array_targets(store, plan, type_, None)
}

pub(super) fn validate_planned_interface_heritage_members_with_array_targets(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    let Some(heritage) = plan.heritage.as_ref() else {
        return false;
    };
    if !matches!(heritage.bases.as_slice(), [_] | [_, _]) {
        return false;
    }
    let planned_base = &heritage.bases[0];
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    let TypeData::Interface(interface) = record.data() else {
        return false;
    };
    let Some(base_types) = interface.resolved_base_types.as_deref() else {
        return false;
    };
    if base_types.len() != heritage.bases.len() {
        return false;
    }
    let base_type = base_types[0];
    let second_base = heritage
        .bases
        .get(1)
        .zip(base_types.get(1))
        .map(|(base, type_)| (base.symbol, *type_));
    let expected_provenance = DirectInterfaceHeritageProvenance {
        owner_symbol: plan.symbol,
        base_symbol: planned_base.symbol,
        base_type,
        second_base,
    };
    if record.symbol() != Some(plan.symbol)
        || interface.declared_members != plan.members
        || store.direct_interface_heritage_provenance(type_) != Some(expected_provenance)
        || heritage
            .bases
            .iter()
            .zip(base_types)
            .any(|(base, type_)| !planned_base_matches(store, base, *type_))
    {
        return false;
    }
    let Some(surface) = validate_direct_heritage_property_interface(store, type_, array_targets)
    else {
        return false;
    };
    let planned_properties = plan
        .properties
        .iter()
        .map(|property| property.symbol)
        .collect::<Vec<_>>();
    let planned_calls = plan
        .call_signatures
        .iter()
        .map(|signature| {
            store
                .signature_links(signature.declaration)?
                .resolved_signature
                .signature()
        })
        .collect::<Option<Vec<_>>>();
    let Some(planned_calls) = planned_calls else {
        return false;
    };
    surface.owner == plan.symbol
        && surface.declared_properties == planned_properties
        && surface.declared_call_signatures == planned_calls
        && plan
            .properties
            .iter()
            .all(|property| valid_declared_property_check_flags(store, property))
}

/// Semantic-only exact proof consumed by structural relations.
pub(super) fn validate_interface_heritage_members(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> InterfaceHeritageMembersValidation {
    validate_interface_heritage_members_with_array_targets(store, type_, None)
}

pub(super) fn validate_interface_heritage_members_with_array_targets(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> InterfaceHeritageMembersValidation {
    let retained_provenance = store.direct_interface_heritage_provenance(type_).is_some();
    let Some(TypeData::Interface(interface)) = store
        .type_payload(type_)
        .map(super::type_records::TypeRecord::data)
    else {
        return if retained_provenance {
            InterfaceHeritageMembersValidation::Malformed
        } else {
            InterfaceHeritageMembersValidation::NotHeritage
        };
    };
    if interface.resolved_base_types.is_none() {
        return if retained_provenance {
            InterfaceHeritageMembersValidation::Malformed
        } else {
            InterfaceHeritageMembersValidation::NotHeritage
        };
    }
    if validate_direct_heritage_property_interface(store, type_, array_targets).is_some() {
        InterfaceHeritageMembersValidation::Valid
    } else {
        InterfaceHeritageMembersValidation::Malformed
    }
}

fn validate_no_heritage_property_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<ValidatedInterfaceSurface> {
    validate_property_interface(store, type_, false, array_targets)
}

fn validate_generic_base_property_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<ValidatedInterfaceSurface> {
    let reference = validate_direct_generic_reference(store, type_).ok()?;
    let members = validate_generic_interface_members(store, type_, array_targets).ok()??;
    let record = store.type_payload(type_)?;
    let owner = record.symbol()?;
    let structured = record.data().structured()?;
    if members.target() != reference.target
        || record.alias().is_some()
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
    {
        return None;
    }
    Some(ValidatedInterfaceSurface {
        owner,
        declared_properties: Vec::new(),
        properties: members.properties().to_vec(),
        index_infos: structured.index_infos.clone().unwrap_or_default(),
        declared_call_signatures: Vec::new(),
        call_signatures: Vec::new(),
    })
}

/// Finds the original reference of a proxy borrowed through interface heritage.
pub(super) fn inherited_generic_property_reference(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    property: SemanticSymbolId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<TypeId> {
    if validate_interface_heritage_members_with_array_targets(store, receiver, array_targets)
        != InterfaceHeritageMembersValidation::Valid
        || store
            .type_payload(receiver)?
            .data()
            .structured()?
            .properties
            .as_deref()
            .is_none_or(|properties| !properties.contains(&property))
    {
        return None;
    }
    let property_record = store.symbol(property)?;
    if !property_record.flags().contains(SymbolFlags::TRANSIENT)
        || !property_record
            .check_flags()
            .contains(CheckFlags::INSTANTIATED)
    {
        return None;
    }
    let links = store.value_symbol_links(property)?;
    let target = links.target?;
    let owner = store.symbol(target)?.parent()?;
    let owner_type = store.declared_type_links(owner)?.declared_type?;
    let TypeData::Interface(interface) = store.type_payload(owner_type)?.data() else {
        return None;
    };
    let original = store.map_type(links.mapper?, interface.this_type?)?;
    let original_members =
        validate_generic_interface_members(store, original, array_targets).ok()??;
    if !original_members.properties().contains(&property) {
        return None;
    }
    let mut pending = vec![receiver];
    let mut seen = HashSet::new();
    while let Some(current) = pending.pop() {
        if !seen.insert(current) {
            continue;
        }
        if let Some(heritage) = store.direct_interface_heritage_provenance(current) {
            if let Some((_, second)) = heritage.second_base {
                pending.push(second);
            }
            pending.push(heritage.base_type);
        } else if validate_direct_generic_reference(store, current).is_ok()
            && validate_generic_interface_members(store, current, array_targets)
                .ok()
                .flatten()
                .is_some_and(|members| members.properties().contains(&property))
        {
            return Some(original);
        }
    }
    None
}

fn validate_direct_heritage_property_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<ValidatedInterfaceSurface> {
    validate_property_interface(store, type_, true, array_targets)
}

fn validate_property_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    requires_direct_base: bool,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<ValidatedInterfaceSurface> {
    validate_property_interface_worker(
        store,
        type_,
        requires_direct_base,
        array_targets,
        &mut HashSet::new(),
    )
}

/// Reads a key only after the complete nongeneric interface has been validated.
pub(super) fn validated_interface_property_by_key(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    name: EscapedNameRef<'_>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<Option<ResolvedOwnProperty>> {
    let inherited = store.direct_interface_heritage_provenance(type_).is_some();
    let view = validate_property_interface(store, type_, inherited, array_targets)?;
    let members = store.type_payload(type_)?.data().structured()?.members;
    let Some(members) = members else {
        return Some(None);
    };
    let Some(symbol) = store.symbol_table(members)?.get(name) else {
        return Some(None);
    };
    if !view.properties.contains(&symbol) {
        return None;
    }
    let record = store.symbol(symbol)?;
    Some(Some(ResolvedOwnProperty {
        symbol,
        type_: store.value_symbol_links(symbol)?.resolved_type?,
        optional: record.flags().contains(SymbolFlags::OPTIONAL),
        readonly: record.check_flags().contains(CheckFlags::READONLY),
    }))
}

fn validate_property_interface_worker(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    requires_direct_base: bool,
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
) -> Option<ValidatedInterfaceSurface> {
    if !active.insert(type_) {
        return None;
    }
    let record = store.type_payload(type_)?;
    let reference_identity =
        requires_direct_base && validate_nongeneric_interface_argument_origin(store, type_).is_ok();
    if record.object_flags().contains(ObjectFlags::REFERENCE) && !reference_identity {
        let result = validate_generic_base_property_interface(store, type_, array_targets);
        assert!(active.remove(&type_));
        return result;
    }
    let TypeData::Interface(interface) = record.data() else {
        return None;
    };
    let owner = record.symbol()?;
    let heritage_provenance = if requires_direct_base {
        let provenance = store.direct_interface_heritage_provenance(type_)?;
        (provenance.owner_symbol == owner).then_some(provenance)?
    } else {
        if store.direct_interface_heritage_provenance(type_).is_some() {
            return None;
        }
        DirectInterfaceHeritageProvenance {
            owner_symbol: owner,
            base_symbol: owner,
            base_type: type_,
            second_base: None,
        }
    };
    let owner_record = store.symbol(owner)?;
    let owner_declarations = owner_record
        .declarations()
        .filter(|declarations| !declarations.is_empty())?;
    let identity_flags = ObjectFlags::INTERFACE
        | if reference_identity {
            ObjectFlags::REFERENCE
        } else {
            ObjectFlags::NONE
        };
    let object_flags = if reference_identity {
        record.object_flags()
            & !(ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
                | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES)
    } else {
        record.object_flags()
    };
    if record.flags() != TypeFlags::OBJECT
        || object_flags != identity_flags | ObjectFlags::MEMBERS_RESOLVED
        || record.alias().is_some()
        || owner_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.value_declaration().is_some()
        || !valid_declared_member_table(store, owner, interface.declared_members)
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || owner_declarations.iter().any(|declaration| {
            store.source_node_kind(*declaration) != Some(SyntaxKind::InterfaceDeclaration)
        })
        || store
            .declared_type_links(owner)
            .is_none_or(|links| links.declared_type != Some(type_))
        || !valid_thisless_interface_identity(interface) && !reference_identity
        || !interface.base_types_resolved
        || !interface.declared_members_resolved
        || interface.resolved_base_constructor_type.is_some()
        || interface.declared_construct_signatures.is_some()
    {
        return None;
    }
    let structured = &interface.reference.object.structured;
    if structured.constrained != ConstrainedTypeData::default()
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return None;
    }

    let declared = declared_members(
        store,
        owner,
        owner_declarations,
        type_,
        interface.declared_members,
        interface.declared_index_infos.as_deref(),
        interface.declared_call_signatures.as_deref(),
    )?;
    if requires_direct_base && !declared.index_infos.is_empty()
        || !declared.call_signatures.is_empty()
            && (!declared.properties.is_empty() || !declared.index_infos.is_empty())
    {
        return None;
    }
    let base_types = match (
        requires_direct_base,
        interface.resolved_base_types.as_deref(),
        heritage_provenance.second_base,
    ) {
        (false, None, None) => &[][..],
        (true, Some([base_type]), None)
            if *base_type != type_ && *base_type == heritage_provenance.base_type =>
        {
            interface.resolved_base_types.as_deref()?
        }
        (true, Some([first, second]), Some((second_symbol, second_type)))
            if *first != type_
                && *second != type_
                && *first != *second
                && *first == heritage_provenance.base_type
                && *second == second_type
                && second_symbol != owner
                && second_symbol != heritage_provenance.base_symbol =>
        {
            interface.resolved_base_types.as_deref()?
        }
        _ => return None,
    };
    let mut base_properties = Vec::new();
    let mut inherited_index_infos = Vec::new();
    let mut inherited_call_signatures = Vec::new();
    let mut inherited_by_name = HashMap::new();
    for (index, base_type) in base_types.iter().copied().enumerate() {
        let inherited_base = store
            .direct_interface_heritage_provenance(base_type)
            .is_some();
        let base = validate_property_interface_worker(
            store,
            base_type,
            inherited_base,
            array_targets,
            active,
        )?;
        let expected_owner = if index == 0 {
            heritage_provenance.base_symbol
        } else {
            heritage_provenance.second_base?.0
        };
        if base.owner != expected_owner
            || base_types.len() == 2
                && (!base.index_infos.is_empty() || !base.call_signatures.is_empty())
            || !base.call_signatures.is_empty()
                && (!declared.properties.is_empty()
                    || !declared.index_infos.is_empty()
                    || !base.properties.is_empty()
                    || !base.index_infos.is_empty())
        {
            return None;
        }
        inherited_index_infos.extend_from_slice(&base.index_infos);
        inherited_call_signatures.extend_from_slice(&base.call_signatures);
        for property in base.properties {
            let name = store.symbol(property)?.name().to_owned();
            if let Some(previous) = inherited_by_name.get(&name).copied() {
                if !matching_inherited_property_contract(store, previous, property) {
                    return None;
                }
                continue;
            }
            inherited_by_name.insert(name, property);
            base_properties.push(property);
        }
    }

    let total = declared
        .properties
        .len()
        .checked_add(base_properties.len())?;
    let mut expected = Vec::with_capacity(total);
    let mut seen_names = HashSet::with_capacity(total);
    for property in &declared.properties {
        let record = store.symbol(*property)?;
        if !seen_names.insert(record.name().to_owned()) {
            return None;
        }
        expected.push(*property);
    }
    for property in &base_properties {
        let record = store.symbol(*property)?;
        if seen_names.insert(record.name().to_owned()) {
            expected.push(*property);
        }
    }
    for &index in &inherited_index_infos {
        for &property in &declared.properties {
            let record = store.symbol(property)?;
            let property_type = store.value_symbol_links(property)?.resolved_type?;
            if !inherited_index_property_compatible(
                store,
                index,
                record.name(),
                property_type,
                record.flags().contains(SymbolFlags::OPTIONAL),
            )? {
                return None;
            }
        }
    }
    let expected_index_infos = if requires_direct_base {
        inherited_index_infos
    } else {
        declared.index_infos
    };
    let mut expected_call_signatures = declared.call_signatures.clone();
    expected_call_signatures.extend_from_slice(&inherited_call_signatures);
    let actual = structured.properties.as_deref().unwrap_or_default();
    if actual.is_empty() != structured.properties.is_none()
        || actual != expected.as_slice()
        || structured.index_infos.as_deref()
            != (!expected_index_infos.is_empty()).then_some(expected_index_infos.as_slice())
        || structured.signatures.as_deref()
            != (!expected_call_signatures.is_empty()).then_some(expected_call_signatures.as_slice())
        || structured.call_signature_count != expected_call_signatures.len()
        || !exact_property_table(
            store,
            &expected,
            structured.members,
            if requires_direct_base {
                None
            } else {
                declared.index_symbol
            },
            declared.call_symbol,
        )
    {
        return None;
    }
    let result = ValidatedInterfaceSurface {
        owner,
        declared_properties: declared.properties,
        properties: expected,
        index_infos: expected_index_infos,
        declared_call_signatures: declared.call_signatures,
        call_signatures: expected_call_signatures,
    };
    assert!(active.remove(&type_));
    Some(result)
}

/// Accepts the raw table or its exact late-bound member expansion.
pub(super) fn valid_declared_member_table(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declared: Option<SymbolTableId>,
) -> bool {
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let Some(computed_count) = store.source_computed_member_count(owner) else {
        return false;
    };
    if owner_record.members() == declared {
        return computed_count == 0;
    }
    let raw = match owner_record.members() {
        Some(table) => {
            let Some(raw) = store.symbol_table(table) else {
                return false;
            };
            Some(raw)
        }
        None if store.source_symbol_has_only_computed_members(owner) => None,
        None => return false,
    };
    let Some(declared) = declared.and_then(|table| store.symbol_table(table)) else {
        return false;
    };
    let Some(resolved) = store
        .members_and_exports_links(owner)
        .and_then(|links| links.table(MembersOrExportsResolutionKind::ResolvedMembers))
        .and_then(|table| store.symbol_table(table))
    else {
        return false;
    };
    if declared.len() != resolved.len()
        || computed_count == 0
        || raw
            .into_iter()
            .flat_map(ts_binder::semantic::SymbolTable::iter)
            .any(|(name, symbol)| {
                resolved
                    .get(name)
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    != store.get_merged_symbol(symbol)
            })
    {
        return false;
    }
    let mut actual_computed = 0usize;
    let mut computed_groups = 0usize;
    let mut source_declarations = HashSet::new();
    let valid = declared.iter().all(|(name, symbol)| {
        if resolved.get(name) != Some(symbol) {
            return false;
        }
        if let Some(raw) = raw.and_then(|raw| raw.get(name)) {
            return store.get_merged_symbol(raw) == Some(symbol);
        }
        let Some(member) = store.symbol(symbol) else {
            return false;
        };
        let Some(declarations) = member.declarations() else {
            return false;
        };
        let Some(links) = store.value_symbol_links(symbol) else {
            return false;
        };
        let Some(count) = actual_computed.checked_add(declarations.len()) else {
            return false;
        };
        let Some(groups) = computed_groups.checked_add(1) else {
            return false;
        };
        if declarations
            .iter()
            .any(|declaration| !source_declarations.insert(*declaration))
        {
            return false;
        }
        actual_computed = count;
        computed_groups = groups;
        valid_late_bound_unique_symbol_member(
            store,
            owner,
            symbol,
            declarations,
            links,
            Some(resolved),
        )
    });
    valid
        && actual_computed == computed_count
        && raw
            .map_or(0, ts_binder::semantic::SymbolTable::len)
            .checked_add(computed_groups)
            == Some(resolved.len())
}

fn declared_members(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declarations: &[NodeRef],
    type_: TypeId,
    members: Option<SymbolTableId>,
    indexes: Option<&[IndexInfoId]>,
    calls: Option<&[SignatureId]>,
) -> Option<ValidatedDeclaredMembers> {
    let Some(members) = members else {
        return (indexes.is_none() && calls.is_none()).then_some(ValidatedDeclaredMembers {
            properties: Vec::new(),
            index_symbol: None,
            index_infos: Vec::new(),
            call_symbol: None,
            call_signatures: Vec::new(),
        });
    };
    let table = store.symbol_table(members)?;
    if table.is_empty() {
        return None;
    }
    let mut properties = Vec::with_capacity(table.len());
    let mut seen_declarations = HashSet::with_capacity(table.len());
    let mut index_symbol = None;
    let mut call_symbol = None;
    for (name, property) in table.iter() {
        let record = store.symbol(property)?;
        let declarations = record
            .declarations()
            .filter(|declarations| !declarations.is_empty())?;
        let mut earliest = None;
        for declaration in declarations {
            let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(*declaration)
            else {
                return None;
            };
            let owner_index = owner_declarations
                .iter()
                .position(|owner_declaration| *owner_declaration == parent)?;
            if !declaration.is_for(parent.arena, parent.file)
                || !seen_declarations.insert(*declaration)
            {
                return None;
            }
            let position = (owner_index, *declaration);
            if earliest.is_none_or(|current| position < current) {
                earliest = Some(position);
            }
        }
        let (owner_index, declaration) = earliest?;
        if record.name() != name || store.get_parent_of_symbol(property) != Some(owner) {
            return None;
        }
        if name == InternalSymbolName::Index.as_ref() {
            if index_symbol.is_some()
                || !valid_index_symbol(store, owner, owner_declarations, property, indexes?)
            {
                return None;
            }
            index_symbol = Some(property);
            continue;
        }
        if name == InternalSymbolName::Call.as_ref() {
            if call_symbol.is_some()
                || !valid_call_symbol(store, owner, owner_declarations, type_, property, calls?)
            {
                return None;
            }
            call_symbol = Some(property);
            continue;
        }
        if !valid_property_symbol(store, property) {
            return None;
        }
        properties.push((owner_index, declaration, property));
    }
    properties.sort_unstable_by_key(|(owner_index, declaration, _)| (*owner_index, *declaration));
    if properties
        .windows(2)
        .any(|pair| (pair[0].0, pair[0].1) >= (pair[1].0, pair[1].1))
    {
        return None;
    }
    if index_symbol.is_some() != indexes.is_some()
        || indexes.is_some_and(<[IndexInfoId]>::is_empty)
        || call_symbol.is_some() != calls.is_some()
        || calls.is_some_and(<[SignatureId]>::is_empty)
    {
        return None;
    }
    Some(ValidatedDeclaredMembers {
        properties: properties
            .into_iter()
            .map(|(_, _, property)| property)
            .collect(),
        index_symbol,
        index_infos: indexes.unwrap_or_default().to_vec(),
        call_symbol,
        call_signatures: calls.unwrap_or_default().to_vec(),
    })
}

pub(super) fn valid_index_symbol(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declarations: &[NodeRef],
    symbol: SemanticSymbolId,
    indexes: &[IndexInfoId],
) -> bool {
    valid_index_symbol_shape(store, owner, owner_declarations, symbol, indexes)
        && indexes.iter().all(|index| {
            store
                .index_info(*index)
                .is_some_and(|info| source_index_info_is_exact(store, owner, info))
        })
}

/// Checks index metadata. Instantiated callers must also prove their source and mapping.
pub(super) fn valid_index_symbol_shape(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declarations: &[NodeRef],
    symbol: SemanticSymbolId,
    indexes: &[IndexInfoId],
) -> bool {
    let Some(record) = store.symbol(symbol) else {
        return false;
    };
    let Some(declarations) = record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
    else {
        return false;
    };
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    if record.flags() != SymbolFlags::SIGNATURE
        || record.check_flags() != CheckFlags::NONE
        || record.name() != InternalSymbolName::Index.as_ref()
        || record.value_declaration().is_some()
        || record.members().is_some()
        || record.exports().is_some()
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || declarations.len() != indexes.len()
    {
        return false;
    }
    let mut seen_indexes = HashSet::with_capacity(indexes.len());
    let mut seen_keys = HashSet::with_capacity(indexes.len());
    indexes
        .iter()
        .zip(declarations)
        .all(|(index, declaration)| {
            let Some(info) = store.index_info(*index) else {
                return false;
            };
            let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(*declaration)
            else {
                return false;
            };
            let key = info.key_type();
            let valid_key = key == bootstrap.string_type
                || key == bootstrap.number_type
                || key == bootstrap.es_symbol_type
                || store
                    .type_payload(key)
                    .is_some_and(|record| record.flags() == TypeFlags::TEMPLATE_LITERAL);
            seen_indexes.insert(*index)
                && seen_keys.insert(key)
                && owner_declarations.contains(&parent)
                && declaration.is_for(parent.arena, parent.file)
                && store.source_node_kind(*declaration) == Some(SyntaxKind::IndexSignature)
                && valid_key
                && store.type_payload(info.value_type()).is_some()
                && info.declaration() == Some(*declaration)
                && info.index_symbol().is_none()
                && info.components().is_empty()
        })
}

fn source_index_info_is_exact(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    info: &IndexInfo,
) -> bool {
    let Some(declaration) = info.declaration() else {
        return false;
    };
    let Some(children) = store.source_direct_children(declaration) else {
        return false;
    };
    let readonly_count = children
        .iter()
        .filter(|child| store.source_node_kind(**child) == Some(SyntaxKind::ReadonlyKeyword))
        .count();
    let Some(parameter) = children
        .iter()
        .copied()
        .find(|child| store.source_node_kind(*child) == Some(SyntaxKind::Parameter))
    else {
        return false;
    };
    if readonly_count > 1
        || children.len() != 2 + readonly_count
        || info.is_readonly() != (readonly_count == 1)
    {
        return false;
    }
    let Some(parameter_children) = store.source_direct_children(parameter) else {
        return false;
    };
    if parameter_children.len() != 2 {
        return false;
    }
    let Some(name) = parameter_children
        .iter()
        .copied()
        .find(|child| store.source_node_kind(*child) == Some(SyntaxKind::Identifier))
    else {
        return false;
    };
    if store
        .source_identifier_text(name)
        .is_none_or(|name| name.is_empty() || name == "this")
    {
        return false;
    }
    let Some(key) = parameter_children
        .iter()
        .copied()
        .find(|child| *child != name)
    else {
        return false;
    };
    let Some(value) = children.iter().copied().find(|child| {
        *child != parameter && store.source_node_kind(*child) != Some(SyntaxKind::ReadonlyKeyword)
    }) else {
        return false;
    };
    matches!(
        store.source_node_kind(key),
        Some(
            SyntaxKind::StringKeyword
                | SyntaxKind::NumberKeyword
                | SyntaxKind::SymbolKeyword
                | SyntaxKind::TemplateLiteralType
        )
    ) && source_index_annotation_is_exact(store, owner, declaration, key, info.key_type())
        && source_index_annotation_is_exact(store, owner, declaration, value, info.value_type())
}

fn source_index_annotation_is_exact(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    mut annotation: NodeRef,
    type_: TypeId,
) -> bool {
    while store.source_node_kind(annotation) == Some(SyntaxKind::ParenthesizedType) {
        if store.type_node_links(annotation).is_some_and(|links| {
            links.outer_type_parameters.is_some()
                || links.resolved_type.is_some_and(|cached| cached != type_)
        }) {
            return false;
        }
        let Some(children) = store.source_direct_children(annotation) else {
            return false;
        };
        let [inner] = children.as_slice() else {
            return false;
        };
        annotation = *inner;
    }
    let Some(kind) = store.source_node_kind(annotation) else {
        return false;
    };
    if !kind.is_keyword_type()
        && !(SyntaxKind::FIRST_TYPE_NODE as u16..=SyntaxKind::LAST_TYPE_NODE as u16)
            .contains(&(kind as u16))
    {
        return false;
    }
    // Source parameters require the same proof before and after node links are published.
    let Some((source_parameter, text)) =
        source_index_type_parameter(store, declaration, annotation)
    else {
        return store.source_direct_type_annotation_is_exact(annotation, type_);
    };
    if store.type_node_links(annotation).is_some_and(|links| {
        links.resolved_type.is_some_and(|cached| cached != type_)
            || links.outer_type_parameters.is_some()
    }) {
        return false;
    }
    let Some([Some(raw_parameter), _]) = store
        .symbol_store()
        .source_binding_symbols(source_parameter)
    else {
        return false;
    };
    let Some(parameter) = store.get_merged_symbol(raw_parameter) else {
        return false;
    };
    if cached_ordinary_type_parameter_owner(store, type_) != Some(parameter) {
        return false;
    }
    let Some(record) = store.symbol(parameter) else {
        return false;
    };
    store.get_parent_of_symbol(parameter) == Some(owner)
        && record.name().as_utf8() == Some(text)
        && store.symbol_node_links(annotation).is_none_or(|links| {
            links
                .resolved_symbol
                .is_none_or(|symbol| store.get_merged_symbol(symbol) == Some(parameter))
        })
        && record.declarations().is_some_and(|declarations| {
            declarations.contains(&source_parameter)
                && declarations.iter().all(|declaration| {
                    store.source_node_kind(*declaration) == Some(SyntaxKind::TypeParameter)
                        && source_binding_matches(store, *declaration, parameter)
                        && matches!(
                            store.source_node_parent(*declaration),
                            Some(SourceNodeParent::Parent(parent))
                                if source_binding_matches(store, parent, owner)
                        )
                        && store
                            .source_child_with_kind(*declaration, SyntaxKind::Identifier)
                            .and_then(|name| store.source_identifier_text(name))
                            == Some(text)
                })
        })
}

fn source_binding_matches(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
) -> bool {
    store
        .symbol_store()
        .source_binding_symbols(declaration)
        .is_some_and(|symbols| {
            symbols
                .into_iter()
                .flatten()
                .any(|bound| store.get_merged_symbol(bound) == Some(symbol))
        })
}

/// Finds the actual owner parameter before checking any mutable type links.
fn source_index_type_parameter(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    annotation: NodeRef,
) -> Option<(NodeRef, &str)> {
    if store.source_node_kind(annotation) != Some(SyntaxKind::TypeReference) {
        return None;
    }
    let children = store.source_direct_children(annotation)?;
    let [name] = children.as_slice() else {
        return None;
    };
    let text = store.source_identifier_text(*name)?;
    let SourceNodeParent::Parent(owner_declaration) = store.source_node_parent(declaration)? else {
        return None;
    };
    let parameter = store
        .source_direct_children(owner_declaration)?
        .into_iter()
        .find(|parameter| {
            store.source_node_kind(*parameter) == Some(SyntaxKind::TypeParameter)
                && store
                    .source_child_with_kind(*parameter, SyntaxKind::Identifier)
                    .and_then(|name| store.source_identifier_text(name))
                    == Some(text)
        })?;
    Some((parameter, text))
}

fn valid_call_symbol(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declarations: &[NodeRef],
    type_: TypeId,
    symbol: SemanticSymbolId,
    signatures: &[SignatureId],
) -> bool {
    let Some(record) = store.symbol(symbol) else {
        return false;
    };
    let Some(declarations) = record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
    else {
        return false;
    };
    if record.flags() != SymbolFlags::SIGNATURE
        || record.check_flags() != CheckFlags::NONE
        || record.name() != InternalSymbolName::Call.as_ref()
        || record.value_declaration().is_some()
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent() != Some(owner)
        || record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || declarations.len() != signatures.len()
        || !store.type_has_declared_call_set_provenance(type_)
    {
        return false;
    }

    let mut seen = HashSet::with_capacity(signatures.len());
    signatures
        .iter()
        .copied()
        .zip(declarations)
        .all(|(signature, declaration)| {
            let Some(call) = store.signature(signature) else {
                return false;
            };
            let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(*declaration)
            else {
                return false;
            };
            let Some(parameter_types) = store.callable_signature_parameter_types(signature) else {
                return false;
            };
            let Some(return_type) = call.resolved_return_type() else {
                return false;
            };
            let Some((annotation, null_literal_identity)) =
                store.function_signature_return_annotation(signature)
            else {
                return false;
            };
            let minimum = usize::try_from(call.min_argument_count()).ok();
            if !seen.insert(signature)
                || store.declared_call_set_type_for_signature(signature) != Some(type_)
                || !owner_declarations.contains(&parent)
                || !declaration.is_for(parent.arena, parent.file)
                || store.source_node_kind(*declaration) != Some(SyntaxKind::CallSignature)
                || call.declaration() != Some(*declaration)
                || store.signature_links(*declaration)
                    != Some(&SignatureLinks {
                        resolved_signature: ResolvedSignatureState::Resolved(signature),
                        ..SignatureLinks::default()
                    })
                || call.flags().bits() & !SignatureFlags::HAS_LITERAL_TYPES.bits() != 0
                || call.resolved_min_argument_count() != -1
                || minimum != Some(call.parameters().len())
                || !call.type_parameters().is_empty()
                || call.this_parameter().is_some()
                || call.resolved_type_predicate().is_some()
                || call.target().is_some()
                || call.mapper().is_some()
                || call.isolated_signature_type().is_some()
                || call.composite().is_some()
                || store.signature_has_circular_return_type(signature)
                || parameter_types.len() != call.parameters().len()
                || store.type_payload(return_type).is_none()
                || !valid_call_return_annotation(
                    store,
                    annotation,
                    null_literal_identity,
                    return_type,
                )
            {
                return false;
            }

            let mut parameters = HashSet::with_capacity(parameter_types.len());
            call.parameters().iter().copied().zip(parameter_types).all(
                |(parameter, parameter_type)| {
                    let Some(record) = store.symbol(parameter) else {
                        return false;
                    };
                    let Some([parameter_declaration]) = record.declarations() else {
                        return false;
                    };
                    parameters.insert(parameter)
                        && record.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                        && record.check_flags() == CheckFlags::NONE
                        && record.value_declaration() == Some(*parameter_declaration)
                        && record.members().is_none()
                        && record.exports().is_none()
                        && record.parent().is_none()
                        && record.export_symbol().is_none()
                        && store.get_merged_symbol(parameter) == Some(parameter)
                        && store.source_node_kind(*parameter_declaration)
                            == Some(SyntaxKind::Parameter)
                        && store.source_node_parent(*parameter_declaration)
                            == Some(SourceNodeParent::Parent(*declaration))
                        && store.type_payload(*parameter_type).is_some()
                        && store.value_symbol_links(parameter)
                            == Some(&ValueSymbolLinks {
                                resolved_type: Some(*parameter_type),
                                ..ValueSymbolLinks::default()
                            })
                },
            )
        })
}

fn valid_call_return_annotation(
    store: &CanonicalTypeMapperStore,
    annotation: NodeRef,
    null_literal_identity: bool,
    return_type: TypeId,
) -> bool {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    if null_literal_identity {
        return return_type == bootstrap.null_type;
    }
    let expected = match store.source_node_kind(annotation) {
        Some(SyntaxKind::AnyKeyword) => Some(bootstrap.any_type),
        Some(SyntaxKind::UnknownKeyword) => Some(bootstrap.unknown_type),
        Some(SyntaxKind::StringKeyword) => Some(bootstrap.string_type),
        Some(SyntaxKind::NumberKeyword) => Some(bootstrap.number_type),
        Some(SyntaxKind::BigIntKeyword) => Some(bootstrap.bigint_type),
        Some(SyntaxKind::BooleanKeyword) => Some(bootstrap.boolean_type),
        Some(SyntaxKind::SymbolKeyword) => Some(bootstrap.es_symbol_type),
        Some(SyntaxKind::VoidKeyword) => Some(bootstrap.void_type),
        Some(SyntaxKind::UndefinedKeyword) => Some(bootstrap.undefined_type),
        Some(SyntaxKind::NullKeyword) => Some(bootstrap.null_type),
        Some(SyntaxKind::NeverKeyword) => Some(bootstrap.never_type),
        Some(SyntaxKind::ObjectKeyword) => Some(bootstrap.non_primitive_type),
        Some(SyntaxKind::IntrinsicKeyword) => Some(bootstrap.intrinsic_marker_type),
        _ => store
            .type_node_links(annotation)
            .and_then(|links| links.resolved_type),
    };
    expected == Some(return_type)
}

fn valid_accessor_declarations(
    store: &CanonicalTypeMapperStore,
    flags: SymbolFlags,
    declarations: &[NodeRef],
) -> bool {
    let mut read_count = 0usize;
    let mut write_count = 0usize;
    let mut property_count = 0usize;
    for declaration in declarations {
        match store.source_node_kind(*declaration) {
            Some(SyntaxKind::GetAccessor) => read_count += 1,
            Some(SyntaxKind::SetAccessor) => write_count += 1,
            Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature) => {
                property_count += 1;
            }
            _ => return false,
        }
    }
    read_count <= 1
        && write_count <= 1
        && flags.contains(SymbolFlags::GET_ACCESSOR) == (read_count == 1)
        && flags.contains(SymbolFlags::SET_ACCESSOR) == (write_count == 1)
        && flags.contains(SymbolFlags::PROPERTY) == (property_count != 0)
}

/// Checks the source and key identities of a published computed member.
pub(super) fn valid_late_bound_unique_symbol_member(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    symbol: SemanticSymbolId,
    declarations: &[NodeRef],
    links: &ValueSymbolLinks,
    resolved_table: Option<&ts_binder::semantic::SymbolTable>,
) -> bool {
    let Some(member) = store.symbol(symbol) else {
        return false;
    };
    let method = member.flags().contains(SymbolFlags::METHOD);
    let member_flag = if method {
        SymbolFlags::METHOD
    } else {
        SymbolFlags::PROPERTY
    };
    let allowed_flags = member_flag | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT;
    let allowed_checks = CheckFlags::LATE
        | if method {
            CheckFlags::NONE
        } else {
            CheckFlags::READONLY
        };
    let Some(name_type) = links.name_type else {
        return false;
    };
    let Some(record) = store.type_payload(name_type) else {
        return false;
    };
    let TypeData::UniqueEsSymbol(unique) = record.data() else {
        return false;
    };
    let Some(key) = record.symbol() else {
        return false;
    };
    let Some(key_record) = store.symbol(key) else {
        return false;
    };
    let Some(key_declaration) = key_record.value_declaration() else {
        return false;
    };
    let Some(annotation) = store.source_direct_type_annotation(key_declaration) else {
        return false;
    };
    let key_property = key_record.flags() == SymbolFlags::PROPERTY;
    if !member
        .flags()
        .contains(member_flag | SymbolFlags::TRANSIENT)
        || member.flags().without(allowed_flags) != SymbolFlags::NONE
        || !member.check_flags().contains(CheckFlags::LATE)
        || member.check_flags().bits() & !allowed_checks.bits() != 0
        || !member.name().is_late_bound()
        || member.name() != unique.name.as_ref()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || declarations.is_empty()
        || member.declarations() != Some(declarations)
        || member
            .value_declaration()
            .is_none_or(|declaration| !declarations.contains(&declaration))
        || member.members().is_some()
        || member.exports().is_some()
        || member.export_symbol().is_some()
        || store
            .value_symbol_links(key)
            .and_then(|links| links.resolved_type)
            != Some(name_type)
        || resolved_table.and_then(|table| table.get(member.name())) != Some(symbol)
        || links
            != &(ValueSymbolLinks {
                resolved_type: links.resolved_type,
                name_type: Some(name_type),
                ..ValueSymbolLinks::default()
            })
    {
        return false;
    }
    if key_property {
        let Some(key_owner) = store.get_parent_of_symbol(key) else {
            return false;
        };
        let Some(key_owner_record) = store.symbol(key_owner) else {
            return false;
        };
        if !key_owner_record
            .flags()
            .intersects(SymbolFlags::INTERFACE | SymbolFlags::TYPE_LITERAL | SymbolFlags::CLASS)
            || !matches!(store.source_node_parent(key_declaration), Some(SourceNodeParent::Parent(parent)) if key_owner_record.declarations().is_some_and(|declarations| declarations.contains(&parent)))
            || store
                .source_child_with_kind(key_declaration, SyntaxKind::ReadonlyKeyword)
                .is_none()
            || key_owner_record.flags().contains(SymbolFlags::CLASS)
                && store
                    .source_child_with_kind(key_declaration, SyntaxKind::StaticKeyword)
                    .is_none()
            || key_record.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
            || ![key_owner_record.members(), key_owner_record.exports()]
                .into_iter()
                .flatten()
                .any(|table| {
                    store
                        .symbol_table(table)
                        .and_then(|table| table.get(key_record.name()))
                        .and_then(|symbol| store.get_merged_symbol(symbol))
                        == Some(key)
                })
        {
            return false;
        }
    } else if !key_record
        .flags()
        .contains(SymbolFlags::BLOCK_SCOPED_VARIABLE)
        || key_record.check_flags() != CheckFlags::NONE
        || store.get_parent_of_symbol(key) != store.get_parent_of_symbol(owner)
        || store.source_node_kind(key_declaration) != Some(SyntaxKind::VariableDeclaration)
    {
        return false;
    }
    if method && !store.late_bound_method_has_exact_sources(symbol, owner) {
        return false;
    }
    declarations.iter().all(|declaration| {
        if store
            .symbol_node_links(*declaration)
            .and_then(|links| links.resolved_symbol)
            != Some(symbol)
        {
            return false;
        }
        let Some(name) =
            store.source_child_with_kind(*declaration, SyntaxKind::ComputedPropertyName)
        else {
            return false;
        };
        let expression = match (
            store.source_child_with_kind(name, SyntaxKind::Identifier),
            store.source_child_with_kind(name, SyntaxKind::PropertyAccessExpression),
        ) {
            (Some(expression), None) | (None, Some(expression)) => expression,
            _ => return false,
        };
        if (method || key_property)
            && (store
                .symbol_node_links(expression)
                .and_then(|links| links.resolved_symbol)
                != Some(key)
                || store
                    .type_node_links(expression)
                    .and_then(|links| links.resolved_type)
                    != Some(name_type))
        {
            return false;
        }
        resolved_computed_member_key(
            store,
            &PlannedComputedMemberKey {
                expression,
                key_symbol: key,
                type_node: annotation,
            },
        )
        .is_ok_and(|resolved| resolved == Some((name_type, unique.name.clone())))
    })
}

fn valid_property_symbol(store: &CanonicalTypeMapperStore, property: SemanticSymbolId) -> bool {
    let Some(record) = store.symbol(property) else {
        return false;
    };
    let Some(declarations) = record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
    else {
        return false;
    };
    let method = record.flags().contains(SymbolFlags::METHOD);
    let accessor = record.flags().intersects(SymbolFlags::ACCESSOR);
    let late = record.name().is_late_bound()
        || record.check_flags().contains(CheckFlags::LATE)
        || record.flags().contains(SymbolFlags::TRANSIENT);
    let expected_flags = if method {
        SymbolFlags::METHOD
    } else if accessor {
        (record.flags() & SymbolFlags::ACCESSOR)
            | if record.flags().contains(SymbolFlags::PROPERTY) {
                SymbolFlags::PROPERTY
            } else {
                SymbolFlags::NONE
            }
    } else {
        SymbolFlags::PROPERTY
    } | if record.flags().contains(SymbolFlags::OPTIONAL) {
        SymbolFlags::OPTIONAL
    } else {
        SymbolFlags::NONE
    } | if late {
        SymbolFlags::TRANSIENT
    } else {
        SymbolFlags::NONE
    };
    if record.flags() != expected_flags
        || method && accessor
        || accessor
            && record.flags().contains(SymbolFlags::OPTIONAL)
            && !record.flags().contains(SymbolFlags::PROPERTY)
        || if late {
            let owner = store.get_parent_of_symbol(property);
            let links = store.value_symbol_links(property);
            let table = owner
                .and_then(|owner| store.members_and_exports_links(owner))
                .and_then(|links| links.table(MembersOrExportsResolutionKind::ResolvedMembers))
                .and_then(|table| store.symbol_table(table));
            accessor
                || !owner.zip(links).is_some_and(|(owner, links)| {
                    valid_late_bound_unique_symbol_member(
                        store,
                        owner,
                        property,
                        declarations,
                        links,
                        table,
                    )
                })
        } else if method || accessor {
            record.check_flags() != CheckFlags::NONE
        } else {
            record.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
        }
        || record
            .value_declaration()
            .is_none_or(|declaration| !declarations.contains(&declaration))
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent().is_none()
        || record.export_symbol().is_some()
        || store.get_merged_symbol(property) != Some(property)
    {
        return false;
    }

    if accessor {
        if !valid_accessor_declarations(store, record.flags(), declarations) {
            return false;
        }
    } else if !declarations.iter().all(|declaration| {
        if method {
            store.source_node_kind(*declaration) == Some(SyntaxKind::MethodSignature)
        } else {
            matches!(
                store.source_node_kind(*declaration),
                Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
            )
        }
    }) {
        return false;
    }

    store.value_symbol_links(property).is_some_and(|links| {
        let Some(read_type) = links.resolved_type else {
            return false;
        };
        let write_type = if accessor { links.write_type } else { None };
        links
            == &ValueSymbolLinks {
                resolved_type: Some(read_type),
                write_type,
                name_type: if late { links.name_type } else { None },
                ..ValueSymbolLinks::default()
            }
            && store.type_payload(read_type).is_some()
            && write_type.is_none_or(|write_type| {
                record.flags().contains(SymbolFlags::SET_ACCESSOR)
                    && write_type != read_type
                    && store.type_payload(write_type).is_some()
            })
            && (!method || valid_interface_method_value(store, property, read_type).is_some())
            && (method
                || accessor
                || late
                || valid_ordinary_property_source_contract(store, property, read_type))
    })
}

fn valid_ordinary_property_source_contract(
    store: &CanonicalTypeMapperStore,
    property: SemanticSymbolId,
    type_: TypeId,
) -> bool {
    let Some(record) = store.symbol(property) else {
        return false;
    };
    let Some(declarations) = record.declarations() else {
        return false;
    };
    let Some(declaration) = record.value_declaration() else {
        return false;
    };
    let optional = record.flags().contains(SymbolFlags::OPTIONAL);
    let readonly = record.check_flags().contains(CheckFlags::READONLY);
    let annotation_matches = match store.source_direct_type_annotation(declaration) {
        Some(annotation) => ordinary_property_annotation_is_exact(store, annotation, type_),
        None => {
            store
                .intrinsic_bootstrap()
                .is_some_and(|bootstrap| type_ == bootstrap.any_type)
                && store.source_direct_children(declaration).is_some_and(|children| {
                    if children.len() != 1 + usize::from(optional) + usize::from(readonly) {
                        return false;
                    }
                    // The source flag checks below authenticate these modifier tokens.
                    let mut meaningful = children.into_iter().filter(|child| {
                        !matches!(
                            store.source_node_kind(*child),
                            Some(SyntaxKind::QuestionToken | SyntaxKind::ReadonlyKeyword)
                        )
                    });
                    matches!(
                        (meaningful.next(), meaningful.next()),
                        (Some(name), None) if store.source_identifier_text(name).is_some_and(|text| record.name().as_utf8() == Some(text))
                    )
                })
        }
    };
    declarations.iter().all(|declaration| {
        store
            .source_child_with_kind(*declaration, SyntaxKind::QuestionToken)
            .is_some()
            == optional
            && store
                .source_child_with_kind(*declaration, SyntaxKind::ReadonlyKeyword)
                .is_some()
                == readonly
    }) && annotation_matches
        && store
            .declared_value_provenance(property)
            .is_none_or(|provenance| {
                provenance.readonly == Some(readonly) && provenance.is_current(store, property)
            })
}

fn ordinary_property_annotation_is_exact(
    store: &CanonicalTypeMapperStore,
    mut annotation: NodeRef,
    type_: TypeId,
) -> bool {
    while store.source_node_kind(annotation) == Some(SyntaxKind::ParenthesizedType) {
        if store.type_node_links(annotation).is_some_and(|links| {
            links.outer_type_parameters.is_some()
                || links.resolved_type.is_some_and(|cached| cached != type_)
        }) || store
            .symbol_node_links(annotation)
            .is_some_and(|links| links.resolved_symbol.is_some())
        {
            return false;
        }
        let Some(children) = store.source_direct_children(annotation) else {
            return false;
        };
        let [inner] = children.as_slice() else {
            return false;
        };
        annotation = *inner;
    }
    store.source_direct_type_annotation_is_exact(annotation, type_)
}

pub(super) fn valid_interface_method_value(
    store: &CanonicalTypeMapperStore,
    method: SemanticSymbolId,
    type_: TypeId,
) -> Option<SignatureId> {
    valid_interface_method_signatures(store, method, type_)
        .and_then(|signatures| signatures.first().copied())
}

fn valid_interface_method_signatures(
    store: &CanonicalTypeMapperStore,
    method: SemanticSymbolId,
    type_: TypeId,
) -> Option<&[SignatureId]> {
    let method_record = store.symbol(method)?;
    let declarations = method_record.declarations()?;
    let owner = method_record.parent()?;
    let owner_record = store.symbol(owner)?;
    let owner_declarations = owner_record.declarations()?;
    let bootstrap = store.intrinsic_bootstrap()?;
    let optional = store.declared_method_optional_flag(method)?;
    if store.value_symbol_links(method)?.resolved_type != Some(type_) {
        return None;
    }
    let callable_type = if optional && bootstrap.options.strict_null_checks {
        let TypeData::Union(union) = store.type_payload(type_)?.data() else {
            return None;
        };
        let sentinel = bootstrap.undefined_or_missing_type;
        let [first, second] = union.union.types.as_slice() else {
            return None;
        };
        let callable = match (*first == sentinel, *second == sentinel) {
            (true, false) => *second,
            (false, true) => *first,
            _ => return None,
        };
        let mut expected = [callable, sentinel];
        expected.sort_unstable();
        store
            .validate_canonical_union_metadata(type_, &expected)
            .ok()?;
        store.validate_union_constituent(sentinel).ok()?;
        callable
    } else {
        type_
    };
    let record = store.type_payload(callable_type)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    let signatures = object.structured.signatures.as_deref()?;
    let merged_namespace_interface = owner_record.flags().contains(SymbolFlags::NAMESPACE_MODULE)
        && store
            .authenticated_interface_method_owner(method)
            .is_some_and(|(authenticated_owner, _)| authenticated_owner == owner);
    if owner_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        && !merged_namespace_interface
        || declarations.is_empty()
        || declarations.len() != signatures.len()
        || record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.symbol() != Some(method)
        || record.alias().is_some()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.members.is_some()
        || object.structured.properties.is_some()
        || object.structured.call_signature_count != signatures.len()
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return None;
    }

    let mut seen_signatures = HashSet::with_capacity(signatures.len());
    for (declaration, signature) in declarations.iter().copied().zip(signatures.iter().copied()) {
        let Some(SourceNodeParent::Parent(owner_declaration)) =
            store.source_node_parent(declaration)
        else {
            return None;
        };
        let callable = store.signature(signature)?;
        let return_type = callable.resolved_return_type()?;
        let annotation = store.source_direct_type_annotation(declaration)?;
        let cached_parameter_types = store.callable_signature_parameter_types(signature);
        if !seen_signatures.insert(signature)
            || !owner_declarations.contains(&owner_declaration)
            || store.source_node_kind(owner_declaration) != Some(SyntaxKind::InterfaceDeclaration)
            || store.source_node_kind(declaration) != Some(SyntaxKind::MethodSignature)
            || callable.flags().bits()
                & !(SignatureFlags::HAS_REST_PARAMETER | SignatureFlags::HAS_LITERAL_TYPES).bits()
                != 0
            || callable.declaration() != Some(declaration)
            || !super::callable_sets::valid_declared_method_type_parameters(
                store,
                callable,
                declaration,
            )
            || callable.this_parameter().is_some()
            || callable.resolved_min_argument_count() != -1
            || callable.resolved_type_predicate().is_some()
            || callable.target().is_some()
            || callable.mapper().is_some()
            || callable.isolated_signature_type().is_some()
            || callable.composite().is_some()
            || store.signature_has_circular_return_type(signature)
            || cached_parameter_types
                .is_some_and(|parameters| parameters.len() != callable.parameters().len())
            || !store.source_direct_type_annotation_is_exact(annotation, return_type)
            || store.signature_links(declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                })
        {
            return None;
        }

        let mut seen_parameters = HashSet::with_capacity(callable.parameters().len());
        let mut required_parameters = 0usize;
        for (index, parameter) in callable.parameters().iter().copied().enumerate() {
            let record = store.symbol(parameter)?;
            let [parameter_declaration] = record.declarations()? else {
                return None;
            };
            let links = store.value_symbol_links(parameter)?;
            let parameter_type = links.resolved_type?;
            let annotation = store.source_direct_type_annotation(*parameter_declaration)?;
            let annotation_type = super::object_members::cached_planned_type_identity(
                store, annotation,
            )
            .or_else(|| {
                store
                    .source_direct_type_annotation_is_exact(annotation, bootstrap.null_type)
                    .then_some(bootstrap.null_type)
            })?;
            let optional = store
                .source_child_with_kind(*parameter_declaration, SyntaxKind::QuestionToken)
                .is_some();
            let rest = callable.has_rest_parameter() && index + 1 == callable.parameters().len();
            if !seen_parameters.insert(parameter)
                || record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                || record.check_flags() != CheckFlags::NONE
                || record.value_declaration() != Some(*parameter_declaration)
                || record.members().is_some()
                || record.exports().is_some()
                || record.parent().is_some()
                || record.export_symbol().is_some()
                || store.get_merged_symbol(parameter) != Some(parameter)
                || store.source_node_kind(*parameter_declaration) != Some(SyntaxKind::Parameter)
                || store.source_node_parent(*parameter_declaration)
                    != Some(SourceNodeParent::Parent(declaration))
                || store.type_payload(parameter_type).is_none()
                || links
                    != &(ValueSymbolLinks {
                        resolved_type: Some(parameter_type),
                        ..ValueSymbolLinks::default()
                    })
                || cached_parameter_types
                    .is_some_and(|parameters| parameters[index] != parameter_type)
                || !store.source_direct_type_annotation_is_exact(annotation, annotation_type)
                || if optional && bootstrap.options.strict_null_checks {
                    store
                        .validate_optional_parameter_type_metadata(annotation_type, parameter_type)
                        .is_err()
                } else {
                    annotation_type != parameter_type
                }
                || rest && optional
            {
                return None;
            }
            if !optional && !rest {
                required_parameters = required_parameters.checked_add(1)?;
            }
        }
        if usize::try_from(callable.min_argument_count()).ok() != Some(required_parameters) {
            return None;
        }
    }
    Some(signatures)
}

fn matching_interface_method_contract(
    store: &CanonicalTypeMapperStore,
    first: SemanticSymbolId,
    second: SemanticSymbolId,
) -> bool {
    let Some(first_type) = store
        .value_symbol_links(first)
        .and_then(|links| links.resolved_type)
    else {
        return false;
    };
    let Some(second_type) = store
        .value_symbol_links(second)
        .and_then(|links| links.resolved_type)
    else {
        return false;
    };
    let Some(first_signatures) = valid_interface_method_signatures(store, first, first_type) else {
        return false;
    };
    let Some(second_signatures) = valid_interface_method_signatures(store, second, second_type)
    else {
        return false;
    };
    first_signatures.len() == second_signatures.len()
        && first_signatures.iter().zip(second_signatures).all(
            |(first_signature, second_signature)| {
                let Some(first_record) = store.signature(*first_signature) else {
                    return false;
                };
                let Some(second_record) = store.signature(*second_signature) else {
                    return false;
                };
                first_record.flags() == second_record.flags()
                    && first_record.min_argument_count() == second_record.min_argument_count()
                    && first_record.type_parameters().len() == second_record.type_parameters().len()
                    && match (
                        first_record.resolved_return_type(),
                        second_record.resolved_return_type(),
                    ) {
                        (Some(first), Some(second)) => matching_generic_method_type(
                            store,
                            first,
                            second,
                            first_record.type_parameters(),
                            second_record.type_parameters(),
                            &mut HashSet::new(),
                        ),
                        (None, None) => true,
                        _ => false,
                    }
                    && first_record.parameters().len() == second_record.parameters().len()
                    && first_record
                        .parameters()
                        .iter()
                        .zip(second_record.parameters())
                        .all(|(first, second)| {
                            match (
                                store
                                    .value_symbol_links(*first)
                                    .and_then(|links| links.resolved_type),
                                store
                                    .value_symbol_links(*second)
                                    .and_then(|links| links.resolved_type),
                            ) {
                                (Some(first), Some(second)) => matching_generic_method_type(
                                    store,
                                    first,
                                    second,
                                    first_record.type_parameters(),
                                    second_record.type_parameters(),
                                    &mut HashSet::new(),
                                ),
                                _ => false,
                            }
                        })
            },
        )
}

fn matching_generic_method_type(
    store: &CanonicalTypeMapperStore,
    first: TypeId,
    second: TypeId,
    first_parameters: &[TypeId],
    second_parameters: &[TypeId],
    active: &mut HashSet<(TypeId, TypeId)>,
) -> bool {
    if first == second {
        return true;
    }
    if let Some(index) = first_parameters
        .iter()
        .position(|parameter| *parameter == first)
    {
        return second_parameters.get(index).copied() == Some(second);
    }
    if !active.insert((first, second)) {
        return true;
    }
    let matches = match (
        store
            .type_payload(first)
            .map(super::type_records::TypeRecord::data),
        store
            .type_payload(second)
            .map(super::type_records::TypeRecord::data),
    ) {
        (Some(TypeData::Union(first)), Some(TypeData::Union(second))) => {
            first.union.types.len() == second.union.types.len()
                && first.union.types.iter().all(|first| {
                    second.union.types.iter().any(|second| {
                        matching_generic_method_type(
                            store,
                            *first,
                            *second,
                            first_parameters,
                            second_parameters,
                            active,
                        )
                    })
                })
        }
        (
            Some(TypeData::TypeReference(_) | TypeData::Interface(_)),
            Some(TypeData::TypeReference(_) | TypeData::Interface(_)),
        ) => match (
            super::reference_types::validate_direct_generic_reference(store, first),
            super::reference_types::validate_direct_generic_reference(store, second),
        ) {
            (Ok(first), Ok(second)) => {
                first.target == second.target
                    && first.type_arguments.len() == second.type_arguments.len()
                    && first.type_arguments.iter().zip(second.type_arguments).all(
                        |(first, second)| {
                            matching_generic_method_type(
                                store,
                                *first,
                                second,
                                first_parameters,
                                second_parameters,
                                active,
                            )
                        },
                    )
            }
            _ => false,
        },
        _ => false,
    };
    active.remove(&(first, second));
    matches
}

fn exact_property_table(
    store: &CanonicalTypeMapperStore,
    properties: &[SemanticSymbolId],
    members: Option<SymbolTableId>,
    index_symbol: Option<SemanticSymbolId>,
    call_symbol: Option<SemanticSymbolId>,
) -> bool {
    if properties.is_empty() && index_symbol.is_none() && call_symbol.is_none() {
        return members.is_none();
    }
    let Some(table) = members.and_then(|members| store.symbol_table(members)) else {
        return false;
    };
    table.len()
        == properties
            .len()
            .saturating_add(usize::from(index_symbol.is_some()))
            .saturating_add(usize::from(call_symbol.is_some()))
        && properties.iter().all(|property| {
            store
                .symbol(*property)
                .is_some_and(|record| table.get(record.name()) == Some(*property))
        })
        && table.get(InternalSymbolName::Index.as_ref()) == index_symbol
        && table.get(InternalSymbolName::Call.as_ref()) == call_symbol
        && table.iter().all(|(_, property)| {
            properties.contains(&property)
                || index_symbol == Some(property)
                || call_symbol == Some(property)
        })
}

fn exact_member_table(
    store: &CanonicalTypeMapperStore,
    entries: &[(EscapedName, SemanticSymbolId)],
    members: Option<SymbolTableId>,
) -> bool {
    if entries.is_empty() {
        return members.is_none();
    }
    let Some(table) = members.and_then(|members| store.symbol_table(members)) else {
        return false;
    };
    table.len() == entries.len()
        && entries
            .iter()
            .all(|(name, property)| table.get(name.as_ref()) == Some(*property))
        && table.iter().all(|(name, property)| {
            entries.iter().any(|(expected_name, expected)| {
                expected_name.as_ref() == name && *expected == property
            })
        })
}

fn valid_thisless_interface_identity(interface: &InterfaceTypeData) -> bool {
    interface.all_type_parameters.is_none()
        && interface.outer_type_parameter_count == 0
        && interface.this_type.is_none()
        && interface.reference.object.target.is_none()
        && interface.reference.object.mapper.is_none()
        && interface.reference.object.instantiations == TypeCacheState::Unallocated
        && interface.reference.node.is_none()
        && interface.reference.resolved_type_arguments.is_none()
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, NodeArena, NodeData, NodeRef};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName, SymbolData,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        DeclaredTypeHost,
        bootstrap::IntrinsicBootstrapOptions,
        declared::get_declared_class_interface_or_type_parameter,
        interface_heritage::plan_direct_interface_heritage,
        object_members::{self, PlannedProperty, PropertyObjectState},
        production::GlobalMergeCompletion,
        relater::RelationUnavailable,
        relation::{IntersectionState, RelationComparisonResult, RelationKind},
    };

    include!("../../../../tests/reviews/index_warm_source_final_invariants.rs");

    const SOURCE: &str = concat!(
        "interface Base { first: number; second: number }\n",
        "interface Other { other: number }\n",
        "interface Derived extends Base { own: number }\n",
    );

    const INDEXED_SOURCE: &str = concat!(
        "interface Base { [key: string]: number; first: number; second: number }\n",
        "interface Other { other: number }\n",
        "interface Derived extends Base { own: number }\n",
    );

    const CALLABLE_SOURCE: &str = concat!(
        "interface Base { (): string }\n",
        "interface Derived extends Base { (key: string): string }\n",
    );

    const METHOD_SOURCE: &str = concat!(
        "interface Base { method(): void }\n",
        "interface Derived { method(): void }\n",
    );

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        files: BTreeMap<FileId, BoundFile>,
        store: CanonicalTypeMapperStore,
    }

    struct PreparedFixture {
        fixture: Fixture,
        derived_plan: PropertyObjectPlan,
        base_type: TypeId,
        other_type: TypeId,
        derived_type: TypeId,
        number_type: TypeId,
    }

    struct PreparedCallableFixture {
        fixture: Fixture,
        derived_plan: PropertyObjectPlan,
        base_type: TypeId,
        derived_type: TypeId,
        string_type: TypeId,
    }

    fn fixture() -> Fixture {
        fixture_with_source(SOURCE, 801)
    }

    fn fixture_with_source(source: &str, file: u32) -> Fixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(file);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/structured-members.ts\""),
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
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let bound = files.get(&file).unwrap();
        let locals = bound.locals(bound.source_file()).unwrap();
        let mut symbols = store
            .symbol_table(locals)
            .unwrap()
            .iter()
            .map(|(name, symbol)| (name.as_bytes().to_vec(), symbol))
            .collect::<Vec<_>>();
        symbols.sort_unstable_by(|left, right| left.0.cmp(&right.0));
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        for (_, symbol) in symbols {
            store.merge_global_symbol(globals, symbol).unwrap();
        }
        Fixture {
            parsed,
            file,
            files,
            store,
        }
    }

    fn host<'a>(arena: &'a NodeArena, bound: &'a BoundFile) -> DeclaredTypeHost<'a> {
        DeclaredTypeHost::new_after_global_merge(
            [(arena, bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap()
    }

    fn interface_symbol(fixture: &Fixture, expected: &str) -> SemanticSymbolId {
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::InterfaceDeclaration(interface) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &fixture.parsed.arena.get(interface.name)?.data
                else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap_or_else(|| panic!("missing interface {expected}"));
        let raw = fixture
            .files
            .get(&fixture.file)
            .unwrap()
            .symbol(declaration)
            .unwrap();
        fixture.store.get_merged_symbol(raw).unwrap()
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep cold proof, paired cache changes, and retries together.
    fn review_index_source_proof_rejects_matching_warm_type_parameter_caches() {
        use crate::semantic::TypeNodeLinks;

        let mut accepted = Vec::new();
        for annotation_text in ["T", "(T)", "((T))"] {
            let mut fixture = fixture_with_source(
                &format!("interface Base<T> {{ [index: number]: {annotation_text}; }}"),
                14_501,
            );
            let owner = interface_symbol(&fixture, "Base");
            let source_host = host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let flags = fixture.store.symbol(owner).unwrap().flags();
            let target = get_declared_class_interface_or_type_parameter(
                &mut fixture.store,
                &source_host,
                owner,
                flags,
            )
            .unwrap()
            .unwrap();
            let TypeData::Interface(interface) = fixture.store.type_payload(target).unwrap().data()
            else {
                panic!("Base retains its real generic interface target")
            };
            let parameter = interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0];
            assert!(cached_ordinary_type_parameter_owner(&fixture.store, parameter).is_some());
            let owner_record = fixture.store.symbol(owner).unwrap();
            let declarations = owner_record.declarations().unwrap().to_vec();
            let symbol = owner_record
                .members()
                .and_then(|members| fixture.store.symbol_table(members))
                .and_then(|members| members.get(InternalSymbolName::Index.as_ref()))
                .unwrap();
            let declaration = fixture
                .store
                .symbol(symbol)
                .unwrap()
                .declarations()
                .unwrap()[0];
            let NodeData::IndexSignatureDeclaration(index_source) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("the index retains its registered source declaration")
            };
            let mut annotation =
                NodeRef::new(declaration.arena, declaration.file, index_source.type_);
            let mut annotations = Vec::new();
            loop {
                annotations.push(annotation);
                if fixture.store.source_node_kind(annotation) != Some(SyntaxKind::ParenthesizedType)
                {
                    break;
                }
                let children = fixture.store.source_direct_children(annotation).unwrap();
                assert_eq!(children.len(), 1);
                annotation = children[0];
            }
            assert_eq!(
                fixture.store.source_node_kind(annotation),
                Some(SyntaxKind::TypeReference)
            );
            let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
            let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
            let original = fixture
                .store
                .alloc_index_info(number, parameter, false, Some(declaration), Vec::new())
                .unwrap();
            let state = |store: &CanonicalTypeMapperStore| {
                (
                    store.type_len(),
                    store.mapper_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.index_info_len(),
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                    annotations
                        .iter()
                        .map(|node| store.type_node_links(*node).cloned())
                        .collect::<Vec<_>>(),
                )
            };
            let validate = |store: &CanonicalTypeMapperStore, index| {
                valid_index_symbol(store, owner, &declarations, symbol, &[index])
            };
            let before = state(&fixture.store);
            assert!(validate(&fixture.store, original), "cold {annotation_text}");
            assert_eq!(state(&fixture.store), before);
            for node in &annotations {
                assert!(fixture.store.set_type_node_links(
                    *node,
                    TypeNodeLinks {
                        resolved_type: Some(parameter),
                        ..TypeNodeLinks::default()
                    }
                ));
            }
            let warm = state(&fixture.store);
            assert!(validate(&fixture.store, original), "warm {annotation_text}");
            assert_eq!(state(&fixture.store), warm);
            let wrong = fixture
                .store
                .alloc_index_info(number, string, false, Some(declaration), Vec::new())
                .unwrap();
            let before = state(&fixture.store);
            assert!(
                !validate(&fixture.store, wrong),
                "index-only {annotation_text}"
            );
            assert_eq!(state(&fixture.store), before);
            for node in &annotations {
                assert!(fixture.store.set_type_node_links(
                    *node,
                    TypeNodeLinks {
                        resolved_type: Some(string),
                        ..TypeNodeLinks::default()
                    }
                ));
            }
            let poisoned = state(&fixture.store);
            assert!(
                !validate(&fixture.store, original),
                "annotation-only {annotation_text}"
            );
            assert_eq!(state(&fixture.store), poisoned);
            for _ in 0..2 {
                accepted.push((annotation_text, validate(&fixture.store, wrong)));
                assert_eq!(state(&fixture.store), poisoned);
            }
            for node in &annotations {
                assert!(fixture.store.set_type_node_links(
                    *node,
                    TypeNodeLinks {
                        resolved_type: Some(parameter),
                        ..TypeNodeLinks::default()
                    }
                ));
            }
            let restored = state(&fixture.store);
            assert!(
                validate(&fixture.store, original),
                "restored {annotation_text}"
            );
            assert_eq!(state(&fixture.store), restored);
        }
        assert!(
            accepted.iter().all(|(_, accepted)| !accepted),
            "matching mutable caches replaced the source type parameter: {accepted:?}"
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep source, cache changes, and retries in one fixture.
    fn index_source_proof_preserves_parenthesized_annotations() {
        use crate::semantic::TypeNodeLinks;

        for annotation_text in ["number", "(number)", "((number))"] {
            for readonly in [false, true] {
                let modifier = if readonly { "readonly " } else { "" };
                let mut fixture = fixture_with_source(
                    &format!("interface Base {{ {modifier}[index: number]: {annotation_text}; }}"),
                    8_149,
                );
                let owner = interface_symbol(&fixture, "Base");
                let owner_record = fixture.store.symbol(owner).unwrap();
                let declarations = owner_record.declarations().unwrap().to_vec();
                let symbol = owner_record
                    .members()
                    .and_then(|members| fixture.store.symbol_table(members))
                    .and_then(|members| members.get(InternalSymbolName::Index.as_ref()))
                    .unwrap();
                let declaration = fixture
                    .store
                    .symbol(symbol)
                    .unwrap()
                    .declarations()
                    .unwrap()[0];
                let NodeData::IndexSignatureDeclaration(index_source) =
                    &fixture.parsed.arena.get(declaration.node).unwrap().data
                else {
                    panic!("the index retains its source declaration")
                };
                let mut annotation =
                    NodeRef::new(declaration.arena, declaration.file, index_source.type_);
                let mut annotations = Vec::new();
                loop {
                    annotations.push(annotation);
                    let NodeData::ParenthesizedTypeNode(parenthesized) =
                        &fixture.parsed.arena.get(annotation.node).unwrap().data
                    else {
                        break;
                    };
                    annotation =
                        NodeRef::new(annotation.arena, annotation.file, parenthesized.type_);
                }
                assert_eq!(
                    fixture.store.source_node_kind(annotation),
                    Some(SyntaxKind::NumberKeyword)
                );
                let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
                let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
                let original = fixture
                    .store
                    .alloc_index_info(number, number, readonly, Some(declaration), Vec::new())
                    .unwrap();
                let state = |store: &CanonicalTypeMapperStore| {
                    (
                        store.type_len(),
                        store.mapper_len(),
                        store.symbol_len(),
                        store.signature_len(),
                        store.index_info_len(),
                        store.checker_link_allocated_lengths(),
                        store.relation_state_snapshot(),
                        annotations
                            .iter()
                            .map(|node| store.type_node_links(*node).cloned())
                            .collect::<Vec<_>>(),
                    )
                };
                let before = state(&fixture.store);
                assert!(valid_index_symbol(
                    &fixture.store,
                    owner,
                    &declarations,
                    symbol,
                    &[original]
                ));
                assert_eq!(state(&fixture.store), before);

                for (value, changed_readonly, change_nodes) in [
                    (number, !readonly, false),
                    (string, readonly, false),
                    (string, readonly, true),
                ] {
                    let changed = fixture
                        .store
                        .alloc_index_info(
                            number,
                            value,
                            changed_readonly,
                            Some(declaration),
                            Vec::new(),
                        )
                        .unwrap();
                    if change_nodes {
                        for node in &annotations {
                            assert!(fixture.store.set_type_node_links(
                                *node,
                                TypeNodeLinks {
                                    resolved_type: Some(value),
                                    ..TypeNodeLinks::default()
                                }
                            ));
                        }
                    }
                    let before = state(&fixture.store);
                    for _ in 0..2 {
                        assert!(
                            !valid_index_symbol(
                                &fixture.store,
                                owner,
                                &declarations,
                                symbol,
                                &[changed]
                            ),
                            "{annotation_text}, readonly={readonly}, change_nodes={change_nodes}"
                        );
                        assert_eq!(state(&fixture.store), before);
                    }
                    if change_nodes {
                        for node in &annotations {
                            assert!(
                                fixture
                                    .store
                                    .set_type_node_links(*node, TypeNodeLinks::default())
                            );
                        }
                    }
                    let restored = state(&fixture.store);
                    assert!(valid_index_symbol(
                        &fixture.store,
                        owner,
                        &declarations,
                        symbol,
                        &[original]
                    ));
                    assert_eq!(state(&fixture.store), restored);
                }
            }
        }
    }

    #[test]
    fn index_source_proof_validates_warm_reference_symbols() {
        use crate::semantic::links::{SymbolNodeLinks, TypeNodeLinks};

        let mut fixture = fixture_with_source(
            "interface Base<T, U> { readonly [index: number]: T; }",
            14_601,
        );
        let owner = interface_symbol(&fixture, "Base");
        let source_host = host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let flags = fixture.store.symbol(owner).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &source_host,
            owner,
            flags,
        )
        .unwrap()
        .unwrap();
        let TypeData::Interface(interface) = fixture.store.type_payload(target).unwrap().data()
        else {
            panic!("Base retains its source type parameters")
        };
        let parameters = interface.reference.resolved_type_arguments.clone().unwrap();
        let parameter = parameters[0];
        let other = parameters[1];
        let symbol = cached_ordinary_type_parameter_owner(&fixture.store, parameter).unwrap();
        let other_symbol = cached_ordinary_type_parameter_owner(&fixture.store, other).unwrap();
        let annotation = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeReference).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let Some(SourceNodeParent::Parent(declaration)) =
            fixture.store.source_node_parent(annotation)
        else {
            panic!("the reference belongs to the source index")
        };
        assert!(source_index_annotation_is_exact(
            &fixture.store,
            owner,
            declaration,
            annotation,
            parameter
        ));
        let state = |store: &CanonicalTypeMapperStore| {
            (
                store.checker_link_allocated_lengths(),
                store.type_node_links(annotation).cloned(),
                store.symbol_node_links(annotation).cloned(),
                store.relation_state_snapshot(),
            )
        };
        for (type_, resolved_symbol, expected) in [
            (parameter, None, true),
            (parameter, Some(other_symbol), false),
            (other, Some(other_symbol), false),
            (parameter, Some(symbol), true),
        ] {
            assert!(fixture.store.set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(type_),
                    outer_type_parameters: None,
                }
            ));
            assert!(
                fixture
                    .store
                    .set_symbol_node_links(annotation, SymbolNodeLinks { resolved_symbol })
            );
            let before = state(&fixture.store);
            for _ in 0..2 {
                assert_eq!(
                    source_index_annotation_is_exact(
                        &fixture.store,
                        owner,
                        declaration,
                        annotation,
                        type_
                    ),
                    expected
                );
                assert_eq!(state(&fixture.store), before);
            }
        }
    }

    #[test]
    fn index_source_proof_preserves_warm_named_reference_values() {
        use crate::semantic::TypeNodeLinks;

        let mut fixture = fixture_with_source(
            "interface Result { value: number; } interface Base<T> { [index: number]: Result; }",
            14_602,
        );
        let owner = interface_symbol(&fixture, "Base");
        let result = interface_symbol(&fixture, "Result");
        let source_host = host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let flags = fixture.store.symbol(result).unwrap().flags();
        let result_type = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &source_host,
            result,
            flags,
        )
        .unwrap()
        .unwrap();
        let annotation = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeReference).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let Some(SourceNodeParent::Parent(declaration)) =
            fixture.store.source_node_parent(annotation)
        else {
            panic!("the named reference belongs to the source index")
        };
        assert!(fixture.store.set_type_node_links(
            annotation,
            TypeNodeLinks {
                resolved_type: Some(result_type),
                outer_type_parameters: None,
            }
        ));
        let before = fixture.store.checker_link_allocated_lengths();
        for _ in 0..2 {
            assert!(source_index_annotation_is_exact(
                &fixture.store,
                owner,
                declaration,
                annotation,
                result_type
            ));
            assert_eq!(fixture.store.checker_link_allocated_lengths(), before);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the real cross-file merge and cache checks together.
    fn index_source_proof_preserves_merged_parameter_bindings() {
        use crate::semantic::links::{SymbolNodeLinks, TypeNodeLinks};

        for annotation_text in ["T", "(T)", "((T))"] {
            let first = parse_source_file("interface Base<T> {}");
            let second = parse_source_file(&format!(
                "interface Base<T> {{ readonly [index: number]: {annotation_text}; }}"
            ));
            let sources = [
                (FileId::new(14_716), &first),
                (FileId::new(14_717), &second),
            ];
            let mut binder = CanonicalBinder::new();
            for &(file, parsed) in &sources {
                assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                binder
                    .bind_source_file_with_facts(
                        &parsed.arena,
                        parsed.source_file,
                        file,
                        CanonicalSourceFileFacts::new(
                            EscapedName::source(format!("\"/merged-index-{}.ts\"", file.index())),
                            CanonicalSourceLanguage::TypeScript,
                            false,
                            CanonicalModuleState::Script,
                        ),
                    )
                    .unwrap();
                binder
                    .bind_typescript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            }
            let (symbols, files) = binder.finish().try_into_parts().unwrap();
            let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
            store
                .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
                .unwrap();
            let globals = store.intrinsic_bootstrap().unwrap().globals;
            let mut raw_parameters = Vec::new();
            for &(file, parsed) in &sources {
                assert!(
                    store
                        .register_source_file(&parsed.arena, parsed.source_file, file)
                        .is_some()
                );
                let bound = files.get(&file).unwrap();
                let owner = store
                    .symbol_table(bound.locals(bound.source_file()).unwrap())
                    .unwrap()
                    .get_source("Base")
                    .unwrap();
                store.merge_global_symbol(globals, owner).unwrap();
                let parameter = bound
                    .traversal_order()
                    .find(|node| store.source_node_kind(*node) == Some(SyntaxKind::TypeParameter))
                    .unwrap();
                let raw = bound.symbol(parameter).unwrap();
                assert_eq!(
                    store.symbol_store().source_binding_symbols(parameter),
                    Some([Some(raw), None])
                );
                raw_parameters.push(raw);
            }
            assert_ne!(raw_parameters[0], raw_parameters[1]);
            let parameter_symbol = store.get_merged_symbol(raw_parameters[0]).unwrap();
            assert_ne!(parameter_symbol, raw_parameters[0]);
            assert_ne!(parameter_symbol, raw_parameters[1]);
            assert_eq!(
                store.get_merged_symbol(raw_parameters[1]),
                Some(parameter_symbol)
            );
            let source_host = DeclaredTypeHost::new_after_global_merge(
                sources
                    .iter()
                    .map(|(file, parsed)| (&parsed.arena, files.get(file).unwrap())),
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let owner = store
                .symbol_table(globals)
                .unwrap()
                .get_source("Base")
                .unwrap();
            let flags = store.symbol(owner).unwrap().flags();
            let target = get_declared_class_interface_or_type_parameter(
                &mut store,
                &source_host,
                owner,
                flags,
            )
            .unwrap()
            .unwrap();
            let TypeData::Interface(interface) = store.type_payload(target).unwrap().data() else {
                panic!("Base retains its merged generic interface")
            };
            let parameters = interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap();
            assert_eq!(parameters.len(), 1);
            let parameter = parameters[0];
            assert_eq!(
                cached_ordinary_type_parameter_owner(&store, parameter),
                Some(parameter_symbol)
            );
            let record = store.symbol(owner).unwrap();
            let declarations = record.declarations().unwrap().to_vec();
            assert_eq!(declarations.len(), 2);
            let symbol = store
                .symbol_table(record.members().unwrap())
                .unwrap()
                .get(InternalSymbolName::Index.as_ref())
                .unwrap();
            let declaration = store.symbol(symbol).unwrap().declarations().unwrap()[0];
            let NodeData::IndexSignatureDeclaration(index_source) =
                &second.arena.get(declaration.node).unwrap().data
            else {
                panic!("the second file retains the index declaration")
            };
            let mut annotation =
                NodeRef::new(declaration.arena, declaration.file, index_source.type_);
            let mut annotations = vec![annotation];
            while store.source_node_kind(annotation) == Some(SyntaxKind::ParenthesizedType) {
                let children = store.source_direct_children(annotation).unwrap();
                let [inner] = children.as_slice() else {
                    panic!("a parenthesized type has one annotation")
                };
                annotation = *inner;
                annotations.push(annotation);
            }
            let number = store.intrinsic_bootstrap().unwrap().number_type;
            let index = store
                .alloc_index_info(number, parameter, true, Some(declaration), Vec::new())
                .unwrap();
            for (warm, resolved_symbol) in [
                (false, None),
                (true, None),
                (true, Some(raw_parameters[0])),
                (true, Some(raw_parameters[1])),
                (true, Some(parameter_symbol)),
            ] {
                if warm {
                    for node in &annotations {
                        assert!(store.set_type_node_links(
                            *node,
                            TypeNodeLinks {
                                resolved_type: Some(parameter),
                                outer_type_parameters: None,
                            }
                        ));
                    }
                    assert!(
                        store
                            .set_symbol_node_links(annotation, SymbolNodeLinks { resolved_symbol })
                    );
                } else {
                    assert!(
                        annotations
                            .iter()
                            .all(|node| store.type_node_links(*node).is_none())
                    );
                    assert!(store.symbol_node_links(annotation).is_none());
                }
                let state = |store: &CanonicalTypeMapperStore| {
                    (
                        store.type_len(),
                        store.mapper_len(),
                        store.symbol_len(),
                        store.index_info_len(),
                        store.checker_link_allocated_lengths(),
                        store.relation_state_snapshot(),
                        annotations
                            .iter()
                            .map(|node| store.type_node_links(*node).cloned())
                            .collect::<Vec<_>>(),
                        store.symbol_node_links(annotation).cloned(),
                    )
                };
                let before = state(&store);
                for _ in 0..2 {
                    assert!(
                        valid_index_symbol(&store, owner, &declarations, symbol, &[index]),
                        "{annotation_text}, warm={warm}, symbol={resolved_symbol:?}"
                    );
                    assert_eq!(state(&store), before);
                }
            }
        }
    }

    #[test]
    fn concrete_base_arguments_are_checked_before_publication() {
        let mut fixture = fixture_with_source(
            "interface Base<T> { value: T } interface Derived extends Base<number> {}",
            861,
        );
        let base = interface_symbol(&fixture, "Base");
        let derived = interface_symbol(&fixture, "Derived");
        let host = host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let base_type = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            base,
            SymbolFlags::INTERFACE,
        )
        .unwrap()
        .unwrap();
        let derived_type = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            derived,
            SymbolFlags::INTERFACE,
        )
        .unwrap()
        .unwrap();
        let plan = object_members::plan_interface(&fixture.store, &host, derived).unwrap();
        let base_plan =
            object_members::plan_generic_interface(&fixture.store, &host, base).unwrap();
        let parameter = validate_direct_generic_reference(&fixture.store, base_type)
            .unwrap()
            .type_arguments[0];
        assert!(
            fixture
                .store
                .publish_interface_no_base_resolution(base_type)
        );
        object_members::publish_generic_interface_declared_members(
            &mut fixture.store,
            &base_plan,
            base_type,
            &[parameter],
        )
        .unwrap();
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let wrong = fixture
            .store
            .create_direct_generic_reference_type(base_type, &[string])
            .unwrap();
        fixture
            .store
            .resolve_generic_interface_members(wrong, None)
            .unwrap();
        let before = (
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert!(
            resolve_direct_interface_members(
                &mut fixture.store,
                &plan,
                derived_type,
                &[],
                &[wrong]
            )
            .is_err()
        );
        assert!(
            fixture
                .store
                .direct_interface_heritage_provenance(derived_type)
                .is_none()
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths()
            ),
            before
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Every forged edge must preserve the same unpublished state.
    fn concrete_base_provenance_authenticates_reference_cache_and_target() {
        for corruption in [
            "none",
            "wrong-owner",
            "wrong-target",
            "wrong-arguments",
            "uncached-reference",
            "sibling-cache",
        ] {
            let mut fixture = fixture_with_source(
                concat!(
                    "interface Base<T> { value: T } ",
                    "interface Other<T> { value: T } ",
                    "interface Derived extends Base<number> {}",
                ),
                862,
            );
            let base = interface_symbol(&fixture, "Base");
            let other = interface_symbol(&fixture, "Other");
            let derived = interface_symbol(&fixture, "Derived");
            let host = host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let [base_type, other_type, derived_type] = [base, other, derived].map(|symbol| {
                get_declared_class_interface_or_type_parameter(
                    &mut fixture.store,
                    &host,
                    symbol,
                    SymbolFlags::INTERFACE,
                )
                .unwrap()
                .unwrap()
            });
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (number, string) = (bootstrap.number_type, bootstrap.string_type);
            let reference = fixture
                .store
                .create_direct_generic_reference_type(base_type, &[number])
                .unwrap();
            let sibling = fixture
                .store
                .create_direct_generic_reference_type(base_type, &[string])
                .unwrap();
            let mut provenance = DirectInterfaceHeritageProvenance {
                owner_symbol: derived,
                base_symbol: base,
                base_type: reference,
                second_base: None,
            };
            match corruption {
                "none" => {}
                "wrong-owner" => provenance.base_symbol = other,
                "wrong-target" => assert!(fixture.store.set_object_target_and_mapper(
                    reference,
                    Some(other_type),
                    None,
                )),
                "wrong-arguments" => assert!(fixture.store.set_type_reference_resolution(
                    reference,
                    None,
                    Some(vec![string]),
                )),
                "uncached-reference" => {
                    let uncached = fixture
                        .store
                        .alloc_type_reference(ObjectFlags::NONE, Some(base))
                        .unwrap();
                    assert!(fixture.store.set_object_target_and_mapper(
                        uncached,
                        Some(base_type),
                        None,
                    ));
                    assert!(fixture.store.set_type_reference_resolution(
                        uncached,
                        None,
                        Some(vec![number]),
                    ));
                    provenance.base_type = uncached;
                }
                "sibling-cache" => assert!(fixture.store.set_type_reference_resolution(
                    sibling,
                    None,
                    Some(vec![number]),
                )),
                _ => unreachable!(),
            }
            assert!(
                fixture
                    .store
                    .try_reserve_direct_interface_heritage_provenance(1)
            );
            let before = (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.store.relation_state_snapshot(),
            );
            let accepted = fixture
                .store
                .publish_direct_interface_heritage_provenance(derived_type, provenance);
            assert_eq!(accepted, corruption == "none", "{corruption}");
            assert_eq!(
                fixture
                    .store
                    .direct_interface_heritage_provenance(derived_type),
                accepted.then_some(provenance),
                "{corruption}",
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.mapper_len(),
                    fixture.store.symbol_store().symbol_table_len(),
                    fixture.store.checker_link_allocated_lengths(),
                    fixture.store.relation_state_snapshot(),
                ),
                before,
                "{corruption}",
            );
            if accepted {
                assert_ne!(reference, base_type);
                assert!(
                    !fixture
                        .store
                        .publish_direct_interface_heritage_provenance(derived_type, provenance,)
                );
                assert_eq!(
                    fixture
                        .store
                        .direct_interface_heritage_provenance(derived_type),
                    Some(provenance),
                );
            }
        }
    }

    fn prepare() -> PreparedFixture {
        prepare_fixture(fixture())
    }

    fn prepare_indexed() -> PreparedFixture {
        prepare_fixture(fixture_with_source(INDEXED_SOURCE, 802))
    }

    fn prepare_callable() -> PreparedCallableFixture {
        let mut fixture = fixture_with_source(CALLABLE_SOURCE, 803);
        let base = interface_symbol(&fixture, "Base");
        let derived = interface_symbol(&fixture, "Derived");
        let host = host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let base_plan = object_members::plan_interface(&fixture.store, &host, base).unwrap();
        let derived_plan = object_members::plan_interface(&fixture.store, &host, derived).unwrap();
        let base_flags = fixture.store.symbol(base).unwrap().flags();
        let derived_flags = fixture.store.symbol(derived).unwrap().flags();
        let base_type = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            base,
            base_flags,
        )
        .unwrap()
        .unwrap();
        let derived_type = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            derived,
            derived_flags,
        )
        .unwrap()
        .unwrap();
        let string_type = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let state = object_members::interface_state(&fixture.store, &base_plan, base_type).unwrap();
        object_members::publish_declared_members(
            &mut fixture.store,
            &base_plan,
            state,
            &[],
            &[],
            &[ResolvedCallSignatureTypes {
                parameter_types: Vec::new(),
                return_type: string_type,
            }],
        )
        .unwrap();
        PreparedCallableFixture {
            fixture,
            derived_plan,
            base_type,
            derived_type,
            string_type,
        }
    }

    fn publish_interface_method_for_test(
        fixture: &mut Fixture,
        owner: &str,
    ) -> (SemanticSymbolId, TypeId, SignatureId) {
        let owner = interface_symbol(fixture, owner);
        let method = fixture
            .store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| fixture.store.symbol_table(members))
            .and_then(|members| members.get_source("method"))
            .unwrap();
        let [declaration] = fixture
            .store
            .symbol(method)
            .unwrap()
            .declarations()
            .unwrap()
        else {
            panic!("the method fixture contains one declaration per interface")
        };
        let declaration = *declaration;
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        let type_ = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
            .unwrap();
        let signature = fixture
            .store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(declaration),
                Vec::new(),
                None,
                Vec::new(),
                Some(void),
                None,
                0,
            )
            .unwrap();
        assert!(fixture.store.set_signature_links(
            declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(fixture.store.set_value_symbol_links(
            method,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(fixture.store.set_structured_type_members(
            type_,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));
        (method, type_, signature)
    }

    fn publish_overloaded_interface_method_for_test(
        fixture: &mut Fixture,
        owner: &str,
    ) -> (SemanticSymbolId, TypeId, Vec<SignatureId>) {
        let owner = interface_symbol(fixture, owner);
        let method = fixture
            .store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| fixture.store.symbol_table(members))
            .and_then(|members| members.get_source("method"))
            .unwrap();
        let declarations = fixture
            .store
            .symbol(method)
            .unwrap()
            .declarations()
            .unwrap()
            .to_vec();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (void, string, number) = (
            bootstrap.void_type,
            bootstrap.string_type,
            bootstrap.number_type,
        );
        let type_ = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
            .unwrap();
        let mut signatures = Vec::with_capacity(declarations.len());
        for declaration in declarations {
            let annotation = fixture
                .store
                .source_primitive_type_annotation(declaration)
                .unwrap();
            let return_type = match fixture.store.source_node_kind(annotation) {
                Some(SyntaxKind::VoidKeyword) => void,
                Some(SyntaxKind::StringKeyword) => string,
                Some(SyntaxKind::NumberKeyword) => number,
                _ => panic!("the overload fixture uses primitive return annotations"),
            };
            let signature = fixture
                .store
                .alloc_signature(
                    SignatureFlags::NONE,
                    Some(declaration),
                    Vec::new(),
                    None,
                    Vec::new(),
                    Some(return_type),
                    None,
                    0,
                )
                .unwrap();
            assert!(fixture.store.set_signature_links(
                declaration,
                SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                },
            ));
            signatures.push(signature);
        }
        assert!(fixture.store.set_value_symbol_links(
            method,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(fixture.store.set_structured_type_members(
            type_,
            None,
            None,
            Some(signatures.clone()),
            None,
            None,
        ));
        (method, type_, signatures)
    }

    fn publish_parameterized_interface_method_for_test(
        fixture: &mut Fixture,
        owner: &str,
        parameter_type: TypeId,
    ) -> (SemanticSymbolId, TypeId, SignatureId, SemanticSymbolId) {
        let owner = interface_symbol(fixture, owner);
        let host = host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let plan = object_members::plan_interface(&fixture.store, &host, owner).unwrap();
        let flags = fixture.store.symbol(owner).unwrap().flags();
        get_declared_class_interface_or_type_parameter(&mut fixture.store, &host, owner, flags)
            .unwrap()
            .unwrap();
        let [method] = plan.methods.as_slice() else {
            panic!("the parameterized method fixture contains one method")
        };
        let [parameter] = method.parameters.as_slice() else {
            panic!("the parameterized method fixture contains one parameter")
        };
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        let type_ = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method.symbol))
            .unwrap();
        let signature = fixture
            .store
            .alloc_signature(
                method.flags,
                Some(method.declaration),
                Vec::new(),
                None,
                vec![parameter.symbol],
                Some(void),
                None,
                1,
            )
            .unwrap();
        assert!(fixture.store.set_signature_links(
            method.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(fixture.store.set_value_symbol_links(
            parameter.symbol,
            ValueSymbolLinks {
                resolved_type: Some(parameter_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(fixture.store.set_value_symbol_links(
            method.symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(fixture.store.set_structured_type_members(
            type_,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));
        assert!(
            fixture
                .store
                .callable_signature_parameter_types(signature)
                .is_none()
        );
        (method.symbol, type_, signature, parameter.symbol)
    }

    fn indexed_derived_plan(
        fixture: &Fixture,
        host: &DeclaredTypeHost<'_>,
        symbol: SemanticSymbolId,
        template: &PropertyObjectPlan,
    ) -> PropertyObjectPlan {
        let owner = fixture.store.symbol(symbol).unwrap();
        let [declaration] = owner.declarations().unwrap() else {
            panic!("the indexed inheritance fixture has one derived declaration")
        };
        let declaration = *declaration;
        let NodeData::InterfaceDeclaration(interface) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("the derived symbol must retain its interface declaration")
        };
        let heritage = plan_direct_interface_heritage(
            &fixture.store,
            host,
            declaration,
            symbol,
            interface.heritage_clauses.as_ref().unwrap(),
        )
        .unwrap();
        let mut plan = template.clone();
        plan.node = declaration;
        plan.declarations = vec![declaration];
        plan.symbol = symbol;
        plan.members = owner.members();
        plan.properties.clear();
        plan.spreads.clear();
        plan.indexes.clear();
        plan.call_signatures.clear();
        plan.alias_symbol = None;
        plan.heritage = Some(heritage);
        if interface.members.nodes.is_empty() {
            return plan;
        }
        let [property_node] = interface.members.nodes.as_slice() else {
            panic!("the derived interface has one source property")
        };
        let property_declaration =
            NodeRef::new(declaration.arena, declaration.file, *property_node);
        let (property_name, property_type, postfix_token) = match &fixture
            .parsed
            .arena
            .get(property_declaration.node)
            .unwrap()
            .data
        {
            NodeData::PropertyDeclaration(property) => (
                property.name,
                property
                    .type_
                    .expect("the derived source property has a type annotation"),
                property.postfix_token,
            ),
            NodeData::PropertySignatureDeclaration(property) => {
                (property.name, property.type_, property.postfix_token)
            }
            _ => panic!("the derived source member must be an interface property"),
        };
        assert!(postfix_token.is_none_or(|token| {
            fixture.parsed.arena.get(token).unwrap().kind == SyntaxKind::QuestionToken
        }));
        let name_node = NodeRef::new(declaration.arena, declaration.file, property_name);
        let bound = fixture.files.get(&fixture.file).unwrap();
        let property_symbol = bound.symbol(property_declaration).unwrap();
        assert_eq!(
            fixture.store.get_merged_symbol(property_symbol),
            Some(property_symbol)
        );
        let name = fixture
            .store
            .symbol(property_symbol)
            .unwrap()
            .name()
            .to_owned();
        plan.properties = vec![PlannedProperty {
            declaration: property_declaration,
            symbol: property_symbol,
            name_node,
            type_node: NodeRef::new(declaration.arena, declaration.file, property_type),
            optional: postfix_token.is_some(),
            readonly: ts_binder::canonical_has_syntactic_modifier(
                &fixture.parsed.arena,
                property_declaration.node,
                SyntaxKind::ReadonlyKeyword,
            ),
            name,
        }];
        plan
    }

    fn prepare_fixture(mut fixture: Fixture) -> PreparedFixture {
        let base = interface_symbol(&fixture, "Base");
        let other = interface_symbol(&fixture, "Other");
        let derived = interface_symbol(&fixture, "Derived");
        let host = host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let base_plan = object_members::plan_interface(&fixture.store, &host, base).unwrap();
        let other_plan = object_members::plan_interface(&fixture.store, &host, other).unwrap();
        let derived_plan = if base_plan.indexes.is_empty() {
            object_members::plan_interface(&fixture.store, &host, derived).unwrap()
        } else {
            assert!(matches!(
                object_members::plan_interface(&fixture.store, &host, derived),
                Err(PropertyObjectError::UnsupportedMember {
                    kind: SyntaxKind::IndexSignature,
                    ..
                })
            ));
            indexed_derived_plan(&fixture, &host, derived, &other_plan)
        };
        let base_flags = fixture.store.symbol(base).unwrap().flags();
        let other_flags = fixture.store.symbol(other).unwrap().flags();
        let derived_flags = fixture.store.symbol(derived).unwrap().flags();
        let base_type = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            base,
            base_flags,
        )
        .unwrap()
        .unwrap();
        let other_type = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            other,
            other_flags,
        )
        .unwrap()
        .unwrap();
        let derived_type = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            derived,
            derived_flags,
        )
        .unwrap()
        .unwrap();
        let number_type = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let string_type = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        for (plan, type_) in [(&base_plan, base_type), (&other_plan, other_type)] {
            let state = object_members::interface_state(&fixture.store, plan, type_).unwrap();
            assert_eq!(state, PropertyObjectState::Shell(type_));
            let indexes = plan
                .indexes
                .iter()
                .map(|index| {
                    let key = match fixture.store.source_node_kind(index.key_type_node) {
                        Some(SyntaxKind::StringKeyword) => string_type,
                        Some(SyntaxKind::NumberKeyword) => number_type,
                        _ => panic!("the index fixture uses string or number keys"),
                    };
                    (key, number_type)
                })
                .collect::<Vec<_>>();
            object_members::publish_declared_members(
                &mut fixture.store,
                plan,
                state,
                &vec![number_type; plan.properties.len()],
                &indexes,
                &[],
            )
            .unwrap();
        }
        PreparedFixture {
            fixture,
            derived_plan,
            base_type,
            other_type,
            derived_type,
            number_type,
        }
    }

    #[test]
    fn interface_methods_preserve_owner_and_match_distinct_callable_identities() {
        let mut fixture = fixture_with_source(METHOD_SOURCE, 804);
        let (base, base_type, base_signature) =
            publish_interface_method_for_test(&mut fixture, "Base");
        let (derived, derived_type, derived_signature) =
            publish_interface_method_for_test(&mut fixture, "Derived");

        assert_ne!(base_type, derived_type);
        assert_ne!(base_signature, derived_signature);
        assert!(valid_property_symbol(&fixture.store, base));
        assert!(valid_property_symbol(&fixture.store, derived));
        assert_eq!(
            valid_interface_method_value(&fixture.store, base, base_type),
            Some(base_signature)
        );
        assert_eq!(
            valid_interface_method_value(&fixture.store, derived, derived_type),
            Some(derived_signature)
        );
        assert!(matching_interface_method_contract(
            &fixture.store,
            base,
            derived
        ));
        assert!(matching_inherited_property_contract(
            &fixture.store,
            base,
            derived
        ));
    }

    #[test]
    fn merged_interface_method_owners_preserve_authenticated_signatures() {
        let mut fixture = fixture_with_source(METHOD_SOURCE, 809);
        let (base, base_type, base_signature) =
            publish_interface_method_for_test(&mut fixture, "Base");
        let (derived, _, _) = publish_interface_method_for_test(&mut fixture, "Derived");
        let owner = interface_symbol(&fixture, "Base");
        assert!(fixture.store.set_symbol_flags(
            owner,
            SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            valid_interface_method_value(&fixture.store, base, base_type),
            Some(base_signature),
        );
        assert!(valid_property_symbol(&fixture.store, base));
        assert!(matching_interface_method_contract(
            &fixture.store,
            base,
            derived,
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );

        assert!(fixture.store.set_symbol_flags(
            owner,
            SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT | SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            CheckFlags::NONE,
        ));
        assert_eq!(
            valid_interface_method_value(&fixture.store, base, base_type),
            None,
        );
        assert!(!valid_property_symbol(&fixture.store, base));
        assert!(!matching_interface_method_contract(
            &fixture.store,
            base,
            derived,
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn malformed_interface_method_values_and_return_types_fail_closed() {
        let mut fixture = fixture_with_source(METHOD_SOURCE, 805);
        let (base, _, _) = publish_interface_method_for_test(&mut fixture, "Base");
        let (derived, derived_type, signature) =
            publish_interface_method_for_test(&mut fixture, "Derived");
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;

        assert!(
            fixture
                .store
                .set_signature_resolved_return_type(signature, Some(number))
        );
        assert!(!valid_property_symbol(&fixture.store, derived));
        assert!(!matching_interface_method_contract(
            &fixture.store,
            base,
            derived
        ));

        assert!(
            fixture
                .store
                .set_signature_resolved_return_type(signature, Some(void))
        );
        assert!(valid_property_symbol(&fixture.store, derived));

        let forged = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(base))
            .unwrap();
        assert!(fixture.store.set_structured_type_members(
            forged,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));
        assert!(fixture.store.set_value_symbol_links(
            derived,
            ValueSymbolLinks {
                resolved_type: Some(forged),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(!valid_property_symbol(&fixture.store, derived));
        assert_eq!(
            valid_interface_method_value(&fixture.store, derived, forged),
            None
        );
        assert_ne!(derived_type, forged);
    }

    #[test]
    fn overloaded_interface_methods_validate_every_signature_in_source_order() {
        let mut fixture = fixture_with_source(
            concat!(
                "interface Base { method(): void; method(): string }\n",
                "interface Derived { method(): void; method(): string }\n",
                "interface Different { method(): void; method(): number }\n",
            ),
            807,
        );
        let (base, base_type, base_signatures) =
            publish_overloaded_interface_method_for_test(&mut fixture, "Base");
        let (derived, derived_type, derived_signatures) =
            publish_overloaded_interface_method_for_test(&mut fixture, "Derived");
        let (different, different_type, different_signatures) =
            publish_overloaded_interface_method_for_test(&mut fixture, "Different");

        assert_eq!(base_signatures.len(), 2);
        assert_eq!(derived_signatures.len(), 2);
        assert_eq!(different_signatures.len(), 2);
        assert_eq!(
            valid_interface_method_value(&fixture.store, base, base_type),
            Some(base_signatures[0])
        );
        assert_eq!(
            valid_interface_method_value(&fixture.store, derived, derived_type),
            Some(derived_signatures[0])
        );
        assert_eq!(
            valid_interface_method_value(&fixture.store, different, different_type),
            Some(different_signatures[0])
        );
        assert!(valid_property_symbol(&fixture.store, base));
        assert!(valid_property_symbol(&fixture.store, derived));
        assert!(matching_interface_method_contract(
            &fixture.store,
            base,
            derived
        ));
        assert!(!matching_interface_method_contract(
            &fixture.store,
            base,
            different
        ));

        assert!(fixture.store.set_structured_type_members(
            derived_type,
            None,
            None,
            Some(vec![derived_signatures[1], derived_signatures[0]]),
            None,
            None,
        ));
        assert_eq!(
            valid_interface_method_value(&fixture.store, derived, derived_type),
            None
        );
        assert!(!valid_property_symbol(&fixture.store, derived));
        assert!(!matching_interface_method_contract(
            &fixture.store,
            base,
            derived
        ));
    }

    #[test]
    fn interface_methods_read_published_parameter_types_without_signature_cache() {
        let mut fixture = fixture_with_source(
            concat!(
                "interface Base { method(value: string): void }\n",
                "interface Derived { method(value: string): void }\n",
                "interface Different { method(value: number): void }\n",
            ),
            808,
        );
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        let (base, base_type, base_signature, _) =
            publish_parameterized_interface_method_for_test(&mut fixture, "Base", string);
        let (derived, derived_type, derived_signature, derived_parameter) =
            publish_parameterized_interface_method_for_test(&mut fixture, "Derived", string);
        let (different, different_type, different_signature, _) =
            publish_parameterized_interface_method_for_test(&mut fixture, "Different", number);

        assert_eq!(
            valid_interface_method_value(&fixture.store, base, base_type),
            Some(base_signature)
        );
        assert_eq!(
            valid_interface_method_value(&fixture.store, derived, derived_type),
            Some(derived_signature)
        );
        assert_eq!(
            valid_interface_method_value(&fixture.store, different, different_type),
            Some(different_signature)
        );
        assert!(matching_interface_method_contract(
            &fixture.store,
            base,
            derived
        ));
        assert!(!matching_interface_method_contract(
            &fixture.store,
            base,
            different
        ));

        assert!(
            fixture
                .store
                .set_value_symbol_links(derived_parameter, ValueSymbolLinks::default())
        );
        assert_eq!(
            valid_interface_method_value(&fixture.store, derived, derived_type),
            None
        );
        assert!(!matching_interface_method_contract(
            &fixture.store,
            base,
            derived
        ));
    }

    #[test]
    fn interface_methods_keep_optional_parameter_arity() {
        let mut fixture =
            fixture_with_source("interface Base { method(value?: string): string }", 809);
        let owner = interface_symbol(&fixture, "Base");
        let host = host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let plan = object_members::plan_interface(&fixture.store, &host, owner).unwrap();
        let flags = fixture.store.symbol(owner).unwrap().flags();
        get_declared_class_interface_or_type_parameter(&mut fixture.store, &host, owner, flags)
            .unwrap()
            .unwrap();
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;

        let values = object_members::publish_interface_method_values(
            &mut fixture.store,
            &plan,
            &[ResolvedCallSignatureTypes {
                parameter_types: vec![string],
                return_type: string,
            }],
        )
        .unwrap();

        let method = plan.methods[0].symbol;
        let signature = valid_interface_method_value(&fixture.store, method, values[0])
            .expect("an optional method parameter must retain a valid source signature");
        assert_eq!(
            fixture
                .store
                .signature(signature)
                .unwrap()
                .min_argument_count(),
            0
        );
        assert!(valid_property_symbol(&fixture.store, method));
    }

    #[test]
    fn callable_interface_heritage_keeps_derived_signatures_before_base_signatures() {
        let mut prepared = prepare_callable();
        let call_types = [ResolvedCallSignatureTypes {
            parameter_types: vec![prepared.string_type],
            return_type: prepared.string_type,
        }];
        let base_signature = {
            let TypeData::Interface(interface) = prepared
                .fixture
                .store
                .type_payload(prepared.base_type)
                .unwrap()
                .data()
            else {
                panic!("the callable base must retain its interface type")
            };
            interface.declared_call_signatures.as_ref().unwrap()[0]
        };

        assert_eq!(
            resolve_direct_interface_callable_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &call_types,
                &[prepared.base_type],
            ),
            Ok(prepared.derived_type)
        );

        let TypeData::Interface(interface) = prepared
            .fixture
            .store
            .type_payload(prepared.derived_type)
            .unwrap()
            .data()
        else {
            panic!("the derived callable must retain its interface type")
        };
        let [own] = interface.declared_call_signatures.as_deref().unwrap() else {
            panic!("the derived interface declares one call signature")
        };
        let own = *own;
        assert_eq!(
            interface.reference.object.structured.signatures.as_deref(),
            Some([own, base_signature].as_slice())
        );
        assert_eq!(
            interface.reference.object.structured.call_signature_count,
            2
        );
        assert_ne!(
            interface.reference.object.structured.members,
            interface.declared_members
        );
        let declared_call = prepared.derived_plan.call_signatures[0].symbol;
        assert_eq!(
            interface
                .reference
                .object
                .structured
                .members
                .and_then(|members| prepared.fixture.store.symbol_table(members))
                .and_then(|members| members.get(InternalSymbolName::Call.as_ref())),
            Some(declared_call)
        );
        assert_eq!(
            prepared
                .fixture
                .store
                .declared_call_set_type_for_signature(own),
            Some(prepared.derived_type)
        );
        assert_eq!(
            prepared
                .fixture
                .store
                .declared_call_set_type_for_signature(base_signature),
            Some(prepared.base_type)
        );
        assert_eq!(
            validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type),
            InterfaceHeritageMembersValidation::Valid
        );
        assert_eq!(
            validate_stored_declared_call_set(&prepared.fixture.store, prepared.derived_type),
            StoredDeclaredCallSetValidation::Valid(vec![
                prepared.string_type,
                prepared.string_type,
                prepared.string_type,
            ])
        );

        let warm = (
            prepared.fixture.store.signature_len(),
            prepared.fixture.store.symbol_store().symbol_table_len(),
            prepared.fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            resolve_direct_interface_callable_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &call_types,
                &[prepared.base_type],
            ),
            Ok(prepared.derived_type)
        );
        assert_eq!(
            (
                prepared.fixture.store.signature_len(),
                prepared.fixture.store.symbol_store().symbol_table_len(),
                prepared.fixture.store.checker_link_allocated_lengths(),
            ),
            warm
        );
    }

    #[test]
    fn reordered_inherited_call_signatures_fail_without_republication() {
        let mut prepared = prepare_callable();
        let call_types = [ResolvedCallSignatureTypes {
            parameter_types: vec![prepared.string_type],
            return_type: prepared.string_type,
        }];
        resolve_direct_interface_callable_members(
            &mut prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
            &call_types,
            &[prepared.base_type],
        )
        .unwrap();
        let (members, own, base) = {
            let TypeData::Interface(interface) = prepared
                .fixture
                .store
                .type_payload(prepared.derived_type)
                .unwrap()
                .data()
            else {
                panic!("the derived callable must retain its interface type")
            };
            let [own, base] = interface
                .reference
                .object
                .structured
                .signatures
                .as_deref()
                .unwrap()
            else {
                panic!("the derived callable must retain its own and inherited signatures")
            };
            (interface.reference.object.structured.members, *own, *base)
        };
        assert!(prepared.fixture.store.set_structured_type_members(
            prepared.derived_type,
            members,
            None,
            Some(vec![base, own]),
            None,
            None,
        ));
        let before = (
            prepared.fixture.store.signature_len(),
            prepared.fixture.store.symbol_store().symbol_table_len(),
            prepared.fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type),
            InterfaceHeritageMembersValidation::Malformed
        );
        assert_eq!(
            validate_stored_declared_call_set(&prepared.fixture.store, prepared.derived_type),
            StoredDeclaredCallSetValidation::Malformed
        );
        assert!(
            resolve_direct_interface_callable_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &call_types,
                &[prepared.base_type],
            )
            .is_err()
        );
        assert_eq!(
            (
                prepared.fixture.store.signature_len(),
                prepared.fixture.store.symbol_store().symbol_table_len(),
                prepared.fixture.store.checker_link_allocated_lengths(),
            ),
            before
        );
    }

    #[test]
    fn inherited_indexes_keep_source_identity_and_exact_cold_and_warm_members() {
        let mut prepared = prepare_indexed();
        let base_index = {
            let TypeData::Interface(base) = prepared
                .fixture
                .store
                .type_payload(prepared.base_type)
                .unwrap()
                .data()
            else {
                panic!("the indexed base must retain its interface type")
            };
            let [index] = base.declared_index_infos.as_deref().unwrap() else {
                panic!("the indexed base must publish one source index")
            };
            *index
        };
        let before_indexes = prepared.fixture.store.index_info_len();

        assert_eq!(
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[prepared.number_type],
                &[prepared.base_type],
            ),
            Ok(prepared.derived_type)
        );

        let TypeData::Interface(derived) = prepared
            .fixture
            .store
            .type_payload(prepared.derived_type)
            .unwrap()
            .data()
        else {
            panic!("the derived interface must retain its interface type")
        };
        assert_eq!(derived.declared_index_infos, None);
        assert_eq!(
            derived.reference.object.structured.index_infos.as_deref(),
            Some(&[base_index][..])
        );
        let members = prepared
            .fixture
            .store
            .symbol_table(derived.reference.object.structured.members.unwrap())
            .unwrap();
        assert_eq!(members.len(), 3);
        assert_eq!(members.get(InternalSymbolName::Index.as_ref()), None);
        let property_names = derived
            .reference
            .object
            .structured
            .properties
            .as_deref()
            .unwrap()
            .iter()
            .map(|property| {
                prepared
                    .fixture
                    .store
                    .symbol(*property)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(property_names, ["own", "first", "second"]);
        assert_eq!(prepared.fixture.store.index_info_len(), before_indexes);
        assert!(validate_planned_interface_heritage_members(
            &prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
        ));

        let warm_state = (
            prepared.fixture.store.type_len(),
            prepared.fixture.store.index_info_len(),
            prepared.fixture.store.symbol_store().symbol_table_len(),
            prepared.fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[prepared.number_type],
                &[prepared.base_type],
            ),
            Ok(prepared.derived_type)
        );
        assert_eq!(
            (
                prepared.fixture.store.type_len(),
                prepared.fixture.store.index_info_len(),
                prepared.fixture.store.symbol_store().symbol_table_len(),
                prepared.fixture.store.checker_link_allocated_lengths(),
            ),
            warm_state
        );
    }

    fn prepare_indexed_reader() -> PreparedFixture {
        let mut prepared = prepare_indexed();
        resolve_direct_interface_members(
            &mut prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
            &[prepared.number_type],
            &[prepared.base_type],
        )
        .unwrap();
        prepared
    }

    #[test]
    fn inherited_index_reader_preserves_own_and_inherited_tables_cold_and_warm() {
        let mut prepared = prepare_indexed_reader();
        let base = prepared
            .fixture
            .store
            .type_payload(prepared.base_type)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .clone();
        let derived = prepared
            .fixture
            .store
            .type_payload(prepared.derived_type)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .clone();
        assert_eq!(base.index_infos, derived.index_infos);
        assert!(
            prepared
                .fixture
                .store
                .symbol_table(base.members.unwrap())
                .unwrap()
                .get(InternalSymbolName::Index.as_ref())
                .is_some()
        );
        assert!(
            prepared
                .fixture
                .store
                .symbol_table(derived.members.unwrap())
                .unwrap()
                .get(InternalSymbolName::Index.as_ref())
                .is_none()
        );
        let own = prepared.derived_plan.properties[0].symbol;
        let first = prepared
            .fixture
            .store
            .symbol_table(base.members.unwrap())
            .unwrap()
            .get_source("first")
            .unwrap();
        let before = (
            derived_state(&prepared.fixture.store, prepared.derived_type, own),
            prepared.fixture.store.type_len(),
            prepared.fixture.store.index_info_len(),
            prepared.fixture.store.relation_state_snapshot(),
        );
        for _ in 0..2 {
            for (receiver, name, symbol) in [
                (prepared.base_type, "first", first),
                (prepared.derived_type, "own", own),
                (prepared.derived_type, "first", first),
            ] {
                let property = prepared
                    .fixture
                    .store
                    .resolved_own_property(receiver, name)
                    .unwrap()
                    .unwrap();
                assert_eq!(property.symbol, symbol);
                assert_eq!(property.type_, prepared.number_type);
            }
            assert_eq!(
                prepared
                    .fixture
                    .store
                    .resolved_own_property(prepared.derived_type, "missing"),
                Ok(None),
            );
            assert_eq!(
                (
                    derived_state(&prepared.fixture.store, prepared.derived_type, own),
                    prepared.fixture.store.type_len(),
                    prepared.fixture.store.index_info_len(),
                    prepared.fixture.store.relation_state_snapshot(),
                ),
                before,
            );
        }
    }

    #[test]
    fn inherited_index_reader_accepts_an_empty_inherited_property_table() {
        let mut prepared = prepare_fixture(fixture_with_source(
            "interface Base { [key: string]: number; } interface Other { other: number; } \
             interface Derived extends Base {}",
            32_181,
        ));
        resolve_direct_interface_members(
            &mut prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
            &[],
            &[prepared.base_type],
        )
        .unwrap();
        let structured = prepared
            .fixture
            .store
            .type_payload(prepared.derived_type)
            .unwrap()
            .data()
            .structured()
            .unwrap();
        assert!(structured.members.is_none());
        assert!(structured.properties.is_none());
        assert_eq!(structured.index_infos.as_deref().unwrap().len(), 1);
        for _ in 0..2 {
            assert_eq!(
                prepared
                    .fixture
                    .store
                    .resolved_own_property(prepared.derived_type, "missing"),
                Ok(None),
            );
        }
    }

    fn assert_index_reader_rejected(
        prepared: &mut PreparedFixture,
        receiver: TypeId,
        name: &str,
        damage: &str,
    ) {
        let state = |store: &CanonicalTypeMapperStore| {
            let structured = store
                .type_payload(receiver)
                .unwrap()
                .data()
                .structured()
                .unwrap();
            let property = structured.properties.as_ref().unwrap()[0];
            let entries = store
                .symbol_table(structured.members.unwrap())
                .unwrap()
                .iter()
                .map(|(name, symbol)| (name.to_owned(), symbol))
                .collect::<Vec<_>>();
            let indexes = structured
                .index_infos
                .as_deref()
                .unwrap_or_default()
                .iter()
                .map(|index| {
                    let info = store.index_info(*index).unwrap();
                    (
                        *index,
                        info.key_type(),
                        info.value_type(),
                        info.is_readonly(),
                        info.declaration(),
                        info.index_symbol(),
                        info.components().to_vec(),
                    )
                })
                .collect::<Vec<_>>();
            (
                derived_state(store, receiver, property),
                [
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.index_info_len(),
                    store.symbol_store().symbol_table_len(),
                ],
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
                entries,
                indexes,
            )
        };
        let before = state(&prepared.fixture.store);
        for _ in 0..2 {
            assert_eq!(
                prepared.fixture.store.resolved_own_property(receiver, name),
                Err(RelationUnavailable::InvalidStructuredMembers(receiver)),
                "{damage}",
            );
            assert_eq!(state(&prepared.fixture.store), before, "{damage}");
        }
    }

    #[test]
    fn inherited_index_reader_rejects_wrong_inherited_entries_and_table_counts() {
        for warm in [false, true] {
            for damage in [
                "index-copy",
                "index-metadata",
                "local-index",
                "extra-property",
                "missing-property",
            ] {
                let mut prepared = prepare_indexed_reader();
                let receiver = prepared.derived_type;
                if warm {
                    assert!(
                        prepared
                            .fixture
                            .store
                            .resolved_own_property(receiver, "own")
                            .unwrap()
                            .is_some()
                    );
                }
                let structured = prepared
                    .fixture
                    .store
                    .type_payload(receiver)
                    .unwrap()
                    .data()
                    .structured()
                    .unwrap()
                    .clone();
                let members = structured.members.unwrap();
                let index = structured.index_infos.as_ref().unwrap()[0];
                let base = prepared
                    .fixture
                    .store
                    .type_payload(prepared.base_type)
                    .unwrap()
                    .data()
                    .structured()
                    .unwrap();
                let index_symbol = prepared
                    .fixture
                    .store
                    .symbol_table(base.members.unwrap())
                    .unwrap()
                    .get(InternalSymbolName::Index.as_ref())
                    .unwrap();
                match damage {
                    "index-copy" => {
                        let info = prepared.fixture.store.index_info(index).unwrap();
                        let (key, value, readonly, declaration) = (
                            info.key_type(),
                            info.value_type(),
                            info.is_readonly(),
                            info.declaration(),
                        );
                        let wrong = prepared
                            .fixture
                            .store
                            .alloc_index_info(key, value, readonly, declaration, Vec::new())
                            .unwrap();
                        assert!(prepared.fixture.store.set_structured_type_members(
                            receiver,
                            Some(members),
                            structured.properties,
                            None,
                            None,
                            Some(vec![wrong]),
                        ));
                    }
                    "index-metadata" => assert!(prepared.fixture.store.set_index_info_symbol(
                        index,
                        Some(prepared.derived_plan.properties[0].symbol),
                    )),
                    "local-index" => assert_eq!(
                        prepared.fixture.store.insert_symbol(
                            members,
                            EscapedName::internal(InternalSymbolName::Index),
                            index_symbol,
                        ),
                        Some(None),
                    ),
                    "extra-property" => {
                        let other = prepared
                            .fixture
                            .store
                            .type_payload(prepared.other_type)
                            .unwrap()
                            .data()
                            .structured()
                            .unwrap()
                            .properties
                            .as_ref()
                            .unwrap()[0];
                        assert_eq!(
                            prepared.fixture.store.insert_symbol(
                                members,
                                EscapedName::source("other"),
                                other,
                            ),
                            Some(None)
                        );
                    }
                    "missing-property" => {
                        let entries = prepared
                            .fixture
                            .store
                            .symbol_table(members)
                            .unwrap()
                            .iter()
                            .filter(|(name, _)| name.as_utf8() != Some("first"))
                            .map(|(name, symbol)| (name.to_owned(), symbol))
                            .collect::<Vec<_>>();
                        let wrong = prepared.fixture.store.alloc_symbol_table();
                        for (name, symbol) in entries {
                            assert_eq!(
                                prepared.fixture.store.insert_symbol(wrong, name, symbol),
                                Some(None)
                            );
                        }
                        assert!(prepared.fixture.store.set_structured_type_members(
                            receiver,
                            Some(wrong),
                            structured.properties,
                            None,
                            None,
                            structured.index_infos,
                        ));
                    }
                    _ => unreachable!(),
                }
                assert_index_reader_rejected(&mut prepared, receiver, "own", damage);
            }
        }
    }

    #[test]
    fn inherited_index_reader_keeps_own_index_slots_and_exact_own_tables_required() {
        for warm in [false, true] {
            for damage in [
                "missing-index",
                "wrong-index",
                "extra-property",
                "wrong-property",
            ] {
                let mut prepared = prepare_indexed_reader();
                let receiver = prepared.base_type;
                if warm {
                    assert!(
                        prepared
                            .fixture
                            .store
                            .resolved_own_property(receiver, "first")
                            .unwrap()
                            .is_some()
                    );
                }
                let structured = prepared
                    .fixture
                    .store
                    .type_payload(receiver)
                    .unwrap()
                    .data()
                    .structured()
                    .unwrap()
                    .clone();
                let members = structured.members.unwrap();
                let first = prepared
                    .fixture
                    .store
                    .symbol_table(members)
                    .unwrap()
                    .get_source("first")
                    .unwrap();
                match damage {
                    "missing-index" => {
                        let entries = prepared
                            .fixture
                            .store
                            .symbol_table(members)
                            .unwrap()
                            .iter()
                            .filter(|(name, _)| *name != InternalSymbolName::Index.as_ref())
                            .map(|(name, symbol)| (name.to_owned(), symbol))
                            .collect::<Vec<_>>();
                        let wrong = prepared.fixture.store.alloc_symbol_table();
                        for (name, symbol) in entries {
                            assert_eq!(
                                prepared.fixture.store.insert_symbol(wrong, name, symbol),
                                Some(None)
                            );
                        }
                        let owner = prepared
                            .fixture
                            .store
                            .type_payload(receiver)
                            .unwrap()
                            .symbol()
                            .unwrap();
                        assert!(prepared.fixture.store.set_symbol_relationships(
                            owner,
                            Some(wrong),
                            None,
                            None,
                            None
                        ));
                        assert!(prepared.fixture.store.set_interface_declared_members(
                            receiver,
                            true,
                            Some(wrong),
                            None,
                            None,
                            structured.index_infos.clone(),
                        ));
                        assert!(prepared.fixture.store.set_structured_type_members(
                            receiver,
                            Some(wrong),
                            structured.properties,
                            None,
                            None,
                            structured.index_infos,
                        ));
                    }
                    "wrong-index" => {
                        assert!(
                            prepared
                                .fixture
                                .store
                                .insert_symbol(
                                    members,
                                    EscapedName::internal(InternalSymbolName::Index),
                                    first,
                                )
                                .unwrap()
                                .is_some()
                        );
                    }
                    "extra-property" => {
                        let other = prepared
                            .fixture
                            .store
                            .type_payload(prepared.other_type)
                            .unwrap()
                            .data()
                            .structured()
                            .unwrap()
                            .properties
                            .as_ref()
                            .unwrap()[0];
                        assert_eq!(
                            prepared.fixture.store.insert_symbol(
                                members,
                                EscapedName::source("other"),
                                other,
                            ),
                            Some(None)
                        );
                    }
                    "wrong-property" => {
                        let second = prepared
                            .fixture
                            .store
                            .symbol_table(members)
                            .unwrap()
                            .get_source("second")
                            .unwrap();
                        assert_eq!(
                            prepared.fixture.store.insert_symbol(
                                members,
                                EscapedName::source("first"),
                                second,
                            ),
                            Some(Some(first))
                        );
                    }
                    _ => unreachable!(),
                }
                assert_index_reader_rejected(&mut prepared, receiver, "first", damage);
            }
        }
    }

    fn prepare_inherited_index_property(key: &str, property: &str) -> PreparedFixture {
        prepare_fixture(fixture_with_source(
            &format!(
                "interface Base {{ [key: {key}]: number; first: number; second: number }} \
                 interface Other {{ other: number }} \
                 interface Derived extends Base {{ {property} }}",
            ),
            32_180,
        ))
    }

    #[test]
    fn inherited_index_properties_keep_applicable_values_required_and_exact() {
        for (key, property, compatible) in [
            ("string", "own: number", true),
            ("string", "own: string", false),
            ("string", "own?: number", false),
            ("number", "own: string", true),
            ("number", "own?: string", true),
            ("number", "readonly own: string", true),
            ("number", "0: number", true),
            ("number", "0: string", false),
            ("number", "0?: number", false),
            ("number", "\"01\": string", true),
            ("number", "\"-1\": number", true),
            ("number", "\"-1\": string", false),
        ] {
            let mut prepared = prepare_inherited_index_property(key, property);
            let own = &prepared.derived_plan.properties[0];
            let property_type = match prepared.fixture.store.source_node_kind(own.type_node) {
                Some(SyntaxKind::NumberKeyword) => prepared.number_type,
                Some(SyntaxKind::StringKeyword) => {
                    prepared
                        .fixture
                        .store
                        .intrinsic_bootstrap()
                        .unwrap()
                        .string_type
                }
                _ => unreachable!(),
            };
            let own = own.symbol;
            let expected = if compatible {
                Ok(prepared.derived_type)
            } else {
                Err(PropertyObjectError::UnsupportedMember {
                    node: prepared.derived_plan.node,
                    kind: SyntaxKind::InterfaceDeclaration,
                })
            };
            let mut before = derived_state(&prepared.fixture.store, prepared.derived_type, own);
            for attempt in 0..2 {
                assert_eq!(
                    resolve_direct_interface_members(
                        &mut prepared.fixture.store,
                        &prepared.derived_plan,
                        prepared.derived_type,
                        &[property_type],
                        &[prepared.base_type],
                    ),
                    expected,
                    "{key}: {property}",
                );
                let after = derived_state(&prepared.fixture.store, prepared.derived_type, own);
                if !compatible || attempt != 0 {
                    assert_eq!(after, before, "{key}: {property}");
                }
                before = after;
                if compatible {
                    assert_eq!(
                        validate_interface_heritage_members(
                            &prepared.fixture.store,
                            prepared.derived_type,
                        ),
                        InterfaceHeritageMembersValidation::Valid,
                        "{key}: {property}",
                    );
                }
            }
        }
    }

    #[test]
    fn inherited_numeric_index_rejects_invalid_own_proofs_before_publication() {
        for damage in ["name", "optional", "foreign-type", "missing-type"] {
            let mut prepared = prepare_inherited_index_property("number", "own?: string");
            let own = prepared.derived_plan.properties[0].symbol;
            let mut types = vec![
                prepared
                    .fixture
                    .store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .string_type,
            ];
            match damage {
                "name" => prepared.derived_plan.properties[0].name = EscapedName::source("01"),
                "optional" => prepared.derived_plan.properties[0].optional = false,
                "foreign-type" => {
                    types[0] = fixture().store.intrinsic_bootstrap().unwrap().string_type;
                }
                "missing-type" => types.clear(),
                _ => unreachable!(),
            }
            let before = (
                derived_state(&prepared.fixture.store, prepared.derived_type, own),
                prepared.fixture.store.type_len(),
                prepared.fixture.store.index_info_len(),
                prepared.fixture.store.checker_link_allocated_lengths(),
                prepared.fixture.store.relation_state_snapshot(),
            );
            for _ in 0..2 {
                assert_eq!(
                    resolve_direct_interface_members(
                        &mut prepared.fixture.store,
                        &prepared.derived_plan,
                        prepared.derived_type,
                        &types,
                        &[prepared.base_type],
                    ),
                    Err(invalid(&prepared.derived_plan, prepared.derived_type)),
                    "{damage}",
                );
                assert_eq!(
                    (
                        derived_state(&prepared.fixture.store, prepared.derived_type, own),
                        prepared.fixture.store.type_len(),
                        prepared.fixture.store.index_info_len(),
                        prepared.fixture.store.checker_link_allocated_lengths(),
                        prepared.fixture.store.relation_state_snapshot(),
                    ),
                    before,
                    "{damage}",
                );
            }
        }
    }

    #[test]
    fn inherited_index_construction_review_rejects_warm_own_property_mismatches() {
        let mut observations = Vec::new();
        for damage in ["value", "optional"] {
            let mut prepared = prepare_inherited_index_property("number", "own: string");
            let own = prepared.derived_plan.properties[0].symbol;
            let string = prepared
                .fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .string_type;
            assert_eq!(
                resolve_direct_interface_members(
                    &mut prepared.fixture.store,
                    &prepared.derived_plan,
                    prepared.derived_type,
                    &[string],
                    &[prepared.base_type],
                ),
                Ok(prepared.derived_type)
            );
            assert_eq!(
                validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type),
                InterfaceHeritageMembersValidation::Valid
            );
            if damage == "value" {
                let mut links = prepared
                    .fixture
                    .store
                    .value_symbol_links(own)
                    .unwrap()
                    .clone();
                links.resolved_type = Some(prepared.number_type);
                assert!(prepared.fixture.store.set_value_symbol_links(own, links));
            } else {
                let record = prepared.fixture.store.symbol(own).unwrap();
                let (flags, checks) = (record.flags(), record.check_flags());
                assert!(prepared.fixture.store.set_symbol_flags(
                    own,
                    flags | SymbolFlags::OPTIONAL,
                    checks
                ));
            }
            let snapshot = |store: &CanonicalTypeMapperStore| {
                (
                    derived_state(store, prepared.derived_type, own),
                    store.symbol(own).unwrap().flags(),
                    store.type_len(),
                    store.index_info_len(),
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                )
            };
            let before = snapshot(&prepared.fixture.store);
            for _ in 0..2 {
                let validation = validate_interface_heritage_members(
                    &prepared.fixture.store,
                    prepared.derived_type,
                );
                let replay = resolve_direct_interface_members(
                    &mut prepared.fixture.store,
                    &prepared.derived_plan,
                    prepared.derived_type,
                    &[string],
                    &[prepared.base_type],
                );
                assert_eq!(snapshot(&prepared.fixture.store), before);
                assert_eq!(
                    replay,
                    Err(invalid(&prepared.derived_plan, prepared.derived_type))
                );
                observations.push((damage, validation));
            }
        }
        assert!(observations.iter().all(|(_, validation)| *validation == InterfaceHeritageMembersValidation::Malformed), "{observations:#?}");
    }

    #[test]
    fn inherited_index_construction_review_rejects_cloned_retained_index_identity() {
        let mut prepared = prepare_inherited_index_property("number", "own: string");
        let own = prepared.derived_plan.properties[0].symbol;
        let string = prepared
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        resolve_direct_interface_members(
            &mut prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
            &[string],
            &[prepared.base_type],
        )
        .unwrap();
        let TypeData::Interface(derived) = prepared
            .fixture
            .store
            .type_payload(prepared.derived_type)
            .unwrap()
            .data()
        else {
            panic!("the derived type remains an interface")
        };
        let structured = &derived.reference.object.structured;
        let (members, properties, inherited) = (
            structured.members,
            structured.properties.clone(),
            structured.index_infos.as_ref().unwrap()[0],
        );
        assert!(derived.declared_index_infos.is_none());
        let info = prepared.fixture.store.index_info(inherited).unwrap();
        let (key, value, readonly, declaration, components, symbol) = (
            info.key_type(),
            info.value_type(),
            info.is_readonly(),
            info.declaration(),
            info.components().to_vec(),
            info.index_symbol(),
        );
        let copied = prepared
            .fixture
            .store
            .alloc_index_info(key, value, readonly, declaration, components)
            .unwrap();
        assert_ne!(copied, inherited);
        assert!(prepared.fixture.store.set_index_info_symbol(copied, symbol));
        assert!(prepared.fixture.store.set_structured_type_members(
            prepared.derived_type,
            members,
            properties,
            None,
            None,
            Some(vec![copied]),
        ));
        let before = (
            derived_state(&prepared.fixture.store, prepared.derived_type, own),
            prepared.fixture.store.type_len(),
            prepared.fixture.store.index_info_len(),
            prepared.fixture.store.checker_link_allocated_lengths(),
            prepared.fixture.store.relation_state_snapshot(),
        );
        for _ in 0..2 {
            assert_eq!(
                validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type),
                InterfaceHeritageMembersValidation::Malformed
            );
            assert_eq!(
                resolve_direct_interface_members(
                    &mut prepared.fixture.store,
                    &prepared.derived_plan,
                    prepared.derived_type,
                    &[string],
                    &[prepared.base_type],
                ),
                Err(invalid(&prepared.derived_plan, prepared.derived_type))
            );
            assert_eq!(
                (
                    derived_state(&prepared.fixture.store, prepared.derived_type, own),
                    prepared.fixture.store.type_len(),
                    prepared.fixture.store.index_info_len(),
                    prepared.fixture.store.checker_link_allocated_lengths(),
                    prepared.fixture.store.relation_state_snapshot(),
                ),
                before
            );
        }
    }

    #[test]
    fn ordinary_property_source_contract_rejects_forged_flags_and_annotation_links() {
        use crate::semantic::TypeNodeLinks;

        for (key, property, damage) in [
            ("number", "own: string", "readonly"),
            ("number", "readonly own: string", "readonly"),
            ("number", "own?: string", "optional"),
            ("number", "own: string", "annotation"),
            ("number", "own: string", "annotation-and-value"),
            ("string", "own: number", "annotation-and-value"),
            ("none", "readonly own: number", "readonly"),
            ("none", "own?: number", "optional"),
            ("none", "own: number", "annotation-and-value"),
        ] {
            let mut prepared = if key == "none" {
                prepare_fixture(fixture_with_source(
                    &format!(
                        "interface Base {{ first: number; second: number }} \
                         interface Other {{ other: number }} \
                         interface Derived extends Base {{ {property} }}",
                    ),
                    32_181,
                ))
            } else {
                prepare_inherited_index_property(key, property)
            };
            let own = prepared.derived_plan.properties[0].symbol;
            let annotation = prepared.derived_plan.properties[0].type_node;
            let type_ =
                object_members::cached_planned_type_identity(&prepared.fixture.store, annotation)
                    .unwrap();
            let other_type = if type_ == prepared.number_type {
                prepared
                    .fixture
                    .store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .string_type
            } else {
                prepared.number_type
            };
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[type_],
                &[prepared.base_type],
            )
            .unwrap();
            assert_eq!(
                validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type),
                InterfaceHeritageMembersValidation::Valid,
                "{key}: {property}",
            );
            let record = prepared.fixture.store.symbol(own).unwrap();
            let (flags, checks) = (record.flags(), record.check_flags());
            match damage {
                "readonly" => {
                    assert!(
                        prepared.fixture.store.set_source_property_readonly(
                            own,
                            !checks.contains(CheckFlags::READONLY),
                        )
                    );
                }
                "optional" => {
                    assert!(prepared.fixture.store.set_symbol_flags(
                        own,
                        flags.without(SymbolFlags::OPTIONAL),
                        checks,
                    ));
                }
                "annotation" | "annotation-and-value" => {
                    assert!(prepared.fixture.store.set_type_node_links(
                        annotation,
                        TypeNodeLinks {
                            resolved_type: Some(other_type),
                            ..TypeNodeLinks::default()
                        },
                    ));
                    if damage == "annotation-and-value" {
                        assert!(prepared.fixture.store.set_value_symbol_links(
                            own,
                            ValueSymbolLinks {
                                resolved_type: Some(other_type),
                                ..ValueSymbolLinks::default()
                            },
                        ));
                    }
                }
                _ => unreachable!(),
            }
            let snapshot = |store: &CanonicalTypeMapperStore| {
                (
                    derived_state(store, prepared.derived_type, own),
                    store.symbol(own).unwrap().flags(),
                    store.symbol(own).unwrap().check_flags(),
                    store.type_node_links(annotation).cloned(),
                    store.type_len(),
                    store.index_info_len(),
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                )
            };
            let before = snapshot(&prepared.fixture.store);
            for _ in 0..2 {
                assert_eq!(
                    validate_interface_heritage_members(
                        &prepared.fixture.store,
                        prepared.derived_type,
                    ),
                    InterfaceHeritageMembersValidation::Malformed,
                    "{key}: {property}: {damage}",
                );
                assert!(
                    validated_interface_property_by_key(
                        &prepared.fixture.store,
                        prepared.derived_type,
                        EscapedNameRef::source("own"),
                        None,
                    )
                    .is_none()
                );
                assert_eq!(snapshot(&prepared.fixture.store), before);
            }
        }
    }

    #[test]
    fn ordinary_property_source_contract_checks_retained_value_provenance() {
        use crate::semantic::{
            CanonicalCheckerDiagnostics, CanonicalCheckerOptions, TypeNodeLinks,
            type_nodes::CanonicalTypeQuery,
        };

        for annotation_source in ["Other", "number | string"] {
            let mut prepared =
                prepare_inherited_index_property("number", &format!("own: {annotation_source}"));
            let own = prepared.derived_plan.properties[0].symbol;
            let annotation = prepared.derived_plan.properties[0].type_node;
            let host = host(
                &prepared.fixture.parsed.arena,
                prepared.fixture.files.get(&prepared.fixture.file).unwrap(),
            );
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let type_ = CanonicalTypeQuery::new(
                &mut prepared.fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(annotation)
            .unwrap();
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[type_],
                &[prepared.base_type],
            )
            .unwrap();
            assert_eq!(
                validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type),
                InterfaceHeritageMembersValidation::Valid,
                "{annotation_source}",
            );
            assert_eq!(
                CanonicalTypeQuery::new(
                    &mut prepared.fixture.store,
                    &host,
                    CanonicalCheckerOptions::default(),
                    &mut diagnostics,
                )
                .unwrap()
                .get_type_of_declared_value(own)
                .unwrap(),
                type_,
            );
            let provenance = prepared
                .fixture
                .store
                .declared_value_provenance(own)
                .unwrap();
            assert!(provenance.is_current(&prepared.fixture.store, own));
            assert_eq!(
                validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type),
                InterfaceHeritageMembersValidation::Valid,
            );
            assert_ne!(type_, prepared.number_type);
            assert!(prepared.fixture.store.set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(prepared.number_type),
                    ..TypeNodeLinks::default()
                },
            ));
            assert!(prepared.fixture.store.set_value_symbol_links(
                own,
                ValueSymbolLinks {
                    resolved_type: Some(prepared.number_type),
                    ..ValueSymbolLinks::default()
                },
            ));
            let snapshot = |store: &CanonicalTypeMapperStore| {
                (
                    derived_state(store, prepared.derived_type, own),
                    store.type_node_links(annotation).cloned(),
                    store.declared_value_provenance(own),
                    store.type_len(),
                    store.index_info_len(),
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                )
            };
            let before = snapshot(&prepared.fixture.store);
            for _ in 0..2 {
                assert_eq!(
                    validate_interface_heritage_members(
                        &prepared.fixture.store,
                        prepared.derived_type,
                    ),
                    InterfaceHeritageMembersValidation::Malformed,
                    "{annotation_source}",
                );
                assert_eq!(snapshot(&prepared.fixture.store), before);
            }
        }
    }

    #[test]
    fn ordinary_property_source_contract_checks_parenthesized_annotations() {
        use crate::semantic::{
            CanonicalCheckerDiagnostics, CanonicalCheckerOptions, TypeNodeLinks,
            type_nodes::CanonicalTypeQuery,
        };

        for annotation_source in ["(string)", "((number))", "(Other)"] {
            let mut prepared =
                prepare_inherited_index_property("number", &format!("own: {annotation_source}"));
            let own = prepared.derived_plan.properties[0].symbol;
            let annotation = prepared.derived_plan.properties[0].type_node;
            let host = host(
                &prepared.fixture.parsed.arena,
                prepared.fixture.files.get(&prepared.fixture.file).unwrap(),
            );
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let type_ = CanonicalTypeQuery::new(
                &mut prepared.fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(annotation)
            .unwrap();
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[type_],
                &[prepared.base_type],
            )
            .unwrap();
            assert!(prepared.fixture.store.type_node_links(annotation).is_none());
            for _ in 0..2 {
                assert_eq!(
                    validate_interface_heritage_members(
                        &prepared.fixture.store,
                        prepared.derived_type,
                    ),
                    InterfaceHeritageMembersValidation::Valid,
                    "{annotation_source}",
                );
            }
            let wrong = prepared
                .fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .boolean_type;
            assert!(prepared.fixture.store.set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(wrong),
                    ..TypeNodeLinks::default()
                },
            ));
            assert!(prepared.fixture.store.set_value_symbol_links(
                own,
                ValueSymbolLinks {
                    resolved_type: Some(wrong),
                    ..ValueSymbolLinks::default()
                },
            ));
            let snapshot = |store: &CanonicalTypeMapperStore| {
                (
                    derived_state(store, prepared.derived_type, own),
                    store.type_node_links(annotation).cloned(),
                    store.type_len(),
                    store.index_info_len(),
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                )
            };
            let before = snapshot(&prepared.fixture.store);
            for _ in 0..2 {
                assert_eq!(
                    validate_interface_heritage_members(
                        &prepared.fixture.store,
                        prepared.derived_type,
                    ),
                    InterfaceHeritageMembersValidation::Malformed,
                    "{annotation_source}",
                );
                assert_eq!(snapshot(&prepared.fixture.store), before);
            }
        }
    }

    #[test]
    fn ordinary_property_source_contract_preserves_unannotated_any() {
        let mut fixture = fixture_with_source("interface Base { own; }", 32_182);
        let owner = interface_symbol(&fixture, "Base");
        let own = fixture
            .store
            .symbol(owner)
            .and_then(|owner| owner.members())
            .and_then(|members| fixture.store.symbol_table(members))
            .and_then(|members| members.get_source("own"))
            .unwrap();
        let (any, number) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.any_type, bootstrap.number_type)
        };
        for (type_, valid) in [(any, true), (number, false)] {
            assert!(fixture.store.set_value_symbol_links(
                own,
                ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                },
            ));
            assert_eq!(valid_property_symbol(&fixture.store, own), valid);
        }
    }

    #[test]
    fn ordinary_property_semantic_review_preserves_unannotated_any_flags() {
        let mut rejected = Vec::new();
        for (member, optional, readonly) in [
            ("own;", false, false),
            ("own?;", true, false),
            ("readonly own;", false, true),
            ("readonly own?;", true, true),
        ] {
            let mut fixture =
                fixture_with_source(&format!("interface Base {{ {member} }}"), 32_186);
            let owner = interface_symbol(&fixture, "Base");
            let own = fixture
                .store
                .symbol(owner)
                .and_then(|owner| owner.members())
                .and_then(|members| fixture.store.symbol_table(members))
                .and_then(|members| members.get_source("own"))
                .unwrap();
            let any = fixture.store.intrinsic_bootstrap().unwrap().any_type;
            assert!(fixture.store.set_source_property_readonly(own, readonly));
            assert!(fixture.store.set_value_symbol_links(
                own,
                ValueSymbolLinks {
                    resolved_type: Some(any),
                    ..ValueSymbolLinks::default()
                },
            ));
            let record = fixture.store.symbol(own).unwrap();
            assert_eq!(record.flags().contains(SymbolFlags::OPTIONAL), optional);
            assert_eq!(
                record.check_flags().contains(CheckFlags::READONLY),
                readonly
            );
            assert!(
                fixture
                    .store
                    .source_direct_type_annotation(record.value_declaration().unwrap(),)
                    .is_none()
            );
            if !valid_property_symbol(&fixture.store, own) {
                rejected.push(member);
            }
        }
        assert!(
            rejected.is_empty(),
            "healthy unannotated properties rejected: {rejected:?}"
        );
    }

    #[test]
    fn ordinary_property_source_contract_rejects_unannotated_cache_changes() {
        for (member, optional, readonly, wrong_type) in [
            ("own;", true, false, false),
            ("own?;", false, false, false),
            ("own;", false, true, false),
            ("readonly own;", false, false, false),
            ("readonly own?;", false, true, false),
            ("readonly own?;", true, false, false),
            ("readonly own?;", true, true, true),
        ] {
            let mut fixture =
                fixture_with_source(&format!("interface Base {{ {member} }}"), 32_187);
            let owner = interface_symbol(&fixture, "Base");
            let own = fixture
                .store
                .symbol(owner)
                .and_then(|owner| owner.members())
                .and_then(|members| fixture.store.symbol_table(members))
                .and_then(|members| members.get_source("own"))
                .unwrap();
            let flags = SymbolFlags::PROPERTY
                | if optional {
                    SymbolFlags::OPTIONAL
                } else {
                    SymbolFlags::NONE
                };
            assert!(fixture.store.set_symbol_flags(own, flags, CheckFlags::NONE));
            assert!(fixture.store.set_source_property_readonly(own, readonly));
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let type_ = if wrong_type {
                bootstrap.number_type
            } else {
                bootstrap.any_type
            };
            assert!(fixture.store.set_value_symbol_links(
                own,
                ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                },
            ));
            let state = |store: &CanonicalTypeMapperStore| {
                (
                    store.symbol(own).unwrap().flags(),
                    store.symbol(own).unwrap().check_flags(),
                    store.value_symbol_links(own).cloned(),
                    store.type_len(),
                    store.symbol_len(),
                    store.index_info_len(),
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                )
            };
            let before = state(&fixture.store);
            for _ in 0..2 {
                assert!(
                    !valid_property_symbol(&fixture.store, own),
                    "{member}: optional={optional}, readonly={readonly}, wrong_type={wrong_type}",
                );
                assert_eq!(state(&fixture.store), before);
            }
        }
    }

    #[test]
    fn merged_interface_bases_preserve_inherited_members_cold_and_warm() {
        let mut prepared = prepare_fixture(fixture_with_source(
            concat!(
                "interface Base { first: number }\n",
                "interface Base { second: number }\n",
                "interface Other { other: number }\n",
                "interface Derived extends Base { own: number }\n",
            ),
            810,
        ));
        let base = interface_symbol(&prepared.fixture, "Base");
        assert_eq!(
            prepared
                .fixture
                .store
                .symbol(base)
                .unwrap()
                .declarations()
                .unwrap()
                .len(),
            2,
        );
        assert!(prepared.fixture.store.set_symbol_flags(
            base,
            SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));

        assert_eq!(
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[prepared.number_type],
                &[prepared.base_type],
            ),
            Ok(prepared.derived_type),
        );

        let TypeData::Interface(derived) = prepared
            .fixture
            .store
            .type_payload(prepared.derived_type)
            .unwrap()
            .data()
        else {
            panic!("the derived interface must retain its interface identity")
        };
        let names = derived
            .reference
            .object
            .structured
            .properties
            .as_deref()
            .unwrap()
            .iter()
            .map(|property| {
                prepared
                    .fixture
                    .store
                    .symbol(*property)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["own", "first", "second"]);
        assert!(validate_planned_interface_heritage_members(
            &prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
        ));
        assert_eq!(
            validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type),
            InterfaceHeritageMembersValidation::Valid,
        );

        let warm = (
            prepared.fixture.store.type_len(),
            prepared.fixture.store.symbol_len(),
            prepared.fixture.store.signature_len(),
            prepared.fixture.store.symbol_store().symbol_table_len(),
            prepared.fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[prepared.number_type],
                &[prepared.base_type],
            ),
            Ok(prepared.derived_type),
        );
        assert_eq!(
            (
                prepared.fixture.store.type_len(),
                prepared.fixture.store.symbol_len(),
                prepared.fixture.store.signature_len(),
                prepared.fixture.store.symbol_store().symbol_table_len(),
                prepared.fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn invalid_merged_interface_base_flags_fail_without_publication() {
        for flags in [
            SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT | SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            SymbolFlags::INTERFACE | SymbolFlags::PROPERTY,
            SymbolFlags::TRANSIENT,
        ] {
            let mut prepared = prepare();
            let base = interface_symbol(&prepared.fixture, "Base");
            let own = prepared.derived_plan.properties[0].symbol;
            assert!(
                prepared
                    .fixture
                    .store
                    .set_symbol_flags(base, flags, CheckFlags::NONE)
            );
            let before = (
                derived_state(&prepared.fixture.store, prepared.derived_type, own),
                prepared.fixture.store.type_len(),
                prepared.fixture.store.symbol_len(),
                prepared.fixture.store.signature_len(),
                prepared.fixture.store.checker_link_allocated_lengths(),
            );

            assert!(matches!(
                resolve_direct_interface_members(
                    &mut prepared.fixture.store,
                    &prepared.derived_plan,
                    prepared.derived_type,
                    &[prepared.number_type],
                    &[prepared.base_type],
                ),
                Err(PropertyObjectError::InvalidCachedInterface { symbol, type_ })
                    if symbol == prepared.derived_plan.symbol && type_ == prepared.derived_type
            ));
            assert_eq!(
                (
                    derived_state(&prepared.fixture.store, prepared.derived_type, own),
                    prepared.fixture.store.type_len(),
                    prepared.fixture.store.symbol_len(),
                    prepared.fixture.store.signature_len(),
                    prepared.fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn transitive_interface_bases_preserve_diamond_order_and_reject_warm_poison() {
        let mut fixture = fixture_with_source(
            concat!(
                "interface Root { shared: number }\n",
                "interface Left extends Root { left: number }\n",
                "interface Right extends Root { right: number }\n",
                "interface Leaf extends Left, Right { own: number }\n",
            ),
            806,
        );
        let root = interface_symbol(&fixture, "Root");
        let left = interface_symbol(&fixture, "Left");
        let right = interface_symbol(&fixture, "Right");
        let leaf = interface_symbol(&fixture, "Leaf");
        let host = host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let root_plan = object_members::plan_interface(&fixture.store, &host, root).unwrap();
        let left_plan = object_members::plan_interface(&fixture.store, &host, left).unwrap();
        let right_plan = object_members::plan_interface(&fixture.store, &host, right).unwrap();
        let leaf_plan = indexed_derived_plan(&fixture, &host, leaf, &root_plan);
        let mut types = Vec::new();
        for symbol in [root, left, right, leaf] {
            let flags = fixture.store.symbol(symbol).unwrap().flags();
            types.push(
                get_declared_class_interface_or_type_parameter(
                    &mut fixture.store,
                    &host,
                    symbol,
                    flags,
                )
                .unwrap()
                .unwrap(),
            );
        }
        let [root_type, left_type, right_type, leaf_type] = types.as_slice() else {
            panic!("the diamond fixture must retain four interface identities")
        };
        let (root_type, left_type, right_type, leaf_type) =
            (*root_type, *left_type, *right_type, *leaf_type);
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let root_state =
            object_members::interface_state(&fixture.store, &root_plan, root_type).unwrap();
        object_members::publish_declared_members(
            &mut fixture.store,
            &root_plan,
            root_state,
            &[number],
            &[],
            &[],
        )
        .unwrap();
        for (plan, type_) in [(&left_plan, left_type), (&right_plan, right_type)] {
            resolve_direct_interface_members(
                &mut fixture.store,
                plan,
                type_,
                &[number],
                &[root_type],
            )
            .unwrap();
        }
        assert_eq!(
            resolve_direct_interface_members(
                &mut fixture.store,
                &leaf_plan,
                leaf_type,
                &[number],
                &[left_type, right_type],
            ),
            Ok(leaf_type)
        );
        let (members, properties) = {
            let TypeData::Interface(interface) =
                fixture.store.type_payload(leaf_type).unwrap().data()
            else {
                panic!("the leaf must retain its interface identity")
            };
            let properties = interface
                .reference
                .object
                .structured
                .properties
                .as_ref()
                .unwrap();
            let names = properties
                .iter()
                .map(|symbol| {
                    fixture
                        .store
                        .symbol(*symbol)
                        .unwrap()
                        .name()
                        .as_utf8()
                        .unwrap()
                })
                .collect::<Vec<_>>();
            assert_eq!(names, ["own", "left", "shared", "right"]);
            assert_eq!(
                interface.resolved_base_types.as_deref(),
                Some([left_type, right_type].as_slice())
            );
            (
                interface.reference.object.structured.members,
                properties.clone(),
            )
        };
        assert_eq!(
            validate_interface_heritage_members(&fixture.store, leaf_type),
            InterfaceHeritageMembersValidation::Valid
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            resolve_direct_interface_members(
                &mut fixture.store,
                &leaf_plan,
                leaf_type,
                &[number],
                &[left_type, right_type],
            ),
            Ok(leaf_type)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm
        );
        let mut reordered = properties;
        reordered.swap(1, 3);
        assert!(fixture.store.set_structured_type_members(
            leaf_type,
            members,
            Some(reordered),
            None,
            None,
            None,
        ));
        assert_eq!(
            validate_interface_heritage_members(&fixture.store, leaf_type),
            InterfaceHeritageMembersValidation::Malformed
        );
    }

    #[test]
    fn poisoned_inherited_indexes_fail_without_republishing_members() {
        let mut prepared = prepare_indexed();
        resolve_direct_interface_members(
            &mut prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
            &[prepared.number_type],
            &[prepared.base_type],
        )
        .unwrap();
        let (members, properties, index) = {
            let TypeData::Interface(interface) = prepared
                .fixture
                .store
                .type_payload(prepared.derived_type)
                .unwrap()
                .data()
            else {
                panic!("the derived interface must retain its interface type")
            };
            (
                interface.reference.object.structured.members,
                interface.reference.object.structured.properties.clone(),
                interface
                    .reference
                    .object
                    .structured
                    .index_infos
                    .as_ref()
                    .unwrap()[0],
            )
        };
        assert!(prepared.fixture.store.set_structured_type_members(
            prepared.derived_type,
            members,
            properties.clone(),
            None,
            None,
            None,
        ));
        let before = derived_state(
            &prepared.fixture.store,
            prepared.derived_type,
            prepared.derived_plan.properties[0].symbol,
        );
        assert_eq!(
            validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type),
            InterfaceHeritageMembersValidation::Malformed,
        );
        assert!(
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[prepared.number_type],
                &[prepared.base_type],
            )
            .is_err()
        );
        assert_eq!(
            derived_state(
                &prepared.fixture.store,
                prepared.derived_type,
                prepared.derived_plan.properties[0].symbol,
            ),
            before
        );

        assert!(prepared.fixture.store.set_structured_type_members(
            prepared.derived_type,
            members,
            properties,
            None,
            None,
            Some(vec![index]),
        ));
        let own = prepared.derived_plan.properties[0].symbol;
        assert!(
            prepared
                .fixture
                .store
                .set_index_info_symbol(index, Some(own))
        );
        assert_eq!(
            validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type),
            InterfaceHeritageMembersValidation::Malformed,
        );
    }

    fn derived_state(
        store: &CanonicalTypeMapperStore,
        type_: TypeId,
        own_property: SemanticSymbolId,
    ) -> (
        ObjectFlags,
        InterfaceTypeData,
        Option<ValueSymbolLinks>,
        usize,
    ) {
        let record = store.type_payload(type_).unwrap();
        let TypeData::Interface(interface) = record.data() else {
            panic!("expected interface")
        };
        (
            record.object_flags(),
            interface.clone(),
            store.value_symbol_links(own_property).cloned(),
            store.symbol_store().symbol_table_len(),
        )
    }

    fn property_wrapper(store: &mut CanonicalTypeMapperStore, property_type: TypeId) -> TypeId {
        let property = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source("value"),
            ))
            .unwrap();
        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(property_type),
                ..ValueSymbolLinks::default()
            },
        ));
        let members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(members, EscapedName::source("value"), property),
            Some(None),
        );
        let wrapper = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            wrapper,
            Some(members),
            Some(vec![property]),
            None,
            None,
            None,
        ));
        wrapper
    }

    #[test]
    fn foreign_base_is_rejected_without_partial_publication() {
        let mut prepared = prepare();
        let own = prepared.derived_plan.properties[0].symbol;
        let before = derived_state(&prepared.fixture.store, prepared.derived_type, own);
        let mut foreign = CanonicalTypeMapperStore::new();
        let foreign_type = foreign
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap()
            .any_type;

        assert!(matches!(
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[prepared.number_type],
                &[foreign_type],
            ),
            Err(PropertyObjectError::InvalidCachedInterface { symbol, type_ })
                if symbol == prepared.derived_plan.symbol && type_ == prepared.derived_type
        ));
        assert_eq!(
            derived_state(&prepared.fixture.store, prepared.derived_type, own),
            before
        );
    }

    #[test]
    fn cold_base_cache_poison_is_rejected_without_partial_publication() {
        let mut prepared = prepare();
        let own = prepared.derived_plan.properties[0].symbol;
        assert!(prepared.fixture.store.set_interface_base_resolution(
            prepared.derived_type,
            true,
            None,
            None,
        ));
        let poisoned = derived_state(&prepared.fixture.store, prepared.derived_type, own);

        assert!(
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[prepared.number_type],
                &[prepared.base_type],
            )
            .is_err()
        );
        assert_eq!(
            derived_state(&prepared.fixture.store, prepared.derived_type, own),
            poisoned,
        );
    }

    #[test]
    fn malformed_override_is_rejected_before_relation_cache_or_member_publication() {
        let mut prepared = prepare();
        let own = prepared.derived_plan.properties[0].symbol;
        let base_first = {
            let record = prepared
                .fixture
                .store
                .type_payload(prepared.base_type)
                .unwrap();
            let TypeData::Interface(interface) = record.data() else {
                panic!("base must retain its interface payload")
            };
            interface
                .reference
                .object
                .structured
                .properties
                .as_ref()
                .unwrap()[0]
        };
        let base_property_type =
            property_wrapper(&mut prepared.fixture.store, prepared.number_type);
        let own_property_type = property_wrapper(&mut prepared.fixture.store, prepared.number_type);
        assert!(prepared.fixture.store.set_value_symbol_links(
            base_first,
            ValueSymbolLinks {
                resolved_type: Some(base_property_type),
                ..ValueSymbolLinks::default()
            },
        ));
        prepared.derived_plan.properties[0].name = EscapedName::source("first");
        let before = (
            derived_state(&prepared.fixture.store, prepared.derived_type, own),
            prepared.fixture.store.relation_state_snapshot(),
        );

        assert!(
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[own_property_type],
                &[prepared.base_type],
            )
            .is_err()
        );
        assert_eq!(
            (
                derived_state(&prepared.fixture.store, prepared.derived_type, own),
                prepared.fixture.store.relation_state_snapshot(),
            ),
            before
        );
    }

    #[test]
    fn warmed_wrapper_relation_rejects_nested_heritage_poison() {
        let mut prepared = prepare();
        resolve_direct_interface_members(
            &mut prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
            &[prepared.number_type],
            &[prepared.base_type],
        )
        .unwrap();
        let source = property_wrapper(&mut prepared.fixture.store, prepared.derived_type);
        let target = property_wrapper(&mut prepared.fixture.store, prepared.base_type);
        let before_warm = prepared.fixture.store.relation_state_snapshot();
        assert_eq!(
            prepared.fixture.store.is_type_assignable_to(source, target),
            Ok(true),
        );
        let warmed = prepared.fixture.store.relation_state_snapshot();
        assert!(warmed.assignable.entries > before_warm.assignable.entries);
        let wrapper_key = prepared
            .fixture
            .store
            .relation_key_if_available(source, target, IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        assert!(
            prepared
                .fixture
                .store
                .relation_cache_get(RelationKind::Assignable, wrapper_key)
                .intersects(RelationComparisonResult::SUCCEEDED)
        );

        assert!(prepared.fixture.store.set_interface_base_resolution(
            prepared.derived_type,
            true,
            None,
            None,
        ));
        assert_eq!(
            prepared
                .fixture
                .store
                .relation_cache_get(RelationKind::Assignable, wrapper_key),
            RelationComparisonResult::NONE,
        );
        assert_eq!(
            prepared.fixture.store.is_type_assignable_to(source, target),
            Err(RelationUnavailable::InvalidStructuredMembers(
                prepared.derived_type
            )),
        );
        assert_eq!(prepared.fixture.store.relation_state_snapshot(), warmed);
    }

    #[test]
    fn inherited_base_cycles_fail_without_unbounded_recursive_validation() {
        let mut prepared = prepare();
        resolve_direct_interface_members(
            &mut prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
            &[prepared.number_type],
            &[prepared.base_type],
        )
        .unwrap();
        let base_owner = prepared
            .fixture
            .store
            .type_payload(prepared.base_type)
            .unwrap()
            .symbol()
            .unwrap();
        assert!(
            prepared
                .fixture
                .store
                .try_reserve_direct_interface_heritage_provenance(1)
        );
        assert!(
            prepared
                .fixture
                .store
                .publish_direct_interface_heritage_provenance(
                    prepared.base_type,
                    DirectInterfaceHeritageProvenance {
                        owner_symbol: base_owner,
                        base_symbol: prepared.derived_plan.symbol,
                        base_type: prepared.derived_type,
                        second_base: None,
                    },
                )
        );
        assert!(prepared.fixture.store.set_interface_base_resolution(
            prepared.base_type,
            true,
            None,
            Some(vec![prepared.derived_type]),
        ));

        assert_eq!(
            validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type),
            InterfaceHeritageMembersValidation::Malformed,
        );
        assert_eq!(
            validate_interface_heritage_members(&prepared.fixture.store, prepared.base_type),
            InterfaceHeritageMembersValidation::Malformed,
        );
    }

    #[test]
    fn warm_validation_rejects_missing_wrong_base_reorder_and_omission() {
        let mut prepared = prepare();
        resolve_direct_interface_members(
            &mut prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
            &[prepared.number_type],
            &[prepared.base_type],
        )
        .unwrap();
        assert!(validate_planned_interface_heritage_members(
            &prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
        ));
        let relation_state_before_warm = prepared.fixture.store.relation_state_snapshot();
        assert_eq!(
            prepared
                .fixture
                .store
                .is_type_assignable_to(prepared.derived_type, prepared.base_type),
            Ok(true),
        );
        let warmed_relation_state = prepared.fixture.store.relation_state_snapshot();
        assert!(
            warmed_relation_state.assignable.entries
                > relation_state_before_warm.assignable.entries
        );

        assert!(prepared.fixture.store.set_interface_base_resolution(
            prepared.derived_type,
            true,
            None,
            None,
        ));
        assert_eq!(
            validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type,),
            InterfaceHeritageMembersValidation::Malformed,
        );
        assert!(!validate_planned_interface_heritage_members(
            &prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
        ));
        assert_eq!(
            prepared
                .fixture
                .store
                .is_type_assignable_to(prepared.derived_type, prepared.base_type),
            Err(RelationUnavailable::InvalidStructuredMembers(
                prepared.derived_type
            )),
        );
        assert_eq!(
            prepared.fixture.store.relation_state_snapshot(),
            warmed_relation_state,
        );
        let missing_base = derived_state(
            &prepared.fixture.store,
            prepared.derived_type,
            prepared.derived_plan.properties[0].symbol,
        );
        assert!(
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[prepared.number_type],
                &[prepared.base_type],
            )
            .is_err()
        );
        assert_eq!(
            derived_state(
                &prepared.fixture.store,
                prepared.derived_type,
                prepared.derived_plan.properties[0].symbol,
            ),
            missing_base,
        );
        assert!(prepared.fixture.store.set_interface_base_resolution(
            prepared.derived_type,
            true,
            None,
            Some(vec![prepared.base_type]),
        ));
        assert!(validate_planned_interface_heritage_members(
            &prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
        ));

        let record = prepared
            .fixture
            .store
            .type_payload(prepared.derived_type)
            .unwrap();
        let TypeData::Interface(interface) = record.data() else {
            unreachable!()
        };
        let members = interface.reference.object.structured.members;
        let properties = interface
            .reference
            .object
            .structured
            .properties
            .clone()
            .unwrap();
        let [own, first, second] = properties.as_slice() else {
            panic!("expected one own and two base properties")
        };
        let (own, first, second) = (*own, *first, *second);
        let TypeData::Interface(other_interface) = prepared
            .fixture
            .store
            .type_payload(prepared.other_type)
            .unwrap()
            .data()
        else {
            unreachable!()
        };
        let [other] = other_interface
            .reference
            .object
            .structured
            .properties
            .as_deref()
            .unwrap()
        else {
            panic!("expected one property on the alternate base")
        };
        let other = *other;
        let wrong_base_members = prepared.fixture.store.alloc_symbol_table();
        for property in [own, other] {
            let name = prepared
                .fixture
                .store
                .symbol(property)
                .unwrap()
                .name()
                .to_owned();
            assert_eq!(
                prepared
                    .fixture
                    .store
                    .insert_symbol(wrong_base_members, name, property),
                Some(None)
            );
        }

        assert!(prepared.fixture.store.set_interface_base_resolution(
            prepared.derived_type,
            true,
            None,
            Some(vec![prepared.other_type]),
        ));
        assert!(prepared.fixture.store.set_structured_type_members(
            prepared.derived_type,
            Some(wrong_base_members),
            Some(vec![own, other]),
            None,
            None,
            None,
        ));
        assert_eq!(
            validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type,),
            InterfaceHeritageMembersValidation::Malformed,
        );
        assert!(!validate_planned_interface_heritage_members(
            &prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
        ));
        assert_eq!(
            prepared
                .fixture
                .store
                .is_type_assignable_to(prepared.derived_type, prepared.base_type),
            Err(RelationUnavailable::InvalidStructuredMembers(
                prepared.derived_type
            )),
        );
        assert_eq!(
            prepared.fixture.store.relation_state_snapshot(),
            warmed_relation_state,
        );
        let wrong_base = derived_state(&prepared.fixture.store, prepared.derived_type, own);
        assert!(
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[prepared.number_type],
                &[prepared.base_type],
            )
            .is_err()
        );
        assert_eq!(
            derived_state(&prepared.fixture.store, prepared.derived_type, own),
            wrong_base,
        );

        assert!(prepared.fixture.store.set_interface_base_resolution(
            prepared.derived_type,
            true,
            None,
            Some(vec![prepared.base_type]),
        ));
        assert!(prepared.fixture.store.set_structured_type_members(
            prepared.derived_type,
            members,
            Some(vec![first, own, second]),
            None,
            None,
            None,
        ));
        let poisoned = derived_state(&prepared.fixture.store, prepared.derived_type, own);
        assert!(!validate_planned_interface_heritage_members(
            &prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
        ));
        assert!(
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[prepared.number_type],
                &[prepared.base_type],
            )
            .is_err()
        );
        assert_eq!(
            derived_state(&prepared.fixture.store, prepared.derived_type, own),
            poisoned
        );

        let omitted_members = prepared.fixture.store.alloc_symbol_table();
        for property in [own, first] {
            let name = prepared
                .fixture
                .store
                .symbol(property)
                .unwrap()
                .name()
                .to_owned();
            assert_eq!(
                prepared
                    .fixture
                    .store
                    .insert_symbol(omitted_members, name, property),
                Some(None)
            );
        }
        assert!(prepared.fixture.store.set_structured_type_members(
            prepared.derived_type,
            Some(omitted_members),
            Some(vec![own, first]),
            None,
            None,
            None,
        ));
        assert_eq!(
            validate_interface_heritage_members(&prepared.fixture.store, prepared.derived_type,),
            InterfaceHeritageMembersValidation::Malformed
        );
        assert!(!validate_planned_interface_heritage_members(
            &prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
        ));
    }
}
