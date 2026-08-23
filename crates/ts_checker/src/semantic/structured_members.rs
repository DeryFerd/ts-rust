//! Structured-member publication for direct, nongeneric interface bases.
//!
//! One or two direct bases preserve declaration and source-base order. A
//! single base can also provide its authenticated declared index signatures.
//! Shared base properties or methods must have identical types and modifiers.
//! Compatible derived members replace inherited members; incompatible
//! overrides remain unsupported until TS2430 is ported.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId,
    semantic::PreparedSymbolTable,
};

use super::{
    CanonicalTypeMapperStore, IndexInfoId, TypeId,
    links::ValueSymbolLinks,
    object_members::{
        DirectInterfaceDeclaredState, PropertyObjectError, PropertyObjectKind, PropertyObjectPlan,
        prepare_direct_interface_declared_properties,
        publish_prepared_direct_interface_declared_properties,
    },
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
}

struct ValidatedDeclaredMembers {
    properties: Vec<SemanticSymbolId>,
    index_symbol: Option<SemanticSymbolId>,
    index_infos: Vec<IndexInfoId>,
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
    first_record.name() == second_record.name()
        && first_record.flags() == second_record.flags()
        && first_record.check_flags() == second_record.check_flags()
        && first_type == second_type
}

/// Resolves and publishes one or two direct interface bases.
///
/// `base_types` must match the canonical symbols retained by the syntax plan.
/// Each base must be a fully resolved, nongeneric interface. One direct base
/// may also provide authenticated index signatures.
/// All allocations and sparse-link slots are staged before semantic mutation.
pub(super) fn resolve_direct_interface_members(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
    property_types: &[TypeId],
    base_types: &[TypeId],
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
        if base_record.symbol() != Some(planned.symbol) {
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
        if second_base.is_some() && inherited_base {
            return Err(PropertyObjectError::UnsupportedMember {
                node: planned.node,
                kind: SyntaxKind::ExpressionWithTypeArguments,
            });
        }
        let surface = if inherited_base {
            validate_direct_heritage_property_interface(store, base)
        } else {
            validate_no_heritage_property_interface(store, base)
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
    if !plan.properties.is_empty()
        && inherited_index_infos.iter().any(|index| {
            let Some(info) = store.index_info(*index) else {
                return true;
            };
            let Some(bootstrap) = store.intrinsic_bootstrap() else {
                return true;
            };
            info.key_type() != bootstrap.string_type
                || plan
                    .properties
                    .iter()
                    .zip(property_types)
                    .any(|(property, type_)| property.optional || *type_ != info.value_type())
        })
    {
        return Err(PropertyObjectError::UnsupportedMember {
            node: plan.node,
            kind: SyntaxKind::InterfaceDeclaration,
        });
    }

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

    for property in &plan.properties {
        let record = store
            .symbol(property.symbol)
            .ok_or_else(|| invalid(plan, type_))?;
        if record.name().as_utf8() != Some(property.name.as_str())
            || record.parent() != Some(plan.symbol)
        {
            return Err(invalid(plan, type_));
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
            .get(&EscapedName::source(&property.name))
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
        if property.optional && !base_optional
            || store.is_type_assignable_to(own_type, base_type) != Ok(true)
        {
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
            || !validate_planned_interface_heritage_members(store, plan, type_)
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

/// Plan-aware warm-cache proof used by contextual typing and diagnostics.
///
/// In addition to exact final member reconstruction, this verifies that the
/// cached base types and canonical symbols exactly match the syntax plan.
pub(super) fn validate_planned_interface_heritage_members(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
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
        || heritage.bases.iter().zip(base_types).any(|(base, type_)| {
            store
                .type_payload(*type_)
                .and_then(super::type_records::TypeRecord::symbol)
                != Some(base.symbol)
        })
    {
        return false;
    }
    let Some(surface) = validate_direct_heritage_property_interface(store, type_) else {
        return false;
    };
    let planned_properties = plan
        .properties
        .iter()
        .map(|property| property.symbol)
        .collect::<Vec<_>>();
    surface.owner == plan.symbol
        && surface.declared_properties == planned_properties
        && plan.properties.iter().all(|property| {
            store.symbol(property.symbol).is_some_and(|record| {
                record.check_flags()
                    == if property.readonly {
                        CheckFlags::READONLY
                    } else {
                        CheckFlags::NONE
                    }
            })
        })
}

/// Semantic-only exact proof consumed by structural relations.
pub(super) fn validate_interface_heritage_members(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
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
    if validate_direct_heritage_property_interface(store, type_).is_some() {
        InterfaceHeritageMembersValidation::Valid
    } else {
        InterfaceHeritageMembersValidation::Malformed
    }
}

fn validate_no_heritage_property_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<ValidatedInterfaceSurface> {
    validate_property_interface(store, type_, false)
}

fn validate_direct_heritage_property_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<ValidatedInterfaceSurface> {
    validate_property_interface(store, type_, true)
}

fn validate_property_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    requires_direct_base: bool,
) -> Option<ValidatedInterfaceSurface> {
    validate_property_interface_worker(store, type_, requires_direct_base, &mut HashSet::new())
}

fn validate_property_interface_worker(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    requires_direct_base: bool,
    active: &mut HashSet<TypeId>,
) -> Option<ValidatedInterfaceSurface> {
    if !active.insert(type_) {
        return None;
    }
    let record = store.type_payload(type_)?;
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
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
        || record.alias().is_some()
        || owner_record.flags() != SymbolFlags::INTERFACE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.value_declaration().is_some()
        || owner_record.members() != interface.declared_members
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || owner_declarations.iter().any(|declaration| {
            store.source_node_kind(*declaration) != Some(SyntaxKind::InterfaceDeclaration)
        })
        || store
            .declared_type_links(owner)
            .is_none_or(|links| links.declared_type != Some(type_))
        || !valid_thisless_interface_identity(interface)
        || !interface.base_types_resolved
        || !interface.declared_members_resolved
        || interface.resolved_base_constructor_type.is_some()
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
    {
        return None;
    }
    let structured = &interface.reference.object.structured;
    if structured.constrained != ConstrainedTypeData::default()
        || structured.call_signature_count != 0
        || structured.signatures.is_some()
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
        interface.declared_members,
        interface.declared_index_infos.as_deref(),
    )?;
    if requires_direct_base && !declared.index_infos.is_empty() {
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
    let mut inherited_by_name = HashMap::new();
    for (index, base_type) in base_types.iter().copied().enumerate() {
        let inherited_base = store
            .direct_interface_heritage_provenance(base_type)
            .is_some();
        if base_types.len() == 2 && inherited_base {
            return None;
        }
        let base = validate_property_interface_worker(store, base_type, inherited_base, active)?;
        let expected_owner = if index == 0 {
            heritage_provenance.base_symbol
        } else {
            heritage_provenance.second_base?.0
        };
        if base.owner != expected_owner || base_types.len() == 2 && !base.index_infos.is_empty() {
            return None;
        }
        inherited_index_infos.extend_from_slice(&base.index_infos);
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
    if !declared.properties.is_empty()
        && inherited_index_infos.iter().any(|index| {
            let Some(info) = store.index_info(*index) else {
                return true;
            };
            let Some(bootstrap) = store.intrinsic_bootstrap() else {
                return true;
            };
            info.key_type() != bootstrap.string_type
                || declared.properties.iter().any(|property| {
                    store
                        .symbol(*property)
                        .is_none_or(|record| record.flags().contains(SymbolFlags::OPTIONAL))
                        || store
                            .value_symbol_links(*property)
                            .and_then(|links| links.resolved_type)
                            != Some(info.value_type())
                })
        })
    {
        return None;
    }
    let expected_index_infos = if requires_direct_base {
        inherited_index_infos
    } else {
        declared.index_infos
    };
    let actual = structured.properties.as_deref().unwrap_or_default();
    if actual.is_empty() != structured.properties.is_none()
        || actual != expected.as_slice()
        || structured.index_infos.as_deref()
            != (!expected_index_infos.is_empty()).then_some(expected_index_infos.as_slice())
        || !exact_property_table(
            store,
            &expected,
            structured.members,
            if requires_direct_base {
                None
            } else {
                declared.index_symbol
            },
        )
    {
        return None;
    }
    let result = ValidatedInterfaceSurface {
        owner,
        declared_properties: declared.properties,
        properties: expected,
        index_infos: expected_index_infos,
    };
    assert!(active.remove(&type_));
    Some(result)
}

fn declared_members(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declarations: &[NodeRef],
    members: Option<SymbolTableId>,
    indexes: Option<&[IndexInfoId]>,
) -> Option<ValidatedDeclaredMembers> {
    let Some(members) = members else {
        return indexes.is_none().then_some(ValidatedDeclaredMembers {
            properties: Vec::new(),
            index_symbol: None,
            index_infos: Vec::new(),
        });
    };
    let table = store.symbol_table(members)?;
    if table.is_empty() {
        return None;
    }
    let mut properties = Vec::with_capacity(table.len());
    let mut seen_declarations = HashSet::with_capacity(table.len());
    let mut index_symbol = None;
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
    if index_symbol.is_some() != indexes.is_some() || indexes.is_some_and(<[IndexInfoId]>::is_empty)
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
    })
}

fn valid_index_symbol(
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
        || record.parent() != Some(owner)
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
    let expected_flags = if method {
        SymbolFlags::METHOD
    } else {
        SymbolFlags::PROPERTY
    } | if record.flags().contains(SymbolFlags::OPTIONAL) {
        SymbolFlags::OPTIONAL
    } else {
        SymbolFlags::NONE
    };
    record.flags() == expected_flags
        && if method {
            record.check_flags() == CheckFlags::NONE
        } else {
            record.check_flags().bits() & !CheckFlags::READONLY.bits() == 0
        }
        && record
            .value_declaration()
            .is_some_and(|declaration| declarations.contains(&declaration))
        && record.members().is_none()
        && record.exports().is_none()
        && record.parent().is_some()
        && record.export_symbol().is_none()
        && store.get_merged_symbol(property) == Some(property)
        && declarations.iter().all(|declaration| {
            if method {
                store.source_node_kind(*declaration) == Some(SyntaxKind::MethodSignature)
            } else {
                matches!(
                    store.source_node_kind(*declaration),
                    Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
                )
            }
        })
        && store.value_symbol_links(property).is_some_and(|links| {
            let Some(type_) = links.resolved_type else {
                return false;
            };
            links
                == &ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                }
                && store.type_payload(type_).is_some()
        })
}

fn exact_property_table(
    store: &CanonicalTypeMapperStore,
    properties: &[SemanticSymbolId],
    members: Option<SymbolTableId>,
    index_symbol: Option<SemanticSymbolId>,
) -> bool {
    if properties.is_empty() && index_symbol.is_none() {
        return members.is_none();
    }
    let Some(table) = members.and_then(|members| store.symbol_table(members)) else {
        return false;
    };
    table.len()
        == properties
            .len()
            .saturating_add(usize::from(index_symbol.is_some()))
        && properties.iter().all(|property| {
            store
                .symbol(*property)
                .is_some_and(|record| table.get(record.name()) == Some(*property))
        })
        && table.get(InternalSymbolName::Index.as_ref()) == index_symbol
        && table
            .iter()
            .all(|(_, property)| properties.contains(&property) || index_symbol == Some(property))
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

    fn prepare() -> PreparedFixture {
        prepare_fixture(fixture())
    }

    fn prepare_indexed() -> PreparedFixture {
        prepare_fixture(fixture_with_source(INDEXED_SOURCE, 802))
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
        let [property_node] = interface.members.nodes.as_slice() else {
            panic!("the derived interface has one source property")
        };
        let property_declaration =
            NodeRef::new(declaration.arena, declaration.file, *property_node);
        let (property_name, property_type, postfix_token, modifiers) = match &fixture
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
                property.modifiers.as_ref(),
            ),
            NodeData::PropertySignatureDeclaration(property) => (
                property.name,
                property.type_,
                property.postfix_token,
                property.modifiers.as_ref(),
            ),
            _ => panic!("the derived source member must be an interface property"),
        };
        assert!(postfix_token.is_none());
        assert!(modifiers.is_none());
        let name_node = NodeRef::new(declaration.arena, declaration.file, property_name);
        let NodeData::Identifier(name) = &fixture.parsed.arena.get(name_node.node).unwrap().data
        else {
            panic!("the derived source property has an identifier name")
        };
        let bound = fixture.files.get(&fixture.file).unwrap();
        let property_symbol = bound.symbol(property_declaration).unwrap();
        assert_eq!(
            fixture.store.get_merged_symbol(property_symbol),
            Some(property_symbol)
        );
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
        plan.properties = vec![PlannedProperty {
            declaration: property_declaration,
            symbol: property_symbol,
            name_node,
            type_node: NodeRef::new(declaration.arena, declaration.file, property_type),
            optional: false,
            readonly: false,
            name: name.text.clone(),
        }];
        plan.spreads.clear();
        plan.indexes.clear();
        plan.call_signatures.clear();
        plan.alias_symbol = None;
        plan.heritage = Some(heritage);
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
            let indexes = vec![(string_type, number_type); plan.indexes.len()];
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
        prepared.derived_plan.properties[0].name = "first".to_owned();
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
