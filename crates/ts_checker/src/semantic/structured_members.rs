//! Structured-member publication for direct, nongeneric interface heritage.
//!
//! The declared-own half remains in [`super::object_members`]. This module
//! validates every resolved base, applies upstream's own-first/left-to-right
//! property merge, and publishes the base and final structured caches as one
//! dependency-closed transition.

use std::collections::HashSet;

use ts_ast::SyntaxKind;
use ts_binder::{
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags, semantic::PreparedSymbolTable,
};

use super::{
    CanonicalTypeMapperStore, TypeId,
    links::ValueSymbolLinks,
    object_members::{
        DirectInterfaceDeclaredState, PropertyObjectError, PropertyObjectKind, PropertyObjectPlan,
        prepare_direct_interface_declared_properties,
        publish_prepared_direct_interface_declared_properties,
    },
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
    properties: Vec<SemanticSymbolId>,
    ancestry: HashSet<SemanticSymbolId>,
}

fn invalid(plan: &PropertyObjectPlan, type_: TypeId) -> PropertyObjectError {
    PropertyObjectError::InvalidCachedInterface {
        symbol: plan.symbol,
        type_,
    }
}

/// Resolves and publishes the first direct interface-heritage capability.
///
/// `base_types` must correspond one-for-one with the symbols retained by the
/// syntax plan. Each base must already expose a fully resolved property-only
/// interface surface. Generic instantiation, signatures, and index infos stay
/// typed boundaries rather than silently dropping members.
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
    if plan.kind != PropertyObjectKind::Interface
        || heritage.bases.is_empty()
        || heritage.bases.len() != base_types.len()
        || !plan.indexes.is_empty()
        || !plan.call_signatures.is_empty()
    {
        return Err(invalid(plan, type_));
    }

    let declared_state =
        prepare_direct_interface_declared_properties(store, plan, type_, property_types)?;
    let mut expected_properties = Vec::new();
    let mut expected_entries = Vec::new();
    let mut seen_names = HashSet::new();
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

    let mut seen_base_types = HashSet::with_capacity(base_types.len());
    for (planned, base_type) in heritage.bases.iter().zip(base_types) {
        if !seen_base_types.insert(*base_type) {
            return Err(invalid(plan, type_));
        }
        let base_record = store
            .type_payload(*base_type)
            .ok_or_else(|| invalid(plan, type_))?;
        if base_record.symbol() != Some(planned.symbol) {
            return Err(invalid(plan, type_));
        }
        if base_record
            .data()
            .structured()
            .is_some_and(|structured| {
                structured.call_signature_count != 0
                    || structured.signatures.as_ref().is_some_and(|set| !set.is_empty())
                    || structured
                        .index_infos
                        .as_ref()
                        .is_some_and(|set| !set.is_empty())
            })
        {
            return Err(PropertyObjectError::UnsupportedMember {
                node: planned.node,
                kind: SyntaxKind::ExpressionWithTypeArguments,
            });
        }
        let surface = validate_resolved_property_interface(store, *base_type)
            .ok_or_else(|| invalid(plan, type_))?;
        for property in surface.properties {
            let property_record = store.symbol(property).ok_or_else(|| invalid(plan, type_))?;
            let name = property_record.name().to_owned();
            if seen_names.insert(name.clone()) {
                expected_entries.push((name, property));
                expected_properties.push(property);
            }
        }
    }

    if declared_state == DirectInterfaceDeclaredState::Resolved {
        let surface = validate_resolved_property_interface(store, type_)
            .ok_or_else(|| invalid(plan, type_))?;
        let TypeData::Interface(interface) = store
            .type_payload(type_)
            .expect("the warm interface surface validated its record")
            .data()
        else {
            unreachable!("the warm interface surface changed payload kind")
        };
        if interface.resolved_base_types.as_deref() != Some(base_types)
            || surface.properties != expected_properties
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

    let prepared_members = if expected_entries.is_empty() {
        None
    } else {
        Some(
            PreparedSymbolTable::new(expected_entries.len())
                .ok_or(PropertyObjectError::Capacity(plan.node))?,
        )
    };

    // No fallible checker work follows this allocation. The prepared table
    // carries entry capacity into the transaction, and every referenced ID was
    // validated above.
    let members = prepared_members.map(|prepared| store.alloc_prepared_symbol_table(prepared));
    if let Some(members) = members {
        for (name, property) in expected_entries {
            assert_eq!(store.insert_symbol(members, name, property), Some(None));
        }
    }
    publish_prepared_direct_interface_declared_properties(
        store,
        plan,
        type_,
        property_types,
        declared_state,
    );
    assert!(store.set_interface_base_resolution(type_, true, None, Some(base_types.to_vec()),));
    assert!(store.set_structured_type_members(
        type_,
        members,
        (!expected_properties.is_empty()).then_some(expected_properties),
        None,
        None,
        None,
    ));
    Ok(type_)
}

/// Validates whether an already-resolved interface uses the direct heritage
/// member shape admitted above. This is the semantic-only proof consumed by
/// structural relations when a final property is owned by an ancestor symbol.
pub(super) fn validate_interface_heritage_members(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> InterfaceHeritageMembersValidation {
    let Some(TypeData::Interface(interface)) =
        store.type_payload(type_).map(|record| record.data())
    else {
        return InterfaceHeritageMembersValidation::NotHeritage;
    };
    let Some(bases) = interface.resolved_base_types.as_deref() else {
        return InterfaceHeritageMembersValidation::NotHeritage;
    };
    if bases.is_empty() {
        return InterfaceHeritageMembersValidation::Malformed;
    }
    if validate_resolved_property_interface(store, type_).is_some() {
        InterfaceHeritageMembersValidation::Valid
    } else {
        InterfaceHeritageMembersValidation::Malformed
    }
}

fn validate_resolved_property_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<ValidatedInterfaceSurface> {
    validate_resolved_property_interface_inner(store, type_, &mut HashSet::new())
}

fn validate_resolved_property_interface_inner(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    active: &mut HashSet<TypeId>,
) -> Option<ValidatedInterfaceSurface> {
    if !active.insert(type_) {
        return None;
    }
    let result = (|| {
        let record = store.type_payload(type_)?;
        let TypeData::Interface(interface) = record.data() else {
            return None;
        };
        let owner = record.symbol()?;
        let owner_record = store.symbol(owner)?;
        if record.flags() != TypeFlags::OBJECT
            || record.object_flags() != ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
            || record.alias().is_some()
            || owner_record.flags() != SymbolFlags::INTERFACE
            || owner_record.check_flags() != CheckFlags::NONE
            || owner_record.members() != interface.declared_members
            || owner_record.exports().is_some()
            || owner_record.export_symbol().is_some()
            || store.get_merged_symbol(owner) != Some(owner)
            || !valid_thisless_interface_identity(interface)
            || !interface.base_types_resolved
            || !interface.declared_members_resolved
            || interface.resolved_base_constructor_type.is_some()
            || interface.declared_call_signatures.is_some()
            || interface.declared_construct_signatures.is_some()
            || interface.declared_index_infos.is_some()
        {
            return None;
        }
        let structured = &interface.reference.object.structured;
        if structured.constrained != ConstrainedTypeData::default()
            || structured.call_signature_count != 0
            || structured.signatures.is_some()
            || structured.index_infos.is_some()
            || structured
                .object_type_without_abstract_construct_signatures
                .is_some()
        {
            return None;
        }

        let mut ancestry = HashSet::new();
        ancestry.insert(owner);
        if let Some(base_types) = interface.resolved_base_types.as_deref() {
            if base_types.is_empty() {
                return None;
            }
            let mut seen_bases = HashSet::with_capacity(base_types.len());
            for base in base_types {
                if !seen_bases.insert(*base) {
                    return None;
                }
                let base_surface =
                    validate_resolved_property_interface_inner(store, *base, active)?;
                ancestry.extend(base_surface.ancestry);
            }
        }

        let properties = structured.properties.clone().unwrap_or_default();
        if properties.is_empty() != structured.properties.is_none() {
            return None;
        }
        let mut entries = Vec::with_capacity(properties.len());
        let mut seen_properties = HashSet::with_capacity(properties.len());
        let mut seen_names = HashSet::with_capacity(properties.len());
        let mut own_properties = HashSet::new();
        for property in &properties {
            let property_record = store.symbol(*property)?;
            let parent = property_record.parent()?;
            let name = property_record.name().to_owned();
            if !seen_properties.insert(*property)
                || !seen_names.insert(name.clone())
                || !ancestry.contains(&parent)
                || !valid_property_symbol(store, *property)
            {
                return None;
            }
            if parent == owner {
                own_properties.insert(*property);
            }
            entries.push((name, *property));
        }
        if !exact_member_table(store, &entries, structured.members) {
            return None;
        }
        let declared = match interface.declared_members {
            None if own_properties.is_empty() => None,
            Some(table) => Some(store.symbol_table(table)?),
            _ => return None,
        };
        if let Some(declared) = declared {
            if declared.len() != own_properties.len()
                || declared.iter().any(|(name, property)| {
                    !own_properties.contains(&property)
                        || store
                            .symbol(property)
                            .is_none_or(|record| record.name() != name)
                })
            {
                return None;
            }
            for property in &own_properties {
                let record = store.symbol(*property)?;
                if declared.get(record.name()) != Some(*property) {
                    return None;
                }
            }
        }
        Some(ValidatedInterfaceSurface {
            properties,
            ancestry,
        })
    })();
    active.remove(&type_);
    result
}

fn valid_property_symbol(store: &CanonicalTypeMapperStore, property: SemanticSymbolId) -> bool {
    let Some(record) = store.symbol(property) else {
        return false;
    };
    let Some([declaration]) = record.declarations() else {
        return false;
    };
    let expected_flags = SymbolFlags::PROPERTY
        | if record.flags().contains(SymbolFlags::OPTIONAL) {
            SymbolFlags::OPTIONAL
        } else {
            SymbolFlags::NONE
        };
    record.flags() == expected_flags
        && record.check_flags() == CheckFlags::NONE
        && record.value_declaration() == Some(*declaration)
        && record.members().is_none()
        && record.exports().is_none()
        && record.parent().is_some()
        && record.export_symbol().is_none()
        && store.get_merged_symbol(property) == Some(property)
        && matches!(
            store.source_node_kind(*declaration),
            Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
        )
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

fn exact_member_table(
    store: &CanonicalTypeMapperStore,
    entries: &[(EscapedName, SemanticSymbolId)],
    members: Option<ts_binder::SymbolTableId>,
) -> bool {
    let table = members.and_then(|members| store.symbol_table(members));
    if entries.is_empty() {
        return members.is_none();
    }
    let Some(table) = table else {
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
