//! Structured-member publication for one direct, nongeneric interface base.
//!
//! The first heritage capability is intentionally narrow: one base, no base
//! heritage, property-only surfaces, and disjoint own/base names. This avoids
//! claiming support for override and conflict diagnostics before their pinned
//! TS2430/TS2320 paths exist.

use std::collections::HashSet;

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags, SymbolTableId,
    semantic::PreparedSymbolTable,
};

use super::{
    CanonicalTypeMapperStore, TypeId,
    links::ValueSymbolLinks,
    object_members::{
        DirectInterfaceDeclaredState, PropertyObjectError, PropertyObjectKind, PropertyObjectPlan,
        prepare_direct_interface_declared_properties,
        publish_prepared_direct_interface_declared_properties,
    },
    store::SourceNodeParent,
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

/// Resolves and publishes the exact one-base interface-heritage capability.
///
/// `base_types` must contain the one type whose canonical symbol was retained
/// by the syntax plan. The base must be a fully resolved, no-heritage,
/// property-only interface. All owned allocations and sparse-link slots are
/// staged before the first observable semantic mutation.
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
    let [planned_base] = heritage.bases.as_slice() else {
        return Err(invalid(plan, type_));
    };
    let [base_type] = base_types else {
        return Err(invalid(plan, type_));
    };
    if plan.kind != PropertyObjectKind::Interface
        || !plan.indexes.is_empty()
        || !plan.call_signatures.is_empty()
    {
        return Err(invalid(plan, type_));
    }

    let base_record = store
        .type_payload(*base_type)
        .ok_or_else(|| invalid(plan, type_))?;
    if base_record.symbol() != Some(planned_base.symbol) {
        return Err(invalid(plan, type_));
    }
    if base_record.data().structured().is_some_and(|structured| {
        structured.call_signature_count != 0
            || structured
                .signatures
                .as_ref()
                .is_some_and(|set| !set.is_empty())
            || structured
                .index_infos
                .as_ref()
                .is_some_and(|set| !set.is_empty())
    }) {
        return Err(PropertyObjectError::UnsupportedMember {
            node: planned_base.node,
            kind: SyntaxKind::ExpressionWithTypeArguments,
        });
    }
    let base_surface = validate_no_heritage_property_interface(store, *base_type)
        .ok_or_else(|| invalid(plan, type_))?;
    if base_surface.owner != planned_base.symbol {
        return Err(invalid(plan, type_));
    }

    let declared_state =
        prepare_direct_interface_declared_properties(store, plan, type_, property_types)?;
    let total_properties = plan
        .properties
        .len()
        .checked_add(base_surface.properties.len())
        .ok_or_else(|| capacity(plan))?;
    let mut expected_properties = Vec::new();
    let mut expected_entries = Vec::new();
    let mut seen_names = HashSet::new();
    expected_properties
        .try_reserve_exact(total_properties)
        .map_err(|_| capacity(plan))?;
    expected_entries
        .try_reserve_exact(total_properties)
        .map_err(|_| capacity(plan))?;
    seen_names
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
    for property in base_surface.properties {
        let record = store.symbol(property).ok_or_else(|| invalid(plan, type_))?;
        let name = record.name().to_owned();
        if !seen_names.insert(name.clone()) {
            return Err(PropertyObjectError::UnsupportedMember {
                node: planned_base.node,
                kind: SyntaxKind::ExpressionWithTypeArguments,
            });
        }
        expected_entries.push((name, property));
        expected_properties.push(property);
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
        .try_reserve_exact(1)
        .map_err(|_| capacity(plan))?;
    staged_base_types.push(*base_type);
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
    {
        return Err(capacity(plan));
    }

    // Every allocation and fallible semantic check precedes this point. The
    // prepared table owns entry capacity, the table arena and sparse value-link
    // map are reserved, and the base/property vectors are already staged.
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
    assert!(store.set_interface_base_resolution(type_, true, None, Some(staged_base_types),));
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

/// Plan-aware warm-cache proof used by contextual typing and diagnostics.
///
/// In addition to exact final member reconstruction, this verifies that the
/// cached base type's canonical symbol is the one resolved by the retained
/// syntax plan.
pub(super) fn validate_planned_interface_heritage_members(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
) -> bool {
    let Some(heritage) = plan.heritage.as_ref() else {
        return false;
    };
    let [planned_base] = heritage.bases.as_slice() else {
        return false;
    };
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    let TypeData::Interface(interface) = record.data() else {
        return false;
    };
    let Some([base_type]) = interface.resolved_base_types.as_deref() else {
        return false;
    };
    if record.symbol() != Some(plan.symbol)
        || interface.declared_members != plan.members
        || store
            .type_payload(*base_type)
            .and_then(|base| base.symbol())
            != Some(planned_base.symbol)
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
    surface.owner == plan.symbol && surface.declared_properties == planned_properties
}

/// Semantic-only exact proof consumed by structural relations.
pub(super) fn validate_interface_heritage_members(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> InterfaceHeritageMembersValidation {
    let Some(TypeData::Interface(interface)) =
        store.type_payload(type_).map(|record| record.data())
    else {
        return InterfaceHeritageMembersValidation::NotHeritage;
    };
    if interface.resolved_base_types.is_none() {
        return InterfaceHeritageMembersValidation::NotHeritage;
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
    let record = store.type_payload(type_)?;
    let TypeData::Interface(interface) = record.data() else {
        return None;
    };
    let owner = record.symbol()?;
    let owner_record = store.symbol(owner)?;
    let [owner_declaration] = owner_record.declarations()? else {
        return None;
    };
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
        || store.source_node_kind(*owner_declaration) != Some(SyntaxKind::InterfaceDeclaration)
        || store
            .declared_type_links(owner)
            .is_none_or(|links| links.declared_type != Some(type_))
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

    let declared_properties =
        declared_properties(store, owner, *owner_declaration, interface.declared_members)?;
    let base_properties = match (
        requires_direct_base,
        interface.resolved_base_types.as_deref(),
    ) {
        (false, None) => Vec::new(),
        (true, Some([base_type])) if *base_type != type_ => {
            let base = validate_no_heritage_property_interface(store, *base_type)?;
            base.properties
        }
        _ => return None,
    };

    let total = declared_properties
        .len()
        .checked_add(base_properties.len())?;
    let mut expected = Vec::with_capacity(total);
    let mut seen_names = HashSet::with_capacity(total);
    for property in declared_properties.iter().chain(&base_properties) {
        let record = store.symbol(*property)?;
        if !seen_names.insert(record.name().to_owned()) {
            return None;
        }
        expected.push(*property);
    }
    let actual = structured.properties.as_deref().unwrap_or_default();
    if actual.is_empty() != structured.properties.is_none()
        || actual != expected.as_slice()
        || !exact_property_table(store, &expected, structured.members)
    {
        return None;
    }
    Some(ValidatedInterfaceSurface {
        owner,
        declared_properties,
        properties: expected,
    })
}

fn declared_properties(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declaration: NodeRef,
    members: Option<SymbolTableId>,
) -> Option<Vec<SemanticSymbolId>> {
    let Some(members) = members else {
        return Some(Vec::new());
    };
    let table = store.symbol_table(members)?;
    if table.is_empty() {
        return None;
    }
    let mut properties = Vec::with_capacity(table.len());
    for (name, property) in table.iter() {
        let record = store.symbol(property)?;
        let declaration = property_declaration(store, property)?;
        if record.name() != name
            || record.parent() != Some(owner)
            || !declaration.is_for(owner_declaration.arena, owner_declaration.file)
            || store.source_node_parent(declaration)
                != Some(SourceNodeParent::Parent(owner_declaration))
            || !valid_property_symbol(store, property)
        {
            return None;
        }
        properties.push(property);
    }
    properties.sort_unstable_by_key(|property| {
        property_declaration(store, *property)
            .expect("validated declared property retains its declaration")
    });
    if properties
        .windows(2)
        .any(|pair| property_declaration(store, pair[0]) >= property_declaration(store, pair[1]))
    {
        return None;
    }
    Some(properties)
}

fn property_declaration(
    store: &CanonicalTypeMapperStore,
    property: SemanticSymbolId,
) -> Option<NodeRef> {
    let [declaration] = store.symbol(property)?.declarations()? else {
        return None;
    };
    Some(*declaration)
}

fn valid_property_symbol(store: &CanonicalTypeMapperStore, property: SemanticSymbolId) -> bool {
    let Some(record) = store.symbol(property) else {
        return false;
    };
    let Some(declaration) = property_declaration(store, property) else {
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
        && record.value_declaration() == Some(declaration)
        && record.members().is_none()
        && record.exports().is_none()
        && record.parent().is_some()
        && record.export_symbol().is_none()
        && store.get_merged_symbol(property) == Some(property)
        && matches!(
            store.source_node_kind(declaration),
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

fn exact_property_table(
    store: &CanonicalTypeMapperStore,
    properties: &[SemanticSymbolId],
    members: Option<SymbolTableId>,
) -> bool {
    if properties.is_empty() {
        return members.is_none();
    }
    let Some(table) = members.and_then(|members| store.symbol_table(members)) else {
        return false;
    };
    table.len() == properties.len()
        && properties.iter().all(|property| {
            store
                .symbol(*property)
                .is_some_and(|record| table.get(record.name()) == Some(*property))
        })
        && table
            .iter()
            .all(|(_, property)| properties.contains(&property))
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
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        DeclaredTypeHost,
        bootstrap::IntrinsicBootstrapOptions,
        declared::get_declared_class_interface_or_type_parameter,
        object_members::{self, PropertyObjectState},
        production::GlobalMergeCompletion,
    };

    const SOURCE: &str = concat!(
        "interface Base { first: number; second: number }\n",
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
        let parsed = parse_source_file(SOURCE);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(801);
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
        let mut fixture = fixture();
        let base = interface_symbol(&fixture, "Base");
        let other = interface_symbol(&fixture, "Other");
        let derived = interface_symbol(&fixture, "Derived");
        let host = host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let base_plan = object_members::plan_interface(&fixture.store, &host, base).unwrap();
        let other_plan = object_members::plan_interface(&fixture.store, &host, other).unwrap();
        let derived_plan = object_members::plan_interface(&fixture.store, &host, derived).unwrap();
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
        for (plan, type_, count) in [
            (&base_plan, base_type, 2usize),
            (&other_plan, other_type, 1usize),
        ] {
            let state = object_members::interface_state(&fixture.store, plan, type_).unwrap();
            assert_eq!(state, PropertyObjectState::Shell(type_));
            object_members::publish_declared_members(
                &mut fixture.store,
                plan,
                state,
                &vec![number_type; count],
                &[],
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
    fn warm_validation_rejects_wrong_base_reorder_and_omission() {
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
            InterfaceHeritageMembersValidation::Valid,
        );
        assert!(!validate_planned_interface_heritage_members(
            &prepared.fixture.store,
            &prepared.derived_plan,
            prepared.derived_type,
        ));
        let wrong_base = derived_state(&prepared.fixture.store, prepared.derived_type, own);
        assert!(
            resolve_direct_interface_members(
                &mut prepared.fixture.store,
                &prepared.derived_plan,
                prepared.derived_type,
                &[prepared.number_type],
                &[prepared.other_type],
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
