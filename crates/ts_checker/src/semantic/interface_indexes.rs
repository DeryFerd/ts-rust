//! Own interface index queries that do not resolve unrelated members.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalCheckerDiagnostics, CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeError,
    DeclaredTypeHost, IndexInfoId, TypeId,
    declared::{preflight_class_or_interface_reference, preflight_node},
    links::TypeNodeLinks,
    object_members::{PlannedIndexSignature, PropertyObjectError, plan_index_signature},
    type_nodes::{CanonicalTypeQuery, CanonicalTypeQueryOptions},
    type_records::{ConstrainedTypeData, InterfaceTypeData, TypeData},
    types::{ObjectFlags, TypeFlags},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct InterfaceIndexView {
    pub key_type: TypeId,
    pub value_type: TypeId,
    pub readonly: bool,
    pub declaration: NodeRef,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum InterfaceIndexError {
    DeclaredType(DeclaredTypeError),
    IndexSignature(PropertyObjectError),
    InvalidInterface(TypeId),
    UnsupportedInterface(TypeId),
    DuplicateNumericIndex(NodeRef),
    InvalidIndexCache(NodeRef),
}

impl From<DeclaredTypeError> for InterfaceIndexError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<PropertyObjectError> for InterfaceIndexError {
    fn from(error: PropertyObjectError) -> Self {
        Self::IndexSignature(error)
    }
}

/// Selects an own numeric index before the caller examines inherited indexes.
///
/// A missing own index returns `None`. The query resolves only the selected
/// key and value annotations. It does not publish interface members or indexes.
pub(super) fn resolve_own_numeric_interface_index(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    options: CanonicalTypeQueryOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    receiver: TypeId,
) -> Result<Option<InterfaceIndexView>, InterfaceIndexError> {
    let Some(plans) = plan_own_interface_indexes(store, host, receiver)? else {
        return Ok(None);
    };
    let mut selected = None;
    for plan in &plans {
        if store.source_node_kind(plan.key_type_node) == Some(SyntaxKind::NumberKeyword)
            && selected.replace(plan).is_some()
        {
            return Err(InterfaceIndexError::DuplicateNumericIndex(plan.declaration));
        }
    }
    let Some(plan) = selected else {
        return Ok(None);
    };
    validate_cached_index_lists(store, receiver, &plans, plan)?;
    let mut query = match global_types {
        Some(global_types) => CanonicalTypeQuery::new_with_global_types(
            store,
            host,
            global_types,
            options,
            diagnostics,
        )?,
        None => CanonicalTypeQuery::new(store, host, options, diagnostics)?,
    };
    query.preflight_type_from_type_node(plan.key_type_node)?;
    query.preflight_type_from_type_node(plan.value_type_node)?;
    let key_type = query.get_type_from_type_node(plan.key_type_node)?;
    let value_type = query.get_type_from_type_node(plan.value_type_node)?;
    validate_cached_index_lists(store, receiver, &plans, plan)?;
    Ok(Some(InterfaceIndexView {
        key_type,
        value_type,
        readonly: plan.readonly,
        declaration: plan.declaration,
    }))
}

#[allow(clippy::too_many_lines)] // Check interface identity and source index ownership before resolution.
fn plan_own_interface_indexes(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    receiver: TypeId,
) -> Result<Option<Vec<PlannedIndexSignature>>, InterfaceIndexError> {
    let invalid = || InterfaceIndexError::InvalidInterface(receiver);
    let record = store.type_payload(receiver).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = record.data() else {
        return Ok(None);
    };
    if !record.object_flags().contains(ObjectFlags::INTERFACE) {
        return Ok(None);
    }
    let owner = record.symbol().ok_or_else(invalid)?;
    let symbol = store.symbol(owner).ok_or_else(invalid)?;
    if symbol.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE {
        return Err(invalid());
    }
    if record.flags() != TypeFlags::OBJECT
        || !record.object_flags().contains(ObjectFlags::INTERFACE)
        || record.object_flags()
            & !(ObjectFlags::INTERFACE | ObjectFlags::REFERENCE | ObjectFlags::MEMBERS_RESOLVED)
            != ObjectFlags::NONE
        || record.alias().is_some()
        || symbol.check_flags() != CheckFlags::NONE
        || symbol.value_declaration().is_some()
        || symbol.exports().is_some()
        || symbol.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(receiver)
    {
        return Err(invalid());
    }
    if preflight_class_or_interface_reference(store, host, owner, SymbolFlags::INTERFACE)? != 0 {
        return Err(InterfaceIndexError::UnsupportedInterface(receiver));
    }
    validate_member_cache_state(store, receiver, interface, owner)?;
    let declarations = symbol
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or_else(invalid)?;
    let mut seen = HashSet::new();
    let mut plans = Vec::new();
    for declaration in declarations {
        let record = preflight_node(store, host, *declaration)?;
        let NodeData::InterfaceDeclaration(interface) = &record.data else {
            return Err(invalid());
        };
        if record.kind != SyntaxKind::InterfaceDeclaration
            || record.flags.0 != 0
            || interface.type_parameters.is_some()
            || interface.symbol.is_some()
            || !host.symbol_matches(store, *declaration, owner)
            || !seen.insert(*declaration)
        {
            return Err(invalid());
        }
        for member in &interface.members.nodes {
            let member = NodeRef::new(declaration.arena, declaration.file, *member);
            let member_record = preflight_node(store, host, member)?;
            if member_record.parent != Some(declaration.node) || !seen.insert(member) {
                return Err(invalid());
            }
            if member_record.kind == SyntaxKind::IndexSignature {
                plans.push(plan_index_signature(
                    store,
                    host,
                    *declaration,
                    owner,
                    member,
                )?);
            }
        }
    }
    let index_symbol = symbol
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get(InternalSymbolName::Index.as_ref()));
    if plans.is_empty() {
        if index_symbol.is_some() || interface.declared_index_infos.is_some() {
            return Err(invalid());
        }
    } else {
        let index_symbol = index_symbol.ok_or_else(invalid)?;
        let index = store.symbol(index_symbol).ok_or_else(invalid)?;
        let expected = plans
            .iter()
            .map(|plan| plan.declaration)
            .collect::<Vec<_>>();
        if index.declarations() != Some(expected.as_slice())
            || plans.iter().any(|plan| plan.symbol != index_symbol)
        {
            return Err(invalid());
        }
    }
    Ok(Some(plans))
}

fn validate_member_cache_state(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    interface: &InterfaceTypeData,
    owner: SemanticSymbolId,
) -> Result<(), InterfaceIndexError> {
    let invalid = || InterfaceIndexError::InvalidInterface(receiver);
    let structured = &interface.reference.object.structured;
    if interface.resolved_base_constructor_type.is_some()
        || structured.constrained != ConstrainedTypeData::default()
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return Err(invalid());
    }
    if interface.declared_members_resolved {
        if interface.declared_members
            != store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
        {
            return Err(invalid());
        }
    } else if interface.declared_members.is_some()
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || interface.declared_index_infos.is_some()
        || structured.members.is_some()
        || structured.properties.is_some()
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
        || structured.index_infos.is_some()
        || store.type_payload(receiver).is_some_and(|record| {
            record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        })
    {
        return Err(invalid());
    }
    Ok(())
}

fn validate_cached_index_lists(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    plans: &[PlannedIndexSignature],
    selected: &PlannedIndexSignature,
) -> Result<(), InterfaceIndexError> {
    let invalid = || InterfaceIndexError::InvalidIndexCache(selected.declaration);
    let TypeData::Interface(interface) = store.type_payload(receiver).ok_or_else(invalid)?.data()
    else {
        return Err(invalid());
    };
    if let Some(indexes) = interface.declared_index_infos.as_deref() {
        if indexes.len() != plans.len() {
            return Err(invalid());
        }
        let mut seen = HashSet::new();
        for (index, plan) in indexes.iter().zip(plans) {
            if !seen.insert(*index) {
                return Err(invalid());
            }
            validate_cached_index(store, *index, plan)?;
        }
    } else if interface.declared_members_resolved {
        return Err(invalid());
    }
    if let Some(indexes) = interface.reference.object.structured.index_infos.as_deref() {
        let number = store.intrinsic_bootstrap().ok_or_else(invalid)?.number_type;
        let mut numeric = indexes.iter().filter(|index| {
            store
                .index_info(**index)
                .is_some_and(|info| info.key_type() == number)
        });
        let index = numeric.next().ok_or_else(invalid)?;
        if numeric.next().is_some() {
            return Err(invalid());
        }
        validate_cached_index(store, *index, selected)?;
    } else if store.type_payload(receiver).is_some_and(|record| {
        record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
    }) {
        return Err(invalid());
    }
    Ok(())
}

fn validate_cached_index(
    store: &CanonicalTypeMapperStore,
    index: IndexInfoId,
    plan: &PlannedIndexSignature,
) -> Result<(), InterfaceIndexError> {
    let invalid = || InterfaceIndexError::InvalidIndexCache(plan.declaration);
    let info = store.index_info(index).ok_or_else(invalid)?;
    if info.declaration() != Some(plan.declaration)
        || info.is_readonly() != plan.readonly
        || info.index_symbol().is_some()
        || !info.components().is_empty()
        || store.type_node_links(plan.key_type_node)
            != Some(&TypeNodeLinks {
                resolved_type: Some(info.key_type()),
                ..TypeNodeLinks::default()
            })
        || store.type_node_links(plan.value_type_node)
            != Some(&TypeNodeLinks {
                resolved_type: Some(info.value_type()),
                ..TypeNodeLinks::default()
            })
    {
        return Err(invalid());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, NodeArena};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{IntrinsicBootstrapOptions, production::GlobalMergeCompletion};

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        files: BTreeMap<FileId, BoundFile>,
        store: CanonicalTypeMapperStore,
    }

    const MIXED: &str = concat!(
        "interface ReadonlyArray<T> { readonly [index: number]: T; } ",
        "interface ArrayIterator<T> {} ",
        "interface Mixed extends ReadonlyArray<unknown> { ",
        "readonly [index: number]: number; ",
        "[Symbol.iterator](): ArrayIterator<string>; }",
    );

    fn fixture(source: &str) -> Fixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(5_126);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/interface-indexes.ts\""),
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

    fn interface(fixture: &mut Fixture, name: &str) -> TypeId {
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let symbol = fixture
            .store
            .symbol_table(globals)
            .unwrap()
            .get_source(name)
            .unwrap();
        let host = host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        fixture
            .store
            .get_declared_type_of_symbol(&host, symbol)
            .unwrap()
    }

    fn query(
        fixture: &mut Fixture,
        receiver: TypeId,
    ) -> Result<Option<InterfaceIndexView>, InterfaceIndexError> {
        let host = host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let result = resolve_own_numeric_interface_index(
            &mut fixture.store,
            &host,
            None,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
            receiver,
        );
        assert!(diagnostics.is_empty());
        result
    }

    #[test]
    fn own_numeric_index_does_not_resolve_generic_base_or_iterator_method() {
        let mut fixture = fixture(MIXED);
        let receiver = interface(&mut fixture, "Mixed");
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.index_info_len(),
        );
        let actual = query(&mut fixture, receiver).unwrap().unwrap();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(actual.key_type, number);
        assert_eq!(actual.value_type, number);
        assert!(actual.readonly);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.index_info_len()
            ),
            before,
        );
        let TypeData::Interface(interface) = fixture.store.type_payload(receiver).unwrap().data()
        else {
            panic!("the receiver must retain its interface shell")
        };
        assert!(!interface.declared_members_resolved);
        assert!(!interface.base_types_resolved);
        assert!(interface.reference.object.structured.index_infos.is_none());
        let warm = fixture.store.checker_link_allocated_lengths();
        assert_eq!(query(&mut fixture, receiver), Ok(Some(actual)));
        assert_eq!(fixture.store.checker_link_allocated_lengths(), warm);
    }

    #[test]
    fn missing_own_numeric_index_leaves_inherited_lookup_to_the_caller() {
        let mut fixture = fixture(concat!(
            "interface ReadonlyArray<T> { readonly [index: number]: T; } ",
            "interface Inherited extends ReadonlyArray<string> {} ",
            "interface Named { [key: string]: number; }",
        ));
        for name in ["Inherited", "Named"] {
            let receiver = interface(&mut fixture, name);
            let state = (
                fixture.store.type_len(),
                fixture.store.index_info_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(query(&mut fixture, receiver), Ok(None));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.index_info_len(),
                    fixture.store.checker_link_allocated_lengths()
                ),
                state,
            );
        }
    }

    #[test]
    fn own_numeric_index_revalidates_existing_index_records() {
        for poison in 0..5 {
            let mut fixture = fixture(MIXED);
            let receiver = interface(&mut fixture, "Mixed");
            let actual = query(&mut fixture, receiver).unwrap().unwrap();
            let owner = fixture
                .store
                .type_payload(receiver)
                .unwrap()
                .symbol()
                .unwrap();
            let members = fixture.store.symbol(owner).unwrap().members();
            let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
            let index = fixture
                .store
                .alloc_index_info(
                    if poison == 1 { string } else { actual.key_type },
                    if poison == 2 {
                        string
                    } else {
                        actual.value_type
                    },
                    poison != 3,
                    if poison == 4 {
                        None
                    } else {
                        Some(actual.declaration)
                    },
                    Vec::new(),
                )
                .unwrap();
            assert!(fixture.store.set_interface_declared_members(
                receiver,
                true,
                members,
                None,
                None,
                Some(vec![index]),
            ));
            let state = (
                fixture.store.type_len(),
                fixture.store.index_info_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            if poison == 0 {
                assert_eq!(query(&mut fixture, receiver), Ok(Some(actual)));
            } else {
                assert_eq!(
                    query(&mut fixture, receiver),
                    Err(InterfaceIndexError::InvalidIndexCache(actual.declaration))
                );
            }
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.index_info_len(),
                    fixture.store.checker_link_allocated_lengths()
                ),
                state,
            );
        }
    }

    #[test]
    fn own_numeric_index_rejects_forged_annotation_and_owner_caches() {
        for warm in [false, true] {
            for poison in 0..3 {
                let mut fixture = fixture(MIXED);
                let receiver = interface(&mut fixture, "Mixed");
                if warm {
                    query(&mut fixture, receiver).unwrap().unwrap();
                }
                let owner = fixture
                    .store
                    .type_payload(receiver)
                    .unwrap()
                    .symbol()
                    .unwrap();
                let host = host(
                    &fixture.parsed.arena,
                    fixture.files.get(&fixture.file).unwrap(),
                );
                let plans = plan_own_interface_indexes(&fixture.store, &host, receiver)
                    .unwrap()
                    .unwrap();
                let plan = &plans[0];
                match poison {
                    0 | 1 => {
                        let wrong = fixture.store.intrinsic_bootstrap().unwrap().string_type;
                        let node = if poison == 0 {
                            plan.key_type_node
                        } else {
                            plan.value_type_node
                        };
                        assert!(fixture.store.set_type_node_links(
                            node,
                            TypeNodeLinks {
                                resolved_type: Some(wrong),
                                ..TypeNodeLinks::default()
                            }
                        ));
                    }
                    2 => assert!(fixture.store.set_symbol_flags(
                        owner,
                        SymbolFlags::INTERFACE | SymbolFlags::CLASS,
                        CheckFlags::NONE
                    )),
                    _ => unreachable!(),
                }
                let state = (
                    fixture.store.type_len(),
                    fixture.store.index_info_len(),
                    fixture.store.checker_link_allocated_lengths(),
                );
                assert!(
                    query(&mut fixture, receiver).is_err(),
                    "poison {poison}, warm {warm}"
                );
                assert_eq!(
                    (
                        fixture.store.type_len(),
                        fixture.store.index_info_len(),
                        fixture.store.checker_link_allocated_lengths()
                    ),
                    state,
                );
            }
        }
    }
}
