use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    type_records::{CacheHashKey, MappedTypeData, TypeCacheState},
};
use ts_parser::{ParseResult, parse_source_file};
use xxhash_rust::xxh3::Xxh3;

const FILE: FileId = FileId::new(5_244);
const CELLS: &str = "interface Wrapper<Value> { value: Value } type Cells<Model> = { readonly [Key in keyof Model]-?: Wrapper<Model[Key]> }; ";
const ANY: &str = "type CallerOne = Cells<any>; type CallerTwo = Cells<any>; type Concrete = Cells<any>; let defaultOne: Cells<any>; let defaultTwo: Cells<any>; ";
const OBJECT: &str = "type Shape = { member: string }; type ObjectCells = Cells<Shape>; ";
const DEMAND: &str = "type ObjectValue = ObjectCells[\"member\"]; type AnyValue = Concrete[\"anything\"];";

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder.bind_source_file_with_facts(&parsed.arena, parsed.source_file, FILE,
        CanonicalSourceFileFacts::new(EscapedName::source("\"/project/homomorphic-any-request.ts\""),
            CanonicalSourceLanguage::TypeScript, false, CanonicalModuleState::Script)).unwrap();
    binder.bind_typescript_declaration_slice(&parsed.arena, FILE).unwrap();
    CanonicalCheckerContext::new(binder.finish(), vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true, exact_optional_property_types: true,
            },
            ..CanonicalCheckerOptions::default()
        }).unwrap()
}

fn alias(parsed: &ParseResult, name: &str) -> (NodeRef, NodeRef) {
    parsed.arena.iter().find_map(|(node, record)| {
        let NodeData::TypeAliasDeclaration(alias) = &record.data else { return None; };
        let NodeData::Identifier(identifier) = &parsed.arena.get(alias.name)?.data else { return None; };
        (identifier.text == name).then_some((
            NodeRef::new(parsed.arena.id(), FILE, node),
            NodeRef::new(parsed.arena.id(), FILE, alias.type_),
        ))
    }).unwrap_or_else(|| panic!("missing alias {name}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn alias_type(parsed: &ParseResult, checker: &CanonicalCheckerContext<'_>, name: &str) -> TypeId {
    checker.store().type_alias_links(symbol(checker, alias(parsed, name).0)).unwrap()
        .declared_type.unwrap()
}

fn annotation(parsed: &ParseResult, name: &str) -> NodeRef {
    parsed.arena.iter().find_map(|(_, record)| {
        let NodeData::VariableDeclaration(variable) = &record.data else { return None; };
        let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data else { return None; };
        (identifier.text == name).then(|| NodeRef::new(parsed.arena.id(), FILE, variable.type_.unwrap()))
    }).unwrap_or_else(|| panic!("missing variable {name}"))
}

fn mapped<'a>(checker: &'a CanonicalCheckerContext<'_>, id: TypeId) -> &'a MappedTypeData {
    let TypeData::Mapped(mapped) = checker.store().type_payload(id).unwrap().data() else {
        panic!("expected a mapped type");
    };
    mapped
}

fn cache_key(arguments: &[TypeId], alias: Option<(u64, &[TypeId])>) -> CacheHashKey {
    let mut hasher = Xxh3::new();
    let mut write = |types: &[TypeId]| {
        hasher.update(&(types.len() as u64).to_le_bytes());
        for type_ in types { hasher.update(&type_.get().to_le_bytes()); }
    };
    write(arguments);
    if let Some((symbol, arguments)) = alias {
        hasher.update(&[1]);
        hasher.update(&symbol.to_le_bytes());
        hasher.update(&(arguments.len() as u64).to_le_bytes());
        for type_ in arguments { hasher.update(&type_.get().to_le_bytes()); }
    } else { hasher.update(&[0]); }
    CacheHashKey::new(hasher.digest128())
}

fn physical_rows<'a>(checker: &'a CanonicalCheckerContext<'_>, target: TypeId)
    -> &'a std::collections::HashMap<CacheHashKey, TypeId>
{
    let TypeCacheState::Allocated(rows) = &mapped(checker, target).object.instantiations else {
        panic!("expected the original target cache");
    };
    rows
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 6] {
    let store = checker.store();
    [store.type_len(), store.type_alias_len(), store.symbol_len(), store.mapper_len(),
        store.index_info_len(), store.intrinsic_bootstrap().unwrap().union_cache_len()]
}

fn assert_wrapper(checker: &CanonicalCheckerContext<'_>, value: TypeId, argument: TypeId) {
    let TypeData::TypeReference(reference) = checker.store().type_payload(value).unwrap().data() else {
        panic!("the value must keep its Wrapper reference");
    };
    assert_eq!(reference.resolved_type_arguments.as_deref(), Some([argument].as_slice()));
}

fn check_mixed_order(object_first: bool) {
    let source = if object_first { format!("{CELLS}{OBJECT}{ANY}{DEMAND}") }
        else { format!("{CELLS}{ANY}{OBJECT}{DEMAND}") };
    let parsed = parse_source_file(&source);
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    assert!(checker.diagnostics().is_empty());
    let target = alias_type(&parsed, &checker, "Cells");
    let cells = symbol(&checker, alias(&parsed, "Cells").0);
    let any = checker.store().intrinsic_bootstrap().unwrap().any_type;
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    let callers = ["CallerOne", "CallerTwo", "Concrete"].map(|name| {
        let owner = symbol(&checker, alias(&parsed, name).0);
        let result = alias_type(&parsed, &checker, name);
        let global = checker.store().symbol_store().assigned_global_symbol_id(owner).unwrap();
        assert_eq!(physical_rows(&checker, target).get(&cache_key(&[any], Some((global, &[])))), Some(&result));
        let logical = checker.store().type_alias_links(cells).unwrap().instantiations.as_ref().unwrap();
        assert_eq!(logical.get(&cache_key(&[any], Some((global, &[])))), Some(&result));
        assert_eq!(checker.type_to_string(result).unwrap(), "Cells<any>");
        (owner, result)
    });
    for (index, (_, result)) in callers.iter().enumerate() {
        for (_, other) in &callers[index + 1..] { assert_ne!(result, other); }
        let data = mapped(&checker, *result);
        assert_eq!(data.object.target, Some(target));
        let parameter = data.type_parameter.unwrap();
        let TypeData::TypeParameter(parameter) = checker.store().type_payload(parameter).unwrap().data() else {
            panic!("expected the fresh key parameter");
        };
        assert_eq!(parameter.target, mapped(&checker, target).type_parameter);
        assert_eq!(parameter.mapper, data.object.mapper);
        let display = checker.store().type_alias(checker.store().type_payload(*result).unwrap().alias().unwrap()).unwrap();
        assert_eq!(display.symbol(), Some(cells));
        assert_eq!(display.type_arguments(), Some([any].as_slice()));
    }
    let first = checker.get_type_from_type_node(annotation(&parsed, "defaultOne")).unwrap();
    let second = checker.get_type_from_type_node(annotation(&parsed, "defaultTwo")).unwrap();
    assert_eq!(first, second);
    assert!(callers.iter().all(|(_, result)| *result != first));
    let global = checker.store().symbol_store().assigned_global_symbol_id(cells).unwrap();
    assert_eq!(physical_rows(&checker, target).get(&cache_key(&[any], Some((global, &[any])))), Some(&first));
    assert_eq!(checker.store().type_alias_links(cells).unwrap().instantiations.as_ref().unwrap()
        .get(&cache_key(&[any], None)), Some(&first));
    let object = alias_type(&parsed, &checker, "ObjectCells");
    assert_eq!(mapped(&checker, object).object.target, Some(target));
    assert_wrapper(&checker, alias_type(&parsed, &checker, "ObjectValue"), string);
    assert_wrapper(&checker, alias_type(&parsed, &checker, "AnyValue"), any);
    let [(.., concrete)] = &callers[2..] else { unreachable!() };
    let indexes = mapped(&checker, *concrete).object.structured.index_infos.as_deref().unwrap();
    let [index] = indexes else { panic!("any must have one string index"); };
    let index = checker.store().index_info(*index).unwrap();
    assert_eq!(index.key_type(), string);
    assert!(index.is_readonly());
    assert_wrapper(&checker, index.value_type(), any);
    let rows = physical_rows(&checker, target).clone();
    let warm = counts(&checker);
    for _ in 0..3 {
        checker.recheck_source_file(FILE).unwrap();
        for (name, (_, result)) in ["CallerOne", "CallerTwo", "Concrete"].into_iter().zip(callers) {
            assert_eq!(checker.get_type_from_type_node(alias(&parsed, name).1), Ok(result));
        }
        assert_eq!(checker.get_type_from_type_node(annotation(&parsed, "defaultOne")), Ok(first));
        assert_eq!(checker.get_type_from_type_node(annotation(&parsed, "defaultTwo")), Ok(first));
        assert_eq!(physical_rows(&checker, target), &rows);
        assert_eq!(counts(&checker), warm);
        assert!(checker.diagnostics().is_empty());
    }
}

#[test]
fn mixed_object_then_any_keeps_request_identity_and_replays() {
    check_mixed_order(true);
}

#[test]
fn mixed_any_then_object_keeps_request_identity_and_replays() {
    check_mixed_order(false);
}

// The crate includes this harness to test damaged private caches without a public mutation API.
#[allow(unused_macros)]
macro_rules! homomorphic_any_damage_controls {
    () => {
        fn damage_fixture() -> ParseResult {
            parse_source_file(&format!("{CELLS}{ANY}{OBJECT}{DEMAND}"))
        }

        #[test]
        fn physical_rows_reject_missing_swapped_and_wrong_target_entries() {
            for damage in 0..3 {
                let parsed = damage_fixture();
                let mut checker = context(&parsed);
                checker.check_source_file(FILE).unwrap();
                let target = alias_type(&parsed, &checker, "Cells");
                let concrete = alias_type(&parsed, &checker, "Concrete");
                let other = alias_type(&parsed, &checker, "CallerTwo");
                let rows = physical_rows(&checker, target).clone();
                let key = *rows.iter().find(|(_, result)| **result == concrete).unwrap().0;
                let mut broken = rows.clone();
                match damage {
                    0 => { broken.remove(&key); }
                    1 => { broken.insert(key, other); }
                    _ => { broken.insert(key, target); }
                }
                assert!(checker.store_mut_for_test().set_object_instantiations(target, TypeCacheState::Allocated(broken)));
                assert!(checker.get_type_from_type_node(alias(&parsed, "Concrete").1).is_err());
                assert!(checker.store_mut_for_test().set_object_instantiations(target, TypeCacheState::Allocated(rows)));
                assert_eq!(checker.get_type_from_type_node(alias(&parsed, "Concrete").1), Ok(concrete));
            }
        }

        #[test]
        fn logical_rows_reject_missing_and_swapped_requests() {
            for remove in [false, true] {
                let parsed = damage_fixture();
                let mut checker = context(&parsed);
                checker.check_source_file(FILE).unwrap();
                let cells = symbol(&checker, alias(&parsed, "Cells").0);
                let concrete = alias_type(&parsed, &checker, "Concrete");
                let other = alias_type(&parsed, &checker, "CallerTwo");
                let saved = checker.store().type_alias_links(cells).unwrap().clone();
                let mut broken = saved.clone();
                let rows = broken.instantiations.as_mut().unwrap();
                let key = *rows.iter().find(|(_, result)| **result == concrete).unwrap().0;
                if remove { rows.remove(&key); } else { rows.insert(key, other); }
                assert!(checker.store_mut_for_test().set_type_alias_links(cells, broken));
                assert!(checker.get_type_from_type_node(alias(&parsed, "Concrete").1).is_err());
                assert!(checker.store_mut_for_test().set_type_alias_links(cells, saved));
                assert_eq!(checker.get_type_from_type_node(alias(&parsed, "Concrete").1), Ok(concrete));
            }
        }

        fn query_counts(store: &crate::semantic::CanonicalTypeMapperStore) -> [usize; 6] {
            [store.type_len(), store.type_alias_len(), store.symbol_len(), store.mapper_len(),
                store.index_info_len(), store.intrinsic_bootstrap().unwrap().union_cache_len()]
        }

        #[test]
        fn source_free_complete_requests_demand_context_and_live_replay_keeps_identity() {
            let parsed = damage_fixture();
            let mut checker = context(&parsed);
            checker.check_source_file(FILE).unwrap();
            let target = alias_type(&parsed, &checker, "Cells");
            let concrete = alias_type(&parsed, &checker, "Concrete");
            let node = alias(&parsed, "Concrete").1;
            let owner = symbol(&checker, alias(&parsed, "Concrete").0);
            let parameters = checker.store().type_alias_links(symbol(&checker, alias(&parsed, "Cells").0))
                .unwrap().type_parameters.clone().unwrap();
            let any = checker.store().intrinsic_bootstrap().unwrap().any_type;
            let globals = checker.global_types().clone();
            let arrays = crate::semantic::array_types::CanonicalArrayTargets::from_global_types(&globals);
            let bound = checker.file(FILE).unwrap().1.clone();
            let options = checker.options();
            let host = crate::semantic::DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
            ).unwrap();
            let mut diagnostics = checker.diagnostics().clone();
            let mut session = super::InstantiationSession::new(super::InstantiationLimits::default());
            let warm = counts(&checker);
            let mut query = super::CanonicalTypeQuery::new_with_global_types_and_session(
                checker.store_mut_for_test(), &host, &globals, options, &mut session, &mut diagnostics,
            ).unwrap();
            assert!(query.completed_signature_instantiations.is_empty());
            for _ in 0..3 {
                let result = crate::semantic::instantiate::cached_instantiation_with_vector(
                    query.store, target, &parameters, &[any], Some(arrays), Some((owner, &[])),
                );
                let Err(crate::semantic::instantiate::InstantiationError::Declared(error)) = result else {
                    panic!("source-free replay must request the live context");
                };
                let demand = super::SourceQueryDemand::from_error(&error).unwrap();
                let request = super::SourceMappedReadRequest::Members { receiver: concrete };
                assert_eq!(demand, super::SourceQueryDemand::Mapped(request));
                assert_eq!(query.resolve_source_query_demand(demand, node), Ok(None));
                assert!(query.active_source_query_demands.is_empty());
                let live = query.source_query_context().unwrap();
                let proof = query.completed_signature_instantiations.iter().find_map(|operation| {
                    let super::SourceOperationProof::MappedRead(proof) = operation else { return None; };
                    (proof.request() == request).then_some(proof)
                }).expect("the resolver must retain the exact Members proof");
                assert_eq!(proof.members().type_id(), concrete);
                let retried = crate::semantic::instantiate::cached_instantiation_with_vector_and_alias_and_source(
                    query.store, target, &parameters, &[any], Some((owner, &[])), &globals, &live,
                );
                assert_eq!(retried, Ok(Some(concrete)));
                assert_eq!(query_counts(query.store), warm);
                assert!(query.diagnostics.is_empty());
            }
        }

        #[test]
        fn complete_any_cached_indexed_caller_consumes_members_demand_before_retry() {
            let parsed = damage_fixture();
            let mut checker = context(&parsed);
            checker.check_source_file(FILE).unwrap();
            let concrete = alias_type(&parsed, &checker, "Concrete");
            let expected = alias_type(&parsed, &checker, "AnyValue");
            let node = alias(&parsed, "AnyValue").1;
            let owner = symbol(&checker, alias(&parsed, "AnyValue").0);
            let bound = checker.file(FILE).unwrap().1.clone();
            let options = checker.options();
            let globals = checker.global_types().clone();
            let host = crate::semantic::DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
            ).unwrap();
            let mut diagnostics = checker.diagnostics().clone();
            let mut session = super::InstantiationSession::new(super::InstantiationLimits::default());
            let warm = counts(&checker);
            let mut query = super::CanonicalTypeQuery::new_with_global_types_and_session(
                checker.store_mut_for_test(), &host, &globals, options, &mut session, &mut diagnostics,
            ).unwrap();
            let syntax = super::plan_indexed_access_type(query.store, &host, node).unwrap();
            let object = query.store.type_node_links(syntax.object).unwrap().resolved_type.unwrap();
            let index = query.store.type_node_links(syntax.index).unwrap().resolved_type.unwrap();
            let indexed = super::PlannedSourceIndexedAccess { syntax, alias: Some(owner) };
            let request = super::SourceMappedReadRequest::Members { receiver: concrete };
            assert_eq!(object, concrete);
            assert_eq!(query.store.type_node_links(node).unwrap().resolved_type, Some(expected));
            assert!(query.completed_signature_instantiations.is_empty());
            let before = query.source_query_context().unwrap();
            assert_eq!(crate::semantic::instantiate::cached_instantiation_with_vector_and_alias_and_source(
                query.store, object, &[], &[], None, &globals, &before,
            ), Ok(Some(object)));
            assert!(crate::semantic::conditional_types::ConditionalBranchSource::completed_source_mapped_read(
                &before, request,
            ).is_none());
            let error = indexed.cached_result(query.store, node, object, index, &globals, &before)
                .expect_err("the cached indexed caller must demand the missing Members proof");
            assert_eq!(super::SourceQueryDemand::from_error(&error),
                Some(super::SourceQueryDemand::Mapped(request)));
            // The normal cached caller must consume that demand without a manual resolver call.
            assert_eq!(query.get_type_from_type_node(node), Ok(expected));
            assert!(query.active_source_query_demands.is_empty());
            assert!(query.completed_signature_instantiations.iter().any(|operation| {
                matches!(operation, super::SourceOperationProof::MappedRead(proof) if proof.request() == request)
            }));
            let live = query.source_query_context().unwrap();
            assert_eq!(indexed.cached_result(query.store, node, object, index, &globals, &live), Ok(Some(expected)));
            assert_eq!(query_counts(query.store), warm);
            for _ in 0..3 {
                assert_eq!(query.get_type_from_type_node(node), Ok(expected));
                assert!(query.active_source_query_demands.is_empty());
                assert_eq!(query_counts(query.store), warm);
                assert!(query.diagnostics.is_empty());
            }
        }

        fn cold_fixture() -> ParseResult {
            parse_source_file(&format!("interface Array<T> {{ length: number; [index: number]: T }} interface ReadonlyArray<T> {{ readonly length: number; readonly [index: number]: T }} {CELLS} declare function cold<P extends Cells<any>>(value: P): P;"))
        }

        fn cold_constraint(parsed: &ParseResult) -> NodeRef {
            parsed.arena.iter().find_map(|(_, record)| {
                let NodeData::TypeParameterDeclaration(parameter) = &record.data else { return None; };
                let NodeData::Identifier(name) = &parsed.arena.get(parameter.name)?.data else { return None; };
                if name.text != "P" { return None; }
                parameter.constraint.map(|constraint| NodeRef::new(parsed.arena.id(), FILE, constraint))
            }).expect("cold has the only written constraint")
        }

        #[test]
        fn completed_any_cold_identity_replays_exact_metadata_and_arrays() {
            let parsed = cold_fixture();
            let mut checker = context(&parsed);
            let node = cold_constraint(&parsed);
            let id = checker.get_type_from_type_node(node).unwrap();
            let before = mapped(&checker, id).clone();
            assert!(!checker.store().type_payload(id).unwrap().object_flags()
                .contains(crate::semantic::types::ObjectFlags::MEMBERS_RESOLVED));
            let warm = counts(&checker);
            for _ in 0..3 {
                assert_eq!(checker.store().validate_deferred_mapped_type(id), Ok(()));
                assert_eq!(checker.store().validate_mapped_type_relation_endpoint(id), Ok(None));
                assert_eq!(checker.type_to_string(id), Ok("Cells<any>".to_owned()));
                assert_eq!(checker.type_to_string_with_flags(id,
                    crate::semantic::CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT), Ok("Cells<any>".to_owned()));
                assert_eq!(mapped(&checker, id), &before);
                assert_eq!(counts(&checker), warm);
                assert!(checker.diagnostics().is_empty());
            }
        }

        #[test]
        fn cold_metadata_rejects_missing_binding_wrong_result_header_and_array_root() {
            for damage in 0..5 {
                let parsed = cold_fixture();
                let mut checker = context(&parsed);
                let node = cold_constraint(&parsed);
                let id = checker.get_type_from_type_node(node).unwrap();
                let before = mapped(&checker, id).clone();
                let binding = checker.store().symbol_node_links(node).unwrap().clone();
                let node_links = checker.store().type_node_links(node).unwrap().clone();
                let cells = symbol(&checker, alias(&parsed, "Cells").0);
                let header = checker.store().type_alias_links(cells).unwrap().clone();
                let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
                let array = checker.global_types().array_type;
                let array_owner = checker.store().type_payload(array).unwrap().symbol().unwrap();
                let array_links = checker.store().declared_type_links(array_owner).unwrap().clone();
                match damage {
                    0 => { assert!(checker.store_mut_for_test().set_symbol_node_links(node,
                        crate::semantic::SymbolNodeLinks { resolved_symbol: None })); }
                    1 => { assert!(checker.store_mut_for_test().set_symbol_node_links(node,
                        crate::semantic::SymbolNodeLinks { resolved_symbol: Some(array_owner) })); }
                    2 => {
                        let mut wrong = node_links.clone(); wrong.resolved_type = Some(string);
                        assert!(checker.store_mut_for_test().set_type_node_links(node, wrong));
                    }
                    3 => {
                        let mut wrong = header.clone(); wrong.type_parameters = None; wrong.instantiations = None;
                        assert!(checker.store_mut_for_test().set_type_alias_links(cells, wrong));
                    }
                    _ => {
                        let mut wrong = array_links.clone(); wrong.declared_type = Some(string);
                        assert!(checker.store_mut_for_test().set_declared_type_links(array_owner, wrong));
                    }
                }
                assert!(checker.store().validate_deferred_mapped_type(id).is_err());
                assert!(checker.type_to_string(id).is_err());
                assert_eq!(mapped(&checker, id), &before);
                assert!(checker.store_mut_for_test().set_symbol_node_links(node, binding));
                assert!(checker.store_mut_for_test().set_type_node_links(node, node_links));
                assert!(checker.store_mut_for_test().set_type_alias_links(cells, header));
                assert!(checker.store_mut_for_test().set_declared_type_links(array_owner, array_links));
                assert_eq!(checker.store().validate_deferred_mapped_type(id), Ok(()));
                assert_eq!(checker.type_to_string(id), Ok("Cells<any>".to_owned()));
                assert_eq!(mapped(&checker, id), &before);
            }
        }

        #[test]
        fn ready_any_reuse_requires_unchanged_request_key_mapping_and_override() {
            let parsed = parse_source_file(&format!("{CELLS} type Caller<Marker> = Cells<any>;"));
            let mut checker = context(&parsed);
            checker.check_source_file(FILE).unwrap();
            let id = alias_type(&parsed, &checker, "Caller");
            let owner = symbol(&checker, alias(&parsed, "Caller").0);
            let marker = checker.store().type_alias_links(owner).unwrap().type_parameters.as_ref().unwrap()[0];
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let bound = checker.file(FILE).unwrap().1.clone();
            let options = checker.options();
            let globals = checker.global_types().clone();
            let host = crate::semantic::DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
            ).unwrap();
            let mut diagnostics = checker.diagnostics().clone();
            let mut session = super::InstantiationSession::new(super::InstantiationLimits::default());
            let warm = counts(&checker);
            let query = super::CanonicalTypeQuery::new_with_global_types_and_session(
                checker.store_mut_for_test(), &host, &globals, options, &mut session, &mut diagnostics,
            ).unwrap();
            let live = query.source_query_context().unwrap();
            for _ in 0..3 {
                assert_eq!(crate::semantic::instantiate::cached_instantiation_with_vector_and_alias_and_source(
                    query.store, id, &[], &[], Some((owner, &[marker])), &globals, &live,
                ), Ok(Some(id)));
                assert!(crate::semantic::instantiate::cached_instantiation_with_vector_and_alias_and_source(
                    query.store, id, &[marker], &[string], None, &globals, &live,
                ).is_err());
                assert!(crate::semantic::instantiate::cached_instantiation_with_vector_and_alias_and_source(
                    query.store, id, &[], &[], Some((owner, &[string])), &globals, &live,
                ).is_err());
                assert_eq!(query_counts(query.store), warm);
            }
        }

        #[test]
        fn readonly_any_display_rejects_different_checker_options_and_globals() {
            let parsed = cold_fixture();
            let mut checker = context(&parsed);
            let id = checker.get_type_from_type_node(cold_constraint(&parsed)).unwrap();
            let bound = checker.file(FILE).unwrap().1.clone();
            let options = checker.options();
            let globals = checker.global_types().clone();
            let host = crate::semantic::DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
            ).unwrap();
            let mut wrong_options = options; wrong_options.strict_function_types = !options.strict_function_types;
            assert!(crate::semantic::formatter::type_to_string_with_checker_options_and_flags(
                checker.store(), &host, &globals, wrong_options, id,
                crate::semantic::CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            ).is_err());
            let mut wrong_globals = globals.clone(); wrong_globals.readonly_array_type = globals.array_type;
            assert!(crate::semantic::formatter::type_to_string_with_checker_options_and_flags(
                checker.store(), &host, &wrong_globals, options, id,
                crate::semantic::CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            ).is_err());
            assert_eq!(checker.type_to_string(id), Ok("Cells<any>".to_owned()));
        }

        #[test]
        fn complete_rows_reject_wrong_display_target_mapper_and_source_binding() {
            for damage in 0..4 {
                let parsed = damage_fixture();
                let mut checker = context(&parsed);
                checker.check_source_file(FILE).unwrap();
                let node = alias(&parsed, "Concrete").1;
                let concrete = alias_type(&parsed, &checker, "Concrete");
                let data = mapped(&checker, concrete).clone();
                let display_alias = checker.store().type_payload(concrete).unwrap().alias().unwrap();
                let display = checker.store().type_alias(display_alias).unwrap().type_arguments().unwrap().to_vec();
                let binding = checker.store().symbol_node_links(node).unwrap().clone();
                let wrong_symbol = symbol(&checker, alias(&parsed, "CallerTwo").0);
                let wrong_type = checker.store().intrinsic_bootstrap().unwrap().string_type;
                let wrong_mapper = checker.store_mut_for_test().new_simple_type_mapper(wrong_type, wrong_type).unwrap();
                match damage {
                    0 => { assert!(checker.store_mut_for_test().set_type_alias_arguments(display_alias, Some(vec![wrong_type]))); }
                    1 => { assert!(checker.store_mut_for_test().set_object_target_and_mapper(concrete, Some(concrete), data.object.mapper)); }
                    2 => { assert!(checker.store_mut_for_test().set_object_target_and_mapper(concrete, data.object.target, Some(wrong_mapper))); }
                    _ => { assert!(checker.store_mut_for_test().set_symbol_node_links(node,
                        crate::semantic::SymbolNodeLinks { resolved_symbol: Some(wrong_symbol) })); }
                }
                assert!(checker.get_type_from_type_node(node).is_err());
                assert!(checker.store_mut_for_test().set_type_alias_arguments(display_alias, Some(display)));
                assert!(checker.store_mut_for_test().set_object_target_and_mapper(concrete, data.object.target, data.object.mapper));
                assert!(checker.store_mut_for_test().set_symbol_node_links(node, binding));
                assert_eq!(checker.get_type_from_type_node(node), Ok(concrete));
            }
        }

        #[test]
        fn captured_complete_any_identity_replays_while_operational_reads_demand_members() {
            let parsed = cold_fixture();
            let mut checker = context(&parsed);
            let node = cold_constraint(&parsed);
            let id = checker.get_type_from_type_node(node).unwrap();
            let before = mapped(&checker, id).clone();
            let bound = checker.file(FILE).unwrap().1.clone();
            let options = checker.options();
            let globals = checker.global_types().clone();
            let arrays = crate::semantic::array_types::CanonicalArrayTargets::from_global_types(&globals);
            let host = crate::semantic::DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
            ).unwrap();
            let mut diagnostics = checker.diagnostics().clone();
            let mut session = super::InstantiationSession::new(super::InstantiationLimits::default());
            let warm = counts(&checker);
            let query = super::CanonicalTypeQuery::new_with_global_types_and_session(
                checker.store_mut_for_test(), &host, &globals, options, &mut session, &mut diagnostics,
            ).unwrap();
            let live = query.source_query_context().unwrap();
            let mut planner = live.planner(query.store);
            planner.plan_type_node_in_context(node, None, false).unwrap();
            let plan = planner.finish();
            for _ in 0..3 {
                assert_eq!(plan.cached_type_query_result_with_source(
                    query.store, Some(arrays), None, &[], node,
                    super::SourceCallableTypeReplay::Identity,
                    &mut std::collections::HashSet::new(), None,
                ), Ok(Some(id)));
                let error = plan.cached_type_query_result_with_source(
                    query.store, Some(arrays), None, &[], node,
                    super::SourceCallableTypeReplay::Operational,
                    &mut std::collections::HashSet::new(), None,
                ).expect_err("Operational replay must retain the Members demand");
                assert_eq!(super::SourceQueryDemand::from_error(&error), Some(
                    super::SourceQueryDemand::Mapped(super::SourceMappedReadRequest::Members {
                        receiver: id,
                    }),
                ));
                let TypeData::Mapped(current) = query.store.type_payload(id).unwrap().data() else {
                    panic!("Identity replay must keep the mapped result");
                };
                assert_eq!(current, &before);
                assert!(!query.store.type_payload(id).unwrap().object_flags()
                    .contains(crate::semantic::types::ObjectFlags::MEMBERS_RESOLVED));
                assert_eq!(query_counts(query.store), warm);
                assert!(query.diagnostics.is_empty());
            }
        }

        #[test]
        fn complete_any_identity_rejects_different_requests_and_preserves_untagged_fallback() {
            let parsed = cold_fixture();
            let mut checker = context(&parsed);
            let id = checker.get_type_from_type_node(cold_constraint(&parsed)).unwrap();
            let cells = symbol(&checker, alias(&parsed, "Cells").0);
            let target = alias_type(&parsed, &checker, "Cells");
            let parameters = checker.store().type_alias_links(cells).unwrap()
                .type_parameters.clone().unwrap();
            let any = checker.store().intrinsic_bootstrap().unwrap().any_type;
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let array = checker.global_types().array_type;
            let array_owner = checker.store().type_payload(array).unwrap().symbol().unwrap();
            let arrays = crate::semantic::array_types::CanonicalArrayTargets::from_global_types(
                checker.global_types(),
            );
            let warm = counts(&checker);
            assert_eq!(checker.store().complete_any_cached_identity_matches(
                cells, target, &parameters, &[any], None, id, Some(arrays),
            ), Ok(Some(true)));
            assert_eq!(checker.store().complete_any_cached_identity_matches(
                array_owner, target, &parameters, &[any], None, id, Some(arrays),
            ), Ok(Some(false)));
            assert_eq!(checker.store().complete_any_cached_identity_matches(
                cells, string, &parameters, &[any], None, id, Some(arrays),
            ), Ok(Some(false)));
            assert_eq!(checker.store().complete_any_cached_identity_matches(
                cells, target, &[string], &[any], None, id, Some(arrays),
            ), Ok(Some(false)));
            assert_eq!(checker.store().complete_any_cached_identity_matches(
                cells, target, &parameters, &[string], None, id, Some(arrays),
            ), Ok(Some(false)));
            assert_eq!(checker.store().complete_any_cached_identity_matches(
                cells, target, &parameters, &[any], Some((cells, &[any])), id, Some(arrays),
            ), Ok(Some(false)));
            assert_eq!(checker.store().complete_any_cached_identity_matches(
                cells, target, &parameters, &[any], None, target, Some(arrays),
            ), Ok(None));
            assert_eq!(counts(&checker), warm);
        }

        #[test]
        fn captured_complete_any_identity_rejects_damaged_rows_and_restores() {
            for physical in [false, true] {
                let parsed = cold_fixture();
                let mut checker = context(&parsed);
                let node = cold_constraint(&parsed);
                let id = checker.get_type_from_type_node(node).unwrap();
                let cells = symbol(&checker, alias(&parsed, "Cells").0);
                let target = alias_type(&parsed, &checker, "Cells");
                let before = mapped(&checker, id).clone();
                let physical_saved = physical_rows(&checker, target).clone();
                let logical_saved = checker.store().type_alias_links(cells).unwrap().clone();
                let bound = checker.file(FILE).unwrap().1.clone();
                let options = checker.options();
                let globals = checker.global_types().clone();
                let arrays = crate::semantic::array_types::CanonicalArrayTargets::from_global_types(&globals);
                let host = crate::semantic::DeclaredTypeHost::new_after_global_merge(
                    [(&parsed.arena, &bound)],
                    crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
                ).unwrap();
                let mut diagnostics = checker.diagnostics().clone();
                let mut session = super::InstantiationSession::new(super::InstantiationLimits::default());
                let warm = counts(&checker);
                let query = super::CanonicalTypeQuery::new_with_global_types_and_session(
                    checker.store_mut_for_test(), &host, &globals, options, &mut session, &mut diagnostics,
                ).unwrap();
                let live = query.source_query_context().unwrap();
                let mut planner = live.planner(query.store);
                planner.plan_type_node_in_context(node, None, false).unwrap();
                let plan = planner.finish();
                if physical {
                    let mut broken = physical_saved.clone();
                    let key = *broken.iter().find(|(_, result)| **result == id).unwrap().0;
                    broken.insert(key, target);
                    assert!(query.store.set_object_instantiations(target, TypeCacheState::Allocated(broken)));
                } else {
                    let mut broken = logical_saved.clone();
                    let rows = broken.instantiations.as_mut().unwrap();
                    let key = *rows.iter().find(|(_, result)| **result == id).unwrap().0;
                    rows.remove(&key);
                    assert!(query.store.set_type_alias_links(cells, broken));
                }
                assert!(plan.cached_type_query_result_with_source(
                    query.store, Some(arrays), None, &[], node,
                    super::SourceCallableTypeReplay::Identity,
                    &mut std::collections::HashSet::new(), None,
                ).is_err());
                assert!(query.store.set_object_instantiations(target, TypeCacheState::Allocated(physical_saved)));
                assert!(query.store.set_type_alias_links(cells, logical_saved));
                assert_eq!(plan.cached_type_query_result_with_source(
                    query.store, Some(arrays), None, &[], node,
                    super::SourceCallableTypeReplay::Identity,
                    &mut std::collections::HashSet::new(), None,
                ), Ok(Some(id)));
                let TypeData::Mapped(current) = query.store.type_payload(id).unwrap().data() else {
                    panic!("Identity replay must keep the mapped result");
                };
                assert_eq!(current, &before);
                assert_eq!(query_counts(query.store), warm);
                assert!(query.diagnostics.is_empty());
            }
        }

        #[test]
        fn complete_any_callable_capture_publication_and_stored_replay_keep_cold_identity() {
            let parsed = cold_fixture();
            let mut checker = context(&parsed);
            let constraint = cold_constraint(&parsed);
            let id = checker.get_type_from_type_node(constraint).unwrap();
            let declaration = parsed.arena.iter().find_map(|(node, record)| {
                matches!(&record.data, NodeData::FunctionDeclaration(_))
                    .then_some(NodeRef::new(parsed.arena.id(), FILE, node))
            }).unwrap();
            let owner = symbol(&checker, declaration);
            let bound = checker.file(FILE).unwrap().1.clone();
            let options = checker.options();
            let globals = checker.global_types().clone();
            let arrays = crate::semantic::array_types::CanonicalArrayTargets::from_global_types(&globals);
            let host = crate::semantic::DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
            ).unwrap();
            let mut diagnostics = checker.diagnostics().clone();
            let mut session = super::InstantiationSession::new(super::InstantiationLimits::default());
            let mut first = None;
            let mut warm = None;
            let mut cold = None;
            for _ in 0..4 {
                let callable_type = {
                    let mut query = super::CanonicalTypeQuery::new_with_global_types_and_session(
                        checker.store_mut_for_test(), &host, &globals, options, &mut session, &mut diagnostics,
                    ).unwrap();
                    query.preflight_type_of_source_callable(declaration, owner).unwrap();
                    query.get_type_of_source_callable(declaration, owner).unwrap()
                };
                let signature = checker.store().source_callable_provenance(callable_type)
                    .unwrap().signature;
                let returned = super::CanonicalTypeQuery::new_with_global_types_and_session(
                    checker.store_mut_for_test(), &host, &globals, options, &mut session, &mut diagnostics,
                ).unwrap().get_return_type_of_signature(signature).unwrap();
                let store = checker.store();
                assert_eq!(store.signature(signature).unwrap().type_parameters(), &[returned]);
                let TypeData::TypeParameter(parameter) = store.type_payload(returned).unwrap().data() else {
                    panic!("the callable return must keep P");
                };
                assert_eq!(parameter.constraint, Some(id));
                assert_eq!(parameter.constrained.resolved_base_constraint, Some(id));
                let evidence = store.source_callable_type_query(signature).unwrap();
                assert!(evidence.is_exact(store));
                assert_eq!(evidence.annotation_type(constraint), Some(id));
                assert_eq!(evidence.base_constraints(), &[id]);
                assert!(!store.type_payload(id).unwrap().object_flags()
                    .contains(crate::semantic::types::ObjectFlags::MEMBERS_RESOLVED));
                let current = (callable_type, signature, returned);
                let current_counts = (
                    counts(&checker), store.signature_len(), store.source_callable_provenance_lengths(),
                    session.query_count(), session.total_count(), session.limit_event_count(),
                );
                if let Some(expected) = first {
                    assert_eq!(current, expected);
                    assert_eq!(Some(current_counts), warm);
                    assert_eq!(Some(mapped(&checker, id)), cold.as_ref());
                } else {
                    first = Some(current);
                    warm = Some(current_counts);
                    cold = Some(mapped(&checker, id).clone());
                }
                let cells = symbol(&checker, alias(&parsed, "Cells").0);
                let target = alias_type(&parsed, &checker, "Cells");
                let parameters = store.type_alias_links(cells).unwrap().type_parameters.as_ref().unwrap();
                let any = store.intrinsic_bootstrap().unwrap().any_type;
                let error = crate::semantic::instantiate::cached_instantiation_with_vector(
                    store, target, parameters, &[any], Some(arrays), None,
                ).expect_err("Operational replay must still request Members after callable publication");
                let crate::semantic::instantiate::InstantiationError::Declared(error) = error else {
                    panic!("the Operational error must retain the declared demand");
                };
                assert_eq!(super::SourceQueryDemand::from_error(&error), Some(
                    super::SourceQueryDemand::Mapped(super::SourceMappedReadRequest::Members {
                        receiver: id,
                    }),
                ));
                assert_eq!(counts(&checker), current_counts.0);
                assert!(diagnostics.is_empty());
            }
        }
    };
}
