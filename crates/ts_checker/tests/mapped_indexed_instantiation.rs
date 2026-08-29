use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeMapperStore, DeclaredTypeLinks,
    GenericInterfaceArrayTarget, GenericInterfaceMemberError, IntrinsicBootstrapOptions, TypeData,
    TypeId, TypeNodeLinks, ValueSymbolLinks,
    type_records::CacheHashKey,
    types::{AccessFlags, ObjectFlags},
};
use ts_parser::{ParseResult, parse_source_file};
use xxhash_rust::xxh3::Xxh3;

fn type_list_key(types: &[TypeId]) -> CacheHashKey {
    let mut hasher = Xxh3::new();
    hasher.update(&(types.len() as u64).to_le_bytes());
    for type_ in types {
        hasher.update(&type_.get().to_le_bytes());
    }
    CacheHashKey::new(hasher.digest128())
}

fn source_alias_type(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    name: &str,
) -> TypeId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap();
    let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context
        .store()
        .type_alias_links(symbol)
        .unwrap()
        .declared_type
        .unwrap()
}

fn interface_target(
    store: &mut CanonicalTypeMapperStore,
    parsed: &ParseResult,
    bound: &BoundFile,
    file: FileId,
    name: &str,
) -> (TypeId, Vec<TypeId>) {
    let (node, interface) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some((node, interface))
        })
        .unwrap();
    let owner = bound
        .symbol(NodeRef::new(parsed.arena.id(), file, node))
        .unwrap();
    let mut parameters = Vec::new();
    for node in &interface.type_parameters.as_ref().unwrap().nodes {
        let symbol = bound
            .symbol(NodeRef::new(parsed.arena.id(), file, *node))
            .unwrap();
        let parameter = store.alloc_type_parameter(Some(symbol)).unwrap();
        assert!(store.set_declared_type_links(
            symbol,
            DeclaredTypeLinks {
                declared_type: Some(parameter),
                ..DeclaredTypeLinks::default()
            },
        ));
        parameters.push(parameter);
    }
    let target = store
        .alloc_interface_type(ObjectFlags::INTERFACE, Some(owner))
        .unwrap();
    assert!(store.set_declared_type_links(
        owner,
        DeclaredTypeLinks {
            declared_type: Some(target),
            ..DeclaredTypeLinks::default()
        },
    ));
    let this_type = store.alloc_type_parameter(Some(owner)).unwrap();
    let mut all_parameters = parameters.clone();
    all_parameters.push(this_type);
    assert!(store.initialize_interface_type_parameters(
        target,
        all_parameters,
        0,
        this_type,
        type_list_key(&parameters),
    ));
    assert!(store.set_interface_base_resolution(target, true, None, None));
    (target, parameters)
}

fn dictionary_interface(
    store: &mut CanonicalTypeMapperStore,
    parsed: &ParseResult,
    bound: &BoundFile,
    file: FileId,
    name: &str,
) -> TypeId {
    fn annotation_type(
        store: &mut CanonicalTypeMapperStore,
        parsed: &ParseResult,
        node: NodeRef,
    ) -> TypeId {
        let record = parsed.arena.get(node.node).unwrap();
        let type_ = match record.kind {
            SyntaxKind::StringKeyword => store.intrinsic_bootstrap().unwrap().string_type,
            SyntaxKind::NumberKeyword => store.intrinsic_bootstrap().unwrap().number_type,
            SyntaxKind::LiteralType => {
                let NodeData::LiteralTypeNode(literal) = &record.data else {
                    unreachable!()
                };
                let NodeData::StringLiteral(literal) =
                    &parsed.arena.get(literal.literal).unwrap().data
                else {
                    panic!("the dictionary fixture uses string literal values")
                };
                store
                    .get_template_literal_type(&[literal.text.clone()], &[])
                    .unwrap()
            }
            _ => panic!("unexpected dictionary annotation"),
        };
        assert!(store.set_type_node_links(
            node,
            TypeNodeLinks {
                resolved_type: Some(type_),
                ..TypeNodeLinks::default()
            },
        ));
        type_
    }

    let (node, interface) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some((node, interface))
        })
        .unwrap();
    assert!(interface.type_parameters.is_none());
    let owner = bound
        .symbol(NodeRef::new(parsed.arena.id(), file, node))
        .unwrap();
    let target = store
        .alloc_interface_type(ObjectFlags::INTERFACE, Some(owner))
        .unwrap();
    assert!(store.set_declared_type_links(
        owner,
        DeclaredTypeLinks {
            declared_type: Some(target),
            ..DeclaredTypeLinks::default()
        },
    ));
    assert!(store.set_interface_base_resolution(target, true, None, None));
    let members = store.symbol(owner).unwrap().members().unwrap();
    let mut properties = Vec::new();
    let mut indexes = Vec::new();
    for node in &interface.members.nodes {
        let declaration = NodeRef::new(parsed.arena.id(), file, *node);
        match &parsed.arena.get(*node).unwrap().data {
            NodeData::IndexSignatureDeclaration(index) => {
                let NodeData::ParameterDeclaration(parameter) =
                    &parsed.arena.get(index.parameters.nodes[0]).unwrap().data
                else {
                    unreachable!()
                };
                let key = annotation_type(
                    store,
                    parsed,
                    NodeRef::new(parsed.arena.id(), file, parameter.type_.unwrap()),
                );
                let value = annotation_type(
                    store,
                    parsed,
                    NodeRef::new(parsed.arena.id(), file, index.type_),
                );
                indexes.push(
                    store
                        .alloc_index_info(key, value, false, Some(declaration), Vec::new())
                        .unwrap(),
                );
            }
            NodeData::PropertyDeclaration(property) => {
                let symbol = bound.symbol(declaration).unwrap();
                let value = annotation_type(
                    store,
                    parsed,
                    NodeRef::new(parsed.arena.id(), file, property.type_.unwrap()),
                );
                assert!(store.set_value_symbol_links(
                    symbol,
                    ValueSymbolLinks {
                        resolved_type: Some(value),
                        ..ValueSymbolLinks::default()
                    },
                ));
                properties.push(symbol);
            }
            _ => panic!("unexpected dictionary member"),
        }
    }
    assert!(store.set_interface_declared_members(
        target,
        true,
        Some(members),
        None,
        None,
        Some(indexes.clone()),
    ));
    assert!(store.set_structured_type_members(
        target,
        Some(members),
        (!properties.is_empty()).then_some(properties),
        None,
        None,
        Some(indexes),
    ));
    target
}

struct Fixture {
    store: CanonicalTypeMapperStore,
    array: TypeId,
    lookup: TypeId,
    object: TypeId,
    index: TypeId,
    template: TypeId,
    dictionary: TypeId,
    string_dictionary: TypeId,
}

impl Fixture {
    fn new(array_name: &str, flags: AccessFlags, exact_optional_property_types: bool) -> Self {
        let source = format!(
            "interface {array_name}<E> {{}}\n\
             interface Lookup<T, K> {{ value: {array_name}<T[K]> }}\n\
             interface Dict {{ named: \"property\"; [key: string]: string; [key: number]: \"numeric\" }}\n\
             interface StringDict {{ [key: string]: string }}\n"
        );
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(0);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/indexed-instantiation.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types,
            })
            .unwrap();
        let (array, _) = interface_target(&mut store, &parsed, &bound, file, array_name);
        assert!(store.set_interface_declared_members(array, true, None, None, None, None));
        let (lookup, parameters) = interface_target(&mut store, &parsed, &bound, file, "Lookup");
        let [object, index] = parameters.as_slice() else {
            panic!("Lookup must have two type parameters")
        };
        let (object, index) = (*object, *index);
        let indexed = store
            .alloc_indexed_access_type(object, index, flags)
            .unwrap();
        // A reference argument reaches the shared instantiation worker.
        let template = store
            .create_direct_generic_reference_type(array, &[indexed])
            .unwrap();
        let owner = store.type_payload(lookup).unwrap().symbol().unwrap();
        let raw_members = store.symbol(owner).unwrap().members().unwrap();
        let property = store
            .symbol_table(raw_members)
            .unwrap()
            .get_source("value")
            .unwrap();
        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(template),
                ..ValueSymbolLinks::default()
            },
        ));
        let members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(members, EscapedName::source("value"), property),
            Some(None),
        );
        assert!(store.set_interface_declared_members(
            lookup,
            true,
            Some(members),
            None,
            None,
            None,
        ));
        assert_eq!(store.symbol(owner).unwrap().members(), Some(raw_members));
        assert_ne!(members, raw_members);
        let dictionary = dictionary_interface(&mut store, &parsed, &bound, file, "Dict");
        let string_dictionary =
            dictionary_interface(&mut store, &parsed, &bound, file, "StringDict");
        Self {
            store,
            array,
            lookup,
            object,
            index,
            template,
            dictionary,
            string_dictionary,
        }
    }

    fn reference(&mut self, object: TypeId, index: TypeId) -> TypeId {
        self.store
            .create_direct_generic_reference_type(self.lookup, &[object, index])
            .unwrap()
    }

    fn array_of(&mut self, element: TypeId) -> TypeId {
        self.store
            .create_direct_generic_reference_type(self.array, &[element])
            .unwrap()
    }

    fn array_element(&self, type_: TypeId) -> TypeId {
        let TypeData::TypeReference(reference) = self.store.type_payload(type_).unwrap().data()
        else {
            panic!("the mapped value must remain an array reference")
        };
        assert_eq!(reference.object.target, Some(self.array));
        let [element] = reference.resolved_type_arguments.as_deref().unwrap() else {
            panic!("an array has one element argument")
        };
        *element
    }

    fn counts(&self) -> (usize, usize, usize, usize) {
        (
            self.store.type_len(),
            self.store.mapper_len(),
            self.store.symbol_len(),
            self.store.index_info_len(),
        )
    }
}

#[test]
fn indexed_array_reads_preserve_missing_in_reference_arguments_cold_and_warm() {
    for array_name in ["Array", "ReadonlyArray"] {
        for exact in [false, true] {
            for flags in [AccessFlags::NONE, AccessFlags::INCLUDE_UNDEFINED] {
                let mut fixture = Fixture::new(array_name, flags, exact);
                let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
                let (string, number, missing, undefined) = (
                    bootstrap.string_type,
                    bootstrap.number_type,
                    bootstrap.missing_type,
                    bootstrap.undefined_type,
                );
                let source_array = fixture.array_of(string);
                let reference = fixture.reference(source_array, number);
                let capability = Some(GenericInterfaceArrayTarget::new(fixture.array));
                let property = fixture
                    .store
                    .resolve_generic_interface_property(reference, "value", capability)
                    .unwrap()
                    .unwrap();
                let element = fixture.array_element(property.type_id());
                if flags == AccessFlags::NONE {
                    assert_eq!(element, string);
                } else {
                    let TypeData::Union(union) =
                        fixture.store.type_payload(element).unwrap().data()
                    else {
                        panic!("an unchecked array read must include missing")
                    };
                    assert_eq!(union.union.types.len(), 2);
                    assert!(union.union.types.contains(&string));
                    assert!(union.union.types.contains(&missing));
                    assert!(!union.union.types.contains(&undefined));
                }
                let warm = fixture.counts();
                assert_eq!(
                    fixture
                        .store
                        .resolve_generic_interface_property(reference, "value", capability),
                    Ok(Some(property)),
                );
                assert_eq!(fixture.counts(), warm);
            }
        }
    }
}

#[test]
fn unknown_with_a_generic_index_stays_unknown_inside_a_reference() {
    for flags in [AccessFlags::NONE, AccessFlags::INCLUDE_UNDEFINED] {
        let mut fixture = Fixture::new("Array", flags, false);
        let unknown = fixture.store.intrinsic_bootstrap().unwrap().unknown_type;
        let reference = fixture.reference(unknown, fixture.index);
        let capability = Some(GenericInterfaceArrayTarget::new(fixture.array));
        let property = fixture
            .store
            .resolve_generic_interface_property(reference, "value", capability)
            .unwrap()
            .unwrap();
        assert_eq!(fixture.array_element(property.type_id()), unknown);
        let warm = fixture.counts();
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_property(reference, "value", capability),
            Ok(Some(property)),
        );
        assert_eq!(fixture.counts(), warm);
    }
}

#[test]
fn warm_indexed_reads_reject_a_cached_value_without_missing() {
    let mut fixture = Fixture::new("Array", AccessFlags::INCLUDE_UNDEFINED, false);
    let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
    let (string, number) = (bootstrap.string_type, bootstrap.number_type);
    let source_array = fixture.array_of(string);
    let reference = fixture.reference(source_array, number);
    let capability = Some(GenericInterfaceArrayTarget::new(fixture.array));
    let property = fixture
        .store
        .resolve_generic_interface_property(reference, "value", capability)
        .unwrap()
        .unwrap();
    let mut links = fixture
        .store
        .value_symbol_links(property.symbol())
        .unwrap()
        .clone();
    links.resolved_type = Some(source_array);
    assert!(
        fixture
            .store
            .set_value_symbol_links(property.symbol(), links)
    );
    let before = fixture.counts();
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_property(reference, "value", capability),
        Err(GenericInterfaceMemberError::InvalidCachedProperty(
            property.symbol()
        )),
    );
    assert_eq!(fixture.counts(), before);
}

#[test]
fn index_signature_values_use_the_same_nested_indexed_instantiation() {
    let mut fixture = Fixture::new("Array", AccessFlags::INCLUDE_UNDEFINED, false);
    let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
    let (string, number, missing) = (
        bootstrap.string_type,
        bootstrap.number_type,
        bootstrap.missing_type,
    );
    let source_array = fixture.array_of(string);
    let reference = fixture.reference(source_array, number);
    let mapper = fixture
        .store
        .new_type_mapper(
            vec![fixture.object, fixture.index],
            vec![source_array, number],
        )
        .unwrap();
    let index = fixture
        .store
        .alloc_index_info(string, fixture.template, true, None, Vec::new())
        .unwrap();
    let mapped = fixture
        .store
        .instantiate_generic_interface_index_info(
            reference,
            index,
            mapper,
            Some(GenericInterfaceArrayTarget::new(fixture.array)),
        )
        .unwrap();
    let info = fixture.store.index_info(mapped).unwrap();
    assert_eq!(info.key_type(), string);
    assert!(info.is_readonly());
    let element = fixture.array_element(info.value_type());
    let TypeData::Union(union) = fixture.store.type_payload(element).unwrap().data() else {
        panic!("the nested indexed value must include missing")
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&string));
    assert!(union.union.types.contains(&missing));
}

#[test]
fn nested_index_signatures_select_exact_keys_and_reuse_warm_results() {
    for exact in [false, true] {
        for flags in [AccessFlags::NONE, AccessFlags::INCLUDE_UNDEFINED] {
            let mut fixture = Fixture::new("Array", flags, exact);
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, number, symbol, missing, undefined, numeric, named) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.es_symbol_type,
                bootstrap.missing_type,
                bootstrap.undefined_type,
                bootstrap.cached_string_literal_type("numeric").unwrap(),
                bootstrap.cached_string_literal_type("property").unwrap(),
            );
            let mut cases = vec![
                (fixture.dictionary, string, string, false),
                (fixture.dictionary, number, numeric, false),
                (fixture.string_dictionary, number, string, false),
                (fixture.string_dictionary, symbol, string, false),
            ];
            for (key, value, own_property) in [
                ("1", numeric, false),
                ("01", string, false),
                ("other", string, false),
                ("named", named, true),
            ] {
                let key = fixture
                    .store
                    .get_template_literal_type(&[key.to_owned()], &[])
                    .unwrap();
                cases.push((fixture.dictionary, key, value, own_property));
            }
            for (object, index, expected, own_property) in cases {
                let reference = fixture.reference(object, index);
                let capability = Some(GenericInterfaceArrayTarget::new(fixture.array));
                let property = fixture
                    .store
                    .resolve_generic_interface_property(reference, "value", capability)
                    .unwrap()
                    .unwrap();
                let value = fixture.array_element(property.type_id());
                if flags == AccessFlags::INCLUDE_UNDEFINED && !own_property {
                    let TypeData::Union(union) = fixture.store.type_payload(value).unwrap().data()
                    else {
                        panic!("an unchecked index signature read must include missing")
                    };
                    assert_eq!(union.union.types.len(), 2);
                    assert!(union.union.types.contains(&expected));
                    assert!(union.union.types.contains(&missing));
                    assert!(!union.union.types.contains(&undefined));
                } else {
                    assert_eq!(value, expected);
                }
                let warm = fixture.counts();
                assert_eq!(
                    fixture
                        .store
                        .resolve_generic_interface_property(reference, "value", capability),
                    Ok(Some(property)),
                );
                assert_eq!(fixture.counts(), warm);
            }
        }
    }
}

#[test]
fn nested_index_signature_reads_reject_a_wrong_warm_value() {
    let mut fixture = Fixture::new("Array", AccessFlags::INCLUDE_UNDEFINED, false);
    let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
    let reference = fixture.reference(fixture.string_dictionary, string);
    let capability = Some(GenericInterfaceArrayTarget::new(fixture.array));
    let property = fixture
        .store
        .resolve_generic_interface_property(reference, "value", capability)
        .unwrap()
        .unwrap();
    let wrong = fixture.array_of(string);
    let mut links = fixture
        .store
        .value_symbol_links(property.symbol())
        .unwrap()
        .clone();
    links.resolved_type = Some(wrong);
    assert!(
        fixture
            .store
            .set_value_symbol_links(property.symbol(), links)
    );
    let before = fixture.counts();
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_property(reference, "value", capability),
        Err(GenericInterfaceMemberError::InvalidCachedProperty(
            property.symbol()
        )),
    );
    assert_eq!(fixture.counts(), before);
}

#[test]
fn nested_mapped_index_signatures_keep_the_value_alias() {
    let parsed = parse_source_file(concat!(
        "type IndexValue = string | number; ",
        "interface Wrapper<Value> { value: Value } ",
        "interface Dict { [key: string]: IndexValue } ",
        "type Cells<Model> = { [Key in keyof Model]: Wrapper<Model[Key]> }; ",
        "type Concrete = Cells<Dict>; ",
        "type Expected = { [key: string]: Wrapper<IndexValue> };",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/nested-mapped-index.ts\""),
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
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: true,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();
    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    let concrete = source_alias_type(&context, &parsed, file, "Concrete");
    let expected = source_alias_type(&context, &parsed, file, "Expected");
    let expected_value = source_alias_type(&context, &parsed, file, "IndexValue");
    let value_alias = context
        .store()
        .type_payload(expected_value)
        .unwrap()
        .alias();
    assert!(value_alias.is_some());
    assert!(context.is_type_assignable_to(concrete, expected).unwrap());
    let store = context.store();
    let TypeData::Mapped(mapped) = store.type_payload(concrete).unwrap().data() else {
        panic!("the concrete alias must retain its mapped type")
    };
    let [index] = mapped.object.structured.index_infos.as_deref().unwrap() else {
        panic!("the mapped dictionary must have one string index")
    };
    let index = *index;
    let info = store.index_info(index).unwrap();
    assert_eq!(
        info.key_type(),
        store.intrinsic_bootstrap().unwrap().string_type
    );
    let value = info.value_type();
    let TypeData::TypeReference(reference) = store.type_payload(value).unwrap().data() else {
        panic!("the index value must remain a Wrapper reference")
    };
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[expected_value][..])
    );
    assert_eq!(
        store.type_payload(expected_value).unwrap().alias(),
        value_alias
    );
    let counts = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            store.type_len(),
            store.symbol_len(),
            store.mapper_len(),
            store.index_info_len(),
        )
    };
    let warm = counts(&context);
    context.recheck_source_file(file).unwrap();
    assert!(context.is_type_assignable_to(concrete, expected).unwrap());
    assert_eq!(
        context.store().index_info(index).unwrap().value_type(),
        value
    );
    assert_eq!(counts(&context), warm);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn optional_property_relations_distribute_stored_unions_by_relation_kind() {
    let parsed = parse_source_file(concat!(
        "type StoredOptional = { value: string | undefined }; ",
        "type Mixed = { value: string | number }; ",
        "type OptionalText = { value?: string }; ",
        "type OptionalBoolean = { value?: boolean };",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/optional-property-unions.ts\""),
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
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();
    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    let stored = source_alias_type(&context, &parsed, file, "StoredOptional");
    let mixed = source_alias_type(&context, &parsed, file, "Mixed");
    let text = source_alias_type(&context, &parsed, file, "OptionalText");
    let boolean = source_alias_type(&context, &parsed, file, "OptionalBoolean");
    let type_count = context.store().type_len();
    for _ in 0..2 {
        assert_eq!(context.is_type_assignable_to(stored, text), Ok(true));
        assert_eq!(context.is_type_assignable_to(mixed, text), Ok(false));
        assert_eq!(context.is_type_comparable_to(mixed, text), Ok(true));
        assert_eq!(context.is_type_assignable_to(mixed, boolean), Ok(false));
        assert_eq!(context.is_type_comparable_to(mixed, boolean), Ok(false));
        assert_eq!(context.store().type_len(), type_count);
    }
}

#[test]
fn nested_optional_reads_preserve_aliases_and_mapped_void_values() {
    let parsed = parse_source_file(concat!(
        "type DeclaredValue = number | undefined; ",
        "interface Wrapper<Value> { value: Value } ",
        "interface Shape { item?: DeclaredValue; empty?: void } ",
        "type Cells<Model> = { [Key in keyof Model]: Wrapper<Model[Key]> }; ",
        "type VoidProps<Model> = { [Key in keyof Model]: void }; ",
        "type Raw = Cells<Shape>; ",
        "type Mapped = Cells<VoidProps<Shape>>; ",
        "type ExpectedRaw = { item?: Wrapper<DeclaredValue>; empty?: Wrapper<void | undefined> }; ",
        "type ExpectedMapped = { item?: Wrapper<void>; empty?: Wrapper<void> };",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/optional-indexed-values.ts\""),
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
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();
    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    let raw = source_alias_type(&context, &parsed, file, "Raw");
    let mapped = source_alias_type(&context, &parsed, file, "Mapped");
    let expected_raw = source_alias_type(&context, &parsed, file, "ExpectedRaw");
    let expected_mapped = source_alias_type(&context, &parsed, file, "ExpectedMapped");
    let declared = source_alias_type(&context, &parsed, file, "DeclaredValue");
    let declared_alias = context.store().type_payload(declared).unwrap().alias();
    assert!(declared_alias.is_some());
    assert_eq!(context.is_type_assignable_to(raw, expected_raw), Ok(true));
    assert_eq!(
        context.is_type_assignable_to(mapped, expected_mapped),
        Ok(true)
    );

    let property_argument = |context: &CanonicalCheckerContext<'_>, owner: TypeId, name: &str| {
        let store = context.store();
        let TypeData::Mapped(mapped) = store.type_payload(owner).unwrap().data() else {
            panic!("the owner must retain its mapped type")
        };
        let property = store
            .symbol_table(mapped.object.structured.members.unwrap())
            .unwrap()
            .get_source(name)
            .unwrap();
        let value = store
            .value_symbol_links(property)
            .unwrap()
            .resolved_type
            .unwrap();
        let wrapper = match store.type_payload(value).unwrap().data() {
            TypeData::Union(union) => *union
                .union
                .types
                .iter()
                .find(|type_| {
                    matches!(
                        store.type_payload(**type_).map(|record| record.data()),
                        Some(TypeData::TypeReference(_))
                    )
                })
                .unwrap(),
            TypeData::TypeReference(_) => value,
            _ => panic!("the property must contain its Wrapper reference"),
        };
        let TypeData::TypeReference(reference) = store.type_payload(wrapper).unwrap().data() else {
            unreachable!()
        };
        let [argument] = reference.resolved_type_arguments.as_deref().unwrap() else {
            panic!("Wrapper must retain one type argument")
        };
        (value, *argument)
    };
    let raw_item = property_argument(&context, raw, "item");
    let raw_empty = property_argument(&context, raw, "empty");
    let mapped_item = property_argument(&context, mapped, "item");
    let mapped_empty = property_argument(&context, mapped, "empty");
    assert_eq!(raw_item.1, declared);
    assert_eq!(
        context.store().type_payload(raw_item.1).unwrap().alias(),
        declared_alias
    );
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let TypeData::Union(union) = context.store().type_payload(raw_empty.1).unwrap().data() else {
        panic!("a raw optional void declaration includes undefined")
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&bootstrap.void_type));
    assert!(union.union.types.contains(&bootstrap.undefined_type));
    assert!(!union.union.types.contains(&bootstrap.missing_type));
    assert_eq!(mapped_item.1, bootstrap.void_type);
    assert_eq!(mapped_empty.1, bootstrap.void_type);
    let counts = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            store.type_len(),
            store.type_alias_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.index_info_len(),
        )
    };
    let warm = counts(&context);
    context.recheck_source_file(file).unwrap();
    assert_eq!(context.is_type_assignable_to(raw, expected_raw), Ok(true));
    assert_eq!(
        context.is_type_assignable_to(mapped, expected_mapped),
        Ok(true)
    );
    assert_eq!(property_argument(&context, raw, "item"), raw_item);
    assert_eq!(property_argument(&context, raw, "empty"), raw_empty);
    assert_eq!(property_argument(&context, mapped, "item"), mapped_item);
    assert_eq!(property_argument(&context, mapped, "empty"), mapped_empty);
    assert_eq!(counts(&context), warm);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn nested_mapped_property_instantiation_keeps_the_optional_sentinel() {
    let parsed = parse_source_file(concat!(
        "interface Wrapper<Value> { value: Value } ",
        "interface Shape { item?: number } ",
        "type Cells<Model> = { [Key in keyof Model]: Wrapper<Model[Key]> }; ",
        "type Concrete = Cells<Shape>; ",
        "type Expected = { item?: Wrapper<number | undefined> };",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    for (strict, exact) in [(false, false), (true, false), (true, true)] {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/nested-mapped-property.ts\""),
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
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: strict,
                    exact_optional_property_types: exact,
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let concrete = source_alias_type(&context, &parsed, file, "Concrete");
        let expected = source_alias_type(&context, &parsed, file, "Expected");
        assert!(context.is_type_assignable_to(concrete, expected).unwrap());
        let store = context.store();
        let TypeData::Mapped(mapped) = store.type_payload(concrete).unwrap().data() else {
            panic!("the concrete alias must retain its mapped type")
        };
        let property = store
            .symbol_table(mapped.object.structured.members.unwrap())
            .unwrap()
            .get_source("item")
            .unwrap();
        let value = store
            .value_symbol_links(property)
            .unwrap()
            .resolved_type
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let wrapper = match store.type_payload(value).unwrap().data() {
            TypeData::Union(union) => *union
                .union
                .types
                .iter()
                .find(|type_| {
                    matches!(
                        store.type_payload(**type_).map(|record| record.data()),
                        Some(TypeData::TypeReference(_))
                    )
                })
                .unwrap(),
            TypeData::TypeReference(_) => value,
            _ => panic!("the mapped property must contain its Wrapper reference"),
        };
        let TypeData::TypeReference(reference) = store.type_payload(wrapper).unwrap().data() else {
            unreachable!()
        };
        let [argument] = reference.resolved_type_arguments.as_deref().unwrap() else {
            panic!("Wrapper must retain one type argument")
        };
        if strict {
            let TypeData::Union(union) = store.type_payload(*argument).unwrap().data() else {
                panic!("the nested optional value must keep its declared union")
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&bootstrap.number_type));
            assert!(
                union
                    .union
                    .types
                    .contains(&bootstrap.undefined_or_missing_type)
            );
            if exact {
                assert!(!union.union.types.contains(&bootstrap.undefined_type));
            }
        } else {
            assert_eq!(*argument, bootstrap.number_type);
        }
        let counts = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            (
                store.type_len(),
                store.symbol_len(),
                store.mapper_len(),
                store.index_info_len(),
            )
        };
        let warm = counts(&context);
        context.recheck_source_file(file).unwrap();
        assert!(context.is_type_assignable_to(concrete, expected).unwrap());
        assert_eq!(
            context
                .store()
                .value_symbol_links(property)
                .unwrap()
                .resolved_type,
            Some(value)
        );
        assert_eq!(counts(&context), warm, "strict={strict}, exact={exact}");
        assert!(context.diagnostics().is_empty());
    }
}
