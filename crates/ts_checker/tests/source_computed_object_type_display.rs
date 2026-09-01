use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, types::ObjectFlags,
    TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(20_241);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/computed-object-type-display.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(FILE, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef, Option<NodeRef>) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    node(parsed, id),
                    node(parsed, variable.name),
                    variable.initializer.map(|id| node(parsed, id)),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn object(parsed: &ParseResult, name: &str) -> NodeRef {
    let initializer = variable(parsed, name).2.unwrap();
    match &parsed.arena.get(initializer.node).unwrap().data {
        NodeData::ObjectLiteralExpression(_) => initializer,
        NodeData::AsExpression(assertion) => node(parsed, assertion.expression),
        _ => panic!("expected an object initializer or its original const assertion"),
    }
}

fn source_types(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> [TypeId; 2] {
    let (declaration, name_node, initializer) = variable(parsed, name);
    let fresh = context.get_type_at_location(object(parsed, name)).unwrap();
    let inferred = context.get_type_at_location(name_node).unwrap();
    let symbol = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(symbol)
            .unwrap()
            .resolved_type,
        Some(inferred)
    );
    let const_assertion = matches!(
        parsed.arena.get(initializer.unwrap().node).unwrap().data,
        NodeData::AsExpression(_)
    );
    if const_assertion {
        assert_eq!(fresh, inferred);
    } else {
        assert_ne!(fresh, inferred);
    }
    assert!(
        context
            .store()
            .type_payload(fresh)
            .unwrap()
            .object_flags()
            .contains(ObjectFlags::FRESH_LITERAL)
    );
    assert_eq!(
        context
            .store()
            .type_payload(inferred)
            .unwrap()
            .object_flags()
            .contains(ObjectFlags::FRESH_LITERAL),
        const_assertion
    );
    [fresh, inferred]
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 6] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn assert_display_and_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    displays: &[(TypeId, &str)],
) {
    let before = counts(context);
    let diagnostics = context.diagnostics().clone();
    let links = parsed
        .arena
        .iter()
        .map(|(id, _)| {
            let location = node(parsed, id);
            (
                location,
                context.store().type_node_links(location).cloned(),
                context.store().symbol_node_links(location).cloned(),
                context.store().signature_links(location).cloned(),
            )
        })
        .collect::<Vec<_>>();
    for _ in 0..2 {
        for &(type_, expected) in displays {
            assert_eq!(context.type_to_string(type_).unwrap(), expected);
        }
        assert_eq!(
            counts(context),
            before,
            "display must not publish new types or members"
        );
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        for &(type_, expected) in displays {
            assert_eq!(context.type_to_string(type_).unwrap(), expected);
        }
        for (location, type_links, symbol_links, signature_links) in &links {
            assert_eq!(
                context.store().type_node_links(*location),
                type_links.as_ref()
            );
            assert_eq!(
                context.store().symbol_node_links(*location),
                symbol_links.as_ref()
            );
            assert_eq!(
                context.store().signature_links(*location),
                signature_links.as_ref()
            );
        }
        assert_eq!(counts(context), before);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
fn computed_literal_property_types_display_real_names_readonly_and_widened_identity() {
    let parsed = parse_source_file(concat!(
        "const label = 'value'; const quoted = 'not valid'; const position = 2;\n",
        "declare const input: number;\n",
        "const named = { [label]: input, [quoted]: input, [position]: input };\n",
        "const readonlyNamed = { [label]: input, [quoted]: input, [position]: input } as const;\n",
    ));
    for query_first in [false, true] {
        let mut context = context(&parsed);
        if query_first {
            context
                .get_type_at_location(object(&parsed, "named"))
                .unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let mut displays = Vec::new();
        for (name, expected) in [
            (
                "named",
                "{ value: number; \"not valid\": number; 2: number; }",
            ),
            (
                "readonlyNamed",
                "{ readonly value: number; readonly \"not valid\": number; readonly 2: number; }",
            ),
        ] {
            let types = source_types(&mut context, &parsed, name);
            let object_node = object(&parsed, name);
            let NodeData::ObjectLiteralExpression(source) =
                &parsed.arena.get(object_node.node).unwrap().data
            else {
                panic!("the original object must remain in the source")
            };
            for (&property, key_name) in source
                .properties
                .nodes
                .iter()
                .zip(["label", "quoted", "position"])
            {
                let NodeData::PropertyAssignment(property) =
                    &parsed.arena.get(property).unwrap().data
                else {
                    panic!("expected the original property assignment")
                };
                let NodeData::ComputedPropertyName(computed) =
                    &parsed.arena.get(property.name).unwrap().data
                else {
                    panic!("the display must use a checked computed key")
                };
                let key = node(&parsed, computed.expression);
                let symbol = context
                    .file(FILE)
                    .unwrap()
                    .1
                    .symbol(variable(&parsed, key_name).0)
                    .unwrap();
                assert_eq!(context.get_symbol_at_location(key).unwrap(), Some(symbol));
            }
            for type_ in types {
                let TypeData::Object(data) = context.store().type_payload(type_).unwrap().data()
                else {
                    panic!("expected a real object type")
                };
                assert_eq!(data.structured.properties.as_ref().unwrap().len(), 3);
                assert!(data.structured.index_infos.is_none());
                displays.push((type_, expected));
            }
        }
        assert!(context.diagnostics().is_empty());
        assert_display_and_replay(&mut context, &parsed, &displays);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Checks index domains, source components, and both display orders.
fn computed_scalar_index_types_display_fallback_names_components_and_readonly() {
    let parsed = parse_source_file(concat!(
        "declare const textKey: string; declare const numberKey: number; declare const input: number;\n",
        "const stringTable = { [textKey]: input };\n",
        "const numberTable = { [numberKey]: input };\n",
        "const mixed = { [textKey]: input, fixed: input, [numberKey]: input };\n",
        "const readonlyTable = { [textKey]: input } as const;\n",
    ));
    for query_first in [false, true] {
        let mut context = context(&parsed);
        if query_first {
            context
                .get_type_at_location(object(&parsed, "stringTable"))
                .unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        let mut displays = Vec::new();
        for (name, expected, domains, readonly) in [
            (
                "stringTable",
                "{ [x: string]: number; }",
                vec![string],
                false,
            ),
            (
                "numberTable",
                "{ [x: number]: number; }",
                vec![number],
                false,
            ),
            (
                "mixed",
                "{ [x: string]: number; [x: number]: number; fixed: number; }",
                vec![string, number],
                false,
            ),
            (
                "readonlyTable",
                "{ readonly [x: string]: number; }",
                vec![string],
                true,
            ),
        ] {
            let types = source_types(&mut context, &parsed, name);
            let object_node = object(&parsed, name);
            let NodeData::ObjectLiteralExpression(source) =
                &parsed.arena.get(object_node.node).unwrap().data
            else {
                panic!("expected the original object")
            };
            let computed = source
                .properties
                .nodes
                .iter()
                .filter_map(|&id| {
                    let NodeData::PropertyAssignment(property) = &parsed.arena.get(id)?.data else {
                        return None;
                    };
                    let NodeData::ComputedPropertyName(name) =
                        &parsed.arena.get(property.name)?.data
                    else {
                        return None;
                    };
                    Some((node(&parsed, id), node(&parsed, name.expression)))
                })
                .collect::<Vec<_>>();
            let mut original_indexes = Vec::new();
            for (type_index, type_) in types.into_iter().enumerate() {
                let TypeData::Object(data) = context.store().type_payload(type_).unwrap().data()
                else {
                    panic!("expected a real object type")
                };
                let indexes = data.structured.index_infos.as_ref().unwrap();
                assert_eq!(indexes.len(), domains.len());
                for (&index, &domain) in indexes.iter().zip(&domains) {
                    let info = context.store().index_info(index).unwrap();
                    assert_eq!(info.key_type(), domain);
                    assert_eq!(info.value_type(), number);
                    assert_eq!(info.is_readonly(), readonly);
                    assert_eq!(info.declaration(), None);
                    assert_eq!(info.index_symbol(), None);
                    let components = computed
                        .iter()
                        .filter_map(|&(property, key)| {
                            let key_type = context
                                .store()
                                .type_node_links(key)
                                .unwrap()
                                .resolved_type
                                .unwrap();
                            (domain == string || key_type == number).then_some(property)
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(info.components(), components);
                }
                if type_index == 0 {
                    original_indexes = indexes.clone();
                } else if readonly {
                    assert_eq!(&original_indexes, indexes);
                } else {
                    assert!(
                        original_indexes
                            .iter()
                            .zip(indexes)
                            .all(|(fresh, widened)| fresh != widened)
                    );
                }
                displays.push((type_, expected));
            }
        }
        assert!(context.diagnostics().is_empty());
        assert_display_and_replay(&mut context, &parsed, &displays);
    }
}
