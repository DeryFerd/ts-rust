use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(20_240);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/computed-object-keys.ts\""),
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

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, Option<NodeRef>) {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    node(parsed, variable.name),
                    variable.initializer.map(|id| node(parsed, id)),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

#[derive(Clone, Copy)]
struct Property {
    declaration: NodeRef,
    key: NodeRef,
    value: NodeRef,
}

fn properties(parsed: &ParseResult, object: NodeRef) -> Vec<Property> {
    let NodeData::ObjectLiteralExpression(object) = &parsed.arena.get(object.node).unwrap().data
    else {
        panic!("expected the original object literal")
    };
    object
        .properties
        .nodes
        .iter()
        .map(|&id| {
            let NodeData::PropertyAssignment(property) = &parsed.arena.get(id).unwrap().data else {
                panic!("expected a property assignment")
            };
            let NodeData::ComputedPropertyName(computed) =
                &parsed.arena.get(property.name).unwrap().data
            else {
                panic!("expected the original computed property name")
            };
            Property {
                declaration: node(parsed, id),
                key: node(parsed, computed.expression),
                value: node(parsed, property.initializer),
            }
        })
        .collect()
}

fn raw_property(
    context: &CanonicalCheckerContext<'_>,
    object: NodeRef,
    property: Property,
) -> SemanticSymbolId {
    let bound = context.file(FILE).unwrap().1;
    let owner = bound.symbol(object).unwrap();
    let symbol = bound.symbol(property.declaration).unwrap();
    let record = context.store().symbol(symbol).unwrap();
    assert_eq!(record.name(), InternalSymbolName::Computed.as_ref());
    assert_eq!(record.parent(), Some(owner));
    assert_eq!(record.declarations(), Some(&[property.declaration][..]));
    assert_eq!(record.value_declaration(), Some(property.declaration));
    assert_ne!(symbol, owner);
    symbol
}

fn resolved(context: &CanonicalCheckerContext<'_>, location: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(location)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing type for {location:?}"))
}

fn assert_index(
    context: &CanonicalCheckerContext<'_>,
    object: NodeRef,
    key: TypeId,
    value: TypeId,
    components: &[NodeRef],
) {
    let record = context
        .store()
        .type_payload(resolved(context, object))
        .unwrap();
    assert_eq!(
        record.symbol(),
        context.file(FILE).unwrap().1.symbol(object)
    );
    let TypeData::Object(object) = record.data() else {
        panic!("computed keys must produce an object type")
    };
    assert!(
        object
            .structured
            .properties
            .as_deref()
            .unwrap_or_default()
            .is_empty()
    );
    assert!(
        context
            .store()
            .symbol_table(object.structured.members.unwrap())
            .unwrap()
            .is_empty()
    );
    let [index] = object.structured.index_infos.as_deref().unwrap() else {
        panic!("expected one real index signature, not a named property")
    };
    let info = context.store().index_info(*index).unwrap();
    assert_eq!(info.key_type(), key);
    assert_eq!(info.value_type(), value);
    assert_eq!(info.components(), components);
    assert_eq!(info.declaration(), None);
    assert_eq!(info.index_symbol(), None);
    assert!(!info.is_readonly());
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.type_alias_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let before = counts(context);
    let diagnostics = context.diagnostics().clone();
    let nodes = parsed
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
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        for (location, type_links, symbol_links, signature_links) in &nodes {
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
        assert_eq!(context.diagnostics(), &diagnostics);
        assert_eq!(counts(context), before);
    }
}

#[test]
fn broad_computed_object_keys_keep_index_types_source_identity_and_assignment_errors() {
    let source = concat!(
        "declare const key: string;\n",
        "declare const position: number;\n",
        "declare const input: number;\n",
        "const object = { [key]: input };\n",
        "const numbered = { [position]: input + 1 };\n",
        "const okay: number = object[key];\n",
        "const numeric: number = numbered[position];\n",
        "const bad: string = object[key];\n",
    );
    let parsed = parse_source_file(source);
    let object = variable(&parsed, "object").1.unwrap();
    let numbered = variable(&parsed, "numbered").1.unwrap();
    for query_first in [false, true] {
        let mut context = context(&parsed);
        if query_first {
            context.get_type_at_location(object).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        for (object, key_type, key_name) in
            [(object, string, "key"), (numbered, number, "position")]
        {
            let [property] = properties(&parsed, object)[..] else {
                panic!("each control has one computed property")
            };
            raw_property(&context, object, property);
            assert_eq!(resolved(&context, property.key), key_type);
            assert_eq!(resolved(&context, property.value), number);
            assert_index(&context, object, key_type, number, &[property.declaration]);
            assert_eq!(
                context.get_type_at_location(property.key).unwrap(),
                key_type
            );
            let key_symbol = context
                .get_symbol_at_location(variable(&parsed, key_name).0)
                .unwrap()
                .unwrap();
            assert_eq!(
                context.get_symbol_at_location(property.key).unwrap(),
                Some(key_symbol)
            );
        }
        for name in ["okay", "numeric", "bad"] {
            assert_eq!(
                resolved(&context, variable(&parsed, name).1.unwrap()),
                number
            );
        }
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("only the wrong value assignment must fail")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.node, Some(variable(&parsed, "bad").0));
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert_replay(&mut context, &parsed);
    }
}

#[test]
fn bound_literal_object_keys_keep_real_property_names_and_key_types() {
    let parsed = parse_source_file(concat!(
        "const key = 'value';\n",
        "const position = 2;\n",
        "declare const input: number;\n",
        "const object = { [key]: input, [position]: input + 1 };\n",
        "const named: number = object.value;\n",
        "const numeric: number = object[2];\n",
    ));
    let object = variable(&parsed, "object").1.unwrap();
    for query_first in [false, true] {
        let mut context = context(&parsed);
        if query_first {
            context.get_type_at_location(object).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        assert!(context.diagnostics().is_empty());
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let parts = properties(&parsed, object);
        let TypeData::Object(object_type) = context
            .store()
            .type_payload(resolved(&context, object))
            .unwrap()
            .data()
        else {
            panic!("literal keys must produce named object properties")
        };
        assert!(
            object_type
                .structured
                .index_infos
                .as_deref()
                .unwrap_or_default()
                .is_empty()
        );
        let published = object_type.structured.properties.as_ref().unwrap().clone();
        assert_eq!(published.len(), 2);
        for ((property, symbol), (name, display, key_name)) in parts
            .iter()
            .zip(published)
            .zip([("value", "\"value\"", "key"), ("2", "2", "position")])
        {
            let raw = raw_property(&context, object, *property);
            let record = context.store().symbol(symbol).unwrap();
            assert_eq!(record.name().as_utf8().unwrap(), name);
            assert_eq!(record.declarations(), Some(&[property.declaration][..]));
            assert_eq!(record.value_declaration(), Some(property.declaration));
            let links = context.store().value_symbol_links(symbol).unwrap();
            assert_eq!(links.resolved_type, Some(number));
            if symbol != raw {
                assert_eq!(links.target, Some(raw));
            }
            assert_eq!(
                context
                    .type_to_string(resolved(&context, property.key))
                    .unwrap(),
                display
            );
            assert_eq!(resolved(&context, property.value), number);
            let key_symbol = context
                .get_symbol_at_location(variable(&parsed, key_name).0)
                .unwrap()
                .unwrap();
            assert_eq!(
                context.get_symbol_at_location(property.key).unwrap(),
                Some(key_symbol)
            );
        }
        for name in ["named", "numeric"] {
            assert_eq!(
                resolved(&context, variable(&parsed, name).1.unwrap()),
                number
            );
        }
        assert_replay(&mut context, &parsed);
    }
}

#[test]
fn computed_object_keys_report_all_key_calls_before_value_calls_and_replay() {
    let parsed = parse_source_file(concat!(
        "declare function firstKey(required: number): string;\n",
        "declare function secondKey(required: number): string;\n",
        "declare function firstValue(required: number): number;\n",
        "declare function secondValue(required: number): number;\n",
        "const object = { [firstKey()]: firstValue(), [secondKey()]: secondValue() };\n",
    ));
    let object = variable(&parsed, "object").1.unwrap();
    let parts = properties(&parsed, object);
    for query_first in [false, true] {
        let mut context = context(&parsed);
        if query_first {
            context.get_type_at_location(object).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        for property in &parts {
            raw_property(&context, object, *property);
            assert_eq!(resolved(&context, property.key), string);
            assert_eq!(resolved(&context, property.value), number);
        }
        assert_index(
            &context,
            object,
            string,
            number,
            &parts
                .iter()
                .map(|property| property.declaration)
                .collect::<Vec<_>>(),
        );
        let calls = [parts[0].key, parts[1].key, parts[0].value, parts[1].value];
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), calls.len());
        for (diagnostic, call) in diagnostics.iter().zip(calls) {
            let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
                panic!("the diagnostic control must retain each actual call")
            };
            let callee = node(&parsed, call.expression);
            assert_eq!(diagnostic.node, Some(callee));
            assert_eq!(diagnostic.diagnostic.code(), 2554);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Expected 1 arguments, but got 0."
            );
            assert_eq!(diagnostic.range_override, None);
            let [related] = diagnostic.related_information.as_slice() else {
                panic!("the missing argument must name its real parameter")
            };
            let symbol = context
                .store()
                .symbol_node_links(callee)
                .unwrap()
                .resolved_symbol
                .unwrap();
            let [declaration] = context
                .store()
                .symbol(symbol)
                .unwrap()
                .declarations()
                .unwrap()
            else {
                panic!("each call has one real function declaration")
            };
            let NodeData::FunctionDeclaration(function) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected the bound function")
            };
            assert_eq!(
                related.node,
                Some(node(&parsed, function.parameters.nodes[0]))
            );
            assert_eq!(
                related.diagnostic.render().unwrap(),
                "An argument for 'required' was not provided."
            );
        }
        assert_replay(&mut context, &parsed);
    }
}
