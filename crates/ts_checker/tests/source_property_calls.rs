use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions};
use ts_parser::{ParseResult, parse_source_file};

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn nodes_of_kind(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|(start, _)| *start);
    nodes.into_iter().map(|(_, node)| node).collect()
}

fn property_name(parsed: &ParseResult, file: FileId, access: NodeRef) -> NodeRef {
    let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(access.node).unwrap().data
    else {
        panic!("expected a property access")
    };
    NodeRef::new(parsed.arena.id(), file, property.name)
}

fn function_type_parameter(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ParameterDeclaration(parameter) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(parameter.name)?.data else {
                return None;
            };
            let parent = parsed.arena.get(record.parent?)?;
            (name.text == expected && parent.kind == SyntaxKind::FunctionType)
                .then(|| NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing function-type parameter {expected:?}"))
}

#[test]
fn class_method_calls_use_published_instance_and_static_signatures() {
    let parsed = parse_source_file(concat!(
        "class Model { public run() {} static ready() {} }\n",
        "const model = new Model();\n",
        "model.run();\n",
        "Model.ready();\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(40);
    let calls = nodes_of_kind(&parsed, file, SyntaxKind::CallExpression);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    for call in calls {
        let return_type = context
            .store()
            .type_node_links(call)
            .and_then(|links| links.resolved_type)
            .expect("class method call must publish its return type");
        assert_eq!(context.type_to_string(return_type).unwrap(), "void");
        assert!(
            context
                .store()
                .signature_links(call)
                .is_some_and(|links| links.resolved_signature.signature().is_some())
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn primitive_wrapper_methods_publish_real_library_symbols_and_signatures() {
    let library = parse_source_file(concat!(
        "interface Array<T> {}\n",
        "interface ReadonlyArray<T> {}\n",
        "interface Number { toFixed(fractionDigits?: number): string; }\n",
        "interface String { toLowerCase(): string; }\n",
    ));
    let source = parse_source_file(concat!(
        "const rounded = 2..toFixed(0);\n",
        "const lowered = 'VALUE'.toLowerCase();\n",
    ));
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
    let library_file = FileId::new(41);
    let file = FileId::new(42);
    let mut binder = CanonicalBinder::new();
    for (parsed, current, path, declaration, default_library) in [
        (&library, library_file, "\"/project/lib.d.ts\"", true, true),
        (
            &source,
            file,
            "\"/project/primitive-methods.ts\"",
            false,
            false,
        ),
    ] {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                current,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    default_library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, current)
            .unwrap();
    }
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(library_file, &library.arena), (file, &source.arena)]
            .into_iter()
            .collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    for access in nodes_of_kind(&source, file, SyntaxKind::PropertyAccessExpression) {
        let symbol = context
            .store()
            .symbol_node_links(access)
            .and_then(|links| links.resolved_symbol)
            .expect("primitive method access must retain its real interface member");
        assert!(
            context
                .store()
                .symbol(symbol)
                .is_some_and(|record| record.flags().contains(ts_binder::SymbolFlags::METHOD))
        );
    }
    for call in nodes_of_kind(&source, file, SyntaxKind::CallExpression) {
        let return_type = context
            .store()
            .type_node_links(call)
            .and_then(|links| links.resolved_type)
            .expect("primitive method call must publish its return type");
        assert_eq!(context.type_to_string(return_type).unwrap(), "string");
        assert!(
            context
                .store()
                .signature_links(call)
                .is_some_and(|links| links.resolved_signature.signature().is_some())
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn required_own_property_calls_publish_public_links_and_diagnostics() {
    let parsed = parse_source_file(concat!(
        "type API = { fn: (value: number) => string }; ",
        "function good(api: API): string { return api.fn(1); } ",
        "function tooFew(api: API): string { return api.fn(); }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let calls = nodes_of_kind(&parsed, file, SyntaxKind::CallExpression);
    let accesses = nodes_of_kind(&parsed, file, SyntaxKind::PropertyAccessExpression);
    let [good_call, too_few_call] = calls.as_slice() else {
        panic!("expected two calls")
    };
    let [good_access, too_few_access] = accesses.as_slice() else {
        panic!("expected two property accesses")
    };
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].diagnostic.code(), 2554);
    assert_eq!(
        diagnostics[0].node,
        Some(property_name(&parsed, file, *too_few_access))
    );
    assert_eq!(diagnostics[0].range_override, None);
    assert_eq!(
        diagnostics[0].diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0."
    );
    let [related] = diagnostics[0].related_information.as_slice() else {
        panic!("TS2554 should retain one missing-argument related diagnostic")
    };
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument for 'value' was not provided."
    );
    assert_eq!(
        related.node,
        Some(function_type_parameter(&parsed, file, "value"))
    );

    for (call, access) in [(*good_call, *good_access), (*too_few_call, *too_few_access)] {
        let return_type = context
            .store()
            .type_node_links(call)
            .and_then(|links| links.resolved_type)
            .expect("call return type must be cached");
        assert_eq!(context.type_to_string(return_type).unwrap(), "string");
        assert!(
            context
                .store()
                .signature_links(call)
                .is_some_and(|links| links.resolved_signature.signature().is_some())
        );
        assert!(
            context
                .store()
                .type_node_links(access)
                .and_then(|links| links.resolved_type)
                .is_some()
        );
        assert!(
            context
                .store()
                .symbol_node_links(access)
                .is_some_and(|links| links.resolved_symbol.is_some())
        );
    }
}

#[test]
fn top_level_property_calls_check_arguments_and_publish_signatures() {
    let parsed = parse_source_file(concat!(
        "type API = { execute: (value: number) => string }; ",
        "declare const api: API; ",
        "api.execute(1); ",
        "api.execute();",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(19);
    let calls = nodes_of_kind(&parsed, file, SyntaxKind::CallExpression);
    let accesses = nodes_of_kind(&parsed, file, SyntaxKind::PropertyAccessExpression);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one argument-count diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2554);
    assert_eq!(
        diagnostic.node,
        Some(property_name(&parsed, file, accesses[1]))
    );
    for call in calls {
        let type_ = context
            .store()
            .type_node_links(call)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(context.type_to_string(type_).unwrap(), "string");
        assert!(
            context
                .store()
                .signature_links(call)
                .is_some_and(|links| links.resolved_signature.signature().is_some())
        );
    }
}

#[test]
fn noncallable_property_calls_report_ts2349_and_preserve_warm_publication() {
    let parsed = parse_source_file(concat!(
        "type API = { fn: (value: number) => string }; ",
        "function good(api: API): string { return api.fn(1); } ",
        "type Broken = { fn: number }; ",
        "function stop(api: Broken): string { return api.fn(1); }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(18);
    let calls = nodes_of_kind(&parsed, file, SyntaxKind::CallExpression);
    let accesses = nodes_of_kind(&parsed, file, SyntaxKind::PropertyAccessExpression);
    let [good_call, bad_call] = calls.as_slice() else {
        panic!("expected one successful and one rejected call")
    };
    let [good_access, bad_access] = accesses.as_slice() else {
        panic!("expected two property accesses")
    };
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    assert!(context.store().type_node_links(*good_call).is_some());
    assert!(context.store().signature_links(*good_call).is_some());
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        context
            .store()
            .type_node_links(*bad_call)
            .and_then(|links| links.resolved_type),
        Some(bootstrap.error_type)
    );
    assert_eq!(
        context
            .store()
            .signature_links(*bad_call)
            .and_then(|links| links.resolved_signature.signature()),
        Some(bootstrap.unknown_signature)
    );
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one noncallable-property diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2349);
    assert_eq!(
        diagnostic.node,
        Some(property_name(&parsed, file, *bad_access))
    );
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "This expression is not callable.\n  Type 'Number' has no call signatures."
    );
    for access in [good_access, bad_access] {
        assert!(context.store().type_node_links(*access).is_some());
        assert!(context.store().symbol_node_links(*access).is_some());
    }
    let source = context.source_file(file).unwrap();
    assert!(
        context
            .store()
            .source_file_links(source)
            .is_some_and(|links| links.type_checked)
    );
    let type_count = context.store().type_len();
    let signature_count = context.store().signature_len();
    let call_state = |context: &CanonicalCheckerContext<'_>| {
        calls
            .iter()
            .map(|call| {
                (
                    context.store().type_node_links(*call).cloned(),
                    context.store().signature_links(*call).cloned(),
                )
            })
            .collect::<Vec<_>>()
    };
    let property_state = |context: &CanonicalCheckerContext<'_>| {
        accesses
            .iter()
            .map(|access| {
                (
                    context.store().type_node_links(*access).cloned(),
                    context.store().symbol_node_links(*access).cloned(),
                )
            })
            .collect::<Vec<_>>()
    };
    let call_links = call_state(&context);
    let property_links = property_state(&context);

    let diagnostics = context.diagnostics().clone();
    context.recheck_source_file(file).unwrap();

    assert_eq!(context.store().type_len(), type_count);
    assert_eq!(context.store().signature_len(), signature_count);
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(call_state(&context), call_links);
    assert_eq!(property_state(&context), property_links);
}

#[test]
fn inherited_property_call_reuses_the_base_member_cold_and_warm() {
    let parsed = parse_source_file(concat!(
        "interface Base { fn: (value: number) => string; } ",
        "interface API extends Base {} ",
        "function use(api: API): string { return api.fn(1); }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(19);
    let calls = nodes_of_kind(&parsed, file, SyntaxKind::CallExpression);
    let accesses = nodes_of_kind(&parsed, file, SyntaxKind::PropertyAccessExpression);
    let [call] = calls.as_slice() else {
        panic!("expected one call")
    };
    let [access] = accesses.as_slice() else {
        panic!("expected one property access")
    };
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let return_type = context
        .store()
        .type_node_links(*call)
        .and_then(|links| links.resolved_type)
        .expect("inherited call return type must be cached");
    assert_eq!(context.type_to_string(return_type).unwrap(), "string");
    let signature = context.store().signature_links(*call).cloned();
    assert!(
        signature
            .as_ref()
            .is_some_and(|links| links.resolved_signature.signature().is_some())
    );
    let property_type = context.store().type_node_links(*access).cloned();
    let property_symbol = context.store().symbol_node_links(*access).cloned();
    assert!(property_type.is_some());
    assert!(
        property_symbol
            .as_ref()
            .is_some_and(|links| links.resolved_symbol.is_some())
    );
    assert!(context.diagnostics().is_empty());

    let counts = (context.store().type_len(), context.store().signature_len());
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (context.store().type_len(), context.store().signature_len()),
        counts
    );
    assert_eq!(context.store().signature_links(*call), signature.as_ref());
    assert_eq!(
        context.store().type_node_links(*access),
        property_type.as_ref()
    );
    assert_eq!(
        context.store().symbol_node_links(*access),
        property_symbol.as_ref()
    );
    assert!(context.diagnostics().is_empty());
}

#[test]
fn nested_property_receivers_publish_their_call_signature_and_return_type() {
    let parsed = parse_source_file(concat!(
        "type API = { fn: (value: number) => string }; ",
        "type Holder = { api: API }; ",
        "function use(holder: Holder): string { return holder.api.fn(1); }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(30);
    let calls = nodes_of_kind(&parsed, file, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("expected one nested property call")
    };
    let accesses = nodes_of_kind(&parsed, file, SyntaxKind::PropertyAccessExpression);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let return_type = context
        .store()
        .type_node_links(*call)
        .and_then(|links| links.resolved_type)
        .expect("nested property call must retain its return type");
    assert_eq!(context.type_to_string(return_type).unwrap(), "string");
    assert!(
        context
            .store()
            .signature_links(*call)
            .is_some_and(|links| links.resolved_signature.signature().is_some())
    );
    assert_eq!(accesses.len(), 2);
    assert!(accesses.iter().all(|access| {
        context
            .store()
            .symbol_node_links(*access)
            .is_some_and(|links| links.resolved_symbol.is_some())
    }));
    assert!(context.diagnostics().is_empty());
}

#[test]
fn nongeneric_property_type_arguments_report_ts2558_and_preserve_public_links() {
    let source = concat!(
        "type API = { fn: (value: number) => string }; ",
        "function use(api: API): string { return api.fn<number>(1); }",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(31);
    let calls = nodes_of_kind(&parsed, file, SyntaxKind::CallExpression);
    let accesses = nodes_of_kind(&parsed, file, SyntaxKind::PropertyAccessExpression);
    let [call] = calls.as_slice() else {
        panic!("expected one nongeneric property call")
    };
    let [access] = accesses.as_slice() else {
        panic!("expected one property access")
    };
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one type-argument arity diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2558);
    assert_eq!(diagnostic.node, Some(*call));
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Expected 0 type arguments, but got 1."
    );
    let range = diagnostic
        .range_override
        .expect("TS2558 retains its type-argument range")
        .range();
    assert_eq!(
        &source[usize::try_from(range.start.get()).unwrap()
            ..usize::try_from(range.end.get()).unwrap()],
        "number"
    );
    let return_type = context
        .store()
        .type_node_links(*call)
        .and_then(|links| links.resolved_type)
        .expect("the rejected type arguments retain the call result");
    assert_eq!(context.type_to_string(return_type).unwrap(), "string");
    assert!(
        context
            .store()
            .signature_links(*call)
            .is_some_and(|links| links.resolved_signature.signature().is_some())
    );
    assert!(context.store().type_node_links(*access).is_some());
    assert!(context.store().symbol_node_links(*access).is_some());

    let diagnostics = context.diagnostics().clone();
    context.recheck_source_file(file).unwrap();
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn method_signature_calls_check_arguments_and_keep_warm_identities() {
    let parsed = parse_source_file(concat!(
        "type API = { fn(value: number): string }; ",
        "function good(api: API): string { return api.fn(1); } ",
        "function wrong(api: API): string { return api.fn('wrong'); } ",
        "function tooFew(api: API): string { return api.fn(); }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(43);
    let methods = nodes_of_kind(&parsed, file, SyntaxKind::MethodSignature);
    let [method] = methods.as_slice() else {
        panic!("expected one method signature")
    };
    let calls = nodes_of_kind(&parsed, file, SyntaxKind::CallExpression);
    let accesses = nodes_of_kind(&parsed, file, SyntaxKind::PropertyAccessExpression);
    let arguments = nodes_of_kind(&parsed, file, SyntaxKind::StringLiteral);
    let [wrong_argument] = arguments.as_slice() else {
        panic!("expected one string argument")
    };
    assert_eq!(calls.len(), 3);
    assert_eq!(accesses.len(), 3);
    let mut context = context(&parsed, file);
    let method_symbol = context.file(file).unwrap().1.symbol(*method).unwrap();
    let mut expected_signature = None;
    let mut expected_counts = None;

    for warm in [false, true] {
        if warm {
            context.recheck_source_file(file).unwrap();
        } else {
            context.check_source_file(file).unwrap();
        }
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        assert_eq!(diagnostics[0].diagnostic.code(), 2345);
        assert_eq!(diagnostics[0].node, Some(*wrong_argument));
        assert_eq!(diagnostics[1].diagnostic.code(), 2554);
        assert_eq!(
            diagnostics[1].node,
            Some(property_name(&parsed, file, accesses[2]))
        );
        let store = context.store();
        let signature = store
            .signature_links(*method)
            .and_then(|links| links.resolved_signature.signature())
            .expect("the method must retain its declared signature");
        if let Some(expected) = expected_signature {
            assert_eq!(signature, expected);
        }
        expected_signature = Some(signature);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        for (call, access) in calls.iter().zip(&accesses) {
            assert_eq!(
                store.type_node_links(*call).unwrap().resolved_type,
                Some(string)
            );
            assert_eq!(
                store
                    .signature_links(*call)
                    .and_then(|links| links.resolved_signature.signature()),
                Some(signature)
            );
            assert_eq!(
                store.symbol_node_links(*access).unwrap().resolved_symbol,
                Some(method_symbol)
            );
        }
        let counts = (
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
        );
        if let Some(expected) = expected_counts {
            assert_eq!(counts, expected);
        }
        expected_counts = Some(counts);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // All unsupported call families share one publication check.
fn unsupported_property_call_families_fail_closed_without_call_publication() {
    let fixtures = [
        (
            "optional property",
            concat!(
                "type API = { fn?: (value: number) => string }; ",
                "function use(api: API): string { return api.fn(1); }",
            ),
        ),
        (
            "generic function type",
            concat!(
                "type API = { fn: <T>(value: T) => T }; ",
                "function use(api: API): number { return api.fn(1); }",
            ),
        ),
        (
            "explicit this",
            concat!(
                "type API = { fn: (this: API, value: number) => string }; ",
                "function use(api: API): string { return api.fn(1); }",
            ),
        ),
        (
            "union receiver",
            concat!(
                "type Left = { fn: (value: number) => string }; ",
                "type Right = { fn: (value: number) => string }; ",
                "function use(api: Left | Right): string { return api.fn(1); }",
            ),
        ),
        (
            "apparent property",
            "function use(api: {}): string { return api.toString(); }",
        ),
        (
            "optional member call",
            concat!(
                "type API = { fn: (value: number) => string }; ",
                "function use(api: API): string { return api.fn?.(1); }",
            ),
        ),
        (
            "spread argument",
            concat!(
                "type API = { fn: (value: number) => string }; ",
                "function use(api: API): string { return api.fn(...[1]); }",
            ),
        ),
        (
            "element callee",
            concat!(
                "type API = { fn: (value: number) => string }; ",
                "function use(api: API): string { return api['fn'](1); }",
            ),
        ),
        (
            "parenthesized callee",
            concat!(
                "type API = { fn: (value: number) => string }; ",
                "function use(api: API): string { return (api.fn)(1); }",
            ),
        ),
        (
            "contextual argument",
            concat!(
                "type API = { fn: (callback: (value: number) => number) => string }; ",
                "function use(api: API): string { return api.fn(value => value); }",
            ),
        ),
    ];

    for (index, (name, text)) in fixtures.into_iter().enumerate() {
        let parsed = parse_source_file(text);
        assert!(
            parsed.diagnostics.is_empty(),
            "parser diagnostics for {name}: {:?}",
            parsed.diagnostics
        );
        let file = FileId::new(u32::try_from(index + 1).unwrap());
        let calls = nodes_of_kind(&parsed, file, SyntaxKind::CallExpression);
        let [call] = calls.as_slice() else {
            panic!("expected one call for {name}")
        };
        let call = *call;
        let mut context = context(&parsed, file);

        let result = context.check_source_file(file);

        assert!(result.is_err(), "{name} unexpectedly succeeded");
        assert!(
            context.store().type_node_links(call).is_none(),
            "{name} published a call type"
        );
        assert!(
            context.store().signature_links(call).is_none(),
            "{name} published a call signature"
        );
        let source = context.source_file(file).unwrap();
        assert!(
            !context
                .store()
                .source_file_links(source)
                .is_some_and(|links| links.type_checked),
            "{name} published source completion"
        );
    }
}
