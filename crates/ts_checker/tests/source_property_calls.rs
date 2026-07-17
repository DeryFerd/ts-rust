use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError};
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
fn property_calls_force_public_warm_replay_while_source_remains_unchecked() {
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

    assert_eq!(
        context.check_source_file(file),
        Err(SourceCheckError::Call(*bad_call))
    );

    assert!(context.store().type_node_links(*good_call).is_some());
    assert!(context.store().signature_links(*good_call).is_some());
    assert!(context.store().type_node_links(*bad_call).is_none());
    assert!(context.store().signature_links(*bad_call).is_none());
    for access in [good_access, bad_access] {
        assert!(context.store().type_node_links(*access).is_some());
        assert!(context.store().symbol_node_links(*access).is_some());
    }
    let source = context.source_file(file).unwrap();
    assert!(
        !context
            .store()
            .source_file_links(source)
            .is_some_and(|links| links.type_checked)
    );
    let type_count = context.store().type_len();
    let signature_count = context.store().signature_len();
    let call_links = calls
        .iter()
        .map(|call| {
            (
                context.store().type_node_links(*call).cloned(),
                context.store().signature_links(*call).cloned(),
            )
        })
        .collect::<Vec<_>>();
    let property_links = accesses
        .iter()
        .map(|access| {
            (
                context.store().type_node_links(*access).cloned(),
                context.store().symbol_node_links(*access).cloned(),
            )
        })
        .collect::<Vec<_>>();

    assert_eq!(
        context.check_source_file(file),
        Err(SourceCheckError::Call(*bad_call))
    );

    assert_eq!(context.store().type_len(), type_count);
    assert_eq!(context.store().signature_len(), signature_count);
    assert_eq!(
        calls
            .iter()
            .map(|call| {
                (
                    context.store().type_node_links(*call).cloned(),
                    context.store().signature_links(*call).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        call_links
    );
    assert_eq!(
        accesses
            .iter()
            .map(|access| {
                (
                    context.store().type_node_links(*access).cloned(),
                    context.store().symbol_node_links(*access).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        property_links
    );
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
            "generic source callable",
            concat!(
                "function identity<T>(value: T): T { return value; } ",
                "const api = { fn: identity }; ",
                "const result = api.fn(1);",
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
            "method signature",
            concat!(
                "type API = { fn(value: number): string }; ",
                "function use(api: API): string { return api.fn(1); }",
            ),
        ),
        (
            "union callable",
            concat!(
                "type API = { fn: ((value: number) => string) | ((value: string) => string) }; ",
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
            "noncallable property",
            concat!(
                "type API = { fn: number }; ",
                "function use(api: API): string { return api.fn(1); }",
            ),
        ),
        (
            "any receiver",
            "function use(api: any): string { return api.fn(1); }",
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
            "nested receiver",
            concat!(
                "type API = { fn: (value: number) => string }; ",
                "type Holder = { api: API }; ",
                "function use(holder: Holder): string { return holder.api.fn(1); }",
            ),
        ),
        (
            "contextual argument",
            concat!(
                "type API = { fn: (callback: (value: number) => number) => string }; ",
                "function use(api: API): string { return api.fn(value => value); }",
            ),
        ),
        (
            "explicit type arguments",
            concat!(
                "type API = { fn: (value: number) => string }; ",
                "function use(api: API): string { return api.fn<number>(1); }",
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
