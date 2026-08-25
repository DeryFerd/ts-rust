use ts_ast::{FileId, NodeRef, SyntaxKind};
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

#[test]
#[allow(clippy::too_many_lines)] // One overload graph proves ordering and both relation passes.
fn declared_call_sets_reorder_literals_and_run_subtype_then_assignable() {
    let parsed = parse_source_file(concat!(
        "interface Ordered { ",
        "(value: number): string; ",
        "(value: number): number; ",
        "} ",
        "type Branching = { ",
        "(value: string): number; ",
        "(value: number): string; ",
        "}; ",
        "interface Specialized { ",
        "(value: number): 'broad'; ",
        "(value: 1): 'literal'; ",
        "} ",
        "interface AnyChoice { ",
        "(value: string): 'string'; ",
        "(value: any): 'any'; ",
        "} ",
        "function ordered(value: Ordered): string { return value(1); } ",
        "function branching(value: Branching): string { return value(1); } ",
        "type API = { fn: Branching }; ",
        "function property(value: API): string { return value.fn(1); } ",
        "function specialized(value: Specialized): 'literal' { return value(1); } ",
        "function subtype(value: AnyChoice, input: any): 'any' { return value(input); }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    let nodes = |kind| {
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
        nodes.into_iter().map(|(_, node)| node).collect::<Vec<_>>()
    };
    let calls = nodes(SyntaxKind::CallExpression);
    let declarations = nodes(SyntaxKind::CallSignature);
    let [
        ordered_call,
        branching_call,
        property_call,
        specialized_call,
        subtype_call,
    ] = calls.as_slice()
    else {
        panic!("expected five overload calls")
    };
    let [
        ordered_first,
        _,
        _,
        branching_second,
        _,
        specialized_second,
        _,
        subtype_second,
    ] = declarations.as_slice()
    else {
        panic!("expected eight declared call signatures")
    };
    let selected_signature = |node| {
        context
            .store()
            .signature_links(node)
            .and_then(|links| links.resolved_signature.signature())
    };
    assert_eq!(
        selected_signature(*ordered_call),
        selected_signature(*ordered_first)
    );
    assert_eq!(
        selected_signature(*branching_call),
        selected_signature(*branching_second)
    );
    assert_eq!(
        selected_signature(*property_call),
        selected_signature(*branching_second)
    );
    assert_eq!(
        selected_signature(*specialized_call),
        selected_signature(*specialized_second)
    );
    assert_eq!(
        selected_signature(*subtype_call),
        selected_signature(*subtype_second)
    );
    assert_eq!(
        calls[..3]
            .iter()
            .map(|call| {
                let type_ = context
                    .store()
                    .type_node_links(*call)
                    .and_then(|links| links.resolved_type)
                    .expect("overload call should retain its selected return type");
                context.type_to_string(type_).unwrap()
            })
            .collect::<Vec<_>>(),
        ["string", "string", "string"]
    );
}

#[test]
fn multi_overload_failure_recovery_remains_an_atomic_boundary() {
    let parsed = parse_source_file(concat!(
        "interface Recovery { ",
        "(value: number, other: number): string; ",
        "(value: string): number; ",
        "} ",
        "function good(value: Recovery): string { return value(1, 2); } ",
        "function recovery(value: Recovery): number { return value(true); }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|(start, _)| *start);
    let [(_, good_call), (_, recovery_call)] = calls.as_slice() else {
        panic!("fixture contains one successful and one recovery call")
    };
    let declarations = parsed
        .arena
        .iter()
        .filter(|(_, record)| record.kind == SyntaxKind::CallSignature)
        .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
        .collect::<Vec<_>>();
    let mut context = context(&parsed, file);

    assert!(context.check_source_file(file).is_err());

    assert!(context.diagnostics().is_empty());
    let good_publication = (
        context.store().type_node_links(*good_call).cloned(),
        context.store().signature_links(*good_call).cloned(),
    );
    assert!(good_publication.0.is_some());
    assert!(good_publication.1.is_some());
    assert!(context.store().type_node_links(*recovery_call).is_none());
    assert!(context.store().signature_links(*recovery_call).is_none());
    assert!(declarations.iter().all(|declaration| {
        context
            .store()
            .signature_links(*declaration)
            .is_some_and(|links| links.resolved_signature.signature().is_some())
    }));
    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );

    assert!(context.check_source_file(file).is_err());

    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts
    );
    assert_eq!(
        (
            context.store().type_node_links(*good_call).cloned(),
            context.store().signature_links(*good_call).cloned(),
        ),
        good_publication
    );
    assert!(context.store().type_node_links(*recovery_call).is_none());
    assert!(context.store().signature_links(*recovery_call).is_none());
}

#[test]
fn one_matching_overload_preserves_its_shared_return_and_argument_diagnostic() {
    let parsed = parse_source_file(concat!(
        "interface Recovery { ",
        "(value: number, other: number): string; ",
        "(value: string): string; ",
        "} ",
        "function good(value: Recovery): string { return value(1, 2); } ",
        "function recovery(value: Recovery): string { return value(true); }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|(start, _)| *start);
    let [(_, good_call), (_, recovery_call)] = calls.as_slice() else {
        panic!("fixture contains one successful and one recovered call")
    };
    let mut declarations = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallSignature).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    declarations.sort_by_key(|(start, _)| *start);
    let [(_, _), (_, recovery_declaration)] = declarations.as_slice() else {
        panic!("fixture contains two overload declarations")
    };
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("only the matching-arity overload should produce a diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'boolean' is not assignable to parameter of type 'string'."
    );
    let declaration_signature = context
        .store()
        .signature_links(*recovery_declaration)
        .and_then(|links| links.resolved_signature.signature());
    assert_eq!(
        context
            .store()
            .signature_links(*recovery_call)
            .and_then(|links| links.resolved_signature.signature()),
        declaration_signature
    );
    for call in [*good_call, *recovery_call] {
        let return_type = context
            .store()
            .type_node_links(call)
            .and_then(|links| links.resolved_type)
            .expect("both overload calls must preserve their shared return type");
        assert_eq!(context.type_to_string(return_type).unwrap(), "string");
    }
    let cold = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        context.store().type_node_links(*recovery_call).cloned(),
        context.store().signature_links(*recovery_call).cloned(),
        context.diagnostics().clone(),
    );

    context.recheck_source_file(file).unwrap();

    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().type_node_links(*recovery_call).cloned(),
            context.store().signature_links(*recovery_call).cloned(),
            context.diagnostics().clone(),
        ),
        cold
    );
}

#[test]
#[allow(clippy::too_many_lines)] // One overload group proves both TS2554 ranges and warm identity.
fn uniform_overload_arity_errors_preserve_diagnostics_signature_and_return() {
    let source = concat!(
        "interface Recovery { ",
        "(text: string): string; ",
        "(count: number): string; ",
        "} ",
        "function missing(value: Recovery): string { return value(); } ",
        "function extra(value: Recovery): string { return value('ready', true); }",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|(start, _)| *start);
    let [(_, missing_call), (_, extra_call)] = calls.as_slice() else {
        panic!("fixture contains one missing-argument and one extra-argument call")
    };
    let mut declarations = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallSignature).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    declarations.sort_by_key(|(start, _)| *start);
    let [(_, first_declaration), (_, _)] = declarations.as_slice() else {
        panic!("fixture contains two overload declarations")
    };
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let [missing, extra] = context.diagnostics().as_slice() else {
        panic!("both overload calls must produce their exact argument-count diagnostic")
    };
    assert_eq!(missing.diagnostic.code(), 2554);
    assert_eq!(
        missing.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0."
    );
    assert!(missing.range_override.is_none());
    let [related] = missing.related_information.as_slice() else {
        panic!("the missing argument must retain its first-overload parameter note")
    };
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument for 'text' was not provided."
    );
    assert_eq!(extra.diagnostic.code(), 2554);
    assert_eq!(
        extra.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 2."
    );
    assert!(extra.related_information.is_empty());
    let extra_range = extra
        .range_override
        .expect("the extra argument must retain its source range")
        .range();
    assert_eq!(
        &source[usize::try_from(extra_range.start.get()).unwrap()
            ..usize::try_from(extra_range.end.get()).unwrap()],
        "true"
    );
    let first_signature = context
        .store()
        .signature_links(*first_declaration)
        .and_then(|links| links.resolved_signature.signature());
    for call in [*missing_call, *extra_call] {
        assert_eq!(
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature()),
            first_signature
        );
        let return_type = context
            .store()
            .type_node_links(call)
            .and_then(|links| links.resolved_type)
            .expect("overload arity recovery must preserve its shared return type");
        assert_eq!(context.type_to_string(return_type).unwrap(), "string");
    }
    let cold = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        [*missing_call, *extra_call].map(|call| {
            (
                context.store().type_node_links(call).cloned(),
                context.store().signature_links(call).cloned(),
            )
        }),
        context.diagnostics().clone(),
    );

    context.recheck_source_file(file).unwrap();

    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            [*missing_call, *extra_call].map(|call| {
                (
                    context.store().type_node_links(call).cloned(),
                    context.store().signature_links(call).cloned(),
                )
            }),
            context.diagnostics().clone(),
        ),
        cold
    );
}
