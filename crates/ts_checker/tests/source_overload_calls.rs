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
fn declared_call_sets_reorder_literals_and_run_subtype_then_assignable_cold_and_warm() {
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

    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts
    );
}

#[test]
fn multi_overload_failure_recovery_remains_an_atomic_boundary() {
    let parsed = parse_source_file(concat!(
        "interface Recovery { ",
        "(value: number, other: number): string; ",
        "(value: string): number; ",
        "} ",
        "function recovery(value: Recovery): number { return value(true); }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let call = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::CallExpression)
                .then(|| NodeRef::new(parsed.arena.id(), file, node))
        })
        .expect("fixture contains one overload call");
    let declarations = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallSignature)
                .then(|| NodeRef::new(parsed.arena.id(), file, node))
        })
        .collect::<Vec<_>>();
    let mut context = context(&parsed, file);

    assert!(context.check_source_file(file).is_err());

    assert!(context.diagnostics().is_empty());
    assert!(context.store().type_node_links(call).is_none());
    assert!(context.store().signature_links(call).is_none());
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
    assert!(context.store().type_node_links(call).is_none());
    assert!(context.store().signature_links(call).is_none());
}
