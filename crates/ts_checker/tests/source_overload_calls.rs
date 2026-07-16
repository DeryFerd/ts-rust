use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions};
use ts_parser::parse_source_file;

#[test]
fn declared_call_sets_select_ordered_and_arity_compatible_overloads_cold_and_warm() {
    let parsed = parse_source_file(concat!(
        "interface Ordered { ",
        "(value: number): string; ",
        "(value: number): number; ",
        "} ",
        "type Branching = { ",
        "(value: string): number; ",
        "(value: number): string; ",
        "}; ",
        "interface Recovery { ",
        "(value: number, other: number): string; ",
        "(value: string): number; ",
        "} ",
        "function ordered(value: Ordered): string { return value(1); } ",
        "function branching(value: Branching): string { return value(1); } ",
        "function recovery(value: Recovery): number { return value(true); }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/source-overload-calls.ts\""),
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
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();

    context.check_source_file(file).unwrap();

    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2345]
    );
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
    let [ordered_call, branching_call, recovery_call] = calls.as_slice() else {
        panic!("expected three overload calls")
    };
    let [ordered_first, _, _, branching_second, _, recovery_second] = declarations.as_slice()
    else {
        panic!("expected six declared call signatures")
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
        selected_signature(*recovery_call),
        selected_signature(*recovery_second)
    );
    assert_eq!(
        calls
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
        ["string", "string", "number"]
    );

    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(context.diagnostics().len(), 1);
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts
    );
}
