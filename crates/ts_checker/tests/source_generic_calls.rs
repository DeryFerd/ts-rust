use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnosticRange, CanonicalCheckerOptions,
    types::TypeFlags,
};
use ts_core::{TextPos, TextRange};
use ts_parser::parse_source_file;

#[test]
fn identity_generic_calls_infer_and_apply_explicit_type_arguments() {
    let parsed = parse_source_file(concat!(
        "type User = { id: number }; ",
        "function identity<T>(value: T): T { return value; } ",
        "const user: User = { id: 1 }; ",
        "const copied: User = identity(user); ",
        "const inferred: 'x' = identity('x'); ",
        "const explicit: string = identity<string>('x'); ",
        "const bad = identity<string>(1);",
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
                EscapedName::source("\"/project/generic-calls.ts\""),
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
    let [(_, structured), (_, inferred), (_, explicit), (_, bad)] = calls.as_slice() else {
        panic!("expected four generic calls")
    };
    let store = context.store();
    let string = store.intrinsic_bootstrap().unwrap().string_type;
    let inferred_type = store
        .type_node_links(*inferred)
        .and_then(|links| links.resolved_type)
        .expect("inferred call type must be cached");
    assert_ne!(inferred_type, string);
    assert_eq!(
        store.type_payload(inferred_type).unwrap().flags(),
        TypeFlags::STRING_LITERAL
    );
    for call in [explicit, bad] {
        assert_eq!(
            store
                .type_node_links(*call)
                .and_then(|links| links.resolved_type),
            Some(string)
        );
    }
    let inferred_signature = store
        .signature_links(*inferred)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let structured_signature = store
        .signature_links(*structured)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let explicit_signature = store
        .signature_links(*explicit)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    assert_ne!(structured_signature, inferred_signature);
    assert_ne!(structured_signature, explicit_signature);
    assert_ne!(inferred_signature, explicit_signature);
    assert_eq!(
        store
            .signature_links(*bad)
            .and_then(|links| links.resolved_signature.signature()),
        Some(explicit_signature)
    );

    let warm_counts = (
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
        warm_counts
    );
}

#[test]
fn generic_call_grammar_precedes_argument_diagnostics_and_uses_exact_ranges() {
    let text = concat!(
        "function identity<T>(value: T): T { return value; } ",
        "const empty = identity<>(1 + true); ",
        "const trailing = identity< string , /* trivia */ >(\"trailing\");",
    );
    let parsed = parse_source_file(text);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-call-grammar.ts\""),
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
    let [(_, empty), (_, trailing)] = calls.as_slice() else {
        panic!("expected empty and trailing-comma generic calls")
    };

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [1099, 2365, 1009]
    );
    let empty_start = text.find("<>").unwrap();
    assert_eq!(
        diagnostics[0].range_override,
        Some(CanonicalCheckerDiagnosticRange::new(
            *empty,
            TextRange::new(
                TextPos::new(u32::try_from(empty_start).unwrap()),
                TextPos::new(u32::try_from(empty_start + 2).unwrap()),
            ),
        ))
    );
    let comma_start = text.find(", /* trivia */").unwrap();
    assert_eq!(
        diagnostics[2].range_override,
        Some(CanonicalCheckerDiagnosticRange::new(
            *trailing,
            TextRange::new(
                TextPos::new(u32::try_from(comma_start).unwrap()),
                TextPos::new(u32::try_from(comma_start + 1).unwrap()),
            ),
        ))
    );

}
