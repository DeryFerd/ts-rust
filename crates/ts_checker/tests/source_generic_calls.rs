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
    let bad_signature = store
        .signature_links(*bad)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    assert_ne!(bad_signature, explicit_signature);

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
#[allow(clippy::too_many_lines)]
fn ordered_generic_calls_publish_go_style_checked_and_recovery_signatures() {
    let parsed = parse_source_file(concat!(
        "function pair<T, U>(left: T, right: U): U { return right; } ",
        "function constrained<T extends string>(value: T): T { return value; } ",
        "function dependent<T, U extends T>(left: T, right: U): U { return right; } ",
        "function defaulted<T, U = T>(left: T, right: U): U { return right; } ",
        "function repeat<T>(left: T, right: T): T { return left; } ",
        "const good = pair<string, number>('a', 1); ",
        "const goodAgain = pair<string, number>('b', 2); ",
        "const badArgA = pair<string, number>('a', ('bad')); ",
        "const badArgB = pair<string, number>('a', 'bad'); ",
        "const badConstraintA = constrained<number>(1); ",
        "const badConstraintB = constrained<number>(2); ",
        "const badDependent = dependent<string, number>('a', 1); ",
        "const badTypeArityA = pair<string>('a', 1); ",
        "const badTypeArityB = pair<string>('b', 2); ",
        "const badValueArityA = pair<string, number>('a'); ",
        "const badValueArityB = pair<string, number>('b'); ",
        "const partial = defaulted<string>('a', 'b'); ",
        "const full = defaulted<string, string>('a', 'b'); ",
        "const rawDefaultFailure = defaulted<string>('a'); ",
        "const repeated = repeat('a', 'b'); ",
        "const inferredSecond = pair('a', 1);",
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
                EscapedName::source("\"/project/ordered-generic-calls.ts\""),
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

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2345, 2345, 2344, 2344, 2344, 2558, 2558, 2554, 2554, 2554]
    );
    assert_eq!(
        diagnostics[4].diagnostic.render().unwrap(),
        "Type 'number' does not satisfy the constraint 'string'."
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
    let calls = calls
        .into_iter()
        .map(|(_, call)| call)
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 16);
    let signature = |index: usize| {
        context
            .store()
            .signature_links(calls[index])
            .and_then(|links| links.resolved_signature.signature())
            .unwrap()
    };
    assert_eq!(signature(0), signature(1));
    assert_ne!(signature(2), signature(3));
    assert_ne!(signature(2), signature(0));
    assert_ne!(signature(3), signature(0));
    assert_ne!(signature(4), signature(5));
    assert_ne!(signature(7), signature(8));
    assert_ne!(signature(9), signature(10));
    assert_eq!(signature(11), signature(12));
    assert_ne!(signature(13), signature(11));

    let resolved_type = |index: usize| {
        context
            .store()
            .type_node_links(calls[index])
            .and_then(|links| links.resolved_type)
            .unwrap()
    };
    assert_eq!(
        context
            .store()
            .type_payload(resolved_type(13))
            .unwrap()
            .flags(),
        TypeFlags::TYPE_PARAMETER
    );
    assert_eq!(context.type_to_string(resolved_type(14)).unwrap(), "\"a\" | \"b\"");
    assert_eq!(
        context
            .store()
            .type_payload(resolved_type(15))
            .unwrap()
            .flags(),
        TypeFlags::NUMBER_LITERAL
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
