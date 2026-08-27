use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
};
use ts_parser::parse_source_file;

#[allow(clippy::too_many_lines)] // Keep source publication and replay checks in one fixture.
fn replay_after_source(annotation: &str, body: &str, query_first: bool, strict_null_checks: bool) {
    let source = format!(
        "declare let value: {annotation}; type Result = {body}; \
         type Forward = Result; type ForwardAgain = Forward;"
    );
    let parsed = parse_source_file(&source);
    assert!(parsed.diagnostics.is_empty());
    let file = FileId::new(13_811);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/typeof-alias-unions.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut checker = CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();
    let find = |kind| {
        parsed
            .arena
            .iter()
            .find_map(|(id, node)| {
                (node.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, id))
            })
            .unwrap()
    };
    let query = find(SyntaxKind::TypeQuery);
    let declaration = find(SyntaxKind::VariableDeclaration);
    let symbol = checker.file(file).unwrap().1.symbol(declaration).unwrap();
    let aliases = parsed
        .arena
        .iter()
        .filter(|(_, node)| node.kind == SyntaxKind::TypeAliasDeclaration)
        .map(|(id, _)| {
            checker
                .file(file)
                .unwrap()
                .1
                .symbol(NodeRef::new(parsed.arena.id(), file, id))
                .unwrap()
        })
        .collect::<Vec<_>>();
    let query_type = query_first.then(|| {
        let expected = checker.get_type_from_type_node(query).unwrap();
        assert_eq!(checker.get_type_from_type_node(query), Ok(expected));
        expected
    });
    checker.check_source_file(file).unwrap();
    assert!(checker.diagnostics().is_empty());
    let expected = checker
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap();
    assert!(query_type.is_none_or(|query_type| query_type == expected));
    assert_eq!(
        checker.get_type_from_type_node(query),
        Ok(expected),
        "annotation={annotation}, body={body}, query_first={query_first}"
    );
    for alias in &aliases {
        assert_eq!(checker.get_declared_type_of_symbol(*alias), Ok(expected));
    }
    let state = |checker: &CanonicalCheckerContext<'_>| {
        let store = checker.store();
        (
            store.type_len(),
            store.symbol_len(),
            store.mapper_len(),
            store.signature_len(),
            store.type_node_links(query).cloned(),
            store.value_symbol_links(symbol).cloned(),
            aliases
                .iter()
                .map(|alias| store.type_alias_links(*alias).cloned())
                .collect::<Vec<_>>(),
            store.relation_state_snapshot(),
        )
    };
    let before = state(&checker);
    checker.recheck_source_file(file).unwrap();
    assert_eq!(checker.get_type_from_type_node(query), Ok(expected));
    for alias in &aliases {
        assert_eq!(checker.get_declared_type_of_symbol(*alias), Ok(expected));
    }
    assert_eq!(state(&checker), before);
    assert!(checker.diagnostics().is_empty());
}

#[test]
fn boolean_alias_replays_after_source_check() {
    for strict in [false, true] {
        for query_first in [false, true] {
            for body in ["typeof value", "((typeof value))"] {
                replay_after_source("boolean", body, query_first, strict);
            }
        }
    }
}

#[test]
fn union_alias_replays_after_source_check() {
    for strict in [false, true] {
        for query_first in [false, true] {
            for body in ["typeof value", "((typeof value))"] {
                replay_after_source("number | string", body, query_first, strict);
            }
        }
    }
}
