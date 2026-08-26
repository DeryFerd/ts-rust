use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions};
use ts_parser::{ParseResult, parse_source_file};

fn context(
    parsed: &ParseResult,
    file: FileId,
    declaration_file: bool,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/locations.ts\""),
                CanonicalSourceLanguage::TypeScript,
                declaration_file,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

#[test]
fn literal_annotation_tokens_use_their_production_type_without_checking_declaration_files() {
    let parsed = parse_source_file(concat!(
        "interface Shape { ",
        "enabled: true; disabled: false; text: 'ready'; count: 42; ",
        "negative: -2; large: 23n; nothing: null; }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4_100);
    let mut context = context(&parsed, file, true);
    let literals = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::LiteralTypeNode(literal) = &record.data else {
                return None;
            };
            Some((
                NodeRef::new(parsed.arena.id(), file, node),
                NodeRef::new(parsed.arena.id(), file, literal.literal),
            ))
        })
        .collect::<Vec<_>>();
    let expected = ["true", "false", "\"ready\"", "42", "-2", "23n", "null"];
    assert_eq!(literals.len(), expected.len());

    for ((annotation, literal), expected) in literals.iter().zip(expected) {
        let type_ = context.get_type_at_location(*literal).unwrap();
        assert_eq!(context.type_to_string(type_).unwrap(), expected);
        assert_eq!(context.get_type_from_type_node(*annotation), Ok(type_));
        assert_eq!(context.get_symbol_at_location(*literal).unwrap(), None);
        assert!(context.store().type_node_links(*literal).is_none());
    }

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.diagnostics().len(),
    );
    for (annotation, literal) in literals {
        assert_eq!(
            context.get_type_at_location(literal).unwrap(),
            context.get_type_from_type_node(annotation).unwrap(),
        );
    }
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.diagnostics().len(),
        ),
        warm,
    );
    assert!(
        context
            .store()
            .source_file_links(context.source_file(file).unwrap())
            .is_none_or(|links| !links.type_checked),
    );
}
