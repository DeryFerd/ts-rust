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
    module_state: CanonicalModuleState,
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
                module_state,
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
    let mut context = context(&parsed, file, true, CanonicalModuleState::Script);
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

#[test]
fn expando_assignment_accesses_reuse_properties_without_exposing_expression_symbols() {
    for source in [
        "const foo = () => {}; foo.bar = 42; export {};",
        "const foo = function() {}; foo.bar = 42; export {};",
        "function foo() {} foo.bar = 42; const copy = foo.bar; export {};",
    ] {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(4_101);
        let mut context = context(&parsed, file, false, CanonicalModuleState::External);
        let (expression, access, name) = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                let NodeData::BinaryExpression(binary) = &record.data else {
                    return None;
                };
                let NodeData::PropertyAccessExpression(access) =
                    &parsed.arena.get(binary.left)?.data
                else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, id),
                    NodeRef::new(parsed.arena.id(), file, binary.left),
                    NodeRef::new(parsed.arena.id(), file, access.name),
                ))
            })
            .unwrap();
        let property = context.file(file).unwrap().1.symbol(expression).unwrap();

        assert_eq!(context.get_symbol_at_location(expression).unwrap(), None);
        let warm = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.diagnostics().len(),
        );
        for _ in 0..2 {
            assert_eq!(context.get_symbol_at_location(access), Ok(Some(property)));
            assert_eq!(context.get_symbol_at_location(name), Ok(Some(property)));
            assert_eq!(context.get_symbol_at_location(expression), Ok(None));
            assert_eq!(
                context.get_symbol_declarations(property),
                Ok(&[expression][..])
            );
        }
        assert_eq!(
            context.file(file).unwrap().1.symbol(expression),
            Some(property)
        );
        assert!(context.store().symbol_node_links(access).is_none());
        assert!(context.store().symbol_node_links(name).is_none());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.diagnostics().len(),
            ),
            warm,
        );
    }
}

#[test]
fn annotated_expando_accesses_keep_declared_property_symbols() {
    let parsed = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {} ",
        "const callback: { (): void; items?: string[] } = () => undefined; ",
        "callback.items = [];",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4_102);
    let mut context = context(&parsed, file, false, CanonicalModuleState::Script);
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::PropertyDeclaration(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap();
    let (expression, access, name) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::BinaryExpression(binary) = &record.data else {
                return None;
            };
            let NodeData::PropertyAccessExpression(access) = &parsed.arena.get(binary.left)?.data
            else {
                return None;
            };
            Some((
                NodeRef::new(parsed.arena.id(), file, node),
                NodeRef::new(parsed.arena.id(), file, binary.left),
                NodeRef::new(parsed.arena.id(), file, access.name),
            ))
        })
        .unwrap();
    let declared = context.file(file).unwrap().1.symbol(declaration).unwrap();
    let assigned = context.file(file).unwrap().1.symbol(expression).unwrap();
    assert_ne!(declared, assigned);
    assert_eq!(context.get_symbol_at_location(access), Ok(Some(declared)));
    assert_eq!(context.get_symbol_at_location(name), Ok(Some(declared)));
    assert_eq!(context.get_symbol_at_location(expression), Ok(None));
    assert_eq!(
        context.get_symbol_declarations(declared),
        Ok(&[declaration][..]),
    );
    assert_eq!(
        context.get_symbol_declarations(assigned),
        Ok(&[expression][..]),
    );
}
