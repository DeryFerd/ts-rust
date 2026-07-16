use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, TypeId};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "type StringTable = { readonly [key: string]: number; };\n",
    "type NumberTable = { [position: number]: string; };\n",
    "function readString(table: StringTable): number { return table[\"answer\"]; }\n",
    "function readNumber(table: NumberTable): string { return table[0]; }\n",
);

fn alias_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> ts_binder::SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing alias {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn element_type(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    index_kind: SyntaxKind,
) -> TypeId {
    let node = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ElementAccessExpression(access) = &record.data else {
                return None;
            };
            (parsed.arena.get(access.argument_expression)?.kind == index_kind)
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing {index_kind:?} element access"));
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
}

#[test]
#[allow(clippy::too_many_lines)] // Proves both key domains and exact cold/warm source composition.
fn source_declared_string_and_number_index_signatures_feed_element_access_cold_and_warm() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/index-signatures.ts\""),
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
    let string_table = alias_symbol(&parsed, file, &context, "StringTable");
    let number_table = alias_symbol(&parsed, file, &context, "NumberTable");
    let before_indexes = context.store().index_info_len();

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    assert_eq!(context.store().index_info_len(), before_indexes + 2);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let expected = [
        (
            string_table,
            bootstrap.string_type,
            bootstrap.number_type,
            true,
        ),
        (
            number_table,
            bootstrap.number_type,
            bootstrap.string_type,
            false,
        ),
    ];
    for (alias, key_type, value_type, readonly) in expected {
        let object_type = context
            .store()
            .type_alias_links(alias)
            .and_then(|links| links.declared_type)
            .expect("source checking resolves the alias");
        let TypeData::Object(object) = context.store().type_payload(object_type).unwrap().data()
        else {
            panic!("index type literals resolve to anonymous objects")
        };
        let [index] = object
            .structured
            .index_infos
            .as_deref()
            .expect("index info is attached")
        else {
            panic!("the bounded alias has exactly one index info")
        };
        let info = context.store().index_info(*index).unwrap();
        assert_eq!(info.key_type(), key_type);
        assert_eq!(info.value_type(), value_type);
        assert_eq!(info.is_readonly(), readonly);
        assert!(info.declaration().is_some());
        assert_eq!(info.index_symbol(), None);
        assert!(info.components().is_empty());
        let members = object
            .structured
            .members
            .expect("bound member table is retained");
        let table = context.store().symbol_table(members).unwrap();
        assert_eq!(table.len(), 1);
        assert!(table.get(InternalSymbolName::Index.as_ref()).is_some());
    }
    assert_eq!(
        context
            .type_to_string(element_type(
                &parsed,
                file,
                &context,
                SyntaxKind::StringLiteral,
            ))
            .unwrap(),
        "number"
    );
    assert_eq!(
        context
            .type_to_string(element_type(
                &parsed,
                file,
                &context,
                SyntaxKind::NumericLiteral,
            ))
            .unwrap(),
        "string"
    );

    let warm_state = (context.store().type_len(), context.store().index_info_len());
    context.check_source_file(file).unwrap();
    assert_eq!(
        (context.store().type_len(), context.store().index_info_len()),
        warm_state
    );
    assert!(context.diagnostics().is_empty());
}
