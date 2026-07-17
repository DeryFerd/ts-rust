use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, TypeId, TypeRecord,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "type Pair = [left: string, right?: number,];\n",
    "type Frozen = readonly [name: string, count?: number];\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/tuple-types.ts\""),
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

fn alias_parts(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> (SemanticSymbolId, NodeRef) {
    let (declaration, rhs) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (name.text == expected).then_some((
                NodeRef::new(parsed.arena.id(), file, node),
                NodeRef::new(parsed.arena.id(), file, alias.type_),
            ))
        })
        .unwrap_or_else(|| panic!("missing alias {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    (context.store().get_merged_symbol(raw).unwrap(), rhs)
}

fn alias_type(context: &CanonicalCheckerContext<'_>, alias: SemanticSymbolId) -> TypeId {
    context
        .store()
        .type_alias_links(alias)
        .and_then(|links| links.declared_type)
        .expect("source checking resolves the tuple alias")
}

#[test]
fn source_tuple_aliases_publish_mutable_and_readonly_type_nodes_cold_and_warm() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);
    let (pair, pair_tuple) = alias_parts(&parsed, file, &context, "Pair");
    let (frozen, readonly_operator) = alias_parts(&parsed, file, &context, "Frozen");
    let NodeData::TypeOperatorNode(operator) =
        &parsed.arena.get(readonly_operator.node).unwrap().data
    else {
        panic!("Frozen has a readonly type operator")
    };
    let frozen_tuple = NodeRef::new(readonly_operator.arena, readonly_operator.file, operator.type_);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    let pair_type = alias_type(&context, pair);
    let frozen_type = alias_type(&context, frozen);
    assert_ne!(pair_type, frozen_type);
    for type_ in [pair_type, frozen_type] {
        assert!(matches!(
            context.store().type_payload(type_).map(TypeRecord::data),
            Some(TypeData::TypeReference(_))
        ));
    }
    assert_eq!(
        context
            .store()
            .type_node_links(pair_tuple)
            .and_then(|links| links.resolved_type),
        Some(pair_type),
    );
    for node in [readonly_operator, frozen_tuple] {
        assert_eq!(
            context
                .store()
                .type_node_links(node)
                .and_then(|links| links.resolved_type),
            Some(frozen_type),
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().type_alias_len(),
        context.store().signature_len(),
        context.store().index_info_len(),
        context.store().type_node_links(pair_tuple).cloned(),
        context.store().type_node_links(readonly_operator).cloned(),
        context.store().type_node_links(frozen_tuple).cloned(),
        context.diagnostics().clone(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(alias_type(&context, pair), pair_type);
    assert_eq!(alias_type(&context, frozen), frozen_type);
    assert_eq!(
        (
            context.store().type_len(),
            context.store().type_alias_len(),
            context.store().signature_len(),
            context.store().index_info_len(),
            context.store().type_node_links(pair_tuple).cloned(),
            context.store().type_node_links(readonly_operator).cloned(),
            context.store().type_node_links(frozen_tuple).cloned(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}
