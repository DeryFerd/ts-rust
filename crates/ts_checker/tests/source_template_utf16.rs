use ts_ast::{FileId, NodeData, NodeRef, decode_js_string, encode_js_string};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeMapperStore,
    IntrinsicBootstrapOptions, TypeData, TypeId, type_records::LiteralValue,
};
use ts_core::JsString;
use ts_parser::{ParseResult, parse_source_file};

fn store() -> CanonicalTypeMapperStore {
    let mut store = CanonicalTypeMapperStore::new();
    store
        .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
        .unwrap();
    store
}

fn literal(store: &mut CanonicalTypeMapperStore, value: &str) -> TypeId {
    store
        .get_template_literal_type(&[value.to_owned()], &[])
        .unwrap()
}

fn literal_units(store: &CanonicalTypeMapperStore, type_: TypeId) -> Vec<u16> {
    let TypeData::Literal(literal) = store.type_payload(type_).unwrap().data() else {
        panic!("expected a string literal")
    };
    let LiteralValue::String(value) = &literal.value else {
        panic!("expected a string literal")
    };
    decode_js_string(value).as_units().to_vec()
}

fn encoded(units: &[u16]) -> String {
    encode_js_string(&JsString::from_units(units.to_vec()))
}

fn mapping_symbol(store: &mut CanonicalTypeMapperStore, name: &str) -> SemanticSymbolId {
    store.alloc_transient_symbol(
        SymbolFlags::TYPE_ALIAS,
        EscapedName::source(name),
        CheckFlags::NONE,
    )
}

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/template-utf16.ts\""),
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

fn alias_type(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> TypeId {
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
        .unwrap_or_else(|| panic!("missing type alias {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    let symbol = context.store().get_merged_symbol(raw).unwrap();
    context
        .store()
        .type_alias_links(symbol)
        .and_then(|links| links.declared_type)
        .unwrap_or_else(|| panic!("missing declared type for {expected}"))
}

#[test]
fn encoded_lone_surrogates_keep_distinct_canonical_literal_identities() {
    let mut store = store();
    let high = literal(&mut store, &encoded(&[0xd800]));
    let low = literal(&mut store, &encoded(&[0xdc00]));

    assert_ne!(high, low);
    assert_eq!(literal_units(&store, high), [0xd800]);
    assert_eq!(literal_units(&store, low), [0xdc00]);
    assert_eq!(literal(&mut store, &encoded(&[0xd800])), high);
    assert_eq!(literal(&mut store, &encoded(&[0xdc00])), low);
}

#[test]
fn adjacent_template_surrogate_halves_share_the_combined_literal_identity() {
    let mut store = store();
    let high_text = encoded(&[0xd83d]);
    let low_text = encoded(&[0xde00]);
    let high = literal(&mut store, &high_text);
    let low = literal(&mut store, &low_text);
    let pair = literal(&mut store, "\u{1f600}");

    for (texts, types) in [
        (
            vec![String::new(), String::new(), String::new()],
            vec![high, low],
        ),
        (vec![high_text.clone(), String::new()], vec![low]),
        (vec![String::new(), low_text.clone()], vec![high]),
    ] {
        let result = store.get_template_literal_type(&texts, &types).unwrap();
        assert_eq!(result, pair);
        assert_eq!(literal_units(&store, result), [0xd83d, 0xde00]);
    }

    let gapped = store
        .get_template_literal_type(
            &[String::new(), "-".to_owned(), String::new()],
            &[high, low],
        )
        .unwrap();
    assert_ne!(gapped, pair);
    assert_eq!(
        literal_units(&store, gapped),
        [0xd83d, u16::from(b'-'), 0xde00]
    );
}

#[test]
fn intrinsic_mappings_preserve_encoded_surrogate_units() {
    let mut store = store();
    let uppercase = mapping_symbol(&mut store, "Uppercase");
    let lowercase = mapping_symbol(&mut store, "Lowercase");
    let capitalize = mapping_symbol(&mut store, "Capitalize");
    let uncapitalize = mapping_symbol(&mut store, "Uncapitalize");

    let high = literal(&mut store, &encoded(&[0xd800]));
    let surrounded = literal(
        &mut store,
        &encoded(&[u16::from(b'A'), 0xd800, u16::from(b'B')]),
    );
    let low_prefix = literal(&mut store, &encoded(&[0xdc00, u16::from(b'x')]));
    let high_prefix = literal(&mut store, &encoded(&[0xd834, u16::from(b'X')]));

    let upper = store.get_string_mapping_type(uppercase, high).unwrap();
    let lower = store
        .get_string_mapping_type(lowercase, surrounded)
        .unwrap();
    let capitalized = store
        .get_string_mapping_type(capitalize, low_prefix)
        .unwrap();
    let uncapitalized = store
        .get_string_mapping_type(uncapitalize, high_prefix)
        .unwrap();

    assert_eq!(literal_units(&store, upper), [0xd800]);
    assert_eq!(
        literal_units(&store, lower),
        [u16::from(b'a'), 0xd800, u16::from(b'b')]
    );
    assert_eq!(
        literal_units(&store, capitalized),
        [0xdc00, u16::from(b'x')]
    );
    assert_eq!(
        literal_units(&store, uncapitalized),
        [0xd834, u16::from(b'X')]
    );
}

#[test]
fn production_template_concatenation_combines_only_adjacent_surrogates() {
    let parsed = parse_source_file(concat!(
        "type High = \"\\uD83D\";\n",
        "type Low = \"\\uDE00\";\n",
        "type Pair = `${High}${Low}`;\n",
        "type Gapped = `${High}-${Low}`;\n",
        "const pair: Pair = \"\\uD83D\\uDE00\";\n",
        "const gapped: Gapped = \"\\uD83D-\\uDE00\";\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let pair = alias_type(&parsed, file, &context, "Pair");
    let gapped = alias_type(&parsed, file, &context, "Gapped");
    assert_eq!(literal_units(context.store(), pair), [0xd83d, 0xde00]);
    assert_eq!(
        literal_units(context.store(), gapped),
        [0xd83d, u16::from(b'-'), 0xde00]
    );
}

#[test]
fn production_assignment_distinguishes_lone_high_and_low_surrogates() {
    let parsed = parse_source_file("const value: \"\\uD800\" = \"\\uDC00\";");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].diagnostic.code(), 2322);
    assert_eq!(
        diagnostics[0].diagnostic.arguments,
        ["\"\\uDC00\"", "\"\\uD800\""]
    );
}

#[test]
fn type_queries_preserve_identical_surrogate_pair_literal_types() {
    let parsed = parse_source_file(concat!(
        "const literal = \"\\u{1F600}\" as const;\n",
        "const braceEscaped = \"\\u{D83D}\\u{DE00}\" as const;\n",
        "const adjacentEscaped = \"\\uD83D\\uDE00\" as const;\n",
        "const first: typeof literal = braceEscaped;\n",
        "const second: typeof adjacentEscaped = braceEscaped;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let queries = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            matches!(record.data, NodeData::TypeQueryNode(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(queries.len(), 2);
    let types = queries
        .iter()
        .map(|query| {
            let NodeData::TypeQueryNode(type_query) = &parsed.arena.get(query.node).unwrap().data
            else {
                panic!("the selected node must be a type query")
            };
            let name = NodeRef::new(query.arena, query.file, type_query.expr_name);
            assert!(
                context
                    .store()
                    .symbol_node_links(name)
                    .and_then(|links| links.resolved_symbol)
                    .is_some(),
                "the referenced identifier must own the resolved symbol",
            );
            assert!(
                context
                    .store()
                    .symbol_node_links(*query)
                    .and_then(|links| links.resolved_symbol)
                    .is_none(),
                "the typeof wrapper must not own the identifier symbol",
            );
            context
                .store()
                .type_node_links(*query)
                .and_then(|links| links.resolved_type)
                .expect("type query must resolve its referenced literal")
        })
        .collect::<Vec<_>>();
    assert_eq!(types[0], types[1]);
    assert_eq!(literal_units(context.store(), types[0]), [0xd83d, 0xde00]);

    let type_count = context.store().type_len();
    context.recheck_source_file(file).unwrap();
    assert_eq!(context.store().type_len(), type_count);
    assert!(context.diagnostics().is_empty());
}
