use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, TypeId, TypeRecord, type_to_string,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "type A2 = keyof { a: 1; b: 2 };\n",
    "type A2R = keyof { b: 3; a: 4 };\n",
    "type A1 = keyof { a: 1 };\n",
    "type E = keyof {};\n",
    "type SI = keyof { [k: string]: unknown };\n",
    "type NI = keyof { [k: number]: unknown };\n",
    "type MN = keyof { fixed: 1; [k: number]: unknown };\n",
    "type MS = keyof { fixed: 1; [k: string]: unknown };\n",
    "type MSP = keyof ({ fixed: 1; [k: string]: unknown });\n",
    "interface I { a: 1; b: 2 }\n",
    "interface J { a: 1; b: 2 }\n",
    "interface One { only: 1 }\n",
    "interface Empty {}\n",
    "interface Table { [k: string]: unknown }\n",
    "interface Node { next: Node }\n",
    "type KI = keyof I;\n",
    "type KI2 = keyof I;\n",
    "type KJ = keyof J;\n",
    "type KO = keyof One;\n",
    "type KE = keyof Empty;\n",
    "type KT = keyof Table;\n",
    "type KN = keyof Node;\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/keyof-types.ts\""),
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

fn named_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    kind: SyntaxKind,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::TypeAliasDeclaration(declaration) => declaration.name,
                NodeData::InterfaceDeclaration(declaration) => declaration.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn alias_parts(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> (SemanticSymbolId, NodeRef) {
    let rhs = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, alias.type_))
        })
        .unwrap_or_else(|| panic!("missing alias {expected}"));
    (
        named_symbol(
            parsed,
            file,
            context,
            SyntaxKind::TypeAliasDeclaration,
            expected,
        ),
        rhs,
    )
}

fn alias_type(context: &CanonicalCheckerContext<'_>, alias: SemanticSymbolId) -> TypeId {
    context
        .store()
        .type_alias_links(alias)
        .and_then(|links| links.declared_type)
        .expect("source checking resolves the keyof alias")
}

fn interface_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
        .expect("source checking resolves the keyof operand")
}

fn union_parts(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> (Vec<TypeId>, Option<TypeId>) {
    let Some(TypeData::Union(union)) = context.store().type_payload(type_).map(TypeRecord::data)
    else {
        panic!("expected union type {type_:?}");
    };
    (union.union.types.clone(), union.origin)
}

#[test]
fn source_keyof_aliases_preserve_canonical_keys_origins_and_warm_caches() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);
    let aliases = [
        "A2", "A2R", "A1", "E", "SI", "NI", "MN", "MS", "MSP", "KI", "KI2", "KJ", "KO", "KE", "KT",
        "KN",
    ]
    .into_iter()
    .map(|name| (name, alias_parts(&parsed, file, &context, name)))
    .collect::<std::collections::BTreeMap<_, _>>();
    let interfaces = ["I", "J", "One", "Empty", "Table", "Node"]
        .into_iter()
        .map(|name| {
            (
                name,
                named_symbol(
                    &parsed,
                    file,
                    &context,
                    SyntaxKind::InterfaceDeclaration,
                    name,
                ),
            )
        })
        .collect::<std::collections::BTreeMap<_, _>>();

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let type_of = |name: &str| alias_type(&context, aliases[name].0);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let a = bootstrap.cached_string_literal_type("a").unwrap();
    let b = bootstrap.cached_string_literal_type("b").unwrap();
    let fixed = bootstrap.cached_string_literal_type("fixed").unwrap();
    let only = bootstrap.cached_string_literal_type("only").unwrap();
    let next = bootstrap.cached_string_literal_type("next").unwrap();

    assert_eq!(type_of("A2"), type_of("A2R"));
    let (mut a2, a2_origin) = union_parts(&context, type_of("A2"));
    a2.sort_unstable();
    let mut expected_a2 = vec![a, b];
    expected_a2.sort_unstable();
    assert_eq!(a2, expected_a2);
    assert_eq!(a2_origin, None);
    assert_eq!(type_of("A1"), a);
    assert_eq!(type_of("E"), bootstrap.never_type);
    assert_eq!(type_of("SI"), bootstrap.string_or_number_type);
    assert_eq!(type_of("NI"), bootstrap.number_type);
    let (mut mn, mn_origin) = union_parts(&context, type_of("MN"));
    mn.sort_unstable();
    let mut expected_mn = vec![bootstrap.number_type, fixed];
    expected_mn.sort_unstable();
    assert_eq!(mn, expected_mn);
    assert_eq!(mn_origin, None);
    assert_eq!(type_of("MS"), bootstrap.string_or_number_type);
    assert_eq!(type_of("MSP"), bootstrap.string_or_number_type);

    let i = interface_type(&context, interfaces["I"]);
    let j = interface_type(&context, interfaces["J"]);
    let ki = type_of("KI");
    assert_eq!(type_of("KI2"), ki);
    assert_ne!(type_of("KJ"), ki);
    for (result, target, display) in [(ki, i, "keyof I"), (type_of("KJ"), j, "keyof J")] {
        let (keys, origin) = union_parts(&context, result);
        let mut keys = keys;
        keys.sort_unstable();
        assert_eq!(keys, expected_a2);
        let origin = origin.expect("named two-key keyof keeps its Index origin");
        let Some(TypeData::Index(index)) =
            context.store().type_payload(origin).map(TypeRecord::data)
        else {
            panic!("keyof origin must be an Index type");
        };
        assert_eq!(index.target, target);
        assert_eq!(type_to_string(context.store(), result).unwrap(), display);
    }
    assert_eq!(type_of("KO"), only);
    assert_eq!(type_of("KE"), bootstrap.never_type);
    assert_eq!(type_of("KT"), bootstrap.string_or_number_type);
    let table = interface_type(&context, interfaces["Table"]);
    let Some(TypeData::Interface(table)) =
        context.store().type_payload(table).map(TypeRecord::data)
    else {
        panic!("Table must resolve to an interface");
    };
    assert_eq!(
        table.declared_index_infos.as_deref(),
        table.reference.object.structured.index_infos.as_deref(),
    );
    assert_eq!(table.declared_index_infos.as_deref().unwrap().len(), 1);
    assert_eq!(type_of("KN"), next);

    for (_, (alias, rhs)) in &aliases {
        assert_eq!(
            context
                .store()
                .type_node_links(*rhs)
                .and_then(|links| links.resolved_type),
            Some(alias_type(&context, *alias)),
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().type_alias_len(),
        context.store().index_info_len(),
        context.store().properties_type_cache_len(),
        context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .string_literal_cache_len(),
        context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .union_cache_len(),
        context.diagnostics().clone(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().type_alias_len(),
            context.store().index_info_len(),
            context.store().properties_type_cache_len(),
            context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .string_literal_cache_len(),
            context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .union_cache_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}
