use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(9_208);
const LIBRARIES: &[(&str, &str)] = &[
    (
        "lib.es5.d.ts",
        include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
    ),
    (
        "lib.decorators.d.ts",
        include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
    ),
    (
        "lib.decorators.legacy.d.ts",
        include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
    ),
];

struct Fixture {
    source: ParseResult,
    libraries: Vec<ParseResult>,
}

impl Fixture {
    fn new(source: &str) -> Self {
        let source = parse_source_file(source);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let libraries = LIBRARIES
            .iter()
            .map(|(name, text)| {
                let parsed = parse_source_file(text);
                assert!(
                    parsed.diagnostics.is_empty(),
                    "{name}: {:?}",
                    parsed.diagnostics
                );
                parsed
            })
            .collect();
        Self { source, libraries }
    }

    fn context(&self, strict: bool, exact: bool) -> CanonicalCheckerContext<'_> {
        let files = self
            .libraries
            .iter()
            .enumerate()
            .map(|(index, parsed)| {
                (
                    FileId::new(u32::try_from(index).unwrap()),
                    parsed,
                    format!("\"/__typescript/lib/{}\"", LIBRARIES[index].0),
                    true,
                )
            })
            .chain(std::iter::once((
                FILE,
                &self.source,
                "\"/project/mapped-result-sessions.ts\"".to_owned(),
                false,
            )))
            .collect::<Vec<_>>();
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, library) in &files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    *file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        *library,
                        *library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (file, parsed, _, _) in &files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, *file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: strict,
                    exact_optional_property_types: exact,
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }
}

fn declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name = match &record.data {
                NodeData::TypeAliasDeclaration(alias) => alias.name,
                NodeData::InterfaceDeclaration(interface) => interface.name,
                NodeData::VariableDeclaration(variable) => variable.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let symbol = checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    checker.store().get_merged_symbol(symbol).unwrap()
}

fn alias_type(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult, name: &str) -> TypeId {
    let owner = symbol(checker, declaration(parsed, FILE, name));
    checker
        .store()
        .type_alias_links(owner)
        .unwrap()
        .declared_type
        .unwrap()
}

fn call_result(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> TypeId {
    let node = declaration(parsed, FILE, name);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(node.node).unwrap().data else {
        panic!("expected a call result declaration")
    };
    let owner = symbol(checker, node);
    let name = NodeRef::new(node.arena, node.file, variable.name);
    let call = NodeRef::new(node.arena, node.file, variable.initializer.unwrap());
    assert_eq!(
        parsed.arena.get(call.node).unwrap().kind,
        SyntaxKind::CallExpression
    );
    let type_ = checker
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(checker.get_type_at_location(name), Ok(type_));
    assert_eq!(checker.get_symbol_at_location(name), Ok(Some(owner)));
    assert_eq!(checker.get_type_at_location(call), Ok(type_));
    let signature = checker
        .store()
        .signature_links(call)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    assert_eq!(
        checker
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type(),
        Some(type_)
    );
    type_
}

fn assert_array_alias(checker: &CanonicalCheckerContext<'_>, fixture: &Fixture) -> TypeId {
    let payload = alias_type(checker, &fixture.source, "Payload");
    let owner = symbol(checker, declaration(&fixture.source, FILE, "Payload"));
    let alias = checker
        .store()
        .type_payload(payload)
        .unwrap()
        .alias()
        .unwrap();
    assert_eq!(
        checker.store().type_alias(alias).unwrap().symbol(),
        Some(owner)
    );
    let array = alias_type(checker, &fixture.source, "Payloads");
    let TypeData::TypeReference(reference) = checker.store().type_payload(array).unwrap().data()
    else {
        panic!("the source array alias must keep its Array reference")
    };
    let target = checker.global_types().array_type;
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[payload][..])
    );
    let array_owner = symbol(
        checker,
        declaration(&fixture.libraries[0], FileId::new(0), "Array"),
    );
    assert_eq!(
        checker.store().type_payload(target).unwrap().symbol(),
        Some(array_owner)
    );
    array
}

fn assert_interface_item(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
    array: TypeId,
    has_index: bool,
) {
    let node = declaration(parsed, FILE, name);
    let owner = symbol(checker, node);
    let type_ = checker
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap();
    let TypeData::Interface(interface) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("the source interface must retain its declared type")
    };
    let structured = &interface.reference.object.structured;
    assert_eq!(
        structured
            .index_infos
            .as_ref()
            .is_some_and(|indexes| !indexes.is_empty()),
        has_index
    );
    let property = checker
        .store()
        .symbol_table(structured.members.unwrap())
        .unwrap()
        .get_source("item")
        .unwrap();
    assert!(
        checker
            .store()
            .symbol(property)
            .unwrap()
            .flags()
            .contains(SymbolFlags::OPTIONAL)
    );
    let property_node = checker
        .store()
        .symbol(property)
        .unwrap()
        .value_declaration()
        .unwrap();
    assert_eq!(symbol(checker, property_node), property);
    let NodeData::PropertyDeclaration(declaration) =
        &parsed.arena.get(property_node.node).unwrap().data
    else {
        panic!("the item must retain its real source declaration")
    };
    let annotation = NodeRef::new(node.arena, node.file, declaration.type_.unwrap());
    assert_eq!(
        checker
            .store()
            .type_node_links(annotation)
            .unwrap()
            .resolved_type,
        Some(array)
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(property)
            .unwrap()
            .resolved_type,
        Some(array)
    );
}

fn assert_union(checker: &CanonicalCheckerContext<'_>, result: TypeId, expected: &[TypeId]) {
    let TypeData::Union(union) = checker.store().type_payload(result).unwrap().data() else {
        panic!("the result must retain its canonical union")
    };
    let mut actual = union.union.types.clone();
    actual.sort_unstable();
    let mut expected = expected.to_vec();
    expected.sort_unstable();
    assert_eq!(actual, expected);
}

fn assert_complete(checker: &CanonicalCheckerContext<'_>) {
    let file = checker.source_file(FILE).unwrap();
    let links = checker.store().source_file_links(file).unwrap();
    assert!(links.type_checked);
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
}

fn assert_recheck_stable(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let snapshot = |checker: &CanonicalCheckerContext<'_>| {
        let store = checker.store();
        (
            [
                store.type_len(),
                store.type_alias_len(),
                store.symbol_len(),
                store.signature_len(),
                store.type_predicate_len(),
                store.mapper_len(),
                store.index_info_len(),
                store.properties_type_cache_len(),
                store.symbol_store().symbol_table_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ],
            store.relation_state_snapshot(),
            parsed
                .arena
                .iter()
                .map(|(node, _)| {
                    let node = NodeRef::new(parsed.arena.id(), FILE, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            store
                .symbol_store()
                .symbols()
                .map(|(symbol, _)| {
                    (
                        symbol,
                        store.value_symbol_links(symbol).cloned(),
                        store.declared_type_links(symbol).cloned(),
                        store.type_alias_links(symbol).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            store
                .source_file_links(checker.source_file(FILE).unwrap())
                .cloned(),
            checker.diagnostics().clone(),
        )
    };
    let before = snapshot(checker);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        assert_complete(checker);
        assert_eq!(snapshot(checker), before);
        checker.recheck_source_file(FILE).unwrap();
        assert_complete(checker);
        assert_eq!(snapshot(checker), before);
    }
}

#[test]
fn optional_indexed_returns_keep_the_source_array_and_exact_sentinel() {
    let fixture = Fixture::new(concat!(
        "type Payload = { id: number };\n",
        "type Payloads = Payload[];\n",
        "interface Plain { item?: Payloads }\n",
        "interface Indexed { [key: string]: Payloads | undefined; item?: Payloads }\n",
        "declare function read<Model, Key extends keyof Model>(value: Model, key: Key): Model[Key];\n",
        "declare const plain: Plain;\n",
        "declare const indexed: Indexed;\n",
        "const plainValue = read<Plain, 'item'>(plain, 'item');\n",
        "const indexedValue = read<Indexed, 'item'>(indexed, 'item');\n",
    ));
    for (strict, exact) in [(false, false), (true, false), (true, true)] {
        let mut checker = fixture.context(strict, exact);
        checker.check_source_file(FILE).unwrap();
        assert_complete(&checker);
        let array = assert_array_alias(&checker, &fixture);
        let plain = call_result(&mut checker, &fixture.source, "plainValue");
        let indexed = call_result(&mut checker, &fixture.source, "indexedValue");
        assert_eq!(plain, indexed);
        if strict {
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let sentinel = if exact {
                bootstrap.missing_type
            } else {
                bootstrap.undefined_type
            };
            assert_union(&checker, plain, &[array, sentinel]);
        } else {
            assert_eq!(plain, array);
        }
        assert_interface_item(&checker, &fixture.source, "Plain", array, false);
        assert_interface_item(&checker, &fixture.source, "Indexed", array, true);
        assert_recheck_stable(&mut checker, &fixture.source);
        assert_eq!(
            call_result(&mut checker, &fixture.source, "plainValue"),
            plain
        );
        assert_eq!(
            call_result(&mut checker, &fixture.source, "indexedValue"),
            indexed
        );
        assert_eq!(assert_array_alias(&checker, &fixture), array);
    }
}

#[test]
fn template_return_unions_keep_array_targets_and_reduce_covered_patterns() {
    let fixture = Fixture::new(concat!(
        "type Payload = { id: number };\n",
        "type Payloads = Payload[];\n",
        "declare function build<T>(): T | number | `id-${number}`;\n",
        "const arrayResult = build<Payloads>();\n",
        "const reduced = build<string>();\n",
        "const reducedArray = build<Payloads | string>();\n",
        "const arrayAgain = build<Payloads>();\n",
        "const reducedAgain = build<string>();\n",
    ));
    let mut checker = fixture.context(true, false);
    checker.check_source_file(FILE).unwrap();
    assert_complete(&checker);
    let array = assert_array_alias(&checker, &fixture);
    let patterns = fixture
        .source
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::TemplateLiteralType).then_some(NodeRef::new(
                fixture.source.arena.id(),
                FILE,
                node,
            ))
        })
        .collect::<Vec<_>>();
    let [pattern] = patterns.as_slice() else {
        panic!("expected the declared return pattern")
    };
    let pattern = checker.get_type_at_location(*pattern).unwrap();
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    let TypeData::TemplateLiteral(template) = checker.store().type_payload(pattern).unwrap().data()
    else {
        panic!("the return pattern must keep its template type")
    };
    assert_eq!(template.texts, ["id-", ""]);
    assert_eq!(template.types, [number]);
    let array_result = call_result(&mut checker, &fixture.source, "arrayResult");
    assert_union(&checker, array_result, &[array, number, pattern]);
    let reduced = call_result(&mut checker, &fixture.source, "reduced");
    assert_union(&checker, reduced, &[string, number]);
    assert_eq!(checker.type_to_string(reduced).unwrap(), "string | number");
    let reduced_array = call_result(&mut checker, &fixture.source, "reducedArray");
    assert_union(&checker, reduced_array, &[array, string, number]);
    assert_eq!(
        call_result(&mut checker, &fixture.source, "arrayAgain"),
        array_result
    );
    assert_eq!(
        call_result(&mut checker, &fixture.source, "reducedAgain"),
        reduced
    );
    assert_recheck_stable(&mut checker, &fixture.source);
    assert_eq!(
        call_result(&mut checker, &fixture.source, "arrayResult"),
        array_result
    );
    assert_eq!(
        call_result(&mut checker, &fixture.source, "reduced"),
        reduced
    );
    assert_eq!(
        call_result(&mut checker, &fixture.source, "reducedArray"),
        reduced_array
    );
    assert_eq!(assert_array_alias(&checker, &fixture), array);
}
