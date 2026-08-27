use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput,
};
use ts_parser::{ParseResult, parse_source_file};

struct TestSource<'arena> {
    parsed: &'arena ParseResult,
    file: FileId,
    path: &'static str,
    declaration_file: bool,
    module_state: CanonicalModuleState,
}

fn context<'arena>(
    sources: &[TestSource<'arena>],
    entries: impl IntoIterator<Item = CanonicalModuleResolutionEntry>,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for source in sources {
        assert!(
            source.parsed.diagnostics.is_empty(),
            "{:?}",
            source.parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &source.parsed.arena,
                source.parsed.source_file,
                source.file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(source.path),
                    CanonicalSourceLanguage::TypeScript,
                    source.declaration_file,
                    source.module_state,
                ),
            )
            .unwrap();
    }
    for source in sources {
        binder
            .bind_typescript_declaration_slice(&source.parsed.arena, source.file)
            .unwrap();
    }
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        sources
            .iter()
            .map(|source| (source.file, &source.parsed.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new(entries),
    )
    .unwrap()
}

fn first_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("the control contains {kind:?}"))
}

fn query_name(parsed: &ParseResult, query: NodeRef) -> NodeRef {
    let NodeData::TypeQueryNode(data) = &parsed.arena.get(query.node).unwrap().data else {
        panic!("the control contains a typeof query")
    };
    NodeRef::new(query.arena, query.file, data.expr_name)
}

fn assert_outer_value_query(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    expected_text: &str,
) {
    let query = first_node(parsed, file, SyntaxKind::TypeQuery);
    let name = query_name(parsed, query);
    let declaration = first_node(parsed, file, SyntaxKind::VariableDeclaration);
    let outer = checker.file(file).unwrap().1.symbol(declaration).unwrap();
    let expected = checker.get_type_from_type_node(query).unwrap();
    assert_eq!(checker.type_to_string(expected).unwrap(), expected_text);
    assert_eq!(
        checker
            .store()
            .symbol_node_links(name)
            .unwrap()
            .resolved_symbol,
        Some(outer)
    );
    assert!(checker.store().value_symbol_links(outer).is_none());
    let before = (
        checker.store().type_len(),
        checker.store().symbol_len(),
        checker.store().signature_len(),
        checker.store().mapper_len(),
    );
    assert_eq!(checker.get_type_from_type_node(query), Ok(expected));
    assert_eq!(
        (
            checker.store().type_len(),
            checker.store().symbol_len(),
            checker.store().signature_len(),
            checker.store().mapper_len(),
        ),
        before
    );
    assert!(checker.store().value_symbol_links(outer).is_none());
    assert!(checker.diagnostics().is_empty());
}

#[test]
fn outer_value_typeof_query_is_cold_and_warm_stable() {
    for (annotation, expected) in [
        ("any", "any"),
        ("unknown", "unknown"),
        ("string", "string"),
        ("number", "number"),
        ("bigint", "bigint"),
        ("boolean", "boolean"),
        ("symbol", "symbol"),
        ("void", "void"),
        ("undefined", "undefined"),
        ("never", "never"),
        ("object", "object"),
        ("null", "null"),
        ("number | string", "string | number"),
    ] {
        for annotation in [annotation.to_owned(), format!("(({annotation}))")] {
            let parsed = parse_source_file(&format!(
                "declare let chosen: {annotation}; namespace Consumer {{ type Q = typeof chosen; }}"
            ));
            let file = FileId::new(13_600);
            let mut checker = context(
                &[TestSource {
                    parsed: &parsed,
                    file,
                    path: "\"/outer-value.ts\"",
                    declaration_file: false,
                    module_state: CanonicalModuleState::Script,
                }],
                [],
            );
            assert_outer_value_query(&mut checker, &parsed, file, expected);
        }
    }
}

#[test]
fn resolved_interface_alias_does_not_hide_outer_typeof_value() {
    for (annotation, expected) in [
        ("number", "number"),
        ("(number)", "number"),
        ("number | string", "string | number"),
    ] {
        let parsed = parse_source_file(&format!(
            "declare let chosen: {annotation}; \
             namespace Types {{ export interface Shape {{}} }} \
             namespace Consumer {{ import chosen = Types.Shape; type Q = typeof chosen; }}",
        ));
        let file = FileId::new(13_601);
        let mut checker = context(
            &[TestSource {
                parsed: &parsed,
                file,
                path: "\"/alias-shadow.ts\"",
                declaration_file: false,
                module_state: CanonicalModuleState::Script,
            }],
            [],
        );
        let declaration = first_node(&parsed, file, SyntaxKind::ImportEqualsDeclaration);
        let interface = first_node(&parsed, file, SyntaxKind::InterfaceDeclaration);
        let alias = checker.file(file).unwrap().1.symbol(declaration).unwrap();
        let resolved = checker.resolve_alias(alias).unwrap();
        let AliasTargetState::Resolved(target) = resolved.target else {
            panic!("the real alias provider resolves the interface")
        };
        assert!(resolved.events.is_empty());
        assert!(
            checker
                .store()
                .symbol(target)
                .unwrap()
                .declarations()
                .unwrap()
                .contains(&interface)
        );
        let links = checker.store().alias_symbol_links(alias).cloned();
        assert_outer_value_query(&mut checker, &parsed, file, expected);
        assert_eq!(checker.store().alias_symbol_links(alias), links.as_ref());
        assert!(checker.store().value_symbol_links(alias).is_none());
    }
}

#[test]
fn qualified_ambient_import_typeof_reuses_uncached_scalar_annotations() {
    for (annotation, expected) in [("number", "number"), ("(null)", "null")] {
        let parsed = parse_source_file(&format!(
            "declare module 'values' {{ export const chosen: {annotation}; }} \
             declare module 'consumer' {{ \
             import * as Values from 'values'; type Q = typeof Values.chosen; }}"
        ));
        let file = FileId::new(13_604);
        let mut checker = context(
            &[TestSource {
                parsed: &parsed,
                file,
                path: "\"/qualified-value.d.ts\"",
                declaration_file: true,
                module_state: CanonicalModuleState::Script,
            }],
            [],
        );
        let query = first_node(&parsed, file, SyntaxKind::TypeQuery);
        let declaration = first_node(&parsed, file, SyntaxKind::VariableDeclaration);
        let symbol = checker.file(file).unwrap().1.symbol(declaration).unwrap();
        let result = checker.get_type_from_type_node(query).unwrap();
        assert_eq!(checker.type_to_string(result).unwrap(), expected);
        let before = (
            checker.store().type_len(),
            checker.store().symbol_len(),
            checker.store().signature_len(),
            checker.store().mapper_len(),
        );
        assert_eq!(checker.get_type_from_type_node(query), Ok(result));
        assert_eq!(
            (
                checker.store().type_len(),
                checker.store().symbol_len(),
                checker.store().signature_len(),
                checker.store().mapper_len(),
            ),
            before
        );
        assert!(checker.store().value_symbol_links(symbol).is_none());
        assert!(checker.diagnostics().is_empty());
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Cold lookup and later value publication share one checker.
fn cold_namespace_typeof_keeps_its_identity_after_value_publication() {
    let importer = parse_source_file(concat!(
        "import * as ns from './target'; ",
        "export type Copy = typeof ns; export const copied = ns;",
    ));
    let target = parse_source_file("export const value: number = 1;");
    let importer_file = FileId::new(13_602);
    let target_file = FileId::new(13_603);
    let import = first_node(&importer, importer_file, SyntaxKind::ImportDeclaration);
    let NodeData::ImportDeclaration(data) = &importer.arena.get(import.node).unwrap().data else {
        panic!("the control contains a namespace import")
    };
    let specifier = NodeRef::new(import.arena, import.file, data.module_specifier);
    let mut checker = context(
        &[
            TestSource {
                parsed: &importer,
                file: importer_file,
                path: "\"/namespace-importer.ts\"",
                declaration_file: false,
                module_state: CanonicalModuleState::External,
            },
            TestSource {
                parsed: &target,
                file: target_file,
                path: "\"/target.ts\"",
                declaration_file: false,
                module_state: CanonicalModuleState::External,
            },
        ],
        [CanonicalModuleResolutionEntry::resolved(
            specifier,
            CanonicalResolvedModuleInput::new(
                target_file,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )],
    );
    let binding = first_node(&importer, importer_file, SyntaxKind::NamespaceImport);
    let alias = checker
        .file(importer_file)
        .unwrap()
        .1
        .symbol(binding)
        .unwrap();
    let bound = checker.file(target_file).unwrap().1;
    let module = bound.symbol(bound.source_file()).unwrap();
    let query = first_node(&importer, importer_file, SyntaxKind::TypeQuery);
    let name = query_name(&importer, query);
    assert!(checker.store().alias_symbol_links(alias).is_none());
    let namespace = checker.get_type_from_type_node(query).unwrap();
    assert_eq!(
        checker.store().type_payload(namespace).unwrap().symbol(),
        Some(module)
    );
    assert_eq!(
        checker
            .store()
            .symbol_node_links(name)
            .unwrap()
            .resolved_symbol,
        Some(alias)
    );
    assert!(checker.store().value_symbol_links(alias).is_none());
    assert!(checker.store().value_symbol_links(module).is_none());
    assert_eq!(checker.get_type_from_type_node(query), Ok(namespace));
    checker.check_source_file(importer_file).unwrap();
    for symbol in [alias, module] {
        assert_eq!(
            checker
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            Some(namespace)
        );
    }
    let before = (
        checker.store().type_len(),
        checker.store().symbol_len(),
        checker.store().signature_len(),
        checker.store().mapper_len(),
    );
    checker.recheck_source_file(importer_file).unwrap();
    assert_eq!(checker.get_type_from_type_node(query), Ok(namespace));
    assert_eq!(
        (
            checker.store().type_len(),
            checker.store().symbol_len(),
            checker.store().signature_len(),
            checker.store().mapper_len(),
        ),
        before
    );
    assert!(checker.diagnostics().is_empty());
}
