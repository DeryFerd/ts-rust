use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const PRODUCER: FileId = FileId::new(14_001);
const CONSUMER: FileId = FileId::new(14_002);

fn node(source: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    source
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(source.arena.id(), file, node))
        })
        .unwrap()
}

fn context<'arena>(
    producer: &'arena ParseResult,
    consumer: &'arena ParseResult,
    usage: CanonicalModuleResolutionMode,
    target: CanonicalModuleResolutionMode,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    let files = [
        (PRODUCER, producer, "\"/producer\""),
        (CONSUMER, consumer, "\"/consumer\""),
    ];
    for (file, source, name) in files {
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(name),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for (file, source, _) in files {
        binder
            .bind_typescript_declaration_slice(&source.arena, file)
            .unwrap();
    }
    let import = node(consumer, CONSUMER, SyntaxKind::ImportDeclaration);
    let NodeData::ImportDeclaration(data) = &consumer.arena.get(import.node).unwrap().data else {
        unreachable!()
    };
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        [(PRODUCER, &producer.arena), (CONSUMER, &consumer.arena)]
            .into_iter()
            .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            NodeRef::new(import.arena, import.file, data.module_specifier),
            CanonicalResolvedModuleInput::new(PRODUCER, usage, target),
        )]),
    )
    .unwrap()
}

fn export(checker: &CanonicalCheckerContext<'_>, file: FileId, name: &str) -> SemanticSymbolId {
    let bound = checker.file(file).unwrap().1;
    let module = bound.symbol(bound.source_file()).unwrap();
    let exports = checker.store().symbol(module).unwrap().exports().unwrap();
    checker
        .store()
        .symbol_table(exports)
        .unwrap()
        .get_source(name)
        .unwrap()
}

fn value_type(checker: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn initializer(source: &ParseResult, name: &str) -> NodeRef {
    source
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &source.arena.get(variable.name)?.data else {
                return None;
            };
            (identifier.text == name)
                .then(|| NodeRef::new(source.arena.id(), CONSUMER, variable.initializer.unwrap()))
        })
        .unwrap()
}

fn assert_property(
    checker: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    name: &str,
    expected_symbol: SemanticSymbolId,
    expected_type: TypeId,
) {
    let access = initializer(source, name);
    let NodeData::PropertyAccessExpression(data) = &source.arena.get(access.node).unwrap().data
    else {
        unreachable!()
    };
    let name_node = NodeRef::new(access.arena, access.file, data.name);
    assert_eq!(checker.get_type_at_location(access), Ok(expected_type));
    assert_eq!(
        checker.get_symbol_at_location(access),
        Ok(Some(expected_symbol))
    );
    assert_eq!(
        checker.get_symbol_at_location(name_node),
        Ok(Some(expected_symbol))
    );
    assert_eq!(
        value_type(checker, export(checker, CONSUMER, name)),
        expected_type
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Query order and source replay must share one checker.
fn namespace_wrapper_properties_preserve_export_and_default_identities_in_each_mode() {
    use CanonicalModuleResolutionMode::{CommonJs, Esm};
    let producer = parse_source_file("export const value: number = 1;");
    for (usage, target) in [
        (Esm, CommonJs),
        (CommonJs, CommonJs),
        (Esm, Esm),
        (CommonJs, Esm),
    ] {
        let wrapped = usage == Esm && target == CommonJs;
        let properties = if wrapped {
            "export const nested = ns.default.value; export const bare = ns.default; export const direct = ns.value;"
        } else {
            "export const direct = ns.value;"
        };
        let consumer = parse_source_file(&format!(
            "import * as ns from './producer.cjs'; {properties} export type Copy = typeof ns;"
        ));
        for query_first in [false, true] {
            for target_first in [false, true] {
                let mut checker = context(&producer, &consumer, usage, target);
                let query = node(&consumer, CONSUMER, SyntaxKind::TypeQuery);
                let binding = node(&consumer, CONSUMER, SyntaxKind::NamespaceImport);
                let alias = checker.file(CONSUMER).unwrap().1.symbol(binding).unwrap();
                let bound = checker.file(PRODUCER).unwrap().1;
                let module = bound.symbol(bound.source_file()).unwrap();
                let exports = checker.store().symbol(module).unwrap().exports().unwrap();
                let entries = checker
                    .store()
                    .symbol_table(exports)
                    .unwrap()
                    .iter()
                    .map(|(name, symbol)| (name.to_owned(), symbol))
                    .collect::<Vec<_>>();
                if target_first {
                    checker.check_source_file(PRODUCER).unwrap();
                }
                let queried = query_first.then(|| checker.get_type_from_type_node(query).unwrap());
                if query_first {
                    assert!(checker.store().value_symbol_links(alias).is_none());
                }
                checker.check_source_file(CONSUMER).unwrap_or_else(|error| panic!(
                    "{usage:?}->{target:?}, query_first={query_first}, target_first={target_first}: {error:?}"
                ));
                let namespace = checker.get_type_from_type_node(query).unwrap();
                assert!(queried.is_none_or(|queried| queried == namespace));
                let bare = value_type(&checker, module);
                let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
                let value = export(&checker, PRODUCER, "value");
                assert_property(&mut checker, &consumer, "direct", value, number);
                let default = if wrapped {
                    assert_ne!(namespace, bare);
                    let access = initializer(&consumer, "bare");
                    let default = checker.get_symbol_at_location(access).unwrap().unwrap();
                    let record = checker.store().symbol(default).unwrap();
                    assert_eq!(record.flags(), SymbolFlags::ALIAS);
                    assert_eq!(record.parent(), Some(module));
                    assert!(record.declarations().is_none());
                    assert_eq!(
                        checker
                            .store()
                            .alias_symbol_links(default)
                            .unwrap()
                            .alias_target,
                        AliasTargetState::Resolved(module)
                    );
                    assert_property(&mut checker, &consumer, "bare", default, bare);
                    assert_property(&mut checker, &consumer, "nested", value, number);
                    Some(default)
                } else {
                    assert_eq!(namespace, bare);
                    None
                };
                assert_eq!(
                    checker
                        .store()
                        .symbol_table(exports)
                        .unwrap()
                        .iter()
                        .map(|(name, symbol)| (name.to_owned(), symbol))
                        .collect::<Vec<_>>(),
                    entries
                );
                assert!(
                    checker
                        .store()
                        .symbol_table(exports)
                        .unwrap()
                        .get_source("default")
                        .is_none()
                );
                let before = (
                    checker.store().type_len(),
                    checker.store().symbol_len(),
                    checker.store().signature_len(),
                    checker.store().mapper_len(),
                );
                checker.recheck_source_file(CONSUMER).unwrap();
                assert_eq!(checker.get_type_from_type_node(query), Ok(namespace));
                assert_property(&mut checker, &consumer, "direct", value, number);
                if let Some(default) = default {
                    assert_property(&mut checker, &consumer, "bare", default, bare);
                    assert_property(&mut checker, &consumer, "nested", value, number);
                }
                assert_eq!(
                    (
                        checker.store().type_len(),
                        checker.store().symbol_len(),
                        checker.store().signature_len(),
                        checker.store().mapper_len()
                    ),
                    before
                );
                assert!(checker.diagnostics().is_empty());
            }
        }
    }
}

#[test]
fn bare_namespace_properties_do_not_gain_a_synthetic_default() {
    use CanonicalModuleResolutionMode::{CommonJs, Esm};
    let producer = parse_source_file("export const value: number = 1;");
    let consumer = parse_source_file(
        "import * as ns from './producer.cjs'; export const missing = ns.default;",
    );
    for (usage, target) in [(CommonJs, CommonJs), (Esm, Esm), (CommonJs, Esm)] {
        let mut checker = context(&producer, &consumer, usage, target);
        checker.check_source_file(CONSUMER).unwrap();
        let error = checker.store().intrinsic_bootstrap().unwrap().error_type;
        assert_eq!(
            value_type(&checker, export(&checker, CONSUMER, "missing")),
            error
        );
        let diagnostics = checker.diagnostics().as_slice().to_vec();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].diagnostic.code(), 2339);
        let before = (checker.store().type_len(), checker.store().symbol_len());
        checker.recheck_source_file(CONSUMER).unwrap();
        assert_eq!(checker.diagnostics().as_slice(), diagnostics.as_slice());
        assert_eq!(
            (checker.store().type_len(), checker.store().symbol_len()),
            before
        );
    }
}
