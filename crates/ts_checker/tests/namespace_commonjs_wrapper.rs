use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

fn node(source: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    source
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(source.arena.id(), file, node))
        })
        .unwrap()
}

fn exported_type(checker: &CanonicalCheckerContext<'_>, file: FileId, name: &str) -> TypeId {
    let bound = checker.file(file).unwrap().1;
    let module = bound.symbol(bound.source_file()).unwrap();
    let exports = checker.store().symbol(module).unwrap().exports().unwrap();
    let symbol = checker
        .store()
        .symbol_table(exports)
        .unwrap()
        .get_source(name)
        .unwrap();
    checker
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn property(
    checker: &CanonicalCheckerContext<'_>,
    owner: TypeId,
    name: &str,
) -> Option<SemanticSymbolId> {
    let TypeData::Object(object) = checker.store().type_payload(owner)?.data() else {
        return None;
    };
    let members = object.structured.members?;
    checker.store().symbol_table(members)?.get_source(name)
}

#[test]
#[allow(clippy::too_many_lines)] // Both views and both publication orders use one retained checker.
fn source_namespace_wrappers_keep_the_bare_default_and_each_import_identity() {
    let target = parse_source_file("export const value: number = 1;");
    let bare_source = parse_source_file(
        "import * as ns from './producer.cjs'; export type Copy = typeof ns; export const copied = ns;",
    );
    let first_source = parse_source_file(
        "import * as ns from './producer.cjs'; export type Copy = typeof ns; export const copied = ns;",
    );
    let second_source = parse_source_file(
        "import * as second from './producer.cjs'; export type Copy = typeof second; export const copied = second;",
    );
    let target_file = FileId::new(13_830);
    let files = [
        FileId::new(13_831),
        FileId::new(13_832),
        FileId::new(13_833),
    ];
    let imports = [&bare_source, &first_source, &second_source];
    for query_first in [true, false] {
        let mut binder = CanonicalBinder::new();
        let sources = [
            (target_file, &target, "\"/producer.cts\""),
            (files[0], &bare_source, "\"/consumer.cts\""),
            (files[1], &first_source, "\"/consumer.mts\""),
            (files[2], &second_source, "\"/second.mts\""),
        ];
        for (file, source, path) in sources {
            assert!(source.diagnostics.is_empty());
            binder
                .bind_source_file_with_facts(
                    &source.arena,
                    source.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
        }
        for (file, source, _) in sources {
            binder
                .bind_typescript_declaration_slice(&source.arena, file)
                .unwrap();
        }
        let entries = imports
            .iter()
            .zip(files)
            .enumerate()
            .map(|(index, (source, file))| {
                let import = node(source, file, SyntaxKind::ImportDeclaration);
                let NodeData::ImportDeclaration(data) =
                    &source.arena.get(import.node).unwrap().data
                else {
                    unreachable!()
                };
                CanonicalModuleResolutionEntry::resolved(
                    NodeRef::new(import.arena, import.file, data.module_specifier),
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        if index == 0 {
                            CanonicalModuleResolutionMode::CommonJs
                        } else {
                            CanonicalModuleResolutionMode::Esm
                        },
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                )
            });
        let mut checker = CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            [
                (target_file, &target.arena),
                (files[0], &bare_source.arena),
                (files[1], &first_source.arena),
                (files[2], &second_source.arena),
            ]
            .into_iter()
            .collect(),
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new(entries),
        )
        .unwrap();
        let bound = checker.file(target_file).unwrap().1;
        let module = bound.symbol(bound.source_file()).unwrap();
        let queries = imports
            .iter()
            .zip(files)
            .map(|(source, file)| node(source, file, SyntaxKind::TypeQuery))
            .collect::<Vec<_>>();
        let aliases = imports
            .iter()
            .zip(files)
            .map(|(source, file)| {
                checker
                    .file(file)
                    .unwrap()
                    .1
                    .symbol(node(source, file, SyntaxKind::NamespaceImport))
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let mut cold = Vec::new();
        if query_first {
            for &query in &queries {
                cold.push(checker.get_type_from_type_node(query).unwrap());
            }
            for &alias in &aliases {
                assert!(checker.store().value_symbol_links(alias).is_none());
            }
            assert!(checker.store().value_symbol_links(module).is_none());
        }
        for index in [1, 0, 2] {
            checker.check_source_file(files[index]).unwrap();
        }
        let views = queries
            .iter()
            .map(|query| checker.get_type_from_type_node(*query).unwrap())
            .collect::<Vec<_>>();
        if query_first {
            assert_eq!(views, cold);
        }
        assert_ne!(views[0], views[1]);
        assert_ne!(views[0], views[2]);
        assert_ne!(views[1], views[2]);
        assert_eq!(
            checker.store().type_payload(views[0]).unwrap().symbol(),
            Some(module)
        );
        assert!(property(&checker, views[0], "default").is_none());
        let mut defaults = Vec::new();
        for (index, (&alias, &view)) in aliases.iter().zip(&views).enumerate() {
            assert_eq!(exported_type(&checker, files[index], "copied"), view);
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(alias)
                    .unwrap()
                    .resolved_type,
                Some(view)
            );
            let namespace = checker
                .store()
                .type_payload(view)
                .unwrap()
                .symbol()
                .unwrap();
            assert_eq!(
                checker
                    .store()
                    .alias_symbol_links(alias)
                    .unwrap()
                    .alias_target,
                AliasTargetState::Resolved(namespace)
            );
            let value = property(&checker, view, "value").unwrap();
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(value)
                    .unwrap()
                    .resolved_type,
                Some(checker.store().intrinsic_bootstrap().unwrap().number_type)
            );
            if index == 0 {
                continue;
            }
            let origin = node(imports[index], files[index], SyntaxKind::ImportDeclaration);
            let links = checker.store().export_type_links(namespace).unwrap();
            assert_eq!(links.target, Some(module));
            assert_eq!(links.originating_import, Some(origin));
            let default = property(&checker, view, "default").unwrap();
            let links = checker.store().value_symbol_links(default).unwrap();
            assert_eq!(links.resolved_type, Some(views[0]));
            let default_alias = links.target.unwrap();
            defaults.push(default_alias);
            let record = checker.store().symbol(default_alias).unwrap();
            assert_eq!(record.flags(), SymbolFlags::ALIAS);
            assert_eq!(record.parent(), Some(module));
            assert!(record.declarations().is_none());
            assert_eq!(
                checker
                    .store()
                    .alias_symbol_links(default_alias)
                    .unwrap()
                    .alias_target,
                AliasTargetState::Resolved(module)
            );
            let exports = checker
                .store()
                .symbol(namespace)
                .unwrap()
                .exports()
                .unwrap();
            assert!(
                checker
                    .store()
                    .symbol_table(exports)
                    .unwrap()
                    .get_source("default")
                    .is_none()
            );
        }
        assert_eq!(defaults.len(), 2);
        assert_eq!(defaults[0], defaults[1]);
        assert_eq!(
            checker
                .store()
                .value_symbol_links(module)
                .unwrap()
                .resolved_type,
            Some(views[0])
        );
        let before = (
            checker.store().type_len(),
            checker.store().symbol_len(),
            checker.store().signature_len(),
            checker.store().mapper_len(),
        );
        for index in [2, 0, 1] {
            checker.recheck_source_file(files[index]).unwrap();
            assert_eq!(
                checker.get_type_from_type_node(queries[index]),
                Ok(views[index])
            );
            let copy = checker
                .file(files[index])
                .unwrap()
                .1
                .symbol(node(
                    imports[index],
                    files[index],
                    SyntaxKind::TypeAliasDeclaration,
                ))
                .unwrap();
            assert_eq!(checker.get_declared_type_of_symbol(copy), Ok(views[index]));
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
