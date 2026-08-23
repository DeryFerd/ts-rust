use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalAliasQueryError, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput,
    alias::{CanonicalAliasResolutionError, CanonicalAliasTargetUnavailable},
};
use ts_parser::{ParseResult, parse_source_file};

#[derive(Clone, Copy)]
struct Source<'arena> {
    parsed: &'arena ParseResult,
    file: FileId,
    path: &'static str,
}

#[derive(Clone, Copy)]
struct Route {
    source: usize,
    specifier: usize,
    target: usize,
    usage_mode: CanonicalModuleResolutionMode,
    target_mode: CanonicalModuleResolutionMode,
}

fn common_js(source: usize, target: usize) -> Route {
    Route {
        source,
        specifier: 0,
        target,
        usage_mode: CanonicalModuleResolutionMode::CommonJs,
        target_mode: CanonicalModuleResolutionMode::CommonJs,
    }
}

fn module_specifiers(source: Source<'_>) -> Vec<NodeRef> {
    let mut specifiers = source
        .parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let specifier = match &record.data {
                NodeData::ImportDeclaration(import) => Some(import.module_specifier),
                NodeData::ExportDeclaration(export) => export.module_specifier,
                NodeData::ImportEqualsDeclaration(import) => match source
                    .parsed
                    .arena
                    .get(import.module_reference)
                    .map(|node| &node.data)
                {
                    Some(NodeData::ExternalModuleReference(reference)) => {
                        Some(reference.expression)
                    }
                    _ => None,
                },
                _ => None,
            }?;
            Some((
                record.range.start,
                NodeRef::new(source.parsed.arena.id(), source.file, specifier),
            ))
        })
        .collect::<Vec<_>>();
    specifiers.sort_by_key(|(start, _)| *start);
    specifiers
        .into_iter()
        .map(|(_, specifier)| specifier)
        .collect()
}

fn context<'arena>(
    sources: &[Source<'arena>],
    routes: &[Route],
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
                    false,
                    CanonicalModuleState::External,
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
        CanonicalCheckerOptions {
            emit_common_js: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(routes.iter().map(|route| {
            let source = sources[route.source];
            let specifier = module_specifiers(source)[route.specifier];
            CanonicalModuleResolutionEntry::resolved(
                specifier,
                CanonicalResolvedModuleInput::new(
                    sources[route.target].file,
                    route.usage_mode,
                    route.target_mode,
                ),
            )
        })),
    )
    .unwrap()
}

fn alias_symbol(
    context: &CanonicalCheckerContext<'_>,
    source: Source<'_>,
    name: &str,
) -> SemanticSymbolId {
    let declaration = source
        .parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name_node = match &record.data {
                NodeData::ImportClause(clause) => clause.name,
                NodeData::ImportSpecifier(specifier) => Some(specifier.name),
                NodeData::ImportEqualsDeclaration(import) => Some(import.name),
                NodeData::NamespaceImport(namespace) => Some(namespace.name),
                NodeData::ExportSpecifier(specifier) => Some(specifier.name),
                _ => None,
            }?;
            let NodeData::Identifier(identifier) = &source.parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(
                source.parsed.arena.id(),
                source.file,
                node,
            ))
        })
        .unwrap_or_else(|| panic!("fixture contains alias {name}"));
    context
        .file(source.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap()
}

fn local_symbol(
    context: &CanonicalCheckerContext<'_>,
    source: Source<'_>,
    name: &str,
) -> SemanticSymbolId {
    let bound = context.file(source.file).unwrap().1;
    let locals = bound.locals(bound.source_file()).unwrap();
    context
        .store()
        .symbol_table(locals)
        .unwrap()
        .get_source(name)
        .unwrap()
}

#[test]
fn commonjs_mode_preserves_named_value_imports_and_reexports() {
    let consumer = parse_source_file(concat!(
        "import { publicValue as value } from './barrel'; ",
        "const good: number = value; ",
        "const bad: string = value;",
    ));
    let barrel = parse_source_file("export { original as publicValue } from './base';");
    let base = parse_source_file("export const original: number = 1;");
    let files = [
        Source {
            parsed: &consumer,
            file: FileId::new(0),
            path: "\"/project/consumer.ts\"",
        },
        Source {
            parsed: &barrel,
            file: FileId::new(1),
            path: "\"/project/barrel.ts\"",
        },
        Source {
            parsed: &base,
            file: FileId::new(2),
            path: "\"/project/base.ts\"",
        },
    ];
    let mut checker = context(&files, &[common_js(0, 1), common_js(1, 2)]);

    checker.check_source_file(files[0].file).unwrap();
    assert_eq!(
        checker
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2322]
    );
    for source in files {
        checker.check_source_file(source.file).unwrap();
    }
    assert_eq!(checker.diagnostics().as_slice().len(), 1);
}

#[test]
fn commonjs_mode_preserves_named_type_imports() {
    let importer = parse_source_file(concat!(
        "import type { Model as LocalModel } from './target'; ",
        "const good: LocalModel = 1; ",
        "const bad: LocalModel = 'wrong';",
    ));
    let target = parse_source_file("export type Model = number;");
    let files = [
        Source {
            parsed: &importer,
            file: FileId::new(10),
            path: "\"/project/type-importer.ts\"",
        },
        Source {
            parsed: &target,
            file: FileId::new(11),
            path: "\"/project/type-target.ts\"",
        },
    ];
    let mut checker = context(&files, &[common_js(0, 1)]);

    checker.check_source_file(files[0].file).unwrap();
    assert_eq!(
        checker
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2322]
    );
}

#[test]
fn external_import_equals_follows_the_export_equals_alias() {
    let importer = parse_source_file("import imported = require('./target');");
    let target = parse_source_file("const value: number = 1; export = value;");
    let files = [
        Source {
            parsed: &importer,
            file: FileId::new(20),
            path: "\"/project/equals-importer.ts\"",
        },
        Source {
            parsed: &target,
            file: FileId::new(21),
            path: "\"/project/equals-target.ts\"",
        },
    ];
    let mut checker = context(&files, &[common_js(0, 1)]);
    let require_alias = alias_symbol(&checker, files[0], "imported");
    let value = local_symbol(&checker, files[1], "value");
    let bound = checker.file(files[1].file).unwrap().1;
    let module = bound.symbol(bound.source_file()).unwrap();
    let exports = checker.store().symbol(module).unwrap().exports().unwrap();
    let export_equals = checker
        .store()
        .symbol_table(exports)
        .unwrap()
        .get(InternalSymbolName::ExportEquals.as_ref())
        .unwrap();

    let resolution = checker.resolve_alias(require_alias).unwrap();
    assert_eq!(resolution.target, AliasTargetState::Resolved(value));
    assert!(resolution.events.is_empty());
    assert_eq!(
        checker
            .store()
            .alias_symbol_links(export_equals)
            .unwrap()
            .alias_target,
        AliasTargetState::Resolved(value)
    );
    assert_eq!(
        checker.resolve_alias(require_alias).unwrap().target,
        AliasTargetState::Resolved(value)
    );
}

#[test]
fn default_import_follows_a_local_default_export_alias() {
    let importer = parse_source_file("import selected from './target';");
    let target = parse_source_file("const value: number = 1; export { value as default };");
    let files = [
        Source {
            parsed: &importer,
            file: FileId::new(30),
            path: "\"/project/default-importer.ts\"",
        },
        Source {
            parsed: &target,
            file: FileId::new(31),
            path: "\"/project/default-target.ts\"",
        },
    ];
    let mut checker = context(&files, &[common_js(0, 1)]);
    let default_alias = alias_symbol(&checker, files[0], "selected");
    let value = local_symbol(&checker, files[1], "value");

    assert_eq!(
        checker.resolve_alias(default_alias).unwrap().target,
        AliasTargetState::Resolved(value)
    );
}

#[test]
fn mixed_module_modes_remain_an_explicit_boundary() {
    let importer = parse_source_file("import { value } from './target';");
    let target = parse_source_file("export const value: number = 1;");
    let files = [
        Source {
            parsed: &importer,
            file: FileId::new(40),
            path: "\"/project/mixed-importer.ts\"",
        },
        Source {
            parsed: &target,
            file: FileId::new(41),
            path: "\"/project/mixed-target.ts\"",
        },
    ];
    let mut checker = context(
        &files,
        &[Route {
            source: 0,
            specifier: 0,
            target: 1,
            usage_mode: CanonicalModuleResolutionMode::CommonJs,
            target_mode: CanonicalModuleResolutionMode::Esm,
        }],
    );
    let value_alias = alias_symbol(&checker, files[0], "value");

    assert!(matches!(
        checker.resolve_alias(value_alias),
        Err(CanonicalAliasQueryError::AliasResolution(
            CanonicalAliasResolutionError::TargetUnavailable {
                reason: CanonicalAliasTargetUnavailable::CommonJsModuleUnsupported {
                    file,
                    ..
                },
                ..
            }
        )) if file == files[1].file
    ));
    assert_eq!(
        checker
            .store()
            .alias_symbol_links(value_alias)
            .unwrap()
            .alias_target,
        AliasTargetState::Unresolved
    );
}

#[test]
fn chained_import_equals_resolves_nested_exported_namespace_functions() {
    let importer = parse_source_file(concat!(
        "import namespaceValue = require('./target');\n",
        "import alias = namespaceValue;\n",
        "alias.members.execute();\n",
    ));
    let target = parse_source_file("export namespace members { export function execute() {} }");
    let files = [
        Source {
            parsed: &importer,
            file: FileId::new(50),
            path: "\"/project/nested-namespace-importer.ts\"",
        },
        Source {
            parsed: &target,
            file: FileId::new(51),
            path: "\"/project/nested-namespace-target.ts\"",
        },
    ];
    let mut checker = context(&files, &[common_js(0, 1)]);

    checker.check_source_file(files[0].file).unwrap();
    assert!(checker.diagnostics().is_empty());

    let first = alias_symbol(&checker, files[0], "namespaceValue");
    let second = alias_symbol(&checker, files[0], "alias");
    assert!(matches!(
        checker.resolve_alias(first).unwrap().target,
        AliasTargetState::Resolved(_)
    ));
    assert_eq!(
        checker.resolve_alias(first).unwrap().target,
        checker.resolve_alias(second).unwrap().target,
    );

    checker.check_source_file(files[1].file).unwrap();
    assert!(checker.diagnostics().is_empty());

    let warm = (
        checker.store().type_len(),
        checker.store().signature_len(),
        checker.diagnostics().clone(),
    );
    checker.recheck_source_file(files[0].file).unwrap();
    assert_eq!(
        (
            checker.store().type_len(),
            checker.store().signature_len(),
            checker.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn default_exported_interfaces_remain_valid_imported_return_types() {
    let consumer = parse_source_file(concat!(
        "import { styled } from './factory';\n",
        "export const value = styled();\n",
    ));
    let factory = parse_source_file(concat!(
        "import Color from './color';\n",
        "export declare function styled(): Color;\n",
    ));
    let color = parse_source_file(concat!(
        "interface Color { c: string; }\n",
        "export default Color;\n",
    ));
    let files = [
        Source {
            parsed: &consumer,
            file: FileId::new(60),
            path: "\"/project/default-interface-consumer.ts\"",
        },
        Source {
            parsed: &factory,
            file: FileId::new(61),
            path: "\"/project/default-interface-factory.ts\"",
        },
        Source {
            parsed: &color,
            file: FileId::new(62),
            path: "\"/project/default-interface-color.ts\"",
        },
    ];
    let mut checker = context(&files, &[common_js(0, 1), common_js(1, 2)]);

    checker.check_source_file(files[0].file).unwrap();
    checker.check_source_file(files[1].file).unwrap();
    checker.check_source_file(files[2].file).unwrap();
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );

    let imported = alias_symbol(&checker, files[1], "Color");
    assert!(matches!(
        checker.resolve_alias(imported).unwrap().target,
        AliasTargetState::Resolved(_)
    ));

    let warm = (
        checker.store().type_len(),
        checker.store().signature_len(),
        checker.diagnostics().clone(),
    );
    checker.recheck_source_file(files[0].file).unwrap();
    checker.recheck_source_file(files[1].file).unwrap();
    checker.recheck_source_file(files[2].file).unwrap();
    assert_eq!(
        (
            checker.store().type_len(),
            checker.store().signature_len(),
            checker.diagnostics().clone(),
        ),
        warm,
    );
}
