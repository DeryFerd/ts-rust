use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, InternalSymbolName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeNodeLinks,
    ValueSymbolLinks,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(203_100);
const FILES: [FileId; 5] = [
    FileId::new(203_101),
    FileId::new(203_102),
    FileId::new(203_103),
    FileId::new(203_104),
    FileId::new(203_105),
];
const PATHS: [&str; 5] = [
    "/node_modules/foo/index.d.ts",
    "/a.d.ts",
    "/b.d.ts",
    "/augment.ts",
    "/index.ts",
];
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

// Original virtual files from globalArrayAugmentationWithAmbientModuleReexportMerge1.ts.
const SOURCES: [&str; 5] = [
    concat!(
        "declare function foo(): void;\r\n",
        "declare namespace foo { export const items: string[]; }\r\n",
        "export = foo;\r\n\r\n",
    ),
    "declare module 'mymod' { import * as foo from 'foo'; export { foo }; }\r\n\r\n",
    "declare module 'mymod' { export const foo: number; }\r\n\r\n",
    concat!(
        "declare global {\r\n",
        "    interface Array<T> {\r\n",
        "        customMethod(): T;\r\n",
        "    }\r\n",
        "}\r\n",
        "export {};\r\n\r\n",
    ),
    concat!(
        "import * as foo from 'foo';\r\n",
        "const items = foo.items;\r\n",
        "const result: string = items.customMethod();\r\n\r\n",
        "const fresh: string[] = [];\r\n",
        "const result2: string = fresh.customMethod();\r\n",
    ),
];

fn reference(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap()
}

fn raw_symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    checker.file(node.file).unwrap().1.symbol(node).unwrap()
}

fn context<'a>(
    library: &'a ParseResult,
    parsed: &'a [ParseResult; 5],
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    let files = std::iter::once((
        LIBRARY,
        library,
        "/lib.es5.d.ts",
        true,
        true,
        CanonicalModuleState::Script,
    ))
    .chain(parsed.iter().enumerate().map(|(index, source)| {
        (
            FILES[index],
            source,
            PATHS[index],
            index < 3,
            false,
            if index == 1 || index == 2 {
                CanonicalModuleState::Script
            } else {
                CanonicalModuleState::External
            },
        )
    }))
    .collect::<Vec<_>>();
    for &(file, source, path, declaration, default_library, module) in &files {
        assert!(
            source.diagnostics.is_empty(),
            "{path}: {:?}",
            source.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(format!("\"{path}\"")),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    default_library,
                    module,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&source.arena, file)
            .unwrap();
    }
    let entries = [1, 4].map(|index| {
        let import = reference(&parsed[index], FILES[index], SyntaxKind::ImportDeclaration);
        let NodeData::ImportDeclaration(import_data) =
            &parsed[index].arena.get(import.node).unwrap().data
        else {
            unreachable!()
        };
        let specifier = NodeRef::new(import.arena, import.file, import_data.module_specifier);
        let NodeData::StringLiteral(text) = &parsed[index].arena.get(specifier.node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(text.text, "foo");
        CanonicalModuleResolutionEntry::resolved(
            specifier,
            CanonicalResolvedModuleInput::new(
                FILES[0],
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )
    });
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|(file, source, ..)| (*file, &source.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_emit: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(entries),
    )
    .unwrap()
}

fn collision_names(parsed: &[ParseResult; 5]) -> [NodeRef; 2] {
    let export = reference(&parsed[1], FILES[1], SyntaxKind::ExportSpecifier);
    let NodeData::ExportSpecifier(export_data) = &parsed[1].arena.get(export.node).unwrap().data
    else {
        unreachable!()
    };
    let variable = reference(&parsed[2], FILES[2], SyntaxKind::VariableDeclaration);
    let NodeData::VariableDeclaration(variable_data) =
        &parsed[2].arena.get(variable.node).unwrap().data
    else {
        unreachable!()
    };
    [
        NodeRef::new(export.arena, export.file, export_data.name),
        NodeRef::new(variable.arena, variable.file, variable_data.name),
    ]
}

fn assert_diagnostics(checker: &CanonicalCheckerContext<'_>, names: [NodeRef; 2]) {
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{:?}", checker.diagnostics());
    for (diagnostic, (name, other)) in diagnostics
        .iter()
        .zip([(names[0], names[1]), (names[1], names[0])])
    {
        assert_eq!(diagnostic.node, Some(name));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), 2451);
        assert_eq!(diagnostic.diagnostic.arguments, ["foo"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Cannot redeclare block-scoped variable 'foo'."
        );
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("each conflict must retain its opposite declaration")
        };
        assert_eq!(related.node, Some(other));
        assert_eq!(related.diagnostic.code(), 6203);
        assert_eq!(related.diagnostic.arguments, ["foo"]);
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "'foo' was also declared here."
        );
    }
}

fn assert_module(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &[ParseResult; 5],
    declarations: [NodeRef; 2],
    raw: [SemanticSymbolId; 2],
) -> SemanticSymbolId {
    let owner = checker.store().get_merged_symbol(raw[0]).unwrap();
    assert_eq!(checker.store().get_merged_symbol(raw[1]), Some(owner));
    assert_eq!(
        checker.get_symbol_declarations(owner).unwrap(),
        declarations
    );
    let conflicting = raw_symbol(
        checker,
        reference(&parsed[2], FILES[2], SyntaxKind::VariableDeclaration),
    );
    let exports = checker.store().symbol(owner).unwrap().exports().unwrap();
    assert_eq!(
        checker
            .store()
            .symbol_table(exports)
            .unwrap()
            .get_source("foo"),
        Some(conflicting),
    );
    assert_eq!(
        checker.store().symbol(owner).unwrap().name().as_utf8(),
        Some("\"mymod\"")
    );
    assert_eq!(checker.symbol_to_string(owner).unwrap(), "\"mymod\"");
    for (index, declaration) in declarations.into_iter().enumerate() {
        let NodeData::ModuleDeclaration(module) =
            &parsed[index + 1].arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let name = NodeRef::new(declaration.arena, declaration.file, module.name);
        assert_eq!(checker.get_symbol_at_location(name).unwrap(), Some(owner));
        assert_eq!(
            checker.get_symbol_at_location(declaration).unwrap(),
            Some(owner)
        );
        assert_eq!(
            checker
                .symbol_to_string_at_location(owner, declaration)
                .unwrap(),
            "\"mymod\""
        );
    }
    owner
}

fn assert_aliases(checker: &CanonicalCheckerContext<'_>, parsed: &[ParseResult; 5]) {
    let function = reference(&parsed[0], FILES[0], SyntaxKind::FunctionDeclaration);
    let original = checker
        .store()
        .get_merged_symbol(raw_symbol(checker, function))
        .unwrap();
    let module = raw_symbol(
        checker,
        NodeRef::new(parsed[0].arena.id(), FILES[0], parsed[0].source_file),
    );
    let exports = checker.store().symbol(module).unwrap().exports().unwrap();
    let assignment = checker
        .store()
        .symbol_table(exports)
        .unwrap()
        .get(InternalSymbolName::ExportEquals.as_ref())
        .unwrap();
    let imported = raw_symbol(
        checker,
        reference(&parsed[1], FILES[1], SyntaxKind::NamespaceImport),
    );
    let reexported = raw_symbol(
        checker,
        reference(&parsed[1], FILES[1], SyntaxKind::ExportSpecifier),
    );
    let conflicting = raw_symbol(
        checker,
        reference(&parsed[2], FILES[2], SyntaxKind::VariableDeclaration),
    );
    assert_ne!(imported, reexported);
    assert_ne!(reexported, conflicting);
    assert_ne!(
        checker.store().get_merged_symbol(reexported),
        checker.store().get_merged_symbol(conflicting)
    );
    assert_eq!(
        checker
            .store()
            .alias_symbol_links(imported)
            .map(|links| (links.immediate_target, links.alias_target)),
        Some((Some(assignment), AliasTargetState::Resolved(original)))
    );
    assert_eq!(
        checker
            .store()
            .alias_symbol_links(reexported)
            .map(|links| (links.immediate_target, links.alias_target)),
        Some((Some(imported), AliasTargetState::Resolved(original)))
    );
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 6],
    nodes: Vec<(
        Option<TypeNodeLinks>,
        Option<SymbolNodeLinks>,
        Option<SignatureLinks>,
    )>,
    symbols: Vec<(
        Option<AliasSymbolLinks>,
        Option<ValueSymbolLinks>,
        Option<SemanticSymbolId>,
    )>,
    sources: Vec<Option<SourceFileLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(checker: &CanonicalCheckerContext<'_>, parsed: &[ParseResult; 5]) -> Snapshot {
    let store = checker.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.merged_symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: parsed
            .iter()
            .enumerate()
            .flat_map(|(index, source)| {
                source.arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(source.arena.id(), FILES[index], node);
                    (
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    store.alias_symbol_links(symbol).cloned(),
                    store.value_symbol_links(symbol).cloned(),
                    store.get_merged_symbol(symbol),
                )
            })
            .collect(),
        sources: FILES
            .iter()
            .map(|&file| {
                store
                    .source_file_links(checker.source_file(file).unwrap())
                    .cloned()
            })
            .collect(),
        diagnostics: checker.diagnostics().clone(),
    }
}

#[test]
fn ambient_module_symbols_keep_both_conflicting_declarations_and_canonical_names() {
    let library = parse_source_file(ES5);
    let parsed = SOURCES.map(parse_source_file);
    let declarations = [
        reference(&parsed[1], FILES[1], SyntaxKind::ModuleDeclaration),
        reference(&parsed[2], FILES[2], SyntaxKind::ModuleDeclaration),
    ];
    let names = collision_names(&parsed);
    for (index, offset) in [(1, 62), (2, 38)] {
        let range = parsed[index]
            .arena
            .get(names[index - 1].node)
            .unwrap()
            .range;
        assert_eq!(range.start.get(), offset);
        assert_eq!(range.end.get() - range.start.get(), 3);
    }
    for order in [[0, 1, 2, 3, 4], [0, 2, 1, 3, 4]] {
        let mut checker = context(&library, &parsed);
        let raw = declarations.map(|declaration| raw_symbol(&checker, declaration));
        assert_ne!(raw[0], raw[1]);
        assert_eq!(
            checker.options().name_resolution.emit_target,
            ScriptTarget::Es2015
        );
        assert!(checker.options().no_emit);
        assert_diagnostics(&checker, names);
        assert_aliases(&checker, &parsed);
        let before_display = snapshot(&checker, &parsed);
        let owner = assert_module(&mut checker, &parsed, declarations, raw);
        assert_eq!(snapshot(&checker, &parsed), before_display);
        for index in order {
            checker.check_source_file(FILES[index]).unwrap();
        }
        assert_diagnostics(&checker, names);
        assert_aliases(&checker, &parsed);
        let conflicting = raw_symbol(
            &checker,
            reference(&parsed[2], FILES[2], SyntaxKind::VariableDeclaration),
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(conflicting)
                .unwrap()
                .resolved_type,
            Some(checker.store().intrinsic_bootstrap().unwrap().number_type)
        );
        let warm = snapshot(&checker, &parsed);
        for _ in 0..2 {
            assert_eq!(
                assert_module(&mut checker, &parsed, declarations, raw),
                owner
            );
            assert_eq!(snapshot(&checker, &parsed), warm);
            for index in order {
                checker.recheck_source_file(FILES[index]).unwrap();
            }
            assert_diagnostics(&checker, names);
            assert_aliases(&checker, &parsed);
            assert_eq!(
                assert_module(&mut checker, &parsed, declarations, raw),
                owner
            );
            assert_eq!(snapshot(&checker, &parsed), warm);
        }
    }
}
