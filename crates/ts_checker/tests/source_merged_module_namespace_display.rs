use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput,
};
use ts_parser::{ParseResult, parse_source_file};

const FILES: [FileId; 3] = [
    FileId::new(203_300),
    FileId::new(203_301),
    FileId::new(203_302),
];
const PATHS: [&str; 3] = ["/a.d.ts", "/b.d.ts", "/consumer.ts"];
const SOURCES: [&str; 3] = [
    "declare module 'shared' { export const first: number; }\n",
    "declare module 'shared' { export const second: string; }\n",
    "import * as ns from 'shared';\n",
];

fn node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap()
}

fn context(parsed: &[ParseResult; 3]) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    for (index, source) in parsed.iter().enumerate() {
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                FILES[index],
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"{}\"", PATHS[index])),
                    CanonicalSourceLanguage::TypeScript,
                    index < 2,
                    if index < 2 {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&source.arena, FILES[index])
            .unwrap();
    }
    let import = node(&parsed[2], FILES[2], SyntaxKind::ImportDeclaration);
    let NodeData::ImportDeclaration(data) = &parsed[2].arena.get(import.node).unwrap().data else {
        unreachable!()
    };
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        parsed
            .iter()
            .enumerate()
            .map(|(index, source)| (FILES[index], &source.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            NodeRef::new(import.arena, import.file, data.module_specifier),
            CanonicalResolvedModuleInput::new(
                FILES[0],
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

fn raw_symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap()
}

struct Owners {
    declarations: [NodeRef; 2],
    raw: [SemanticSymbolId; 2],
    module: SemanticSymbolId,
    alias: SemanticSymbolId,
    exports: [SemanticSymbolId; 2],
}

fn owners(checker: &CanonicalCheckerContext<'_>, parsed: &[ParseResult; 3]) -> Owners {
    let declarations =
        [0, 1].map(|index| node(&parsed[index], FILES[index], SyntaxKind::ModuleDeclaration));
    let raw = declarations.map(|declaration| raw_symbol(checker, declaration));
    let module = checker.store().get_merged_symbol(raw[0]).unwrap();
    assert_ne!(raw[0], raw[1]);
    for symbol in raw {
        assert_ne!(symbol, module);
        assert_eq!(checker.store().get_merged_symbol(symbol), Some(module));
    }
    let record = checker.store().symbol(module).unwrap();
    assert_eq!(
        record.flags(),
        SymbolFlags::VALUE_MODULE | SymbolFlags::TRANSIENT
    );
    assert_eq!(record.declarations(), Some(declarations.as_slice()));
    let binding = node(&parsed[2], FILES[2], SyntaxKind::NamespaceImport);
    let alias = raw_symbol(checker, binding);
    assert_ne!(alias, module);
    assert_eq!(
        checker.store().symbol(alias).unwrap().flags(),
        SymbolFlags::ALIAS
    );
    assert_eq!(
        checker.store().symbol(alias).unwrap().declarations(),
        Some([binding].as_slice())
    );
    let exports = [0, 1].map(|index| {
        let declaration = node(
            &parsed[index],
            FILES[index],
            SyntaxKind::VariableDeclaration,
        );
        checker
            .store()
            .get_merged_symbol(raw_symbol(checker, declaration))
            .unwrap()
    });
    let table = checker
        .store()
        .symbol_table(record.exports().unwrap())
        .unwrap();
    assert_eq!(table.len(), 2);
    for (name, symbol) in ["first", "second"].into_iter().zip(exports) {
        assert_eq!(table.get_source(name), Some(symbol));
        assert_eq!(checker.store().get_parent_of_symbol(symbol), Some(module));
    }
    Owners {
        declarations,
        raw,
        module,
        alias,
        exports,
    }
}

fn assert_value_cold(checker: &CanonicalCheckerContext<'_>, owners: &Owners) {
    for symbol in owners.raw.into_iter().chain([owners.module, owners.alias]) {
        assert!(checker.store().export_type_links(symbol).is_none());
        assert!(checker.store().value_symbol_links(symbol).is_none());
        assert!(checker.store().declared_type_links(symbol).is_none());
    }
    assert!(checker.diagnostics().is_empty());
}

fn assert_display(checker: &mut CanonicalCheckerContext<'_>, owners: &Owners) {
    assert_eq!(
        checker.get_symbol_declarations(owners.module).unwrap(),
        owners.declarations
    );
    for declaration in owners.declarations {
        assert_eq!(
            checker.get_symbol_at_location(declaration).unwrap(),
            Some(owners.module)
        );
        assert_eq!(
            checker
                .symbol_to_string_at_location(owners.module, declaration)
                .unwrap(),
            "\"shared\""
        );
    }
    assert_value_cold(checker, owners);
}

fn assert_alias(checker: &mut CanonicalCheckerContext<'_>, owners: &Owners) {
    let resolved = checker.resolve_alias(owners.alias).unwrap();
    assert_eq!(resolved.target, AliasTargetState::Resolved(owners.module));
    assert!(resolved.events.is_empty());
    assert_eq!(
        checker.store().alias_symbol_links(owners.alias),
        Some(&AliasSymbolLinks {
            immediate_target: Some(owners.module),
            alias_target: AliasTargetState::Resolved(owners.module),
            ..AliasSymbolLinks::default()
        })
    );
    assert_value_cold(checker, owners);
}

fn snapshot(checker: &CanonicalCheckerContext<'_>) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.merged_symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        checker.global_types().clone(),
        store.relation_state_snapshot(),
        checker.diagnostics().clone(),
        checker
            .file_order()
            .iter()
            .map(|&file| {
                store
                    .source_file_links(checker.source_file(file).unwrap())
                    .cloned()
            })
            .collect::<Vec<_>>(),
        checker
            .file_order()
            .iter()
            .flat_map(|&file| {
                let (arena, _) = checker.file(file).unwrap();
                arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(arena.id(), file, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, record)| {
                (
                    symbol,
                    (
                        record.name().to_owned(),
                        record.flags(),
                        record.check_flags(),
                        record.parent(),
                        record.declarations().map(<[_]>::to_vec),
                        record.value_declaration(),
                        record.export_symbol(),
                    ),
                    [record.members(), record.exports()].map(|table| {
                        table.map(|table| {
                            (
                                table,
                                store
                                    .symbol_table(table)
                                    .unwrap()
                                    .iter()
                                    .map(|(name, symbol)| (name.to_owned(), symbol))
                                    .collect::<Vec<_>>(),
                            )
                        })
                    }),
                    (
                        store.get_merged_symbol(symbol),
                        store.alias_symbol_links(symbol).cloned(),
                        store.export_type_links(symbol).cloned(),
                        store.value_symbol_links(symbol).cloned(),
                        store.declared_type_links(symbol).cloned(),
                        store.module_symbol_links(symbol).cloned(),
                        store.members_and_exports_links(symbol).cloned(),
                    ),
                )
            })
            .collect::<Vec<_>>(),
    )
}

fn check_sources(checker: &mut CanonicalCheckerContext<'_>, owners: &Owners) {
    for file in FILES {
        checker.check_source_file(file).unwrap();
    }
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    for (symbol, expected) in owners
        .exports
        .into_iter()
        .zip([bootstrap.number_type, bootstrap.string_type])
    {
        assert_eq!(
            checker
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            Some(expected)
        );
    }
    assert_value_cold(checker, owners);
}

fn run(source_first: bool) {
    let parsed = SOURCES.map(parse_source_file);
    let mut checker = context(&parsed);
    let owners = owners(&checker, &parsed);
    assert_value_cold(&checker, &owners);
    assert!(checker.store().alias_symbol_links(owners.alias).is_none());
    let type_counts = (
        checker.store().type_len(),
        checker.store().signature_len(),
        checker.store().mapper_len(),
    );

    if source_first {
        check_sources(&mut checker, &owners);
    } else {
        let cold = snapshot(&checker);
        assert_display(&mut checker, &owners);
        assert_eq!(snapshot(&checker), cold);
        assert!(checker.store().alias_symbol_links(owners.alias).is_none());
    }

    assert_alias(&mut checker, &owners);
    let resolved = snapshot(&checker);
    for _ in 0..2 {
        assert_display(&mut checker, &owners);
        assert_alias(&mut checker, &owners);
        assert_eq!(snapshot(&checker), resolved);
    }
    if !source_first {
        check_sources(&mut checker, &owners);
    }
    assert_eq!(
        (
            checker.store().type_len(),
            checker.store().signature_len(),
            checker.store().mapper_len()
        ),
        type_counts
    );
    for file in FILES {
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(file).unwrap())
                .unwrap()
                .type_checked
        );
    }
    let warm = snapshot(&checker);
    for _ in 0..2 {
        for file in FILES {
            checker.recheck_source_file(file).unwrap();
        }
        assert_alias(&mut checker, &owners);
        assert_display(&mut checker, &owners);
        assert_eq!(snapshot(&checker), warm);
    }
}

#[test]
fn merged_module_namespace_symbol_display_is_read_only_before_and_after_alias_resolution() {
    run(false);
}

#[test]
fn merged_module_namespace_symbol_display_preserves_source_first_and_recheck_identity() {
    run(true);
}
