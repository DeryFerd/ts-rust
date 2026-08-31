use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId,
    SymbolFlags, SymbolTableId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, TypeData, TypeId,
    ValueSymbolLinks,
    type_records::{ObjectTypeData, TypeCacheState},
    types::{ObjectFlags, TypeFlags},
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARIES: [&str; 3] = [
    include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
    include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
    include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
];
const LIBRARY_PATHS: [&str; 3] = [
    "/lib.es5.d.ts",
    "/lib.decorators.d.ts",
    "/lib.decorators.legacy.d.ts",
];
const LIBRARY_FILES: [FileId; 3] = [
    FileId::new(203_300),
    FileId::new(203_301),
    FileId::new(203_302),
];
const FILES: [FileId; 5] = [
    FileId::new(203_310),
    FileId::new(203_311),
    FileId::new(203_312),
    FileId::new(203_313),
    FileId::new(203_314),
];
const PATHS: [&str; 5] = [
    "/node_modules/foo/index.d.ts",
    "/a.d.ts",
    "/b.d.ts",
    "/augment.ts",
    "/index.ts",
];

// Exact virtual files from globalArrayAugmentationWithAmbientModuleReexportMerge1.ts.
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

fn node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("the source contains {kind:?}"))
}

fn raw_symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap()
}

fn name(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let name = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::ModuleDeclaration(module) => module.name,
        NodeData::VariableDeclaration(variable) => variable.name,
        NodeData::ExportSpecifier(export) => export.name,
        _ => panic!("the selected declaration has a name"),
    };
    NodeRef::new(declaration.arena, declaration.file, name)
}

fn context<'arena>(
    libraries: &'arena [ParseResult; 3],
    parsed: &'arena [ParseResult; 5],
) -> CanonicalCheckerContext<'arena> {
    let sources = libraries
        .iter()
        .enumerate()
        .map(|(index, parsed)| {
            (
                LIBRARY_FILES[index],
                parsed,
                LIBRARY_PATHS[index],
                true,
                true,
                CanonicalModuleState::Script,
            )
        })
        .chain(parsed.iter().enumerate().map(|(index, parsed)| {
            (
                FILES[index],
                parsed,
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
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, declaration, library, module) in &sources {
        assert!(
            parsed.diagnostics.is_empty(),
            "{path}: {:?}",
            parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(format!("\"{path}\"")),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    library,
                    module,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let entries = [1, 4].map(|index| {
        let declaration = node(&parsed[index], FILES[index], SyntaxKind::ImportDeclaration);
        let NodeData::ImportDeclaration(import) =
            &parsed[index].arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        CanonicalModuleResolutionEntry::resolved(
            NodeRef::new(declaration.arena, declaration.file, import.module_specifier),
            CanonicalResolvedModuleInput::new(
                FILES[0],
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )
    });
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        sources
            .iter()
            .map(|(file, parsed, ..)| (*file, &parsed.arena))
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

struct Conflict {
    declarations: [NodeRef; 2],
    names: [NodeRef; 2],
    raw: [SemanticSymbolId; 2],
    raw_tables: [SymbolTableId; 2],
    owner: SemanticSymbolId,
    exports: SymbolTableId,
    selected: SemanticSymbolId,
    selected_declaration: NodeRef,
    aliases: [(SemanticSymbolId, NodeRef); 3],
    target: SemanticSymbolId,
    target_declaration: NodeRef,
}

fn conflict(checker: &CanonicalCheckerContext<'_>, parsed: &[ParseResult; 5]) -> Conflict {
    let declarations =
        [1, 2].map(|index| node(&parsed[index], FILES[index], SyntaxKind::ModuleDeclaration));
    let names = [
        name(&parsed[1], declarations[0]),
        name(&parsed[2], declarations[1]),
    ];
    let raw = declarations.map(|declaration| raw_symbol(checker, declaration));
    let owner = checker.store().get_merged_symbol(raw[0]).unwrap();
    let selected_declaration = node(&parsed[2], FILES[2], SyntaxKind::VariableDeclaration);
    let target_declaration = node(&parsed[0], FILES[0], SyntaxKind::FunctionDeclaration);
    let alias_declarations = [
        node(&parsed[1], FILES[1], SyntaxKind::ExportSpecifier),
        node(&parsed[1], FILES[1], SyntaxKind::NamespaceImport),
        node(&parsed[0], FILES[0], SyntaxKind::ExportAssignment),
    ];
    Conflict {
        declarations,
        names,
        raw,
        raw_tables: raw.map(|symbol| checker.store().symbol(symbol).unwrap().exports().unwrap()),
        owner,
        exports: checker.store().symbol(owner).unwrap().exports().unwrap(),
        selected: raw_symbol(checker, selected_declaration),
        selected_declaration,
        aliases: alias_declarations
            .map(|declaration| (raw_symbol(checker, declaration), declaration)),
        target: checker
            .store()
            .get_merged_symbol(raw_symbol(checker, target_declaration))
            .unwrap(),
        target_declaration,
    }
}

fn assert_selection(checker: &CanonicalCheckerContext<'_>, conflict: &Conflict) {
    let store = checker.store();
    assert_ne!(conflict.raw[0], conflict.raw[1]);
    for raw in conflict.raw {
        assert_eq!(store.get_merged_symbol(raw), Some(conflict.owner));
    }
    let owner = store.symbol(conflict.owner).unwrap();
    assert_eq!(owner.name().as_utf8(), Some("\"mymod\""));
    assert_eq!(owner.declarations(), Some(conflict.declarations.as_slice()));
    assert!(owner.flags().contains(SymbolFlags::VALUE_MODULE));
    assert_eq!(owner.check_flags(), CheckFlags::NONE);
    assert_eq!(owner.parent(), None);
    assert_eq!(owner.exports(), Some(conflict.exports));
    assert_eq!(
        store
            .symbol_table(checker.globals())
            .unwrap()
            .get_source("\"mymod\""),
        Some(conflict.owner)
    );
    let exports = store.symbol_table(conflict.exports).unwrap();
    assert_eq!(exports.len(), 1);
    assert_eq!(exports.get_source("foo"), Some(conflict.selected));
    for (index, expected) in [conflict.aliases[0].0, conflict.selected]
        .into_iter()
        .enumerate()
    {
        assert_eq!(
            store.symbol(conflict.raw[index]).unwrap().exports(),
            Some(conflict.raw_tables[index])
        );
        let raw = store.symbol_table(conflict.raw_tables[index]).unwrap();
        assert_eq!(raw.len(), 1);
        assert_eq!(raw.get_source("foo"), Some(expected));
    }
    let selected = store.symbol(conflict.selected).unwrap();
    assert_eq!(selected.flags(), SymbolFlags::BLOCK_SCOPED_VARIABLE);
    assert_eq!(selected.check_flags(), CheckFlags::NONE);
    assert_eq!(
        selected.declarations(),
        Some([conflict.selected_declaration].as_slice())
    );
    assert_eq!(
        selected.value_declaration(),
        Some(conflict.selected_declaration)
    );
    assert_eq!(selected.parent(), Some(conflict.raw[1]));
    assert_eq!(
        store.get_parent_of_symbol(conflict.selected),
        Some(conflict.owner)
    );
    for (index, &(alias, declaration)) in conflict.aliases.iter().enumerate() {
        assert_ne!(alias, conflict.selected);
        assert_ne!(alias, conflict.target);
        assert_eq!(store.get_merged_symbol(alias), Some(alias));
        let record = store.symbol(alias).unwrap();
        assert_eq!(record.flags(), SymbolFlags::ALIAS);
        assert_eq!(record.declarations(), Some([declaration].as_slice()));
        let next = conflict
            .aliases
            .get(index + 1)
            .map_or(conflict.target, |next| next.0);
        let links = store.alias_symbol_links(alias).unwrap();
        assert_eq!(links.immediate_target, Some(next));
        assert_eq!(
            links.alias_target,
            AliasTargetState::Resolved(conflict.target)
        );
        assert_eq!(links.type_only_declaration, None);
    }
    assert_eq!(
        store.symbol(conflict.aliases[0].0).unwrap().parent(),
        Some(conflict.raw[0])
    );
    assert_eq!(
        store.get_parent_of_symbol(conflict.aliases[0].0),
        Some(conflict.owner)
    );
    let target = store.symbol(conflict.target).unwrap();
    assert!(
        target
            .flags()
            .contains(SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE)
    );
    assert_eq!(
        target.value_declaration(),
        Some(conflict.target_declaration)
    );
    let provider = checker.file(FILES[0]).unwrap().1;
    let provider = store
        .symbol(provider.symbol(provider.source_file()).unwrap())
        .unwrap();
    assert_eq!(
        store
            .symbol_table(provider.exports().unwrap())
            .unwrap()
            .get(InternalSymbolName::ExportEquals.as_ref()),
        Some(conflict.aliases[2].0)
    );
}

fn assert_diagnostics(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &[ParseResult; 5],
    conflict: &Conflict,
) {
    let names = [
        name(&parsed[1], conflict.aliases[0].1),
        name(&parsed[2], conflict.selected_declaration),
    ];
    for (index, expected_start) in [(0, 62), (1, 38)] {
        let range = parsed[index + 1]
            .arena
            .get(names[index].node)
            .unwrap()
            .range;
        assert_eq!(range.start.get(), expected_start);
        assert_eq!(range.end.get() - range.start.get(), 3);
    }
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
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
            panic!("each conflict keeps the other source declaration")
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

fn assert_module_value(
    checker: &mut CanonicalCheckerContext<'_>,
    conflict: &Conflict,
    type_: TypeId,
) {
    assert_eq!(
        checker.store().value_symbol_links(conflict.owner),
        Some(&ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        })
    );
    let record = checker.store().type_payload(type_).unwrap();
    assert_eq!(record.flags(), TypeFlags::OBJECT);
    assert_eq!(record.symbol(), Some(conflict.owner));
    assert!(record.alias().is_none());
    let TypeData::Object(object) = record.data() else {
        panic!("the real module keeps its anonymous value identity")
    };
    assert!(object.target.is_none());
    assert!(object.mapper.is_none());
    assert_eq!(object.instantiations, TypeCacheState::Unallocated);
    if record.object_flags() == ObjectFlags::ANONYMOUS {
        assert_eq!(object, &ObjectTypeData::default());
    } else {
        assert_eq!(
            record.object_flags(),
            ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        );
        assert_eq!(object.structured.members, Some(conflict.exports));
        assert_eq!(
            object.structured.properties.as_deref(),
            Some([conflict.selected].as_slice())
        );
        assert!(object.structured.signatures.is_none());
        assert_eq!(object.structured.call_signature_count, 0);
        assert!(object.structured.index_infos.is_none());
    }
    assert_eq!(
        checker.type_to_string(type_).unwrap(),
        "typeof import(\"mymod\")"
    );
    for location in conflict.names {
        assert_eq!(checker.get_type_at_location(location), Ok(type_));
        assert_eq!(
            checker.get_symbol_at_location(location),
            Ok(Some(conflict.owner))
        );
        assert_eq!(
            checker.type_to_string_at_location(type_, location).unwrap(),
            "typeof import(\"mymod\")"
        );
    }
    for owner in [conflict.owner, conflict.raw[0], conflict.raw[1]] {
        assert_eq!(checker.get_type_of_module_value(owner), Ok(type_));
    }
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = checker.store();
    let root = store.type_payload(type_).unwrap();
    let TypeData::Object(object) = root.data() else {
        panic!("the module snapshot retains its real object type")
    };
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.merged_symbol_len(),
            store.symbol_store().symbol_table_len(),
        ],
        checker.global_types().clone(),
        (
            root.flags(),
            root.object_flags(),
            root.symbol(),
            root.alias(),
            object.clone(),
        ),
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
                        record.declarations().map(<[_]>::to_vec),
                        record.value_declaration(),
                        record.parent(),
                        record.export_symbol(),
                        store.get_merged_symbol(symbol),
                    ),
                    [record.members(), record.exports()].map(|table| {
                        table.map(|table| (table, store.symbol_table(table).unwrap().clone()))
                    }),
                    (
                        store.value_symbol_links(symbol).cloned(),
                        store.alias_symbol_links(symbol).cloned(),
                        store.module_symbol_links(symbol).cloned(),
                        store.declared_type_links(symbol).cloned(),
                    ),
                )
            })
            .collect::<Vec<_>>(),
    )
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the original source, both query orders, and both source-check orders together.
fn ambient_module_values_keep_native_selection_cold_and_warm() {
    let libraries = LIBRARIES.map(parse_source_file);
    let parsed = SOURCES.map(parse_source_file);
    for order in [[0, 1, 2, 3, 4], [0, 2, 1, 3, 4]] {
        for query_first in [false, true] {
            for first_query in [0, 1] {
                let mut checker = context(&libraries, &parsed);
                let conflict = conflict(&checker, &parsed);
                assert_eq!(
                    checker.options().name_resolution.emit_target,
                    ScriptTarget::Es2015
                );
                assert!(checker.options().no_emit);
                assert!(checker.global_type_diagnostics().next().is_none());
                let globals = checker.global_types().clone();
                assert_selection(&checker, &conflict);
                assert_diagnostics(&checker, &parsed, &conflict);
                assert!(checker.store().value_symbol_links(conflict.owner).is_none());
                let early = if query_first {
                    let before = checker.store().type_len();
                    let type_ = checker
                        .get_type_at_location(conflict.names[first_query])
                        .unwrap();
                    assert_eq!(checker.store().type_len(), before + 1);
                    assert_eq!(
                        checker.store().type_payload(type_).unwrap().object_flags(),
                        ObjectFlags::ANONYMOUS
                    );
                    assert_module_value(&mut checker, &conflict, type_);
                    for symbol in [conflict.selected, conflict.target] {
                        assert!(checker.store().value_symbol_links(symbol).is_none());
                    }
                    assert!(
                        checker
                            .store()
                            .signature_links(conflict.target_declaration)
                            .is_none()
                    );
                    for file in FILES {
                        assert!(
                            checker
                                .store()
                                .source_file_links(checker.source_file(file).unwrap())
                                .is_none_or(|links| !links.type_checked)
                        );
                    }
                    let cold = snapshot(&checker, type_);
                    for _ in 0..2 {
                        assert_module_value(&mut checker, &conflict, type_);
                        assert_selection(&checker, &conflict);
                        assert_eq!(snapshot(&checker, type_), cold);
                    }
                    Some(type_)
                } else {
                    None
                };
                for index in order {
                    checker.check_source_file(FILES[index]).unwrap();
                }
                let type_ = checker
                    .get_type_at_location(conflict.names[first_query])
                    .unwrap();
                if let Some(early) = early {
                    assert_eq!(type_, early);
                }
                assert_module_value(&mut checker, &conflict, type_);
                assert_selection(&checker, &conflict);
                let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
                assert_eq!(
                    checker
                        .store()
                        .value_symbol_links(conflict.selected)
                        .unwrap()
                        .resolved_type,
                    Some(number)
                );
                for &(alias, _) in &conflict.aliases {
                    let resolution = checker.resolve_alias(alias).unwrap();
                    assert_eq!(
                        resolution.target,
                        AliasTargetState::Resolved(conflict.target)
                    );
                    assert!(resolution.events.is_empty());
                }
                assert_eq!(checker.global_types(), &globals);
                assert_diagnostics(&checker, &parsed, &conflict);
                let warm = snapshot(&checker, type_);
                for _ in 0..2 {
                    assert_module_value(&mut checker, &conflict, type_);
                    for index in order {
                        checker.recheck_source_file(FILES[index]).unwrap();
                    }
                    assert_module_value(&mut checker, &conflict, type_);
                    assert_selection(&checker, &conflict);
                    assert_diagnostics(&checker, &parsed, &conflict);
                    assert_eq!(snapshot(&checker, type_), warm);
                }
            }
        }
    }
}
