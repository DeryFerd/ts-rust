use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, DeclaredTypeError, DeclaredTypeLinks, MembersAndExportsLinks,
    SourceFileLinks, SymbolNodeLinks, TypeAliasLinks, TypeNodeLinks, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(49_810);
const PROVIDER: FileId = FileId::new(49_811);
const BARREL: FileId = FileId::new(49_812);
const PROVIDER_TEXT: &str = concat!(
    "export declare class Item { value: string; }\n",
    "export type Instance = Item;\n",
    "export type Constructor = typeof Item;\n",
);

fn context<'arena>(
    files: &[(FileId, &'arena ParseResult, &str)],
    entries: Option<Vec<CanonicalModuleResolutionEntry>>,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
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
    for &(file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let arenas = files
        .iter()
        .map(|&(file, parsed, _)| (file, &parsed.arena))
        .collect();
    let bound = binder.finish();
    match entries {
        Some(entries) => CanonicalCheckerContext::new_with_module_resolutions(
            bound,
            arenas,
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new(entries),
        ),
        None => CanonicalCheckerContext::new(bound, arenas, CanonicalCheckerOptions::default()),
    }
    .unwrap()
}

fn alias_body(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, alias.type_))
        })
        .unwrap_or_else(|| panic!("the source declares type {name}"))
}

fn import_parts(parsed: &ParseResult, node: NodeRef) -> (NodeRef, NodeRef, NodeRef) {
    let NodeData::ImportTypeNode(import) = &parsed.arena.get(node.node).unwrap().data else {
        panic!("the alias body is the written import type");
    };
    let argument = NodeRef::new(node.arena, node.file, import.argument);
    let NodeData::LiteralTypeNode(literal) = &parsed.arena.get(import.argument).unwrap().data
    else {
        panic!("the import argument is a literal type");
    };
    (
        argument,
        NodeRef::new(node.arena, node.file, literal.literal),
        NodeRef::new(node.arena, node.file, import.qualifier.unwrap()),
    )
}

fn resolved(specifier: NodeRef, target: FileId) -> CanonicalModuleResolutionEntry {
    CanonicalModuleResolutionEntry::resolved(
        specifier,
        CanonicalResolvedModuleInput::new(
            target,
            CanonicalModuleResolutionMode::Esm,
            CanonicalModuleResolutionMode::Esm,
        ),
    )
}

fn declaration(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
    });
    let node = nodes.next().expect("the source has this declaration");
    assert!(nodes.next().is_none());
    node
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

#[derive(Debug, Eq, PartialEq)]
struct SymbolState {
    symbol: SemanticSymbolId,
    declared: Option<DeclaredTypeLinks>,
    value: Option<ValueSymbolLinks>,
    alias: Option<AliasSymbolLinks>,
    type_alias: Option<TypeAliasLinks>,
    members: Option<MembersAndExportsLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    sources: Vec<Option<SourceFileLinks>>,
    nodes: Vec<(NodeRef, Option<TypeNodeLinks>, Option<SymbolNodeLinks>)>,
    symbols: Vec<SymbolState>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(context: &CanonicalCheckerContext<'_>) -> Snapshot {
    let store = context.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        sources: context
            .file_order()
            .iter()
            .map(|&file| {
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            })
            .collect(),
        nodes: context
            .file_order()
            .iter()
            .flat_map(|&file| {
                let arena = context.file(file).unwrap().0;
                arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(arena.id(), file, node);
                    (
                        node,
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                    )
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| SymbolState {
                symbol,
                declared: store.declared_type_links(symbol).cloned(),
                value: store.value_symbol_links(symbol).cloned(),
                alias: store.alias_symbol_links(symbol).cloned(),
                type_alias: store.type_alias_links(symbol).cloned(),
                members: store.members_and_exports_links(symbol).cloned(),
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_resolved_owner(
    context: &CanonicalCheckerContext<'_>,
    node: NodeRef,
    owner: SemanticSymbolId,
) {
    assert_eq!(
        context
            .store()
            .symbol_node_links(node)
            .unwrap()
            .resolved_symbol,
        Some(owner),
    );
}

#[test]
fn ordinary_import_types_keep_class_type_and_value_owners_in_both_query_orders() {
    let source = parse_source_file(concat!(
        "export type Instance = import('./provider').Item;\n",
        "export type Constructor = typeof import('./provider').Item;\n",
    ));
    let provider = parse_source_file(PROVIDER_TEXT);
    let instance = alias_body(&source, SOURCE, "Instance");
    let constructor = alias_body(&source, SOURCE, "Constructor");
    let files = [
        (SOURCE, &source, "\"/project/source.ts\""),
        (PROVIDER, &provider, "\"/project/provider.ts\""),
    ];
    for source_first in [false, true] {
        let mut context = context(
            &files,
            Some(vec![
                resolved(import_parts(&source, instance).1, PROVIDER),
                resolved(import_parts(&source, constructor).1, PROVIDER),
            ]),
        );
        if source_first {
            context.check_source_file(PROVIDER).unwrap();
            context.check_source_file(SOURCE).unwrap();
        }
        let instance_type = context.get_type_from_type_node(instance).unwrap();
        let constructor_type = context.get_type_from_type_node(constructor).unwrap();
        let owner = symbol(
            &context,
            declaration(&provider, PROVIDER, SyntaxKind::ClassDeclaration),
        );
        assert_ne!(instance_type, constructor_type);
        assert_eq!(
            context.get_declared_type_of_symbol(owner),
            Ok(instance_type)
        );
        assert_eq!(
            context.get_type_from_type_node(alias_body(&provider, PROVIDER, "Instance")),
            Ok(instance_type),
        );
        assert_eq!(
            context.get_type_from_type_node(alias_body(&provider, PROVIDER, "Constructor")),
            Ok(constructor_type),
        );
        for (node, type_) in [(instance, instance_type), (constructor, constructor_type)] {
            assert_resolved_owner(&context, node, owner);
            assert_eq!(
                context.store().type_payload(type_).unwrap().symbol(),
                Some(owner)
            );
        }
        context.check_source_file(PROVIDER).unwrap();
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let before = snapshot(&context);
        for _ in 0..2 {
            assert_eq!(context.get_type_from_type_node(instance), Ok(instance_type));
            assert_eq!(
                context.get_type_from_type_node(constructor),
                Ok(constructor_type)
            );
            context.recheck_source_file(PROVIDER).unwrap();
            context.recheck_source_file(SOURCE).unwrap();
            assert_eq!(snapshot(&context), before);
        }
    }
}

#[test]
fn ordinary_import_types_follow_real_export_stars_and_aliases() {
    let source = parse_source_file(concat!(
        "export type Direct = import('./barrel').Item;\n",
        "export type Renamed = import('./barrel').Renamed;\n",
        "export type Constructor = typeof import('./barrel').Renamed;\n",
    ));
    let barrel = parse_source_file(concat!(
        "export * from './provider';\n",
        "export { Item as Renamed } from './provider';\n",
    ));
    let provider = parse_source_file(PROVIDER_TEXT);
    let requests =
        ["Direct", "Renamed", "Constructor"].map(|name| alias_body(&source, SOURCE, name));
    let mut entries: Vec<_> = requests
        .iter()
        .map(|&node| resolved(import_parts(&source, node).1, BARREL))
        .collect();
    entries.extend(barrel.arena.iter().filter_map(|(_, record)| {
        let NodeData::ExportDeclaration(export) = &record.data else {
            return None;
        };
        Some(resolved(
            NodeRef::new(barrel.arena.id(), BARREL, export.module_specifier?),
            PROVIDER,
        ))
    }));
    let mut context = context(
        &[
            (SOURCE, &source, "\"/project/source.ts\""),
            (BARREL, &barrel, "\"/project/barrel.ts\""),
            (PROVIDER, &provider, "\"/project/provider.ts\""),
        ],
        Some(entries),
    );
    let owner = symbol(
        &context,
        declaration(&provider, PROVIDER, SyntaxKind::ClassDeclaration),
    );
    let alias = symbol(
        &context,
        declaration(&barrel, BARREL, SyntaxKind::ExportSpecifier),
    );
    assert_ne!(alias, owner);
    let types = requests.map(|node| context.get_type_from_type_node(node).unwrap());
    assert_eq!(types[0], types[1]);
    assert_ne!(types[1], types[2]);
    assert_eq!(context.get_declared_type_of_symbol(owner), Ok(types[0]));
    assert_eq!(
        context
            .store()
            .alias_symbol_links(alias)
            .unwrap()
            .alias_target,
        AliasTargetState::Resolved(owner)
    );
    for node in requests {
        assert_resolved_owner(&context, node, owner);
    }
    for file in [PROVIDER, BARREL, SOURCE] {
        context.check_source_file(file).unwrap();
    }
    assert!(context.diagnostics().is_empty());
    let before = snapshot(&context);
    for (node, type_) in requests.into_iter().zip(types).rev() {
        assert_eq!(context.get_type_from_type_node(node), Ok(type_));
    }
    for file in [SOURCE, BARREL, PROVIDER] {
        context.recheck_source_file(file).unwrap();
    }
    assert_eq!(snapshot(&context), before);
}

#[test]
fn ordinary_import_types_require_each_exact_manifest_entry() {
    let source = parse_source_file(concat!(
        "export type First = import('./provider').Item;\n",
        "export type Second = import('./provider').Item;\n",
    ));
    let provider = parse_source_file(PROVIDER_TEXT);
    let first = alias_body(&source, SOURCE, "First");
    let second = alias_body(&source, SOURCE, "Second");
    assert_ne!(
        import_parts(&source, first).1,
        import_parts(&source, second).1
    );
    let mut context = context(
        &[
            (SOURCE, &source, "\"/project/source.ts\""),
            (PROVIDER, &provider, "\"/project/provider.ts\""),
        ],
        Some(vec![resolved(import_parts(&source, first).1, PROVIDER)]),
    );
    let type_ = context.get_type_from_type_node(first).unwrap();
    let before = snapshot(&context);
    let error = context.get_type_from_type_node(second).unwrap_err();
    assert!(matches!(error, DeclaredTypeError::TypeNodeUnavailable(_)));
    assert_eq!(snapshot(&context), before);
    assert_eq!(context.get_type_from_type_node(second), Err(error));
    assert_eq!(context.get_type_from_type_node(first), Ok(type_));
    assert_eq!(snapshot(&context), before);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn ordinary_import_types_keep_missing_capability_distinct_from_unresolved_modules() {
    let source = parse_source_file("export type Use = import('./provider').Item;");
    let provider = parse_source_file(PROVIDER_TEXT);
    let node = alias_body(&source, SOURCE, "Use");
    let files = [
        (SOURCE, &source, "\"/project/source.ts\""),
        (PROVIDER, &provider, "\"/project/provider.ts\""),
    ];
    let mut errors = Vec::new();
    for entries in [None, Some(Vec::new())] {
        let mut context = context(&files, entries);
        let before = snapshot(&context);
        let error = context.get_type_from_type_node(node).unwrap_err();
        assert!(matches!(error, DeclaredTypeError::TypeNodeUnavailable(_)));
        assert_eq!(snapshot(&context), before);
        assert_eq!(context.get_type_from_type_node(node), Err(error));
        assert_eq!(snapshot(&context), before);
        assert!(context.diagnostics().is_empty());
        errors.push(error);
    }
    assert_ne!(errors[0], errors[1]);
}

#[test]
fn ordinary_import_type_errors_keep_real_nodes_codes_and_error_identity() {
    for (text, code) in [
        ("export type Use = import(123).Item;", 1141),
        ("export type Use = import('./absent').Item;", 2307),
        ("export type Use = import('./provider').Missing;", 2694),
    ] {
        let source = parse_source_file(text);
        let provider = parse_source_file(PROVIDER_TEXT);
        let node = alias_body(&source, SOURCE, "Use");
        let (argument, specifier, qualifier) = import_parts(&source, node);
        let entries = match code {
            1141 => Vec::new(),
            2307 => vec![CanonicalModuleResolutionEntry::unresolved(specifier)],
            2694 => vec![resolved(specifier, PROVIDER)],
            _ => unreachable!(),
        };
        let mut context = context(
            &[
                (SOURCE, &source, "\"/project/source.ts\""),
                (PROVIDER, &provider, "\"/project/provider.ts\""),
            ],
            Some(entries),
        );
        let error_type = context.store().intrinsic_bootstrap().unwrap().error_type;
        assert_eq!(context.get_type_from_type_node(node), Ok(error_type));
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!(
                "the import has one TS{code} diagnostic: {:?}",
                context.diagnostics()
            );
        };
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(
            diagnostic.node,
            Some(match code {
                1141 => argument,
                2307 => specifier,
                2694 => qualifier,
                _ => unreachable!(),
            })
        );
        let before = snapshot(&context);
        for _ in 0..2 {
            assert_eq!(context.get_type_from_type_node(node), Ok(error_type));
            assert_eq!(snapshot(&context), before);
        }
    }
}

#[test]
fn ordinary_import_types_do_not_admit_later_syntax() {
    for text in [
        "export type Use = import('./provider');",
        "export type Use = import('./provider').Item<string>;",
        "export type Use = import('./provider').Nested.Item;",
        "export type Use = import('./provider', { with: { 'resolution-mode': 'import' } }).Item;",
    ] {
        let source = parse_source_file(text);
        let provider = parse_source_file(PROVIDER_TEXT);
        let node = alias_body(&source, SOURCE, "Use");
        let NodeData::ImportTypeNode(import) = &source.arena.get(node.node).unwrap().data else {
            panic!("the request is an import type");
        };
        let NodeData::LiteralTypeNode(argument) = &source.arena.get(import.argument).unwrap().data
        else {
            panic!("the unsupported syntax still has a literal module name");
        };
        let specifier = NodeRef::new(source.arena.id(), SOURCE, argument.literal);
        let mut context = context(
            &[
                (SOURCE, &source, "\"/project/source.ts\""),
                (PROVIDER, &provider, "\"/project/provider.ts\""),
            ],
            Some(vec![resolved(specifier, PROVIDER)]),
        );
        let before = snapshot(&context);
        let error = context.get_type_from_type_node(node).unwrap_err();
        assert!(matches!(error, DeclaredTypeError::TypeNodeUnavailable(_)));
        assert_eq!(snapshot(&context), before);
        assert_eq!(context.get_type_from_type_node(node), Err(error));
        assert_eq!(snapshot(&context), before);
    }
}
