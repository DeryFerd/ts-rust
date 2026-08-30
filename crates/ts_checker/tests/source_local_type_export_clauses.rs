use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, DeclaredTypeLinks, SourceFileLinks, SymbolNodeLinks,
    TypeAliasLinks, TypeNodeLinks, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const CONSUMER: FileId = FileId::new(46_701);
const PROVIDER: FileId = FileId::new(46_702);
const BARREL: FileId = FileId::new(46_703);

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 6],
    sources: Vec<Option<SourceFileLinks>>,
    nodes: Vec<(Option<TypeNodeLinks>, Option<SymbolNodeLinks>)>,
    imports: Vec<Option<AliasSymbolLinks>>,
    aliases: Vec<Option<TypeAliasLinks>>,
    declared: Vec<Option<DeclaredTypeLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn context<'arena>(
    files: &[(FileId, &'arena ParseResult)],
    routes: &[(FileId, FileId)],
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for &(file, parsed) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let path = match file {
            CONSUMER => "\"/project/consumer.ts\"",
            PROVIDER => "\"/project/provider.d.ts\"",
            BARREL => "\"/project/index.d.ts\"",
            _ => panic!("unexpected fixture file"),
        };
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file != CONSUMER,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for &(file, parsed) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let entries = routes.iter().map(|&(source, target)| {
        let parsed = files.iter().find(|(file, _)| *file == source).unwrap().1;
        let specifiers = parsed
            .arena
            .iter()
            .filter_map(|(_, record)| {
                let node = match &record.data {
                    NodeData::ImportDeclaration(import) => Some(import.module_specifier),
                    NodeData::ExportDeclaration(export) => export.module_specifier,
                    _ => None,
                }?;
                Some(NodeRef::new(parsed.arena.id(), source, node))
            })
            .collect::<Vec<_>>();
        let [specifier] = specifiers.as_slice() else {
            panic!("each routed fixture file has one actual module specifier");
        };
        CanonicalModuleResolutionEntry::resolved(
            *specifier,
            CanonicalResolvedModuleInput::new(
                target,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )
    });
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new(entries),
    )
    .unwrap()
}

fn named_node(parsed: &ParseResult, file: FileId, expected: &str, binding: bool) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name = match &record.data {
                NodeData::ImportSpecifier(import) if binding => import.name,
                NodeData::InterfaceDeclaration(interface) if !binding => interface.name,
                NodeData::TypeAliasDeclaration(alias) if !binding => alias.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("fixture declares {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    context
        .file(node.file)
        .unwrap()
        .1
        .symbol(node)
        .and_then(|symbol| context.store().get_merged_symbol(symbol))
        .unwrap()
}

fn export_symbol(
    context: &CanonicalCheckerContext<'_>,
    file: FileId,
    name: &str,
) -> SemanticSymbolId {
    let bound = context.file(file).unwrap().1;
    let module = bound.symbol(bound.source_file()).unwrap();
    let exports = context.store().symbol(module).unwrap().exports().unwrap();
    context
        .store()
        .symbol_table(exports)
        .unwrap()
        .get_source(name)
        .unwrap()
}

fn assert_import(
    context: &CanonicalCheckerContext<'_>,
    binding: NodeRef,
    target: SemanticSymbolId,
) {
    let alias = symbol(context, binding);
    let links = context.store().alias_symbol_links(alias).unwrap();
    assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    assert_eq!(links.type_only_declaration, Some(binding));
    assert!(context.store().value_symbol_links(alias).is_none());
    assert!(context.store().value_symbol_links(target).is_none());
}

fn assert_unchecked(context: &CanonicalCheckerContext<'_>, files: &[(FileId, &ParseResult)]) {
    for &(file, _) in files {
        if file != CONSUMER {
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .is_none_or(|links| !links.type_checked)
            );
        }
    }
}

fn snapshot(context: &CanonicalCheckerContext<'_>, files: &[(FileId, &ParseResult)]) -> Snapshot {
    let store = context.store();
    let nodes = files
        .iter()
        .flat_map(|(file, parsed)| {
            parsed
                .arena
                .iter()
                .map(move |(node, _)| NodeRef::new(parsed.arena.id(), *file, node))
        })
        .collect::<Vec<_>>();
    let symbols = nodes
        .iter()
        .filter_map(|node| context.file(node.file).unwrap().1.symbol(*node))
        .collect::<Vec<_>>();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        sources: files
            .iter()
            .map(|(file, _)| {
                store
                    .source_file_links(context.source_file(*file).unwrap())
                    .cloned()
            })
            .collect(),
        nodes: nodes
            .iter()
            .map(|&node| {
                (
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                )
            })
            .collect(),
        imports: symbols
            .iter()
            .map(|&symbol| store.alias_symbol_links(symbol).cloned())
            .collect(),
        aliases: symbols
            .iter()
            .map(|&symbol| store.type_alias_links(symbol).cloned())
            .collect(),
        declared: symbols
            .iter()
            .map(|&symbol| store.declared_type_links(symbol).cloned())
            .collect(),
        values: symbols
            .iter()
            .map(|&symbol| store.value_symbol_links(symbol).cloned())
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, files: &[(FileId, &ParseResult)]) {
    let before = snapshot(context, files);
    context.check_source_file(CONSUMER).unwrap();
    assert_eq!(snapshot(context, files), before);
    context.recheck_source_file(CONSUMER).unwrap();
    assert_eq!(snapshot(context, files), before);
    assert_unchecked(context, files);
}

fn assert_annotation_identity(
    context: &mut CanonicalCheckerContext<'_>,
    consumer: &ParseResult,
    name: &str,
    target: SemanticSymbolId,
) {
    let expected = context.get_declared_type_of_symbol(target).unwrap();
    let references = consumer
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::TypeReferenceNode(reference) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &consumer.arena.get(reference.type_name)?.data
            else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(consumer.arena.id(), CONSUMER, node))
        })
        .collect::<Vec<_>>();
    assert!(!references.is_empty());
    for reference in references {
        assert_eq!(
            context
                .store()
                .type_node_links(reference)
                .and_then(|links| links.resolved_type),
            Some(expected)
        );
    }
}

#[test]
fn local_named_type_exports_preserve_declaration_and_annotation_identity() {
    for clause in [
        "export { Model, Label };",
        "export type { Model, Label };",
        "export { type Model, type Label };",
    ] {
        let provider = parse_source_file(&format!(
            "interface Model {{ id: number; }} type Label = string; {clause}"
        ));
        let consumer = parse_source_file(concat!(
            "import type { Model, Label } from './provider'; ",
            "const model: Model = { id: 1 }; const label: Label = 'ok'; ",
            "const wrong: Label = 1;"
        ));
        let files = [(CONSUMER, &consumer), (PROVIDER, &provider)];
        let mut context = context(&files, &[(CONSUMER, PROVIDER)]);
        context.check_source_file(CONSUMER).unwrap();
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2322]
        );
        for name in ["Model", "Label"] {
            let declaration = named_node(&provider, PROVIDER, name, false);
            let target = symbol(&context, declaration);
            assert_eq!(
                context.store().symbol(target).unwrap().declarations(),
                Some(&[declaration][..])
            );
            let binding = named_node(&consumer, CONSUMER, name, true);
            assert_import(&context, binding, target);
            let exported = export_symbol(&context, PROVIDER, name);
            assert_eq!(
                context
                    .store()
                    .alias_symbol_links(symbol(&context, binding))
                    .unwrap()
                    .immediate_target,
                Some(exported)
            );
            assert_eq!(
                context.resolve_alias(exported).unwrap().target,
                AliasTargetState::Resolved(target)
            );
            assert_annotation_identity(&mut context, &consumer, name, target);
        }
        assert_unchecked(&context, &files);
        assert_replay(&mut context, &files);
    }
}

#[test]
fn renamed_local_type_exports_survive_a_type_reexport_barrel() {
    let provider = parse_source_file(concat!(
        "interface InternalModel { id: number; } type InternalLabel = string; ",
        "export { InternalModel as PublicModel, InternalLabel as PublicLabel };"
    ));
    let barrel =
        parse_source_file("export { type PublicModel, type PublicLabel } from './provider';");
    let consumer = parse_source_file(concat!(
        "import type { PublicModel as Model, PublicLabel as Label } from './index'; ",
        "const model: Model = { id: 1 }; const label: Label = 'ok';"
    ));
    let files = [
        (CONSUMER, &consumer),
        (BARREL, &barrel),
        (PROVIDER, &provider),
    ];
    let mut context = context(&files, &[(CONSUMER, BARREL), (BARREL, PROVIDER)]);
    context.check_source_file(CONSUMER).unwrap();
    assert!(context.diagnostics().is_empty());
    for (local, original) in [("Model", "InternalModel"), ("Label", "InternalLabel")] {
        let target = symbol(&context, named_node(&provider, PROVIDER, original, false));
        let binding = named_node(&consumer, CONSUMER, local, true);
        assert_import(&context, binding, target);
        let public_name = format!("Public{local}");
        let reexport = export_symbol(&context, BARREL, &public_name);
        let local_export = export_symbol(&context, PROVIDER, &public_name);
        assert_eq!(
            context
                .store()
                .alias_symbol_links(symbol(&context, binding))
                .unwrap()
                .immediate_target,
            Some(reexport)
        );
        assert_eq!(
            context.resolve_alias(reexport).unwrap().target,
            AliasTargetState::Resolved(target)
        );
        assert_eq!(
            context.resolve_alias(local_export).unwrap().target,
            AliasTargetState::Resolved(target)
        );
        assert_eq!(
            context
                .resolve_alias(symbol(&context, binding))
                .unwrap()
                .target,
            AliasTargetState::Resolved(target)
        );
        assert_annotation_identity(&mut context, &consumer, local, target);
    }
    assert_unchecked(&context, &files);
    assert_replay(&mut context, &files);
}

#[test]
fn unused_local_type_exports_resolve_without_typing_the_provider() {
    let provider = parse_source_file(concat!(
        "interface Model { id: number; } type Label = string; ",
        "export { Model, Label };"
    ));
    let consumer = parse_source_file("import type { Model, Label } from './provider';");
    let files = [(CONSUMER, &consumer), (PROVIDER, &provider)];
    let mut context = context(&files, &[(CONSUMER, PROVIDER)]);
    let before = (context.store().type_len(), context.store().signature_len());
    context.check_source_file(CONSUMER).unwrap();
    assert!(context.diagnostics().is_empty());
    assert_eq!(
        (context.store().type_len(), context.store().signature_len()),
        before
    );
    for name in ["Model", "Label"] {
        let target = symbol(&context, named_node(&provider, PROVIDER, name, false));
        assert_import(
            &context,
            named_node(&consumer, CONSUMER, name, true),
            target,
        );
        assert!(context.store().declared_type_links(target).is_none());
        assert!(context.store().type_alias_links(target).is_none());
    }
    for (node, _) in provider.arena.iter() {
        assert!(
            context
                .store()
                .type_node_links(NodeRef::new(provider.arena.id(), PROVIDER, node))
                .is_none()
        );
    }
    assert_unchecked(&context, &files);
    assert_replay(&mut context, &files);
}

#[test]
fn local_type_export_clauses_do_not_authorize_a_type_only_value_read() {
    let provider =
        parse_source_file("type InternalLabel = string; export { InternalLabel as Label };");
    let consumer =
        parse_source_file("import type { Label } from './provider'; const invalid = Label;");
    let files = [(CONSUMER, &consumer), (PROVIDER, &provider)];
    let mut context = context(&files, &[(CONSUMER, PROVIDER)]);
    context.check_source_file(CONSUMER).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].diagnostic.code(), 1361);
    assert_eq!(
        diagnostics[0].diagnostic.render().unwrap(),
        "'Label' cannot be used as a value because it was imported using 'import type'."
    );
    let target = symbol(
        &context,
        named_node(&provider, PROVIDER, "InternalLabel", false),
    );
    assert_import(
        &context,
        named_node(&consumer, CONSUMER, "Label", true),
        target,
    );
    assert!(context.store().type_alias_links(target).is_none());
    assert_unchecked(&context, &files);
    assert_replay(&mut context, &files);
}
