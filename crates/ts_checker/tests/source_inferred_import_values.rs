use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, SourceCheckError, TypeId,
    UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

const IMPORTER: FileId = FileId::new(0);
const PROVIDER: FileId = FileId::new(1);
const PROVIDER_SOURCE: &str = "export const ready = 1 === 1; export const count = 20 + 22;";

fn context<'arena>(
    importer: &'arena ParseResult,
    provider: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, name) in [
        (IMPORTER, importer, "\"/project/importer.ts\""),
        (PROVIDER, provider, "\"/project/provider.ts\""),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
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
    for (file, parsed) in [(IMPORTER, importer), (PROVIDER, provider)] {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let resolutions = importer.arena.iter().filter_map(|(_, record)| {
        let NodeData::ImportDeclaration(import) = &record.data else {
            return None;
        };
        Some(CanonicalModuleResolutionEntry::resolved(
            NodeRef::new(importer.arena.id(), IMPORTER, import.module_specifier),
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        ))
    });
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        [(IMPORTER, &importer.arena), (PROVIDER, &provider.arena)]
            .into_iter()
            .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new(resolutions),
    )
    .unwrap()
}

fn variable(parsed: &ParseResult, file: FileId, name: &str) -> (NodeRef, NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (identifier.text == name).then(|| {
                (
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, variable.name),
                    NodeRef::new(parsed.arena.id(), file, variable.initializer.unwrap()),
                )
            })
        })
        .unwrap_or_else(|| panic!("fixture has variable {name}"))
}

fn import_binding(parsed: &ParseResult, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ImportSpecifier(specifier) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(specifier.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), IMPORTER, node))
        })
        .unwrap_or_else(|| panic!("fixture imports {name}"))
}

fn export_symbol(
    context: &CanonicalCheckerContext<'_>,
    provider: &ParseResult,
    name: &str,
) -> SemanticSymbolId {
    let bound = context.file(PROVIDER).unwrap().1;
    let module = bound.symbol(bound.source_file()).unwrap();
    let exports = context.store().symbol(module).unwrap().exports().unwrap();
    let target = context
        .store()
        .symbol_table(exports)
        .unwrap()
        .get_source(name)
        .unwrap();
    let declaration = variable(provider, PROVIDER, name).0;
    let NodeData::VariableDeclaration(variable) =
        &provider.arena.get(declaration.node).unwrap().data
    else {
        panic!("export is a variable declaration");
    };
    assert!(variable.type_.is_none(), "export type must be inferred");
    assert_eq!(bound.symbol(declaration), Some(target));
    assert_eq!(
        context.store().symbol(target).unwrap().value_declaration(),
        Some(declaration),
    );
    target
}

fn checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

fn assert_import(
    context: &mut CanonicalCheckerContext<'_>,
    importer: &ParseResult,
    provider: &ParseResult,
    local: &str,
    exported: &str,
    read: NodeRef,
    type_: TypeId,
) -> (SemanticSymbolId, SemanticSymbolId) {
    let binding = import_binding(importer, local);
    let alias = context.file(IMPORTER).unwrap().1.symbol(binding).unwrap();
    let target = export_symbol(context, provider, exported);
    assert_ne!(alias, target);
    let links = context.store().alias_symbol_links(alias).unwrap();
    assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    assert!(links.type_only_declaration.is_none());
    assert_eq!(context.get_symbol_at_location(read).unwrap(), Some(alias));
    assert_eq!(context.get_type_at_location(read).unwrap(), type_);
    (alias, target)
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = context.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    importer: &ParseResult,
    provider: &ParseResult,
    reads: &[(NodeRef, TypeId)],
    symbols: &[SemanticSymbolId],
) {
    for &(read, type_) in reads {
        assert_eq!(context.get_type_at_location(read).unwrap(), type_);
    }
    let nodes = [(IMPORTER, importer), (PROVIDER, provider)]
        .into_iter()
        .flat_map(|(file, parsed)| {
            parsed
                .arena
                .iter()
                .map(move |(node, _)| NodeRef::new(parsed.arena.id(), file, node))
        })
        .collect::<Vec<_>>();
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        (
            counts(context),
            context.diagnostics().clone(),
            [IMPORTER, PROVIDER].map(|file| {
                context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            }),
            nodes
                .iter()
                .map(|&node| {
                    (
                        context.store().type_node_links(node).cloned(),
                        context.store().symbol_node_links(node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            symbols
                .iter()
                .map(|&symbol| {
                    (
                        context.store().alias_symbol_links(symbol).cloned(),
                        context.store().value_symbol_links(symbol).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
        )
    };
    let before = snapshot(context);
    for _ in 0..2 {
        for &(read, type_) in reads {
            assert_eq!(context.get_type_at_location(read).unwrap(), type_);
        }
        context.check_source_file(IMPORTER).unwrap();
        context.recheck_source_file(IMPORTER).unwrap();
        assert_eq!(snapshot(context), before);
    }
}

#[test]
fn inferred_scalar_imports_keep_types_aliases_and_assignment_errors() {
    let provider = parse_source_file(PROVIDER_SOURCE);
    let importer = parse_source_file(concat!(
        "import { ready as first, count } from './provider'; ",
        "import { ready as second } from './provider'; ",
        "const good: boolean = first; const again: boolean = second; ",
        "const total: number = count; const bad: string = count;",
    ));
    let first_read = variable(&importer, IMPORTER, "good").2;
    let second_read = variable(&importer, IMPORTER, "again").2;
    let count_read = variable(&importer, IMPORTER, "total").2;
    let (_, bad_name, bad_read) = variable(&importer, IMPORTER, "bad");
    for (provider_first, read_first) in [(false, false), (true, false), (false, true)] {
        let mut context = context(&importer, &provider);
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        let cold = read_first.then(|| context.get_type_at_location(first_read).unwrap());
        context.check_source_file(IMPORTER).unwrap();
        assert!(checked(&context, IMPORTER));
        assert_eq!(checked(&context, PROVIDER), provider_first);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let boolean = bootstrap.boolean_type;
        let number = bootstrap.number_type;
        if let Some(cold) = cold {
            assert_eq!(cold, boolean);
        }
        let first = assert_import(
            &mut context,
            &importer,
            &provider,
            "first",
            "ready",
            first_read,
            boolean,
        );
        let second = assert_import(
            &mut context,
            &importer,
            &provider,
            "second",
            "ready",
            second_read,
            boolean,
        );
        let count = assert_import(
            &mut context,
            &importer,
            &provider,
            "count",
            "count",
            count_read,
            number,
        );
        assert_ne!(first.0, second.0);
        assert_eq!(first.1, second.1);
        assert_ne!(first.1, count.1);
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one receiving-variable error");
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.node, Some(bad_name));
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'.",
        );
        assert_replay(
            &mut context,
            &importer,
            &provider,
            &[
                (first_read, boolean),
                (second_read, boolean),
                (count_read, number),
                (bad_read, number),
            ],
            &[first.0, second.0, count.0, first.1, count.1],
        );
        assert_eq!(checked(&context, PROVIDER), provider_first);
    }
}

#[test]
fn inferred_imports_do_not_check_unrelated_provider_statements() {
    let provider = parse_source_file(&format!("{PROVIDER_SOURCE} debugger;"));
    let importer = parse_source_file(concat!(
        "import { ready, count } from './provider'; ",
        "const flag: boolean = ready; const total: number = count;",
    ));
    let mut context = context(&importer, &provider);
    context.check_source_file(IMPORTER).unwrap();
    assert!(checked(&context, IMPORTER));
    assert!(!checked(&context, PROVIDER));
    assert!(context.diagnostics().is_empty());
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let boolean = bootstrap.boolean_type;
    let number = bootstrap.number_type;
    let ready_read = variable(&importer, IMPORTER, "flag").2;
    let count_read = variable(&importer, IMPORTER, "total").2;
    let ready = assert_import(
        &mut context,
        &importer,
        &provider,
        "ready",
        "ready",
        ready_read,
        boolean,
    );
    let count = assert_import(
        &mut context,
        &importer,
        &provider,
        "count",
        "count",
        count_read,
        number,
    );
    assert_replay(
        &mut context,
        &importer,
        &provider,
        &[(ready_read, boolean), (count_read, number)],
        &[ready.0, count.0, ready.1, count.1],
    );
    assert!(!checked(&context, PROVIDER));
    assert!(matches!(
        context.check_source_file(PROVIDER),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Syntax { .. }
        )),
    ));
    assert!(!checked(&context, PROVIDER));
    assert!(context.diagnostics().is_empty());
}
