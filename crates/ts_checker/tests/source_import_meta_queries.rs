use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions};
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const LIBRARY_FILE: FileId = FileId::new(0);
const SOURCE_FILE: FileId = FileId::new(1);

fn context<'arena>(
    library: &'arena ParseResult,
    source: &'arena ParseResult,
    module: ModuleKind,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path, is_library) in [
        (library, LIBRARY_FILE, "\"/lib.es5.d.ts\"", true),
        (source, SOURCE_FILE, "\"/main.ts\"", false),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    is_library,
                    is_library,
                    if is_library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_implied_node_format(ModuleKind::CommonJs),
            )
            .unwrap();
    }
    for (parsed, file) in [(library, LIBRARY_FILE), (source, SOURCE_FILE)] {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        [(LIBRARY_FILE, &library.arena), (SOURCE_FILE, &source.arena)]
            .into_iter()
            .collect(),
        CanonicalCheckerOptions {
            module_kind: module,
            emit_common_js: module == ModuleKind::CommonJs,
            no_emit: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2025,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn meta_nodes(parsed: &ParseResult) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::MetaProperty(meta) = &record.data else {
                return None;
            };
            (meta.keyword_token == SyntaxKind::ImportKeyword).then(|| {
                (
                    NodeRef::new(parsed.arena.id(), SOURCE_FILE, node),
                    NodeRef::new(parsed.arena.id(), SOURCE_FILE, meta.name),
                )
            })
        })
        .unwrap()
}

#[test]
fn cold_import_meta_name_symbol_query_does_not_check_the_source_or_module() {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file("const meta = 1; const value = import.meta;");
    let (expression, name) = meta_nodes(&source);
    for (module, code) in [(ModuleKind::CommonJs, 1343), (ModuleKind::NodeNext, 1470)] {
        let mut context = context(&library, &source, module);
        let file = context.source_file(SOURCE_FILE).unwrap();
        assert!(context.global_type_diagnostics().next().is_none());
        assert!(context.store().type_node_links(expression).is_none());

        let property = context.get_symbol_at_location(name).unwrap().unwrap();
        assert_eq!(
            context.store().symbol(property).unwrap().check_flags(),
            CheckFlags::READONLY
        );
        let type_ = context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(context.type_to_string(type_).unwrap(), "ImportMeta");
        assert!(context.diagnostics().as_slice().is_empty());
        assert!(context.global_type_diagnostics().next().is_none());
        assert!(context.store().type_node_links(expression).is_none());
        assert!(
            !context
                .store()
                .source_file_links(file)
                .is_some_and(|links| links.type_checked)
        );

        assert_eq!(context.get_type_at_location(expression), Ok(type_));
        assert_eq!(context.get_type_at_location(name), Ok(type_));
        assert_eq!(context.get_symbol_at_location(name), Ok(Some(property)));
        let global = context.get_symbol_at_location(expression).unwrap().unwrap();
        assert_ne!(global, property);
        let declarations = context.get_symbol_declarations(global).unwrap();
        assert!(!declarations.is_empty());
        assert!(declarations.iter().all(|node| node.file == LIBRARY_FILE));
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [code]
        );
        let diagnostics = context.diagnostics().as_slice().to_vec();
        context.recheck_source_file(SOURCE_FILE).unwrap();
        assert_eq!(context.diagnostics().as_slice(), diagnostics);
        assert_eq!(context.get_symbol_at_location(name), Ok(Some(property)));
        assert_eq!(context.get_type_at_location(expression), Ok(type_));
    }
}

#[test]
fn cold_import_meta_name_symbol_query_memoizes_only_the_missing_global_error() {
    let parsed_library = parse_source_file(LIBRARY);
    let range = parsed_library
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            matches!(&parsed_library.arena.get(interface.name)?.data,
            NodeData::Identifier(name) if name.text == "ImportMeta")
            .then_some(record.range)
        })
        .unwrap();
    let mut library_text = LIBRARY.to_owned();
    let start = range.start.get() as usize;
    let end = range.end.get() as usize;
    library_text.replace_range(start..end, &" ".repeat(end - start));
    let library = parse_source_file(&library_text);
    let source = parse_source_file("const value = import.meta;");
    let (expression, name) = meta_nodes(&source);
    let mut context = context(&library, &source, ModuleKind::CommonJs);
    let empty = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .empty_object_type;
    let file = context.source_file(SOURCE_FILE).unwrap();
    assert!(context.global_type_diagnostics().next().is_none());

    let property = context.get_symbol_at_location(name).unwrap().unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .resolved_type,
        Some(empty)
    );
    assert!(context.diagnostics().as_slice().is_empty());
    assert!(context.store().type_node_links(expression).is_none());
    assert!(
        !context
            .store()
            .source_file_links(file)
            .is_some_and(|links| links.type_checked)
    );
    let globals = context
        .global_type_diagnostics()
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(
        globals
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2318]
    );
    assert!(globals[0].node.is_none());

    assert_eq!(context.get_symbol_at_location(name), Ok(Some(property)));
    assert_eq!(context.get_type_at_location(expression), Ok(empty));
    assert_eq!(context.get_type_at_location(name), Ok(empty));
    assert_eq!(context.get_symbol_at_location(expression), Ok(None));
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [1343]
    );
    assert_eq!(
        context
            .global_type_diagnostics()
            .cloned()
            .collect::<Vec<_>>(),
        globals
    );
    let diagnostics = context.diagnostics().as_slice().to_vec();
    context.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(context.diagnostics().as_slice(), diagnostics);
    assert_eq!(
        context
            .global_type_diagnostics()
            .cloned()
            .collect::<Vec<_>>(),
        globals
    );
    assert_eq!(context.get_symbol_at_location(name), Ok(Some(property)));
}
