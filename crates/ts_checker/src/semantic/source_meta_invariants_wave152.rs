use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SymbolFlags,
};
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};
use xxhash_rust::xxh3::xxh3_128;

use super::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostic, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalGlobalTypeDiagnostic, CanonicalGlobalTypeInitializationError,
    DeclaredTypeError, DeclaredTypeHost, DeclaredTypeUnavailable, SemanticSymbolId,
    SourceCheckError, SourceMetaError, SymbolNodeLinks, TypeId, TypeNodeLinks, ValueSymbolLinks,
    artifact_queries::CanonicalArtifactQueryError,
    production::GlobalMergeCompletion,
    source_meta::{check_import_meta_property, plan_import_meta_property},
};

const LIBRARY: &str = include_str!("../../../ts_bundled/libs/lib.es5.d.ts");
const LIBRARY_FILE: FileId = FileId::new(152_100);
const SOURCE_FILE: FileId = FileId::new(152_101);
const SECOND_FILE: FileId = FileId::new(152_102);

#[derive(Clone, Copy)]
struct MetaNodes {
    expression: NodeRef,
    name: NodeRef,
}

#[derive(Debug, Eq, PartialEq)]
struct Observation {
    store_hash: u128,
    counts: [usize; 6],
    links: [usize; 26],
    diagnostics: Vec<CanonicalCheckerDiagnostic>,
    globals: Vec<CanonicalGlobalTypeDiagnostic>,
}

fn parsed(source: &str) -> ParseResult {
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    parsed
}

fn options(module_kind: ModuleKind) -> CanonicalCheckerOptions {
    let mut options = CanonicalCheckerOptions {
        module_kind,
        ..CanonicalCheckerOptions::default()
    };
    options.name_resolution.emit_target = ScriptTarget::Es2025;
    options.emit_common_js = module_kind == ModuleKind::CommonJs;
    options
}

fn context<'a>(
    library: &'a ParseResult,
    sources: &[(FileId, &'a ParseResult, Option<ModuleKind>)],
    options: CanonicalCheckerOptions,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &library.arena,
            library.source_file,
            LIBRARY_FILE,
            CanonicalSourceFileFacts::new_with_default_library(
                EscapedName::source("\"/lib/lib.es5.d.ts\""),
                CanonicalSourceLanguage::TypeScript,
                true,
                true,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    let mut arenas = vec![(LIBRARY_FILE, &library.arena)];
    for &(file, parsed, format) in sources {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut facts = CanonicalSourceFileFacts::new(
            EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::External,
        );
        if let Some(format) = format {
            facts = facts.with_implied_node_format(format);
        }
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts)
            .unwrap();
        arenas.push((file, &parsed.arena));
    }
    for &(file, arena) in &arenas {
        binder
            .bind_typescript_declaration_slice(arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(binder.finish(), arenas, options).unwrap()
}

fn meta_nodes(source: &ParseResult, file: FileId) -> MetaNodes {
    source
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::MetaProperty(meta) = &record.data else {
                return None;
            };
            (meta.keyword_token == SyntaxKind::ImportKeyword).then_some(MetaNodes {
                expression: NodeRef::new(source.arena.id(), file, node),
                name: NodeRef::new(source.arena.id(), file, meta.name),
            })
        })
        .expect("the real source contains import.meta")
}

fn observe(context: &CanonicalCheckerContext<'_>) -> Observation {
    let store = context.store();
    // Include existing record contents, not just counts, when checking no-write errors.
    let state = format!("{store:?}");
    Observation {
        store_hash: xxh3_128(state.as_bytes()),
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
        ],
        links: store.checker_link_allocated_lengths(),
        diagnostics: context.diagnostics().as_slice().to_vec(),
        globals: context.global_type_diagnostics().cloned().collect(),
    }
}

fn assert_meta_error<T: std::fmt::Debug>(
    result: &Result<T, CanonicalArtifactQueryError>,
    expected: SourceMetaError,
) {
    assert!(
        matches!(
            result,
            Err(CanonicalArtifactQueryError::SourceCheck(SourceCheckError::MetaProperty(error)))
                if *error == expected
        ),
        "expected {expected:?}, got {result:?}"
    );
}

fn global_symbol(context: &CanonicalCheckerContext<'_>, name: &str) -> SemanticSymbolId {
    let globals = context.store().intrinsic_bootstrap().unwrap().globals;
    context
        .store()
        .symbol_table(globals)
        .unwrap()
        .get_source(name)
        .unwrap()
}

fn warm(context: &mut CanonicalCheckerContext<'_>, nodes: MetaNodes) -> TypeId {
    let type_ = context.get_type_at_location(nodes.expression).unwrap();
    assert_eq!(context.get_type_at_location(nodes.name), Ok(type_));
    context.get_symbol_at_location(nodes.expression).unwrap();
    context.get_symbol_at_location(nodes.name).unwrap().unwrap();
    type_
}

fn replaced_library(replacement: &str) -> String {
    let library = parsed(LIBRARY);
    let range = library
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &library.arena.get(interface.name)?.data else {
                return None;
            };
            (name.text == "ImportMeta").then_some(record.range)
        })
        .unwrap();
    let mut source = LIBRARY.to_owned();
    source.replace_range(
        usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap(),
        replacement,
    );
    source
}

#[test]
fn real_library_meta_queries_keep_lazy_global_and_distinct_readonly_wrapper() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let second = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    let other = meta_nodes(&second, SECOND_FILE);
    for name_first in [false, true] {
        let mut context = context(
            &library,
            &[(SOURCE_FILE, &source, None), (SECOND_FILE, &second, None)],
            options(ModuleKind::EsNext),
        );
        let declared = global_symbol(&context, "ImportMeta");
        assert!(context.store().import_meta_global().is_none());
        assert!(context.store().import_meta_expression().is_none());
        assert!(context.global_type_diagnostics().next().is_none());
        context.check_source_file(SOURCE_FILE).unwrap();
        let actual = context.store().import_meta_global().unwrap().type_();
        assert_eq!(
            context.store().type_payload(actual).unwrap().symbol(),
            Some(declared)
        );
        assert!(context.store().import_meta_expression().is_none());
        let order = if name_first {
            [nodes.name, nodes.expression]
        } else {
            [nodes.expression, nodes.name]
        };
        for node in order {
            assert_eq!(context.get_type_at_location(node), Ok(actual));
            context.get_symbol_at_location(node).unwrap().unwrap();
        }
        let wrapper = context.store().import_meta_expression().unwrap();
        assert_ne!(wrapper.type_, actual);
        assert_ne!(wrapper.symbol, declared);
        assert_ne!(wrapper.meta, declared);
        assert_eq!(wrapper.import_meta_type, actual);
        let property = context.store().symbol(wrapper.meta).unwrap();
        assert_eq!(
            property.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
        );
        assert_eq!(property.check_flags(), CheckFlags::READONLY);
        assert_eq!(property.parent(), Some(wrapper.symbol));
        assert!(property.declarations().is_none());
        assert_eq!(
            context.get_symbol_at_location(nodes.expression),
            Ok(Some(declared))
        );
        assert_eq!(
            context.get_symbol_at_location(nodes.name),
            Ok(Some(wrapper.meta))
        );
        assert_eq!(warm(&mut context, other), actual);
        let before = observe(&context);
        for file in [SECOND_FILE, SOURCE_FILE, SOURCE_FILE, SECOND_FILE] {
            context.check_source_file(file).unwrap();
        }
        for node in [other.name, nodes.expression, other.expression, nodes.name] {
            assert_eq!(context.get_type_at_location(node), Ok(actual));
            context.get_symbol_at_location(node).unwrap().unwrap();
        }
        assert_eq!(observe(&context), before);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn lazy_global_fallback_diagnostics_survive_source_and_artifact_replay() {
    let source = parsed("import.meta;");
    let second = parsed("import.meta;");
    for (replacement, code) in [
        ("", 2318),
        ("type ImportMeta = {};", 2316),
        ("interface ImportMeta<T> {}", 2317),
    ] {
        let library = parsed(&replaced_library(replacement));
        for reverse in [false, true] {
            let mut context = context(
                &library,
                &[(SOURCE_FILE, &source, None), (SECOND_FILE, &second, None)],
                options(ModuleKind::EsNext),
            );
            let nodes = meta_nodes(&source, SOURCE_FILE);
            let other = meta_nodes(&second, SECOND_FILE);
            assert!(context.global_type_diagnostics().next().is_none());
            assert!(context.store().import_meta_global().is_none());
            let expected = context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .empty_object_type;
            for node in if reverse {
                [other.name, nodes.expression, other.expression, nodes.name]
            } else {
                [nodes.expression, other.name, nodes.name, other.expression]
            } {
                assert_eq!(context.get_type_at_location(node), Ok(expected));
                context.get_symbol_at_location(node).unwrap();
                let diagnostics = context
                    .global_type_diagnostics()
                    .cloned()
                    .collect::<Vec<_>>();
                assert_eq!(diagnostics.len(), 1, "{replacement:?}");
                assert_eq!(diagnostics[0].diagnostic.code(), code);
                assert_eq!(diagnostics[0].diagnostic.arguments[0], "ImportMeta");
            }
            let before = observe(&context);
            for file in [SOURCE_FILE, SECOND_FILE, SOURCE_FILE] {
                context.check_source_file(file).unwrap();
            }
            assert_eq!(observe(&context), before);
            assert!(context.diagnostics().is_empty());
        }
    }
}

#[test]
fn import_meta_type_link_metadata_fails_before_a_cold_global_write() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    for warm_first in [false, true] {
        for node in [nodes.expression, nodes.name] {
            let mut context = context(
                &library,
                &[(SOURCE_FILE, &source, None)],
                options(ModuleKind::EsNext),
            );
            let expected = warm_first.then(|| warm(&mut context, nodes));
            let original = context
                .store()
                .type_node_links(node)
                .cloned()
                .unwrap_or_default();
            let mut poisoned = original.clone();
            poisoned.outer_type_parameters = Some(Vec::new());
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_node_links(node, poisoned)
            );
            let before = observe(&context);
            assert_meta_error(
                &context.get_type_at_location(node),
                SourceMetaError::InvalidTypeCache(node),
            );
            assert_eq!(
                observe(&context),
                before,
                "warm={warm_first}, node={node:?}"
            );
            assert_meta_error(
                &context.get_symbol_at_location(node),
                SourceMetaError::InvalidTypeCache(node),
            );
            assert_eq!(observe(&context), before);
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_node_links(node, original)
            );
            let restored = warm(&mut context, nodes);
            assert!(expected.is_none_or(|expected| expected == restored));
        }
    }
}

#[test]
fn matching_wrong_expression_and_name_types_do_not_authenticate_each_other() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    for warm_first in [false, true] {
        let mut context = context(
            &library,
            &[(SOURCE_FILE, &source, None)],
            options(ModuleKind::EsNext),
        );
        let expected = warm_first.then(|| warm(&mut context, nodes));
        let original = [nodes.expression, nodes.name].map(|node| {
            context
                .store()
                .type_node_links(node)
                .cloned()
                .unwrap_or_default()
        });
        let wrong = context.store().intrinsic_bootstrap().unwrap().number_type;
        for node in [nodes.expression, nodes.name] {
            assert!(context.store_mut_for_test().set_type_node_links(
                node,
                TypeNodeLinks {
                    resolved_type: Some(wrong),
                    ..TypeNodeLinks::default()
                },
            ));
        }
        let before = observe(&context);
        for node in [nodes.name, nodes.expression] {
            assert_meta_error(
                &context.get_type_at_location(node),
                SourceMetaError::InvalidTypeCache(nodes.expression),
            );
            assert_meta_error(
                &context.get_symbol_at_location(node),
                SourceMetaError::InvalidTypeCache(nodes.expression),
            );
            assert_eq!(observe(&context), before, "warm={warm_first}");
        }
        for (node, links) in [nodes.expression, nodes.name].into_iter().zip(original) {
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_node_links(node, links)
            );
        }
        let restored = warm(&mut context, nodes);
        assert!(expected.is_none_or(|expected| expected == restored));
    }
}

#[test]
fn wrong_meta_symbol_caches_fail_without_lazy_publication() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    for warm_first in [false, true] {
        for node in [nodes.expression, nodes.name] {
            let mut context = context(
                &library,
                &[(SOURCE_FILE, &source, None)],
                options(ModuleKind::EsNext),
            );
            let expected = warm_first.then(|| warm(&mut context, nodes));
            let original = context
                .store()
                .symbol_node_links(node)
                .cloned()
                .unwrap_or_default();
            let wrong = global_symbol(&context, "Number");
            assert!(context.store_mut_for_test().set_symbol_node_links(
                node,
                SymbolNodeLinks {
                    resolved_symbol: Some(wrong)
                },
            ));
            let before = observe(&context);
            assert_meta_error(
                &context.get_type_at_location(node),
                SourceMetaError::InvalidSymbolCache(node),
            );
            assert_eq!(observe(&context), before);
            assert_meta_error(
                &context.get_symbol_at_location(node),
                SourceMetaError::InvalidSymbolCache(node),
            );
            assert_eq!(observe(&context), before);
            assert!(
                context
                    .store_mut_for_test()
                    .set_symbol_node_links(node, original)
            );
            let restored = warm(&mut context, nodes);
            assert!(expected.is_none_or(|expected| expected == restored));
        }
    }
}

#[test]
fn foreign_meta_handles_are_rejected_before_store_publication() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    let foreign_source = parsed("import.meta;");
    let foreign_nodes = meta_nodes(&foreign_source, SOURCE_FILE);
    let mut foreign = context(
        &library,
        &[(SOURCE_FILE, &foreign_source, None)],
        options(ModuleKind::EsNext),
    );
    let foreign_type = warm(&mut foreign, foreign_nodes);
    let foreign_global = foreign.store().import_meta_global().unwrap().clone();
    let foreign_wrapper = foreign.store().import_meta_expression().unwrap();
    let mut context = context(
        &library,
        &[(SOURCE_FILE, &source, None)],
        options(ModuleKind::EsNext),
    );
    let before = observe(&context);
    assert_eq!(
        context.get_type_at_location(foreign_nodes.expression),
        Err(CanonicalArtifactQueryError::ForeignNode(
            foreign_nodes.expression
        )),
    );
    assert!(
        !context
            .store_mut_for_test()
            .set_import_meta_global(foreign_global)
    );
    assert!(
        !context
            .store_mut_for_test()
            .set_import_meta_expression(foreign_wrapper)
    );
    assert!(!context.store_mut_for_test().set_type_node_links(
        nodes.expression,
        TypeNodeLinks {
            resolved_type: Some(foreign_type),
            ..TypeNodeLinks::default()
        },
    ));
    assert!(!context.store_mut_for_test().set_symbol_node_links(
        nodes.name,
        SymbolNodeLinks {
            resolved_symbol: Some(foreign_wrapper.meta)
        },
    ));
    assert_eq!(observe(&context), before);
    let actual = warm(&mut context, nodes);
    assert_ne!(actual, foreign_type);
    let local_global = context.store().import_meta_global().unwrap().clone();
    let local_wrapper = context.store().import_meta_expression().unwrap();
    let before = observe(&context);
    assert!(
        context
            .store_mut_for_test()
            .set_import_meta_global(local_global)
    );
    assert!(
        context
            .store_mut_for_test()
            .set_import_meta_expression(local_wrapper)
    );
    assert!(
        !context
            .store_mut_for_test()
            .set_import_meta_expression(foreign_wrapper)
    );
    let mut conflicting = local_wrapper;
    conflicting.meta = global_symbol(&context, "Number");
    assert!(
        !context
            .store_mut_for_test()
            .set_import_meta_expression(conflicting)
    );
    assert_eq!(observe(&context), before);
}

#[test]
fn readonly_meta_wrapper_corruption_fails_and_restores_exact_identity() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    for change in ["readonly", "parent", "value", "table", "owner"] {
        let mut context = context(
            &library,
            &[(SOURCE_FILE, &source, None)],
            options(ModuleKind::EsNext),
        );
        let actual = warm(&mut context, nodes);
        let wrapper = context.store().import_meta_expression().unwrap();
        let original_value = context
            .store()
            .value_symbol_links(wrapper.meta)
            .cloned()
            .unwrap();
        let wrong_type = context.store().intrinsic_bootstrap().unwrap().number_type;
        let wrong_symbol = global_symbol(&context, "Number");
        let store = context.store_mut_for_test();
        match change {
            "readonly" => assert!(store.set_symbol_flags(
                wrapper.meta,
                SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
                CheckFlags::NONE,
            )),
            "parent" => {
                assert!(store.set_symbol_relationships(wrapper.meta, None, None, None, None));
            }
            "value" => assert!(store.set_value_symbol_links(
                wrapper.meta,
                ValueSymbolLinks {
                    resolved_type: Some(wrong_type),
                    ..ValueSymbolLinks::default()
                },
            )),
            "table" => assert_eq!(
                store.insert_symbol(wrapper.members, EscapedName::source("meta"), wrong_symbol),
                Some(Some(wrapper.meta)),
            ),
            "owner" => {
                assert!(store.set_symbol_relationships(wrapper.symbol, None, None, None, None));
            }
            _ => unreachable!(),
        }
        let before = observe(&context);
        for node in [nodes.name, nodes.expression] {
            assert_meta_error(
                &context.get_type_at_location(node),
                SourceMetaError::InvalidWrapper(wrapper.type_),
            );
            assert_meta_error(
                &context.get_symbol_at_location(node),
                SourceMetaError::InvalidWrapper(wrapper.type_),
            );
            assert_eq!(observe(&context), before, "change={change}");
        }
        let store = context.store_mut_for_test();
        assert!(store.set_symbol_flags(
            wrapper.meta,
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
            CheckFlags::READONLY,
        ));
        assert!(store.set_symbol_relationships(
            wrapper.meta,
            None,
            None,
            Some(wrapper.symbol),
            None
        ));
        assert!(store.set_symbol_relationships(
            wrapper.symbol,
            Some(wrapper.members),
            None,
            None,
            None
        ));
        assert!(store.set_value_symbol_links(wrapper.meta, original_value));
        assert!(
            store
                .insert_symbol(wrapper.members, EscapedName::source("meta"), wrapper.meta)
                .is_some()
        );
        assert_eq!(warm(&mut context, nodes), actual);
        assert_eq!(context.store().import_meta_expression(), Some(wrapper));
    }
}

#[test]
fn actual_global_declarations_are_checked_before_cold_and_warm_demands() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    for warm_first in [false, true] {
        for change in ["empty", "other_declaration", "flags"] {
            let mut context = context(
                &library,
                &[(SOURCE_FILE, &source, None)],
                options(ModuleKind::EsNext),
            );
            let actual = warm_first.then(|| warm(&mut context, nodes));
            let symbol = global_symbol(&context, "ImportMeta");
            let record = context.store().symbol(symbol).unwrap();
            let declarations = record.declarations().unwrap().to_vec();
            let value = record.value_declaration();
            let flags = record.flags();
            let check_flags = record.check_flags();
            let wrong = global_symbol(&context, "Number");
            let wrong_declarations = context
                .store()
                .symbol(wrong)
                .unwrap()
                .declarations()
                .unwrap()
                .to_vec();
            let store = context.store_mut_for_test();
            match change {
                "empty" => assert!(store.set_symbol_declarations(symbol, Some(Vec::new()), value)),
                "other_declaration" => {
                    assert!(store.set_symbol_declarations(symbol, Some(wrong_declarations), value));
                }
                "flags" => {
                    assert!(store.set_symbol_flags(symbol, SymbolFlags::TYPE_ALIAS, check_flags));
                }
                _ => unreachable!(),
            }
            let before = observe(&context);
            let expected = SourceMetaError::Global(
                CanonicalGlobalTypeInitializationError::InvalidSymbol(symbol),
            );
            assert_meta_error(&context.get_type_at_location(nodes.expression), expected);
            assert_eq!(
                observe(&context),
                before,
                "warm={warm_first}, change={change}"
            );
            assert_meta_error(&context.get_symbol_at_location(nodes.name), expected);
            assert_eq!(observe(&context), before);
            let store = context.store_mut_for_test();
            assert!(store.set_symbol_flags(symbol, flags, check_flags));
            assert!(store.set_symbol_declarations(symbol, Some(declarations), value));
            let restored = warm(&mut context, nodes);
            assert!(actual.is_none_or(|actual| actual == restored));
        }
    }
}

#[test]
fn a_same_program_wrong_declared_type_does_not_replace_import_meta() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    for warm_first in [false, true] {
        let mut context = context(
            &library,
            &[(SOURCE_FILE, &source, None)],
            options(ModuleKind::EsNext),
        );
        let actual = warm_first.then(|| warm(&mut context, nodes));
        let symbol = global_symbol(&context, "ImportMeta");
        let wrong_symbol = global_symbol(&context, "Number");
        let wrong_type = context
            .store()
            .declared_type_links(wrong_symbol)
            .unwrap()
            .declared_type
            .unwrap();
        let original = context
            .store()
            .declared_type_links(symbol)
            .cloned()
            .unwrap_or_default();
        let mut poisoned = original.clone();
        poisoned.declared_type = Some(wrong_type);
        assert!(
            context
                .store_mut_for_test()
                .set_declared_type_links(symbol, poisoned)
        );
        let before = observe(&context);
        let expected = CanonicalArtifactQueryError::SourceCheck(SourceCheckError::DeclaredType(
            DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::InvalidCachedDeclaredType {
                symbol,
                declared_type: wrong_type,
            }),
        ));
        assert_eq!(
            context.get_type_at_location(nodes.expression),
            Err(expected)
        );
        assert_eq!(observe(&context), before, "warm={warm_first}");
        assert_eq!(context.get_symbol_at_location(nodes.name), Err(expected));
        assert_eq!(observe(&context), before);
        assert!(
            context
                .store_mut_for_test()
                .set_declared_type_links(symbol, original)
        );
        let restored = warm(&mut context, nodes);
        assert!(actual.is_none_or(|actual| actual == restored));
    }
}

#[test]
fn registered_node_formats_are_required_without_filename_inference() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    for (format, expected) in [
        (None, SourceMetaError::MissingImpliedNodeFormat(SOURCE_FILE)),
        (
            Some(ModuleKind::Es2020),
            SourceMetaError::InvalidImpliedNodeFormat {
                file: SOURCE_FILE,
                format: ModuleKind::Es2020,
            },
        ),
    ] {
        let mut context = context(
            &library,
            &[(SOURCE_FILE, &source, format)],
            options(ModuleKind::NodeNext),
        );
        let before = observe(&context);
        assert_meta_error(&context.get_type_at_location(nodes.expression), expected);
        assert_meta_error(&context.get_symbol_at_location(nodes.name), expected);
        assert_eq!(observe(&context), before);
        assert!(context.store().import_meta_global().is_none());
    }
    for format in [ModuleKind::CommonJs, ModuleKind::EsNext] {
        let mut context = context(
            &library,
            &[(SOURCE_FILE, &source, Some(format))],
            options(ModuleKind::NodeNext),
        );
        let actual = warm(&mut context, nodes);
        assert_eq!(
            context.store().type_payload(actual).unwrap().symbol(),
            Some(global_symbol(&context, "ImportMeta"))
        );
        let codes = context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|record| record.diagnostic.code())
            .collect::<Vec<_>>();
        assert_eq!(
            codes,
            if format == ModuleKind::CommonJs {
                vec![1470]
            } else {
                Vec::new()
            }
        );
    }
}

#[test]
fn caller_module_options_are_checked_again_before_execution() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    {
        let configured = options(ModuleKind::EsNext);
        let mut context = context(&library, &[(SOURCE_FILE, &source, None)], configured);
        let library_bound = context.file(LIBRARY_FILE).unwrap().1.clone();
        let source_bound = context.file(SOURCE_FILE).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
            ],
            GlobalMergeCompletion::for_test(configured.name_resolution),
        )
        .unwrap();
        let plan = plan_import_meta_property(context.store(), &host, nodes.expression, configured)
            .unwrap();
        let before = observe(&context);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            check_import_meta_property(
                context.store_mut_for_test(),
                &host,
                &plan,
                options(ModuleKind::CommonJs),
                &mut diagnostics
            ),
            Err(SourceMetaError::InvalidPlan(nodes.expression)),
        );
        assert_eq!(observe(&context), before);
        assert!(diagnostics.is_empty());
        let restored = check_import_meta_property(
            context.store_mut_for_test(),
            &host,
            &plan,
            configured,
            &mut diagnostics,
        )
        .unwrap();
        assert_eq!(warm(&mut context, nodes), restored);
        assert!(diagnostics.is_empty());
    }

    for (target, expected_code) in [
        (ScriptTarget::Es2015, Some(1343)),
        (ScriptTarget::Es2021, None),
    ] {
        let mut configured = options(ModuleKind::None);
        configured.name_resolution.emit_target = target;
        let mut separate = context(&library, &[(SOURCE_FILE, &source, None)], configured);
        let actual = warm(&mut separate, nodes);
        assert_eq!(
            separate.store().type_payload(actual).unwrap().symbol(),
            Some(global_symbol(&separate, "ImportMeta"))
        );
        assert_eq!(
            separate
                .diagnostics()
                .as_slice()
                .iter()
                .map(|record| record.diagnostic.code())
                .collect::<Vec<_>>(),
            expected_code.into_iter().collect::<Vec<_>>(),
        );
    }
}

#[test]
fn invariant_global_errors_do_not_publish_module_diagnostics() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    for configured in [options(ModuleKind::EsNext), options(ModuleKind::CommonJs)] {
        let mut context = context(&library, &[(SOURCE_FILE, &source, None)], configured);
        let library_bound = context.file(LIBRARY_FILE).unwrap().1.clone();
        let source_bound = context.file(SOURCE_FILE).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
            ],
            GlobalMergeCompletion::for_test(configured.name_resolution),
        )
        .unwrap();
        let plan = plan_import_meta_property(context.store(), &host, nodes.expression, configured)
            .unwrap();
        let symbol = global_symbol(&context, "ImportMeta");
        let flags = context.store().symbol(symbol).unwrap().flags();
        let check_flags = context.store().symbol(symbol).unwrap().check_flags();
        assert!(context.store_mut_for_test().set_symbol_flags(
            symbol,
            SymbolFlags::TYPE_ALIAS,
            check_flags
        ));
        let before = observe(&context);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            check_import_meta_property(
                context.store_mut_for_test(),
                &host,
                &plan,
                configured,
                &mut diagnostics
            ),
            Err(SourceMetaError::Global(
                CanonicalGlobalTypeInitializationError::InvalidSymbol(symbol)
            )),
        );
        assert_eq!(observe(&context), before);
        assert!(
            diagnostics.is_empty(),
            "mode={:?}, diagnostics={diagnostics:?}",
            configured.module_kind
        );
        assert!(
            context
                .store_mut_for_test()
                .set_symbol_flags(symbol, flags, check_flags)
        );
        check_import_meta_property(
            context.store_mut_for_test(),
            &host,
            &plan,
            configured,
            &mut diagnostics,
        )
        .unwrap();
        let expected = if configured.module_kind == ModuleKind::CommonJs {
            vec![1343]
        } else {
            Vec::new()
        };
        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|record| record.diagnostic.code())
                .collect::<Vec<_>>(),
            expected
        );
    }
}

#[test]
fn scanned_source_name_cannot_be_replaced_by_a_rebound_identifier() {
    let library = parsed(LIBRARY);
    let mut source = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    let original = source.arena.get(nodes.name.node).unwrap().clone();
    let NodeData::Identifier(name) = &mut source.arena.get_mut(nodes.name.node).unwrap().data
    else {
        unreachable!();
    };
    name.text = "data".to_owned();
    {
        let mut context = context(
            &library,
            &[(SOURCE_FILE, &source, None)],
            options(ModuleKind::EsNext),
        );
        let before = observe(&context);
        assert_meta_error(
            &context.get_type_at_location(nodes.expression),
            SourceMetaError::InvalidNode(nodes.expression),
        );
        assert_eq!(observe(&context), before);
    }
    *source.arena.get_mut(nodes.name.node).unwrap() = original;
    let mut restored = context(
        &library,
        &[(SOURCE_FILE, &source, None)],
        options(ModuleKind::EsNext),
    );
    warm(&mut restored, nodes);
    assert!(restored.diagnostics().is_empty());
}

#[test]
fn a_source_without_import_meta_does_not_demand_its_missing_global() {
    let library = parsed(&replaced_library(""));
    let source = parsed("export {}; const value = 1;");
    let mut context = context(
        &library,
        &[(SOURCE_FILE, &source, None)],
        options(ModuleKind::EsNext),
    );
    context.check_source_file(SOURCE_FILE).unwrap();
    assert!(context.store().import_meta_global().is_none());
    assert!(context.store().import_meta_expression().is_none());
    assert!(context.global_type_diagnostics().next().is_none());
    assert!(context.diagnostics().is_empty());
}

#[test]
fn a_real_global_augmentation_requires_the_complete_merged_declaration_set() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let augmentation =
        parsed("export {}; declare global { interface ImportMeta { readonly marker: string; } }");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    for warm_first in [false, true] {
        let mut context = context(
            &library,
            &[
                (SOURCE_FILE, &source, None),
                (SECOND_FILE, &augmentation, None),
            ],
            options(ModuleKind::EsNext),
        );
        let symbol = global_symbol(&context, "ImportMeta");
        let record = context.store().symbol(symbol).unwrap();
        let declarations = record.declarations().unwrap().to_vec();
        let value = record.value_declaration();
        assert_eq!(declarations.len(), 2);
        assert!(declarations.iter().any(|node| node.file == LIBRARY_FILE));
        assert!(declarations.iter().any(|node| node.file == SECOND_FILE));
        let actual = warm_first.then(|| warm(&mut context, nodes));
        assert!(context.store_mut_for_test().set_symbol_declarations(
            symbol,
            Some(vec![declarations[0]]),
            value,
        ));
        let before = observe(&context);
        let expected = SourceMetaError::Global(
            CanonicalGlobalTypeInitializationError::InvalidSymbol(symbol),
        );
        assert_meta_error(&context.get_type_at_location(nodes.expression), expected);
        assert_meta_error(&context.get_symbol_at_location(nodes.name), expected);
        assert_eq!(observe(&context), before);
        assert!(context.store_mut_for_test().set_symbol_declarations(
            symbol,
            Some(declarations),
            value
        ));
        let restored = warm(&mut context, nodes);
        assert!(actual.is_none_or(|actual| actual == restored));
        assert_eq!(
            context.store().type_payload(restored).unwrap().symbol(),
            Some(symbol)
        );
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn populated_node_format_is_validated_outside_node_module_modes() {
    let library = parsed(LIBRARY);
    let source = parsed("import.meta;");
    let nodes = meta_nodes(&source, SOURCE_FILE);
    for module in [ModuleKind::CommonJs, ModuleKind::System, ModuleKind::EsNext] {
        let mut context = context(
            &library,
            &[(SOURCE_FILE, &source, Some(ModuleKind::Es2020))],
            options(module),
        );
        let before = observe(&context);
        let expected = SourceMetaError::InvalidImpliedNodeFormat {
            file: SOURCE_FILE,
            format: ModuleKind::Es2020,
        };
        assert_meta_error(&context.get_type_at_location(nodes.expression), expected);
        assert_meta_error(&context.get_symbol_at_location(nodes.name), expected);
        assert_eq!(observe(&context), before);
    }
    for format in [ModuleKind::CommonJs, ModuleKind::EsNext] {
        let mut context = context(
            &library,
            &[(SOURCE_FILE, &source, Some(format))],
            options(ModuleKind::EsNext),
        );
        let actual = warm(&mut context, nodes);
        context.recheck_source_file(SOURCE_FILE).unwrap();
        assert_eq!(warm(&mut context, nodes), actual);
        assert!(context.diagnostics().is_empty());
    }
}
