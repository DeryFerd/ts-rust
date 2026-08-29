use std::collections::BTreeSet;

use ts_ast::{NodeArena, NodeData, NodeFlags, NodeId, SyntaxKind};
use ts_binder::CanonicalBinder;
use ts_options::{
    CompilerOptions, ModuleDetectionKind, ModuleKind, ModuleResolutionKind, ScriptTarget,
};
use ts_parser::parse_source_file;
use ts_vfs::{FileSystem, MemoryFileSystem};

use super::{Program, ProgramChecker, canonical_source_file_facts, source_file_is_external_module};

fn options() -> CompilerOptions {
    CompilerOptions {
        module: ModuleKind::EsNext,
        module_specified: true,
        target: ScriptTarget::Es2022,
        lib: Some(vec!["es5".to_owned()]),
        no_emit: true,
        ..CompilerOptions::default()
    }
}

fn descendants(arena: &NodeArena, root: NodeId) -> BTreeSet<NodeId> {
    let mut reached = BTreeSet::new();
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        if reached.insert(node) {
            arena
                .get(node)
                .unwrap()
                .for_each_child(|child| pending.push(child));
        }
    }
    reached
}

#[test]
fn ordinary_and_import_meta_sources_retain_canonical_scope() {
    for detection in [ModuleDetectionKind::Auto, ModuleDetectionKind::Legacy] {
        for (text, external) in [
            ("const value = 1;", false),
            ("export {}; const value = 1;", true),
            ("const value = import.meta;", true),
            ("export {}; const value = import.meta;", true),
            ("import './other'; const value = import.meta;", true),
            ("function value(): ImportMeta { return import.meta; }", true),
            (
                "declare function take(meta: ImportMeta): ImportMeta; const value = take(import.meta);",
                true,
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/main.ts", text).unwrap();
            fs.write_file("/project/other.ts", "export {};").unwrap();
            let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
                &fs,
                "/project",
                &["main.ts".to_owned()],
                CompilerOptions {
                    module_detection: detection,
                    ..options()
                },
                |program, queries| {
                    let source = program.source_file("/project/main.ts").unwrap();
                    let (_, bound) = queries.context.file(source.id).unwrap();
                    let facts = bound.source_facts().unwrap();
                    assert!(bound.declarations_complete());
                    assert_eq!(facts.is_external_module(), external, "{text}");
                    assert!(!facts.is_common_js_module(), "{text}");
                    assert_eq!(facts.implied_node_format(), Some(ModuleKind::CommonJs));
                    assert_eq!(bound.symbol(bound.source_file()).is_some(), external);
                    let value = queries
                        .context
                        .store()
                        .symbol_table(bound.locals(bound.source_file()).unwrap())
                        .unwrap()
                        .get_source("value")
                        .unwrap();
                    let global = queries
                        .context
                        .store()
                        .symbol_table(queries.context.globals())
                        .unwrap()
                        .get_source("value");
                    assert_eq!(global, (!external).then_some(value), "{text}");
                    for (node, record) in source.parse.arena.iter() {
                        if record.kind == SyntaxKind::MetaProperty {
                            let type_ = queries
                                .get_type_at_location(source.node_ref(node).unwrap())
                                .unwrap();
                            assert_eq!(queries.type_to_string(type_).unwrap(), "ImportMeta");
                        }
                    }
                    assert!(queries.cold_diagnostic_snapshot().is_empty());
                    assert!(queries.replay_sources().unwrap().is_empty());
                },
            )
            .unwrap_or_else(|error| panic!("{detection:?}: {text}: {error:?}"));
            assert_eq!(checked, Some(()));
            assert!(
                program.diagnostics().is_empty(),
                "{text}: {:?}",
                program.diagnostics()
            );
        }
    }
}

#[test]
fn import_meta_node_next_facts_follow_package_type_and_fixed_suffix() {
    for (file, package_type, format, code) in [
        ("main.ts", Some("module"), ModuleKind::EsNext, None),
        (
            "main.ts",
            Some("commonjs"),
            ModuleKind::CommonJs,
            Some(1470),
        ),
        ("main.ts", None, ModuleKind::CommonJs, Some(1470)),
        ("main.mts", Some("commonjs"), ModuleKind::EsNext, None),
        ("main.cts", Some("module"), ModuleKind::CommonJs, Some(1470)),
    ] {
        let fs = MemoryFileSystem::new(true);
        let path = format!("/project/{file}");
        let text = "const value = import.meta;";
        fs.write_file(&path, text).unwrap();
        if let Some(package_type) = package_type {
            fs.write_file(
                "/project/package.json",
                &format!(r#"{{"type":"{package_type}"}}"#),
            )
            .unwrap();
        }
        let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &[file.to_owned()],
            CompilerOptions {
                module: ModuleKind::NodeNext,
                module_resolution: ModuleResolutionKind::NodeNext,
                ..options()
            },
            |program, queries| {
                let source = program.source_file(&path).unwrap();
                let (_, bound) = queries.context.file(source.id).unwrap();
                let facts = bound.source_facts().unwrap();
                assert_eq!(source.implied_node_format, format);
                assert_eq!(facts.implied_node_format(), Some(format));
                assert!(facts.is_external_module());
                assert!(!facts.is_common_js_module());
                assert!(bound.symbol(bound.source_file()).is_some());
                assert!(
                    queries
                        .context
                        .store()
                        .symbol_table(queries.context.globals())
                        .unwrap()
                        .get_source("value")
                        .is_none()
                );
                let meta = source
                    .parse
                    .arena
                    .iter()
                    .find_map(|(id, record)| {
                        (record.kind == SyntaxKind::MetaProperty).then_some(id)
                    })
                    .unwrap();
                let type_ = queries
                    .get_type_at_location(source.node_ref(meta).unwrap())
                    .unwrap();
                assert_eq!(queries.type_to_string(type_).unwrap(), "ImportMeta");
                assert_eq!(
                    queries.replay_sources().unwrap(),
                    queries.cold_diagnostic_snapshot()
                );
            },
        )
        .unwrap_or_else(|error| panic!("{file}, {package_type:?}: {error:?}"));
        assert_eq!(checked, Some(()));
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            code.into_iter().map(Some).collect::<Vec<_>>()
        );
        if code.is_some() {
            let [diagnostic] = program.diagnostics() else {
                panic!("expected TS1470")
            };
            assert_eq!(
                diagnostic.message,
                "The 'import.meta' meta-property is not allowed in files which will build into CommonJS output."
            );
            let range = diagnostic.range.unwrap();
            assert_eq!(
                &text[range.start.get() as usize..range.end.get() as usize],
                "import.meta"
            );
        }
    }
}

#[test]
fn syntactic_module_indicators_suppress_commonjs_but_forced_modules_do_not() {
    for detection in [
        ModuleDetectionKind::Legacy,
        ModuleDetectionKind::Auto,
        ModuleDetectionKind::Force,
    ] {
        for (text, syntactic) in [
            ("const value = 1; module.exports = value;", false),
            ("const value = import.meta; module.exports = value;", true),
            ("export {}; const value = 1; module.exports = value;", true),
            (
                "import './other'; const value = 1; module.exports = value;",
                true,
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/main.js", text).unwrap();
            fs.write_file("/project/other.js", "export {};").unwrap();
            let program = Program::new_unchecked_with_options_and_checker(
                &fs,
                "/project",
                &["main.js".to_owned()],
                CompilerOptions {
                    allow_js: true,
                    check_js: true,
                    no_check: true,
                    no_lib: true,
                    lib: None,
                    module_detection: detection,
                    ..options()
                },
                ProgramChecker::Canonical,
            );
            let source = program.source_file("/project/main.js").unwrap();
            let facts = canonical_source_file_facts(source, program.options()).unwrap();
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &source.parse.arena,
                    source.parse.source_file,
                    source.id,
                    facts,
                )
                .unwrap();
            binder
                .bind_javascript_declaration_slice(&source.parse.arena, source.id)
                .unwrap();
            let bound = binder.file(source.id).unwrap();
            let facts = bound.source_facts().unwrap();
            assert!(bound.declarations_complete());
            assert_eq!(
                facts.is_external_module(),
                syntactic || detection == ModuleDetectionKind::Force,
                "{text}"
            );
            assert_eq!(facts.is_common_js_module(), !syntactic, "{text}");
            assert_eq!(facts.implied_node_format(), Some(ModuleKind::CommonJs));
            assert!(bound.symbol(bound.source_file()).is_some());
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep parsed JSDoc owners and bound module facts together.
fn import_meta_jsdoc_nodes_do_not_set_bound_module_facts() {
    #[derive(Clone, Copy, Debug)]
    enum Annotation {
        Typedef,
        Return,
        Parameter,
        Detached,
    }

    for (text, location) in [
        (
            "/** @typedef {{ [import.meta]: number }} Shape */\nconst value = 0;",
            Annotation::Typedef,
        ),
        (
            "/** @template T @param {T} x @returns {{ [import.meta]: number }} */\nconst f = x => x;",
            Annotation::Return,
        ),
        (
            "/** @template T @param {{ [import.meta]: number }} x @returns {T} */\nconst f = x => x;",
            Annotation::Parameter,
        ),
        (
            "/** @template T @param {{ [import.meta]: number }} x @returns {T broken} */\nconst f = x => x;",
            Annotation::Detached,
        ),
    ] {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.js", text).unwrap();
        let program = Program::new_unchecked_with_options_and_checker(
            &fs,
            "/project",
            &["main.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                no_check: true,
                no_lib: true,
                lib: None,
                module_detection: ModuleDetectionKind::Legacy,
                ..options()
            },
            ProgramChecker::Canonical,
        );
        let source = program.source_file("/project/main.js").unwrap();
        let parse = &source.parse;
        let arena = &parse.arena;
        assert!(
            parse.diagnostics.is_empty(),
            "{location:?}: {:?}",
            parse.diagnostics
        );
        let meta = arena
            .iter()
            .find_map(|(node, record)| (record.kind == SyntaxKind::MetaProperty).then_some(node))
            .unwrap();
        let reachable = descendants(arena, parse.source_file);
        assert_eq!(
            reachable.contains(&meta),
            !matches!(location, Annotation::Detached)
        );
        match location {
            Annotation::Typedef => {
                let (alias, record) = arena
                    .iter()
                    .find(|(_, record)| record.kind == SyntaxKind::JsTypeAliasDeclaration)
                    .unwrap();
                assert_eq!(record.flags, NodeFlags::REPARSED);
                assert!(reachable.contains(&alias));
                assert!(descendants(arena, alias).contains(&meta));
            }
            Annotation::Return | Annotation::Parameter | Annotation::Detached => {
                let (arrow, function) = arena
                    .iter()
                    .find_map(|(id, record)| {
                        if let NodeData::ArrowFunction(function) = &record.data {
                            Some((id, function))
                        } else {
                            None
                        }
                    })
                    .unwrap();
                let parameter_id = function.parameters.nodes[0];
                let NodeData::ParameterDeclaration(parameter) =
                    &arena.get(parameter_id).unwrap().data
                else {
                    panic!("expected an arrow parameter")
                };
                if matches!(location, Annotation::Detached) {
                    assert!(function.type_.is_none());
                    assert!(function.type_parameters.is_none());
                    assert!(parameter.type_.is_none());
                    assert!(
                        arena
                            .iter()
                            .any(|(id, record)| record.kind == SyntaxKind::TypeLiteral
                                && record.parent.is_none()
                                && descendants(arena, id).contains(&meta))
                    );
                } else {
                    let (root, parent) = if matches!(location, Annotation::Return) {
                        (function.type_.unwrap(), arrow)
                    } else {
                        (parameter.type_.unwrap(), parameter_id)
                    };
                    let record = arena.get(root).unwrap();
                    assert_eq!(record.kind, SyntaxKind::TypeLiteral);
                    assert_eq!(record.flags, NodeFlags::REPARSED);
                    assert_eq!(record.parent, Some(parent));
                    assert!(descendants(arena, root).contains(&meta));
                }
            }
        }
        assert!(!ts_ast::source_file_contains_import_meta(
            arena,
            parse.source_file
        ));
        assert!(!source_file_is_external_module(parse));
        let facts = canonical_source_file_facts(source, program.options()).unwrap();
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(arena, parse.source_file, source.id, facts)
            .unwrap();
        let bound = binder.file(source.id).unwrap();
        assert!(
            !bound
                .source_facts()
                .unwrap()
                .is_external_or_common_js_module()
        );
        assert_eq!(
            bound.contains(source.node_ref(meta).unwrap()),
            !matches!(location, Annotation::Detached)
        );
    }
}

#[test]
fn import_meta_detector_keeps_real_type_syntax_and_reparsed_runtime_nodes() {
    let parsed = parse_source_file("type Shape = { [import.meta]: number };");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert!(source_file_is_external_module(&parsed));

    let mut parsed = parse_source_file("import.meta;");
    let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected source root")
    };
    let statement = source.statements.nodes[0];
    parsed.arena.get_mut(statement).unwrap().flags = NodeFlags::REPARSED;
    assert!(source_file_is_external_module(&parsed));

    for text in [
        "/** @template T @param {T} x @returns {T} */\nconst f = x => import.meta;",
        "/** @template T @param {T} x @returns {T} */\nconst f = (x = import.meta) => x;",
    ] {
        let parsed = ts_parser::parse_javascript_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        assert!(source_file_is_external_module(&parsed), "{text}");
    }
}

#[test]
fn import_meta_detector_does_not_match_other_import_forms_or_new_target() {
    for text in [
        "const value = 'import.meta'; // import.meta",
        "import('pkg');",
        "import.defer('pkg');",
        "const value = import.defer;",
        "const value = import.other;",
        "function value() { return new.target; }",
    ] {
        let parsed = parse_source_file(text);
        assert!(!source_file_is_external_module(&parsed), "{text}");
    }
}

#[test]
fn import_meta_failure_classification_keeps_invariant_and_declared_errors_distinct() {
    use super::{CanonicalProgramCheckError, CanonicalProgramCheckFailureClass};
    use ts_checker::semantic::{
        CanonicalGlobalTypeInitializationError, DeclaredTypeError, SourceCheckError,
        SourceMetaError, TypeNodeUnavailable,
    };

    let parsed = parse_source_file("const value = import.meta;");
    let file = ts_ast::FileId::new(0);
    let node = ts_ast::NodeRef::new(parsed.arena.id(), file, parsed.source_file);
    let classify = |error: SourceMetaError| {
        CanonicalProgramCheckError::SourceCheck {
            file_name: "/project/main.ts".to_owned(),
            error: SourceCheckError::from(error),
        }
        .failure_class()
    };
    assert_eq!(
        classify(SourceMetaError::Unsupported(node)),
        CanonicalProgramCheckFailureClass::Unsupported {
            capability_code: "E00.SOURCE_SYNTAX"
        }
    );
    for error in [
        SourceMetaError::InvalidNode(node),
        SourceMetaError::InvalidPlan(node),
        SourceMetaError::MissingSourceFacts(file),
        SourceMetaError::MissingImpliedNodeFormat(file),
        SourceMetaError::InvalidImpliedNodeFormat {
            file,
            format: ModuleKind::System,
        },
        SourceMetaError::InvalidGlobalCache,
        SourceMetaError::InvalidTypeCache(node),
        SourceMetaError::InvalidSymbolCache(node),
        SourceMetaError::Global(CanonicalGlobalTypeInitializationError::MissingBootstrap),
    ] {
        assert_eq!(
            classify(error),
            CanonicalProgramCheckFailureClass::Fatal {
                invariant_code: "INV.SOURCE.META_PROPERTY",
            },
            "{error:?}"
        );
    }
    for (declared, expected) in [
        (
            DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::TypeArgumentsUnsupported(
                node,
            )),
            CanonicalProgramCheckFailureClass::Unsupported {
                capability_code: "T06.TYPE_NODE",
            },
        ),
        (
            DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::InvalidFunctionType(node)),
            CanonicalProgramCheckFailureClass::Fatal {
                invariant_code: "INV.SOURCE.DECLARED_TYPE",
            },
        ),
    ] {
        assert_eq!(classify(SourceMetaError::Declared(declared)), expected);
        assert_eq!(
            classify(SourceMetaError::Global(
                CanonicalGlobalTypeInitializationError::DeclaredType(declared)
            )),
            expected
        );
    }
}
