use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn options(module: ModuleKind) -> CompilerOptions {
    CompilerOptions {
        module,
        module_specified: true,
        target: ScriptTarget::Es2022,
        lib: Some(vec!["es5".to_owned()]),
        no_emit: true,
        ..CompilerOptions::default()
    }
}

fn meta_nodes(program: &Program, file: &str) -> Vec<(NodeRef, NodeRef)> {
    let source = program.source_file(file).unwrap();
    source
        .parse
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::MetaProperty(meta) = &record.data else {
                return None;
            };
            (meta.keyword_token == SyntaxKind::ImportKeyword).then(|| {
                (
                    source.node_ref(node).unwrap(),
                    source.node_ref(meta.name).unwrap(),
                )
            })
        })
        .collect()
}

#[test]
fn import_meta_uses_real_library_identity_and_one_wrapper_across_source_replay() {
    let fs = MemoryFileSystem::new(true);
    for file in ["first.ts", "second.ts"] {
        fs.write_file(&format!("/project/{file}"), "const value = import.meta;")
            .unwrap();
    }
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
        &fs,
        "/project",
        &["first.ts".to_owned(), "second.ts".to_owned()],
        options(ModuleKind::EsNext),
        |program, queries| {
            let first = meta_nodes(program, "/project/first.ts")[0];
            let second = meta_nodes(program, "/project/second.ts")[0];
            let property = queries.get_symbol_at_location(first.1).unwrap().unwrap();
            let type_ = queries.get_type_at_location(first.0).unwrap();
            let global = queries.get_symbol_at_location(first.0).unwrap().unwrap();
            assert_eq!(queries.type_to_string(type_).unwrap(), "ImportMeta");
            assert_eq!(queries.symbol_to_string(property).unwrap(), "meta");
            assert_ne!(property, global);
            assert!(
                queries
                    .get_symbol_declarations(property)
                    .unwrap()
                    .is_empty()
            );
            let declarations = queries.get_symbol_declarations(global).unwrap();
            assert!(!declarations.is_empty());
            assert!(declarations.iter().all(|declaration| {
                program
                    .source_file_by_id(declaration.file)
                    .unwrap()
                    .is_default_library
            }));

            for (expression, name) in [second, first] {
                assert_eq!(queries.get_type_at_location(name), Ok(type_));
                assert_eq!(queries.get_type_at_location(expression), Ok(type_));
                assert_eq!(queries.get_symbol_at_location(expression), Ok(Some(global)));
                assert_eq!(queries.get_symbol_at_location(name), Ok(Some(property)));
            }
            for file in ["/project/first.ts", "/project/second.ts"] {
                let source = program.source_file(file).unwrap();
                let root = source.node_ref(source.parse.source_file).unwrap();
                assert!(queries.get_symbol_at_location(root).unwrap().is_some());
            }
            let diagnostics = queries.cold_diagnostic_snapshot();
            assert!(diagnostics.is_empty());
            assert_eq!(queries.replay_sources().unwrap(), diagnostics);
            for (expression, name) in [first, second] {
                assert_eq!(queries.get_type_at_location(expression), Ok(type_));
                assert_eq!(queries.get_type_at_location(name), Ok(type_));
                assert_eq!(queries.get_symbol_at_location(expression), Ok(Some(global)));
                assert_eq!(queries.get_symbol_at_location(name), Ok(Some(property)));
            }
        },
    )
    .unwrap();
    assert_eq!(checked, Some(()));
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn import_meta_module_diagnostics_preserve_the_library_type() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/main.ts", "const value = import.meta;")
        .unwrap();
    for (module, code) in [
        (ModuleKind::CommonJs, Some(1343)),
        (ModuleKind::Amd, Some(1343)),
        (ModuleKind::Umd, Some(1343)),
        (ModuleKind::Es2015, Some(1343)),
        (ModuleKind::System, None),
        (ModuleKind::Es2020, None),
        (ModuleKind::Es2022, None),
        (ModuleKind::EsNext, None),
        (ModuleKind::Preserve, None),
    ] {
        let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            options(module),
            |program, queries| {
                let (expression, name) = meta_nodes(program, "/project/main.ts")[0];
                let type_ = queries.get_type_at_location(expression).unwrap();
                assert_eq!(queries.type_to_string(type_).unwrap(), "ImportMeta");
                assert_eq!(queries.get_type_at_location(name), Ok(type_));
                let diagnostics = queries.cold_diagnostic_snapshot();
                assert_eq!(queries.replay_sources().unwrap(), diagnostics);
                if let Some(code) = code {
                    let [diagnostic] = diagnostics.as_slice() else {
                        panic!("{module:?}: {diagnostics:?}");
                    };
                    assert_eq!(diagnostic.code, Some(code));
                    let range = diagnostic.range.unwrap();
                    let source = program.source_file("/project/main.ts").unwrap();
                    assert_eq!(
                        &source.source_text[range.start.get() as usize..range.end.get() as usize],
                        "import.meta"
                    );
                } else {
                    assert!(diagnostics.is_empty(), "{module:?}: {diagnostics:?}");
                }
            },
        )
        .unwrap_or_else(|error| panic!("{module:?}: {error:?}"));
        assert_eq!(checked, Some(()));
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            code.into_iter().map(Some).collect::<Vec<_>>(),
            "{module:?}"
        );
    }
}

#[test]
fn import_meta_derives_an_omitted_module_from_an_explicit_target() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/main.ts", "const value = import.meta;")
        .unwrap();
    for (target, code) in [
        (ScriptTarget::Es2015, Some(1343)),
        (ScriptTarget::Es2019, Some(1343)),
        (ScriptTarget::Es2020, None),
        (ScriptTarget::Es2021, None),
        (ScriptTarget::Es2022, None),
        (ScriptTarget::Es2025, None),
        (ScriptTarget::EsNext, None),
    ] {
        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                target,
                module_specified: false,
                ..options(ModuleKind::None)
            },
        )
        .unwrap_or_else(|error| panic!("{target:?}: {error:?}"));
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            code.into_iter().map(Some).collect::<Vec<_>>(),
            "{target:?}"
        );
    }
}

#[test]
fn import_meta_node_mode_uses_real_extension_and_package_format() {
    for (file, package_type, code) in [
        ("main.mts", None, None),
        ("main.cts", None, Some(1470)),
        ("main.ts", Some("module"), None),
        ("main.ts", Some("commonjs"), Some(1470)),
    ] {
        let fs = MemoryFileSystem::new(true);
        let path = format!("/project/{file}");
        fs.write_file(&path, "const value = import.meta;").unwrap();
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
                module_resolution: ModuleResolutionKind::NodeNext,
                ..options(ModuleKind::NodeNext)
            },
            |program, queries| {
                let (expression, name) = meta_nodes(program, &path)[0];
                let type_ = queries.get_type_at_location(expression).unwrap();
                assert_eq!(queries.type_to_string(type_).unwrap(), "ImportMeta");
                assert_eq!(queries.get_type_at_location(name), Ok(type_));
                let source = program.source_file(&path).unwrap();
                let root = source.node_ref(source.parse.source_file).unwrap();
                assert!(queries.get_symbol_at_location(root).unwrap().is_some());
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
            code.into_iter().map(Some).collect::<Vec<_>>(),
            "{file}, {package_type:?}"
        );
    }
}

#[test]
fn import_meta_reads_members_from_the_real_dom_global_augmentation() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        "const url: string = import.meta.url; const wrong: number = import.meta.url;",
    )
    .unwrap();
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        CompilerOptions {
            lib: Some(vec!["es5".to_owned(), "dom".to_owned()]),
            ..options(ModuleKind::EsNext)
        },
        |program, queries| {
            let nodes = meta_nodes(program, "/project/main.ts");
            let first = queries.get_type_at_location(nodes[0].0).unwrap();
            let second = queries.get_type_at_location(nodes[1].0).unwrap();
            assert_eq!(first, second);
            assert_eq!(queries.type_to_string(first).unwrap(), "ImportMeta");
            let symbol = queries.get_symbol_at_location(nodes[0].0).unwrap().unwrap();
            let declarations = queries.get_symbol_declarations(symbol).unwrap();
            assert_eq!(declarations.len(), 2);
            assert!(declarations.iter().any(|declaration| {
                program
                    .source_file_by_id(declaration.file)
                    .unwrap()
                    .file_name
                    .ends_with("lib.dom.d.ts")
            }));
            assert_eq!(
                queries.replay_sources().unwrap(),
                queries.cold_diagnostic_snapshot()
            );
        },
    )
    .unwrap();
    assert_eq!(checked, Some(()));
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [Some(2322)]
    );
}

#[test]
fn import_meta_missing_and_invalid_globals_keep_their_fallback_and_diagnostic() {
    for (declarations, code) in [
        ("", 2318),
        ("type ImportMeta = number;", 2316),
        ("interface ImportMeta<T> {}", 2317),
    ] {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/globals.d.ts", declarations)
            .unwrap();
        fs.write_file("/project/main.ts", "const value = import.meta;")
            .unwrap();
        let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["globals.d.ts".to_owned(), "main.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                lib: None,
                ..options(ModuleKind::EsNext)
            },
            |program, queries| {
                let (expression, name) = meta_nodes(program, "/project/main.ts")[0];
                let type_ = queries.get_type_at_location(expression).unwrap();
                assert_eq!(queries.type_to_string(type_).unwrap(), "{}");
                assert_eq!(queries.get_type_at_location(name), Ok(type_));
                assert_eq!(queries.get_symbol_at_location(expression), Ok(None));
                let property = queries.get_symbol_at_location(name).unwrap().unwrap();
                let diagnostics = queries.cold_diagnostic_snapshot();
                let import_meta = diagnostics
                    .iter()
                    .filter(|diagnostic| diagnostic.message.contains("'ImportMeta'"))
                    .collect::<Vec<_>>();
                assert_eq!(import_meta.len(), 1, "{declarations}: {diagnostics:?}");
                assert_eq!(import_meta[0].code, Some(code));
                if declarations.is_empty() {
                    assert!(import_meta[0].file_name.is_none());
                    assert!(import_meta[0].range.is_none());
                } else {
                    assert_eq!(
                        import_meta[0].file_name.as_deref(),
                        Some("/project/globals.d.ts")
                    );
                    let range = import_meta[0].range.unwrap();
                    assert_eq!(
                        &declarations[range.start.get() as usize..range.end.get() as usize],
                        "ImportMeta"
                    );
                }
                assert_eq!(queries.replay_sources().unwrap(), diagnostics);
                assert_eq!(queries.get_type_at_location(expression), Ok(type_));
                assert_eq!(queries.get_symbol_at_location(name), Ok(Some(property)));
            },
        )
        .unwrap_or_else(|error| panic!("{declarations}: {error:?}"));
        assert_eq!(checked, Some(()));
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.message.contains("'ImportMeta'"))
                .count(),
            1
        );
    }
}

#[test]
fn import_meta_javascript_diagnostics_follow_check_js() {
    for check_js in [false, true] {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.js", "const value = import.meta;")
            .unwrap();
        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["main.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js,
                ..options(ModuleKind::CommonJs)
            },
        )
        .unwrap();
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            if check_js {
                vec![Some(1343)]
            } else {
                Vec::new()
            }
        );
    }
}

#[test]
fn import_meta_omitted_target_and_module_uses_shared_defaults() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/main.ts", "const value = import.meta;")
        .unwrap();
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        CompilerOptions {
            lib: Some(vec!["es5".to_owned()]),
            no_emit: true,
            ..CompilerOptions::default()
        },
        |program, queries| {
            let (expression, _) = meta_nodes(program, "/project/main.ts")[0];
            let type_ = queries.get_type_at_location(expression).unwrap();
            assert_eq!(queries.type_to_string(type_).unwrap(), "ImportMeta");
            assert_eq!(
                queries.replay_sources().unwrap(),
                queries.cold_diagnostic_snapshot()
            );
        },
    )
    .unwrap();
    assert_eq!(checked, Some(()));
    // Pinned Go uses its latest standard target when both options are omitted.
    // Keep this assertion until the shared default implementation matches it.
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn import_meta_config_defaults_keep_explicit_modules_and_raw_inputs() {
    for (configured, module, code) in [
        (None, ModuleKind::None, None),
        (Some("commonjs"), ModuleKind::CommonJs, Some(1343)),
        (Some("es2015"), ModuleKind::Es2015, Some(1343)),
        (Some("system"), ModuleKind::System, None),
        (Some("esnext"), ModuleKind::EsNext, None),
    ] {
        let fs = MemoryFileSystem::new(true);
        let source_text = "const value = import.meta;";
        fs.write_file("/project/main.ts", source_text).unwrap();
        let mut config = serde_json::json!({
            "files": ["main.ts"],
            "compilerOptions": {"lib": ["es5"], "noEmit": true},
        });
        if let Some(module) = configured {
            config["compilerOptions"]["module"] = serde_json::json!(module);
        }
        assert!(config["compilerOptions"].get("target").is_none());
        assert_eq!(
            config["compilerOptions"].get("module").is_some(),
            configured.is_some()
        );
        let config_text = config.to_string();
        fs.write_file("/project/tsconfig.json", &config_text)
            .unwrap();
        let (program, checked) = Program::try_from_config_with_canonical_checker_and_queries(
            &fs,
            "/project/tsconfig.json",
            |program, queries| {
                assert_eq!(program.options().target, ScriptTarget::Es2025);
                assert_eq!(program.options().module, module);
                assert_eq!(program.options().module_specified, configured.is_some());
                assert!(!program.options().no_check);
                let (expression, name) = meta_nodes(program, "/project/main.ts")[0];
                let type_ = queries.get_type_at_location(expression).unwrap();
                assert_eq!(queries.type_to_string(type_).unwrap(), "ImportMeta");
                assert_eq!(queries.get_type_at_location(name), Ok(type_));
                assert_eq!(
                    queries.replay_sources().unwrap(),
                    queries.cold_diagnostic_snapshot()
                );
            },
        )
        .unwrap_or_else(|error| panic!("{configured:?}: {error:?}"));
        assert_eq!(checked, Some(()), "{configured:?}");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            code.into_iter().map(Some).collect::<Vec<_>>(),
            "{configured:?}"
        );
        let graph = program.project_graph_snapshot();
        assert_eq!(
            graph.config.as_ref().unwrap().source_text.as_deref(),
            Some(config_text.as_str())
        );
        assert_eq!(fs.read_file("/project/tsconfig.json").unwrap(), config_text);
        assert_eq!(fs.read_file("/project/main.ts").unwrap(), source_text);
    }
}
