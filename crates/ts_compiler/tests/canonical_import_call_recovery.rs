use ts_ast::{NodeData, SyntaxKind};
use ts_checker::semantic::CanonicalModuleResolutionLookup;
use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn options(module: ModuleKind) -> CompilerOptions {
    CompilerOptions {
        module,
        module_specified: true,
        module_resolution: match module {
            ModuleKind::Node16 | ModuleKind::Node18 | ModuleKind::Node20 => {
                ModuleResolutionKind::Node16
            }
            ModuleKind::NodeNext => ModuleResolutionKind::NodeNext,
            ModuleKind::Preserve => ModuleResolutionKind::Bundler,
            _ => ModuleResolutionKind::Node10,
        },
        target: ScriptTarget::Es2015,
        lib: Some(vec!["es6".to_owned()]),
        skip_lib_check: true,
        no_emit: true,
        ..CompilerOptions::default()
    }
}

fn check_recovery(text: &str, options: CompilerOptions) -> Program {
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file("/project/main.ts", text).unwrap();
    filesystem
        .write_file("/project/foo.ts", "export const value = 1;")
        .unwrap();
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["main.ts".to_owned()],
        options,
        |program, queries| {
            let source = program.source_file("/project/main.ts").unwrap();
            assert!(program.source_file("/project/foo.ts").is_none());
            let (node, call) = source
                .parse
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::CallExpression(call) = &record.data else {
                        return None;
                    };
                    ts_ast::is_import_call(&source.parse.arena, record)
                        .then_some((source.node_ref(node).unwrap(), call))
                })
                .unwrap();
            let specifier = source.node_ref(call.arguments.nodes[0]).unwrap();
            let lookup = queries.module_resolution(specifier);
            let symbol = queries.get_symbol_at_location(specifier).unwrap();
            if source.parse.arena.get(specifier.node).unwrap().kind == SyntaxKind::StringLiteral {
                assert_eq!(lookup, CanonicalModuleResolutionLookup::Unresolved);
                assert_eq!(symbol, None);
            } else {
                assert_eq!(lookup, CanonicalModuleResolutionLookup::EntryAbsent);
                let NodeData::Identifier(identifier) = &program.node(specifier).unwrap().data
                else {
                    panic!("expected an identifier specifier")
                };
                if identifier.text != "missing" {
                    assert!(
                        symbol.is_some(),
                        "the identifier keeps its declaration symbol"
                    );
                }
                if let Some(symbol) = symbol {
                    let declarations = queries.get_symbol_declarations(symbol).unwrap();
                    assert!(!declarations.is_empty());
                    assert!(declarations.iter().all(|declaration| {
                        program.node(*declaration).unwrap().kind == SyntaxKind::VariableDeclaration
                    }));
                }
            }
            let type_ = queries.get_type_at_location(node).unwrap();
            assert_eq!(queries.type_to_string(type_).unwrap(), "Promise<any>");
            assert_eq!(queries.intrinsic_any_name(type_).unwrap(), None);
            assert_eq!(queries.get_symbol_at_location(node).unwrap(), None);
            let specifier_type = queries.get_type_at_location(specifier).unwrap();
            let cold = queries.cold_diagnostic_snapshot();
            for _ in 0..2 {
                assert_eq!(queries.replay_sources().unwrap(), cold);
                assert_eq!(queries.get_type_at_location(node).unwrap(), type_);
                assert_eq!(
                    queries.get_type_at_location(specifier).unwrap(),
                    specifier_type
                );
                assert_eq!(queries.get_symbol_at_location(specifier).unwrap(), symbol);
                assert_eq!(queries.module_resolution(specifier), lookup);
            }
        },
    )
    .unwrap();
    checked.expect("canonical checker ran");
    program
}

#[test]
fn unresolved_import_in_default_export_preserves_ts2307_and_promise_any() {
    let text = concat!(
        "export default {\n",
        "    getInstance: function () {\n",
        "        return import('./foo2');\n",
        "    }\n",
        "}",
    );
    let program = check_recovery(text, options(ModuleKind::CommonJs));
    let [diagnostic] = program.diagnostics() else {
        panic!("{:?}", program.diagnostics())
    };
    assert_eq!(diagnostic.code, Some(2307));
    assert_eq!(diagnostic.file_name.as_deref(), Some("/project/main.ts"));
    assert_eq!(
        diagnostic.message,
        "Cannot find module './foo2' or its corresponding type declarations."
    );
    let range = diagnostic.range.unwrap();
    assert_eq!(
        &text[range.start.get() as usize..range.end.get() as usize],
        "'./foo2'"
    );
}

#[test]
fn import_trailing_comma_preserves_the_identifier_and_exact_comma_range() {
    for text in [
        "const path = './foo';\nimport(path,);",
        "const path = './foo';\nimport(path /* before */, /* after */\n);",
    ] {
        let program = check_recovery(text, options(ModuleKind::CommonJs));
        let [diagnostic] = program.diagnostics() else {
            panic!("{:?}", program.diagnostics())
        };
        assert_eq!(diagnostic.code, Some(1009));
        assert_eq!(diagnostic.message, "Trailing comma not allowed.");
        let range = diagnostic.range.unwrap();
        assert_eq!(
            &text[range.start.get() as usize..range.end.get() as usize],
            ","
        );
    }
}

#[test]
fn import_comma_grammar_obeys_module_modes_and_earlier_grammar_errors() {
    for module in [
        ModuleKind::CommonJs,
        ModuleKind::Amd,
        ModuleKind::System,
        ModuleKind::Umd,
        ModuleKind::Es2015,
        ModuleKind::Es2020,
        ModuleKind::Es2022,
        ModuleKind::Node16,
        ModuleKind::Node18,
        ModuleKind::Node20,
        ModuleKind::NodeNext,
        ModuleKind::EsNext,
        ModuleKind::Preserve,
    ] {
        for deferred in [false, true] {
            let expression = if deferred { "import.defer" } else { "import" };
            let text = format!("const path = './foo';\n{expression}(path,);");
            let program = check_recovery(&text, options(module));
            let expected =
                if deferred && !matches!(module, ModuleKind::EsNext | ModuleKind::Preserve) {
                    Some(18060)
                } else if !deferred && module == ModuleKind::Es2015 {
                    Some(1323)
                } else if matches!(
                    module,
                    ModuleKind::CommonJs
                        | ModuleKind::Amd
                        | ModuleKind::System
                        | ModuleKind::Umd
                        | ModuleKind::Es2020
                        | ModuleKind::Es2022
                ) {
                    Some(1009)
                } else {
                    None
                };
            assert_eq!(
                program
                    .diagnostics()
                    .iter()
                    .map(|diagnostic| diagnostic.code)
                    .collect::<Vec<_>>(),
                expected.into_iter().map(Some).collect::<Vec<_>>(),
                "{module:?} {expression}"
            );
        }
    }
}

#[test]
fn import_recovery_retains_specifier_and_body_type_errors() {
    let text = "const path = 42;\nimport(path,);\nconst wrong: string = 1;";
    let program = check_recovery(text, options(ModuleKind::CommonJs));
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [Some(7036), Some(1009), Some(2322)]
    );
    assert_eq!(
        program.diagnostics()[0].message,
        "Dynamic import's specifier must be of type 'string', but here has type '42'."
    );
    let program = check_recovery(
        "function load() { const wrong: string = 1; return import('./foo2'); }",
        options(ModuleKind::CommonJs),
    );
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [Some(2322), Some(2307)]
    );
}

#[test]
fn import_recovery_retains_uninitialized_and_missing_identifier_errors() {
    let mut strict = options(ModuleKind::CommonJs);
    strict.strict = true;
    let program = check_recovery("let path: string;\nimport(path,);", strict);
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [Some(2454), Some(1009)]
    );
    let program = check_recovery("import(missing,);", options(ModuleKind::CommonJs));
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [Some(2304), Some(1009)]
    );
}

#[test]
fn resolved_import_with_comma_keeps_the_real_target_and_target_errors() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/main.ts", "import('./a',);")
        .unwrap();
    filesystem
        .write_file("/project/a.ts", "export const wrong: string = 1;")
        .unwrap();
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["main.ts".to_owned()],
        options(ModuleKind::CommonJs),
        |program, queries| {
            let source = program.source_file("/project/main.ts").unwrap();
            let target = program.source_file("/project/a.ts").unwrap();
            let (node, call) = source
                .parse
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::CallExpression(call) = &record.data else {
                        return None;
                    };
                    ts_ast::is_import_call(&source.parse.arena, record)
                        .then_some((source.node_ref(node).unwrap(), call))
                })
                .unwrap();
            let specifier = source.node_ref(call.arguments.nodes[0]).unwrap();
            let CanonicalModuleResolutionLookup::Resolved(resolution) =
                queries.module_resolution(specifier)
            else {
                panic!("the target must remain resolved")
            };
            assert_eq!(resolution.target_file(), target.id);
            assert_eq!(
                queries.get_symbol_at_location(specifier).unwrap(),
                Some(resolution.target_symbol())
            );
            let type_ = queries.get_type_at_location(node).unwrap();
            assert_eq!(queries.intrinsic_any_name(type_).unwrap(), None);
            let cold = queries.cold_diagnostic_snapshot();
            assert_eq!(queries.replay_sources().unwrap(), cold);
            assert_eq!(queries.get_type_at_location(node).unwrap(), type_);
        },
    )
    .unwrap();
    checked.expect("canonical checker ran");
    let mut codes = program
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect::<Vec<_>>();
    codes.sort_unstable();
    assert_eq!(codes, [Some(1009), Some(2322)]);
}
