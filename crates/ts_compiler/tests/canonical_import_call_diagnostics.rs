use ts_ast::NodeData;
use ts_checker::semantic::{CanonicalModuleResolutionLookup, CanonicalModuleResolutionMode};
use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn check_call(options: CompilerOptions, deferred: bool, expected_code: Option<u32>) {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/a.ts", "export {};\n")
        .unwrap();
    let expression = if deferred {
        "import.defer('./a')"
    } else {
        "import('./a')"
    };
    filesystem
        .write_file(
            "/project/main.ts",
            &format!("export {{}};\n{expression};\n"),
        )
        .unwrap();
    let configured_module = options.module;
    let module_specified = options.module_specified;
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["main.ts".to_owned()],
        options,
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
                panic!("import call must retain its real module target")
            };
            assert_eq!(resolution.usage_mode(), CanonicalModuleResolutionMode::Esm);
            assert_eq!(resolution.target_file(), target.id);
            assert_eq!(
                queries
                    .get_symbol_declarations(resolution.target_symbol())
                    .unwrap(),
                &[target.node_ref(target.parse.source_file).unwrap()]
            );
            let type_ = queries.get_type_at_location(node).unwrap();
            assert_eq!(queries.intrinsic_any_name(type_).unwrap(), None);
            let cold = queries.cold_diagnostic_snapshot();
            assert_eq!(queries.replay_sources().unwrap(), cold);
            assert_eq!(queries.get_type_at_location(node).unwrap(), type_);
            assert_eq!(
                queries.get_symbol_at_location(specifier).unwrap(),
                Some(resolution.target_symbol())
            );
            program.node(node).unwrap().range
        },
    )
    .unwrap();
    let call_range = result.expect("canonical checker ran");
    assert_eq!(program.options().module, configured_module);
    assert_eq!(program.options().module_specified, module_specified);
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        expected_code.into_iter().map(Some).collect::<Vec<_>>()
    );
    if expected_code.is_some() {
        assert_eq!(program.diagnostics()[0].range, Some(call_range));
        assert_eq!(
            program.diagnostics()[0].file_name.as_deref(),
            Some("/project/main.ts")
        );
    }
}

#[test]
fn import_call_diagnostics_use_configured_module_modes_and_replay() {
    for module in [
        ModuleKind::CommonJs,
        ModuleKind::Es2015,
        ModuleKind::EsNext,
        ModuleKind::Preserve,
    ] {
        for deferred in [false, true] {
            let expected =
                if deferred && !matches!(module, ModuleKind::EsNext | ModuleKind::Preserve) {
                    Some(18060)
                } else if !deferred && module == ModuleKind::Es2015 {
                    Some(1323)
                } else {
                    None
                };
            check_call(
                CompilerOptions {
                    module,
                    module_specified: true,
                    module_resolution: if module == ModuleKind::Preserve {
                        ModuleResolutionKind::Bundler
                    } else {
                        ModuleResolutionKind::Node10
                    },
                    target: ScriptTarget::Es2025,
                    strict: true,
                    skip_lib_check: true,
                    no_emit: true,
                    ..CompilerOptions::default()
                },
                deferred,
                expected,
            );
        }
    }
}

#[test]
fn import_call_diagnostics_derive_only_the_omitted_global_module_mode() {
    for (target, deferred, expected) in [
        (ScriptTarget::Es2015, false, Some(1323)),
        (ScriptTarget::Es2015, true, Some(18060)),
        (ScriptTarget::EsNext, false, None),
        (ScriptTarget::EsNext, true, None),
        (ScriptTarget::Es2025, true, Some(18060)),
    ] {
        check_call(
            CompilerOptions {
                module: ModuleKind::None,
                module_specified: false,
                module_resolution: ModuleResolutionKind::Node10,
                target,
                strict: true,
                skip_lib_check: true,
                no_emit: true,
                ..CompilerOptions::default()
            },
            deferred,
            expected,
        );
    }
}
