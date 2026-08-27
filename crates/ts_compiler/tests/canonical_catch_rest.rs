use ts_ast::NodeData;
use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn canonical_catch_rest_option_matrix_preserves_intrinsic_identity_and_replay() {
    for strict in [false, true] {
        for unknown in [None, Some(false), Some(true)] {
            let filesystem = MemoryFileSystem::new(true);
            filesystem
                .write_file("/project/input.ts", "try {} catch ({ ...rest }) {}\n")
                .unwrap();
            let options = CompilerOptions {
                strict,
                use_unknown_in_catch_variables: unknown.unwrap_or(true),
                use_unknown_in_catch_variables_specified: unknown.is_some(),
                target: ScriptTarget::Es2017,
                module: ModuleKind::EsNext,
                module_specified: true,
                module_resolution: ModuleResolutionKind::Bundler,
                lib: Some(vec!["es5".to_owned()]),
                no_emit: true,
                ..CompilerOptions::default()
            };
            let effective = unknown.unwrap_or(strict);
            let (program, result) = Program::try_new_with_canonical_checker_and_queries(
                &filesystem,
                "/project",
                &["input.ts".to_owned()],
                options,
                |program, queries| {
                    let source = program.source_file("/project/input.ts").unwrap();
                    let (element, name) = source
                        .parse
                        .arena
                        .iter()
                        .find_map(|(node, record)| {
                            let NodeData::BindingElement(binding) = &record.data else {
                                return None;
                            };
                            Some((source.node_ref(node)?, source.node_ref(binding.name?)?))
                        })
                        .unwrap();
                    let cold = queries.cold_diagnostic_snapshot();
                    assert_eq!(cold.len(), usize::from(effective));
                    for diagnostic in &cold {
                        assert_eq!(diagnostic.code, Some(2700));
                        assert_eq!(diagnostic.range, Some(program.node(name).unwrap().range));
                        assert_eq!(
                            diagnostic.message,
                            "Rest types may only be created from object types.",
                        );
                    }
                    let type_ = queries.get_type_at_location(name).unwrap();
                    let intrinsic = queries.intrinsic_any_name(type_).unwrap().unwrap().to_owned();
                    assert_eq!(
                        intrinsic,
                        if effective { "error" } else { "any" },
                        "strict={strict} override={unknown:?}",
                    );
                    assert_eq!(queries.type_to_string(type_).unwrap(), "any");
                    let symbol = queries.get_symbol_at_location(name).unwrap().unwrap();
                    assert_eq!(queries.get_symbol_declarations(symbol).unwrap(), &[element]);
                    for _ in 0..2 {
                        for location in [element, name] {
                            assert_eq!(queries.get_type_at_location(location).unwrap(), type_);
                            assert_eq!(queries.get_symbol_at_location(location).unwrap(), Some(symbol));
                        }
                        assert_eq!(queries.replay_sources().unwrap(), cold);
                        assert_eq!(queries.cold_diagnostic_snapshot(), cold);
                        assert_eq!(queries.has_diagnostics(), effective);
                    }
                    eprintln!(
                        "strict={strict} override={unknown:?} effective={effective} intrinsic={intrinsic}",
                    );
                },
            )
            .unwrap();
            assert_eq!(result, Some(()));
            assert_eq!(program.diagnostics().len(), usize::from(effective));
            assert!(
                program
                    .diagnostics()
                    .iter()
                    .all(|diagnostic| diagnostic.code == Some(2700))
            );
        }
    }
}
