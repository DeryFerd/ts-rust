use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn canonical_commonjs_reserves_object_only_for_runtime_external_modules() {
    for (source, module, no_emit, expected_collision) in [
        (
            "let Object = 0;\nexport const x = 1;\n",
            ModuleKind::CommonJs,
            false,
            true,
        ),
        (
            "let Object = 0;\nexport const x = 1;\n",
            ModuleKind::EsNext,
            false,
            false,
        ),
        (
            "let Object = 0;\nexport const x = 1;\n",
            ModuleKind::CommonJs,
            true,
            false,
        ),
        ("let Object = 0;\n", ModuleKind::CommonJs, false, false),
        (
            "declare const Object: number;\nexport const x = 1;\n",
            ModuleKind::CommonJs,
            false,
            false,
        ),
    ] {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.ts", source).unwrap();
        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                module,
                module_specified: true,
                no_emit,
                no_lib: true,
                ..CompilerOptions::default()
            },
        )
        .unwrap_or_else(|error| {
            panic!("failed for {module:?}, noEmit={no_emit}, source {source:?}: {error:?}")
        });

        let collisions = program
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code == Some(2441))
            .collect::<Vec<_>>();
        if expected_collision {
            let [diagnostic] = collisions.as_slice() else {
                panic!(
                    "expected one CommonJS collision: {:?}",
                    program.diagnostics()
                );
            };
            assert_eq!(diagnostic.code, Some(2441));
            assert_eq!(diagnostic.file_name.as_deref(), Some("/project/input.ts"));
            let range = diagnostic.range.expect("collision name range");
            assert_eq!((range.start.get(), range.end.get()), (4, 10));
            assert_eq!(
                diagnostic.message,
                "Duplicate identifier 'Object'. Compiler reserves name 'Object' in top level scope of a module."
            );
        } else {
            assert!(
                collisions.is_empty(),
                "unexpected collisions for {module:?}, noEmit={no_emit}: {collisions:?}"
            );
        }
    }
}
