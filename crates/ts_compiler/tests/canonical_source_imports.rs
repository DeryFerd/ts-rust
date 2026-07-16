use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn canonical_program_checks_importer_first_array_values_through_bundler_manifest() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/importer.ts",
        concat!(
            "import { values } from './target'; ",
            "const copy: string[] = values; ",
            "const bad: number = values;",
        ),
    )
    .unwrap();
    fs.write_file(
        "/project/target.ts",
        "export const values: string[] = ['value'];",
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["importer.ts".to_owned()],
        CompilerOptions {
            module: ModuleKind::EsNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::Bundler,
            lib: Some(vec!["es5".to_owned()]),
            ..CompilerOptions::default()
        },
    )
    .unwrap();

    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| (
                diagnostic.file_name.as_deref(),
                diagnostic.code,
                diagnostic.message.as_str(),
            ))
            .collect::<Vec<_>>(),
        [(
            Some("/project/importer.ts"),
            Some(2322),
            "Type 'string[]' is not assignable to type 'number'.",
        )]
    );
}
