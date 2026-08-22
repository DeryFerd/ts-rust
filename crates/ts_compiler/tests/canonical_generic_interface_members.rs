use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn canonical_program_checks_generic_interface_members_and_assignability() {
    let filesystem = MemoryFileSystem::new(true);
    let source = concat!(
        "interface Box<T> { value: T; readonly label: string; }\n",
        "declare const text: Box<string>;\n",
        "const value: string = text.value;\n",
        "const label: string = text.label;\n",
        "const wrong: Box<number> = text;\n",
    );
    filesystem.write_file("/project/input.ts", source).unwrap();

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        CompilerOptions {
            module: ModuleKind::EsNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::Bundler,
            lib: Some(vec!["es5".to_owned()]),
            ..CompilerOptions::default()
        },
    )
    .unwrap();

    let [diagnostic] = program.diagnostics() else {
        panic!(
            "expected one generic assignment error: {:?}",
            program.diagnostics()
        );
    };
    assert_eq!(diagnostic.code, Some(2322));
    assert_eq!(diagnostic.file_name.as_deref(), Some("/project/input.ts"));
    let wrong_start = u32::try_from(source.find("wrong").unwrap()).unwrap();
    let range = diagnostic.range.expect("assignment diagnostic range");
    assert_eq!(
        (range.start.get(), range.end.get()),
        (wrong_start, wrong_start + 5)
    );
    assert!(
        diagnostic
            .message
            .starts_with("Type 'Box<string>' is not assignable to type 'Box<number>'"),
        "{}",
        diagnostic.message
    );
}
