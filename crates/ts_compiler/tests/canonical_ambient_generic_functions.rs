use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn canonical_options() -> CompilerOptions {
    CompilerOptions {
        module: ModuleKind::EsNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::Bundler,
        lib: Some(vec!["es5".to_owned()]),
        strict: true,
        ..CompilerOptions::default()
    }
}

fn span_within(source: &str, container: &str, selected: &str) -> (u32, u32) {
    let container_start = source
        .find(container)
        .unwrap_or_else(|| panic!("missing source container {container:?}"));
    let selected_start = container
        .find(selected)
        .unwrap_or_else(|| panic!("missing {selected:?} in {container:?}"));
    let start = container_start + selected_start;
    (
        u32::try_from(start).unwrap(),
        u32::try_from(start + selected.len()).unwrap(),
    )
}

#[test]
fn canonical_program_checks_hoisted_generic_ambient_calls_and_defaults() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!(
            "export {};\n",
            "const before: string = dependent<string>(\"left\", \"right\");\n",
            "declare function identity<T>(value: T): T;\n",
            "const inferred: \"inferred\" = identity(\"inferred\");\n",
            "const explicit: string = identity<string>(\"explicit\");\n",
            "declare function dependent<T extends string, U extends T = T>(left: T, right: U): U;\n",
            "const after: number = identity(1);\n",
        ),
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        canonical_options(),
    )
    .unwrap();

    assert!(program.diagnostics().is_empty());
}

#[test]
fn canonical_program_matches_pinned_type_argument_arity_trivia_fixture() {
    // Pinned typescript-go:
    // `testdata/tests/cases/compiler/typeArgumentArityErrorSkipsTrivia.ts`.
    const SOURCE: &str = concat!(
        "declare function f<T>(a: T): T;\n",
        "\n",
        "f<   string, number>(\"a\");\n",
        "\n",
        "f<\n",
        "    string, number>(\"a\");\n",
    );
    const FILE_NAME: &str = "/project/typeArgumentArityErrorSkipsTrivia.ts";
    let fs = MemoryFileSystem::new(true);
    fs.write_file(FILE_NAME, SOURCE).unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["typeArgumentArityErrorSkipsTrivia.ts".to_owned()],
        canonical_options(),
    )
    .unwrap();

    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| (
                diagnostic.file_name.as_deref(),
                diagnostic
                    .range
                    .map(|range| (range.start.get(), range.end.get())),
                diagnostic.code,
                diagnostic.message.as_str(),
            ))
            .collect::<Vec<_>>(),
        [
            (
                Some(FILE_NAME),
                Some(span_within(
                    SOURCE,
                    "f<   string, number>(\"a\")",
                    "string, number",
                )),
                Some(2558),
                "Expected 1 type arguments, but got 2.",
            ),
            (
                Some(FILE_NAME),
                Some(span_within(
                    SOURCE,
                    "f<\n    string, number>(\"a\")",
                    "string, number",
                )),
                Some(2558),
                "Expected 1 type arguments, but got 2.",
            ),
        ]
    );
}
