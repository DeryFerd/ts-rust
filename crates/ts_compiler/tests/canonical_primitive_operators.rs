use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn span(source: &str, expected: &str) -> (u32, u32) {
    let start = source
        .find(expected)
        .unwrap_or_else(|| panic!("missing source span {expected:?}"));
    (
        u32::try_from(start).unwrap(),
        u32::try_from(start + expected.len()).unwrap(),
    )
}

#[test]
fn canonical_program_source_sorts_mixed_bigint_operator_diagnostics() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/input.ts", "export const mixed = 1n - \"c\";")
        .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
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
                Some("/project/input.ts"),
                Some((21, 29)),
                Some(2365),
                "Operator '-' cannot be applied to types 'bigint' and 'string'.",
            ),
            (
                Some("/project/input.ts"),
                Some((26, 29)),
                Some(2363),
                "The right-hand side of an arithmetic operation must be of type 'any', 'number', 'bigint' or an enum type.",
            ),
        ],
    );
}

#[test]
fn canonical_program_sorts_assignment_children_and_fixed_call_arguments() {
    const SOURCE: &str = concat!(
        "function pair(left: number, right: number): void {}\n",
        "var target: number = 0;\n",
        "target = (\"a\" - false) + true;\n",
        "const checked = pair((1 + true) - \"b\", (2n - 3) + true);\n",
    );
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/input.ts", SOURCE).unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
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
                Some("/project/input.ts"),
                Some(span(SOURCE, "(\"a\" - false) + true")),
                Some(2365),
                "Operator '+' cannot be applied to types 'number' and 'boolean'.",
            ),
            (
                Some("/project/input.ts"),
                Some(span(SOURCE, "\"a\"")),
                Some(2362),
                "The left-hand side of an arithmetic operation must be of type 'any', 'number', 'bigint' or an enum type.",
            ),
            (
                Some("/project/input.ts"),
                Some(span(SOURCE, "false")),
                Some(2363),
                "The right-hand side of an arithmetic operation must be of type 'any', 'number', 'bigint' or an enum type.",
            ),
            (
                Some("/project/input.ts"),
                Some(span(SOURCE, "1 + true")),
                Some(2365),
                "Operator '+' cannot be applied to types 'number' and 'boolean'.",
            ),
            (
                Some("/project/input.ts"),
                Some(span(SOURCE, "\"b\"")),
                Some(2363),
                "The right-hand side of an arithmetic operation must be of type 'any', 'number', 'bigint' or an enum type.",
            ),
            (
                Some("/project/input.ts"),
                Some(span(SOURCE, "2n - 3")),
                Some(2365),
                "Operator '-' cannot be applied to types 'bigint' and 'number'.",
            ),
        ],
    );
}
