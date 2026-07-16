use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

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

#[test]
#[allow(clippy::too_many_lines)]
fn canonical_program_emits_exact_ordered_generic_call_diagnostics() {
    const SOURCE: &str = concat!(
        "function pair<T, U>(left: T, right: U): U { return right; }\n",
        "function constrained<T extends string>(value: T): T { return value; }\n",
        "const empty = pair< /* empty */ >(\"left\", 1);\n",
        "const trailing = pair< string, number , /* trailing */ >(\"left\", 1);\n",
        "const trailingArity = pair< string , /* trailing arity */ >(\"left\", 1);\n",
        "const typeArity = pair<  string  >(\"left\", 1);\n",
        "const tooFew = pair<string, number>(\"left\");\n",
        "const tooMany = pair<string, number>(\"left\", 1, (\"extra\"), true);\n",
        "const badConstraint = constrained<number>(1);\n",
        "const badArgument = pair<string, number>(\"left\", ((\"bad\")));\n",
    );
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/input.ts", SOURCE).unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["input.ts".to_owned()],
        canonical_options(),
    )
    .unwrap();

    let diagnostics = program.diagnostics();
    assert_eq!(
        diagnostics
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
                Some(span_within(
                    SOURCE,
                    "pair< /* empty */ >(\"left\", 1)",
                    "< /* empty */ >",
                )),
                Some(1099),
                "Type argument list cannot be empty.",
            ),
            (
                Some("/project/input.ts"),
                Some(span_within(
                    SOURCE,
                    "number , /* trailing */",
                    ",",
                )),
                Some(1009),
                "Trailing comma not allowed.",
            ),
            (
                Some("/project/input.ts"),
                Some(span_within(
                    SOURCE,
                    "pair< string , /* trailing arity */ >(\"left\", 1)",
                    "string ,",
                )),
                Some(2558),
                "Expected 2 type arguments, but got 1.",
            ),
            (
                Some("/project/input.ts"),
                Some(span_within(
                    SOURCE,
                    "string , /* trailing arity */",
                    ",",
                )),
                Some(1009),
                "Trailing comma not allowed.",
            ),
            (
                Some("/project/input.ts"),
                Some(span_within(
                    SOURCE,
                    "pair<  string  >(\"left\", 1)",
                    "string",
                )),
                Some(2558),
                "Expected 2 type arguments, but got 1.",
            ),
            (
                Some("/project/input.ts"),
                Some(span_within(
                    SOURCE,
                    "pair<string, number>(\"left\")",
                    "pair",
                )),
                Some(2554),
                "Expected 2 arguments, but got 1.",
            ),
            (
                Some("/project/input.ts"),
                Some(span_within(
                    SOURCE,
                    "pair<string, number>(\"left\", 1, (\"extra\"), true)",
                    "(\"extra\"), true",
                )),
                Some(2554),
                "Expected 2 arguments, but got 4.",
            ),
            (
                Some("/project/input.ts"),
                Some(span_within(SOURCE, "constrained<number>(1)", "number")),
                Some(2344),
                "Type 'number' does not satisfy the constraint 'string'.",
            ),
            (
                Some("/project/input.ts"),
                Some(span_within(
                    SOURCE,
                    "pair<string, number>(\"left\", ((\"bad\")))",
                    "\"bad\"",
                )),
                Some(2345),
                "Argument of type 'string' is not assignable to parameter of type 'number'.",
            ),
        ]
    );
    assert!(diagnostics[..5]
        .iter()
        .all(|diagnostic| diagnostic.related_information.is_empty()));
    assert_eq!(diagnostics[5].related_information.len(), 1);
    let related = &diagnostics[5].related_information[0];
    assert_eq!(related.file_name.as_deref(), Some("/project/input.ts"));
    assert_eq!(
        related
            .range
            .map(|range| (range.start.get(), range.end.get())),
        Some(span_within(SOURCE, "left: T, right: U", "right: U"))
    );
    assert_eq!(related.code, Some(6210));
    assert_eq!(related.message, "An argument for 'right' was not provided.");
    assert!(related.related_information.is_empty());
}

#[test]
fn canonical_program_keeps_imported_missing_argument_related_information_cross_file() {
    const IMPORTER: &str = concat!(
        "import { pair } from './target';\n",
        "export const result = pair<string, number>(\"left\");\n",
    );
    const TARGET: &str =
        "export function pair<T, U>(left: T, right: U): U { return right; }\n";
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/importer.ts", IMPORTER).unwrap();
    fs.write_file("/project/target.ts", TARGET).unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["importer.ts".to_owned()],
        canonical_options(),
    )
    .unwrap();

    let [diagnostic] = program.diagnostics() else {
        panic!("expected one imported too-few diagnostic")
    };
    assert_eq!(diagnostic.file_name.as_deref(), Some("/project/importer.ts"));
    assert_eq!(
        diagnostic
            .range
            .map(|range| (range.start.get(), range.end.get())),
        Some(span_within(
            IMPORTER,
            "pair<string, number>(\"left\")",
            "pair",
        ))
    );
    assert_eq!(diagnostic.code, Some(2554));
    assert_eq!(diagnostic.message, "Expected 2 arguments, but got 1.");
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("expected one missing-parameter related diagnostic")
    };
    assert_eq!(related.file_name.as_deref(), Some("/project/target.ts"));
    assert_eq!(
        related
            .range
            .map(|range| (range.start.get(), range.end.get())),
        Some(span_within(TARGET, "left: T, right: U", "right: U"))
    );
    assert_eq!(related.code, Some(6210));
    assert_eq!(related.message, "An argument for 'right' was not provided.");
}
