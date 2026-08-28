use ts_compiler::Program;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

const ORIGINAL: &str = include_str!("fixtures/booleanAssignment.ts");

fn assignment_name_span(source: &str, assignment: &str) -> (u32, u32) {
    let start = u32::try_from(source.find(assignment).unwrap()).unwrap();
    (start, start + 1)
}

#[test]
fn original_boolean_assignment_preserves_wrapper_errors_and_accepted_primitives() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/booleanAssignment.ts", ORIGINAL)
        .unwrap();
    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["booleanAssignment.ts".to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2015,
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
                Some("/project/booleanAssignment.ts"),
                Some(assignment_name_span(ORIGINAL, "b = 1;")),
                Some(2322),
                "Type 'number' is not assignable to type 'Boolean'.",
            ),
            (
                Some("/project/booleanAssignment.ts"),
                Some(assignment_name_span(ORIGINAL, "b = \"a\";")),
                Some(2322),
                "Type 'string' is not assignable to type 'Boolean'.",
            ),
            (
                Some("/project/booleanAssignment.ts"),
                Some(assignment_name_span(ORIGINAL, "b = {};")),
                Some(2322),
                concat!(
                    "Type '{}' is not assignable to type 'Boolean'.\n",
                    "  The types returned by 'valueOf()' are incompatible between these types.\n",
                    "    Type 'Object' is not assignable to type 'boolean'.",
                ),
            ),
        ],
    );
}

#[test]
fn missing_declared_method_keeps_its_real_missing_property_diagnostic() {
    let source = concat!(
        "interface NeedsMethod { requiredMethod(): number; }\n",
        "const missing: NeedsMethod = {};\n",
    );
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/input.ts", source).unwrap();
    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["input.ts".to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2015,
            ..CompilerOptions::default()
        },
    )
    .unwrap();

    let [diagnostic] = program.diagnostics() else {
        panic!("expected one missing-method diagnostic");
    };
    assert_eq!(diagnostic.code, Some(2741));
    assert_eq!(
        diagnostic.message,
        "Property 'requiredMethod' is missing in type '{}' but required in type 'NeedsMethod'.",
    );
    let start = u32::try_from(source.find("missing").unwrap()).unwrap();
    assert_eq!(
        diagnostic
            .range
            .map(|range| (range.start.get(), range.end.get())),
        Some((start, start + 7)),
    );
}

#[test]
fn prototype_return_details_skip_compatible_void_methods() {
    let source = "const bad: { toString(): void; toLocaleString(): number } = {};\n";
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/input.ts", source).unwrap();
    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["input.ts".to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2015,
            ..CompilerOptions::default()
        },
    )
    .unwrap();

    let [diagnostic] = program.diagnostics() else {
        panic!("expected one prototype method diagnostic");
    };
    assert_eq!(diagnostic.code, Some(2322));
    assert_eq!(diagnostic.file_name.as_deref(), Some("/project/input.ts"));
    assert_eq!(
        diagnostic
            .range
            .map(|range| (range.start.get(), range.end.get())),
        Some((6, 9)),
    );
    assert_eq!(
        diagnostic.message.lines().skip(1).collect::<Vec<_>>(),
        [
            "  The types returned by 'toLocaleString()' are incompatible between these types.",
            "    Type 'string' is not assignable to type 'number'.",
        ],
    );
}
