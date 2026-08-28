use ts_compiler::Program;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

// Original source unit after the fixture harness removes compiler directives.
const ORIGINAL: &str = "// repro from https://github.com/microsoft/TypeScript/issues/54420

declare const array1: [...number[], number]
const el1: number = array1[0]

declare const array2: [...number[], number]
const el2: number = array2[1]

declare const array3: [number, ...number[], number]
const el3: number = array3[1]

declare const array4: [number, ...number[], number]
const el4: number = array4[2]
";

#[derive(Debug, PartialEq)]
struct ObservedDiagnostic {
    code: u32,
    start: usize,
    text: String,
    message: String,
}

fn check(source: &str, strict: bool, unchecked: bool) -> Vec<ObservedDiagnostic> {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/indexedAccessWithVariableElement.ts", source)
        .unwrap();
    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["indexedAccessWithVariableElement.ts".to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2015,
            strict,
            strict_null_checks: strict,
            no_unchecked_indexed_access: unchecked,
            no_emit: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    program
        .diagnostics()
        .iter()
        .map(|diagnostic| {
            let range = diagnostic.range.unwrap();
            ObservedDiagnostic {
                code: diagnostic.code.unwrap(),
                start: range.start.get() as usize,
                text: source[range.start.get() as usize..range.end.get() as usize].to_owned(),
                message: diagnostic.message.clone(),
            }
        })
        .collect()
}

#[test]
fn original_variable_tuple_fixture_reports_only_the_two_unchecked_reads() {
    let diagnostics = check(ORIGINAL, true, true);
    let expected = ["el2", "el4"]
        .into_iter()
        .map(|name| ObservedDiagnostic {
            code: 2322,
            start: ORIGINAL.find(name).unwrap(),
            text: name.to_owned(),
            message: "Type 'number | undefined' is not assignable to type 'number'.\n  Type 'undefined' is not assignable to type 'number'.".to_owned(),
        })
        .collect::<Vec<_>>();
    assert_eq!(diagnostics, expected);
}

#[test]
fn variable_tuple_reads_only_add_undefined_when_both_options_are_enabled() {
    for (strict, unchecked) in [(true, false), (false, true), (false, false)] {
        let diagnostics = check(ORIGINAL, strict, unchecked);
        assert!(
            diagnostics.is_empty(),
            "strict={strict}, unchecked={unchecked}: {diagnostics:?}",
        );
    }
}

#[test]
fn rest_tuple_reads_keep_fixed_positions_and_union_the_variable_part() {
    let source = "
declare const leading: [...string[], number, boolean];
const leadingFirst: string | number | boolean = leading[0];
const leadingSecond: string | number | boolean = leading['1'];
const leadingMaybe: string | number | boolean | undefined = leading[2];
const leadingFar: string | number | boolean | undefined = leading[100];

declare const middle: [boolean, ...string[], number];
const middlePrefix: boolean = middle[0];
const middleKnown: string | number = middle[1];
const middleMaybe: string | number | undefined = middle[2];

declare const trailing: [number, ...string[]];
const trailingPrefix: number = trailing[0];
const trailingMaybe: string | undefined = trailing[1];
const trailingFar: string | undefined = trailing[100];

declare const fixed: [number, string];
const fixedKnown: string = fixed[1];
";
    assert!(check(source, true, true).is_empty());
}
