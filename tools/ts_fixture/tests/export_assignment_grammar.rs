use std::{env, fs, path::Component};

use serde_json::json;
use ts_compiler::{CanonicalProgramCheckError, Program};
use ts_fixture::Case;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};
use xxhash_rust::xxh3::xxh3_128;

const MESSAGE: &str =
    "An export assignment cannot be used in a module with other exported elements.";

fn record_go_inputs(name: &str, case: &Case, roots: &[&str]) {
    let Some(directory) = env::var_os("TS_EXPORT_ASSIGNMENT_GO_INPUTS") else {
        return;
    };
    let directory = std::path::PathBuf::from(directory).join(name);
    fs::create_dir_all(&directory).unwrap();
    let mut units = Vec::new();
    for unit in &case.units {
        assert!(
            unit.path
                .components()
                .all(|component| matches!(component, Component::Normal(_)))
        );
        fs::write(directory.join(&unit.path), unit.source_text.as_bytes()).unwrap();
        units.push(json!({
            "path": unit.path,
            "byteCount": unit.source_text.as_bytes().len(),
            "xxh3": format!("{:032x}", xxh3_128(unit.source_text.as_bytes())),
        }));
    }
    fs::write(
        directory.join("inputs.json"),
        serde_json::to_vec_pretty(&json!({
            "name": name,
            "roots": roots,
            "arguments": ["--module", "commonjs", "--declaration"],
            "units": units,
        }))
        .unwrap(),
    )
    .unwrap();
}

fn checked(case: &Case, roots: &[&str]) -> Result<Program, CanonicalProgramCheckError> {
    let filesystem = MemoryFileSystem::new(true);
    for unit in &case.units {
        filesystem
            .write_file(
                &format!("/.src/{}", unit.path.display()),
                unit.source_text.as_scannable_str(),
            )
            .unwrap();
    }
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/.src",
        &roots
            .iter()
            .map(|root| (*root).to_owned())
            .collect::<Vec<_>>(),
        CompilerOptions {
            target: ScriptTarget::Es2025,
            module: ModuleKind::CommonJs,
            module_specified: true,
            module_resolution: ModuleResolutionKind::Node10,
            declaration: true,
            declaration_specified: true,
            ..CompilerOptions::default()
        },
        |_, queries| {
            let before = queries.cold_diagnostic_snapshot();
            assert_eq!(queries.replay_sources().unwrap(), before);
            assert_eq!(queries.replay_sources().unwrap(), before);
        },
    )?;
    checked.expect("canonical source checking ran");
    Ok(program)
}

fn diagnostic_spans(program: &Program) -> Vec<(u32, &str)> {
    program
        .diagnostics()
        .iter()
        .map(|diagnostic| {
            let source = program
                .source_file(diagnostic.file_name.as_deref().unwrap())
                .unwrap();
            let range = diagnostic.range.unwrap();
            let start = usize::try_from(range.start.get()).unwrap();
            let end = usize::try_from(range.end.get()).unwrap();
            if diagnostic.code == Some(2309) {
                assert_eq!(diagnostic.message, MESSAGE);
            }
            (diagnostic.code.unwrap(), &source.source_text[start..end])
        })
        .collect()
}

#[test]
fn export_assignment_merging4_keeps_the_exact_corpus_inputs_and_ts2309_range() {
    let source = include_str!("fixtures/export-assignment-grammar/exportAssignmentMerging4.ts");
    let case = Case::parse("exportAssignmentMerging4.ts", source).unwrap();
    assert_eq!(case.source_text.as_bytes().len(), 382);
    assert_eq!(case.units.len(), 2);
    assert_eq!(case.units[0].path.to_str(), Some("a.ts"));
    assert_eq!(case.units[1].path.to_str(), Some("b.ts"));
    for (unit, length, digest) in [
        (&case.units[0], 164, "a733dd29c272bf0d2001451f505920b9"),
        (&case.units[1], 121, "b79224631f4527bf729b36ddce9cb855"),
    ] {
        assert_eq!(unit.source_text.as_bytes().len(), length);
        assert_eq!(
            format!("{:032x}", xxh3_128(unit.source_text.as_bytes())),
            digest
        );
    }
    record_go_inputs("merging4", &case, &["b.ts"]);
    let program = checked(&case, &["b.ts"]).unwrap();
    assert_eq!(
        diagnostic_spans(&program),
        [(2309, "export = { a: 1, b: \"hello\" };")],
    );
    let diagnostic = &program.diagnostics()[0];
    assert_eq!(diagnostic.file_name.as_deref(), Some("/.src/a.ts"));
    let range = diagnostic.range.unwrap();
    assert_eq!((range.start.get(), range.end.get()), (134, 164));
}

#[test]
#[allow(clippy::too_many_lines)] // Keep each source and its expected grammar result together.
fn export_assignment_grammar_distinguishes_value_exports_and_type_merges() {
    // Checker units cover these bound modules before their source-admission limits.
    for (name, source) in [
        ("same-value", "export const value = 1; export = value;"),
        (
            "aliased-type",
            "const value = 1; type Other = number; export { Other }; export = value;",
        ),
        (
            "value-namespace",
            "export type Top = number; namespace value { export const member = 1; } export = value;",
        ),
        (
            "namespace-shadow",
            "export type Top = number; namespace value { export type Inner = string; export const member = 1; } export = value;",
        ),
        (
            "aliased-namespace-shadow",
            "type Top = number; export { Top }; namespace value { export type Inner = string; export const member = 1; } export = value;",
        ),
    ] {
        let case = Case::parse("input.ts", source).unwrap();
        record_go_inputs(name, &case, &["input.ts"]);
    }
    let mut failures = Vec::new();
    for (name, file, source, error) in [
        (
            "value-before",
            "input.ts",
            "const value = 1; export const other = 2; export = value;",
            true,
        ),
        (
            "value-after-tsx",
            "input.tsx",
            "/* \u{e9}\u{1f642} */\nconst value = 1; export = value; export const other = 2;",
            true,
        ),
        (
            "aliased-value",
            "input.ts",
            "const value = 1; const other = 2; export { other }; export = value;",
            true,
        ),
        (
            "explicit-type-alias",
            "input.ts",
            "const value = 1; type Other = number; export type { Other }; export = value;",
            false,
        ),
        (
            "object-type-merge",
            "input.ts",
            "export type Top = number; export namespace Types { export interface Item {} } export = { value: 1 };",
            false,
        ),
        (
            "runtime-value-namespace",
            "input.ts",
            "export type Top = number; namespace value { export var member = 1; } export = value;",
            false,
        ),
        (
            "runtime-namespace-shadow",
            "input.ts",
            "export type Top = number; namespace value { export type Inner = string; export var member = 1; } export = value;",
            true,
        ),
        (
            "ambient-value",
            "input.d.ts",
            "declare module 'pkg' { export const other: number; namespace value { export const member: number; } export = value; }",
            true,
        ),
        (
            "ambient-namespace",
            "input.d.ts",
            "declare module 'pkg' { namespace value { export const member: number; } export = value; }",
            false,
        ),
        (
            "default-export",
            "input.ts",
            "export const other = 1; export default { value: 1 };",
            false,
        ),
    ] {
        let case = Case::parse(file, source).unwrap();
        record_go_inputs(name, &case, &[file]);
        let expected = if error {
            vec![(2309, "export = value;")]
        } else {
            Vec::new()
        };
        match checked(&case, &[file]) {
            Ok(program) => {
                let observed = diagnostic_spans(&program);
                if observed != expected {
                    failures.push(format!("{name}: expected {expected:?}, got {observed:?}"));
                }
            }
            Err(error) => failures.push(format!("{name}: {error:?}")),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn export_assignment_grammar_orders_the_assignment_before_its_ambient_expression() {
    let case = Case::parse(
        "input.d.ts",
        "export const other: number;\nexport = 2 + 2;\n",
    )
    .unwrap();
    record_go_inputs("ambient-order", &case, &["input.d.ts"]);
    let program = checked(&case, &["input.d.ts"]).unwrap();
    assert_eq!(
        diagnostic_spans(&program),
        [(2309, "export = 2 + 2;"), (2714, "2 + 2")],
    );
}
