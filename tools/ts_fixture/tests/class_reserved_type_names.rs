use std::{env, path::PathBuf};

use ts_compiler::Program;
use ts_fixture::{RunnerOptions, run_upstream_diagnostic_baselines};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn program(source: &str, declaration: bool) -> Program {
    let file = if declaration {
        "input.d.ts"
    } else {
        "input.ts"
    };
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(&format!("/project/{file}"), source)
        .unwrap();
    Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &[file.to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2015,
            module: ModuleKind::EsNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::Bundler,
            lib: Some(vec!["es5".to_owned()]),
            no_emit: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"))
}

fn assert_reserved_name(source: &str, raw_name: &str, decoded: &str, declaration: bool) {
    let program = program(source, declaration);
    let [diagnostic] = program.diagnostics() else {
        panic!("{source}: {:?}", program.diagnostics());
    };
    assert_eq!(diagnostic.code, Some(2414), "{source}");
    assert_eq!(
        diagnostic.message,
        format!("Class name cannot be '{decoded}'.")
    );
    let range = diagnostic.range.unwrap();
    assert_eq!(
        range.start.get() as usize,
        source.find(raw_name).unwrap(),
        "{source}"
    );
    assert_eq!(range.len() as usize, raw_name.len(), "{source}");
}

#[test]
fn original_class_declaration_24_matches_the_complete_diagnostic_baseline() {
    let Ok(repository) = env::var("TS_GO_REPO") else {
        return;
    };
    let mut output = Vec::new();
    let summary = run_upstream_diagnostic_baselines(
        &PathBuf::from(repository),
        &RunnerOptions {
            filter: Some(
                "_submodules/TypeScript/tests/cases/compiler/ClassDeclaration24.ts".to_owned(),
            ),
            diagnostics: true,
            canonical_checker: true,
            ..RunnerOptions::default()
        },
        &mut output,
    )
    .unwrap();
    assert_eq!(summary.selected_cases, 1);
    assert_eq!(summary.executed_variants, 1);
    assert_eq!(summary.matched, 1, "{}", String::from_utf8_lossy(&output));
    assert_eq!(summary.mismatched, 0);
    assert_eq!(summary.missing, 0);
}

#[test]
fn class_type_keywords_report_decoded_names_and_identifier_spans() {
    for name in [
        "any",
        "unknown",
        "never",
        "number",
        "bigint",
        "boolean",
        "string",
        "symbol",
        "object",
        "undefined",
    ] {
        assert_reserved_name(
            &format!("export {{}}; class {name} {{}}"),
            name,
            name,
            false,
        );
    }
    for (source, raw, decoded) in [
        ("class \\u0061ny {}", "\\u0061ny", "any"),
        (
            "/* \u{1f600} */ class \\u0073tring {}",
            "\\u0073tring",
            "string",
        ),
    ] {
        assert_reserved_name(source, raw, decoded, false);
    }
}

#[test]
fn reserved_class_names_cover_supported_declaration_forms() {
    for (source, declaration) in [
        ("class any {}", false),
        ("export class any {}", false),
        ("abstract class any {}", false),
        ("declare class any {}", true),
    ] {
        assert_reserved_name(source, "any", "any", declaration);
    }
}

#[test]
fn ordinary_class_names_remain_valid() {
    for source in ["class Any {}", "class anyValue {}", "class intrinsic {}"] {
        let program = program(source, false);
        assert!(
            program.diagnostics().is_empty(),
            "{source}: {:?}",
            program.diagnostics()
        );
    }
}

#[test]
fn reserved_class_name_does_not_replace_other_source_diagnostics() {
    let program = program("class any {} const value: number = 'bad';", false);
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .filter_map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [2414, 2322],
    );
}
