//! Port-only test of `handle_file_delete` (Go `programtosnapshot.go:162
//! handleFileDelete`).
//!
//! PORT: Go stops at the first gone file of a random-order `SyncMap`, so
//! Go takes the global branch with chance (gone global files) / (gone
//! files) and has no stable test for it. The port takes Go's more likely
//! answer, and the global branch on a tie (the PORT comment of
//! `handle_file_delete`). These tests fix those answers.

use ts_goport::execute::tsc::ExitStatus;

use crate::support::child::run_command_in_child;
use crate::support::runner::TscInput;
use crate::support::test_sys::{TSC_LIB_PATH, TestSys, new_test_sys};

const PROJECT: &str = "/home/src/workspaces/project";

/// The tsconfig with `lib` set to `lib`.
fn config(lib: &str) -> String {
    format!(r#"{{"compilerOptions":{{"incremental":true,"lib":["{lib}"]}},"files":["a.ts"]}}"#)
}

/// `tsc -p tsconfig.json --pretty false` in a command child.
fn build(sys: &TestSys) -> ExitStatus {
    build_with(sys, &[])
}

/// `tsc -p tsconfig.json --pretty false` and `extra` in a command child.
fn build_with(sys: &TestSys, extra: &[&str]) -> ExitStatus {
    let mut args = ["-p", "tsconfig.json", "--pretty", "false"]
        .map(String::from)
        .to_vec();
    args.extend(extra.iter().map(|arg| arg.to_string()));
    let result = run_command_in_child(sys, &args).unwrap_or_else(|err| panic!("tsgo: {err}"));
    assert!(result.unported.is_none(), "unported {:?}", result.unported);
    result.status
}

// `lib` goes from es2016 to es2015. Two lib files leave the program:
// `lib.es2016.d.ts` (only `/// <reference lib>` lines, so it does not
// affect global scope) and then `lib.es2016.array.include.d.ts` (a global
// declaration). `lib` does not affect semantic diagnostics, so only the
// gone global file makes the program check `a.ts` again.
#[test]
fn lib_change_rechecks_when_a_later_gone_file_affects_global_scope() {
    let es2016 = format!("{TSC_LIB_PATH}/lib.es2016.d.ts");
    let include = format!("{TSC_LIB_PATH}/lib.es2016.array.include.d.ts");
    let input = TscInput {
        files: [
            (
                format!("{PROJECT}/a.ts"),
                "const x: number = fromInclude;\n".into(),
            ),
            (format!("{PROJECT}/tsconfig.json"), config("es2016").into()),
            (
                es2016,
                "/// <reference lib=\"es2015\" />\n/// <reference lib=\"es2016.array.include\" />\n"
                    .into(),
            ),
            (include, "declare const fromInclude: number;\n".into()),
        ]
        .into_iter()
        .collect(),
        ..Default::default()
    };
    let sys = new_test_sys(&input, false);
    let fs = sys.fs_from_file_map();

    assert_eq!(build(&sys), ExitStatus::Success, "{}", sys.output_text());

    // The non-global gone file comes first in the build info, so a walk
    // that stops at the first gone file would keep the old diagnostics.
    let (build_info, ok) = fs.read_file(&format!("{PROJECT}/tsconfig.tsbuildinfo"));
    assert!(ok, "no build info");
    let start = build_info.find(r#""fileNames":["#).expect("fileNames");
    let file_names = &build_info[start..start + build_info[start..].find(']').expect("]")];
    let position = |name: &str| {
        file_names
            .find(&format!("\"{name}\""))
            .unwrap_or_else(|| panic!("{name} not in {file_names}"))
    };
    assert!(position("lib.es2016.d.ts") < position("lib.es2016.array.include.d.ts"));

    fs.write_file(&format!("{PROJECT}/tsconfig.json"), &config("es2015"))
        .expect("write tsconfig.json");
    sys.clear_output();
    let status = build(&sys);
    let output = sys.output_text();
    assert_eq!(
        status,
        ExitStatus::DiagnosticsPresentOutputsGenerated,
        "{output}"
    );
    assert!(
        output.contains("error TS2304: Cannot find name 'fromInclude'."),
        "{output}"
    );
}

// realworld3 docusaurus (incremental rebuild after a dependency change):
// three files leave the program and only `g.d.ts` affects global scope.
// Go meets a module file first in 2 of 3 runs (pin 673a5f17d713: 134 of
// 200), takes the branch that only rewrites the build info, and does not
// emit the unchanged `a.ts` again. The global branch re-emits every file
// (docusaurus: 855 unchanged JS files where Go writes 3).
#[test]
fn gone_files_mostly_modules_do_not_change_all_files() {
    let source = |name: &str| format!("{PROJECT}/src/{name}");
    let input = TscInput {
        files: [
            (
                format!("{PROJECT}/tsconfig.json"),
                r#"{"compilerOptions":{"incremental":true,"rootDir":"src","outDir":"out"},"include":["src"]}"#
                    .into(),
            ),
            (source("a.ts"), "export const a = 1;\n".into()),
            (source("g.d.ts"), "declare const g: number;\n".into()),
            (source("m1.d.ts"), "export declare const m1: number;\n".into()),
            (source("m2.d.ts"), "export declare const m2: number;\n".into()),
        ]
        .into_iter()
        .collect(),
        ..Default::default()
    };
    let sys = new_test_sys(&input, false);
    let fs = sys.fs_from_file_map();

    let status = build_with(&sys, &["--listEmittedFiles"]);
    let output = sys.output_text();
    assert_eq!(status, ExitStatus::Success, "{output}");
    assert!(
        output.contains(&format!("TSFILE: {PROJECT}/out/a.js")),
        "{output}"
    );

    for name in ["g.d.ts", "m1.d.ts", "m2.d.ts"] {
        fs.remove(&source(name))
            .unwrap_or_else(|err| panic!("remove {name}: {err:?}"));
    }
    sys.clear_output();
    let status = build_with(&sys, &["--listEmittedFiles"]);
    let output = sys.output_text();
    assert_eq!(status, ExitStatus::Success, "{output}");
    assert!(
        !output.contains(&format!("TSFILE: {PROJECT}/out/a.js")),
        "{output}"
    );
    assert!(
        output.contains(&format!("TSFILE: {PROJECT}/tsconfig.tsbuildinfo")),
        "{output}"
    );
}
