//! Rust port of `internal/execute/tsctests/tscbuild_test.go` lines 1-1913:
//! `TestBuildCommandLine` through `TestBuildOutputPaths`.
//!
//! Each Go test function is one `#[test]` that runs its non-watch inputs.
//! When a Go test function also has watch inputs (`-w`), a second `_watch`
//! test runs them. Inputs are built in the Go order.

use std::rc::Rc;

use ts_goport::frontend::tsoptions::{ParseConfigHost, get_parsed_command_line_of_config_file};
use ts_goport::frontend::vfs::Fs;
use ts_goport::options::CompilerOptions;

use crate::support::runner::{
    FileMap, TscEdit, TscInput, WatchFilter, edit, no_change, no_change_only_edit, run_tsc_inputs,
};
use crate::support::stringtestutil::{dedent, go_sprintf};
use crate::support::test_sys::{TSC_LIB_PATH, TestSys};
use crate::support::vfstest::{self, MapFile, symlink};

/// Go `FileMap{"path": value, ...}`. Each value goes through `MapFile::from`.
// PORT: a local macro with the same job as `support::runner::file_map!`,
// so this file does not depend on how that macro is exported.
macro_rules! files {
    ($($path:expr => $value:expr),* $(,)?) => {{
        #[allow(unused_mut)]
        let mut files = FileMap::new();
        $(files.insert(String::from($path), MapFile::from($value));)*
        files
    }};
}

/// Go `[]string{...}` for command line arguments.
fn args(list: &[&str]) -> Vec<String> {
    list.iter().map(std::string::ToString::to_string).collect()
}

/// Go `files[path].(string)`: the text of a file map entry.
fn file_text(files: &FileMap, path: &str) -> String {
    String::from_utf8(files[path].data.clone()).expect("file map entry is UTF-8 text")
}

// Go: tsctests/sys.go:37 tscDefaultLibContent
// PORT: the support contract does not export this value, so it is copied
// here from the pinned Go source.
fn tsc_default_lib_content() -> String {
    dedent(
        r#"
/// <reference no-default-lib="true"/>
interface Boolean {}
interface Function {}
interface CallableFunction {}
interface NewableFunction {}
interface IArguments {}
interface Number { toExponential: any; }
interface Object {}
interface RegExp {}
interface String { charAt: any; }
interface Array<T> { length: number; [n: number]: T; }
interface ReadonlyArray<T> {}
interface SymbolConstructor {
    (desc?: string | number): symbol;
    for(name: string): symbol;
    readonly toStringTag: symbol;
}
declare var Symbol: SymbolConstructor;
interface Symbol {
    readonly [Symbol.toStringTag]: string;
}
declare const console: { log(msg: any): void; };
"#,
    )
}

/// The `lib.d.ts` of `TestBuildJavascriptProjectEmit` and
/// `TestBuildModuleSpecifiers`: the default lib with `Symbol.species`.
// Go: tscbuild_test.go:1438 strings.Replace(tscDefaultLibContent, ...)
fn lib_with_symbol_species() -> String {
    tsc_default_lib_content().replacen(
        "interface SymbolConstructor {",
        "interface SymbolConstructor {\n    readonly species: symbol;",
        1,
    )
}

// ---------------------------------------------------------------------------
// TestBuildCommandLine
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:21 getBuildCommandLineDifferentOptionsMap
fn get_build_command_line_different_options_map(option_name: &str) -> FileMap {
    files! {
        "/home/src/workspaces/project/tsconfig.json" => dedent(&go_sprintf(r#"
			{
				"compilerOptions": {
					"%s": true
				}
			}"#, &[&option_name])),
        "/home/src/workspaces/project/a.ts" => "export const a = 10;const aLocal = 10;",
        "/home/src/workspaces/project/b.ts" => "export const b = 10;const bLocal = 10;",
        "/home/src/workspaces/project/c.ts" => r#"import { a } from "./a";export const c = a;"#,
        "/home/src/workspaces/project/d.ts" => r#"import { b } from "./b";export const d = b;"#,
    }
}

// Go: tscbuild_test.go:35 getBuildCommandLineEmitDeclarationOnlyMap
fn get_build_command_line_emit_declaration_only_map(options: &[&str]) -> FileMap {
    let compiler_options_str = options
        .iter()
        .map(|opt| go_sprintf(r#""%s": true"#, &[opt]))
        .collect::<Vec<_>>()
        .join(", ");
    files! {
        "/home/src/workspaces/solution/project1/src/tsconfig.json" => dedent(&go_sprintf(r#"
			{
				"compilerOptions": { %s }
			}"#, &[&compiler_options_str])),
        "/home/src/workspaces/solution/project1/src/a.ts" => "export const a = 10;const aLocal = 10;",
        "/home/src/workspaces/solution/project1/src/b.ts" => "export const b = 10;const bLocal = 10;",
        "/home/src/workspaces/solution/project1/src/c.ts" => r#"import { a } from "./a";export const c = a;"#,
        "/home/src/workspaces/solution/project1/src/d.ts" => r#"import { b } from "./b";export const d = b;"#,
        "/home/src/workspaces/solution/project2/src/tsconfig.json" => dedent(&go_sprintf(r#"
			{
				"compilerOptions": { %s },
				"references": [{ "path": "../../project1/src" }]
			}"#, &[&compiler_options_str])),
        "/home/src/workspaces/solution/project2/src/e.ts" => "export const e = 10;",
        "/home/src/workspaces/solution/project2/src/f.ts" => r#"import { a } from "../../project1/src/a"; export const f = a;"#,
        "/home/src/workspaces/solution/project2/src/g.ts" => r#"import { b } from "../../project1/src/b"; export const g = b;"#,
    }
}

// Go: tscbuild_test.go:58 getBuildCommandLineEmitDeclarationOnlyTestCases
fn get_build_command_line_emit_declaration_only_test_cases(
    options: &[&str],
    suffix: &str,
) -> Vec<TscInput> {
    vec![
        TscInput {
            sub_scenario: "emitDeclarationOnly on commandline".to_string() + suffix,
            files: get_build_command_line_emit_declaration_only_map(options),
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args(&["--b", "project2/src", "--verbose", "--emitDeclarationOnly"]),
            edits: vec![
                no_change(),
                TscEdit {
                    caption: "local change".into(),
                    edit: edit(|sys| {
                        sys.append_file(
                            "/home/src/workspaces/solution/project1/src/a.ts",
                            "const aa = 10;",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "non local change".into(),
                    edit: edit(|sys| {
                        sys.append_file(
                            "/home/src/workspaces/solution/project1/src/a.ts",
                            "export const aaa = 10;",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "emit js files".into(),
                    command_line_args: Some(args(&["--b", "project2/src", "--verbose"])),
                    ..Default::default()
                },
                no_change(),
                TscEdit {
                    caption: "js emit with change without emitDeclarationOnly".into(),
                    edit: edit(|sys| {
                        sys.append_file(
                            "/home/src/workspaces/solution/project1/src/b.ts",
                            "const alocal = 10;",
                        );
                    }),
                    command_line_args: Some(args(&["--b", "project2/src", "--verbose"])),
                    ..Default::default()
                },
                TscEdit {
                    caption: "local change".into(),
                    edit: edit(|sys| {
                        sys.append_file(
                            "/home/src/workspaces/solution/project1/src/b.ts",
                            "const aaaa = 10;",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "non local change".into(),
                    edit: edit(|sys| {
                        sys.append_file(
                            "/home/src/workspaces/solution/project1/src/b.ts",
                            "export const aaaaa = 10;",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "js emit with change without emitDeclarationOnly".into(),
                    edit: edit(|sys| {
                        sys.append_file(
                            "/home/src/workspaces/solution/project1/src/b.ts",
                            "export const a2 = 10;",
                        );
                    }),
                    command_line_args: Some(args(&["--b", "project2/src", "--verbose"])),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "emitDeclarationOnly false on commandline".to_string() + suffix,
            files: get_build_command_line_emit_declaration_only_map(
                &[options, &["emitDeclarationOnly"][..]].concat(),
            ),
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args(&["--b", "project2/src", "--verbose"]),
            edits: vec![
                no_change(),
                TscEdit {
                    caption: "change".into(),
                    edit: edit(|sys| {
                        sys.append_file(
                            "/home/src/workspaces/solution/project1/src/a.ts",
                            "const aa = 10;",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "emit js files".into(),
                    command_line_args: Some(args(&[
                        "--b",
                        "project2/src",
                        "--verbose",
                        "--emitDeclarationOnly",
                        "false",
                    ])),
                    ..Default::default()
                },
                no_change(),
                TscEdit {
                    caption: "no change run with js emit".into(),
                    command_line_args: Some(args(&[
                        "--b",
                        "project2/src",
                        "--verbose",
                        "--emitDeclarationOnly",
                        "false",
                    ])),
                    ..Default::default()
                },
                TscEdit {
                    caption: "js emit with change".into(),
                    edit: edit(|sys| {
                        sys.append_file(
                            "/home/src/workspaces/solution/project1/src/b.ts",
                            "const blocal = 10;",
                        );
                    }),
                    command_line_args: Some(args(&[
                        "--b",
                        "project2/src",
                        "--verbose",
                        "--emitDeclarationOnly",
                        "false",
                    ])),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
    ]
}

// Go: tscbuild_test.go:19 TestBuildCommandLine
#[test]
fn build_command_line() {
    let mut test_cases = vec![
        TscInput {
            sub_scenario: "included tsconfig json can be imported as json input".into(),
            files: files! {
                "/home/src/workspaces/project/index.ts" => r#"import tsconfig from "./tsconfig.json" with { type: "json" };
declare global {
    interface ImportAttributes {
        type: "json";
    }
}
console.log(tsconfig);"#,
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"module": "preserve",
							"moduleResolution": "bundler",
							"noEmit": true,
							"resolveJsonModule": true,
							"strict": true,
							"target": "esnext"
						},
						"include": ["index.ts", "tsconfig.json"]
					}"#),
            },
            command_line_args: args(&["--build"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "help".into(),
            files: FileMap::new(),
            command_line_args: args(&["--build", "--help"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "locale".into(),
            files: FileMap::new(),
            command_line_args: args(&["--build", "--help", "--locale", "en"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "bad locale".into(),
            files: FileMap::new(),
            command_line_args: args(&["--build", "--help", "--locale", "whoops"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "different options".into(),
            files: get_build_command_line_different_options_map("composite"),
            command_line_args: args(&["--build", "--verbose"]),
            edits: vec![
                TscEdit {
                    caption: "with sourceMap".into(),
                    command_line_args: Some(args(&["--build", "--verbose", "--sourceMap"])),
                    ..Default::default()
                },
                TscEdit {
                    caption: "should re-emit only js so they dont contain sourcemap".into(),
                    ..Default::default()
                },
                TscEdit {
                    caption: "with declaration should not emit anything".into(),
                    command_line_args: Some(args(&["--build", "--verbose", "--declaration"])),
                    ..Default::default()
                },
                no_change(),
                TscEdit {
                    caption: "with declaration and declarationMap".into(),
                    command_line_args: Some(args(&[
                        "--build",
                        "--verbose",
                        "--declaration",
                        "--declarationMap",
                    ])),
                    ..Default::default()
                },
                TscEdit {
                    caption: "should re-emit only dts so they dont contain sourcemap".into(),
                    ..Default::default()
                },
                TscEdit {
                    caption: "with emitDeclarationOnly should not emit anything".into(),
                    command_line_args: Some(args(&[
                        "--build",
                        "--verbose",
                        "--emitDeclarationOnly",
                    ])),
                    ..Default::default()
                },
                no_change(),
                TscEdit {
                    caption: "local change".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/a.ts",
                            "Local = 1",
                            "Local = 10",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "with declaration should not emit anything".into(),
                    command_line_args: Some(args(&["--build", "--verbose", "--declaration"])),
                    ..Default::default()
                },
                TscEdit {
                    caption: "with inlineSourceMap".into(),
                    command_line_args: Some(args(&["--build", "--verbose", "--inlineSourceMap"])),
                    ..Default::default()
                },
                TscEdit {
                    caption: "with sourceMap".into(),
                    command_line_args: Some(args(&["--build", "--verbose", "--sourceMap"])),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "different options with incremental".into(),
            files: get_build_command_line_different_options_map("incremental"),
            command_line_args: args(&["--build", "--verbose"]),
            edits: vec![
                TscEdit {
                    caption: "with sourceMap".into(),
                    command_line_args: Some(args(&["--build", "--verbose", "--sourceMap"])),
                    ..Default::default()
                },
                TscEdit {
                    caption: "should re-emit only js so they dont contain sourcemap".into(),
                    ..Default::default()
                },
                TscEdit {
                    caption: "with declaration, emit Dts and should not emit js".into(),
                    command_line_args: Some(args(&["--build", "--verbose", "--declaration"])),
                    ..Default::default()
                },
                TscEdit {
                    caption: "with declaration and declarationMap".into(),
                    command_line_args: Some(args(&[
                        "--build",
                        "--verbose",
                        "--declaration",
                        "--declarationMap",
                    ])),
                    ..Default::default()
                },
                no_change(),
                TscEdit {
                    caption: "local change".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/a.ts",
                            "Local = 1",
                            "Local = 10",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "with declaration and declarationMap".into(),
                    command_line_args: Some(args(&[
                        "--build",
                        "--verbose",
                        "--declaration",
                        "--declarationMap",
                    ])),
                    ..Default::default()
                },
                no_change(),
                TscEdit {
                    caption: "with inlineSourceMap".into(),
                    command_line_args: Some(args(&["--build", "--verbose", "--inlineSourceMap"])),
                    ..Default::default()
                },
                TscEdit {
                    caption: "with sourceMap".into(),
                    command_line_args: Some(args(&["--build", "--verbose", "--sourceMap"])),
                    ..Default::default()
                },
                TscEdit {
                    caption: "emit js files".into(),
                    ..Default::default()
                },
                TscEdit {
                    caption: "with declaration and declarationMap".into(),
                    command_line_args: Some(args(&[
                        "--build",
                        "--verbose",
                        "--declaration",
                        "--declarationMap",
                    ])),
                    ..Default::default()
                },
                TscEdit {
                    caption: "with declaration and declarationMap, should not re-emit".into(),
                    command_line_args: Some(args(&[
                        "--build",
                        "--verbose",
                        "--declaration",
                        "--declarationMap",
                    ])),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
    ];
    test_cases.extend(get_build_command_line_emit_declaration_only_test_cases(
        &["composite"],
        "",
    ));
    test_cases.extend(get_build_command_line_emit_declaration_only_test_cases(
        &["incremental", "declaration"],
        " with declaration and incremental",
    ));
    test_cases.extend(get_build_command_line_emit_declaration_only_test_cases(
        &["declaration"],
        " with declaration",
    ));

    run_tsc_inputs("commandLine", test_cases, WatchFilter::NonWatch);
}

// ---------------------------------------------------------------------------
// TestBuildClean
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:300 TestBuildClean
#[test]
fn build_clean() {
    let test_cases = vec![
        TscInput {
            sub_scenario: "file name and output name clashing".into(),
            files: files! {
                "/home/src/workspaces/solution/index.js" => "",
                "/home/src/workspaces/solution/bar.ts" => "",
                "/home/src/workspaces/solution/tsconfig.json" => dedent(r#"
				{
					"compilerOptions": { "allowJs": true }
				}"#),
            },
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args(&["--b", "--clean"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "tsx with dts emit".into(),
            files: files! {
                "/home/src/workspaces/solution/project/src/main.tsx" => "export const x = 10;",
                "/home/src/workspaces/solution/project/tsconfig.json" => dedent(r#"
				{
					"compilerOptions": { "declaration": true },
					"include": ["src/**/*.tsx", "src/**/*.ts"]
				}"#),
            },
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args(&["--b", "project", "-v", "--explainFiles"]),
            edits: vec![
                no_change(),
                TscEdit {
                    caption: "clean build".into(),
                    command_line_args: Some(args(&["-b", "project", "--clean"])),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
    ];

    run_tsc_inputs("clean", test_cases, WatchFilter::NonWatch);
}

// ---------------------------------------------------------------------------
// TestBuildConfigFileErrors
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:343 TestBuildConfigFileErrors
fn build_config_file_errors_inputs() -> Vec<TscInput> {
    vec![
        TscInput {
            sub_scenario: "when tsconfig extends the missing file".into(),
            files: files! {
                "/home/src/workspaces/project/tsconfig.first.json" => dedent(r#"
					{
						"extends": "./foobar.json",
						"compilerOptions": {
							"composite": true
						}
					}"#),
                "/home/src/workspaces/project/tsconfig.second.json" => dedent(r#"
					{
						"extends": "./foobar.json",
						"compilerOptions": {
							"composite": true
						}
					}"#),
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true
						},
						"references": [
							{ "path": "./tsconfig.first.json" },
							{ "path": "./tsconfig.second.json" }
						]
					}"#),
            },
            command_line_args: args(&["--b"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "reports invalid project reference fields".into(),
            files: files! {
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true
						},
						"files": ["index.ts"],
						"references": [
							{ "path": true },
							{ "circular": true },
							{ "path": "./utils", "circular": "yes" },
							{ "path": "" },
							{ "path": "./valid", "circular": true }
						]
					}"#),
                "/home/src/workspaces/project/index.ts" => "export const x = 10;",
                "/home/src/workspaces/project/utils/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true
						},
						"files": ["index.ts"]
					}"#),
                "/home/src/workspaces/project/utils/index.ts" => "export const y = 10;",
                "/home/src/workspaces/project/valid/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true
						},
						"files": ["index.ts"]
					}"#),
                "/home/src/workspaces/project/valid/index.ts" => "export const z = 10;",
            },
            command_line_args: args(&["--b", "--dry"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "reports syntax errors in config file".into(),
            files: files! {
                "/home/src/workspaces/project/a.ts" => "export function foo() { }",
                "/home/src/workspaces/project/b.ts" => "export function bar() { }",
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
						},
						"files": [
							"a.ts"
							"b.ts"
						]
					}"#),
            },
            command_line_args: args(&["--b"]),
            edits: vec![
                TscEdit {
                    caption: "reports syntax errors after change to config file".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/tsconfig.json",
                            ",",
                            r#", "declaration": true"#,
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "reports syntax errors after change to ts file".into(),
                    edit: edit(|sys| {
                        sys.append_file(
                            "/home/src/workspaces/project/a.ts",
                            "export function fooBar() { }",
                        );
                    }),
                    ..Default::default()
                },
                no_change(),
                TscEdit {
                    caption: "builds after fixing config file errors".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/home/src/workspaces/project/tsconfig.json",
                            &dedent(
                                r#"
							{
								"compilerOptions": {
									"composite": true, "declaration": true
								},
								"files": [
									"a.ts",
									"b.ts"
								]
							}"#,
                            ),
                        );
                    }),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "missing config file".into(),
            files: FileMap::new(),
            command_line_args: args(&["--b", "bogus.json"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "reports syntax errors in config file".into(),
            files: files! {
                "/home/src/workspaces/project/a.ts" => "export function foo() { }",
                "/home/src/workspaces/project/b.ts" => "export function bar() { }",
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
						},
						"files": [
							"a.ts"
							"b.ts"
						]
					}"#),
            },
            command_line_args: args(&["--b", "-w"]),
            edits: vec![
                TscEdit {
                    caption: "reports syntax errors after change to config file".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/tsconfig.json",
                            ",",
                            r#", "declaration": true"#,
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "reports syntax errors after change to ts file".into(),
                    edit: edit(|sys| {
                        sys.append_file(
                            "/home/src/workspaces/project/a.ts",
                            "export function fooBar() { }",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "reports error when there is no change to tsconfig file".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text("/home/src/workspaces/project/tsconfig.json", "", "");
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "builds after fixing config file errors".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/home/src/workspaces/project/tsconfig.json",
                            &dedent(
                                r#"
							{
								"compilerOptions": {
									"composite": true, "declaration": true
								},
								"files": [
									"a.ts",
									"b.ts"
								]
							}"#,
                            ),
                        );
                    }),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
    ]
}

#[test]
fn build_config_file_errors() {
    run_tsc_inputs(
        "configFileErrors",
        build_config_file_errors_inputs(),
        WatchFilter::NonWatch,
    );
}

#[test]
fn build_config_file_errors_watch() {
    run_tsc_inputs(
        "configFileErrors",
        build_config_file_errors_inputs(),
        WatchFilter::WatchOnly,
    );
}

// ---------------------------------------------------------------------------
// TestBuildDemoProject
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:492 getBuildDemoFileMap
// PORT: Go passes a nil `modify` for no change; callers here pass `|_| {}`.
fn get_build_demo_file_map(modify: impl FnOnce(&mut FileMap)) -> FileMap {
    let mut files = files! {
        "/user/username/projects/demo/animals/animal.ts" => dedent(r#"
				export type Size = "small" | "medium" | "large";
				export default interface Animal {
					size: Size;
				}
			"#),
        "/user/username/projects/demo/animals/dog.ts" => dedent(r#"
				import Animal from '.';
				import { makeRandomName } from '../core/utilities';

				export interface Dog extends Animal {
					woof(): void;
					name: string;
				}

				export function createDog(): Dog {
					return ({
						size: "medium",
						woof: function(this: Dog) {
							console.log(`${ this.name } says "Woof"!`);
						},
						name: makeRandomName()
					});
				}
			"#),
        "/user/username/projects/demo/animals/index.ts" => dedent(r"
				import Animal from './animal';

				export default Animal;
				import { createDog, Dog } from './dog';
				export { createDog, Dog };
			"),
        "/user/username/projects/demo/animals/tsconfig.json" => dedent(r#"
				{
					"extends": "../tsconfig-base.json",
					"compilerOptions": {
						"outDir": "../lib/animals",
						"rootDir": "."
					},
					"references": [
						{ "path": "../core" }
					]
				}
			"#),
        "/user/username/projects/demo/core/utilities.ts" => dedent(r#"

				export function makeRandomName() {
					return "Bob!?! ";
				}

				export function lastElementOf<T>(arr: T[]): T | undefined {
					if (arr.length === 0) return undefined;
					return arr[arr.length - 1];
				}
			"#),
        "/user/username/projects/demo/core/tsconfig.json" => dedent(r#"
				{
					"extends": "../tsconfig-base.json",
					"compilerOptions": {
						"outDir": "../lib/core",
						"rootDir": "."
					},
				}
			"#),
        "/user/username/projects/demo/zoo/zoo.ts" => dedent(r"
				import { Dog, createDog } from '../animals/index';

				export function createZoo(): Array<Dog> {
					return [
						createDog()
					];
				}
			"),
        "/user/username/projects/demo/zoo/tsconfig.json" => dedent(r#"
				{
					"extends": "../tsconfig-base.json",
					"compilerOptions": {
						"outDir": "../lib/zoo",
						"rootDir": "."
					},
					"references": [
						{
							"path": "../animals"
						}
					]
				}
			"#),
        "/user/username/projects/demo/tsconfig-base.json" => dedent(r#"
				{
					"compilerOptions": {
						"declaration": true,
						"target": "es5",
						"module": "commonjs",
						"strict": true,
						"noUnusedLocals": true,
						"noUnusedParameters": true,
						"noImplicitReturns": true,
						"noFallthroughCasesInSwitch": true,
						"composite": true,
					},
				}
			"#),
        "/user/username/projects/demo/tsconfig.json" => dedent(r#"
				{
					"files": [],
					"references": [
						{
							"path": "./core"
						},
						{
							"path": "./animals",
						},
						{
							"path": "./zoo",
						},
					],
				}
			"#),
    };
    modify(&mut files);
    files
}

// Go: tscbuild_test.go:489 TestBuildDemoProject
fn build_demo_project_inputs() -> Vec<TscInput> {
    vec![
        TscInput {
            sub_scenario: "in master branch with everything setup correctly and reports no error"
                .into(),
            files: get_build_demo_file_map(|_| {}),
            cwd: "/user/username/projects/demo".into(),
            command_line_args: args(&["--b", "--verbose"]),
            edits: no_change_only_edit(),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "in circular branch reports the error about it by stopping build".into(),
            files: get_build_demo_file_map(|files| {
                files.insert(
                    "/user/username/projects/demo/core/tsconfig.json".into(),
                    MapFile::from(dedent(r#"
					{
						"extends": "../tsconfig-base.json",
						"compilerOptions": {
							"outDir": "../lib/core",
							"rootDir": "."
						},
						"references": [
							{
								"path": "../zoo",
							}
						]
					}
				"#)),
                );
            }),
            cwd: "/user/username/projects/demo".into(),
            command_line_args: args(&["--b", "--verbose"]),
            ..Default::default()
        },
        TscInput {
            // !!! sheetal - this has missing errors from strada about files not in rootDir (3)
            sub_scenario:
                "in bad-ref branch reports the error about files not in rootDir at the import location"
                    .into(),
            files: get_build_demo_file_map(|files| {
                let utilities = file_text(files, "/user/username/projects/demo/core/utilities.ts");
                files.insert(
                    "/user/username/projects/demo/core/utilities.ts".into(),
                    MapFile::from(r"import * as A from '../animals'
".to_string() + &utilities),
                );
            }),
            cwd: "/user/username/projects/demo".into(),
            command_line_args: args(&["--b", "--verbose"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "in circular is set in the reference".into(),
            files: get_build_demo_file_map(|files| {
                files.insert(
                    "/user/username/projects/demo/a/tsconfig.json".into(),
                    MapFile::from(dedent(r#"
				{
					"extends": "../tsconfig-base.json",
					"compilerOptions": {
						"outDir": "../lib/a",
						"rootDir": "."
					},
					"references": [
						{
							"path": "../b",
							"circular": true
						}
					]
				}"#)),
                );
                files.insert(
                    "/user/username/projects/demo/b/tsconfig.json".into(),
                    MapFile::from(dedent(r#"
				{
					"extends": "../tsconfig-base.json",
					"compilerOptions": {
						"outDir": "../lib/b",
						"rootDir": "."
					},
					"references": [
						{
							"path": "../a",
						}
					]
				}"#)),
                );
                files.insert(
                    "/user/username/projects/demo/a/index.ts".into(),
                    MapFile::from("export const a = 10;"),
                );
                files.insert(
                    "/user/username/projects/demo/b/index.ts".into(),
                    MapFile::from("export const b = 10;"),
                );
                files.insert(
                    "/user/username/projects/demo/tsconfig.json".into(),
                    MapFile::from(dedent(r#"
				{
					"files": [],
					"references": [
						{
							"path": "./core"
						},
						{
							"path": "./animals",
						},
						{
							"path": "./zoo",
						},
						{
							"path": "./a",
						},
						{
							"path": "./b",
						},
					],
				}"#)),
                );
            }),
            cwd: "/user/username/projects/demo".into(),
            command_line_args: args(&["--b", "--verbose"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "updates with circular reference".into(),
            files: get_build_demo_file_map(|files| {
                files.insert(
                    "/user/username/projects/demo/core/tsconfig.json".into(),
                    MapFile::from(dedent(r#"
					{
						"extends": "../tsconfig-base.json",
						"compilerOptions": {
							"outDir": "../lib/core",
							"rootDir": "."
						},
						"references": [
							{
								"path": "../zoo",
							}
						]
					}
				"#)),
                );
            }),
            cwd: "/user/username/projects/demo".into(),
            command_line_args: args(&["--b", "-w", "--verbose"]),
            edits: vec![TscEdit {
                caption: "Fix error".into(),
                edit: edit(|sys| {
                    sys.write_file_no_error(
                        "/user/username/projects/demo/core/tsconfig.json",
                        &dedent(r#"
							{
								"extends": "../tsconfig-base.json",
								"compilerOptions": {
									"outDir": "../lib/core",
									"rootDir": "."
								},
							}
						"#),
                    );
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            // !!! sheetal - this has missing errors from strada about files not in rootDir (3)
            sub_scenario: "updates with bad reference".into(),
            files: get_build_demo_file_map(|files| {
                let utilities = file_text(files, "/user/username/projects/demo/core/utilities.ts");
                files.insert(
                    "/user/username/projects/demo/core/utilities.ts".into(),
                    MapFile::from(r"import * as A from '../animals'
".to_string() + &utilities),
                );
            }),
            cwd: "/user/username/projects/demo".into(),
            command_line_args: args(&["--b", "-w", "--verbose"]),
            edits: vec![TscEdit {
                caption: "Prepend a line".into(),
                edit: edit(|sys| {
                    sys.prepend_file("/user/username/projects/demo/core/utilities.ts", "\n");
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
    ]
}

#[test]
fn build_demo_project() {
    run_tsc_inputs("demo", build_demo_project_inputs(), WatchFilter::NonWatch);
}

#[test]
fn build_demo_project_watch() {
    run_tsc_inputs("demo", build_demo_project_inputs(), WatchFilter::WatchOnly);
}

// ---------------------------------------------------------------------------
// TestBuildEmitDeclarationOnly
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:778 getBuildEmitDeclarationOnlyImportFileMap
fn get_build_emit_declaration_only_import_file_map(
    declaration_map: bool,
    circular_ref: bool,
) -> FileMap {
    let mut files = files! {
        "/home/src/workspaces/project/src/a.ts" => dedent(r#"
				import { B } from "./b";

				export interface A {
					b: B;
				}
			"#),
        "/home/src/workspaces/project/src/b.ts" => dedent(r#"
				import { C } from "./c";

				export interface B {
					b: C;
				}
			"#),
        "/home/src/workspaces/project/src/c.ts" => dedent(r#"
				import { A } from "./a";

				export interface C {
					a: A;
				}
			"#),
        "/home/src/workspaces/project/src/index.ts" => dedent(r#"
				export { A } from "./a";
				export { B } from "./b";
				export { C } from "./c";
			"#),
        "/home/src/workspaces/project/tsconfig.json" => dedent(&go_sprintf(r#"
				{
					"compilerOptions": {
						"incremental": true,
						"target": "es5",
						"module": "commonjs",
						"declaration": true,
						"declarationMap": %t,
						"sourceMap": true,
						"outDir": "./lib",
						"composite": true,
						"strict": true,
						"esModuleInterop": true,
						"alwaysStrict": true,
						"rootDir": "src",
						"emitDeclarationOnly": true,
					},
				}"#, &[&declaration_map])),
    };
    if !circular_ref {
        files.remove("/home/src/workspaces/project/src/index.ts");
        files.insert(
            "/home/src/workspaces/project/src/a.ts".into(),
            MapFile::from(dedent(
                r#"
				export class B { prop = "hello"; }

				export interface A {
					b: B;
				}
			"#,
            )),
        );
    }
    files
}

// Go: tscbuild_test.go:837 getBuildEmitDeclarationOnlyTestCase
fn get_build_emit_declaration_only_test_case(declaration_map: bool) -> TscInput {
    TscInput {
        sub_scenario: "only dts output in circular import project with emitDeclarationOnly"
            .to_string()
            + if declaration_map {
                " and declarationMap"
            } else {
                ""
            },
        files: get_build_emit_declaration_only_import_file_map(declaration_map, true),
        command_line_args: args(&["--b", "--verbose"]),
        edits: vec![TscEdit {
            caption: "incremental-declaration-changes".into(),
            edit: edit(|sys| {
                sys.replace_file_text(
                    "/home/src/workspaces/project/src/a.ts",
                    "b: B;",
                    "b: B; foo: any;",
                );
            }),
            ..Default::default()
        }],
        ..Default::default()
    }
}

// Go: tscbuild_test.go:776 TestBuildEmitDeclarationOnly
#[test]
fn build_emit_declaration_only() {
    let test_cases = vec![
        get_build_emit_declaration_only_test_case(false),
        get_build_emit_declaration_only_test_case(true),
        TscInput {
            sub_scenario:
                "only dts output in non circular imports project with emitDeclarationOnly".into(),
            files: get_build_emit_declaration_only_import_file_map(true, false),
            command_line_args: args(&["--b", "--verbose"]),
            edits: vec![
                TscEdit {
                    caption: "incremental-declaration-doesnt-change".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/src/a.ts",
                            "export interface A {",
                            &dedent(
                                r"
								class C { }
								export interface A {",
                            ),
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "incremental-declaration-changes".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/src/a.ts",
                            "b: B;",
                            "b: B; foo: any;",
                        );
                    }),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
    ];

    run_tsc_inputs("emitDeclarationOnly", test_cases, WatchFilter::NonWatch);
}

// ---------------------------------------------------------------------------
// TestBuildFileDelete
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:887 TestBuildFileDelete
#[test]
fn build_file_delete() {
    let test_cases = vec![
        TscInput {
            sub_scenario: "detects deleted file".into(),
            files: files! {
                "/home/src/workspaces/solution/child/child.ts" => dedent(r#"
					import { child2 } from "../child/child2";
					export function child() {
						child2();
					}
				"#),
                "/home/src/workspaces/solution/child/child2.ts" => dedent(r"
					export function child2() {
					}
				"),
                "/home/src/workspaces/solution/child/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": { "composite": true }
					}
				"#),
                "/home/src/workspaces/solution/main/main.ts" => dedent(r#"
                    import { child } from "../child/child";
                    export function main() {
                        child();
                    }
                "#),
                "/home/src/workspaces/solution/main/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": { "composite": true },
						"references": [{ "path": "../child" }],
					}
				"#),
            },
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args(&[
                "--b",
                "main/tsconfig.json",
                "-v",
                "--traceResolution",
                "--explainFiles",
            ]),
            edits: vec![TscEdit {
                caption: "delete child2 file".into(),
                edit: edit(|sys| {
                    sys.remove_no_error("/home/src/workspaces/solution/child/child2.ts");
                    sys.remove_no_error("/home/src/workspaces/solution/child/child2.js");
                    sys.remove_no_error("/home/src/workspaces/solution/child/child2.d.ts");
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "deleted file without composite".into(),
            files: files! {
                "/home/src/workspaces/solution/child/child.ts" => dedent(r#"
					import { child2 } from "../child/child2";
					export function child() {
						child2();
					}
				"#),
                "/home/src/workspaces/solution/child/child2.ts" => dedent(r"
					export function child2() {
					}
				"),
                "/home/src/workspaces/solution/child/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": { }
					}
				"#),
            },
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args(&[
                "--b",
                "child/tsconfig.json",
                "-v",
                "--traceResolution",
                "--explainFiles",
            ]),
            edits: vec![TscEdit {
                caption: "delete child2 file".into(),
                edit: edit(|sys| {
                    sys.remove_no_error("/home/src/workspaces/solution/child/child2.ts");
                    sys.remove_no_error("/home/src/workspaces/solution/child/child2.js");
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
    ];

    run_tsc_inputs("fileDelete", test_cases, WatchFilter::NonWatch);
}

// ---------------------------------------------------------------------------
// TestBuildDependencyUpdate
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:1082 TestBuildDependencyUpdate (added by tsgo#4301)
fn build_dependency_update_inputs() -> Vec<TscInput> {
    // Project shape shared by the batched dependency update scenarios:
    // src/consumer.ts depends on dep-a only through src/middle.ts, whose .d.ts
    // signature does not change when dep-a's type gains a member. src/env.ts
    // pulls in dep-b, whose .d.ts augments the global scope.
    fn get_batch_dependency_update_files() -> FileMap {
        files! {
            "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
				{
					"compilerOptions": {
						"composite": true,
						"outDir": "dist",
						"strict": true
					},
					"include": ["src/**/*"]
				}
			"#),
            "/home/src/workspaces/project/src/consumer.ts" => dedent(r#"
				import type { Kind } from "./middle";
				export function describe(kind: Kind): string {
					switch (kind) {
						case "a":
							return "first";
						case "b":
							return "second";
					}
				}
			"#),
            "/home/src/workspaces/project/src/middle.ts" => r#"export type { Kind } from "dep-a";"#,
            "/home/src/workspaces/project/src/env.ts" => r#"import "dep-b";"#,
            "/home/src/workspaces/project/node_modules/dep-a/package.json" => dedent(r#"
				{
					"name": "dep-a",
					"version": "1.0.0",
					"types": "index.d.ts"
				}
			"#),
            "/home/src/workspaces/project/node_modules/dep-a/index.d.ts" => r#"export type Kind = "a" | "b";"#,
            "/home/src/workspaces/project/node_modules/dep-b/package.json" => dedent(r#"
				{
					"name": "dep-b",
					"version": "1.0.0",
					"types": "index.d.ts"
				}
			"#),
            "/home/src/workspaces/project/node_modules/dep-b/index.d.ts" => dedent(r#"
				declare global {
					interface DepBGlobal {
						marker: string;
					}
				}
				export {};
			"#),
        }
    }
    fn update_dep_a_with_breaking_type_change(sys: &TestSys) {
        sys.write_file_no_error(
            "/home/src/workspaces/project/node_modules/dep-a/index.d.ts",
            r#"export type Kind = "a" | "b" | "c";"#,
        );
    }
    vec![
        TscInput {
            // https://github.com/microsoft/typescript-go/issues/2666
            sub_scenario: "rebuilds when dependency in node_modules is updated".into(),
            files: files! {
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"outDir": "dist",
							"strict": true
						},
						"include": ["src/**/*"]
					}
				"#),
                "/home/src/workspaces/project/src/index.ts" => dedent(r#"
					import { myValue } from "my-dep";
					export const value: string = myValue;
				"#),
                "/home/src/workspaces/project/node_modules/my-dep/package.json" => dedent(r#"
					{
						"name": "my-dep",
						"version": "1.0.0",
						"types": "index.d.ts"
					}
				"#),
                "/home/src/workspaces/project/node_modules/my-dep/index.d.ts" => "export declare const myValue: string;",
            },
            cwd: "/home/src/workspaces/project".into(),
            command_line_args: args(&["--b", "--verbose"]),
            edits: vec![
                no_change(),
                TscEdit {
                    caption: "update dependency d.ts with breaking type change".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/home/src/workspaces/project/node_modules/my-dep/index.d.ts",
                            "export declare const myValue: number;",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "restore dependency d.ts".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/home/src/workspaces/project/node_modules/my-dep/index.d.ts",
                            "export declare const myValue: string;",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "update dependency d.ts timestamp without changing text".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/home/src/workspaces/project/node_modules/my-dep/index.d.ts",
                            "export declare const myValue: string;",
                        );
                    }),
                    ..Default::default()
                },
                no_change(),
                TscEdit {
                    caption: "delete dependency d.ts".into(),
                    edit: edit(|sys| {
                        sys.remove_no_error(
                            "/home/src/workspaces/project/node_modules/my-dep/index.d.ts",
                        );
                    }),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "rebuilds when missing dependency package json is added".into(),
            files: files! {
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"outDir": "dist",
							"strict": true
						},
						"include": ["src/**/*"]
					}
				"#),
                "/home/src/workspaces/project/src/index.ts" => dedent(r#"
					import { myValue } from "my-dep";
					export const value: string = myValue;
				"#),
                "/home/src/workspaces/project/node_modules/my-dep/index.d.ts" => "export declare const myValue: string;",
                "/home/src/workspaces/project/node_modules/my-dep/alt.d.ts" => "export declare const myValue: number;",
            },
            cwd: "/home/src/workspaces/project".into(),
            command_line_args: args(&["--b", "--verbose"]),
            edits: vec![TscEdit {
                caption: "add package json redirecting types to a declaration file with a breaking type change".into(),
                edit: edit(|sys| {
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/node_modules/my-dep/package.json",
                        r#"{"types":"alt.d.ts"}"#,
                    );
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "rebuilds when dependency package json redirects to a different declaration file".into(),
            files: files! {
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"outDir": "dist",
							"strict": true
						},
						"include": ["src/**/*"]
					}
				"#),
                "/home/src/workspaces/project/src/index.ts" => dedent(r#"
					import { myValue } from "my-dep";
					export const value: string = myValue;
				"#),
                "/home/src/workspaces/project/node_modules/my-dep/package.json" => dedent(r#"
					{
						"name": "my-dep",
						"version": "1.0.0",
						"types": "index.d.ts"
					}
				"#),
                "/home/src/workspaces/project/node_modules/my-dep/index.d.ts" => "export declare const myValue: string;",
                "/home/src/workspaces/project/node_modules/my-dep/alt.d.ts" => "export declare const myValue: number;",
            },
            cwd: "/home/src/workspaces/project".into(),
            command_line_args: args(&["--b", "--verbose"]),
            edits: vec![TscEdit {
                caption: "redirect package types to a declaration file with a breaking type change".into(),
                edit: edit(|sys| {
                    sys.replace_file_text(
                        "/home/src/workspaces/project/node_modules/my-dep/package.json",
                        "index.d.ts",
                        "alt.d.ts",
                    );
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "rebuilds when absolute non-root dependency is updated".into(),
            files: files! {
                "C:/work/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"outDir": "dist",
							"paths": {
								"abs-dep": ["D:/work/deps/dep.d.ts"]
							},
							"strict": true
						},
						"include": ["src/**/*"]
					}
				"#),
                "C:/work/project/src/index.ts" => dedent(r#"
					import { myValue } from "abs-dep";
					export const value: string = myValue;
				"#),
                "D:/work/deps/dep.d.ts" => "export declare const myValue: string;",
            },
            cwd: "C:/work/project".into(),
            windows_style_root: "C:/".into(),
            ignore_case: true,
            command_line_args: args(&["--b", "--verbose"]),
            edits: vec![TscEdit {
                caption: "update absolute non-root dependency with breaking type change".into(),
                edit: edit(|sys| {
                    sys.write_file_no_error(
                        "D:/work/deps/dep.d.ts",
                        "export declare const myValue: number;",
                    );
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watches absolute non-root dependency updates".into(),
            files: files! {
                "C:/work/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"outDir": "dist",
							"paths": {
								"abs-dep": ["D:/work/deps/dep.d.ts"]
							},
							"strict": true
						},
						"include": ["src/**/*"]
					}
				"#),
                "C:/work/project/src/index.ts" => dedent(r#"
					import { myValue } from "abs-dep";
					export const value: string = myValue;
				"#),
                "D:/work/deps/dep.d.ts" => "export declare const myValue: string;",
            },
            cwd: "C:/work/project".into(),
            windows_style_root: "C:/".into(),
            ignore_case: true,
            command_line_args: args(&["--b", "--verbose", "--watch"]),
            edits: vec![TscEdit {
                caption: "update absolute non-root dependency with breaking type change".into(),
                edit: edit(|sys| {
                    sys.write_file_no_error(
                        "D:/work/deps/dep.d.ts",
                        "export declare const myValue: number;",
                    );
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        // Go: added by tsgo#4665
        TscInput {
            sub_scenario: "rebuilds transitive dependents when dependency update batch includes a global scope change".into(),
            files: get_batch_dependency_update_files(),
            cwd: "/home/src/workspaces/project".into(),
            command_line_args: args(&["--b", "--verbose"]),
            edits: vec![
                TscEdit {
                    caption: "update dep-a with a breaking type change and dep-b with a global scope change in one batch".into(),
                    edit: edit(|sys| {
                        update_dep_a_with_breaking_type_change(sys);
                        sys.write_file_no_error(
                            "/home/src/workspaces/project/node_modules/dep-b/index.d.ts",
                            &dedent(r#"
							declare global {
								interface DepBGlobal {
									marker: string;
									extra: number;
								}
							}
							export {};
						"#),
                        );
                    }),
                    ..Default::default()
                },
                no_change(),
            ],
            ..Default::default()
        },
        TscInput {
            // Control for the batched scenario: the same dep-a break without dep-b's global scope change.
            sub_scenario: "rebuilds transitive dependents when dependency update batch has no global scope change".into(),
            files: get_batch_dependency_update_files(),
            cwd: "/home/src/workspaces/project".into(),
            command_line_args: args(&["--b", "--verbose"]),
            edits: vec![TscEdit {
                caption: "update dep-a with a breaking type change".into(),
                edit: edit(update_dep_a_with_breaking_type_change),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "rebuilds files using globals when global scope dependency is updated".into(),
            files: files! {
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"outDir": "dist",
							"strict": true
						},
						"include": ["src/**/*"]
					}
				"#),
                "/home/src/workspaces/project/src/env.ts" => r#"import "dep-b";"#,
                "/home/src/workspaces/project/src/user.ts" => "export const marker: string = globalMarker;",
                "/home/src/workspaces/project/node_modules/dep-b/package.json" => dedent(r#"
					{
						"name": "dep-b",
						"version": "1.0.0",
						"types": "index.d.ts"
					}
				"#),
                "/home/src/workspaces/project/node_modules/dep-b/index.d.ts" => dedent(r#"
					declare global {
						var globalMarker: string;
					}
					export {};
				"#),
            },
            cwd: "/home/src/workspaces/project".into(),
            command_line_args: args(&["--b", "--verbose"]),
            edits: vec![TscEdit {
                caption: "update dep-b changing the type of a global".into(),
                edit: edit(|sys| {
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/node_modules/dep-b/index.d.ts",
                        &dedent(r#"
							declare global {
								var globalMarker: number;
							}
							export {};
						"#),
                    );
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
    ]
}

#[test]
fn build_dependency_update() {
    run_tsc_inputs(
        "dependencyUpdate",
        build_dependency_update_inputs(),
        WatchFilter::NonWatch,
    );
}

#[test]
fn build_dependency_update_watch() {
    run_tsc_inputs(
        "dependencyUpdate",
        build_dependency_update_inputs(),
        WatchFilter::WatchOnly,
    );
}

// ---------------------------------------------------------------------------
// TestBuildInferredTypeFromTransitiveModule
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:974 getBuildInferredTypeFromTransitiveModuleMap
fn get_build_inferred_type_from_transitive_module_map(
    isolated_modules: bool,
    lazy_extra_contents: &str,
) -> FileMap {
    files! {
        "/home/src/workspaces/project/bar.ts" => dedent(r"
				interface RawAction {
					(...args: any[]): Promise<any> | void;
				}
				interface ActionFactory {
					<T extends RawAction>(target: T): T;
				}
				declare function foo<U extends any[] = any[]>(): ActionFactory;
				export default foo()(function foobar(param: string): void {
				});
			"),
        "/home/src/workspaces/project/bundling.ts" => dedent(r"
				export class LazyModule<TModule> {
					constructor(private importCallback: () => Promise<TModule>) {}
				}

				export class LazyAction<
					TAction extends (...args: any[]) => any,
					TModule
				>  {
					constructor(_lazyModule: LazyModule<TModule>, _getter: (module: TModule) => TAction) {
					}
				}
			"),
        "/home/src/workspaces/project/global.d.ts" => dedent(r"
				interface PromiseConstructor {
					new <T>(): Promise<T>;
				}
				declare var Promise: PromiseConstructor;
				interface Promise<T> {
				}
			"),
        "/home/src/workspaces/project/index.ts" => dedent(r"
				import { LazyAction, LazyModule } from './bundling';
				const lazyModule = new LazyModule(() =>
					import('./lazyIndex')
				);
				export const lazyBar = new LazyAction(lazyModule, m => m.bar);
			"),
        "/home/src/workspaces/project/lazyIndex.ts" => dedent(r"
				export { default as bar } from './bar';
			") + lazy_extra_contents,
        "/home/src/workspaces/project/tsconfig.json" => dedent(&go_sprintf(r#"
				{
					"compilerOptions": {
						"target": "es5",
						"declaration": true,
						"outDir": "obj",
						"incremental": true,
						"isolatedModules": %t,
					},
				}"#, &[&isolated_modules])),
    }
}

// Go: tscbuild_test.go:972 TestBuildInferredTypeFromTransitiveModule
#[test]
fn build_inferred_type_from_transitive_module() {
    let test_cases = vec![
        TscInput {
            sub_scenario: "inferred type from transitive module".into(),
            files: get_build_inferred_type_from_transitive_module_map(false, ""),
            command_line_args: args(&["--b", "--verbose"]),
            edits: vec![
                TscEdit {
                    caption: "incremental-declaration-changes".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/bar.ts",
                            "param: string",
                            "",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "incremental-declaration-changes".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/bar.ts",
                            "foobar()",
                            "foobar(param: string)",
                        );
                    }),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "inferred type from transitive module with isolatedModules".into(),
            files: get_build_inferred_type_from_transitive_module_map(true, ""),
            command_line_args: args(&["--b", "--verbose"]),
            edits: vec![
                TscEdit {
                    caption: "incremental-declaration-changes".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/bar.ts",
                            "param: string",
                            "",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "incremental-declaration-changes".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/bar.ts",
                            "foobar()",
                            "foobar(param: string)",
                        );
                    }),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
        TscInput {
            sub_scenario:
                "reports errors in files affected by change in signature with isolatedModules"
                    .into(),
            files: get_build_inferred_type_from_transitive_module_map(
                true,
                &dedent(
                    r#"
				import { default as bar } from './bar';
				bar("hello");
			"#,
                ),
            ),
            command_line_args: args(&["--b", "--verbose"]),
            edits: vec![
                TscEdit {
                    caption: "incremental-declaration-changes".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/bar.ts",
                            "param: string",
                            "",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "incremental-declaration-changes".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/bar.ts",
                            "foobar()",
                            "foobar(param: string)",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "incremental-declaration-changes".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/bar.ts",
                            "param: string",
                            "",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "Fix Error".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/home/src/workspaces/project/lazyIndex.ts",
                            r#"bar("hello")"#,
                            "bar()",
                        );
                    }),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
    ];

    run_tsc_inputs(
        "inferredTypeFromTransitiveModule",
        test_cases,
        WatchFilter::NonWatch,
    );
}

// ---------------------------------------------------------------------------
// TestBuildInferredTypeFromMonorepoReference
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:1110 TestBuildInferredTypeFromMonorepoReference
#[test]
fn build_inferred_type_from_monorepo_reference() {
    let test_cases = vec![TscInput {
        sub_scenario:
            "inferred type from referenced project that references another project in monorepo"
                .into(),
        files: files! {
            // Root package.json and tsconfig.json
            "/home/src/workspaces/solution/package.json" => dedent(r#"
					{
						"name": "tsgo-monorepo-issue",
						"private": true,
						"workspaces": ["packages/*"]
					}"#),
            "/home/src/workspaces/solution/tsconfig.json" => dedent(r#"
					{
						"files": [],
						"include": [],
						"references": [
							{ "path": "packages/package-a" },
							{ "path": "packages/package-b" },
							{ "path": "packages/package-c" }
						]
					}"#),
            // package-c: exports MyType interface
            "/home/src/workspaces/solution/packages/package-c/package.json" => dedent(r#"
					{
						"name": "package-c",
						"version": "1.0.0",
						"private": true,
						"type": "module",
						"main": "./src/index.ts",
						"types": "./src/index.ts",
						"exports": {
							".": "./src/index.ts"
						}
					}"#),
            "/home/src/workspaces/solution/packages/package-c/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"declaration": true,
							"emitDeclarationOnly": true,
							"module": "ESNext",
							"moduleResolution": "Bundler",
							"target": "ES2022",
							"outDir": "./out",
							"rootDir": "./src"
						},
						"include": ["src/**/*"]
					}"#),
            "/home/src/workspaces/solution/packages/package-c/src/index.ts" => dedent(r"
					export interface MyType {
						id: string;
						name: string;
						enabled: boolean;
					}"),
            // package-b: project reference to package-c, exports createThing() returning MyType
            "/home/src/workspaces/solution/packages/package-b/package.json" => dedent(r#"
					{
						"name": "package-b",
						"version": "1.0.0",
						"private": true,
						"type": "module",
						"main": "./src/index.ts",
						"types": "./src/index.ts",
						"exports": {
							".": "./src/index.ts"
						},
						"dependencies": {
							"package-c": "workspace:*"
						}
					}"#),
            "/home/src/workspaces/solution/packages/package-b/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"declaration": true,
							"emitDeclarationOnly": true,
							"module": "ESNext",
							"moduleResolution": "Bundler",
							"target": "ES2022",
							"outDir": "./out",
							"rootDir": "./src"
						},
						"include": ["src/**/*"],
						"references": [{ "path": "../package-c" }]
					}"#),
            "/home/src/workspaces/solution/packages/package-b/src/index.ts" => dedent(r#"
					import type { MyType } from "package-c";

					export function createThing(input: MyType): MyType {
						return { ...input };
					}"#),
            // package-a: project reference to package-b only (not package-c), uses createThing() without type annotation
            "/home/src/workspaces/solution/packages/package-a/package.json" => dedent(r#"
					{
						"name": "package-a",
						"version": "1.0.0",
						"private": true,
						"type": "module",
						"main": "./src/index.ts",
						"types": "./src/index.ts",
						"exports": {
							".": "./src/index.ts"
						},
						"dependencies": {
							"package-b": "workspace:*"
						}
					}"#),
            "/home/src/workspaces/solution/packages/package-a/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"declaration": true,
							"emitDeclarationOnly": true,
							"module": "ESNext",
							"moduleResolution": "Bundler",
							"target": "ES2022",
							"outDir": "./out",
							"rootDir": "./src"
						},
						"include": ["src/**/*"],
						"references": [{ "path": "../package-b" }]
					}"#),
            "/home/src/workspaces/solution/packages/package-a/src/index.ts" => dedent(r#"
					import { createThing } from "package-b";

					class MyClass {
						public thing = createThing({ id: "1", name: "test", enabled: true });
					}

					export { MyClass };"#),
            // Symlinks for node_modules to simulate pnpm/yarn workspace hoisting
            "/home/src/workspaces/solution/node_modules/package-a" => symlink("/home/src/workspaces/solution/packages/package-a"),
            "/home/src/workspaces/solution/node_modules/package-b" => symlink("/home/src/workspaces/solution/packages/package-b"),
            "/home/src/workspaces/solution/node_modules/package-c" => symlink("/home/src/workspaces/solution/packages/package-c"),
        },
        cwd: "/home/src/workspaces/solution".into(),
        command_line_args: args(&["--b", "--verbose"]),
        ..Default::default()
    }];

    run_tsc_inputs(
        "inferredTypeFromMonorepoReference",
        test_cases,
        WatchFilter::NonWatch,
    );
}

// ---------------------------------------------------------------------------
// TestBuildDeclarationEmitForReferencedProjectTypesSubpath
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:1257 TestBuildDeclarationEmitForReferencedProjectTypesSubpath
#[test]
fn build_declaration_emit_for_referenced_project_types_subpath() {
    let test_cases = vec![TscInput {
        // https://github.com/microsoft/typescript-go/issues/3617
        // This package.json exposes the same files under two exports subpaths
        // (`./src/*` and `./types/*`), so both `import("@scope/dep/src/...")` and
        // `import("@scope/dep/types/...")` are technically valid module specifiers for
        // the inferred type. The point of this test is not that one is "correct" and
        // the other "wrong", but that we pick the same one Strada does: when ranking
        // candidate paths, project-reference redirects (here the emitted `./types`
        // `.d.ts`) sort ahead of non-redirect paths (the symlinked `./src` source).
        // A regression in `comparePathsByRedirect` had inverted that ordering, causing
        // the `./src/*` specifier to win instead.
        sub_scenario: "declaration emit names referenced project type via types subpath".into(),
        files: files! {
            "/home/src/workspaces/solution/packages/dep/package.json" => dedent(r#"
					{
						"name": "@scope/dep",
						"version": "1.0.0",
						"exports": {
							"./src/*": "./src/*",
							"./types/*": "./types/*",
							".": { "types": "./types/index.d.ts", "default": "./src/index.ts" }
						}
					}"#),
            "/home/src/workspaces/solution/packages/dep/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"declaration": true,
							"emitDeclarationOnly": true,
							"module": "esnext",
							"moduleResolution": "bundler",
							"rootDir": "src",
							"outDir": "types",
							"declarationDir": "types",
							"strict": true
						},
						"include": ["src"]
					}"#),
            "/home/src/workspaces/solution/packages/dep/src/index.ts" => dedent(r#"
					import type { ComponentTypes as NewComponentTypes } from "./themes/componentTypes/index.js"
					export type { NewComponentTypes }"#),
            "/home/src/workspaces/solution/packages/dep/src/themes/componentTypes/index.ts" => dedent(r#"
					import type FormFieldLayout from "./formFieldLayout.js"
					export type ComponentTypes = {
						formFieldLayout: () => FormFieldLayout
					}"#),
            "/home/src/workspaces/solution/packages/dep/src/themes/componentTypes/formFieldLayout.ts" => dedent(r"
					export type FormFieldLayout = {
						textColor: string
						fontSize: string
					}
					export default FormFieldLayout"),
            "/home/src/workspaces/solution/packages/consumer/package.json" => dedent(r#"
					{
						"name": "@scope/consumer",
						"version": "1.0.0"
					}"#),
            "/home/src/workspaces/solution/packages/consumer/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"declaration": true,
							"emitDeclarationOnly": true,
							"module": "esnext",
							"moduleResolution": "bundler",
							"rootDir": "src",
							"outDir": "types",
							"declarationDir": "types",
							"strict": true
						},
						"include": ["src"],
						"references": [{ "path": "../dep" }]
					}"#),
            "/home/src/workspaces/solution/packages/consumer/src/index.ts" => dedent(r#"
					import type { NewComponentTypes } from "@scope/dep"
					declare const c: NewComponentTypes
					export const style = c.formFieldLayout()"#),
            "/home/src/workspaces/solution/node_modules/@scope/dep" => symlink("/home/src/workspaces/solution/packages/dep"),
            "/home/src/workspaces/solution/node_modules/@scope/consumer" => symlink("/home/src/workspaces/solution/packages/consumer"),
        },
        cwd: "/home/src/workspaces/solution".into(),
        command_line_args: args(&["--b", "packages/consumer", "--verbose"]),
        ..Default::default()
    }];

    run_tsc_inputs(
        "declarationEmitForReferencedProjectTypesSubpath",
        test_cases,
        WatchFilter::NonWatch,
    );
}

// ---------------------------------------------------------------------------
// TestBuildJavascriptProjectEmit
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:1350 TestBuildJavascriptProjectEmit
#[test]
fn build_javascript_project_emit() {
    let test_cases = vec![
        TscInput {
            // !!! sheetal errors seem different
            sub_scenario: "loads js-based projects and emits them correctly".into(),
            files: files! {
                "/home/src/workspaces/solution/common/nominal.js" => dedent(r"
                    /**
                     * @template T, Name
                     * @typedef {T & {[Symbol.species]: Name}} Nominal
                     */
                    module.exports = {};
				"),
                "/home/src/workspaces/solution/common/tsconfig.json" => dedent(r#"
					{
						"extends": "../tsconfig.base.json",
						"compilerOptions": {
							"composite": true,
						},
						"include": ["nominal.js"],
					}
				"#),
                "/home/src/workspaces/solution/sub-project/index.js" => dedent(r"
                    import { Nominal } from '../common/nominal';

                    /**
                     * @typedef {Nominal<string, 'MyNominal'>} MyNominal
                     */
				"),
                "/home/src/workspaces/solution/sub-project/tsconfig.json" => dedent(r#"
				{
					"extends": "../tsconfig.base.json",
					"compilerOptions": {
						"composite": true,
					},
					"references": [
						{ "path": "../common" },
					],
					"include": ["./index.js"],
				}"#),
                "/home/src/workspaces/solution/sub-project-2/index.js" => dedent(r"
                    import { MyNominal } from '../sub-project/index';

                    const variable = {
                        key: /** @type {MyNominal} */('value'),
                    };

                    /**
                     * @return {keyof typeof variable}
                     */
                    export function getVar() {
                        return 'key';
                    }
				"),
                "/home/src/workspaces/solution/sub-project-2/tsconfig.json" => dedent(r#"
				{
                    "extends": "../tsconfig.base.json",
                    "compilerOptions": {
                        "composite": true,
                    },
                    "references": [
                        { "path": "../sub-project" },
                    ],
                    "include": ["./index.js"],
                }"#),
                "/home/src/workspaces/solution/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": {
                        "composite": true,
                    },
                    "references": [
                        { "path": "./sub-project" },
                        { "path": "./sub-project-2" },
                    ],
                    "include": [],
                }"#),
                "/home/src/workspaces/solution/tsconfig.base.json" => dedent(r#"
				{
                    "compilerOptions": {
                        "skipLibCheck": true,
                        "rootDir": "./",
                        "outDir": "../lib",
                        "allowJs": true,
                        "checkJs": true,
                        "declaration": true,
                    },
                }"#),
                TSC_LIB_PATH.to_string() + "/lib.d.ts" => lib_with_symbol_species(),
            },
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args(&["--b"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario:
                "loads js-based projects with non-moved json files and emits them correctly".into(),
            files: files! {
                "/home/src/workspaces/solution/common/obj.json" => dedent(r#"
				{
                    "val": 42,
                }"#),
                "/home/src/workspaces/solution/common/index.ts" => dedent(r#"
                    import x = require("./obj.json");
                    export = x;
                "#),
                "/home/src/workspaces/solution/common/tsconfig.json" => dedent(r#"
				{
                    "extends": "../tsconfig.base.json",
                    "compilerOptions": {
                        "outDir": null,
                        "composite": true,
                    },
                    "include": ["index.ts", "obj.json"],
                }"#),
                "/home/src/workspaces/solution/sub-project/index.js" => dedent(r"
                    import mod from '../common';

                    export const m = mod;
				"),
                "/home/src/workspaces/solution/sub-project/tsconfig.json" => dedent(r#"
				{
                    "extends": "../tsconfig.base.json",
                    "compilerOptions": {
                        "composite": true,
                    },
                    "references": [
                        { "path": "../common" },
                    ],
                    "include": ["./index.js"],
                }"#),
                "/home/src/workspaces/solution/sub-project-2/index.js" => dedent(r"
                    import { m } from '../sub-project/index';

                    const variable = {
                        key: m,
                    };

                    export function getVar() {
                        return variable;
                    }
				"),
                "/home/src/workspaces/solution/sub-project-2/tsconfig.json" => dedent(r#"
				{
					"extends": "../tsconfig.base.json",
					"compilerOptions": {
						"composite": true,
					},
                    "references": [
                        { "path": "../sub-project" },
                    ],
                    "include": ["./index.js"],
                }"#),
                "/home/src/workspaces/solution/tsconfig.json" => dedent(r#"
				{
					"compilerOptions": {
						"composite": true,
					},
					"references": [
						{ "path": "./sub-project" },
						{ "path": "./sub-project-2" },
                    ],
                    "include": [],
                }"#),
                "/home/src/workspaces/solution/tsconfig.base.json" => dedent(r#"
				{
					"compilerOptions": {
						"skipLibCheck": true,
						"rootDir": "./",
						"outDir": "../out",
						"allowJs": true,
						"checkJs": true,
						"resolveJsonModule": true,
						"esModuleInterop": true,
						"declaration": true,
					},
                }"#),
            },
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args(&["-b"]),
            ..Default::default()
        },
    ];

    run_tsc_inputs("javascriptProjectEmit", test_cases, WatchFilter::NonWatch);
}

// ---------------------------------------------------------------------------
// TestBuildLateBoundSymbol
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:1536 TestBuildLateBoundSymbol
#[test]
fn build_late_bound_symbol() {
    let test_cases = vec![TscInput {
        sub_scenario: "interface is merged and contains late bound member".into(),
        files: files! {
            "/home/src/workspaces/project/src/globals.d.ts" => dedent(r"
                    interface SymbolConstructor {
                        (description?: string | number): symbol;
                    }
                    declare var Symbol: SymbolConstructor;
                "),
            "/home/src/workspaces/project/src/hkt.ts" => "export interface HKT<T> { }",
            "/home/src/workspaces/project/src/main.ts" => dedent(r#"
                    import { HKT } from "./hkt";

                    const sym = Symbol();

                    declare module "./hkt" {
                        interface HKT<T> {
                            [sym]: { a: T }
                        }
                    }
                    const x = 10;
                    type A = HKT<number>[typeof sym];
                "#),
            "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": {
                        "rootDir": "src",
                        "incremental": true,
                    },
                }"#),
        },
        command_line_args: args(&["--b", "--verbose"]),
        edits: vec![
            TscEdit {
                caption: "incremental-declaration-doesnt-change".into(),
                edit: edit(|sys| {
                    sys.replace_file_text(
                        "/home/src/workspaces/project/src/main.ts",
                        "const x = 10;",
                        "",
                    );
                }),
                ..Default::default()
            },
            TscEdit {
                caption: "incremental-declaration-doesnt-change".into(),
                edit: edit(|sys| {
                    sys.append_file("/home/src/workspaces/project/src/main.ts", "const x = 10;");
                }),
                ..Default::default()
            },
        ],
        ..Default::default()
    }];

    run_tsc_inputs("lateBoundSymbol", test_cases, WatchFilter::NonWatch);
}

// ---------------------------------------------------------------------------
// TestBuildModuleSpecifiers
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:1593 TestBuildModuleSpecifiers
#[test]
fn build_module_specifiers() {
    let test_cases = vec![
        TscInput {
            sub_scenario: "synthesized module specifiers resolve correctly".into(),
            files: files! {
                "/home/src/workspaces/packages/solution/common/nominal.ts" => dedent(r"
                    export declare type Nominal<T, Name extends string> = T & {
                        [Symbol.species]: Name;
                    };
				"),
                "/home/src/workspaces/packages/solution/common/tsconfig.json" => dedent(r#"
				{
                    "extends": "../../tsconfig.base.json",
                    "compilerOptions": {
                        "composite": true
                    },
                    "include": ["nominal.ts"]
				}
				"#),
                "/home/src/workspaces/packages/solution/sub-project/index.ts" => dedent(r"
                    import { Nominal } from '../common/nominal';

                    export type MyNominal = Nominal<string, 'MyNominal'>;
				"),
                "/home/src/workspaces/packages/solution/sub-project/tsconfig.json" => dedent(r#"
                    {
                        "extends": "../../tsconfig.base.json",
                        "compilerOptions": {
                            "composite": true
                        },
                        "references": [
                            { "path": "../common" }
                        ],
                        "include": ["./index.ts"]
                    }
                "#),
                "/home/src/workspaces/packages/solution/sub-project-2/index.ts" => dedent(r"
                    import { MyNominal } from '../sub-project/index';

                    const variable = {
                        key: 'value' as MyNominal,
                    };

                    export function getVar(): keyof typeof variable {
                        return 'key';
                    }
				"),
                "/home/src/workspaces/packages/solution/sub-project-2/tsconfig.json" => dedent(r#"
                    {
                        "extends": "../../tsconfig.base.json",
                        "compilerOptions": {
                            "composite": true
                        },
                        "references": [
                            { "path": "../sub-project" }
                        ],
                        "include": ["./index.ts"]
                    }
                "#),
                "/home/src/workspaces/packages/solution/tsconfig.json" => dedent(r#"
                    {
                        "compilerOptions": {
                            "composite": true
                        },
                        "references": [
                            { "path": "./sub-project" },
                            { "path": "./sub-project-2" }
                        ],
                        "include": []
                    }
                "#),
                "/home/src/workspaces/packages/tsconfig.base.json" => dedent(r#"
                    {
                        "compilerOptions": {
                            "skipLibCheck": true,
                            "rootDir": "./",
                            "outDir": "lib"
						}
                    }
                "#),
                "/home/src/workspaces/packages/tsconfig.json" => dedent(r#"
                    {
                        "compilerOptions": {
                            "composite": true
                        },
                        "references": [
                            { "path": "./solution" },
                        ],
                        "include": [],
                    }
                "#),
                TSC_LIB_PATH.to_string() + "/lib.d.ts" => lib_with_symbol_species(),
            },
            cwd: "/home/src/workspaces/packages".into(),
            command_line_args: args(&["-b", "--verbose"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "synthesized module specifiers across projects resolve correctly".into(),
            files: files! {
                "/home/src/workspaces/packages/src-types/index.ts" => dedent(r"
                    export * from './dogconfig.js';"),
                "/home/src/workspaces/packages/src-types/dogconfig.ts" => dedent(r"
                    export interface DogConfig {
                        name: string;
					}
				"),
                "/home/src/workspaces/packages/src-dogs/index.ts" => dedent(r"
                    export * from 'src-types';
                    export * from './lassie/lassiedog.js';
				"),
                "/home/src/workspaces/packages/src-dogs/dogconfig.ts" => dedent(r"
                    import { DogConfig } from 'src-types';

                    export const DOG_CONFIG: DogConfig = {
                        name: 'Default dog',
                    };
				"),
                "/home/src/workspaces/packages/src-dogs/dog.ts" => dedent(r"
                    import { DogConfig } from 'src-types';
                    import { DOG_CONFIG } from './dogconfig.js';
                    
                    export abstract class Dog {
                    
                        public static getCapabilities(): DogConfig {
                            return DOG_CONFIG;
                        }
                    }
				"),
                "/home/src/workspaces/packages/src-dogs/lassie/lassiedog.ts" => dedent(r"
                    import { Dog } from '../dog.js';
                    import { LASSIE_CONFIG } from './lassieconfig.js';
                    
                    export class LassieDog extends Dog {
                        protected static getDogConfig = () => LASSIE_CONFIG;
                    }
				"),
                "/home/src/workspaces/packages/src-dogs/lassie/lassieconfig.ts" => dedent(r"
                    import { DogConfig } from 'src-types';

                    export const LASSIE_CONFIG: DogConfig = { name: 'Lassie' };
				"),
                "/home/src/workspaces/packages/tsconfig-base.json" => dedent(r#"
                    {
                        "compilerOptions": {
                            "declaration": true,
                            "module": "node16",
                        },
                    }
				"#),
                "/home/src/workspaces/packages/src-types/package.json" => dedent(r#"
				{
                    "type": "module",
                    "exports": "./index.js"
                }"#),
                "/home/src/workspaces/packages/src-dogs/package.json" => dedent(r#"
				{
                    "type": "module",
                    "exports": "./index.js"
                }"#),
                "/home/src/workspaces/packages/src-types/tsconfig.json" => dedent(r#"
				{
                    "extends": "../tsconfig-base.json",
                    "compilerOptions": {
                        "composite": true,
                    },
                    "include": [
                        "**/*",
                    ],
                }"#),
                "/home/src/workspaces/packages/src-dogs/tsconfig.json" => dedent(r#"
				{
                    "extends": "../tsconfig-base.json",
                    "compilerOptions": {
                        "composite": true,
                    },
                    "references": [
                        { "path": "../src-types" },
                    ],
                    "include": [
                        "**/*",
                    ],
                }"#),
                "/home/src/workspaces/packages/src-types/node_modules" => symlink("/home/src/workspaces/packages"),
                "/home/src/workspaces/packages/src-dogs/node_modules" => symlink("/home/src/workspaces/packages"),
            },
            cwd: "/home/src/workspaces/packages".into(),
            command_line_args: args(&["-b", "src-types", "src-dogs", "--verbose"]),
            ..Default::default()
        },
    ];

    run_tsc_inputs("moduleSpecifiers", test_cases, WatchFilter::NonWatch);
}

// ---------------------------------------------------------------------------
// TestBuildOutputPaths
// ---------------------------------------------------------------------------

// Go: tscbuild_test.go:1791 tscOutputPathScenario
struct TscOutputPathScenario {
    sub_scenario: &'static str,
    files: FileMap,
    expected_dts_names: Vec<&'static str>,
}

// Go: tsoptionstest/vfsparseconfighost.go VfsParseConfigHost
// PORT: Go passes the `TestSys` as the `ParseConfigHost`. This host has the
// same `FS()` files, current directory and case sensitivity.
struct OutputPathsParseHost {
    fs: Rc<dyn Fs>,
    current_directory: String,
}

impl ParseConfigHost for OutputPathsParseHost {
    fn fs(&self) -> Rc<dyn Fs> {
        self.fs.clone()
    }

    fn get_current_directory(&self) -> String {
        self.current_directory.clone()
    }
}

// Go: tscbuild_test.go:1812 t.Run("GetOutputFileNames/"+s.subScenario, ...)
// PORT: Go builds the host with `newTestSys(input, false)`. Its default lib
// files are outside the project directory and its output capture is not
// used by config parsing, so a plain `MapFs` view of the input files gives
// the same parsed config. A mismatch is returned, not asserted, so that the
// caller can report it with the baseline failures.
fn check_output_file_names(input: &TscInput, expected_dts_names: &[&str]) -> Result<(), String> {
    let current_directory = if input.cwd.is_empty() {
        "/home/src/workspaces/project".to_string()
    } else {
        input.cwd.clone()
    };
    let host = OutputPathsParseHost {
        fs: vfstest::from_map(input.files.clone(), !input.ignore_case),
        current_directory,
    };
    let (config, _) = get_parsed_command_line_of_config_file(
        "/home/src/workspaces/project/tsconfig.json",
        Some(&CompilerOptions::default()),
        None,
        &host,
        None,
    );
    let Some(config) = config else {
        return Err(format!(
            "GetOutputFileNames/{}: no parsed command line",
            input.sub_scenario
        ));
    };
    let actual = config.get_output_file_names();
    if actual != expected_dts_names {
        return Err(format!(
            "GetOutputFileNames/{}:\n  actual:   {actual:?}\n  expected: {expected_dts_names:?}",
            input.sub_scenario
        ));
    }
    Ok(())
}

// Go: tscbuild_test.go:1789 TestBuildOutputPaths
#[test]
fn build_output_paths() {
    let test_cases = vec![
        TscOutputPathScenario {
            sub_scenario: "when rootDir is not specified",
            files: files! {
                "/home/src/workspaces/project/src/index.ts" => "export const x = 10;",
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": {
                        "outDir": "dist",
                    },
                }"#),
            },
            expected_dts_names: vec!["/home/src/workspaces/project/dist/src/index.js"],
        },
        TscOutputPathScenario {
            sub_scenario: "when rootDir is not specified and is composite",
            files: files! {
                "/home/src/workspaces/project/src/index.ts" => "export const x = 10;",
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": {
                        "outDir": "dist",
						"composite": true,
                    },
                }"#),
            },
            expected_dts_names: vec![
                "/home/src/workspaces/project/dist/src/index.js",
                "/home/src/workspaces/project/dist/src/index.d.ts",
            ],
        },
        TscOutputPathScenario {
            sub_scenario: "when rootDir is specified",
            files: files! {
                "/home/src/workspaces/project/src/index.ts" => "export const x = 10;",
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": {
                        "outDir": "dist",
						"rootDir": "src",
                    },
                }"#),
            },
            expected_dts_names: vec!["/home/src/workspaces/project/dist/index.js"],
        },
        TscOutputPathScenario {
            // !!! sheetal error missing as not yet implemented
            sub_scenario: "when rootDir is specified but not all files belong to rootDir",
            files: files! {
                "/home/src/workspaces/project/src/index.ts" => "export const x = 10;",
                "/home/src/workspaces/project/types/type.ts" => "export type t = string;",
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": {
                        "outDir": "dist",
						"rootDir": "src",
                    },
                }"#),
            },
            expected_dts_names: vec![
                "/home/src/workspaces/project/dist/index.js",
                "/home/src/workspaces/project/types/type.js",
            ],
        },
        TscOutputPathScenario {
            // !!! sheetal error missing as not yet implemented
            sub_scenario: "when rootDir is specified but not all files belong to rootDir and is composite",
            files: files! {
                "/home/src/workspaces/project/src/index.ts" => "export const x = 10;",
                "/home/src/workspaces/project/types/type.ts" => "export type t = string;",
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": {
                        "outDir": "dist",
						"rootDir": "src",
						"composite": true
                    },
                }"#),
            },
            expected_dts_names: vec![
                "/home/src/workspaces/project/dist/index.js",
                "/home/src/workspaces/project/dist/index.d.ts",
                "/home/src/workspaces/project/types/type.js",
                "/home/src/workspaces/project/types/type.d.ts",
            ],
        },
    ];

    // Go: tscbuild_test.go:1796 runOutputPaths
    let mut inputs = Vec::new();
    let mut output_name_failures = Vec::new();
    for test in test_cases {
        let input = TscInput {
            sub_scenario: test.sub_scenario.into(),
            files: test.files,
            command_line_args: args(&["-b", "-v"]),
            edits: vec![
                no_change(),
                TscEdit {
                    caption: "Normal build without change, that does not block emit on error to show files that get emitted".into(),
                    command_line_args: Some(args(&["-p", "/home/src/workspaces/project/tsconfig.json"])),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        if let Err(failure) = check_output_file_names(&input, &test.expected_dts_names) {
            output_name_failures.push(failure);
        }
        inputs.push(input);
    }
    // PORT: Go reports these as separate subtests. They are printed first so
    // that a baseline failure (which panics) does not hide them.
    for failure in &output_name_failures {
        eprintln!("{failure}");
    }
    run_tsc_inputs("outputPaths", inputs, WatchFilter::NonWatch);
    assert!(
        output_name_failures.is_empty(),
        "GetOutputFileNames mismatches:\n{}",
        output_name_failures.join("\n")
    );
}
