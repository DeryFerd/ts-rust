//! Go: `internal/execute/tsctests/tscwatch_test.go` (`tscWatch/commandLineWatch`
//! and `tscWatch/noEmit` baselines).
//!
//! Every input here is a watch input.
//!
//! PORT: Go string literals with tabs keep the tabs as `\t` escapes.

use crate::support::runner::{
    self, FileMap, TscEdit, TscInput, WatchFilter, no_change, run_tsc_inputs,
};
use crate::support::test_sys::TestSys;
use crate::support::vfstest::{MapFile, symlink};

/// Go `FileMap{...}` literal.
fn file_map<const N: usize>(entries: [(&str, MapFile); N]) -> FileMap {
    entries
        .into_iter()
        .map(|(path, file)| (path.to_string(), file))
        .collect()
}

/// Go `[]string{...}` command line literal.
fn args<const N: usize>(args: [&str; N]) -> Vec<String> {
    args.map(String::from).into()
}

// Go: tscwatch_test.go:10 TestWatch
#[test]
fn watch_watch() {
    let test_cases = vec![
        TscInput {
            sub_scenario: "watch with no tsconfig".into(),
            files: file_map([("/home/src/workspaces/project/index.ts", "".into())]),
            command_line_args: args(["index.ts", "--watch"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch with tsconfig and incremental".into(),
            files: file_map([
                ("/home/src/workspaces/project/index.ts", "".into()),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch", "--incremental"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch skips build when no files change".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    "const x: number = 1;".into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![no_change()],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch rebuilds when file is modified".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    "const x: number = 1;".into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit("modify file", |sys| {
                sys.write_file_no_error(
                    "/home/src/workspaces/project/index.ts",
                    "const x: number = 2;",
                );
            })],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch rebuilds when source file is deleted".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/a.ts",
                    r#"import { b } from "./b";"#.into(),
                ),
                (
                    "/home/src/workspaces/project/b.ts",
                    "export const b = 1;".into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![TscEdit {
                caption: "delete imported file".into(),
                edit: runner::edit(|sys| {
                    sys.remove_no_error("/home/src/workspaces/project/b.ts");
                }),
                expected_diff: "incremental resolves to .js output from prior build (TS7016) while clean build cannot find module at all (TS2307)".into(),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch detects new file resolving failed import".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/a.ts",
                    r#"import { b } from "./b";"#.into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit("create missing file", |sys| {
                sys.write_file_no_error(
                    "/home/src/workspaces/project/b.ts",
                    "export const b = 1;",
                );
            })],
            ..Default::default()
        },
        // Directory-level change detection via imports
        TscInput {
            sub_scenario: "watch detects imported file added in new directory".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import { util } from "./lib/util";"#.into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit("create directory and imported file", |sys| {
                sys.write_file_no_error(
                    "/home/src/workspaces/project/lib/util.ts",
                    r#"export const util = "hello";"#,
                );
            })],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch detects imported directory removed".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import { util } from "./lib/util";"#.into(),
                ),
                (
                    "/home/src/workspaces/project/lib/util.ts",
                    r#"export const util = "hello";"#.into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![TscEdit {
                caption: "remove directory with imported file".into(),
                edit: runner::edit(|sys| {
                    sys.remove_no_error("/home/src/workspaces/project/lib/util.ts");
                }),
                expected_diff: "incremental resolves to .js output from prior build (TS7016) while clean build cannot find module at all (TS2307)".into(),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch detects import path restructured".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import { util } from "./lib/util";"#.into(),
                ),
                (
                    "/home/src/workspaces/project/lib/util.ts",
                    r#"export const util = "v1";"#.into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit(
                "move file to new path and update import",
                |sys| {
                    sys.remove_no_error("/home/src/workspaces/project/lib/util.ts");
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/src/util.ts",
                        r#"export const util = "v2";"#,
                    );
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/index.ts",
                        r#"import { util } from "./src/util";"#,
                    );
                },
            )],
            ..Default::default()
        },
        // tsconfig include/exclude change detection
        TscInput {
            sub_scenario: "watch rebuilds when tsconfig include pattern adds file".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    "const x = 1;".into(),
                ),
                (
                    "/home/src/workspaces/project/tsconfig.json",
                    "{\n\t\"compilerOptions\": {},\n\t\"include\": [\"*.ts\"]\n}".into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit(
                "widen include pattern to add src dir",
                |sys| {
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/src/extra.ts",
                        "export const extra = 2;",
                    );
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/tsconfig.json",
                        "{\n\t\"compilerOptions\": {},\n\t\"include\": [\"*.ts\", \"src/**/*.ts\"]\n}",
                    );
                },
            )],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch rebuilds when tsconfig is modified to change strict".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    "const x = null; const y: string = x;".into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit("enable strict mode", |sys| {
                sys.write_file_no_error(
                    "/home/src/workspaces/project/tsconfig.json",
                    r#"{"compilerOptions": {"strict": true}}"#,
                );
            })],
            ..Default::default()
        },
        // Path resolution: tsconfig include pointing to non-existent directory
        TscInput {
            sub_scenario: "watch detects file added to previously non-existent include path"
                .into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    "const x = 1;".into(),
                ),
                (
                    "/home/src/workspaces/project/tsconfig.json",
                    "{\n\t\"compilerOptions\": {},\n\t\"include\": [\"index.ts\", \"src/**/*.ts\"]\n}"
                        .into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit(
                "create src dir with ts file matching include",
                |sys| {
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/src/helper.ts",
                        r#"export const helper = "added";"#,
                    );
                },
            )],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch detects new file in existing include directory".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/src/a.ts",
                    "export const a = 1;".into(),
                ),
                (
                    "/home/src/workspaces/project/tsconfig.json",
                    "{\n\t\"compilerOptions\": {},\n\t\"include\": [\"src/**/*.ts\"]\n}".into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit(
                "add new file to existing src directory",
                |sys| {
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/src/b.ts",
                        "export const b = 2;",
                    );
                },
            )],
            ..Default::default()
        },
        // Wildcard include: nested subdirectory detection
        TscInput {
            sub_scenario: "watch detects file added in new nested subdirectory".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/src/a.ts",
                    "export const a = 1;".into(),
                ),
                (
                    "/home/src/workspaces/project/tsconfig.json",
                    "{\n\t\"compilerOptions\": {},\n\t\"include\": [\"src/**/*.ts\"]\n}".into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit("create nested dir with ts file", |sys| {
                sys.write_file_no_error(
                    "/home/src/workspaces/project/src/deep/nested/util.ts",
                    r#"export const util = "nested";"#,
                );
            })],
            ..Default::default()
        },
        TscInput {
            sub_scenario:
                "watch detects file added in multiple new subdirectories simultaneously".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/src/a.ts",
                    "export const a = 1;".into(),
                ),
                (
                    "/home/src/workspaces/project/tsconfig.json",
                    "{\n\t\"compilerOptions\": {},\n\t\"include\": [\"src/**/*.ts\"]\n}".into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit(
                "create multiple new subdirs with files",
                |sys| {
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/src/models/user.ts",
                        "export interface User { name: string; }",
                    );
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/src/utils/format.ts",
                        "export function format(s: string): string { return s.trim(); }",
                    );
                },
            )],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch detects nested subdirectory removed and recreated".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/src/lib/helper.ts",
                    r#"export const helper = "v1";"#.into(),
                ),
                (
                    "/home/src/workspaces/project/tsconfig.json",
                    "{\n\t\"compilerOptions\": {},\n\t\"include\": [\"src/**/*.ts\"]\n}".into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![
                TscEdit {
                    caption: "remove nested dir".into(),
                    expected_diff:
                        "incremental has prior state and does not report no-inputs error".into(),
                    edit: runner::edit(|sys| {
                        sys.remove_no_error("/home/src/workspaces/project/src/lib/helper.ts");
                    }),
                    ..Default::default()
                },
                new_tsc_edit("recreate nested dir with new content", |sys| {
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/src/lib/helper.ts",
                        r#"export const helper = "v2";"#,
                    );
                }),
            ],
            ..Default::default()
        },
        // Path resolution: import from non-existent node_modules package
        TscInput {
            sub_scenario: "watch detects node modules package added".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import { lib } from "mylib";"#.into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit("install package in node_modules", |sys| {
                sys.write_file_no_error(
                    "/home/src/workspaces/project/node_modules/mylib/package.json",
                    r#"{"name": "mylib", "main": "index.js", "types": "index.d.ts"}"#,
                );
                sys.write_file_no_error(
                    "/home/src/workspaces/project/node_modules/mylib/index.js",
                    r#"exports.lib = "hello";"#,
                );
                sys.write_file_no_error(
                    "/home/src/workspaces/project/node_modules/mylib/index.d.ts",
                    "export declare const lib: string;",
                );
            })],
            ..Default::default()
        },
        // Path resolution: node_modules package removed
        TscInput {
            sub_scenario: "watch detects node modules package removed".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import { lib } from "mylib";"#.into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
                (
                    "/home/src/workspaces/project/node_modules/mylib/package.json",
                    r#"{"name": "mylib", "main": "index.js", "types": "index.d.ts"}"#.into(),
                ),
                (
                    "/home/src/workspaces/project/node_modules/mylib/index.js",
                    r#"exports.lib = "hello";"#.into(),
                ),
                (
                    "/home/src/workspaces/project/node_modules/mylib/index.d.ts",
                    "export declare const lib: string;".into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![TscEdit {
                caption: "remove node_modules package".into(),
                edit: runner::edit(|sys| {
                    sys.remove_no_error(
                        "/home/src/workspaces/project/node_modules/mylib/index.d.ts",
                    );
                    sys.remove_no_error("/home/src/workspaces/project/node_modules/mylib/index.js");
                    sys.remove_no_error(
                        "/home/src/workspaces/project/node_modules/mylib/package.json",
                    );
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        // Path resolution: node_modules removed then reinstalled (npm ci after rm -rf)
        TscInput {
            sub_scenario: "watch detects node modules reinstalled after deletion".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import { lib } from "mylib";"#.into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
                (
                    "/home/src/workspaces/project/node_modules/mylib/package.json",
                    r#"{"name": "mylib", "main": "index.js", "types": "index.d.ts"}"#.into(),
                ),
                (
                    "/home/src/workspaces/project/node_modules/mylib/index.js",
                    r#"exports.lib = "hello";"#.into(),
                ),
                (
                    "/home/src/workspaces/project/node_modules/mylib/index.d.ts",
                    "export declare const lib: string;".into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![
                TscEdit {
                    caption: "delete node_modules entirely".into(),
                    edit: runner::edit(|sys| {
                        sys.remove_no_error(
                            "/home/src/workspaces/project/node_modules/mylib/index.d.ts",
                        );
                        sys.remove_no_error(
                            "/home/src/workspaces/project/node_modules/mylib/index.js",
                        );
                        sys.remove_no_error(
                            "/home/src/workspaces/project/node_modules/mylib/package.json",
                        );
                    }),
                    ..Default::default()
                },
                new_tsc_edit("reinstall node_modules", |sys| {
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/node_modules/mylib/package.json",
                        r#"{"name": "mylib", "main": "index.js", "types": "index.d.ts"}"#,
                    );
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/node_modules/mylib/index.js",
                        r#"exports.lib = "hello";"#,
                    );
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/node_modules/mylib/index.d.ts",
                        "export declare const lib: string;",
                    );
                }),
            ],
            ..Default::default()
        },
        // Config file lifecycle
        TscInput {
            sub_scenario: "watch handles tsconfig deleted".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    "const x = 1;".into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![TscEdit {
                caption: "delete tsconfig".into(),
                expected_diff: "incremental reports config read error while clean build without tsconfig prints usage help".into(),
                edit: runner::edit(|sys| {
                    sys.remove_no_error("/home/src/workspaces/project/tsconfig.json");
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch handles tsconfig with extends base modified".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    "const x = null; const y: string = x;".into(),
                ),
                (
                    "/home/src/workspaces/project/base.json",
                    "{\n\t\"compilerOptions\": { \"strict\": false }\n}".into(),
                ),
                (
                    "/home/src/workspaces/project/tsconfig.json",
                    "{\n\t\"extends\": \"./base.json\"\n}".into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit(
                "modify base config to enable strict",
                |sys| {
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/base.json",
                        "{\n\t\"compilerOptions\": { \"strict\": true }\n}",
                    );
                },
            )],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch rebuilds when tsconfig is touched but content unchanged".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    "const x = 1;".into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit(
                "touch tsconfig without changing content",
                |sys| {
                    let content =
                        sys.read_file_no_error("/home/src/workspaces/project/tsconfig.json");
                    sys.write_file_no_error("/home/src/workspaces/project/tsconfig.json", &content);
                },
            )],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch with tsconfig files list entry deleted".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/a.ts",
                    "export const a = 1;".into(),
                ),
                (
                    "/home/src/workspaces/project/b.ts",
                    "export const b = 2;".into(),
                ),
                (
                    "/home/src/workspaces/project/tsconfig.json",
                    "{\n\t\"compilerOptions\": {},\n\t\"files\": [\"a.ts\", \"b.ts\"]\n}".into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit("delete file listed in files array", |sys| {
                sys.remove_no_error("/home/src/workspaces/project/b.ts");
            })],
            ..Default::default()
        },
        // Module resolution & dependencies
        TscInput {
            sub_scenario: "watch detects module going missing then coming back".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import { util } from "./util";"#.into(),
                ),
                (
                    "/home/src/workspaces/project/util.ts",
                    r#"export const util = "v1";"#.into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![
                TscEdit {
                    caption: "delete util module".into(),
                    edit: runner::edit(|sys| {
                        sys.remove_no_error("/home/src/workspaces/project/util.ts");
                    }),
                    expected_diff: "incremental resolves to .js output from prior build while clean build cannot find module".into(),
                    ..Default::default()
                },
                new_tsc_edit("recreate util module with new content", |sys| {
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/util.ts",
                        r#"export const util = "v2";"#,
                    );
                }),
            ],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch detects scoped package installed".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import { lib } from "@scope/mylib";"#.into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit("install scoped package", |sys| {
                sys.write_file_no_error(
                    "/home/src/workspaces/project/node_modules/@scope/mylib/package.json",
                    r#"{"name": "@scope/mylib", "types": "index.d.ts"}"#,
                );
                sys.write_file_no_error(
                    "/home/src/workspaces/project/node_modules/@scope/mylib/index.d.ts",
                    "export declare const lib: string;",
                );
            })],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch detects package json types field edited".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import { lib } from "mylib";"#.into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
                (
                    "/home/src/workspaces/project/node_modules/mylib/package.json",
                    r#"{"name": "mylib", "types": "old.d.ts"}"#.into(),
                ),
                (
                    "/home/src/workspaces/project/node_modules/mylib/old.d.ts",
                    "export declare const lib: number;".into(),
                ),
                (
                    "/home/src/workspaces/project/node_modules/mylib/new.d.ts",
                    "export declare const lib: string;".into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit("change package.json types field", |sys| {
                sys.write_file_no_error(
                    "/home/src/workspaces/project/node_modules/mylib/package.json",
                    r#"{"name": "mylib", "types": "new.d.ts"}"#,
                );
            })],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch detects at-types package installed later".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import * as lib from "untyped-lib";"#.into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
                (
                    "/home/src/workspaces/project/node_modules/untyped-lib/index.js",
                    "module.exports = {};".into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit("install @types for the library", |sys| {
                sys.write_file_no_error(
                    "/home/src/workspaces/project/node_modules/@types/untyped-lib/index.d.ts",
                    r#"declare module "untyped-lib" { export const value: string; }"#,
                );
                sys.write_file_no_error(
                    "/home/src/workspaces/project/node_modules/@types/untyped-lib/package.json",
                    r#"{"name": "@types/untyped-lib", "types": "index.d.ts"}"#,
                );
            })],
            ..Default::default()
        },
        // File operations
        TscInput {
            sub_scenario: "watch detects file renamed and renamed back".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import { helper } from "./helper";"#.into(),
                ),
                (
                    "/home/src/workspaces/project/helper.ts",
                    "export const helper = 1;".into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![
                TscEdit {
                    caption: "rename helper to helper2".into(),
                    edit: runner::edit(|sys| {
                        sys.rename_file_no_error(
                            "/home/src/workspaces/project/helper.ts",
                            "/home/src/workspaces/project/helper2.ts",
                        );
                    }),
                    expected_diff: "incremental resolves to .js output from prior build while clean build cannot find module".into(),
                    ..Default::default()
                },
                new_tsc_edit("rename back to helper", |sys| {
                    sys.rename_file_no_error(
                        "/home/src/workspaces/project/helper2.ts",
                        "/home/src/workspaces/project/helper.ts",
                    );
                }),
            ],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch detects file deleted and new file added simultaneously".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/a.ts",
                    r#"import { b } from "./b";"#.into(),
                ),
                (
                    "/home/src/workspaces/project/b.ts",
                    "export const b = 1;".into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit(
                "delete b.ts and create c.ts with updated import",
                |sys| {
                    sys.remove_no_error("/home/src/workspaces/project/b.ts");
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/c.ts",
                        "export const c = 2;",
                    );
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/a.ts",
                        r#"import { c } from "./c";"#,
                    );
                },
            )],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "watch handles file rapidly recreated".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import { val } from "./data";"#.into(),
                ),
                (
                    "/home/src/workspaces/project/data.ts",
                    r#"export const val = "original";"#.into(),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit(
                "delete and immediately recreate with new content",
                |sys| {
                    sys.remove_no_error("/home/src/workspaces/project/data.ts");
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/data.ts",
                        r#"export const val = "recreated";"#,
                    );
                },
            )],
            ..Default::default()
        },
        // Symlinks: only node_modules symlinks are resolved via Realpath,
        // matching the TypeScript compiler's behavior (see program.ts:2119).
        TscInput {
            sub_scenario: "watch detects change in symlinked node_modules file".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    r#"import { shared } from "shared";"#.into(),
                ),
                (
                    "/home/src/workspaces/shared/index.ts",
                    r#"export const shared = "v1";"#.into(),
                ),
                (
                    "/home/src/workspaces/project/node_modules/shared/index.ts",
                    symlink("/home/src/workspaces/shared/index.ts"),
                ),
                ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit("modify symlink target", |sys| {
                sys.write_file_no_error(
                    "/home/src/workspaces/shared/index.ts",
                    r#"export const shared = "v2";"#,
                );
            })],
            ..Default::default()
        },
        // Ancestor fallback stability: when a tsconfig include references a
        // directory that doesn't exist
        TscInput {
            sub_scenario: "watch stability with ancestor directory fallback".into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    "const x: number = 1;".into(),
                ),
                (
                    "/home/src/workspaces/project/tsconfig.json",
                    r#"{ "include": ["*.ts", "missing/**/*"] }"#.into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit("trivial file change", |sys| {
                sys.write_file_no_error(
                    "/home/src/workspaces/project/index.ts",
                    "const x: number = 2;",
                );
            })],
            ..Default::default()
        },
        // Ancestor fallback: creating deeply nested directories that didn't
        // exist at initial build time should trigger a rebuild and re-watch.
        TscInput {
            sub_scenario: "watch detects file added in deeply nested non-existent include path"
                .into(),
            files: file_map([
                (
                    "/home/src/workspaces/project/index.ts",
                    "const x: number = 1;".into(),
                ),
                (
                    "/home/src/workspaces/project/tsconfig.json",
                    r#"{ "include": ["*.ts", "deep/nested/dir/**/*"] }"#.into(),
                ),
            ]),
            command_line_args: args(["--watch"]),
            edits: vec![new_tsc_edit(
                "create deeply nested file matching include",
                |sys| {
                    sys.write_file_no_error(
                        "/home/src/workspaces/project/deep/nested/dir/added.ts",
                        "export const added = 1;",
                    );
                },
            )],
            ..Default::default()
        },
    ];

    run_tsc_inputs("commandLineWatch", test_cases, WatchFilter::WatchOnly);
}

// Go: tscwatch_test.go:563 listToTsconfig
fn list_to_tsconfig(base: &str, tsconfig_opts: &[&str]) -> (String, String) {
    let option_string = tsconfig_opts.join(",\n            ");
    let mut tsconfig_text = String::from("{\n\t\"compilerOptions\": {\n");
    let mut after = "            ";
    if !base.is_empty() {
        tsconfig_text += "            ";
        tsconfig_text += base;
        after = ",\n            ";
    }
    if !tsconfig_opts.is_empty() {
        tsconfig_text += after;
        tsconfig_text += &option_string;
    }
    tsconfig_text += "\n\t}\n}";
    (tsconfig_text, option_string)
}

// Go: tscwatch_test.go:582 toTsconfig
fn to_tsconfig(base: &str, compiler_opts: &str) -> String {
    let (tsconfig_text, _) = list_to_tsconfig(base, &[compiler_opts]);
    tsconfig_text
}

// Go: tscwatch_test.go:587 noEmitWatchTestInput
// PORT: Go `tsconfigOptions ...string` called with `nil` is an empty slice.
fn no_emit_watch_test_input(
    sub_scenario: &str,
    command_line_args: Vec<String>,
    a_text: &str,
    tsconfig_options: &[&str],
) -> TscInput {
    const A_TS: &str = "/home/src/workspaces/project/a.ts";
    const TSCONFIG: &str = "/home/src/workspaces/project/tsconfig.json";
    let no_emit_opt = r#""noEmit": true"#;
    let (tsconfig_text, option_string) = list_to_tsconfig(no_emit_opt, tsconfig_options);
    TscInput {
        sub_scenario: sub_scenario.to_string(),
        command_line_args,
        files: file_map([(A_TS, a_text.into()), (TSCONFIG, tsconfig_text.into())]),
        edits: vec![
            new_tsc_edit("fix error", |sys| {
                sys.write_file_no_error(A_TS, r#"const a = "hello";"#);
            }),
            new_tsc_edit("emit after fixing error", {
                let option_string = option_string.clone();
                move |sys: &TestSys| {
                    sys.write_file_no_error(TSCONFIG, &to_tsconfig("", &option_string));
                }
            }),
            new_tsc_edit("no emit run after fixing error", {
                let option_string = option_string.clone();
                move |sys: &TestSys| {
                    sys.write_file_no_error(TSCONFIG, &to_tsconfig(no_emit_opt, &option_string));
                }
            }),
            new_tsc_edit("introduce error", {
                let a_text = a_text.to_string();
                move |sys: &TestSys| {
                    sys.write_file_no_error(A_TS, &a_text);
                }
            }),
            new_tsc_edit("emit when error", {
                let option_string = option_string.clone();
                move |sys: &TestSys| {
                    sys.write_file_no_error(TSCONFIG, &to_tsconfig("", &option_string));
                }
            }),
            new_tsc_edit("no emit run when error", {
                let option_string = option_string.clone();
                move |sys: &TestSys| {
                    sys.write_file_no_error(TSCONFIG, &to_tsconfig(no_emit_opt, &option_string));
                }
            }),
        ],
        ..Default::default()
    }
}

// Go: tscwatch_test.go:625 newTscEdit
fn new_tsc_edit(name: &str, edit: impl Fn(&TestSys) + Send + Sync + 'static) -> TscEdit {
    TscEdit {
        caption: name.to_string(),
        edit: runner::edit(edit),
        ..Default::default()
    }
}

// Go: tscwatch_test.go:629 TestTscNoEmitWatch
#[test]
fn tsc_no_emit_watch_watch() {
    let test_cases = vec![
        no_emit_watch_test_input("syntax errors", args(["-w"]), "const a = \"hello", &[]),
        no_emit_watch_test_input(
            "semantic errors",
            args(["-w"]),
            "const a: number = \"hello\"",
            &[],
        ),
        no_emit_watch_test_input(
            "dts errors without dts enabled",
            args(["-w"]),
            "const a = class { private p = 10; };",
            &[],
        ),
        no_emit_watch_test_input(
            "dts errors",
            args(["-w"]),
            "const a = class { private p = 10; };",
            &[r#""declaration": true"#],
        ),
    ];

    run_tsc_inputs("noEmit", test_cases, WatchFilter::WatchOnly);
}
