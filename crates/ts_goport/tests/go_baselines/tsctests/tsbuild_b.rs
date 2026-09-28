//! Go: internal/execute/tsctests/tscbuild_test.go:1914-4317, from
//! `TestBuildProgramUpdates` to
//! `TestBuildProjectReferenceRedirectWithMultipleSubProjects`.
//!
//! Each Go test function is one `#[test]` for its non-watch inputs. When it
//! has watch inputs, one more `_watch` test runs those
//! (`support::runner`). Inputs keep the Go order, so each baseline gets the same
//! inputs as in Go.
//!
//! PORT: Go `FileMap` values are `any` holding a string. The helpers read
//! and change them as text through `file_text`.

use crate::support::harnessutil::FAKE_TS_VERSION;
use crate::support::runner::{
    FileMap, TscEdit, TscInput, WatchFilter, edit, no_change, no_change_only_edit, run_tsc_inputs,
};
use crate::support::stringtestutil::{dedent, go_sprintf};
use crate::support::test_sys::{TSC_LIB_PATH, get_test_lib_path_for};
use crate::support::vfstest::{MapFile, symlink};
use ts_goport::core::version;

/// Go `FileMap{"path": value, ...}`. Each value goes through `MapFile::from`.
// PORT: a local copy of `support::runner::file_map!`, so this file does not
// depend on how that macro is exported.
macro_rules! file_map {
    ($($path:expr => $value:expr),* $(,)?) => {{
        let mut files = FileMap::new();
        $(files.insert(String::from($path), MapFile::from($value));)*
        files
    }};
}

/// Go `[]string{...}` for command line arguments.
// PORT: a local copy of `support::runner::args!`, for the same reason.
macro_rules! args {
    ($($arg:expr),* $(,)?) => {
        vec![$(String::from($arg)),*]
    };
}

/// Returns the text of a `FileMap` value (Go `text.(string)`).
fn file_text(files: &FileMap, path: &str) -> String {
    String::from_utf8(files[path].data.clone()).expect("FileMap value is text")
}

// Go: tscbuild_test.go:1914 TestBuildProgramUpdates
fn program_updates_inputs() -> Vec<TscInput> {
    vec![
        TscInput {
            sub_scenario: "when referenced project change introduces error in the down stream project and then fixes it".into(),
            files: file_map! {
                "/user/username/projects/sample1/Library/tsconfig.json" => dedent(r#"
				{ 
					"compilerOptions": {
						"composite": true
					}
				}"#),
                "/user/username/projects/sample1/Library/library.ts" => dedent(r#"
					interface SomeObject
					{
						message: string;
					}

					export function createSomeObject(): SomeObject
					{
						return {
							message: "new Object"
						};
					}
				"#),
                "/user/username/projects/sample1/App/tsconfig.json" => dedent(r#"
				{ 
					"references": [{ "path": "../Library" }]
				}"#),
                "/user/username/projects/sample1/App/app.ts" => dedent(r#"
					import { createSomeObject } from "../Library/library";
					createSomeObject().message;
				"#),
            },
            cwd: "/user/username/projects/sample1".into(),
            command_line_args: args!["-b", "-w", "App"],
            edits: vec![
                TscEdit {
                    caption: "Introduce error".into(),
                    // Change message in library to message2
                    edit: edit(|sys| {
                        sys.replace_file_text_all(
                            "/user/username/projects/sample1/Library/library.ts",
                            "message",
                            "message2",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "Fix error".into(),
                    // Revert library changes
                    edit: edit(|sys| {
                        sys.replace_file_text_all(
                            "/user/username/projects/sample1/Library/library.ts",
                            "message2",
                            "message",
                        );
                    }),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "declarationEmitErrors when fixing error files all files are emitted".into(),
            files: file_map! {
                "/user/username/projects/solution/app/fileWithError.ts" => dedent(r"
					export var myClassWithError = class {
						tags() { }
						private p = 12
					};
				"),
                "/user/username/projects/solution/app/fileWithoutError.ts" => "export class myClass { }",
                "/user/username/projects/solution/app/tsconfig.json" => dedent(r#"
				{
					"compilerOptions": {
						"composite": true
					}
				}"#),
            },
            cwd: "/user/username/projects/solution".into(),
            command_line_args: args!["-b", "-w", "app"],
            edits: vec![TscEdit {
                caption: "Fix error".into(),
                edit: edit(|sys| {
                    sys.replace_file_text(
                        "/user/username/projects/solution/app/fileWithError.ts",
                        "private p = 12",
                        "",
                    );
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "declarationEmitErrors when file with no error changes".into(),
            files: file_map! {
                "/user/username/projects/solution/app/fileWithError.ts" => dedent(r"
					export var myClassWithError = class {
						tags() { }
						private p = 12
					};
				"),
                "/user/username/projects/solution/app/fileWithoutError.ts" => "export class myClass { }",
                "/user/username/projects/solution/app/tsconfig.json" => dedent(r#"
				{
					"compilerOptions": {
						"composite": true
					}
				}"#),
            },
            cwd: "/user/username/projects/solution".into(),
            command_line_args: args!["-b", "-w", "app"],
            edits: vec![TscEdit {
                caption: "Change fileWithoutError".into(),
                edit: edit(|sys| {
                    sys.replace_file_text_all(
                        "/user/username/projects/solution/app/fileWithoutError.ts",
                        "myClass",
                        "myClass2",
                    );
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "declarationEmitErrors introduceError when fixing errors only changed file is emitted".into(),
            files: file_map! {
                "/user/username/projects/solution/app/fileWithError.ts" => dedent(r"
					export var myClassWithError = class {
						tags() { }
						
					};
				"),
                "/user/username/projects/solution/app/fileWithoutError.ts" => "export class myClass { }",
                "/user/username/projects/solution/app/tsconfig.json" => dedent(r#"
				{
					"compilerOptions": {
						"composite": true
					}
				}"#),
            },
            cwd: "/user/username/projects/solution".into(),
            command_line_args: args!["-b", "-w", "app"],
            edits: vec![
                TscEdit {
                    caption: "Introduce error".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/user/username/projects/solution/app/fileWithError.ts",
                            &dedent(r"
							export var myClassWithError = class {
								tags() { }
								private p = 12
							};
						"),
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "Fix error".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/user/username/projects/solution/app/fileWithError.ts",
                            "private p = 12",
                            "",
                        );
                    }),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "declarationEmitErrors introduceError when file with no error changes".into(),
            files: file_map! {
                "/user/username/projects/solution/app/fileWithError.ts" => dedent(r"
					export var myClassWithError = class {
						tags() { }
						
					};
				"),
                "/user/username/projects/solution/app/fileWithoutError.ts" => "export class myClass { }",
                "/user/username/projects/solution/app/tsconfig.json" => dedent(r#"
				{
					"compilerOptions": {
						"composite": true
					}
				}"#),
            },
            cwd: "/user/username/projects/solution".into(),
            command_line_args: args!["-b", "-w", "app"],
            edits: vec![
                TscEdit {
                    caption: "Introduce error".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/user/username/projects/solution/app/fileWithError.ts",
                            &dedent(r"
							export var myClassWithError = class {
								tags() { }
								private p = 12
							};
						"),
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "Change fileWithoutError".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text_all(
                            "/user/username/projects/solution/app/fileWithoutError.ts",
                            "myClass",
                            "myClass2",
                        );
                    }),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "works when noUnusedParameters changes to false".into(),
            files: file_map! {
                "/user/username/projects/myproject/index.ts" => "const fn = (a: string, b: string) => b;",
                "/user/username/projects/myproject/tsconfig.json" => dedent(r#"
				{
					"compilerOptions": {
						"noUnusedParameters": true,
					},
				}"#),
            },
            cwd: "/user/username/projects/myproject".into(),
            command_line_args: args!["-b", "-w"],

            edits: vec![TscEdit {
                caption: "Change tsconfig to set noUnusedParameters to false".into(),
                edit: edit(|sys| {
                    sys.write_file_no_error("/user/username/projects/myproject/tsconfig.json", &dedent(r#"
							{
								"compilerOptions": {
									"noUnusedParameters": false,
								},
							}"#));
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "works with extended source files".into(),
            cwd: "/user/username/projects/project".into(),
            files: file_map! {
                "/user/username/projects/project/commonFile1.ts" => "let x = 1",
                "/user/username/projects/project/commonFile2.ts" => "let y = 1",
                "/user/username/projects/project/alpha.tsconfig.json" => "{}",
                "/user/username/projects/project/project1.tsconfig.json" => dedent(r#"
					{
						"extends": "./alpha.tsconfig.json",
						"compilerOptions": {
							"composite": true,
						},
						"files": ["commonFile1.ts", "commonFile2.ts"],
					}
				"#),
                "/user/username/projects/project/bravo.tsconfig.json" => dedent(r#"
					{
						"extends": "./alpha.tsconfig.json",
					}
				"#),
                "/user/username/projects/project/other.ts" => "let z = 0;",
                "/user/username/projects/project/project2.tsconfig.json" => dedent(r#"
					{
						"extends": "./bravo.tsconfig.json",
						"compilerOptions": {
							"composite": true,
						},
						"files": ["other.ts"],
					}
				"#),
                "/user/username/projects/project/other2.ts" => "let k = 0;",
                "/user/username/projects/project/extendsConfig1.tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
						},
					}
				"#),
                "/user/username/projects/project/extendsConfig2.tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"strictNullChecks": false,
						},
					}
				"#),
                "/user/username/projects/project/extendsConfig3.tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"noImplicitAny": true,
						},
					}
				"#),
                "/user/username/projects/project/project3.tsconfig.json" => dedent(r#"
				{
                    "extends": [
                        "./extendsConfig1.tsconfig.json",
                        "./extendsConfig2.tsconfig.json",
                        "./extendsConfig3.tsconfig.json",
                    ],
                    "compilerOptions": {
                        "composite": false,
                    },
                    "files": ["other2.ts"],
                }"#),
            },
            command_line_args: args![
                "-b",
                "-w",
                "-v",
                "project1.tsconfig.json",
                "project2.tsconfig.json",
                "project3.tsconfig.json"
            ],
            edits: vec![
                TscEdit {
                    caption: "Modify alpha config".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/user/username/projects/project/alpha.tsconfig.json",
                            &dedent(r#"
						{
                            "compilerOptions": {
								"strict": true
							}
                        }"#),
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "change bravo config".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/user/username/projects/project/bravo.tsconfig.json",
                            &dedent(r#"
						{
                            "extends": "./alpha.tsconfig.json",
                            "compilerOptions": { "strict": false }
                        }"#),
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "project 2 extends alpha".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/user/username/projects/project/project2.tsconfig.json",
                            &dedent(r#"
						{
                            "extends": "./alpha.tsconfig.json",
                            "files": ["other.ts"]
                        }"#),
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "update aplha config".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/user/username/projects/project/alpha.tsconfig.json",
                            "{}",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "Modify extendsConfigFile2".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/user/username/projects/project/extendsConfig2.tsconfig.json",
                            &dedent(r#"
						{
                            "compilerOptions": { "strictNullChecks": true }
                        }"#),
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "Modify project 3".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/user/username/projects/project/project3.tsconfig.json",
                            &dedent(r#"
						{
                            "extends": ["./extendsConfig1.tsconfig.json", "./extendsConfig2.tsconfig.json"],
                            "compilerOptions": { "composite": false },
                            "files": ["other2.ts"],
                        }"#),
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "Delete extendedConfigFile2 and report error".into(),
                    edit: edit(|sys| {
                        sys.remove_no_error(
                            "/user/username/projects/project/extendsConfig2.tsconfig.json",
                        );
                    }),
                    ..Default::default()
                },
            ],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "works correctly when project with extended config is removed".into(),
            files: file_map! {
                "/user/username/projects/project/commonFile1.ts" => "let x = 1",
                "/user/username/projects/project/commonFile2.ts" => "let y = 1",
                "/user/username/projects/project/alpha.tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": {
                        "strict": true,
                    },
                }"#),
                "/user/username/projects/project/project1.tsconfig.json" => dedent(r#"
				{
                    "extends": "./alpha.tsconfig.json",
                    "compilerOptions": {
                        "composite": true,
                    },
                    "files": ["commonFile1.ts", "commonFile2.ts"],
                }"#),
                "/user/username/projects/project/bravo.tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": {
                        "strict": true,
                    },
                }"#),
                "/user/username/projects/project/other.ts" => "let z = 0;",
                "/user/username/projects/project/project2.tsconfig.json" => dedent(r#"
				{
                    "extends": "./bravo.tsconfig.json",
                    "compilerOptions": {
                        "composite": true,
                    },
                    "files": ["other.ts"],
                }"#),
                "/user/username/projects/project/tsconfig.json" => dedent(r#"
				{
                    "references": [
                        {
                            "path": "./project1.tsconfig.json",
                        },
                        {
                            "path": "./project2.tsconfig.json",
                        },
                    ],
                    "files": [],
                }"#),
            },
            cwd: "/user/username/projects/project".into(),
            command_line_args: args!["-b", "-w", "-v"],
            edits: vec![TscEdit {
                caption: "Remove project2 from base config".into(),
                edit: edit(|sys| {
                    sys.write_file_no_error(
                        "/user/username/projects/project/tsconfig.json",
                        &dedent(r#"
						{
                            "references": [
                                {
                                    "path": "./project1.tsconfig.json",
                                },
                            ],
                            "files": [],
                        }"#),
                    );
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "tsbuildinfo has error".into(),
            files: file_map! {
                "/user/username/projects/project/main.ts" => "export const x = 10;",
                "/user/username/projects/project/tsconfig.json" => "{}",
                "/user/username/projects/project/tsconfig.tsbuildinfo" => "Some random string",
            },
            cwd: "/user/username/projects/project".into(),
            command_line_args: args!["--b", "-i", "-w"],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "tsbuildinfo has fewer fileInfos than fileNames".into(),
            files: file_map! {
                "/user/username/projects/project/src/a.ts" => "export const a = 1;",
                "/user/username/projects/project/src/b.ts" => "export const b = 2;",
                "/user/username/projects/project/tsconfig.json" => r#"{"compilerOptions":{"composite":true,"outDir":"dist"},"files":["src/a.ts","src/b.ts"]}"#,
                "/user/username/projects/project/dist/tsconfig.tsbuildinfo" => r#"{
					"version": "FakeTSVersion",
					"fileNames": ["lib.es2025.full.d.ts", "../src/a.ts", "../src/b.ts"],
					"fileInfos": ["abc123"],
					"options": {"composite": true, "outDir": "./"},
					"root": [2, 3]
				}"#,
            },
            cwd: "/user/username/projects/project".into(),
            command_line_args: args!["--b", "-v"],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "when root is source from project reference".into(),
            files: file_map! {
                "/home/src/workspaces/project/lib/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"outDir": "./dist"
						}
					}"#),
                "/home/src/workspaces/project/lib/foo.ts" => "export const FOO: string = 'THEFOOEXPORT';",
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
					{
						"references": [ { "path": "./lib" } ]
					}"#),
                "/home/src/workspaces/project/index.ts" => r#"import { FOO } from "./lib/foo";"#,
            },
            command_line_args: args!["--b"],
            edits: vec![TscEdit {
                caption: "dts doesnt change".into(),
                edit: edit(|sys| {
                    sys.append_file("/home/src/workspaces/project/lib/foo.ts", "const Bar = 10;");
                }),
                ..Default::default()
            }],
            cwd: "/home/src/workspaces/project".into(),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "when root is source from project reference with composite".into(),
            files: file_map! {
                "/home/src/workspaces/project/lib/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
							"outDir": "./dist"
						}
					}"#),
                "/home/src/workspaces/project/lib/foo.ts" => "export const FOO: string = 'THEFOOEXPORT';",
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"composite": true,
						},
						"references": [ { "path": "./lib" } ]
					}"#),
                "/home/src/workspaces/project/index.ts" => r#"import { FOO } from "./lib/foo";"#,
            },
            command_line_args: args!["--b"],
            edits: vec![TscEdit {
                caption: "dts doesnt change".into(),
                edit: edit(|sys| {
                    sys.append_file("/home/src/workspaces/project/lib/foo.ts", "const Bar = 10;");
                }),
                ..Default::default()
            }],
            cwd: "/home/src/workspaces/project".into(),
            ..Default::default()
        },
    ]
}

#[test]
fn build_program_updates() {
    run_tsc_inputs(
        "programUpdates",
        program_updates_inputs(),
        WatchFilter::NonWatch,
    );
}

#[test]
fn build_program_updates_watch() {
    run_tsc_inputs(
        "programUpdates",
        program_updates_inputs(),
        WatchFilter::WatchOnly,
    );
}

// Go: tscbuild_test.go:2406 TestBuildProjectsBuilding
fn projects_building_inputs() -> Vec<TscInput> {
    // Go: tscbuild_test.go:2408 addPackageFiles
    fn add_package_files(files: &mut FileMap, index: usize) {
        files.insert(
            go_sprintf(
                "/user/username/projects/myproject/pkg%d/index.ts",
                &[&index],
            ),
            go_sprintf("export const pkg%d = %d;", &[&index, &index]).into(),
        );
        let references = if index > 0 {
            r#""references": [{ "path": "../pkg0" }],"#
        } else {
            ""
        };
        files.insert(
            go_sprintf(
                "/user/username/projects/myproject/pkg%d/tsconfig.json",
                &[&index],
            ),
            dedent(&go_sprintf(
                r#"
		{
			"compilerOptions": { "composite": true },
			%s
		}"#,
                &[&references],
            ))
            .into(),
        );
    }
    // Go: tscbuild_test.go:2420 addSolution
    fn add_solution(files: &mut FileMap, count: usize) {
        let mut pkg_references = Vec::new();
        for i in 0..count {
            pkg_references.push(go_sprintf(r#"{ "path": "./pkg%d" }"#, &[&i]));
        }
        files.insert(
            "/user/username/projects/myproject/tsconfig.json".to_string(),
            dedent(&go_sprintf(
                r#"
		{
			"compilerOptions": { "composite": true },
			"references": [
				%s
			]
		}"#,
                &[&pkg_references.join(",\n\t\t\t\t")],
            ))
            .into(),
        );
    }
    // Go: tscbuild_test.go:2433 files
    fn files(count: usize) -> FileMap {
        let mut files = FileMap::new();
        for i in 0..count {
            add_package_files(&mut files, i);
        }
        add_solution(&mut files, count);
        files
    }

    // Go: tscbuild_test.go:2442 getTestCases
    fn get_test_cases(pkg_count: usize, builders: usize) -> Vec<TscInput> {
        let edits = vec![
            TscEdit {
                caption: "dts doesn't change".into(),
                edit: edit(|sys| {
                    sys.append_file(
                        "/user/username/projects/myproject/pkg0/index.ts",
                        "const someConst2 = 10;",
                    );
                }),
                ..Default::default()
            },
            no_change(),
            TscEdit {
                caption: "dts change".into(),
                edit: edit(|sys| {
                    sys.append_file(
                        "/user/username/projects/myproject/pkg0/index.ts",
                        "export const someConst = 10;",
                    );
                }),
                ..Default::default()
            },
            no_change(),
        ];
        vec![
            TscInput {
                sub_scenario: go_sprintf("when there are %d projects in a solution", &[&pkg_count]),
                files: files(pkg_count),
                cwd: "/user/username/projects/myproject".into(),
                command_line_args: args!["-b", "-v"],
                edits: edits.clone(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: go_sprintf(
                    "when there are %d projects in a solution with --builders %d",
                    &[&pkg_count, &builders],
                ),
                files: files(pkg_count),
                cwd: "/user/username/projects/myproject".into(),
                command_line_args: args!["-b", "-v", "--builders", builders.to_string()],
                edits: edits.clone(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: go_sprintf("when there are %d projects in a solution", &[&pkg_count]),
                files: files(pkg_count),
                cwd: "/user/username/projects/myproject".into(),
                command_line_args: args!["-b", "-w", "-v"],
                edits: edits.clone(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: go_sprintf(
                    "when there are %d projects in a solution with --builders %d",
                    &[&pkg_count, &builders],
                ),
                files: files(pkg_count),
                cwd: "/user/username/projects/myproject".into(),
                command_line_args: args!["-b", "-w", "-v", "--builders", builders.to_string()],
                edits,
                ..Default::default()
            },
        ]
    }

    [
        get_test_cases(3, 1),
        get_test_cases(5, 2),
        get_test_cases(8, 3),
        get_test_cases(23, 3),
    ]
    .concat()
}

#[test]
fn build_projects_building() {
    run_tsc_inputs(
        "projectsBuilding",
        projects_building_inputs(),
        WatchFilter::NonWatch,
    );
}

#[test]
fn build_projects_building_watch() {
    run_tsc_inputs(
        "projectsBuilding",
        projects_building_inputs(),
        WatchFilter::WatchOnly,
    );
}

// Go: tscbuild_test.go:2503 TestBuildProjectReferenceWithRootDirInParent
#[test]
fn build_project_reference_with_root_dir_in_parent() {
    // Go: tscbuild_test.go:2505 getBuildProjectReferenceWithRootDirInParentFileMap
    fn get_build_project_reference_with_root_dir_in_parent_file_map(
        modify: Option<fn(&mut FileMap)>,
    ) -> FileMap {
        let mut files = file_map! {
            "/home/src/workspaces/solution/src/main/a.ts" => dedent(r"
				import { b } from './b';
				const a = b;
			"),
            "/home/src/workspaces/solution/src/main/b.ts" => dedent(r"
				export const b = 0;
			"),
            "/home/src/workspaces/solution/src/main/tsconfig.json" => dedent(r#"
			{
				"extends": "../../tsconfig.base.json",
				"references": [
					{ "path": "../other" },
				],
			}"#),
            "/home/src/workspaces/solution/src/other/other.ts" => dedent(r"
				export const Other = 0;
			"),
            "/home/src/workspaces/solution/src/other/tsconfig.json" => dedent(r#"
			{
				"extends": "../../tsconfig.base.json",
			}
			"#),
            "/home/src/workspaces/solution/tsconfig.base.json" => dedent(r#"
			{
				"compilerOptions": {
					"composite": true,
					"declaration": true,
					"rootDir": "./src/",
					"outDir": "./dist/",
					"skipDefaultLibCheck": true,
				},
				"exclude": [
					"node_modules",
				],
			}"#),
        };
        if let Some(modify) = modify {
            modify(&mut files);
        }
        files
    }
    let test_cases = vec![
        TscInput {
            sub_scenario: "builds correctly".into(),
            files: get_build_project_reference_with_root_dir_in_parent_file_map(None),
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args!["--b", "src/main", "/home/src/workspaces/solution/src/other"],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "reports error for same tsbuildinfo file because no rootDir in the base"
                .into(),
            files: get_build_project_reference_with_root_dir_in_parent_file_map(Some(
                |files: &mut FileMap| {
                    let text = file_text(files, "/home/src/workspaces/solution/tsconfig.base.json");
                    files.insert(
                        "/home/src/workspaces/solution/tsconfig.base.json".into(),
                        text.replacen(r#""rootDir": "./src/","#, "", 1).into(),
                    );
                },
            )),
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args!["--b", "src/main", "--verbose"],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "reports error for same tsbuildinfo file".into(),
            files: get_build_project_reference_with_root_dir_in_parent_file_map(Some(
                |files: &mut FileMap| {
                    files.insert(
                        "/home/src/workspaces/solution/src/main/tsconfig.json".into(),
                        dedent(
                            r#"
                    {
                        "compilerOptions": { "composite": true, "outDir": "../../dist/" },
                        "references": [{ "path": "../other" }]
                    }"#,
                        )
                        .into(),
                    );
                    files.insert(
                        "/home/src/workspaces/solution/src/other/tsconfig.json".into(),
                        dedent(
                            r#"
                    {
                        "compilerOptions": { "composite": true, "outDir": "../../dist/" },
                    }"#,
                        )
                        .into(),
                    );
                },
            )),
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args!["--b", "src/main", "--verbose"],
            edits: no_change_only_edit(),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "reports error for same tsbuildinfo file without incremental".into(),
            files: get_build_project_reference_with_root_dir_in_parent_file_map(Some(
                |files: &mut FileMap| {
                    files.insert(
                        "/home/src/workspaces/solution/src/main/tsconfig.json".into(),
                        dedent(
                            r#"
                    {
                        "compilerOptions": { "outDir": "../../dist/" },
                        "references": [{ "path": "../other" }]
                    }"#,
                        )
                        .into(),
                    );
                    files.insert(
                        "/home/src/workspaces/solution/src/other/tsconfig.json".into(),
                        dedent(
                            r#"
                    {
                        "compilerOptions": { "composite": true, "outDir": "../../dist/" },
                    }"#,
                        )
                        .into(),
                    );
                },
            )),
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args!["--b", "src/main", "--verbose"],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "reports error for same tsbuildinfo file without incremental with tsc"
                .into(),
            files: get_build_project_reference_with_root_dir_in_parent_file_map(Some(
                |files: &mut FileMap| {
                    files.insert(
                        "/home/src/workspaces/solution/src/main/tsconfig.json".into(),
                        dedent(
                            r#"
                    {
                        "compilerOptions": { "outDir": "../../dist/" },
                        "references": [{ "path": "../other" }]
                    }"#,
                        )
                        .into(),
                    );
                    files.insert(
                        "/home/src/workspaces/solution/src/other/tsconfig.json".into(),
                        dedent(
                            r#"
                    {
                        "compilerOptions": { "composite": true, "outDir": "../../dist/" },
                    }"#,
                        )
                        .into(),
                    );
                },
            )),
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args!["--b", "src/other", "--verbose"],
            edits: vec![TscEdit {
                caption: "Running tsc on main".into(),
                command_line_args: Some(args!["-p", "src/main"]),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "reports no error when tsbuildinfo differ".into(),
            files: get_build_project_reference_with_root_dir_in_parent_file_map(Some(
                |files: &mut FileMap| {
                    files.remove("/home/src/workspaces/solution/src/main/tsconfig.json");
                    files.remove("/home/src/workspaces/solution/src/other/tsconfig.json");
                    files.insert(
                        "/home/src/workspaces/solution/src/main/tsconfig.main.json".into(),
                        dedent(
                            r#"
                    {
                        "compilerOptions": { "composite": true, "outDir": "../../dist/" },
                        "references": [{ "path": "../other/tsconfig.other.json" }]
                    }"#,
                        )
                        .into(),
                    );
                    files.insert(
                        "/home/src/workspaces/solution/src/other/tsconfig.other.json".into(),
                        dedent(
                            r#"
                    {
                        "compilerOptions": { "composite": true, "outDir": "../../dist/" },
                    }"#,
                        )
                        .into(),
                    );
                },
            )),
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args!["--b", "src/main/tsconfig.main.json", "--verbose"],
            edits: no_change_only_edit(),
            ..Default::default()
        },
    ];

    run_tsc_inputs(
        "projectReferenceWithRootDirInParent",
        test_cases,
        WatchFilter::NonWatch,
    );
}

// Go: tscbuild_test.go:2655 TestBuildReexport
// PORT: every input of this Go test is a watch input, so there is no
// non-watch test.
fn reexport_inputs() -> Vec<TscInput> {
    vec![TscInput {
        sub_scenario: "Reports errors correctly".into(),
        files: file_map! {
            "/user/username/projects/reexport/src/tsconfig.json" => dedent(r#"
				{
                    "files": [],
                    "include": [],
                    "references": [{ "path": "./pure" }, { "path": "./main" }],
                }"#),
            "/user/username/projects/reexport/src/main/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": {
                        "outDir": "../../out",
                        "rootDir": "../",
                    },
                    "include": ["**/*.ts"],
                    "references": [{ "path": "../pure" }],
                }"#),
            "/user/username/projects/reexport/src/main/index.ts" => dedent(r#"
                    import { Session } from "../pure";

                    export const session: Session = {
                        foo: 1
                    };
                "#),
            "/user/username/projects/reexport/src/pure/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": {
                        "composite": true,
                        "outDir": "../../out",
                        "rootDir": "../",
                    },
                    "include": ["**/*.ts"],
                }"#),
            "/user/username/projects/reexport/src/pure/index.ts" => r#"export * from "./session";"#,
            "/user/username/projects/reexport/src/pure/session.ts" => dedent(r"
                    export interface Session {
                        foo: number;
                        // bar: number;
                    }
                "),
        },
        cwd: "/user/username/projects/reexport".into(),
        command_line_args: args!["-b", "-w", "-verbose", "src"],
        edits: vec![
            TscEdit {
                caption: "Introduce error".into(),
                edit: edit(|sys| {
                    sys.replace_file_text(
                        "/user/username/projects/reexport/src/pure/session.ts",
                        "// ",
                        "",
                    );
                }),
                ..Default::default()
            },
            TscEdit {
                caption: "Fix error".into(),
                edit: edit(|sys| {
                    sys.replace_file_text(
                        "/user/username/projects/reexport/src/pure/session.ts",
                        "bar: ",
                        "// bar: ",
                    );
                }),
                ..Default::default()
            },
        ],
        ..Default::default()
    }]
}

#[test]
fn build_reexport_watch() {
    run_tsc_inputs("reexport", reexport_inputs(), WatchFilter::WatchOnly);
}

// Go: tscbuild_test.go:2724 TestBuildResolveJsonModule
#[test]
fn build_resolve_json_module() {
    // Go: tscbuild_test.go:2726 buildResolveJsonModuleScenario
    #[derive(Default)]
    struct BuildResolveJsonModuleScenario {
        sub_scenario: &'static str,
        tsconfig_files: &'static str,
        additional_compiler_options: &'static str,
        skip_outdir: bool,
        modify_files: Option<fn(&mut FileMap)>,
        edits: Vec<TscEdit>,
    }
    // Go: tscbuild_test.go:2734 getBuildResolveJsonModuleFileMap
    fn get_build_resolve_json_module_file_map(
        composite: bool,
        s: &BuildResolveJsonModuleScenario,
    ) -> FileMap {
        let out_dir_str = if s.skip_outdir {
            ""
        } else {
            r#""outDir": "dist","#
        };
        let mut files = file_map! {
            "/home/src/workspaces/solution/project/src/hello.json" => dedent(r#"
			{
				"hello": "world"
			}"#),
            "/home/src/workspaces/solution/project/src/index.ts" => dedent(r#"
				import hello from "./hello.json"
				export default hello.hello
			"#),
            "/home/src/workspaces/solution/project/tsconfig.json" => dedent(&go_sprintf(
                r#"
			{
				"compilerOptions": {
					"composite": %t,
					"module": "commonjs",
					"resolveJsonModule": true,
					"esModuleInterop": true,
					"allowSyntheticDefaultImports": true,
					%s
					"skipDefaultLibCheck": true,
					%s
				},
				%s
			}"#,
                &[&composite, &out_dir_str, &s.additional_compiler_options, &s.tsconfig_files],
            )),
        };
        if let Some(modify_files) = s.modify_files {
            modify_files(&mut files);
        }
        files
    }
    // Go: tscbuild_test.go:2768 getBuildResolveJsonModuleTestCases
    fn get_build_resolve_json_module_test_cases(
        scenarios: &[BuildResolveJsonModuleScenario],
    ) -> Vec<TscInput> {
        let mut test_cases = Vec::with_capacity(scenarios.len() * 2);
        for s in scenarios {
            test_cases.push(TscInput {
                sub_scenario: s.sub_scenario.into(),
                files: get_build_resolve_json_module_file_map(true, s),
                cwd: "/home/src/workspaces/solution".into(),
                command_line_args: args![
                    "--b",
                    "project",
                    "--v",
                    "--explainFiles",
                    "--listEmittedFiles"
                ],
                edits: s.edits.clone(),
                ..Default::default()
            });
            test_cases.push(TscInput {
                sub_scenario: s.sub_scenario.to_string() + " non-composite",
                files: get_build_resolve_json_module_file_map(false, s),
                cwd: "/home/src/workspaces/solution".into(),
                command_line_args: args![
                    "--b",
                    "project",
                    "--v",
                    "--explainFiles",
                    "--listEmittedFiles"
                ],
                edits: s.edits.clone(),
                ..Default::default()
            });
        }
        test_cases
    }
    let scenarios = vec![
        BuildResolveJsonModuleScenario {
            sub_scenario: "include only",
            tsconfig_files: r#""include": [ "src/**/*" ],"#,
            ..Default::default()
        },
        BuildResolveJsonModuleScenario {
            sub_scenario: "include only without outDir",
            tsconfig_files: r#""include": [ "src/**/*" ],"#,
            skip_outdir: true,
            ..Default::default()
        },
        BuildResolveJsonModuleScenario {
            sub_scenario: "include only with json not in rootDir",
            tsconfig_files: r#""include": [ "src/**/*" ],"#,
            additional_compiler_options: r#""rootDir": "src","#,
            modify_files: Some(|files: &mut FileMap| {
                // Go: text, _ := files[...]; delete(files, ...)
                let text = files
                    .remove("/home/src/workspaces/solution/project/src/hello.json")
                    .expect("hello.json is in the file map");
                files.insert(
                    "/home/src/workspaces/solution/project/hello.json".into(),
                    text,
                );
                let text = file_text(files, "/home/src/workspaces/solution/project/src/index.ts");
                files.insert(
                    "/home/src/workspaces/solution/project/src/index.ts".into(),
                    text.replacen("./hello.json", "../hello.json", 1).into(),
                );
            }),
            ..Default::default()
        },
        BuildResolveJsonModuleScenario {
            sub_scenario: "include only with json without rootDir but outside configDirectory",
            tsconfig_files: r#""include": [ "src/**/*" ],"#,
            modify_files: Some(|files: &mut FileMap| {
                // Go: text, _ := files[...]; delete(files, ...)
                let text = files
                    .remove("/home/src/workspaces/solution/project/src/hello.json")
                    .expect("hello.json is in the file map");
                files.insert("/home/src/workspaces/solution/hello.json".into(), text);
                let text = file_text(files, "/home/src/workspaces/solution/project/src/index.ts");
                files.insert(
                    "/home/src/workspaces/solution/project/src/index.ts".into(),
                    text.replacen("./hello.json", "../../hello.json", 1).into(),
                );
            }),
            ..Default::default()
        },
        BuildResolveJsonModuleScenario {
            sub_scenario: "include of json along with other include",
            tsconfig_files: r#""include": [ "src/**/*", "src/**/*.json" ],"#,
            ..Default::default()
        },
        BuildResolveJsonModuleScenario {
            sub_scenario: "include of json along with other include and file name matches ts file",
            tsconfig_files: r#""include": [ "src/**/*", "src/**/*.json" ],"#,
            modify_files: Some(|files: &mut FileMap| {
                // Go: text, _ := files[...]; delete(files, ...)
                let text = files
                    .remove("/home/src/workspaces/solution/project/src/hello.json")
                    .expect("hello.json is in the file map");
                files.insert(
                    "/home/src/workspaces/solution/project/src/index.json".into(),
                    text,
                );
                let text = file_text(files, "/home/src/workspaces/solution/project/src/index.ts");
                files.insert(
                    "/home/src/workspaces/solution/project/src/index.ts".into(),
                    text.replacen("./hello.json", "./index.json", 1).into(),
                );
            }),
            ..Default::default()
        },
        BuildResolveJsonModuleScenario {
            sub_scenario: "files containing json file",
            tsconfig_files: r#""files": [ "src/index.ts", "src/hello.json", ],"#,
            ..Default::default()
        },
        BuildResolveJsonModuleScenario {
            sub_scenario: "include and files",
            tsconfig_files: r#""files": [ "src/hello.json" ], "include": [ "src/**/*" ],"#,
            ..Default::default()
        },
        BuildResolveJsonModuleScenario {
            sub_scenario: "sourcemap",
            tsconfig_files: r#""files": [ "src/index.ts", "src/hello.json", ],"#,
            additional_compiler_options: r#""sourceMap": true,"#,
            edits: no_change_only_edit(),
            ..Default::default()
        },
        BuildResolveJsonModuleScenario {
            sub_scenario: "without outDir",
            tsconfig_files: r#""files": [ "src/index.ts", "src/hello.json", ],"#,
            skip_outdir: true,
            edits: no_change_only_edit(),
            ..Default::default()
        },
    ];
    let test_cases = [
        get_build_resolve_json_module_test_cases(&scenarios),
        vec![TscInput {
            sub_scenario: "importing json module from project reference".into(),
            files: file_map! {
                "/home/src/workspaces/solution/project/strings/foo.json" => dedent(r#"
						{
							"foo": "bar baz"
						}
					"#),
                "/home/src/workspaces/solution/project/strings/tsconfig.json" => dedent(r#"
						{
							"extends": "../tsconfig.json",
							"include": ["foo.json"],
							"references": [],
						}
					"#),
                "/home/src/workspaces/solution/project/main/index.ts" => dedent(r"
						import { foo } from '../strings/foo.json';
						console.log(foo);
					"),
                "/home/src/workspaces/solution/project/main/tsconfig.json" => dedent(r#"
						{
							"extends": "../tsconfig.json",
							"include": [
								"./**/*.ts",
							],
							"references": [{
								"path": "../strings/tsconfig.json",
							}],
						}
					"#),
                "/home/src/workspaces/solution/project/tsconfig.json" => dedent(r#"
						{
							"compilerOptions": {
								"target": "es5",
								"module": "commonjs",
								"rootDir": "./",
								"composite": true,
								"resolveJsonModule": true,
								"strict": true,
								"esModuleInterop": true,
							},
							"references": [
								{ "path": "./strings/tsconfig.json" },
								{ "path": "./main/tsconfig.json" },
							],
							"files": [],
						}
					"#),
            },
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args!["--b", "project", "--verbose", "--explainFiles"],
            edits: no_change_only_edit(),
            ..Default::default()
        }],
    ]
    .concat();

    run_tsc_inputs("resolveJsonModule", test_cases, WatchFilter::NonWatch);
}

// Go: tscbuild_test.go:2924 TestBuildRoots
fn roots_inputs() -> Vec<TscInput> {
    // Go: tscbuild_test.go:2926 getBuildRootsFromProjectReferencedProjectFileMap
    fn get_build_roots_from_project_referenced_project_file_map(server_first: bool) -> FileMap {
        let include = if server_first {
            r#""src/**/*.ts", "../shared/src/**/*.ts""#
        } else {
            r#""../shared/src/**/*.ts", "src/**/*.ts""#
        };
        file_map! {
            "/home/src/workspaces/solution/tsconfig.json" => dedent(r#"
			{
				"compilerOptions": {
					"composite": true,
				},
				"references": [
					{ "path": "projects/server" },
					{ "path": "projects/shared" },
				],
			}"#),
            "/home/src/workspaces/solution/projects/shared/src/myClass.ts" => "export class MyClass { }",
            "/home/src/workspaces/solution/projects/shared/src/logging.ts" => dedent(r"
				export function log(str: string) {
					console.log(str);
				}
			"),
            "/home/src/workspaces/solution/projects/shared/src/random.ts" => dedent(r"
				export function randomFn(str: string) {
					console.log(str);
				}
			"),
            "/home/src/workspaces/solution/projects/shared/tsconfig.json" => dedent(r#"
			{
				"extends": "../../tsconfig.json",
				"compilerOptions": {
					"outDir": "./dist",
				},
				"include": ["src/**/*.ts"],
			}"#),
            "/home/src/workspaces/solution/projects/server/src/server.ts" => dedent(r"
				import { MyClass } from ':shared/myClass.js';
				console.log('Hello, world!');
			"),
            "/home/src/workspaces/solution/projects/server/tsconfig.json" => dedent(&go_sprintf(r#"
			{
				"extends": "../../tsconfig.json",
				"compilerOptions": {
					"rootDir": "..",
					"outDir": "./dist",
					"paths": {
						":shared/*": ["./src/../../shared/src/*"],
					},
				},
				"include": [ %s ],
				"references": [
					{ "path": "../shared" },
				],
			}"#, &[&include])),
        }
    }
    // Go: tscbuild_test.go:2979 getBuildRootsFromProjectReferencedProjectTestEdits
    fn get_build_roots_from_project_referenced_project_test_edits() -> Vec<TscEdit> {
        vec![
            no_change(),
            TscEdit {
                caption: "edit logging file".into(),
                edit: edit(|sys| {
                    sys.append_file(
                        "/home/src/workspaces/solution/projects/shared/src/logging.ts",
                        "export const x = 10;",
                    );
                }),
                ..Default::default()
            },
            no_change(),
            TscEdit {
                caption: "delete random file".into(),
                edit: edit(|sys| {
                    sys.remove_no_error(
                        "/home/src/workspaces/solution/projects/shared/src/random.ts",
                    );
                }),
                ..Default::default()
            },
            no_change(),
        ]
    }
    vec![
        TscInput {
            sub_scenario: "when two root files are consecutive".into(),
            files: file_map! {
                "/home/src/workspaces/project/file1.ts" => r#"export const x = "hello";"#,
                "/home/src/workspaces/project/file2.ts" => r#"export const y = "world";"#,
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": { "composite": true },
                    "include": ["*.ts"],
                }"#),
            },
            command_line_args: args!["--b", "-v"],
            edits: vec![TscEdit {
                caption: "delete file1".into(),
                edit: edit(|sys| {
                    sys.remove_no_error("/home/src/workspaces/project/file1.ts");
                    sys.remove_no_error("/home/src/workspaces/project/file1.js");
                    sys.remove_no_error("/home/src/workspaces/project/file1.d.ts");
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "when multiple root files are consecutive".into(),
            files: file_map! {
                "/home/src/workspaces/project/file1.ts" => r#"export const x = "hello";"#,
                "/home/src/workspaces/project/file2.ts" => r#"export const y = "world";"#,
                "/home/src/workspaces/project/file3.ts" => r#"export const y = "world";"#,
                "/home/src/workspaces/project/file4.ts" => r#"export const y = "world";"#,
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": { "composite": true },
                    "include": ["*.ts"],
                }"#),
            },
            command_line_args: args!["--b", "-v"],
            edits: vec![TscEdit {
                caption: "delete file1".into(),
                edit: edit(|sys| {
                    sys.remove_no_error("/home/src/workspaces/project/file1.ts");
                    sys.remove_no_error("/home/src/workspaces/project/file1.js");
                    sys.remove_no_error("/home/src/workspaces/project/file1.d.ts");
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "when files are not consecutive".into(),
            files: file_map! {
                "/home/src/workspaces/project/file1.ts" => r#"export const x = "hello";"#,
                "/home/src/workspaces/project/random.d.ts" => r#"export const random = "world";"#,
                "/home/src/workspaces/project/file2.ts" => dedent(r#"
                    import { random } from "./random";
                    export const y = "world";
                "#),
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": { "composite": true },
                    "include": ["file*.ts"],
                }"#),
            },
            command_line_args: args!["--b", "-v"],
            edits: vec![TscEdit {
                caption: "delete file1".into(),
                edit: edit(|sys| {
                    sys.remove_no_error("/home/src/workspaces/project/file1.ts");
                    sys.remove_no_error("/home/src/workspaces/project/file1.js");
                    sys.remove_no_error("/home/src/workspaces/project/file1.d.ts");
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "when consecutive and non consecutive are mixed".into(),
            files: file_map! {
                "/home/src/workspaces/project/file1.ts" => r#"export const x = "hello";"#,
                "/home/src/workspaces/project/file2.ts" => r#"export const y = "world";"#,
                "/home/src/workspaces/project/random.d.ts" => r#"export const random = "hello";"#,
                "/home/src/workspaces/project/nonconsecutive.ts" => dedent(r#"
                import { random } from "./random";
					export const nonConsecutive = "hello";
				"#),
                "/home/src/workspaces/project/random1.d.ts" => r#"export const random = "hello";"#,
                "/home/src/workspaces/project/asArray1.ts" => dedent(r#"
					import { random } from "./random1";
					export const x = "hello";
				"#),
                "/home/src/workspaces/project/asArray2.ts" => r#"export const x = "hello";"#,
                "/home/src/workspaces/project/asArray3.ts" => r#"export const x = "hello";"#,
                "/home/src/workspaces/project/random2.d.ts" => r#"export const random = "hello";"#,
                "/home/src/workspaces/project/anotherNonConsecutive.ts" => dedent(r#"
					import { random } from "./random2";
					export const nonConsecutive = "hello";
				"#),
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
				{
                    "compilerOptions": { "composite": true },
                    "include": ["file*.ts", "nonconsecutive*.ts", "asArray*.ts", "anotherNonConsecutive.ts"],
                }"#),
            },
            command_line_args: args!["--b", "-v"],
            edits: vec![TscEdit {
                caption: "delete file1".into(),
                edit: edit(|sys| {
                    sys.remove_no_error("/home/src/workspaces/project/file1.ts");
                    sys.remove_no_error("/home/src/workspaces/project/file1.js");
                    sys.remove_no_error("/home/src/workspaces/project/file1.d.ts");
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "when root file is from referenced project".into(),
            files: get_build_roots_from_project_referenced_project_file_map(true),
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args![
                "--b",
                "projects/server",
                "-v",
                "--traceResolution",
                "--explainFiles"
            ],
            edits: get_build_roots_from_project_referenced_project_test_edits(),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "when root file is from referenced project and shared is first".into(),
            files: get_build_roots_from_project_referenced_project_file_map(false),
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args![
                "--b",
                "projects/server",
                "-v",
                "--traceResolution",
                "--explainFiles"
            ],
            edits: get_build_roots_from_project_referenced_project_test_edits(),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "when root file is from referenced project".into(),
            files: get_build_roots_from_project_referenced_project_file_map(true),
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args![
                "--b",
                "-w",
                "projects/server",
                "-v",
                "--traceResolution",
                "--explainFiles"
            ],
            edits: get_build_roots_from_project_referenced_project_test_edits(),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "when root file is from referenced project and shared is first".into(),
            files: get_build_roots_from_project_referenced_project_file_map(false),
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args![
                "--b",
                "-w",
                "projects/server",
                "-v",
                "--traceResolution",
                "--explainFiles"
            ],
            edits: get_build_roots_from_project_referenced_project_test_edits(),
            ..Default::default()
        },
    ]
}

#[test]
fn build_roots() {
    run_tsc_inputs("roots", roots_inputs(), WatchFilter::NonWatch);
}

#[test]
fn build_roots_watch() {
    run_tsc_inputs("roots", roots_inputs(), WatchFilter::WatchOnly);
}

// Go: tscbuild_test.go:3149 TestBuildSample
fn sample_inputs() -> Vec<TscInput> {
    // Go: tscbuild_test.go:3152 getLogicConfig
    fn get_logic_config() -> String {
        dedent(
            r#"
			{
				"compilerOptions": {
					"composite": true,
					"declaration": true,
					"sourceMap": true,
					"skipDefaultLibCheck": true,
				},
				"references": [
					{ "path": "../core" },
				],
			}"#,
        )
    }

    // Go: tscbuild_test.go:3167 getBuildSampleFileMap
    fn get_build_sample_file_map(modify: Option<fn(&mut FileMap)>) -> FileMap {
        let mut files = file_map! {
            "/user/username/projects/sample1/core/tsconfig.json" => dedent(r#"
			{
				"compilerOptions": {
					"composite": true,
					"declaration": true,
					"declarationMap": true,
					"skipDefaultLibCheck": true,
				},
			}"#),
            "/user/username/projects/sample1/core/index.ts" => dedent(r#"
				export const someString: string = "HELLO WORLD";
				export function leftPad(s: string, n: number) { return s + n; }
				export function multiply(a: number, b: number) { return a * b; }
			"#),
            "/user/username/projects/sample1/core/some_decl.d.ts" => "declare const dts: any;",
            "/user/username/projects/sample1/core/anotherModule.ts" => r#"export const World = "hello";"#,
            "/user/username/projects/sample1/logic/tsconfig.json" => get_logic_config(),
            "/user/username/projects/sample1/logic/index.ts" => dedent(r"
				import * as c from '../core/index';
				export function getSecondsInDay() {
					return c.multiply(10, 15);
				}
				import * as mod from '../core/anotherModule';
				export const m = mod;
			"),
            "/user/username/projects/sample1/tests/tsconfig.json" => dedent(r#"
			{
				"references": [
					{ "path": "../core" },
					{ "path": "../logic" },
				],
				"files": ["index.ts"],
				"compilerOptions": {
					"composite": true,
					"declaration": true,
					"skipDefaultLibCheck": true,
				},
			}"#),
            "/user/username/projects/sample1/tests/index.ts" => dedent(r#"
				import * as c from '../core/index';
				import * as logic from '../logic/index';

				c.leftPad("", 10);
				logic.getSecondsInDay();

				import * as mod from '../core/anotherModule';
				export const m = mod;
			"#),
        };
        if let Some(modify) = modify {
            modify(&mut files);
        }
        files
    }
    // Go: tscbuild_test.go:3223 getStopBuildOnErrorTests
    // PORT: Go `options == nil` is `options.is_none()`.
    fn get_stop_build_on_error_tests(options: Option<Vec<String>>) -> Vec<TscInput> {
        let no_change = if options.is_none() {
            no_change_only_edit()
        } else {
            Vec::new()
        };
        let options = options.unwrap_or_default();
        vec![
            TscInput {
                sub_scenario: "skips builds downstream projects if upstream projects have errors with stopBuildOnErrors".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    let text = file_text(files, "/user/username/projects/sample1/core/index.ts");
                    files.insert(
                        "/user/username/projects/sample1/core/index.ts".into(),
                        (text + "multiply();").into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: [
                    args!["--b", "tests", "--verbose", "--stopBuildOnErrors"],
                    options.clone(),
                ]
                .concat(),
                edits: [
                    no_change.clone(),
                    vec![TscEdit {
                        caption: "fix error".into(),
                        edit: edit(|sys| {
                            sys.replace_file_text(
                                "/user/username/projects/sample1/core/index.ts",
                                "multiply();",
                                "",
                            );
                        }),
                        ..Default::default()
                    }],
                ]
                .concat(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "skips builds downstream projects if upstream projects have errors with stopBuildOnErrors when test does not reference core".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    files.insert(
                        "/user/username/projects/sample1/tests/tsconfig.json".into(),
                        dedent(r#"
					{
						"references": [
							{ "path": "../logic" },
						],
						"files": ["index.ts"],
						"compilerOptions": {
							"composite": true,
							"declaration": true,
							"skipDefaultLibCheck": true,
						},
					}"#).into(),
                    );
                    let text = file_text(files, "/user/username/projects/sample1/core/index.ts");
                    files.insert(
                        "/user/username/projects/sample1/core/index.ts".into(),
                        (text + "multiply();").into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: [
                    args!["--b", "tests", "--verbose", "--stopBuildOnErrors"],
                    options.clone(),
                ]
                .concat(),
                edits: [
                    no_change.clone(),
                    vec![TscEdit {
                        caption: "fix error".into(),
                        edit: edit(|sys| {
                            sys.replace_file_text(
                                "/user/username/projects/sample1/core/index.ts",
                                "multiply();",
                                "",
                            );
                        }),
                        ..Default::default()
                    }],
                ]
                .concat(),
                ..Default::default()
            },
        ]
    }
    // Go: tscbuild_test.go:3280 getBuildSampleCoreChangeEdits
    fn get_build_sample_core_change_edits() -> Vec<TscEdit> {
        vec![
            TscEdit {
                caption: "incremental-declaration-changes".into(),
                edit: edit(|sys| {
                    sys.append_file(
                        "/user/username/projects/sample1/core/index.ts",
                        r"
export class someClass { }",
                    );
                }),
                ..Default::default()
            },
            TscEdit {
                caption: "incremental-declaration-doesnt-change".into(),
                edit: edit(|sys| {
                    sys.append_file(
                        "/user/username/projects/sample1/core/index.ts",
                        r"
class someClass2 { }",
                    );
                }),
                ..Default::default()
            },
            no_change(),
        ]
    }
    // Go: tscbuild_test.go:3305 getBuildSampleWatchDtsChangingEdits
    fn get_build_sample_watch_dts_changing_edits() -> Vec<TscEdit> {
        vec![
            TscEdit {
                caption: "Make change to core".into(),
                edit: edit(|sys| {
                    sys.append_file(
                        "/user/username/projects/sample1/core/index.ts",
                        "\nexport class someClass { }",
                    );
                }),
                ..Default::default()
            },
            TscEdit {
                caption: "Revert core file".into(),
                edit: edit(|sys| {
                    sys.replace_file_text(
                        "/user/username/projects/sample1/core/index.ts",
                        "\nexport class someClass { }",
                        "",
                    );
                }),
                ..Default::default()
            },
            TscEdit {
                caption: "Make two changes".into(),
                edit: edit(|sys| {
                    sys.append_file(
                        "/user/username/projects/sample1/core/index.ts",
                        "\nexport class someClass { }",
                    );
                    sys.append_file(
                        "/user/username/projects/sample1/core/index.ts",
                        "\nexport class someClass2 { }",
                    );
                }),
                ..Default::default()
            },
        ]
    }
    // Go: tscbuild_test.go:3328 getBuildSampleWatchNonDtsChangingEdits
    fn get_build_sample_watch_non_dts_changing_edits() -> Vec<TscEdit> {
        vec![TscEdit {
            caption: "Make local change to core".into(),
            edit: edit(|sys| {
                sys.append_file(
                    "/user/username/projects/sample1/core/index.ts",
                    "\nfunction foo() { }",
                );
            }),
            ..Default::default()
        }]
    }
    // Go: tscbuild_test.go:3338 getBuildSampleWatchNewFileEdits
    fn get_build_sample_watch_new_file_edits() -> Vec<TscEdit> {
        vec![
            TscEdit {
                caption: "Change to new File and build core".into(),
                edit: edit(|sys| {
                    sys.write_file_no_error(
                        "/user/username/projects/sample1/core/newfile.ts",
                        "export const newFileConst = 30;",
                    );
                }),
                ..Default::default()
            },
            TscEdit {
                caption: "Change to new File and build core".into(),
                edit: edit(|sys| {
                    sys.write_file_no_error(
                        "/user/username/projects/sample1/core/newfile.ts",
                        "\nexport class someClass2 { }",
                    );
                }),
                ..Default::default()
            },
        ]
    }
    // Go: tscbuild_test.go:3354 makeCircularReferences
    fn make_circular_references(files: &mut FileMap) {
        files.insert(
            "/user/username/projects/sample1/core/tsconfig.json".into(),
            dedent(
                r#"
		{
			"compilerOptions": {
				"composite": true,
				"declaration": true
			},
			"references": [
				{ "path": "../tests", "circular": true }
			],
		}"#,
            )
            .into(),
        );
    }
    // Go: tscbuild_test.go:3366 getIncrementalErrorTest
    fn get_incremental_error_test(sub_scenario: &str, options: &[&str]) -> TscInput {
        let mut expected_diff_with_logic_error = String::new();
        if options.contains(&"--stopBuildOnErrors") {
            expected_diff_with_logic_error = dedent(
                r"
				Clean build will stop on error in core and will not report error in logic
				Watch build will retain previous errors from logic and report it
			",
            );
        }
        let mut command_line_args = args!["-b", "-w", "tests"];
        command_line_args.extend(options.iter().map(std::string::ToString::to_string));
        TscInput {
            sub_scenario: "reportErrors ".to_string() + sub_scenario,
            files: get_build_sample_file_map(None),
            cwd: "/user/username/projects/sample1".into(),
            command_line_args,
            edits: vec![
                TscEdit {
                    caption: "change logic".into(),
                    edit: edit(|sys| {
                        sys.append_file(
                            "/user/username/projects/sample1/logic/index.ts",
                            "\nlet y: string = 10;",
                        );
                    }),
                    ..Default::default()
                },
                TscEdit {
                    caption: "change core".into(),
                    edit: edit(|sys| {
                        sys.append_file(
                            "/user/username/projects/sample1/core/index.ts",
                            "\nlet x: string = 10;",
                        );
                    }),
                    expected_diff: expected_diff_with_logic_error,
                    ..Default::default()
                },
                TscEdit {
                    caption: "fix error in logic".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/user/username/projects/sample1/logic/index.ts",
                            "\nlet y: string = 10;",
                            "",
                        );
                    }),
                    ..Default::default()
                },
            ],
            ..Default::default()
        }
    }
    [
        vec![
            TscInput {
                sub_scenario: "builds correctly when outDir is specified".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    files.insert(
                        "/user/username/projects/sample1/logic/tsconfig.json".into(),
                        dedent(r#"
				{
					"compilerOptions": {
						"composite": true,
						"declaration": true,
						"sourceMap": true,
						"outDir": "outDir",
					},
					"references": [
						{ "path": "../core" },
					],
				}"#).into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests"],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "builds correctly when declarationDir is specified".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    files.insert(
                        "/user/username/projects/sample1/logic/tsconfig.json".into(),
                        dedent(r#"
				{
					"compilerOptions": {
						"composite": true,
						"declaration": true,
						"sourceMap": true,
						"declarationDir": "out/decls",
					},
					"references": [
						{ "path": "../core" },
					],
				}"#).into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests"],
                ..Default::default()
            },
            TscInput {
                sub_scenario:
                    "builds correctly when project is not composite or doesnt have any references"
                        .into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    let text =
                        file_text(files, "/user/username/projects/sample1/core/tsconfig.json");
                    files.insert(
                        "/user/username/projects/sample1/core/tsconfig.json".into(),
                        text.replacen(r#""composite": true,"#, "", 1).into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "core", "--verbose"],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "does not write any files in a dry build".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--dry"],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "removes all files it built".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests"],
                edits: vec![
                    TscEdit {
                        caption: "removes all files it built".into(),
                        command_line_args: Some(args!["--b", "tests", "--clean"]),
                        ..Default::default()
                    },
                    TscEdit {
                        caption: "no change --clean".into(),
                        command_line_args: Some(args!["--b", "tests", "--clean"]),
                        ..Default::default()
                    },
                ],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "cleaning project in not build order doesnt throw error".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "logic2", "--clean"],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "always builds under with force option".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--force"],
                edits: no_change_only_edit(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "can detect when and what to rebuild".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--verbose"],
                edits: vec![
                    no_change(),
                    TscEdit {
                        // Update a file in the leaf node (tests), only it should rebuild the last one
                        caption: "Only builds the leaf node project".into(),
                        edit: edit(|sys| {
                            sys.write_file_no_error(
                                "/user/username/projects/sample1/tests/index.ts",
                                "const m = 10;",
                            );
                        }),
                        ..Default::default()
                    },
                    TscEdit {
                        // Update a file in the parent (without affecting types), should get fast downstream builds
                        caption: "Detects type-only changes in upstream projects".into(),
                        edit: edit(|sys| {
                            sys.replace_file_text(
                                "/user/username/projects/sample1/core/index.ts",
                                "HELLO WORLD",
                                "WELCOME PLANET",
                            );
                        }),
                        ..Default::default()
                    },
                    TscEdit {
                        caption: "rebuilds when tsconfig changes".into(),
                        edit: edit(|sys| {
                            sys.replace_file_text(
                                "/user/username/projects/sample1/tests/tsconfig.json",
                                r#""composite": true"#,
                                r#""composite": true, "target": "es2020""#,
                            );
                        }),
                        ..Default::default()
                    },
                ],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "when input file text does not change but its modified time changes"
                    .into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--verbose"],
                edits: vec![TscEdit {
                    caption: "upstream project changes without changing file text".into(),
                    edit: edit(|sys| {
                        let err = sys.fs().chtimes(
                            "/user/username/projects/sample1/core/index.ts",
                            None,
                            Some(sys.now()),
                        );
                        if let Err(err) = err {
                            panic!("{err:?}");
                        }
                    }),
                    ..Default::default()
                }],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "when declarationMap changes".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--verbose"],
                edits: vec![
                    TscEdit {
                        caption: "Disable declarationMap".into(),
                        edit: edit(|sys| {
                            sys.replace_file_text(
                                "/user/username/projects/sample1/core/tsconfig.json",
                                r#""declarationMap": true,"#,
                                r#""declarationMap": false,"#,
                            );
                        }),
                        ..Default::default()
                    },
                    TscEdit {
                        caption: "Enable declarationMap".into(),
                        edit: edit(|sys| {
                            sys.replace_file_text(
                                "/user/username/projects/sample1/core/tsconfig.json",
                                r#""declarationMap": false,"#,
                                r#""declarationMap": true,"#,
                            );
                        }),
                        ..Default::default()
                    },
                ],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "indicates that it would skip builds during a dry build".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests"],
                edits: vec![TscEdit {
                    caption: "--dry".into(),
                    command_line_args: Some(args!["--b", "tests", "--dry"]),
                    ..Default::default()
                }],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "rebuilds from start if force option is set".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests"],
                edits: vec![TscEdit {
                    caption: "--force build".into(),
                    command_line_args: Some(args!["--b", "tests", "--verbose", "--force"]),
                    ..Default::default()
                }],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "tsbuildinfo has error".into(),
                files: file_map! {
                    "/home/src/workspaces/project/main.ts" => "export const x = 10;",
                    "/home/src/workspaces/project/tsconfig.json" => "{}",
                    "/home/src/workspaces/project/tsconfig.tsbuildinfo" => "Some random string",
                },
                command_line_args: args!["--b", "-i", "-v"],
                edits: vec![TscEdit {
                    caption: "tsbuildinfo written has error".into(),
                    edit: edit(|sys| {
                        // This is to ensure the non incremental doesnt crash - as it wont have tsbuildInfo
                        if !sys.for_incremental_correctness() {
                            sys.prepend_file(
                                "/home/src/workspaces/project/tsconfig.tsbuildinfo",
                                "Some random string",
                            );
                            sys.replace_file_text(
                                "/home/src/workspaces/project/tsconfig.tsbuildinfo",
                                &go_sprintf(r#""version":"%s""#, &[&version()]),
                                &go_sprintf(r#""version":"%s""#, &[&FAKE_TS_VERSION]),
                            ); // build info won't parse, need to manually sterilize for baseline
                        }
                    }),
                    ..Default::default()
                }],
                ..Default::default()
            },
            TscInput {
                sub_scenario:
                    "rebuilds completely when version in tsbuildinfo doesnt match ts version"
                        .into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--verbose"],
                edits: vec![TscEdit {
                    caption:
                        "convert tsbuildInfo version to something that is say to previous version"
                            .into(),
                    edit: edit(|sys| {
                        // This is to ensure the non incremental doesnt crash - as it wont have tsbuildInfo
                        if !sys.for_incremental_correctness() {
                            sys.replace_file_text(
                                "/user/username/projects/sample1/core/tsconfig.tsbuildinfo",
                                &go_sprintf(r#""version":"%s""#, &[&FAKE_TS_VERSION]),
                                &go_sprintf(r#""version":"%s""#, &[&"FakeTsPreviousVersion"]),
                            );
                            sys.replace_file_text(
                                "/user/username/projects/sample1/logic/tsconfig.tsbuildinfo",
                                &go_sprintf(r#""version":"%s""#, &[&FAKE_TS_VERSION]),
                                &go_sprintf(r#""version":"%s""#, &[&"FakeTsPreviousVersion"]),
                            );
                            sys.replace_file_text(
                                "/user/username/projects/sample1/tests/tsconfig.tsbuildinfo",
                                &go_sprintf(r#""version":"%s""#, &[&FAKE_TS_VERSION]),
                                &go_sprintf(r#""version":"%s""#, &[&"FakeTsPreviousVersion"]),
                            );
                        }
                    }),
                    ..Default::default()
                }],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "rebuilds when extended config file changes".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    files.insert(
                        "/user/username/projects/sample1/tests/tsconfig.base.json".into(),
                        dedent(r#"
				{
					"compilerOptions": {
						"target": "es5"
					}
				}"#).into(),
                    );
                    let text =
                        file_text(files, "/user/username/projects/sample1/tests/tsconfig.json");
                    files.insert(
                        "/user/username/projects/sample1/tests/tsconfig.json".into(),
                        text.replacen(r#""references": ["#, r#""extends": "./tsconfig.base.json", "references": ["#, 1).into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--verbose"],
                edits: vec![TscEdit {
                    caption: "change extended file".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/user/username/projects/sample1/tests/tsconfig.base.json",
                            &dedent(r#"
						{
							"compilerOptions": { }
						}"#),
                        );
                    }),
                    ..Default::default()
                }],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "building project in not build order doesnt throw error".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "logic2/tsconfig.json", "--verbose"],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "builds downstream projects even if upstream projects have errors"
                    .into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    let text = file_text(files, "/user/username/projects/sample1/logic/index.ts");
                    files.insert(
                        "/user/username/projects/sample1/logic/index.ts".into(),
                        text.replacen("c.multiply(10, 15)", "c.muitply()", 1).into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--verbose"],
                edits: no_change_only_edit(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "listFiles".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--listFiles"],
                edits: get_build_sample_core_change_edits(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "listEmittedFiles".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--listEmittedFiles"],
                edits: get_build_sample_core_change_edits(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "explainFiles".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--explainFiles", "--v"],
                edits: get_build_sample_core_change_edits(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "sample".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--verbose"],
                edits: [
                    get_build_sample_core_change_edits(),
                    vec![
                        TscEdit {
                            caption: "when logic config changes declaration dir".into(),
                            edit: edit(|sys| {
                                sys.replace_file_text(
                                    "/user/username/projects/sample1/logic/tsconfig.json",
                                    r#""declaration": true,"#,
                                    r#""declaration": true,
        "declarationDir": "decls","#,
                                );
                            }),
                            ..Default::default()
                        },
                        no_change(),
                    ],
                ]
                .concat(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "when logic specifies tsBuildInfoFile".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    let text =
                        file_text(files, "/user/username/projects/sample1/logic/tsconfig.json");
                    files.insert(
                        "/user/username/projects/sample1/logic/tsconfig.json".into(),
                        text.replacen(r#""composite": true,"#, r#""composite": true,
    "tsBuildInfoFile": "ownFile.tsbuildinfo","#, 1).into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--verbose"],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "when declaration option changes".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    files.insert(
                        "/user/username/projects/sample1/core/tsconfig.json".into(),
                        dedent(r#"
				{
					"compilerOptions": {
						"incremental": true,
						"skipDefaultLibCheck": true,
					},
				}"#).into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "core", "--verbose"],
                edits: vec![TscEdit {
                    caption: "incremental-declaration-changes".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/user/username/projects/sample1/core/tsconfig.json",
                            r#""incremental": true,"#,
                            r#""incremental": true, "declaration": true,"#,
                        );
                    }),
                    ..Default::default()
                }],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "when target option changes".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    files.insert(get_test_lib_path_for("esnext.full"), r#"/// <reference no-default-lib="true"/>
/// <reference lib="esnext" />"#.into());
                    files.insert(TSC_LIB_PATH.to_string() + "/lib.d.ts", r#"/// <reference no-default-lib="true"/>
/// <reference lib="esnext" />"#.into());
                    files.insert(
                        "/user/username/projects/sample1/core/tsconfig.json".into(),
                        dedent(r#"
				{
					"compilerOptions": {
						"incremental": true,
						"listFiles": true,
						"listEmittedFiles": true,
						"target": "esnext",
					},
				}"#).into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "core", "--verbose"],
                edits: vec![TscEdit {
                    caption: "incremental-declaration-changes".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/user/username/projects/sample1/core/tsconfig.json",
                            "esnext",
                            "es5",
                        );
                    }),
                    ..Default::default()
                }],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "when module option changes".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    files.insert(
                        "/user/username/projects/sample1/core/tsconfig.json".into(),
                        dedent(r#"
				{
					"compilerOptions": {
						"incremental": true,
						"module": "node18",
					},
				}"#).into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "core", "--verbose"],
                edits: vec![TscEdit {
                    caption: "incremental-declaration-changes".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/user/username/projects/sample1/core/tsconfig.json",
                            "node18",
                            "nodenext",
                        );
                    }),
                    ..Default::default()
                }],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "when esModuleInterop option changes".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    files.insert(
                        "/user/username/projects/sample1/tests/tsconfig.json".into(),
                        dedent(r#"
				{
					"references": [
						{ "path": "../core" },
						{ "path": "../logic" },
					],
					"files": ["index.ts"],
					"compilerOptions": {
						"composite": true,
						"declaration": true,
						"skipDefaultLibCheck": true,
						"esModuleInterop": false,
					},
				}"#).into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--verbose"],
                edits: vec![TscEdit {
                    caption: "incremental-declaration-changes".into(),
                    edit: edit(|sys| {
                        sys.replace_file_text(
                            "/user/username/projects/sample1/tests/tsconfig.json",
                            r#""esModuleInterop": false"#,
                            r#""esModuleInterop": true"#,
                        );
                    }),
                    ..Default::default()
                }],
                ..Default::default()
            },
            TscInput {
                // !!! sheetal this is not reporting error as file not found is not yet implemented
                sub_scenario: "reports error if input file is missing".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    files.insert(
                        "/user/username/projects/sample1/core/tsconfig.json".into(),
                        dedent(r#"
				{
					 "compilerOptions": { "composite": true },
					 "files": ["anotherModule.ts", "index.ts", "some_decl.d.ts"],
				}"#).into(),
                    );
                    files.remove("/user/username/projects/sample1/core/anotherModule.ts");
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--verbose"],
                ..Default::default()
            },
            TscInput {
                // !!! sheetal this is not reporting error as file not found is not yet implemented
                sub_scenario: "reports error if input file is missing with force".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    files.insert(
                        "/user/username/projects/sample1/core/tsconfig.json".into(),
                        dedent(r#"
				{
					 "compilerOptions": { "composite": true },
					 "files": ["anotherModule.ts", "index.ts", "some_decl.d.ts"],
				}"#).into(),
                    );
                    files.remove("/user/username/projects/sample1/core/anotherModule.ts");
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "tests", "--verbose", "--force"],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "change builds changes and reports found errors message".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "-w", "tests"],
                edits: get_build_sample_watch_dts_changing_edits(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "non local change does not start build of referencing projects"
                    .into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "-w", "tests"],
                edits: get_build_sample_watch_non_dts_changing_edits(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "builds when new file is added, and its subsequent updates".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "-w", "tests"],
                edits: get_build_sample_watch_new_file_edits(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "change builds changes and reports found errors message with circular references".into(),
                files: get_build_sample_file_map(Some(make_circular_references)),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "-w", "tests"],
                edits: get_build_sample_watch_dts_changing_edits(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "non local change does not start build of referencing projects with circular references".into(),
                files: get_build_sample_file_map(Some(make_circular_references)),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "-w", "tests"],
                edits: get_build_sample_watch_non_dts_changing_edits(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "builds when new file is added, and its subsequent updates with circular references".into(),
                files: get_build_sample_file_map(Some(make_circular_references)),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "-w", "tests"],
                edits: get_build_sample_watch_new_file_edits(),
                ..Default::default()
            },
            TscInput {
                sub_scenario: "watches config files that are not present".into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    files.remove("/user/username/projects/sample1/logic/tsconfig.json");
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "-w", "tests"],
                edits: vec![TscEdit {
                    caption: "Write logic".into(),
                    edit: edit(|sys| {
                        sys.write_file_no_error(
                            "/user/username/projects/sample1/logic/tsconfig.json",
                            &get_logic_config(),
                        );
                    }),
                    ..Default::default()
                }],
                ..Default::default()
            },
            get_incremental_error_test("when preserveWatchOutput is not used", &[]),
            get_incremental_error_test(
                "when preserveWatchOutput is passed on command line",
                &["--preserveWatchOutput"],
            ),
            get_incremental_error_test(
                "when stopBuildOnErrors is passed on command line",
                &["--stopBuildOnErrors"],
            ),
            TscInput {
                sub_scenario: "incremental updates in verbose mode".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "-w", "tests", "--verbose"],
                edits: vec![
                    TscEdit {
                        caption: "Make non dts change".into(),
                        edit: edit(|sys| {
                            sys.append_file(
                                "/user/username/projects/sample1/logic/index.ts",
                                "\nfunction someFn() { }",
                            );
                        }),
                        ..Default::default()
                    },
                    TscEdit {
                        caption: "Make dts change".into(),
                        edit: edit(|sys| {
                            sys.replace_file_text(
                                "/user/username/projects/sample1/logic/index.ts",
                                "\nfunction someFn() { }",
                                "\nexport function someFn() { }",
                            );
                        }),
                        ..Default::default()
                    },
                ],
                ..Default::default()
            },
            TscInput {
                sub_scenario: "should not trigger recompilation because of program emit".into(),
                files: get_build_sample_file_map(None),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "-w", "core", "--verbose"],
                edits: vec![
                    no_change(),
                    TscEdit {
                        caption: "Add new file".into(),
                        edit: edit(|sys| {
                            sys.write_file_no_error(
                                "/user/username/projects/sample1/core/file3.ts",
                                "export const y = 10;",
                            );
                        }),
                        ..Default::default()
                    },
                    no_change(),
                ],
                ..Default::default()
            },
            TscInput {
                sub_scenario:
                    "should not trigger recompilation because of program emit with outDir specified"
                        .into(),
                files: get_build_sample_file_map(Some(|files: &mut FileMap| {
                    files.insert(
                        "/user/username/projects/sample1/core/tsconfig.json".into(),
                        dedent(r#"
				{
					"compilerOptions": {
						"composite": true,
						"outDir": "outDir"
					}
                }"#).into(),
                    );
                })),
                cwd: "/user/username/projects/sample1".into(),
                command_line_args: args!["--b", "-w", "core", "--verbose"],
                edits: vec![
                    no_change(),
                    TscEdit {
                        caption: "Add new file".into(),
                        edit: edit(|sys| {
                            sys.write_file_no_error(
                                "/user/username/projects/sample1/core/file3.ts",
                                "export const y = 10;",
                            );
                        }),
                        ..Default::default()
                    },
                    no_change(),
                ],
                ..Default::default()
            },
        ],
        get_stop_build_on_error_tests(None),
        get_stop_build_on_error_tests(Some(args!["--watch"])),
    ]
    .concat()
}

#[test]
fn build_sample() {
    run_tsc_inputs("sample", sample_inputs(), WatchFilter::NonWatch);
}

#[test]
fn build_sample_watch() {
    run_tsc_inputs("sample", sample_inputs(), WatchFilter::WatchOnly);
}

// Go: tscbuild_test.go:3973 TestBuildTransitiveReferences
#[test]
fn build_transitive_references() {
    // Go: tscbuild_test.go:3976 getBuildTransitiveReferencesFileMap
    fn get_build_transitive_references_file_map(modify: Option<fn(&mut FileMap)>) -> FileMap {
        let mut files = file_map! {
            "/user/username/projects/transitiveReferences/refs/a.d.ts" => dedent(r"
				export class X {}
				export class A {}
			"),
            "/user/username/projects/transitiveReferences/a.ts" => dedent(r"
				export class A {}
			"),
            "/user/username/projects/transitiveReferences/b.ts" => dedent(r"
				import {A} from '@ref/a';
				export const b = new A();
			"),
            "/user/username/projects/transitiveReferences/c.ts" => dedent(r#"
				import {b} from './b';
				import {X} from "@ref/a";
				b;
				X;
			"#),
            "/user/username/projects/transitiveReferences/tsconfig.a.json" => dedent(r#"
			{
				"files": ["a.ts"],
				"compilerOptions": {
					"composite": true,
				},
			}"#),
            "/user/username/projects/transitiveReferences/tsconfig.b.json" => dedent(r#"
			{
				"files": ["b.ts"],
				"compilerOptions": {
					"composite": true,
					"paths": {
						"@ref/*": ["./*"],
					},
				},
				"references": [{ "path": "tsconfig.a.json" }],
			}"#),
            "/user/username/projects/transitiveReferences/tsconfig.c.json" => dedent(r#"
			{
				"files": ["c.ts"],
				"compilerOptions": {
					"paths": {
						"@ref/*": ["./refs/*"],
					},
				},
				"references": [{ "path": "tsconfig.b.json" }],
			}"#),
        };
        if let Some(modify) = modify {
            modify(&mut files);
        }
        files
    }
    let test_cases = vec![
        TscInput {
            sub_scenario: "builds correctly".into(),
            files: get_build_transitive_references_file_map(None),
            cwd: "/user/username/projects/transitiveReferences".into(),
            command_line_args: args!["--b", "tsconfig.c.json", "--listFiles"],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "reports error about module not found with node resolution with external module name".into(),
            files: get_build_transitive_references_file_map(Some(|files: &mut FileMap| {
                files.insert(
                    "/user/username/projects/transitiveReferences/b.ts".into(),
                    r"import {A} from 'a';
export const b = new A();".into(),
                );
                files.insert(
                    "/user/username/projects/transitiveReferences/tsconfig.b.json".into(),
                    dedent(r#"
				{
					"files": ["b.ts"],
					"compilerOptions": {
						"composite": true,
						"module": "nodenext",
					},
					"references": [{ "path": "tsconfig.a.json" }],
				}"#).into(),
                );
            })),
            cwd: "/user/username/projects/transitiveReferences".into(),
            command_line_args: args!["--b", "tsconfig.c.json", "--listFiles"],
            ..Default::default()
        },
    ];

    run_tsc_inputs("transitiveReferences", test_cases, WatchFilter::NonWatch);
}

// Go: tscbuild_test.go:4061 TestBuildSolutionProject
#[test]
fn build_solution_project() {
    let test_cases = vec![
        TscInput {
            sub_scenario: "verify that subsequent builds after initial build doesnt build anything"
                .into(),
            files: file_map! {
                "/home/src/workspaces/solution/src/folder/index.ts" => "export const x = 10;",
                "/home/src/workspaces/solution/src/folder/tsconfig.json" => dedent(r#"
                    {
                        "files": ["index.ts"],
                        "compilerOptions": {
                            "composite": true
                        }
                    }
                "#),
                "/home/src/workspaces/solution/src/folder2/index.ts" => "export const x = 10;",
                "/home/src/workspaces/solution/src/folder2/tsconfig.json" => dedent(r#"
                    {
                        "files": ["index.ts"],
                        "compilerOptions": {
                            "composite": true
                        }
                    }
                "#),
                "/home/src/workspaces/solution/src/tsconfig.json" => dedent(r#"
                    {
                        "files": [],
                        "compilerOptions": {
                            "composite": true
                        },
						"references": [
							{ "path": "./folder" },
							{ "path": "./folder2" },
						]
                }"#),
                "/home/src/workspaces/solution/tests/index.ts" => "export const x = 10;",
                "/home/src/workspaces/solution/tests/tsconfig.json" => dedent(r#"
                    {
                        "files": ["index.ts"],
                        "compilerOptions": {
                            "composite": true
                        },
                        "references": [
                            { "path": "../src" }
                        ]
                    }
                "#),
                "/home/src/workspaces/solution/tsconfig.json" => dedent(r#"
                    {
                        "files": [],
                        "compilerOptions": {
                            "composite": true
                        },
                        "references": [
                            { "path": "./src" },
                            { "path": "./tests" }
                        ]
                    }
                "#),
            },
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args!["--b", "--v"],
            edits: no_change_only_edit(),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "when solution is referenced indirectly".into(),
            files: file_map! {
                "/home/src/workspaces/solution/project1/tsconfig.json" => dedent(r#"
                    {
                        "compilerOptions": { "composite": true },
                        "references": []
                    }
                "#),
                "/home/src/workspaces/solution/project2/tsconfig.json" => dedent(r#"
                    {
                        "compilerOptions": { "composite": true },
                        "references": []
                    }
                "#),
                "/home/src/workspaces/solution/project2/src/b.ts" => "export const b = 10;",
                "/home/src/workspaces/solution/project3/tsconfig.json" => dedent(r#"
                    {
                        "compilerOptions": { "composite": true },
                        "references": [
							{ "path": "../project1" },
							{ "path": "../project2" }
						]
                    }
                "#),
                "/home/src/workspaces/solution/project3/src/c.ts" => "export const c = 10;",
                "/home/src/workspaces/solution/project4/tsconfig.json" => dedent(r#"
                    {
                        "compilerOptions": { "composite": true },
                        "references": [{ "path": "../project3" }]
                    }
                "#),
                "/home/src/workspaces/solution/project4/src/d.ts" => "export const d = 10;",
            },
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args!["--b", "project4", "--verbose", "--explainFiles"],
            edits: vec![TscEdit {
                caption: "modify project3 file".into(),
                edit: edit(|sys| {
                    sys.replace_file_text(
                        "/home/src/workspaces/solution/project3/src/c.ts",
                        "c = ",
                        "cc = ",
                    );
                }),
                ..Default::default()
            }],
            ..Default::default()
        },
        TscInput {
            sub_scenario:
                "has empty files diagnostic when files is empty and no references are provided"
                    .into(),
            files: file_map! {
                "/home/src/workspaces/solution/no-references/tsconfig.json" => dedent(r#"
                    {
                        "references": [],
                        "files": [],
                        "compilerOptions": {
                            "composite": true,
                            "declaration": true,
                            "forceConsistentCasingInFileNames": true,
                            "skipDefaultLibCheck": true,
                        },
                    }"#),
            },
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args!["--b", "no-references"],
            ..Default::default()
        },
        TscInput {
            sub_scenario: "does not have empty files diagnostic when files is empty and references are provided".into(),
            files: file_map! {
                "/home/src/workspaces/solution/core/index.ts" => "export function multiply(a: number, b: number) { return a * b; }",
                "/home/src/workspaces/solution/core/tsconfig.json" => dedent(r#"
                    {
                        "compilerOptions": {
                            "composite": true,
                            "declaration": true,
                            "declarationMap": true,
                            "skipDefaultLibCheck": true,
                        },
                    }"#),
                "/home/src/workspaces/solution/with-references/tsconfig.json" => dedent(r#"
                    {
                        "references": [
                            { "path": "../core" },
                        ],
                        "files": [],
                        "compilerOptions": {
                            "composite": true,
                            "declaration": true,
                            "forceConsistentCasingInFileNames": true,
                            "skipDefaultLibCheck": true,
                        },
                    }"#),
            },
            cwd: "/home/src/workspaces/solution".into(),
            command_line_args: args!["--b", "with-references"],
            ..Default::default()
        },
    ];

    run_tsc_inputs("solution", test_cases, WatchFilter::NonWatch);
}

// Go: tscbuild_test.go:4225 TestBuildProjectReferenceRedirectWithMultipleSubProjects
#[test]
fn build_project_reference_redirect_with_multiple_sub_projects() {
    let test_cases = vec![TscInput {
        sub_scenario:
            "uses correct project reference redirect when file belongs to multiple sub-projects"
                .into(),
        files: file_map! {
            // Consumer tsconfig - uses customConditions and moduleSuffixes for react-native
            "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"module": "esnext",
							"moduleResolution": "bundler",
							"customConditions": ["react-native"],
							"moduleSuffixes": [".native", ""],
							"strict": true,
							"noEmit": true
						},
						"include": ["app.ts"],
						"references": [
							{ "path": "./pkg" }
						]
					}"#),
            // Consumer app - imports from pkg, expects native platform
            "/home/src/workspaces/project/app.ts" => dedent(r#"
					import { platform } from "pkg";
					const check: "native" = platform;"#),
            // Package - web tsconfig (includes all files via **/*)
            "/home/src/workspaces/project/pkg/tsconfig.json" => dedent(r#"
					{
						"compilerOptions": {
							"module": "esnext",
							"moduleResolution": "bundler",
							"composite": true,
							"declaration": true,
							"emitDeclarationOnly": true,
							"outDir": "./dist",
							"strict": true
						},
						"include": ["**/*"],
						"exclude": ["dist"],
						"references": [
							{ "path": "./tsconfig.native.json" }
						]
					}"#),
            // Package - native tsconfig (includes specific files, has customConditions)
            "/home/src/workspaces/project/pkg/tsconfig.native.json" => dedent(r#"
					{
						"compilerOptions": {
							"module": "esnext",
							"moduleResolution": "bundler",
							"composite": true,
							"declaration": true,
							"emitDeclarationOnly": true,
							"outDir": "./dist",
							"strict": true,
							"customConditions": ["react-native"],
							"moduleSuffixes": [".native", ""]
						},
						"include": ["index.native.ts", "src/util.native.ts", "src/util.ts"],
						"exclude": ["dist"]
					}"#),
            // Package exports - react-native condition maps to index.native.ts
            "/home/src/workspaces/project/pkg/package.json" => dedent(r#"
					{
						"name": "pkg",
						"exports": {
							".": {
								"react-native": "./index.native.ts",
								"types": "./index.ts",
								"default": "./index.ts"
							}
						}
					}"#),
            // Web entry point
            "/home/src/workspaces/project/pkg/index.ts" => r#"export { platform } from "./src/util";"#,
            // Native entry point (same content, but should resolve internal imports using native tsconfig)
            "/home/src/workspaces/project/pkg/index.native.ts" => r#"export { platform } from "./src/util";"#,
            // Web util
            "/home/src/workspaces/project/pkg/src/util.ts" => r#"export const platform = "web" as const;"#,
            // Native util
            "/home/src/workspaces/project/pkg/src/util.native.ts" => r#"export const platform = "native" as const;"#,
            // node_modules symlink
            "/home/src/workspaces/project/node_modules/pkg" => symlink("/home/src/workspaces/project/pkg"),
        },
        cwd: "/home/src/workspaces/project".into(),
        command_line_args: args!["--b", "--verbose"],
        ..Default::default()
    }];

    run_tsc_inputs(
        "projectReferenceRedirect",
        test_cases,
        WatchFilter::NonWatch,
    );
}
