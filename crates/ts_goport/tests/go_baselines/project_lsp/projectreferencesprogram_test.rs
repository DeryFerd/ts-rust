//! Port of Go `internal/project/projectreferencesprogram_test.go` (`TestProjectReferencesProgram`).

use ts_goport::ls::lsconv;
use ts_goport::project::Kind;

use super::projecttestutil::{self, FileMap, files};
use super::util::*;
use crate::support::vfstest;

const MAIN: &str = "/user/username/projects/myproject/main/main.ts";
const MAIN_URI: &str = "file:///user/username/projects/myproject/main/main.ts";

fn file_text(files: &FileMap, name: &str) -> String {
    String::from_utf8(files[name].data.clone()).unwrap()
}

/// The one project of the session, which must be configured.
fn only_configured_program(
    session: &std::rc::Rc<ts_goport::project::Session>,
) -> &'static ts_goport::frontend::compiler::NewProgram {
    let projects = session.snapshot().project_collection.projects();
    assert_eq!(projects.len(), 1);
    let p = projects[0].borrow();
    assert_eq!(p.kind, Kind::CONFIGURED);
    p.program.expect("program")
}

child_test! {
    // Go: projectreferencesprogram_test.go:26 TestProjectReferencesProgram/program for referenced project
    fn program_for_referenced_project() {
        let files = files_for_referenced_project_program(false);
        let (session, _) = projecttestutil::setup(files.clone());
        assert_eq!(projects_len(&session), 0);

        open(&session, MAIN_URI, &file_text(&files, MAIN));

        let program = only_configured_program(&session);
        let file = program.get_source_file_by_path(&path("/user/username/projects/myproject/dependency/fns.ts"));
        assert!(file.is_some());
        let dts_file = program.get_source_file_by_path(&path("/user/username/projects/myproject/decls/fns.d.ts"));
        assert!(dts_file.is_none());
    }
}

child_test! {
    // Go: projectreferencesprogram_test.go:48 TestProjectReferencesProgram/program with disableSourceOfProjectReferenceRedirect
    fn program_with_disable_source_of_project_reference_redirect() {
        let mut files = files_for_referenced_project_program(true);
        files.insert(
            "/user/username/projects/myproject/decls/fns.d.ts".into(),
            "
			export declare function fn1(): void;
			export declare function fn2(): void;
			export declare function fn3(): void;
			export declare function fn4(): void;
			export declare function fn5(): void;
		"
            .into(),
        );
        let (session, _) = projecttestutil::setup(files.clone());
        assert_eq!(projects_len(&session), 0);

        open(&session, MAIN_URI, &file_text(&files, MAIN));

        let program = only_configured_program(&session);
        let file = program.get_source_file_by_path(&path("/user/username/projects/myproject/dependency/fns.ts"));
        assert!(file.is_none());
        let dts_file = program.get_source_file_by_path(&path("/user/username/projects/myproject/decls/fns.d.ts"));
        assert!(dts_file.is_some());
    }
}

/// The body of the eight "references through symlink" subtests.
fn references_through_symlink(files: FileMap, a_test: &str, b_foo: &str, b_bar: &str) {
    let (session, _) = projecttestutil::setup(files.clone());
    assert_eq!(projects_len(&session), 0);

    let u = lsconv::file_name_to_document_uri(a_test);
    open(&session, &u.0, &file_text(&files, a_test));

    let program = only_configured_program(&session);
    assert!(program.get_source_file(b_foo).is_some());
    assert!(program.get_source_file(b_bar).is_some());
}

child_test! {
    // Go: projectreferencesprogram_test.go:77 TestProjectReferencesProgram/references through symlink with index and typings
    fn references_through_symlink_with_index_and_typings() {
        let (files, a, foo, bar) = files_for_symlink_references(false, "");
        references_through_symlink(files, a, foo, bar);
    }
}

child_test! {
    // Go: projectreferencesprogram_test.go:99 TestProjectReferencesProgram/references through symlink with index and typings with preserveSymlinks
    fn references_through_symlink_with_index_and_typings_with_preserve_symlinks() {
        let (files, a, foo, bar) = files_for_symlink_references(true, "");
        references_through_symlink(files, a, foo, bar);
    }
}

child_test! {
    // Go: projectreferencesprogram_test.go:121 TestProjectReferencesProgram/references through symlink with index and typings scoped package
    fn references_through_symlink_with_index_and_typings_scoped_package() {
        let (files, a, foo, bar) = files_for_symlink_references(false, "@issue/");
        references_through_symlink(files, a, foo, bar);
    }
}

child_test! {
    // Go: projectreferencesprogram_test.go:143 TestProjectReferencesProgram/references through symlink with index and typings with scoped package preserveSymlinks
    fn references_through_symlink_with_index_and_typings_with_scoped_package_preserve_symlinks() {
        let (files, a, foo, bar) = files_for_symlink_references(true, "@issue/");
        references_through_symlink(files, a, foo, bar);
    }
}

child_test! {
    // Go: projectreferencesprogram_test.go:165 TestProjectReferencesProgram/references through symlink referencing from subFolder
    fn references_through_symlink_referencing_from_sub_folder() {
        let (files, a, foo, bar) = files_for_symlink_references_in_subfolder(false, "");
        references_through_symlink(files, a, foo, bar);
    }
}

child_test! {
    // Go: projectreferencesprogram_test.go:187 TestProjectReferencesProgram/references through symlink referencing from subFolder with preserveSymlinks
    fn references_through_symlink_referencing_from_sub_folder_with_preserve_symlinks() {
        let (files, a, foo, bar) = files_for_symlink_references_in_subfolder(true, "");
        references_through_symlink(files, a, foo, bar);
    }
}

child_test! {
    // Go: projectreferencesprogram_test.go:209 TestProjectReferencesProgram/references through symlink referencing from subFolder scoped package
    fn references_through_symlink_referencing_from_sub_folder_scoped_package() {
        let (files, a, foo, bar) = files_for_symlink_references_in_subfolder(false, "@issue/");
        references_through_symlink(files, a, foo, bar);
    }
}

child_test! {
    // Go: projectreferencesprogram_test.go:231 TestProjectReferencesProgram/references through symlink referencing from subFolder with scoped package preserveSymlinks
    fn references_through_symlink_referencing_from_sub_folder_with_scoped_package_preserve_symlinks() {
        let (files, a, foo, bar) = files_for_symlink_references_in_subfolder(true, "@issue/");
        references_through_symlink(files, a, foo, bar);
    }
}

child_test! {
    // Go: projectreferencesprogram_test.go:253 TestProjectReferencesProgram/when new file is added to referenced project
    fn when_new_file_is_added_to_referenced_project() {
        let files = files_for_referenced_project_program(false);
        let (session, utils) = projecttestutil::setup(files.clone());
        open(&session, MAIN_URI, &file_text(&files, MAIN));
        assert_eq!(projects_len(&session), 1);
        let program_before = session.snapshot().project_collection.projects()[0]
            .borrow()
            .program
            .expect("program");

        utils
            .fs()
            .write_file("/user/username/projects/myproject/dependency/fns2.ts", "export const x = 2;")
            .unwrap();
        watch(&session, &[(CREATED, "file:///user/username/projects/myproject/dependency/fns2.ts")]);

        let _ = language_service(&session, MAIN_URI);
        assert_eq!(projects_len(&session), 1);
        let program_after = session.snapshot().project_collection.projects()[0]
            .borrow()
            .program
            .expect("program");
        assert!(!same_program(program_after, program_before));
    }
}

// Go: projectreferencesprogram_test.go:280 filesForReferencedProjectProgram
fn files_for_referenced_project_program(
    disable_source_of_project_reference_redirect: bool,
) -> FileMap {
    let extra = if disable_source_of_project_reference_redirect {
        r#", "disableSourceOfProjectReferenceRedirect": true"#
    } else {
        ""
    };
    let main_tsconfig = format!(
        r#"{{
			"compilerOptions": {{
				"composite": true{extra}
			}},
			"references": [{{ "path": "../dependency" }}]
		}}"#
    );
    files(&[
        (
            "/user/username/projects/myproject/main/tsconfig.json",
            main_tsconfig.as_str(),
        ),
        (
            MAIN,
            "
			import {
				fn1,
				fn2,
				fn3,
				fn4,
				fn5
			} from '../decls/fns'
			fn1();
			fn2();
			fn3();
			fn4();
			fn5();
		",
        ),
        (
            "/user/username/projects/myproject/dependency/tsconfig.json",
            r#"{
			"compilerOptions": {
				"composite": true,
				"declarationDir": "../decls"
			},
		}"#,
        ),
        (
            "/user/username/projects/myproject/dependency/fns.ts",
            "
			export function fn1() { }
			export function fn2() { }
			export function fn3() { }
			export function fn4() { }
			export function fn5() { }
		",
        ),
    ])
}

// Go: projectreferencesprogram_test.go:318 filesForSymlinkReferences
fn files_for_symlink_references(
    preserve_symlinks: bool,
    scope: &str,
) -> (FileMap, &'static str, &'static str, &'static str) {
    let a_test = "/user/username/projects/myproject/packages/A/src/index.ts";
    let b_foo = "/user/username/projects/myproject/packages/B/src/index.ts";
    let b_bar = "/user/username/projects/myproject/packages/B/src/bar.ts";
    let a_text = format!(
        "
			import {{ foo }} from '{scope}b';
			import {{ bar }} from '{scope}b/lib/bar';
			foo();
			bar();
		"
    );
    let mut files = files(&[
        (
            "/user/username/projects/myproject/packages/B/package.json",
            r#"{
			"main": "lib/index.js",
			"types": "lib/index.d.ts"
		}"#,
        ),
        (a_test, a_text.as_str()),
        (b_foo, "export function foo() { }"),
        (b_bar, "export function bar() { }"),
    ]);
    files.insert(
        format!("/user/username/projects/myproject/node_modules/{scope}b"),
        vfstest::symlink("/user/username/projects/myproject/packages/B"),
    );
    add_config_for_package(&mut files, "A", preserve_symlinks, &["../B"]);
    add_config_for_package(&mut files, "B", preserve_symlinks, &[]);
    (files, a_test, b_foo, b_bar)
}

// Go: projectreferencesprogram_test.go:342 filesForSymlinkReferencesInSubfolder
fn files_for_symlink_references_in_subfolder(
    preserve_symlinks: bool,
    scope: &str,
) -> (FileMap, &'static str, &'static str, &'static str) {
    let a_test = "/user/username/projects/myproject/packages/A/src/test.ts";
    let b_foo = "/user/username/projects/myproject/packages/B/src/foo.ts";
    let b_bar = "/user/username/projects/myproject/packages/B/src/bar/foo.ts";
    let a_text = format!(
        "
			import {{ foo }} from '{scope}b/lib/foo';
			import {{ bar }} from '{scope}b/lib/bar/foo';
			foo();
			bar();
		"
    );
    let mut files = files(&[
        (
            "/user/username/projects/myproject/packages/B/package.json",
            "{}",
        ),
        (a_test, a_text.as_str()),
        (b_foo, "export function foo() { }"),
        (b_bar, "export function bar() { }"),
    ]);
    files.insert(
        format!("/user/username/projects/myproject/node_modules/{scope}b"),
        vfstest::symlink("/user/username/projects/myproject/packages/B"),
    );
    add_config_for_package(&mut files, "A", preserve_symlinks, &["../B"]);
    add_config_for_package(&mut files, "B", preserve_symlinks, &[]);
    (files, a_test, b_foo, b_bar)
}

// Go: projectreferencesprogram_test.go:363 addConfigForPackage
// PORT: Go builds the JSON with `core.StringifyJson` of maps (sorted keys);
// a nil `references` slice is `null`.
fn add_config_for_package(
    files: &mut FileMap,
    package_name: &str,
    preserve_symlinks: bool,
    references: &[&str],
) {
    let preserve = if preserve_symlinks {
        ",\n        \"preserveSymlinks\": true"
    } else {
        ""
    };
    let references = if references.is_empty() {
        "null".to_string()
    } else {
        let items: Vec<String> = references
            .iter()
            .map(|r| format!("\n        {{\n          \"path\": \"{r}\"\n        }}"))
            .collect();
        format!("[{}\n    ]", items.join(","))
    };
    let text = format!(
        "{{\n    \"compilerOptions\": {{\n        \"composite\": true,\n        \"outDir\": \"lib\"{preserve},\n        \"rootDir\": \"src\"\n    }},\n    \"include\": [\n        \"src\"\n    ],\n    \"references\": {references}\n}}"
    );
    files.insert(
        format!("/user/username/projects/myproject/packages/{package_name}/tsconfig.json"),
        text.into(),
    );
}
