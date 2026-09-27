//! Port of Go `internal/project/projectcollectiondefaultproject_test.go`.

use super::projecttestutil::{self, files};
use super::util::*;

child_test! {
    // Go: projectcollectiondefaultproject_test.go:12 TestProjectCollectionDefaultProject
    fn project_collection_default_project() {
        // Project 1 references project 2, which does not have open files.
        // File project1/dist/index.d.ts does not belong to any tsconfig.json, but is included in programs for
        // projects 3 and 4 via project 1's output.
        // When looking for a default project for project1/dist/index.d.ts,
        // we should not try to unconditionally access project 2,
        // which isn't loaded because of `disableReferencedProjectLoad`.
        let entries: &[(&str, &str)] = &[
        ("/project1/tsconfig.json", r#"{
			"extends": "../tsconfig.json",
			"files": [],
			"include": ["src/**/*"],
			"references": [
				{
					"path": "../project2"
				}
			],
			"compilerOptions": {
				"composite": true,
				"outDir": "./dist",
				"rootDir": "./src",
			}
		}"#),
        ("/project1/src/index.ts", r#"export const foo = 42;
        export type Bar = { a: string };"#),
        ("/project1/dist/index.d.ts", r#"export declare const foo = 42;
			export type Bar = {
				a: string;
			};"#),
        ("/project2/tsconfig.json", r#"{
			"extends": "../tsconfig.json",
			"files": [],
			"include": ["src/**/*"],
			"compilerOptions": {
				"composite": true,
				"outDir": "./dist",
				"rootDir": "./src"
			}
		}"#),
        ("/project3/tsconfig.json", r#"{
			"extends": "../tsconfig.json",
			"files": [],
			"include": ["src/**/*"],
			"references": [
				{
					"path": "../project1"
				}
			],
			"compilerOptions": {
				"composite": true,
				"outDir": "./dist",
				"rootDir": "./src",
			}
		}"#),
        ("/project3/src/index.ts", r#"import { Bar } from "../../project1/dist/index.js";
			declare const b: Bar;
			const x: string = b.a;"#),
        ("/project4/tsconfig.json", r#"{
			"extends": "../tsconfig.json",
			"files": [],
			"include": ["src/**/*"],
			"references": [
				{
					"path": "../project1"
				}
			],
			"compilerOptions": {
				"composite": true,
				"outDir": "./dist",
				"rootDir": "./src",
			}
		}"#),
        ("/project4/src/index.ts", r#"import { Bar } from "../../project1/dist/index.js";
declare const b: Bar;
const x: string = b.a;"#),
        ("/tsconfig.json", r#"{
			"compilerOptions": {
				"disableReferencedProjectLoad": true,
				"disableSolutionSearching": true,
				"disableSourceOfProjectReferenceRedirect": true
			},
			"files": [],
			"references": [
				{
					"path": "./project1"
				},
				{
					"path": "./project2"
				},
				{
					"path": "./project3"
				},
				{
					"path": "./project4"
				}
			]
		}"#),
        ];
        let files = files(entries);
        let uris = [
            "file:///project1/dist/index.d.ts",
            "file:///project1/src/index.ts",
            "file:///project3/src/index.ts",
            "file:///project4/src/index.ts",
        ];
        let (session, _) = projecttestutil::setup(files.clone());
        // Should not crash.
        for u in uris {
            let content = String::from_utf8(files[&u[7..]].data.clone()).unwrap();
            open(&session, u, &content);
        }
    }
}
