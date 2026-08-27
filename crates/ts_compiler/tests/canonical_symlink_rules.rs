use std::{io, sync::Mutex};

use ts_ast::NodeData;
use ts_compiler::{Program, ProgramGraphMissingEvidence, ProgramGraphReferenceKind};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{DirectoryEntries, FileSystem, MemoryFileSystem};

struct ObservedFileSystem {
    files: MemoryFileSystem,
    realpaths: Mutex<Vec<(String, String)>>,
}

impl FileSystem for ObservedFileSystem {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.files.use_case_sensitive_file_names()
    }

    fn file_exists(&self, path: &str) -> bool {
        self.files.file_exists(path)
    }

    fn directory_exists(&self, path: &str) -> bool {
        self.files.directory_exists(path)
    }

    fn realpath(&self, path: &str) -> String {
        let result = self.files.realpath(path);
        self.realpaths
            .lock()
            .unwrap()
            .push((path.to_owned(), result.clone()));
        result
    }

    fn modified_time(&self, path: &str) -> Option<u128> {
        self.files.modified_time(path)
    }

    fn read_file(&self, path: &str) -> io::Result<String> {
        self.files.read_file(path)
    }

    fn write_file(&self, path: &str, contents: &str) -> io::Result<()> {
        self.files.write_file(path, contents)
    }

    fn read_directory(&self, path: &str) -> io::Result<DirectoryEntries> {
        self.files.read_directory(path)
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Check the roots, references, resolver, and checker in one Program.
fn canonical_symlink_rules_keep_roots_references_and_relative_imports_logical() {
    for preserve_symlinks in [false, true] {
        let filesystem = ObservedFileSystem {
            files: MemoryFileSystem::new(true),
            realpaths: Mutex::new(Vec::new()),
        };
        for (path, contents) in [
            (
                "/project/main.ts",
                concat!(
                    "/// <reference path=\"linked/helper.d.ts\" />\n",
                    "import { value } from './linked/local';\n",
                    "import { remote } from 'pkg';\n",
                    "export const result: number = value + remote;",
                ),
            ),
            ("/real/local/local.ts", "export const value: number = 1;"),
            ("/real/local/helper.d.ts", "declare const helper: number;"),
            (
                "/packages/pkg/package.json",
                r#"{"name":"pkg","types":"index.d.ts"}"#,
            ),
            (
                "/packages/pkg/index.d.ts",
                "export declare const remote: number;",
            ),
        ] {
            filesystem.write_file(path, contents).unwrap();
        }
        filesystem
            .files
            .add_directory_link("/real/local", "/project/linked");
        filesystem
            .files
            .add_directory_link("/packages/pkg", "/project/node_modules/pkg");
        let (program, checked) =
            Program::try_new_with_canonical_checker_and_queries(
                &filesystem,
                "/project",
                &["main.ts".to_owned(), "linked/local.ts".to_owned()],
                CompilerOptions {
                    preserve_symlinks,
                    module: ModuleKind::EsNext,
                    module_resolution: ModuleResolutionKind::Bundler,
                    lib: Some(vec!["es5".to_owned()]),
                    types: Some(Vec::new()),
                    ..CompilerOptions::default()
                },
                |program, queries| {
                    let source = program.source_file("/project/main.ts").unwrap();
                    let location = source.parse.arena.iter().find_map(|(id, node)| {
                    matches!(&node.data, NodeData::Identifier(name) if name.text == "result")
                        .then(|| source.node_ref(id).unwrap())
                }).unwrap();
                    let type_ = queries.get_type_at_location(location).unwrap();
                    assert_eq!(queries.type_to_string(type_).unwrap(), "number");
                },
            )
            .unwrap();
        assert_eq!(checked, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );

        let graph = program.project_graph_snapshot();
        assert_eq!(
            graph.resolution_options.as_ref().unwrap().preserve_symlinks,
            preserve_symlinks
        );
        let relative = graph
            .resolutions
            .iter()
            .find(|resolution| resolution.request.specifier == "./linked/local")
            .unwrap();
        let local = relative.result.resolved.as_ref().unwrap();
        assert_eq!(local.original_file_name, "/project/linked/local.ts");
        assert_eq!(local.resolved_file_name, "/project/linked/local.ts");
        assert_eq!(
            relative.target.as_ref().unwrap().file_id,
            graph.roots[1].file_id.unwrap()
        );
        assert!(program.source_file("/real/local/local.ts").is_none());
        assert!(program.source_file("/project/linked/helper.d.ts").is_some());
        assert!(program.source_file("/real/local/helper.d.ts").is_none());
        let reference = graph
            .references
            .iter()
            .find(|reference| reference.kind == ProgramGraphReferenceKind::Path)
            .unwrap();
        assert_eq!(
            reference.targets[0].file_name,
            "/project/linked/helper.d.ts"
        );

        let package = graph
            .resolutions
            .iter()
            .find(|resolution| resolution.request.specifier == "pkg")
            .unwrap()
            .result
            .resolved
            .as_ref()
            .unwrap();
        assert_eq!(
            package.original_file_name,
            "/project/node_modules/pkg/index.d.ts"
        );
        assert_eq!(
            package.resolved_file_name,
            if preserve_symlinks {
                "/project/node_modules/pkg/index.d.ts"
            } else {
                "/packages/pkg/index.d.ts"
            }
        );
        assert!(
            graph
                .missing_evidence
                .contains(&ProgramGraphMissingEvidence::SourceRealPaths)
        );
        let expected = if preserve_symlinks {
            Vec::new()
        } else {
            vec![(
                "/project/node_modules/pkg/index.d.ts".to_owned(),
                "/packages/pkg/index.d.ts".to_owned(),
            )]
        };
        assert_eq!(*filesystem.realpaths.lock().unwrap(), expected);
        assert_eq!(program.project_graph_snapshot(), graph);
        assert_eq!(*filesystem.realpaths.lock().unwrap(), expected);
    }
}
