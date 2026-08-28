use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn type_roots_program(files: &[(&str, &str)], roots: &[&str], types: &[&str]) -> Program {
    let fs = MemoryFileSystem::new(true);
    for (file, source) in files {
        fs.write_file(file, source).unwrap();
    }
    Program::try_new_with_canonical_checker(
        &fs,
        "/",
        &["/a.ts".to_owned()],
        CompilerOptions {
            module: ModuleKind::CommonJs,
            module_specified: true,
            target: ScriptTarget::Es2015,
            type_roots: Some(roots.iter().map(|root| (*root).to_owned()).collect()),
            types: Some(types.iter().map(|name| (*name).to_owned()).collect()),
            trace_resolution: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap()
}

#[test]
fn ordinary_type_roots_match_the_original_module_resolution_fixture() {
    let program = type_roots_program(
        &[
            (
                "/typings/phaser/types/phaser.d.ts",
                "export const a2: number;\r\n\r\n",
            ),
            (
                "/typings/phaser/package.json",
                "{ \"name\": \"phaser\", \"version\": \"1.2.3\", \"types\": \"types/phaser.d.ts\" }\r\n\r\n\r\n",
            ),
            ("/a.ts", "import { a2 } from \"phaser\";"),
        ],
        &["/typings"],
        &["phaser"],
    );
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    assert!(
        program
            .source_file("/typings/phaser/types/phaser.d.ts")
            .is_some()
    );
}

#[test]
fn scoped_type_roots_match_the_original_module_resolution_fixture() {
    let program = type_roots_program(
        &[
            (
                "/a/types/dummy/index.d.ts",
                "export const dummy: number;\r\n\r\n",
            ),
            (
                "/a/types/@scoped/typescache/index.d.ts",
                "export const typesCache: number;\r\n\r\n",
            ),
            (
                "/a/types/mangled__typescache/index.d.ts",
                "export const mangledTypes: number;\r\n\r\n",
            ),
            (
                "/a/node_modules/@scoped/nodemodulescache/index.d.ts",
                "export const nodeModulesCache: number;\r\n\r\n",
            ),
            (
                "/a/node_modules/mangled__nodemodulescache/index.d.ts",
                "export const mangledNodeModules: number;\r\n\r\n",
            ),
            (
                "/a/node_modules/@types/@scoped/attypescache/index.d.ts",
                "export const atTypesCache: number;\r\n\r\n",
            ),
            (
                "/a/node_modules/@types/mangled__attypescache/index.d.ts",
                "export const mangledAtTypesCache: number;\r\n\r\n\r\n",
            ),
            (
                "/a.ts",
                concat!(
                    "import { typesCache } from \"@scoped/typescache\";\r\n",
                    "import { mangledTypes } from \"@mangled/typescache\";\r\n",
                    "import { nodeModulesCache } from \"@scoped/nodemodulescache\";\r\n",
                    "import { mangledNodeModules } from \"@mangled/nodemodulescache\";\r\n",
                    "import { atTypesCache } from \"@scoped/attypescache\";\r\n",
                    "import { mangledAtTypesCache } from \"@mangled/attypescache\";\r\n",
                ),
            ),
        ],
        &["/a/types", "/a/node_modules", "/a/node_modules/@types"],
        &["dummy"],
    );
    let expected = [
        "@mangled/typescache",
        "@mangled/nodemodulescache",
        "@scoped/attypescache",
    ];
    assert_eq!(program.diagnostics().len(), expected.len());
    let main = program.source_file("/a.ts").unwrap();
    for (diagnostic, specifier) in program.diagnostics().iter().zip(expected) {
        assert_eq!(diagnostic.code, Some(2307));
        assert_eq!(diagnostic.file_name.as_deref(), Some("/a.ts"));
        assert_eq!(
            diagnostic.message,
            format!("Cannot find module '{specifier}' or its corresponding type declarations.")
        );
        let range = diagnostic.range.unwrap();
        assert_eq!(
            &main.source_text[usize::try_from(range.start.get()).unwrap()
                ..usize::try_from(range.end.get()).unwrap()],
            format!("\"{specifier}\"")
        );
    }
    assert!(
        program
            .source_file("/a/node_modules/@types/mangled__attypescache/index.d.ts")
            .is_some()
    );
}
