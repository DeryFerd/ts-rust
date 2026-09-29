//! Rust port of `internal/tsoptions/contentmappers_test.go` (tsgo#4712).
//!
//! PORT: Go runs the tests in parallel (`t.Parallel`); here they run in
//! order. The Go test is in package `tsoptions`; the Rust items it reads
//! (`resolve_content_mapper_manifest`, the `ParsedCommandLine` fields) are
//! `pub`. Go compares mapper pointers; here `Rc::ptr_eq`.

use ts_goport::contentmapper::{Definition, Mapper};
use ts_goport::frontend::prelude::*;
use ts_goport::frontend::tsoptions;

use super::tsoptionstest::{file_map, vfs_from_map};

/// Go `&contentmapper.Mapper{Definition: contentmapper.Definition{Package: package, Extensions: extensions}}`.
fn mapper(package: &str, extensions: &[&str]) -> Rc<Mapper> {
    Rc::new(Mapper {
        definition: Definition {
            package: package.to_string(),
            extensions: extensions.iter().map(|ext| (*ext).to_string()).collect(),
            ..Default::default()
        },
        ..Default::default()
    })
}

/// Go `&ParsedCommandLine{ParsedConfig: &ParsedOptions{ContentMappers: mappers}, comparePathsOptions: ...}`.
fn command_line_with_mappers(
    mappers: Vec<Rc<Mapper>>,
    compare_paths_options: ComparePathsOptions,
) -> ParsedCommandLine {
    ParsedCommandLine {
        parsed_config: ParsedOptions {
            content_mappers: mappers,
            ..Default::default()
        },
        compare_paths_options,
        ..Default::default()
    }
}

/// Go `commandLine.GetContentMapperForFileName(fileName) == want`.
fn is_mapper(command_line: &ParsedCommandLine, file_name: &str, want: &Rc<Mapper>) -> bool {
    command_line
        .get_content_mapper_for_file_name(file_name)
        .is_some_and(|got| Rc::ptr_eq(&got, want))
}

// Go: contentmappers_test.go:20 TestGetContentMapperForFileNameUsesLongestExtension
#[test]
fn get_content_mapper_for_file_name_uses_longest_extension() {
    let z_mapper = mapper("z", &[".z"]);
    let yz_mapper = mapper("yz", &[".y.z"]);
    let command_line = command_line_with_mappers(
        vec![z_mapper.clone(), yz_mapper.clone()],
        ComparePathsOptions::default(),
    );

    assert!(is_mapper(&command_line, "/src/Component.y.z", &yz_mapper));
    assert!(is_mapper(&command_line, "/src/Component.z", &z_mapper));
}

// Go: contentmappers_test.go:30 TestGetContentMapperForFileNameUsesHostCaseSensitivity
#[test]
fn get_content_mapper_for_file_name_uses_host_case_sensitivity() {
    let mapper = mapper("", &[".vue"]);
    let insensitive = command_line_with_mappers(
        vec![mapper.clone()],
        ComparePathsOptions {
            use_case_sensitive_file_names: false,
            ..Default::default()
        },
    );
    let sensitive = command_line_with_mappers(
        vec![mapper.clone()],
        ComparePathsOptions {
            use_case_sensitive_file_names: true,
            ..Default::default()
        },
    );

    assert!(is_mapper(&insensitive, "/src/Component.VUE", &mapper));
    assert!(
        sensitive
            .get_content_mapper_for_file_name("/src/Component.VUE")
            .is_none()
    );
}

// Go: contentmappers_test.go:46 TestGetOutputFileNamesExcludesMapperOwnedOutputs
#[test]
fn get_output_file_names_excludes_mapper_owned_outputs() {
    let mapper = mapper("", &[".vue"]);
    let mut command_line = new_parsed_command_line(
        Rc::new(CompilerOptions {
            out_dir: "/dist".to_string(),
            declaration: Tristate::True,
            declaration_map: Tristate::True,
            source_map: Tristate::True,
            ..Default::default()
        }),
        vec!["/src/Component.vue".to_string()],
        ComparePathsOptions {
            current_directory: "/".to_string(),
            use_case_sensitive_file_names: true,
        },
    );
    command_line.parsed_config.content_mappers = vec![mapper];

    assert_eq!(
        command_line.get_output_file_names(),
        vec!["/dist/Component.d.vue.ts".to_string()]
    );
}

// Go: contentmappers_test.go:16 resolveContentMapperHost
struct ResolveContentMapperHost {
    fs: Rc<dyn Fs>,
}

impl ParseConfigHost for ResolveContentMapperHost {
    // Go: contentmappers_test.go:64 (resolveContentMapperHost).FS
    fn fs(&self) -> Rc<dyn Fs> {
        self.fs.clone()
    }

    // Go: contentmappers_test.go:65 (resolveContentMapperHost).GetCurrentDirectory
    fn get_current_directory(&self) -> String {
        "/home/project".to_string()
    }
}

// Go: contentmappers_test.go:67 TestResolveContentMapperManifest
#[test]
fn resolve_content_mapper_manifest() {
    let host = ResolveContentMapperHost {
        fs: vfs_from_map(
            &file_map(&[
                (
                    "/home/project/node_modules/vue-ts-mapper/package.json",
                    "{\n\t\t\t\"name\": \"vue-ts-mapper\",\n\t\t\t\"version\": \"1.2.3\",\n\t\t\t\"typescript\": { \"contentMapper\": { \"exec\": [\"node\", \"./dist/mapper.js\"], \"compilerOptions\": [\"target\", \"jsx\"] } }\n\t\t}",
                ),
                (
                    "/home/node_modules/@scope/noversion/package.json",
                    "{\n\t\t\t\"name\": \"@scope/noversion\",\n\t\t\t\"typescript\": { \"contentMapper\": { \"exec\": [\"run\"] } }\n\t\t}",
                ),
                (
                    "/home/project/node_modules/no-name/package.json",
                    "{\n\t\t\t\"version\": \"1.0.0\"\n\t\t}",
                ),
                (
                    "/home/project/node_modules/no-manifest/package.json",
                    "{\n\t\t\t\"name\": \"no-manifest\"\n\t\t}",
                ),
                (
                    "/home/project/node_modules/no-exec/package.json",
                    "{\n\t\t\t\"name\": \"no-exec\",\n\t\t\t\"typescript\": { \"contentMapper\": {} }\n\t\t}",
                ),
                (
                    "/home/project/node_modules/bad-exec/package.json",
                    "{\n\t\t\t\"name\": \"bad-exec\",\n\t\t\t\"typescript\": { \"contentMapper\": { \"exec\": \"node ./mapper.js\" } }\n\t\t}",
                ),
            ]),
            true, /*useCaseSensitiveFileNames*/
        ),
    };
    let code = |message: &'static Message| message.code() as i32;

    // Name, version, and the verbatim exec argv are preserved.
    let (manifest, package_directory, diagnostic) = tsoptions::resolve_content_mapper_manifest(
        &host,
        "/home/project/tsconfig.json",
        "vue-ts-mapper",
    );
    assert!(diagnostic.is_none());
    assert_eq!(manifest.name, "vue-ts-mapper");
    assert_eq!(manifest.version, "1.2.3");
    assert_eq!(
        package_directory,
        "/home/project/node_modules/vue-ts-mapper"
    );
    assert_eq!(
        manifest.exec,
        vec!["node".to_string(), "./dist/mapper.js".to_string()]
    );
    assert_eq!(
        manifest.compiler_options,
        vec!["target".to_string(), "jsx".to_string()]
    );

    // Resolution walks up node_modules; a package with no version resolves to a name and empty version.
    let (manifest, _, diagnostic) = tsoptions::resolve_content_mapper_manifest(
        &host,
        "/home/project/src/tsconfig.json",
        "@scope/noversion",
    );
    assert!(diagnostic.is_none());
    assert_eq!(manifest.name, "@scope/noversion");
    assert_eq!(manifest.version, "");

    // A package that is not installed reports a resolution diagnostic.
    let (_, _, diagnostic) = tsoptions::resolve_content_mapper_manifest(
        &host,
        "/home/project/tsconfig.json",
        "missing-mapper",
    );
    let diagnostic = diagnostic.expect("expected a diagnostic for missing-mapper");
    assert_eq!(
        diagnostic.code,
        code(diag::The_content_mapper_package_0_could_not_be_resolved)
    );

    // A package whose package.json has no name reports a diagnostic.
    let (_, package_directory, diagnostic) =
        tsoptions::resolve_content_mapper_manifest(&host, "/home/project/tsconfig.json", "no-name");
    let diagnostic = diagnostic.expect("expected a diagnostic for no-name");
    assert_eq!(package_directory, "/home/project/node_modules/no-name");
    assert_eq!(
        diagnostic.code,
        code(diag::The_package_json_of_the_content_mapper_package_0_does_not_specify_a_name)
    );

    // A package that does not declare a "typescript.contentMapper" object reports a diagnostic.
    let (_, _, diagnostic) = tsoptions::resolve_content_mapper_manifest(
        &host,
        "/home/project/tsconfig.json",
        "no-manifest",
    );
    let diagnostic = diagnostic.expect("expected a diagnostic for no-manifest");
    assert_eq!(
        diagnostic.code,
        code(
            diag::The_package_json_of_the_content_mapper_package_0_does_not_declare_a_typescript_contentMapper_object
        )
    );

    // A "typescript.contentMapper" with no "exec", or an "exec" of the wrong type, reports a diagnostic.
    for pkg in ["no-exec", "bad-exec"] {
        let (_, _, diagnostic) =
            tsoptions::resolve_content_mapper_manifest(&host, "/home/project/tsconfig.json", pkg);
        let diagnostic = diagnostic.unwrap_or_else(|| panic!("expected a diagnostic for {pkg}"));
        assert_eq!(
            diagnostic.code,
            code(
                diag::The_typescript_contentMapper_exec_of_the_content_mapper_package_0_must_be_a_non_empty_array_of_strings
            )
        );
    }
}
