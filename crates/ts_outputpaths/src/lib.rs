//! TypeScript-compatible emit output path calculation.

use ts_options::{CompilerOptions, JsxEmit};
use ts_path::{
    CaseSensitivity, FileExtension, base_file_name, canonical_file_name, canonicalize,
    common_path_prefix, declaration_emit_extension, directory_path,
    ensure_trailing_directory_separator, extension_from_path, normalize_path,
    relative_path_from_directory, remove_file_extension, resolve_path, root_length,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OutputPaths {
    pub javascript: Option<String>,
    pub source_map: Option<String>,
    pub declaration: Option<String>,
    pub declaration_map: Option<String>,
}

/// Computes the single output paths selected by `outFile`.
#[must_use]
pub fn bundle_output_paths(
    options: &CompilerOptions,
    current_directory: &str,
) -> Option<OutputPaths> {
    let out_file = options.out_file.as_deref()?;
    let out_file = if ts_path::is_absolute(out_file) {
        normalize_path(out_file)
    } else {
        resolve_path(current_directory, &[out_file])
    };
    let javascript = options
        .printer_settings()
        .emit_javascript
        .then(|| out_file.clone());
    let source_map = javascript
        .as_ref()
        .filter(|_| options.source_map && !options.inline_source_map)
        .map(|javascript| format!("{javascript}.map"));
    let declaration = options
        .printer_settings()
        .emit_declarations
        .then(|| format!("{}.d.ts", remove_file_extension(&out_file)));
    let declaration_map = declaration
        .as_ref()
        .filter(|_| options.declaration_map)
        .map(|declaration| format!("{declaration}.map"));
    Some(OutputPaths {
        javascript,
        source_map,
        declaration,
        declaration_map,
    })
}

#[must_use]
pub fn output_extension(file_name: &str, jsx: JsxEmit) -> &'static str {
    match extension_from_path(file_name) {
        Some(FileExtension::Json) => ".json",
        Some(FileExtension::Tsx | FileExtension::Jsx) if jsx == JsxEmit::Preserve => ".jsx",
        Some(FileExtension::Mts | FileExtension::Mjs) => ".mjs",
        Some(FileExtension::Cts | FileExtension::Cjs) => ".cjs",
        _ => ".js",
    }
}

#[must_use]
pub fn declaration_extension(file_name: &str) -> &'static str {
    declaration_emit_extension(file_name)
}

#[must_use]
pub fn common_source_directory(
    file_names: &[String],
    current_directory: &str,
    case_sensitivity: CaseSensitivity,
) -> String {
    if file_names.is_empty() {
        return ensure_trailing_directory_separator(&normalize_path(current_directory));
    }
    let directories: Vec<_> = file_names
        .iter()
        .map(|file_name| {
            directory_path(&canonicalize(
                file_name,
                current_directory,
                CaseSensitivity::Sensitive,
            ))
        })
        .collect();
    let directory_refs: Vec<_> = directories.iter().map(String::as_str).collect();
    let Some(common) = common_path_prefix(&directory_refs, case_sensitivity) else {
        return String::new();
    };
    ensure_trailing_directory_separator(&common)
}

#[must_use]
pub fn source_file_path_in_new_directory(
    file_name: &str,
    new_directory: &str,
    current_directory: &str,
    common_source_directory: &str,
    case_sensitivity: CaseSensitivity,
) -> String {
    let source = canonicalize(file_name, current_directory, CaseSensitivity::Sensitive);
    let common = ensure_trailing_directory_separator(&canonicalize(
        common_source_directory,
        current_directory,
        CaseSensitivity::Sensitive,
    ));
    let canonical_source = canonical_file_name(&source, case_sensitivity);
    let canonical_common = canonical_file_name(&common, case_sensitivity);
    let source_root = root_length(&canonical_source);
    let common_root = root_length(&canonical_common);
    if canonical_file_name(
        &canonical_source[..source_root],
        CaseSensitivity::Insensitive,
    ) != canonical_file_name(
        &canonical_common[..common_root],
        CaseSensitivity::Insensitive,
    ) {
        return source;
    }
    let Some(remainder) =
        canonical_source[source_root..].strip_prefix(&canonical_common[common_root..])
    else {
        return source;
    };
    let component_count = remainder.bytes().filter(|byte| *byte == b'/').count() + 1;
    let display_remainder = source
        .rmatch_indices('/')
        .nth(component_count - 1)
        .map_or(source.as_str(), |(separator, _)| &source[separator + 1..]);
    resolve_path(new_directory, &[display_remainder])
}

#[must_use]
pub fn output_paths(
    file_name: &str,
    options: &CompilerOptions,
    current_directory: &str,
    common_source_directory: &str,
    case_sensitivity: CaseSensitivity,
) -> OutputPaths {
    let is_json = extension_from_path(file_name) == Some(FileExtension::Json);
    let source_root = options
        .root_dir
        .as_deref()
        .unwrap_or(common_source_directory);
    let javascript = options
        .printer_settings()
        .emit_javascript
        .then(|| {
            output_file_path(
                file_name,
                options.out_dir.as_deref(),
                current_directory,
                source_root,
                case_sensitivity,
                output_extension(file_name, options.jsx),
            )
        })
        .filter(|output| {
            !is_json
                || canonicalize(output, current_directory, case_sensitivity)
                    != canonicalize(file_name, current_directory, case_sensitivity)
        });
    let source_map = javascript
        .as_ref()
        .filter(|_| !is_json && options.source_map && !options.inline_source_map)
        .map(|javascript| format!("{javascript}.map"));
    let declaration = (options.printer_settings().emit_declarations && !is_json).then(|| {
        output_file_path(
            file_name,
            options
                .declaration_dir
                .as_deref()
                .or(options.out_dir.as_deref()),
            current_directory,
            source_root,
            case_sensitivity,
            declaration_extension(file_name),
        )
    });
    let declaration_map = declaration
        .as_ref()
        .filter(|_| options.declaration_map)
        .map(|declaration| format!("{declaration}.map"));
    OutputPaths {
        javascript,
        source_map,
        declaration,
        declaration_map,
    }
}

#[must_use]
pub fn build_info_path(
    options: &CompilerOptions,
    config_path: &str,
    case_sensitivity: CaseSensitivity,
) -> String {
    if let Some(path) = &options.ts_build_info_file {
        return path.clone();
    }

    let config_path = normalize_path(config_path);
    let config_directory = directory_path(&config_path);
    if let Some(out_file) = &options.out_file {
        let out_file = if ts_path::is_absolute(out_file) {
            normalize_path(out_file)
        } else {
            resolve_path(&config_directory, &[out_file])
        };
        return format!("{}.tsbuildinfo", remove_file_extension(&out_file));
    }

    let config_without_extension = remove_file_extension(&config_path);
    let output_without_extension = if let Some(out_dir) = &options.out_dir {
        let out_dir = if ts_path::is_absolute(out_dir) {
            normalize_path(out_dir)
        } else {
            resolve_path(&config_directory, &[out_dir])
        };
        if let Some(root_dir) = &options.root_dir {
            let root_dir = if ts_path::is_absolute(root_dir) {
                normalize_path(root_dir)
            } else {
                resolve_path(&config_directory, &[root_dir])
            };
            let relative =
                relative_path_from_directory(&root_dir, config_without_extension, case_sensitivity);
            resolve_path(&out_dir, &[&relative])
        } else {
            resolve_path(&out_dir, &[base_file_name(config_without_extension)])
        }
    } else {
        config_without_extension.to_owned()
    };
    format!("{output_without_extension}.tsbuildinfo")
}

fn output_file_path(
    file_name: &str,
    directory: Option<&str>,
    current_directory: &str,
    source_root: &str,
    case_sensitivity: CaseSensitivity,
    extension: &str,
) -> String {
    let path = directory.map_or_else(
        || canonicalize(file_name, current_directory, CaseSensitivity::Sensitive),
        |directory| {
            let directory = if ts_path::is_absolute(directory) {
                normalize_path(directory)
            } else {
                resolve_path(current_directory, &[directory])
            };
            source_file_path_in_new_directory(
                file_name,
                &directory,
                current_directory,
                source_root,
                case_sensitivity,
            )
        },
    );
    format!("{}{extension}", remove_file_extension(&path))
}

#[cfg(test)]
mod tests {
    use ts_options::{CompilerOptions, JsxEmit};
    use ts_path::CaseSensitivity;

    use super::{
        OutputPaths, build_info_path, bundle_output_paths, common_source_directory,
        declaration_extension, output_extension, output_paths, source_file_path_in_new_directory,
    };

    #[test]
    fn selects_javascript_and_declaration_extensions() {
        assert_eq!(output_extension("view.tsx", JsxEmit::None), ".js");
        assert_eq!(output_extension("view.jsx", JsxEmit::None), ".js");
        assert_eq!(output_extension("view.tsx", JsxEmit::Preserve), ".jsx");
        assert_eq!(output_extension("view.tsx", JsxEmit::ReactJsx), ".js");
        assert_eq!(output_extension("entry.mts", JsxEmit::Preserve), ".mjs");
        assert_eq!(output_extension("entry.cts", JsxEmit::Preserve), ".cjs");
        assert_eq!(output_extension("data.json", JsxEmit::Preserve), ".json");
        assert_eq!(declaration_extension("entry.mts"), ".d.mts");
        assert_eq!(declaration_extension("entry.cts"), ".d.cts");
    }

    #[test]
    fn computes_common_directory_and_rehomes_sources() {
        let files = vec![
            "/project/src/a.ts".to_owned(),
            "/project/src/nested/b.ts".to_owned(),
        ];
        let common = common_source_directory(&files, "/project", CaseSensitivity::Sensitive);
        assert_eq!(common, "/project/src/");
        assert_eq!(
            source_file_path_in_new_directory(
                "/project/src/nested/b.ts",
                "/project/dist",
                "/project",
                &common,
                CaseSensitivity::Sensitive,
            ),
            "/project/dist/nested/b.ts"
        );
    }

    #[test]
    fn different_disk_roots_have_no_common_source_directory() {
        let files = vec![
            "C:/project/main.ts".to_owned(),
            "D:/shared/util.ts".to_owned(),
        ];

        assert_eq!(
            common_source_directory(&files, "C:/project", CaseSensitivity::Insensitive),
            ""
        );
    }

    #[test]
    fn output_rehoming_respects_case_sensitivity() {
        assert_eq!(
            source_file_path_in_new_directory(
                "/PROJECT/src/a.ts",
                "/dist",
                "/project",
                "/project/src",
                CaseSensitivity::Insensitive,
            ),
            "/dist/a.ts"
        );
        assert_eq!(
            source_file_path_in_new_directory(
                "C:/Project/src/a.ts",
                "D:/dist",
                "C:/Project",
                "c:/Project/src",
                CaseSensitivity::Sensitive,
            ),
            "D:/dist/a.ts"
        );
        assert_eq!(
            source_file_path_in_new_directory(
                "/PROJECT/\u{1e9e}RC/a.ts",
                "/dist",
                "/project",
                "/project/\u{00df}rc",
                CaseSensitivity::Insensitive,
            ),
            "/dist/a.ts"
        );
    }

    #[test]
    fn leaves_sources_outside_the_common_directory_in_place() {
        assert_eq!(
            source_file_path_in_new_directory(
                "/outside/file.ts",
                "/project/dist",
                "/project",
                "/project/src",
                CaseSensitivity::Sensitive,
            ),
            "/outside/file.ts"
        );
    }

    #[test]
    fn computes_javascript_map_and_declaration_directories() {
        let options = CompilerOptions {
            declaration: true,
            declaration_map: true,
            source_map: true,
            out_dir: Some("/project/dist".into()),
            root_dir: Some("/project/src".into()),
            declaration_dir: Some("/project/types".into()),
            ts_build_info_file: Some("/project/cache/build.tsbuildinfo".into()),
            ..CompilerOptions::default()
        };
        let paths = output_paths(
            "/project/src/nested/entry.mts",
            &options,
            "/project",
            "/project/src/",
            CaseSensitivity::Sensitive,
        );
        assert_eq!(
            paths.javascript.as_deref(),
            Some("/project/dist/nested/entry.mjs")
        );
        assert_eq!(
            paths.source_map.as_deref(),
            Some("/project/dist/nested/entry.mjs.map")
        );
        assert_eq!(
            paths.declaration.as_deref(),
            Some("/project/types/nested/entry.d.mts")
        );
        assert_eq!(
            paths.declaration_map.as_deref(),
            Some("/project/types/nested/entry.d.mts.map")
        );
        assert_eq!(
            build_info_path(
                &options,
                "/project/tsconfig.json",
                CaseSensitivity::Sensitive,
            ),
            "/project/cache/build.tsbuildinfo"
        );
    }

    #[test]
    fn derives_build_info_paths_from_output_and_root_directories() {
        assert_eq!(
            build_info_path(
                &CompilerOptions::default(),
                "/project/tsconfig.json",
                CaseSensitivity::Sensitive,
            ),
            "/project/tsconfig.tsbuildinfo"
        );

        let options = CompilerOptions {
            out_dir: Some("dist".to_owned()),
            ..CompilerOptions::default()
        };
        assert_eq!(
            build_info_path(
                &options,
                "/project/tsconfig.json",
                CaseSensitivity::Sensitive,
            ),
            "/project/dist/tsconfig.tsbuildinfo"
        );

        let options = CompilerOptions {
            out_dir: Some("/project/dist".to_owned()),
            root_dir: Some("/project/packages".to_owned()),
            ..CompilerOptions::default()
        };
        assert_eq!(
            build_info_path(
                &options,
                "/project/packages/app/tsconfig.app.json",
                CaseSensitivity::Sensitive,
            ),
            "/project/dist/app/tsconfig.app.tsbuildinfo"
        );
    }

    #[test]
    fn build_info_paths_prefer_normalized_bundle_outputs() {
        let options = CompilerOptions {
            out_file: Some("dist/../bundle/output.custom".to_owned()),
            out_dir: Some("ignored".to_owned()),
            root_dir: Some("other".to_owned()),
            ..CompilerOptions::default()
        };
        assert_eq!(
            build_info_path(
                &options,
                "/project/tsconfig.json",
                CaseSensitivity::Sensitive,
            ),
            "/project/bundle/output.custom.tsbuildinfo"
        );

        let options = CompilerOptions {
            out_file: Some(r"C:\project\dist\bundle.d.ts".to_owned()),
            ..CompilerOptions::default()
        };
        assert_eq!(
            build_info_path(
                &options,
                r"C:\project\tsconfig.json",
                CaseSensitivity::Insensitive,
            ),
            "C:/project/dist/bundle.tsbuildinfo"
        );
    }

    #[test]
    fn declaration_only_paths_respect_normalized_relative_directories() {
        let options = CompilerOptions {
            declaration: true,
            declaration_map: true,
            emit_declaration_only: true,
            source_map: true,
            out_dir: Some("./dist/../dist".into()),
            root_dir: Some("./src/../src".into()),
            declaration_dir: Some("./types/../types".into()),
            ..CompilerOptions::default()
        };
        let paths = output_paths(
            "/project/src/nested/entry.ts",
            &options,
            "/project",
            "/project/src/",
            CaseSensitivity::Sensitive,
        );

        assert!(paths.javascript.is_none());
        assert!(paths.source_map.is_none());
        assert_eq!(
            paths.declaration.as_deref(),
            Some("/project/types/nested/entry.d.ts")
        );
        assert_eq!(
            paths.declaration_map.as_deref(),
            Some("/project/types/nested/entry.d.ts.map")
        );
    }

    #[test]
    fn no_emit_suppresses_individual_and_bundled_outputs() {
        let options = CompilerOptions {
            declaration: true,
            declaration_map: true,
            no_emit: true,
            source_map: true,
            out_file: Some("dist/bundle.js".into()),
            out_dir: Some("dist".into()),
            declaration_dir: Some("types".into()),
            ..CompilerOptions::default()
        };

        for paths in [
            output_paths(
                "/project/src/entry.ts",
                &options,
                "/project",
                "/project/src/",
                CaseSensitivity::Sensitive,
            ),
            bundle_output_paths(&options, "/project").unwrap(),
        ] {
            assert_eq!(
                paths,
                OutputPaths {
                    javascript: None,
                    source_map: None,
                    declaration: None,
                    declaration_map: None,
                }
            );
        }
    }

    #[test]
    fn inline_maps_do_not_allocate_external_map_paths() {
        let options = CompilerOptions {
            inline_source_map: true,
            out_dir: Some("dist".into()),
            ..CompilerOptions::default()
        };
        let paths = output_paths(
            "/project/src/main.ts",
            &options,
            "/project",
            "/project/src/",
            CaseSensitivity::Sensitive,
        );
        assert_eq!(paths.javascript.as_deref(), Some("/project/dist/main.js"));
        assert!(paths.source_map.is_none());
    }

    #[test]
    fn json_outputs_never_emit_declarations_or_source_maps() {
        let options = CompilerOptions {
            declaration: true,
            declaration_map: true,
            source_map: true,
            out_dir: Some("dist".into()),
            ..CompilerOptions::default()
        };
        let paths = output_paths(
            "/project/src/data.json",
            &options,
            "/project",
            "/project/src/",
            CaseSensitivity::Sensitive,
        );

        assert_eq!(paths.javascript.as_deref(), Some("/project/dist/data.json"));
        assert!(paths.source_map.is_none());
        assert!(paths.declaration.is_none());
        assert!(paths.declaration_map.is_none());
    }

    #[test]
    fn json_inputs_are_not_written_back_to_their_source_paths() {
        let paths = output_paths(
            "/project/src/data.json",
            &CompilerOptions::default(),
            "/project",
            "/project/src/",
            CaseSensitivity::Sensitive,
        );

        assert!(paths.javascript.is_none());
        assert!(paths.source_map.is_none());
        assert!(paths.declaration.is_none());
        assert!(paths.declaration_map.is_none());
    }

    #[test]
    fn json_collision_checks_follow_filesystem_case_sensitivity() {
        let options = CompilerOptions {
            out_dir: Some("/PROJECT/src/./".into()),
            ..CompilerOptions::default()
        };

        let insensitive = output_paths(
            "/project/src/data.json",
            &options,
            "/project",
            "/project/src/",
            CaseSensitivity::Insensitive,
        );
        assert!(insensitive.javascript.is_none());

        let sensitive = output_paths(
            "/project/src/data.json",
            &options,
            "/project",
            "/project/src/",
            CaseSensitivity::Sensitive,
        );
        assert_eq!(
            sensitive.javascript.as_deref(),
            Some("/PROJECT/src/data.json")
        );
    }

    #[test]
    fn unrecognized_source_extensions_do_not_overwrite_inputs() {
        let paths = output_paths(
            "/project/src/INPUT.TS",
            &CompilerOptions {
                declaration: true,
                ..CompilerOptions::default()
            },
            "/project",
            "/project/src/",
            CaseSensitivity::Sensitive,
        );

        assert_eq!(
            paths.javascript.as_deref(),
            Some("/project/src/INPUT.TS.js")
        );
        assert_eq!(
            paths.declaration.as_deref(),
            Some("/project/src/INPUT.TS.d.ts")
        );
    }

    #[test]
    fn computes_single_out_file_paths() {
        let options = CompilerOptions {
            out_file: Some("dist/bundle.js".into()),
            declaration: true,
            declaration_map: true,
            source_map: true,
            ..CompilerOptions::default()
        };
        let paths = bundle_output_paths(&options, "/project").unwrap();
        assert_eq!(paths.javascript.as_deref(), Some("/project/dist/bundle.js"));
        assert_eq!(
            paths.source_map.as_deref(),
            Some("/project/dist/bundle.js.map")
        );
        assert_eq!(
            paths.declaration.as_deref(),
            Some("/project/dist/bundle.d.ts")
        );
        assert_eq!(
            paths.declaration_map.as_deref(),
            Some("/project/dist/bundle.d.ts.map")
        );
    }

    #[test]
    fn bundled_declarations_append_extensions_and_ignore_declaration_directory() {
        for (out_file, declaration) in [
            ("dist/./bundle", "/project/dist/bundle.d.ts"),
            ("dist/bundle.custom", "/project/dist/bundle.custom.d.ts"),
            ("dist/bundle.d.ts", "/project/dist/bundle.d.ts"),
        ] {
            let options = CompilerOptions {
                out_file: Some(out_file.into()),
                declaration: true,
                declaration_map: true,
                declaration_dir: Some("types".into()),
                emit_declaration_only: true,
                source_map: true,
                ..CompilerOptions::default()
            };
            let paths = bundle_output_paths(&options, "/project").unwrap();

            assert!(paths.javascript.is_none());
            assert!(paths.source_map.is_none());
            assert_eq!(paths.declaration.as_deref(), Some(declaration));
            assert_eq!(
                paths.declaration_map.as_deref(),
                Some(format!("{declaration}.map").as_str())
            );
        }
    }
}
