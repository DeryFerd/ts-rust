//! TypeScript-compatible emit output path calculation.

use ts_options::{CompilerOptions, JsxEmit};
use ts_path::{
    CaseSensitivity, FileExtension, canonicalize, change_extension, common_path_prefix,
    declaration_emit_extension, directory_path, ensure_trailing_directory_separator,
    extension_from_path, normalize_path, resolve_path,
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
        .then(|| change_extension(&out_file, ".d.ts"));
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
    let common = common_path_prefix(&directory_refs, case_sensitivity)
        .filter(|path| !path.is_empty())
        .unwrap_or_else(|| normalize_path(current_directory));
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
    let in_common = match case_sensitivity {
        CaseSensitivity::Sensitive => source.starts_with(&common),
        CaseSensitivity::Insensitive => source
            .get(..common.len())
            .is_some_and(|prefix| prefix.eq_ignore_ascii_case(&common)),
    };
    if !in_common {
        return source;
    }
    resolve_path(new_directory, &[&source[common.len()..]])
}

#[must_use]
pub fn output_paths(
    file_name: &str,
    options: &CompilerOptions,
    current_directory: &str,
    common_source_directory: &str,
    case_sensitivity: CaseSensitivity,
) -> OutputPaths {
    let source_root = options
        .root_dir
        .as_deref()
        .unwrap_or(common_source_directory);
    let javascript = options.printer_settings().emit_javascript.then(|| {
        output_file_path(
            file_name,
            options.out_dir.as_deref(),
            current_directory,
            source_root,
            case_sensitivity,
            output_extension(file_name, options.jsx),
        )
    });
    let source_map = javascript
        .as_ref()
        .filter(|_| options.source_map && !options.inline_source_map)
        .map(|javascript| format!("{javascript}.map"));
    let declaration = options.printer_settings().emit_declarations.then(|| {
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
pub fn build_info_path(options: &CompilerOptions) -> Option<String> {
    options.ts_build_info_file.clone()
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
    change_extension(&path, extension)
}

#[cfg(test)]
mod tests {
    use ts_options::{CompilerOptions, JsxEmit};
    use ts_path::CaseSensitivity;

    use super::{
        build_info_path, bundle_output_paths, common_source_directory, declaration_extension,
        output_extension, output_paths, source_file_path_in_new_directory,
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
            build_info_path(&options).as_deref(),
            Some("/project/cache/build.tsbuildinfo")
        );
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
}
