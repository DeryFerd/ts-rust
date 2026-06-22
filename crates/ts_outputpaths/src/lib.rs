//! TypeScript-compatible emit output path calculation.

use ts_options::JsxEmit;
use ts_path::{
    CaseSensitivity, FileExtension, canonicalize, common_path_prefix, declaration_emit_extension,
    directory_path, ensure_trailing_directory_separator, extension_from_path, normalize_path,
    resolve_path,
};

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
    let relative = if in_common {
        &source[common.len()..]
    } else {
        source.trim_start_matches('/')
    };
    resolve_path(new_directory, &[relative])
}

#[cfg(test)]
mod tests {
    use ts_options::JsxEmit;
    use ts_path::CaseSensitivity;

    use super::{
        common_source_directory, declaration_extension, output_extension,
        source_file_path_in_new_directory,
    };

    #[test]
    fn selects_javascript_and_declaration_extensions() {
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
}
