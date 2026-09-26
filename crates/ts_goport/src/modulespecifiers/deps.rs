//! The parts of Go `internal/module`, `internal/core` (pattern.go),
//! `internal/stringutil` and `internal/outputpaths` that modulespecifiers
//! uses.
//!
//! PORT: the Go `module` and `outputpaths` packages are ported under
//! `src/frontend/`, which `lib.rs` does not compile, and they need the full
//! resolver. These are copies of the small functions this package calls.

use crate::prelude::*;

use super::packagejson::TYPE_SCRIPT_VERSION;
use super::semver;
use super::tspath;

// Go: module/util.go:17 IsApplicableVersionedTypesKey
pub fn is_applicable_versioned_types_key(key: &str) -> bool {
    let Some(rest) = key.strip_prefix("types@") else {
        return false;
    };
    let (range, ok) = semver::try_parse_version_range(rest);
    if !ok {
        return false;
    }
    range.test(&semver::must_parse_version(TYPE_SCRIPT_VERSION))
}

// Go: module/util.go:69 UnmangleScopedPackageName
pub fn unmangle_scoped_package_name(package_name: &str) -> String {
    if let Some((before, after)) = package_name.split_once("__") {
        return format!("@{before}/{after}");
    }
    package_name.to_string()
}

// Go: module/util.go:81 GetPackageNameFromTypesPackageName
pub fn get_package_name_from_types_package_name(mangled_name: &str) -> String {
    if let Some(without_at_type_prefix) = mangled_name.strip_prefix("@types/") {
        return unmangle_scoped_package_name(without_at_type_prefix);
    }
    mangled_name.to_string()
}

// Go: module/util.go:58 MangleScopedPackageName
pub fn mangle_scoped_package_name(package_name: &str) -> String {
    if package_name.starts_with('@') {
        let Some(idx) = package_name.find('/') else {
            return package_name.to_string();
        };
        return format!("{}__{}", &package_name[1..idx], &package_name[idx + 1..]);
    }
    package_name.to_string()
}

// Go: module/util.go:178 TryGetJSExtensionForFile
// TryGetJSExtensionForFile maps TS/JS/DTS extensions to the output JS-side extension.
// Returns an empty string if the extension is unsupported.
pub fn try_get_js_extension_for_file(file_name: &str, options: &CompilerOptions) -> &'static str {
    let ext = tspath::try_get_extension_from_path(file_name);
    match ext {
        tspath::EXTENSION_TS | tspath::EXTENSION_DTS => tspath::EXTENSION_JS,
        tspath::EXTENSION_TSX => {
            if options.jsx == JsxEmit::PRESERVE {
                return tspath::EXTENSION_JSX;
            }
            tspath::EXTENSION_JS
        }
        tspath::EXTENSION_JS | tspath::EXTENSION_JSX | tspath::EXTENSION_JSON => ext,
        tspath::EXTENSION_DMTS | tspath::EXTENSION_MTS | tspath::EXTENSION_MJS => {
            tspath::EXTENSION_MJS
        }
        tspath::EXTENSION_DCTS | tspath::EXTENSION_CTS | tspath::EXTENSION_CJS => {
            tspath::EXTENSION_CJS
        }
        _ => "",
    }
}

// Go: module/resolver.go:1918 GetConditions
pub fn get_conditions(
    options: &CompilerOptions,
    mut resolution_mode: ResolutionMode,
) -> Vec<String> {
    let module_resolution = options.get_module_resolution_kind();
    if resolution_mode == ModuleKind::NONE && module_resolution == ModuleResolutionKind::BUNDLER {
        resolution_mode = ModuleKind::ES_NEXT;
    }
    let custom_conditions = options.custom_conditions.as_deref().unwrap_or_default();
    let mut conditions: Vec<String> = Vec::with_capacity(3 + custom_conditions.len());
    if resolution_mode == ModuleKind::ES_NEXT {
        conditions.push("import".to_string());
    } else {
        conditions.push("require".to_string());
    }

    if options.no_dts_resolution != Tristate::True {
        conditions.push("types".to_string());
    }
    if module_resolution != ModuleResolutionKind::BUNDLER {
        conditions.push("node".to_string());
    }
    conditions.extend(custom_conditions.iter().cloned());
    conditions
}

// Go: core/pattern.go:5 Pattern
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Pattern {
    pub text: String,
    pub star_index: isize, // -1 for exact match
}

impl Pattern {
    // Go: core/pattern.go:18 IsValid
    pub fn is_valid(&self) -> bool {
        self.star_index == -1 || (self.star_index as usize) < self.text.len()
    }

    // Go: core/pattern.go:22 Matches
    // PORT: Go compares bytes. `text` and `candidate` are port forms, so
    // this compares their Go bytes (see `scanner_util::GO_STRING_MARKER`).
    // `star_index` is the port offset of the star.
    pub fn matches(&self, candidate: &str) -> bool {
        if self.star_index == -1 {
            return self.text == candidate;
        }
        let star = self.star_index as usize;
        go_len(candidate) + 1 >= go_len(&self.text)
            && go_has_prefix(candidate, &self.text[..star])
            && go_has_suffix(candidate, &self.text[star + 1..])
    }

    /// Go `StarIndex`: the Go byte offset of the star, or -1.
    fn go_star_index(&self) -> isize {
        if self.star_index == -1 {
            return -1;
        }
        go_len(&self.text[..self.star_index as usize]) as isize
    }
}

// Go: core/pattern.go:10 TryParsePattern
pub fn try_parse_pattern(pattern: &str) -> Pattern {
    let star_index = pattern.find('*');
    match star_index {
        None => Pattern {
            text: pattern.to_string(),
            star_index: -1,
        },
        Some(i) if !pattern[i + 1..].contains('*') => Pattern {
            text: pattern.to_string(),
            star_index: i as isize,
        },
        Some(_) => Pattern::default(),
    }
}

// Go: core/pattern.go:41 FindBestPatternMatch
pub fn find_best_pattern_match(values: &[Pattern], candidate: &str) -> Pattern {
    let mut best_pattern = Pattern::default();
    let mut longest_match_prefix_length: isize = -1;
    for pattern in values {
        let star_index = pattern.go_star_index();
        if (star_index == -1 || star_index > longest_match_prefix_length)
            && pattern.matches(candidate)
        {
            best_pattern = pattern.clone();
            longest_match_prefix_length = star_index;
        }
    }
    best_pattern
}

// Go: module/resolver.go:1976 ParsedPatterns
#[derive(Clone, Debug, Default)]
pub struct ParsedPatterns {
    matchable_string_set: FxHashSet<String>,
    patterns: Vec<Pattern>,
}

// Go: module/resolver.go:1988 TryParsePatterns
pub fn try_parse_patterns(
    path_mappings: Option<&IndexMap<String, Option<Vec<String>>>>,
) -> ParsedPatterns {
    let mut result = ParsedPatterns::default();
    let Some(path_mappings) = path_mappings else {
        return result;
    };
    for path in path_mappings.keys() {
        let pattern = try_parse_pattern(path);
        if pattern.is_valid() {
            if pattern.star_index == -1 {
                result.matchable_string_set.insert(path.clone());
            } else {
                result.patterns.push(pattern);
            }
        }
    }
    result
}

// Go: module/resolver.go:2023 MatchPatternOrExact
pub fn match_pattern_or_exact(patterns: &ParsedPatterns, candidate: &str) -> Pattern {
    if patterns.matchable_string_set.contains(candidate) {
        return Pattern {
            text: candidate.to_string(),
            star_index: -1,
        };
    }
    if patterns.patterns.is_empty() {
        return Pattern::default();
    }
    find_best_pattern_match(&patterns.patterns, candidate)
}

// Go: core/core.go:678 IndexAfter
pub fn index_after(s: &str, pattern: &str, start_index: usize) -> isize {
    match s.get(start_index..).and_then(|rest| rest.find(pattern)) {
        None => -1,
        Some(matched) => (matched + start_index) as isize,
    }
}

// Go: core/core.go:830 CompareBooleans
// CompareBooleans treats true as greater than false.
pub fn compare_booleans(a: bool, b: bool) -> i32 {
    if a && !b {
        1
    } else if !a && b {
        -1
    } else {
        0
    }
}

// Go: stringutil/compare.go:74 HasPrefix
// PORT: compares the Go bytes of the port forms (see
// `scanner_util::GO_STRING_MARKER`).
pub fn has_prefix(s: &str, prefix: &str, case_sensitive: bool) -> bool {
    let (s, prefix) = (go_string_bytes(s), go_string_bytes(prefix));
    if case_sensitive {
        return s.starts_with(&prefix);
    }
    if prefix.len() > s.len() {
        return false;
    }
    s[..prefix.len()].eq_ignore_ascii_case(&prefix)
}

// Go: stringutil/compare.go:84 HasSuffix
// PORT: see `has_prefix`.
pub fn has_suffix(s: &str, suffix: &str, case_sensitive: bool) -> bool {
    let (s, suffix) = (go_string_bytes(s), go_string_bytes(suffix));
    if case_sensitive {
        return s.ends_with(&suffix);
    }
    if suffix.len() > s.len() {
        return false;
    }
    s[s.len() - suffix.len()..].eq_ignore_ascii_case(&suffix)
}
// PORT: Go uses strings.EqualFold (Unicode simple folding). This compares
// ASCII case only, which matches for the ASCII paths in practice.

// Go: stringutil/compare.go:94 HasPrefixAndSuffixWithoutOverlap
pub fn has_prefix_and_suffix_without_overlap(
    s: &str,
    prefix: &str,
    suffix: &str,
    case_sensitive: bool,
) -> bool {
    if go_len(prefix) + go_len(suffix) > go_len(s) {
        return false;
    }
    has_prefix(s, prefix, case_sensitive) && has_suffix(s, suffix, case_sensitive)
}

// Go: outputpaths/outputpaths.go:11 OutputPathsHost
pub trait OutputPathsHost {
    fn common_source_directory(&self) -> String;
    fn get_current_directory(&self) -> String;
    fn use_case_sensitive_file_names(&self) -> bool;
}

// Go: outputpaths/outputpaths.go:91 GetOutputJSFileNameWorker
pub fn get_output_js_file_name_worker(
    input_file_name: &str,
    options: &CompilerOptions,
    host: &dyn OutputPathsHost,
) -> String {
    tspath::change_extension(
        &get_output_path_without_changing_extension(input_file_name, &options.out_dir, host),
        get_output_extension(input_file_name, options.jsx),
    )
}

// Go: outputpaths/outputpaths.go:98 GetOutputDeclarationFileNameWorker
pub fn get_output_declaration_file_name_worker(
    input_file_name: &str,
    options: &CompilerOptions,
    host: &dyn OutputPathsHost,
) -> String {
    let mut dir = options.declaration_dir.as_str();
    if dir.is_empty() {
        dir = options.out_dir.as_str();
    }
    tspath::change_extension(
        &get_output_path_without_changing_extension(input_file_name, dir, host),
        &tspath::get_declaration_emit_extension_for_path(input_file_name),
    )
}

// Go: outputpaths/outputpaths.go:109 GetOutputExtension
pub fn get_output_extension(file_name: &str, jsx: JsxEmit) -> &'static str {
    if tspath::file_extension_is(file_name, tspath::EXTENSION_JSON) {
        tspath::EXTENSION_JSON
    } else if jsx == JsxEmit::PRESERVE
        && tspath::file_extension_is_one_of(
            file_name,
            &[tspath::EXTENSION_JSX, tspath::EXTENSION_TSX],
        )
    {
        tspath::EXTENSION_JSX
    } else if tspath::file_extension_is_one_of(
        file_name,
        &[tspath::EXTENSION_MTS, tspath::EXTENSION_MJS],
    ) {
        tspath::EXTENSION_MJS
    } else if tspath::file_extension_is_one_of(
        file_name,
        &[tspath::EXTENSION_CTS, tspath::EXTENSION_CJS],
    ) {
        tspath::EXTENSION_CJS
    } else {
        tspath::EXTENSION_JS
    }
}

// Go: outputpaths/outputpaths.go:155 getOutputPathWithoutChangingExtension
fn get_output_path_without_changing_extension(
    input_file_name: &str,
    output_directory: &str,
    host: &dyn OutputPathsHost,
) -> String {
    if !output_directory.is_empty() {
        let relative = tspath::get_relative_path_from_directory(
            &host.common_source_directory(),
            input_file_name,
            &tspath::ComparePathsOptions {
                use_case_sensitive_file_names: host.use_case_sensitive_file_names(),
                current_directory: host.get_current_directory(),
            },
        );
        return tspath::resolve_path(output_directory, &[&relative]);
    }
    input_file_name.to_string()
}
