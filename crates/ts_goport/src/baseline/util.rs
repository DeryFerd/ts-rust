//! Port of the parts of `internal/testutil/tsbaseline/util.go` that the
//! type and symbol baselines use.

use crate::frontend::tspath::path::get_base_file_name;

// Go: tsbaseline/util.go:24 testPathPrefixReplacer
const TEST_PATH_PREFIX_REPLACEMENTS: [(&str, &str); 7] = [
    ("/.ts/", ""),
    ("/.lib/", ""),
    ("/.src/", ""),
    ("bundled:///libs/", ""),
    ("file:///./ts/", "file:///"),
    ("file:///./lib/", "file:///"),
    ("file:///./src/", "file:///"),
];

// Go: tsbaseline/util.go:33 testPathTrailingReplacerTrailingSeparator
const TEST_PATH_TRAILING_REPLACEMENTS: [(&str, &str); 7] = [
    ("/.ts/", "/"),
    ("/.lib/", "/"),
    ("/.src/", "/"),
    ("bundled:///libs/", "/"),
    ("file:///./ts/", "file:///"),
    ("file:///./lib/", "file:///"),
    ("file:///./src/", "file:///"),
];

/// Go `strings.NewReplacer(...).Replace`: scans left to right, and at each
/// position the first pair (in argument order) whose old string matches wins.
/// Matches do not overlap.
fn replace_all(text: &str, pairs: &[(&str, &str)]) -> String {
    let bytes = text.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    'outer: while i < bytes.len() {
        for (old, new) in pairs {
            if bytes[i..].starts_with(old.as_bytes()) {
                out.extend_from_slice(new.as_bytes());
                i += old.len();
                continue 'outer;
            }
        }
        out.push(bytes[i]);
        i += 1;
    }
    // All old and new strings are ASCII, so no UTF-8 sequence is split.
    String::from_utf8(out).expect("ASCII replacements keep UTF-8 valid")
}

// Go: tsbaseline/util.go:44 removeTestPathPrefixes
pub fn remove_test_path_prefixes(text: &str, retain_trailing_directory_separator: bool) -> String {
    if retain_trailing_directory_separator {
        return replace_all(text, &TEST_PATH_TRAILING_REPLACEMENTS);
    }
    replace_all(text, &TEST_PATH_PREFIX_REPLACEMENTS)
}

// Go: tsbaseline/util.go:51 isDefaultLibraryFile
pub fn is_default_library_file(file_path: &str) -> bool {
    let file_name = get_base_file_name(file_path);
    file_name.starts_with("lib.") && file_name.ends_with(".d.ts")
}

/// Go `lineDelimiter.ReplaceAllString(s, "")` with `lineDelimiter` =
/// `\r?\n` (tsbaseline/util.go:11). Removes `\r\n` and `\n`; a lone `\r`
/// stays.
pub fn remove_line_delimiters(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut prev = '\0';
    for ch in text.chars() {
        if ch == '\n' {
            if prev == '\r' {
                out.pop();
            }
        } else {
            out.push(ch);
        }
        prev = ch;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replacer_and_line_delimiters() {
        assert_eq!(
            remove_test_path_prefixes("a/.ts/b bundled:///libs/lib.d.ts", false),
            "ab lib.d.ts"
        );
        assert_eq!(
            remove_test_path_prefixes("file:///./src/x", true),
            "file:///x"
        );
        assert_eq!(remove_line_delimiters("a\r\nb\nc\rd\r\r\n"), "abc\rd\r");
        assert!(is_default_library_file("/x/lib.es5.d.ts"));
        assert!(!is_default_library_file("/x/lib.es5.ts"));
    }
}
