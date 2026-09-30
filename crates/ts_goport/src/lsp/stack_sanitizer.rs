//! Go `internal/lsp/stack_sanitizer.go`.

use crate::lsp::prelude::*;

// VS Code's telemetry pipeline redacts any string matching
// /(key|token|sig|secret|signature|password|passwd|pwd|android:value)[^a-zA-Z0-9]/i
// as `<REDACTED: Generic Secret>`, which trips on innocuous Go frames like
// `getSignatureHelp(`. Insert `X_X` after each trigger keyword that we know
// can appear in our sanitized output, when followed by punctuation we
// actually emit (`(`, `[`, `.`, `|`); reverse by removing the marker (replace
// `X_X` with the empty string) on the dashboard.
//
// Go: lsp/stack_sanitizer.go:17 genericSecretKeywordRegex
// PORT: no regex engine. The Go pattern is
// `(?i)(key|token|signature|sig|pwd)([(\[.|])`; `GENERIC_SECRET_KEYWORDS`
// holds the alternatives in pattern order and `defeat_generic_secret_regex`
// scans for them the way Go's leftmost-first matcher does.
pub const GENERIC_SECRET_KEYWORDS: [&str; 5] = ["key", "token", "signature", "sig", "pwd"];

// Go: `[(\[.|]`, the second group of genericSecretKeywordRegex.
fn is_generic_secret_punctuation(c: char) -> bool {
    matches!(c, '(' | '[' | '.' | '|')
}

// Go `(?i)` matching of one pattern letter (always lowercase ASCII here)
// against one rune: the simple case-folding orbit of the letter. Among the
// letters of the keywords only `k` (K, U+212A KELVIN SIGN) and `s` (S,
// U+017F LATIN SMALL LETTER LONG S) have a non-ASCII member.
fn fold_eq(pattern: char, c: char) -> bool {
    if c.to_ascii_lowercase() == pattern {
        return true;
    }
    match pattern {
        'k' => c == '\u{212A}',
        's' => c == '\u{017F}',
        _ => false,
    }
}

// Tries the pattern at byte offset `start`: the first keyword (in pattern
// order) that matches, followed by one punctuation rune. Returns the end of
// the keyword and the end of the whole match.
fn match_generic_secret_at(s: &str, start: usize) -> Option<(usize, usize)> {
    for keyword in GENERIC_SECRET_KEYWORDS {
        let mut chars = s[start..].char_indices();
        let mut matched = true;
        for pattern in keyword.chars() {
            match chars.next() {
                Some((_, c)) if fold_eq(pattern, c) => {}
                _ => {
                    matched = false;
                    break;
                }
            }
        }
        if !matched {
            continue;
        }
        let keyword_end = match chars.clone().next() {
            Some((offset, _)) => start + offset,
            None => continue,
        };
        match chars.next() {
            Some((offset, c)) if is_generic_secret_punctuation(c) => {
                return Some((keyword_end, start + offset + c.len_utf8()));
            }
            _ => continue,
        }
    }
    None
}

// Go: lsp/stack_sanitizer.go:19 defeatGenericSecretRegex
// Go: `genericSecretKeywordRegex.ReplaceAllString(s, "${1}X_X${2}")`.
pub fn defeat_generic_secret_regex(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut i = 0;
    while i < s.len() {
        if let Some((keyword_end, match_end)) = match_generic_secret_at(s, i) {
            result.push_str(&s[i..keyword_end]);
            result.push_str("X_X");
            result.push_str(&s[keyword_end..match_end]);
            i = match_end;
            continue;
        }
        let c = s[i..].chars().next().expect("index is on a char boundary");
        result.push(c);
        i += c.len_utf8();
    }
    result
}

// Go: lsp/stack_sanitizer.go:23 sanitizeStackTrace
pub fn sanitize_stack_trace(stack: &str) -> String {
    // TODO: should we just look for the first '(' and
    // just strip everything before the prior newline?
    let Some(start_index) = stack.find("runtime/debug.Stack()") else {
        return String::new();
    };
    let stack = &stack[start_index..];

    let mut result = String::new();

    // Go: `strings.Lines`: each line keeps its "\n"; no empty last line.
    for (line_num, line) in stack.split_inclusive('\n').enumerate() {
        if line_num > 0 {
            result.push('\n');
        }

        let mut i = 0;
        let bytes = line.as_bytes();
        // Skip whitespace
        while i < bytes.len() {
            if bytes[i] != b' ' && bytes[i] != b'\t' {
                break;
            }
            i += 1;
        }

        result.push_str(&line[..i]);

        let line = &line[i..];

        // Go N (migration 5f647a841a): the module path is "TypeScript/tsc/".
        if let Some(our_module_index) = line.find("TypeScript/tsc/") {
            let line = &line[our_module_index..];
            write_sanitized_module_or_path(line, &mut result);
        } else {
            result.push_str("(REDACTED FRAME)");
        }
    }

    defeat_generic_secret_regex(&result)
}

// Go: lsp/stack_sanitizer.go:64 writeSanitizedModuleOrPath
pub fn write_sanitized_module_or_path(line: &str, result: &mut String) {
    // We don't expect things like \r, but it doesn't hurt to trim just in case.
    let mut line = line.trim();

    if let Some(plus_hex) = line.find(" +0x") {
        line = &line[..plus_hex];
    } else if let Some(in_goroutine) = line.rfind(" in goroutine ") {
        line = &line[..in_goroutine];
    }

    for (segment_index, segment) in line.split('/').enumerate() {
        if segment_index > 0 {
            result.push_str("|>");
        }

        // See if the string ends with ), and strip out all the arguments.
        if segment.ends_with(')') {
            let Some(open_paren_index) = segment.rfind('(') else {
                // Closing parenthesis, but no opening - bail out.
                result.push_str("???");
                continue;
            };

            let segment = &segment[..open_paren_index];
            result.push_str(segment);
            result.push_str("()");
            continue;
        }

        result.push_str(segment);
    }
}
