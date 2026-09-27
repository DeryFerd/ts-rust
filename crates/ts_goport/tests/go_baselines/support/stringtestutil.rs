//! Port of internal/testutil/stringtestutil (Dedent), Go
//! `stringutil.GuessIndentation`, and a Go `fmt.Sprintf` subset for
//! scenario files.
//!
//! PORT: the texts are port form strings (see
//! `ts_goport::scanner_util::GO_STRING_MARKER`). Go slices the lines by
//! bytes, which can cut a multi-byte whitespace char. `dedent` slices the Go
//! bytes and converts the result back to the port form, so the result is
//! the same Go string.

use std::fmt::Display;

use ts_goport::scanner_util::{go_string_bytes, go_string_from_bytes, is_white_space_like};

// Go: testutil/stringtestutil/stringtestutil.go:9 Dedent
/// Removes blank lines at the start and end, converts tabs in the
/// indentation of each line to 4 spaces, and removes the common
/// indentation.
pub fn dedent(text: &str) -> String {
    let mut lines: Vec<String> = text.split('\n').map(str::to_string).collect();
    // Remove blank lines in the beginning and end
    // and convert all tabs in the beginning of line to spaces
    let mut start_line: Option<usize> = None;
    let mut last_line = 0usize;
    for (i, line) in lines.iter_mut().enumerate() {
        // Go `strings.IndexFunc`: -1 when every char is whitespace-like.
        let first_non_white = line
            .char_indices()
            .find(|&(_, ch)| !is_white_space_like(ch))
            .map(|(at, _)| at);
        if let Some(first_non_white) = first_non_white.filter(|&at| at > 0) {
            *line = line[..first_non_white].replace('\t', "    ") + &line[first_non_white..];
        }
        // Go `strings.TrimSpace` trims Unicode white space, as `str::trim` does.
        if !line.trim().is_empty() {
            if start_line.is_none() {
                start_line = Some(i);
            }
            last_line = i;
        }
    }
    // PORT: Go slices `lines[-1:lastLine+1]` when every line is blank, which
    // panics.
    let start_line = start_line.expect("Dedent: slice bounds out of range (every line is blank)");
    let lines = &lines[start_line..=last_line];
    let mapped_lines: Vec<&str> = lines
        .iter()
        .map(|line| {
            if line.trim().is_empty() {
                ""
            } else {
                line.as_str()
            }
        })
        .collect();
    let indentation = guess_indentation(&mapped_lines);
    let lines: Vec<String> = if indentation > 0 {
        lines
            .iter()
            .map(|line| {
                let bytes = go_string_bytes(line);
                if bytes.len() > indentation {
                    go_string_from_bytes(bytes[indentation..].to_vec())
                } else {
                    String::new()
                }
            })
            .collect()
    } else {
        lines.to_vec()
    };
    lines.join("\n")
}

// Go: stringutil/util.go:115 GuessIndentation
/// The smallest number of leading whitespace-like bytes of the non-empty
/// lines, or 0.
pub fn guess_indentation(lines: &[&str]) -> usize {
    const MAX_SMI_X86: usize = 0x3fff_ffff;
    let mut indentation = MAX_SMI_X86;
    for line in lines {
        if line.is_empty() {
            continue;
        }
        let mut i = 0;
        while i < line.len() && i < indentation {
            // PORT: Go decodes the rune at byte `i`. `i` is always a char
            // boundary here, and a port form unit starts with a char that is
            // not whitespace-like.
            let ch = line[i..].chars().next().expect("a char at a boundary");
            if !is_white_space_like(ch) {
                break;
            }
            i += ch.len_utf8();
        }
        if i < indentation {
            indentation = i;
        }
        if indentation == 0 {
            return 0;
        }
    }
    if indentation == MAX_SMI_X86 {
        return 0;
    }
    indentation
}

/// Go `fmt.Sprintf` for the verbs that scenario files use: `%s`, `%d`,
/// `%t`, `%v` and `%%`. Scenario files use it for JSON text, where the
/// braces would be `format!` placeholders.
///
/// Each verb writes the next argument with `Display`, which gives the Go
/// text for strings, integers and booleans. Like Go, a verb without an
/// argument writes `%!<verb>(MISSING)` and a `%` at the end writes
/// `%!(NOVERB)`.
// PORT: Go checks the argument type against the verb and appends
// `%!(EXTRA type=value)` for unused arguments. `Display` has no Go type name,
// so unused arguments and other verbs, flags or widths panic.
pub fn go_sprintf(format: &str, args: &[&dyn Display]) -> String {
    let mut out = String::with_capacity(format.len());
    let mut next_arg = 0usize;
    let mut chars = format.chars();
    while let Some(ch) = chars.next() {
        if ch != '%' {
            out.push(ch);
            continue;
        }
        match chars.next() {
            None => out.push_str("%!(NOVERB)"),
            Some('%') => out.push('%'),
            Some(verb @ ('s' | 'd' | 't' | 'v')) => {
                if let Some(arg) = args.get(next_arg) {
                    out.push_str(&arg.to_string());
                    next_arg += 1;
                } else {
                    out.push_str("%!");
                    out.push(verb);
                    out.push_str("(MISSING)");
                }
            }
            Some(other) => panic!("go_sprintf: unsupported verb %{other} in {format:?}"),
        }
    }
    assert!(
        next_arg >= args.len(),
        "go_sprintf: {} unused arguments for {format:?}",
        args.len() - next_arg
    );
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stringtestutil_dedent() {
        let text = "\n\t{\n\t\t\"compilerOptions\": {\n\t\t\t\"composite\": true\n\t\t}\n\t}\n\t";
        assert_eq!(
            dedent(text),
            "{\n    \"compilerOptions\": {\n        \"composite\": true\n    }\n}"
        );
        // Blank inner lines become empty; lines shorter than the
        // indentation become empty.
        assert_eq!(dedent("\n    a\n  \n      b\n    "), "a\n\n  b");
        // Mixed tabs and spaces: a tab is 4 spaces.
        assert_eq!(dedent("\t  x\n      y"), "x\ny");
        // No common indentation.
        assert_eq!(dedent("x\n  y"), "x\n  y");
    }

    #[test]
    fn stringutil_guess_indentation() {
        assert_eq!(guess_indentation(&[]), 0);
        assert_eq!(guess_indentation(&["", ""]), 0);
        assert_eq!(guess_indentation(&["    a", "  b", ""]), 2);
        assert_eq!(guess_indentation(&["a", "  b"]), 0);
    }

    #[test]
    fn go_sprintf_verbs() {
        assert_eq!(
            go_sprintf(
                "{\"a\": \"%s\", \"b\": %d, \"c\": %t, \"d\": %v}%%",
                &[&"x", &12, &true, &"y"]
            ),
            "{\"a\": \"x\", \"b\": 12, \"c\": true, \"d\": y}%"
        );
        assert_eq!(go_sprintf("%s %d", &[&"a"]), "a %!d(MISSING)");
        assert_eq!(go_sprintf("100%", &[]), "100%!(NOVERB)");
    }
}
