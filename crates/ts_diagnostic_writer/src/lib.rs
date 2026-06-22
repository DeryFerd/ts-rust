//! TypeScript-style diagnostic formatting with UTF-16 source coordinates.

use std::fmt::Write as _;

use ts_core::TextRange;

const RESET: &str = "\u{1b}[0m";
const GREY: &str = "\u{1b}[90m";
const RED: &str = "\u{1b}[91m";
const YELLOW: &str = "\u{1b}[93m";
const BLUE: &str = "\u{1b}[94m";
const CYAN: &str = "\u{1b}[96m";

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum DiagnosticCategory {
    #[default]
    Error,
    Warning,
    Suggestion,
    Message,
}

impl DiagnosticCategory {
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Error => "error",
            Self::Warning => "warning",
            Self::Suggestion => "suggestion",
            Self::Message => "message",
        }
    }

    const fn color(self) -> &'static str {
        match self {
            Self::Error => RED,
            Self::Warning => YELLOW,
            Self::Suggestion => GREY,
            Self::Message => BLUE,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Diagnostic<'a> {
    pub file_name: Option<&'a str>,
    pub source_text: Option<&'a str>,
    pub range: Option<TextRange>,
    pub code: Option<u32>,
    pub category: DiagnosticCategory,
    pub message: &'a str,
}

#[derive(Clone, Copy, Debug)]
pub struct FormattingOptions<'a> {
    pub current_directory: &'a str,
    pub new_line: &'a str,
    pub pretty: bool,
}

impl Default for FormattingOptions<'_> {
    fn default() -> Self {
        Self {
            current_directory: "",
            new_line: "\n",
            pretty: false,
        }
    }
}

#[must_use]
pub fn format_diagnostics(
    diagnostics: &[Diagnostic<'_>],
    options: FormattingOptions<'_>,
) -> String {
    let mut output = String::new();
    for diagnostic in diagnostics {
        if options.pretty {
            format_pretty(&mut output, diagnostic, options);
        } else {
            format_plain(&mut output, diagnostic, options);
        }
    }
    output
}

fn format_plain(output: &mut String, diagnostic: &Diagnostic<'_>, options: FormattingOptions<'_>) {
    if let Some((file_name, line, column)) = location(diagnostic, options.current_directory) {
        let _ = write!(output, "{file_name}({line},{column}): ");
    }
    write_message(output, diagnostic, false);
    output.push_str(options.new_line);
}

fn format_pretty(output: &mut String, diagnostic: &Diagnostic<'_>, options: FormattingOptions<'_>) {
    if let Some((file_name, line, column)) = location(diagnostic, options.current_directory) {
        let _ = write!(
            output,
            "{CYAN}{file_name}{RESET}:{YELLOW}{line}{RESET}:{YELLOW}{column}{RESET} - "
        );
    }
    write_message(output, diagnostic, true);
    if let (Some(source), Some(range)) = (diagnostic.source_text, diagnostic.range) {
        output.push_str(options.new_line);
        write_snippet(
            output,
            source,
            range,
            diagnostic.category.color(),
            options.new_line,
        );
    }
    output.push_str(options.new_line);
}

fn write_message(output: &mut String, diagnostic: &Diagnostic<'_>, color: bool) {
    if color {
        let _ = write!(
            output,
            "{}{}{}",
            diagnostic.category.color(),
            diagnostic.category.name(),
            RESET
        );
    } else {
        output.push_str(diagnostic.category.name());
    }
    if let Some(code) = diagnostic.code {
        if color {
            let _ = write!(output, "{GREY} TS{code}:{RESET} ");
        } else {
            let _ = write!(output, " TS{code}: ");
        }
    } else {
        output.push_str(": ");
    }
    output.push_str(diagnostic.message);
}

fn location(
    diagnostic: &Diagnostic<'_>,
    current_directory: &str,
) -> Option<(String, usize, usize)> {
    let file_name = relative_file_name(diagnostic.file_name?, current_directory);
    let source = diagnostic.source_text?;
    let position = diagnostic.range?.start.get() as usize;
    let (line, column) = line_and_utf16_column(source, position);
    Some((file_name, line + 1, column + 1))
}

fn relative_file_name(file_name: &str, current_directory: &str) -> String {
    let current = current_directory.trim_end_matches(['/', '\\']);
    if !current.is_empty()
        && let Some(relative) = file_name.strip_prefix(current)
        && let Some(relative) = relative.strip_prefix(['/', '\\'])
    {
        return relative.to_owned();
    }
    file_name.to_owned()
}

fn line_and_utf16_column(source: &str, byte_position: usize) -> (usize, usize) {
    let position = byte_position.min(source.len());
    let prefix = &source[..position];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count();
    let line_start = prefix.rfind('\n').map_or(0, |index| index + 1);
    let column = prefix[line_start..].encode_utf16().count();
    (line, column)
}

fn write_snippet(output: &mut String, source: &str, range: TextRange, color: &str, new_line: &str) {
    let start = range.start.get() as usize;
    let end = (range.end.get() as usize).max(start.saturating_add(1));
    let (line, column) = line_and_utf16_column(source, start);
    let line_start = source[..start.min(source.len())]
        .rfind('\n')
        .map_or(0, |index| index + 1);
    let line_end = source[line_start..]
        .find(['\r', '\n'])
        .map_or(source.len(), |index| line_start + index);
    let content = source[line_start..line_end].replace('\t', " ");
    let marked_end = end.min(line_end);
    let (_, end_column) = line_and_utf16_column(source, marked_end);
    let mark_len = end_column.saturating_sub(column).max(1);
    let gutter_width = (line + 1).to_string().len();
    let _ = write!(
        output,
        "{GREY}{:>gutter_width$}{RESET} {content}{new_line}",
        line + 1
    );
    let _ = write!(
        output,
        "{GREY}{:>gutter_width$}{RESET} {color}{}{}{RESET}",
        "",
        " ".repeat(column),
        "~".repeat(mark_len)
    );
}

#[cfg(test)]
mod tests {
    use ts_core::{TextPos, TextRange};

    use super::{Diagnostic, DiagnosticCategory, FormattingOptions, format_diagnostics};

    #[test]
    fn formats_plain_diagnostics_with_relative_utf16_locations() {
        let source = "const 😀value = 1;\n";
        let diagnostic = Diagnostic {
            file_name: Some("/project/src/main.ts"),
            source_text: Some(source),
            range: Some(TextRange::new(TextPos::new(10), TextPos::new(15))),
            code: Some(2304),
            category: DiagnosticCategory::Error,
            message: "Cannot find name 'value'.",
        };
        assert_eq!(
            format_diagnostics(
                &[diagnostic],
                FormattingOptions {
                    current_directory: "/project",
                    ..FormattingOptions::default()
                },
            ),
            "src/main.ts(1,9): error TS2304: Cannot find name 'value'.\n"
        );
    }

    #[test]
    fn formats_contextual_diagnostics_and_global_messages() {
        let source = "let answer: string = 42;";
        let diagnostics = [
            Diagnostic {
                file_name: Some("main.ts"),
                source_text: Some(source),
                range: Some(TextRange::new(TextPos::new(21), TextPos::new(23))),
                code: Some(2322),
                category: DiagnosticCategory::Error,
                message: "Type 'number' is not assignable to type 'string'.",
            },
            Diagnostic {
                file_name: None,
                source_text: None,
                range: None,
                code: None,
                category: DiagnosticCategory::Warning,
                message: "global warning",
            },
        ];
        let formatted = format_diagnostics(
            &diagnostics,
            FormattingOptions {
                pretty: true,
                ..FormattingOptions::default()
            },
        );
        assert!(formatted.contains("main.ts"));
        assert!(formatted.contains("TS2322"));
        assert!(formatted.contains("42"));
        assert!(formatted.contains("~~"));
        assert!(formatted.contains("global warning"));
        assert!(formatted.contains("\u{1b}[91m"));
    }
}
