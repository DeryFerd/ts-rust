//! TypeScript-style diagnostic formatting with UTF-16 source coordinates.

use std::{
    fmt::Write as _,
    path::{Component, Path, PathBuf},
};

use ts_core::TextRange;

const RESET: &str = "\u{1b}[0m";
const GUTTER: &str = "\u{1b}[7m";
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
            format_pretty(&mut output, diagnostic, &[], options);
        } else {
            format_plain(&mut output, diagnostic, options);
        }
    }
    output
}

/// Formats one diagnostic with its associated source locations.
///
/// Related locations are shown only when contextual output is enabled.
#[must_use]
pub fn format_diagnostic_with_related(
    diagnostic: Diagnostic<'_>,
    related_information: &[Diagnostic<'_>],
    options: FormattingOptions<'_>,
) -> String {
    let mut output = String::new();
    if options.pretty {
        format_pretty(&mut output, &diagnostic, related_information, options);
    } else {
        format_plain(&mut output, &diagnostic, options);
    }
    output
}

fn format_plain(output: &mut String, diagnostic: &Diagnostic<'_>, options: FormattingOptions<'_>) {
    if let Some((file_name, line, column)) = location(diagnostic, options.current_directory) {
        let _ = write!(output, "{file_name}({line},{column}): ");
    }
    write_message(output, diagnostic, false, options.new_line);
    output.push_str(options.new_line);
}

fn format_pretty(
    output: &mut String,
    diagnostic: &Diagnostic<'_>,
    related_information: &[Diagnostic<'_>],
    options: FormattingOptions<'_>,
) {
    if let Some((file_name, line, column)) = location(diagnostic, options.current_directory) {
        let _ = write!(
            output,
            "{CYAN}{file_name}{RESET}:{YELLOW}{line}{RESET}:{YELLOW}{column}{RESET} - "
        );
    }
    write_message(output, diagnostic, true, options.new_line);
    if let (Some(source), Some(range)) = (diagnostic.source_text, diagnostic.range)
        && diagnostic.code != Some(1490)
    {
        output.push_str(options.new_line);
        write_snippet(
            output,
            source,
            range,
            diagnostic.category.color(),
            "",
            options.new_line,
        );
        output.push_str(options.new_line);
    }

    for related in related_information {
        if let Some((file_name, line, column)) = location(related, options.current_directory) {
            output.push_str(options.new_line);
            let _ = write!(
                output,
                "  {CYAN}{file_name}{RESET}:{YELLOW}{line}{RESET}:{YELLOW}{column}{RESET} - "
            );
            write_message_text(output, related.message, options.new_line);
            if let (Some(source), Some(range)) = (related.source_text, related.range) {
                write_snippet(output, source, range, CYAN, "    ", options.new_line);
            }
        }
        output.push_str(options.new_line);
    }
    output.push_str(options.new_line);
}

fn write_message(output: &mut String, diagnostic: &Diagnostic<'_>, color: bool, new_line: &str) {
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
            let _ = write!(output, "{GREY} TS{code}: {RESET}");
        } else {
            let _ = write!(output, " TS{code}: ");
        }
    } else {
        output.push_str(": ");
    }
    write_message_text(output, diagnostic.message, new_line);
}

fn write_message_text(output: &mut String, message: &str, new_line: &str) {
    let mut remaining = message;
    while let Some(index) = remaining.find(['\r', '\n']) {
        output.push_str(&remaining[..index]);
        remaining = &remaining[index..];
        if let Some(tail) = remaining.strip_prefix("\r\n") {
            remaining = tail;
        } else {
            remaining = &remaining[1..];
        }
        output.push_str(new_line);
    }
    output.push_str(remaining);
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
    let normalized_file = file_name.replace('\\', "/");
    let normalized_current = current_directory.replace('\\', "/");
    let file_path = Path::new(&normalized_file);
    let current_path = Path::new(&normalized_current);
    if file_path.is_absolute() && current_path.is_absolute() {
        return relative_disk_path(file_path, current_path).unwrap_or(normalized_file);
    }

    if let (Some((file_drive, file_path)), Some((current_drive, current_path))) = (
        windows_drive_path(&normalized_file),
        windows_drive_path(&normalized_current),
    ) {
        if file_drive.eq_ignore_ascii_case(current_drive) {
            return relative_disk_path(file_path, current_path).unwrap_or(normalized_file);
        }
        return normalized_file;
    }

    file_name.to_owned()
}

fn windows_drive_path(path: &str) -> Option<(&str, &Path)> {
    let bytes = path.as_bytes();
    if bytes.first().is_some_and(u8::is_ascii_alphabetic)
        && bytes.get(1) == Some(&b':')
        && bytes.get(2) == Some(&b'/')
    {
        return Some((&path[..2], Path::new(&path[2..])));
    }
    None
}

fn relative_disk_path(file_path: &Path, current_path: &Path) -> Option<String> {
    let file_components = reduced_path_components(file_path);
    let current_components = reduced_path_components(current_path);
    let common = file_components
        .iter()
        .zip(&current_components)
        .take_while(|(file, current)| file == current)
        .count();
    if common == 0 {
        return None;
    }

    let mut relative = PathBuf::new();
    for _ in common..current_components.len() {
        relative.push("..");
    }
    for component in &file_components[common..] {
        relative.push(component.as_os_str());
    }
    if relative.as_os_str().is_empty() {
        return Some(String::new());
    }
    Some(relative.to_string_lossy().replace('\\', "/"))
}

fn reduced_path_components(path: &Path) -> Vec<Component<'_>> {
    let mut reduced = Vec::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir if matches!(reduced.last(), Some(Component::Normal(_))) => {
                reduced.pop();
            }
            Component::ParentDir if matches!(reduced.last(), Some(Component::RootDir)) => {}
            _ => reduced.push(component),
        }
    }
    reduced
}

fn line_and_utf16_column(source: &str, byte_position: usize) -> (usize, usize) {
    line_and_utf16_column_at(source, &ecma_line_starts(source), byte_position)
}

fn line_and_utf16_column_at(
    source: &str,
    line_starts: &[usize],
    byte_position: usize,
) -> (usize, usize) {
    let mut position = byte_position.min(source.len());
    while !source.is_char_boundary(position) {
        position -= 1;
    }
    let line = line_starts
        .partition_point(|line_start| *line_start <= position)
        .saturating_sub(1);
    let column = source[line_starts[line]..position].encode_utf16().count();
    (line, column)
}

fn ecma_line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    let mut characters = source.char_indices().peekable();
    while let Some((index, character)) = characters.next() {
        match character {
            '\r' => {
                if let Some(&(next_index, '\n')) = characters.peek() {
                    characters.next();
                    starts.push(next_index + 1);
                } else {
                    starts.push(index + 1);
                }
            }
            '\n' => starts.push(index + 1),
            '\u{2028}' | '\u{2029}' => starts.push(index + character.len_utf8()),
            _ => {}
        }
    }
    starts
}

fn write_snippet(
    output: &mut String,
    source: &str,
    range: TextRange,
    color: &str,
    indent: &str,
    new_line: &str,
) {
    let starts = ecma_line_starts(source);
    let start = range.start.get() as usize;
    let end = (range.end.get() as usize).max(start);
    let (first_line, first_column) = line_and_utf16_column_at(source, &starts, start);
    let (last_line, mut last_column) = line_and_utf16_column_at(source, &starts, end);
    if start == end {
        last_column += 1;
    }

    let abbreviated = last_line.saturating_sub(first_line) >= 4;
    let gutter_width = if abbreviated {
        (last_line + 1).to_string().len().max(3)
    } else {
        (last_line + 1).to_string().len()
    };

    let mut line = first_line;
    while line <= last_line {
        output.push_str(new_line);
        if abbreviated && line > first_line + 1 && line < last_line - 1 {
            let _ = write!(
                output,
                "{indent}{GUTTER}{:>gutter_width$}{RESET} {new_line}",
                "..."
            );
            line = last_line - 1;
        }

        let line_start = starts[line];
        let line_end = starts.get(line + 1).copied().unwrap_or(source.len());
        let content = source[line_start..line_end].trim_end().replace('\t', " ");
        let _ = write!(
            output,
            "{indent}{GUTTER}{:>gutter_width$}{RESET} {content}{new_line}",
            line + 1
        );
        let _ = write!(
            output,
            "{indent}{GUTTER}{:>gutter_width$}{RESET} {color}",
            ""
        );

        if line == first_line {
            let marked_end = if line == last_line {
                last_column
            } else {
                content.encode_utf16().count()
            };
            output.push_str(&" ".repeat(first_column));
            output.push_str(&"~".repeat(marked_end.saturating_sub(first_column)));
        } else if line == last_line {
            output.push_str(&"~".repeat(last_column));
        } else {
            output.push_str(&"~".repeat(content.encode_utf16().count()));
        }

        output.push_str(RESET);
        line += 1;
    }
}

#[cfg(test)]
mod tests {
    use ts_core::{TextPos, TextRange};

    use super::{
        Diagnostic, DiagnosticCategory, FormattingOptions, format_diagnostic_with_related,
        format_diagnostics, relative_file_name,
    };

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
    fn formats_absolute_paths_outside_the_current_directory_relatively() {
        let diagnostic = Diagnostic {
            file_name: Some("/project/tests/example.ts"),
            source_text: Some("missing"),
            range: Some(TextRange::new(TextPos::new(0), TextPos::new(7))),
            code: Some(2304),
            category: DiagnosticCategory::Error,
            message: "Cannot find name 'missing'.",
        };

        assert_eq!(
            format_diagnostics(
                &[diagnostic],
                FormattingOptions {
                    current_directory: "/project/crates/compiler",
                    ..FormattingOptions::default()
                },
            ),
            "../../tests/example.ts(1,1): error TS2304: Cannot find name 'missing'.\n"
        );
    }

    #[test]
    fn preserves_relative_paths_and_converts_root_children() {
        let diagnostic = Diagnostic {
            file_name: Some("../tests/example.ts"),
            source_text: Some("missing"),
            range: Some(TextRange::new(TextPos::new(0), TextPos::new(7))),
            code: Some(2304),
            category: DiagnosticCategory::Error,
            message: "Cannot find name 'missing'.",
        };
        assert_eq!(
            format_diagnostics(
                &[diagnostic],
                FormattingOptions {
                    current_directory: "/project",
                    ..FormattingOptions::default()
                },
            ),
            "../tests/example.ts(1,1): error TS2304: Cannot find name 'missing'.\n"
        );

        let rooted = Diagnostic {
            file_name: Some("/example.ts"),
            ..diagnostic
        };
        assert_eq!(
            format_diagnostics(
                &[rooted],
                FormattingOptions {
                    current_directory: "/",
                    ..FormattingOptions::default()
                },
            ),
            "example.ts(1,1): error TS2304: Cannot find name 'missing'.\n"
        );
    }

    #[test]
    fn relative_paths_match_upstream_windows_and_unc_rules() {
        assert_eq!(
            relative_file_name(
                r"C:\project\tests\example.ts",
                r"c:\project\crates\compiler",
            ),
            "../../tests/example.ts"
        );
        assert_eq!(
            relative_file_name(r"C:\project\src\example.ts", "C:/project"),
            "src/example.ts"
        );
        assert_eq!(
            relative_file_name(r"D:\project\example.ts", r"C:\project"),
            "D:/project/example.ts"
        );
        assert_eq!(
            relative_file_name(r"\\server\share\tests\example.ts", r"\\server\share\src",),
            "../tests/example.ts"
        );
    }

    #[test]
    fn relative_paths_reduce_dot_and_parent_segments() {
        assert_eq!(
            relative_file_name("/project/source/../tests/example.ts", "/project/./src",),
            "../tests/example.ts"
        );
        assert_eq!(relative_file_name("/project", "/project"), "");
        assert_eq!(relative_file_name("/", "/project"), "..");
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

    #[test]
    fn pretty_diagnostics_include_cross_file_related_information() {
        let primary_source = "const result = pair(\"left\");\n";
        let related_source = "export function pair(left: string, right: number): number;\n";
        let primary_start = primary_source.find("pair").unwrap();
        let related_start = related_source.find("right").unwrap();
        let primary = Diagnostic {
            file_name: Some("/project/importer.ts"),
            source_text: Some(primary_source),
            range: Some(TextRange::new(
                TextPos::new(u32::try_from(primary_start).unwrap()),
                TextPos::new(u32::try_from(primary_start + "pair".len()).unwrap()),
            )),
            code: Some(2554),
            category: DiagnosticCategory::Error,
            message: "Expected 2 arguments, but got 1.",
        };
        let related = Diagnostic {
            file_name: Some("/project/target.ts"),
            source_text: Some(related_source),
            range: Some(TextRange::new(
                TextPos::new(u32::try_from(related_start).unwrap()),
                TextPos::new(u32::try_from(related_start + "right: number".len()).unwrap()),
            )),
            code: Some(6210),
            category: DiagnosticCategory::Message,
            message: "An argument for 'right' was not provided.",
        };

        let formatted = format_diagnostic_with_related(
            primary,
            &[related],
            FormattingOptions {
                current_directory: "/project",
                pretty: true,
                ..FormattingOptions::default()
            },
        );

        assert!(formatted.contains("\u{1b}[96mimporter.ts\u{1b}[0m"));
        assert!(formatted.contains("TS2554"));
        assert!(formatted.contains(concat!(
            "\n\n  \u{1b}[96mtarget.ts\u{1b}[0m:",
            "\u{1b}[93m1\u{1b}[0m:\u{1b}[93m36\u{1b}[0m - ",
            "An argument for 'right' was not provided.\n",
            "    \u{1b}[7m1\u{1b}[0m export function pair(left: string, right: number): number;\n",
            "    \u{1b}[7m \u{1b}[0m \u{1b}[96m                                   ~~~~~~~~~~~~~\u{1b}[0m\n\n",
        )));
        assert!(!formatted.contains("TS6210"));
    }

    #[test]
    fn plain_diagnostics_suppress_related_information() {
        let primary = Diagnostic {
            file_name: Some("/project/importer.ts"),
            source_text: Some("pair()"),
            range: Some(TextRange::new(TextPos::new(0), TextPos::new(4))),
            code: Some(2554),
            category: DiagnosticCategory::Error,
            message: "Expected 1 argument, but got 0.",
        };
        let related = Diagnostic {
            file_name: Some("/project/target.ts"),
            source_text: Some("function pair(value: string): void;"),
            range: Some(TextRange::new(TextPos::new(14), TextPos::new(19))),
            code: Some(6210),
            category: DiagnosticCategory::Message,
            message: "An argument for 'value' was not provided.",
        };
        let options = FormattingOptions {
            current_directory: "/project",
            ..FormattingOptions::default()
        };

        assert_eq!(
            format_diagnostic_with_related(primary, &[related], options),
            format_diagnostics(&[primary], options)
        );
    }

    #[test]
    fn related_information_keeps_input_order_and_configured_newlines() {
        let primary = Diagnostic {
            file_name: Some("/project/main.ts"),
            source_text: Some("value"),
            range: Some(TextRange::new(TextPos::new(0), TextPos::new(5))),
            code: Some(2300),
            category: DiagnosticCategory::Error,
            message: "Duplicate identifier 'value'.",
        };
        let first = Diagnostic {
            file_name: Some("/project/first.ts"),
            source_text: Some("value"),
            range: Some(TextRange::new(TextPos::new(0), TextPos::new(5))),
            code: Some(6203),
            category: DiagnosticCategory::Message,
            message: "'value' was also declared here.\n  First detail.",
        };
        let second = Diagnostic {
            file_name: Some("/project/second.ts"),
            message: "and here.",
            code: Some(6204),
            ..first
        };
        let formatted = format_diagnostic_with_related(
            primary,
            &[first, second],
            FormattingOptions {
                current_directory: "/project",
                new_line: "\r\n",
                pretty: true,
            },
        );

        let first_position = formatted.find("first.ts").unwrap();
        let second_position = formatted.find("second.ts").unwrap();
        assert!(first_position < second_position);
        assert!(formatted.contains("'value' was also declared here.\r\n  First detail."));
        assert!(
            formatted
                .as_bytes()
                .windows(2)
                .filter(|pair| pair[1] == b'\n')
                .all(|pair| pair[0] == b'\r')
        );
    }

    #[test]
    fn diagnostic_details_use_the_configured_newline() {
        let diagnostic = Diagnostic {
            file_name: None,
            source_text: None,
            range: None,
            code: Some(2322),
            category: DiagnosticCategory::Error,
            message: "Type mismatch.\n  First detail.\r\n    Second detail.\rThird detail.",
        };

        assert_eq!(
            format_diagnostics(
                &[diagnostic],
                FormattingOptions {
                    new_line: "\r\n",
                    ..FormattingOptions::default()
                },
            ),
            concat!(
                "error TS2322: Type mismatch.\r\n",
                "  First detail.\r\n",
                "    Second detail.\r\n",
                "Third detail.\r\n",
            )
        );
    }

    #[test]
    fn preserves_duplicate_diagnostics_and_input_order() {
        let first = Diagnostic {
            file_name: None,
            source_text: None,
            range: None,
            code: Some(2300),
            category: DiagnosticCategory::Error,
            message: "Duplicate identifier 'value'.",
        };
        let second = Diagnostic {
            message: "Duplicate identifier 'other'.",
            ..first
        };

        assert_eq!(
            format_diagnostics(&[first, second, first], FormattingOptions::default()),
            concat!(
                "error TS2300: Duplicate identifier 'value'.\n",
                "error TS2300: Duplicate identifier 'other'.\n",
                "error TS2300: Duplicate identifier 'value'.\n",
            )
        );
    }

    #[test]
    fn pretty_diagnostics_match_upstream_spacing_and_gutters() {
        let source = "let answer: string = 42;\n";
        let diagnostic = Diagnostic {
            file_name: Some("main.ts"),
            source_text: Some(source),
            range: Some(TextRange::new(TextPos::new(21), TextPos::new(23))),
            code: Some(2322),
            category: DiagnosticCategory::Error,
            message: "Type 'number' is not assignable to type 'string'.",
        };

        assert_eq!(
            format_diagnostics(
                &[diagnostic],
                FormattingOptions {
                    pretty: true,
                    ..FormattingOptions::default()
                },
            ),
            concat!(
                "\u{1b}[96mmain.ts\u{1b}[0m:\u{1b}[93m1\u{1b}[0m:",
                "\u{1b}[93m22\u{1b}[0m - ",
                "\u{1b}[91merror\u{1b}[0m\u{1b}[90m TS2322: \u{1b}[0m",
                "Type 'number' is not assignable to type 'string'.\n\n",
                "\u{1b}[7m1\u{1b}[0m let answer: string = 42;\n",
                "\u{1b}[7m \u{1b}[0m \u{1b}[91m                     ~~\u{1b}[0m\n\n",
            )
        );
    }

    #[test]
    fn diagnostics_use_ecmascript_line_breaks_and_utf16_columns() {
        let source = "first\rsecond\r\n😀third\u{2028}fourth\u{2029}last";
        let start = source.find("third").unwrap();
        let diagnostic = Diagnostic {
            file_name: Some("main.ts"),
            source_text: Some(source),
            range: Some(TextRange::new(
                TextPos::new(u32::try_from(start).unwrap()),
                TextPos::new(u32::try_from(start + "third".len()).unwrap()),
            )),
            code: Some(2304),
            category: DiagnosticCategory::Error,
            message: "Cannot find name 'third'.",
        };

        assert_eq!(
            format_diagnostics(&[diagnostic], FormattingOptions::default()),
            "main.ts(3,3): error TS2304: Cannot find name 'third'.\n"
        );

        let last_start = source.find("last").unwrap();
        let last_diagnostic = Diagnostic {
            range: Some(TextRange::new(
                TextPos::new(u32::try_from(last_start).unwrap()),
                TextPos::new(u32::try_from(last_start + "last".len()).unwrap()),
            )),
            message: "Cannot find name 'last'.",
            ..diagnostic
        };
        assert_eq!(
            format_diagnostics(&[last_diagnostic], FormattingOptions::default()),
            "main.ts(5,1): error TS2304: Cannot find name 'last'.\n"
        );
    }

    #[test]
    fn pretty_diagnostics_count_surrogate_pairs_and_use_crlf() {
        let source = "first\r\n😀name\r\n";
        let start = source.find("name").unwrap();
        let diagnostic = Diagnostic {
            file_name: Some("main.ts"),
            source_text: Some(source),
            range: Some(TextRange::new(
                TextPos::new(u32::try_from(start).unwrap()),
                TextPos::new(u32::try_from(start + "name".len()).unwrap()),
            )),
            code: Some(2304),
            category: DiagnosticCategory::Error,
            message: "Cannot find name 'name'.\n  Related detail.",
        };
        let formatted = format_diagnostics(
            &[diagnostic],
            FormattingOptions {
                new_line: "\r\n",
                pretty: true,
                ..FormattingOptions::default()
            },
        );

        assert!(formatted.contains("\u{1b}[93m2\u{1b}[0m:\u{1b}[93m3\u{1b}[0m"));
        assert!(formatted.contains("Cannot find name 'name'.\r\n  Related detail.\r\n\r\n"));
        assert!(formatted.contains("\u{1b}[7m2\u{1b}[0m 😀name\r\n"));
        assert!(formatted.contains("\u{1b}[91m  ~~~~\u{1b}[0m\r\n\r\n"));
        assert!(
            formatted
                .as_bytes()
                .windows(2)
                .filter(|pair| pair[1] == b'\n')
                .all(|pair| pair[0] == b'\r')
        );
    }

    #[test]
    fn pretty_diagnostics_mark_both_utf16_units_of_an_astral_character() {
        let diagnostic = Diagnostic {
            file_name: Some("main.ts"),
            source_text: Some("😀value"),
            range: Some(TextRange::new(TextPos::new(0), TextPos::new(4))),
            code: Some(1005),
            category: DiagnosticCategory::Error,
            message: "Expected token.",
        };
        let formatted = format_diagnostics(
            &[diagnostic],
            FormattingOptions {
                pretty: true,
                ..FormattingOptions::default()
            },
        );

        assert!(formatted.contains("\u{1b}[91m~~\u{1b}[0m"));
    }

    #[test]
    fn pretty_diagnostics_abbreviate_spans_over_five_lines() {
        let source = "one\ntwo\nthree\nfour\nfive\nsix\nseven";
        let diagnostic = Diagnostic {
            file_name: Some("main.ts"),
            source_text: Some(source),
            range: Some(TextRange::new(TextPos::new(1), TextPos::new(30))),
            code: Some(1005),
            category: DiagnosticCategory::Error,
            message: "Expected token.",
        };
        let formatted = format_diagnostics(
            &[diagnostic],
            FormattingOptions {
                pretty: true,
                ..FormattingOptions::default()
            },
        );

        assert!(formatted.contains("\u{1b}[7m  1\u{1b}[0m one"));
        assert!(formatted.contains("\u{1b}[7m  2\u{1b}[0m two"));
        assert!(formatted.contains("\u{1b}[7m...\u{1b}[0m"));
        assert!(!formatted.contains("three"));
        assert!(!formatted.contains("four"));
        assert!(formatted.contains("\u{1b}[7m  6\u{1b}[0m six"));
        assert!(formatted.contains("\u{1b}[7m  7\u{1b}[0m seven"));
    }

    #[test]
    fn pretty_diagnostics_do_not_render_binary_file_contents() {
        let diagnostic = Diagnostic {
            file_name: Some("main.ts"),
            source_text: Some("binary data"),
            range: Some(TextRange::new(TextPos::new(0), TextPos::new(6))),
            code: Some(1490),
            category: DiagnosticCategory::Error,
            message: "File appears to be binary.",
        };
        let formatted = format_diagnostics(
            &[diagnostic],
            FormattingOptions {
                pretty: true,
                ..FormattingOptions::default()
            },
        );

        assert!(!formatted.contains("binary data"));
        assert!(formatted.ends_with("File appears to be binary.\n"));
    }

    #[test]
    fn pretty_diagnostics_mark_zero_length_ranges() {
        let diagnostic = Diagnostic {
            file_name: Some("main.ts"),
            source_text: Some("value"),
            range: Some(TextRange::new(TextPos::new(2), TextPos::new(2))),
            code: Some(1005),
            category: DiagnosticCategory::Error,
            message: "Expected token.",
        };
        let formatted = format_diagnostics(
            &[diagnostic],
            FormattingOptions {
                pretty: true,
                ..FormattingOptions::default()
            },
        );

        assert!(formatted.contains("\u{1b}[91m  ~\u{1b}[0m"));
    }
}
