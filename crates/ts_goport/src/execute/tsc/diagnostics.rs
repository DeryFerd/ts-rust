//! Go: execute/tsc/diagnostics.go (diagnostic, error summary and status
//! reporters), with the `diagnosticwriter` pieces they call, and
//! execute/tsc/help.go (`PrintVersion`, `PrintBuildHelp` and the helpers
//! they call).
//!
//! PORT: the locale parameters are dropped: the port has only English
//! messages. Go `diagnosticwriter.FileLike` is the diagnostic's source file
//! node.

use crate::prelude::*;

use std::time::{SystemTime, UNIX_EPOCH};

use super::compile::{System, Writer, write_str};
use crate::frontend::tsoptions::{
    CommandLineOption, CommandLineOptionKind, CompilerOptionsValue, TSC_BUILD_OPTION,
};
use crate::frontend::tspath::{ComparePathsOptions, convert_to_relative_path, path_is_absolute};
use ts_diagnostics::{Category, Message};

// Go: diagnosticwriter/diagnosticwriter.go:24 FormattingOptions
// PORT: the Go `Locale` field is dropped.
#[derive(Clone, Debug, Default)]
pub struct FormattingOptions {
    pub new_line: String,
    pub compare_paths_options: ComparePathsOptions,
}

// Go: execute/tsc/diagnostics.go:15 getFormatOptsOfSys
fn get_format_opts_of_sys(sys: &dyn System) -> FormattingOptions {
    FormattingOptions {
        new_line: "\n".to_string(),
        compare_paths_options: ComparePathsOptions {
            current_directory: sys.get_current_directory(),
            use_case_sensitive_file_names: sys.fs().use_case_sensitive_file_names(),
        },
    }
}

// Go: execute/tsc/diagnostics.go:26 DiagnosticReporter
pub type DiagnosticReporter = Rc<dyn Fn(&Diagnostic)>;

// Go: execute/tsc/diagnostics.go:28 QuietDiagnosticReporter
pub fn quiet_diagnostic_reporter() -> DiagnosticReporter {
    Rc::new(|_diagnostic: &Diagnostic| {})
}

// Go: execute/tsc/diagnostics.go:30 CreateDiagnosticReporter
pub fn create_diagnostic_reporter(
    sys: &dyn System,
    w: Writer,
    options: &CompilerOptions,
) -> DiagnosticReporter {
    if options.quiet.is_true() {
        return quiet_diagnostic_reporter();
    }
    let format_opts = get_format_opts_of_sys(sys);
    if should_be_pretty(sys, Some(options)) {
        return Rc::new(move |diagnostic: &Diagnostic| {
            format_diagnostic_with_color_and_context(&w, diagnostic, &format_opts);
            write_str(&w, &format_opts.new_line);
        });
    }
    Rc::new(move |diagnostic: &Diagnostic| {
        write_format_diagnostic(&w, diagnostic, &format_opts);
    })
}

// Go: execute/tsc/diagnostics.go:46 defaultIsPretty
fn default_is_pretty(sys: &dyn System) -> bool {
    if !sys.get_environment_variable("NO_COLOR").is_empty() {
        return false;
    }
    if !sys.get_environment_variable("FORCE_COLOR").is_empty() {
        return true;
    }
    sys.write_output_is_tty()
}

// Go: execute/tsc/diagnostics.go:56 shouldBePretty
pub fn should_be_pretty(sys: &dyn System, options: Option<&CompilerOptions>) -> bool {
    match options {
        Some(options) if !options.pretty.is_unknown() => options.pretty.is_true(),
        _ => default_is_pretty(sys),
    }
}

// Go: execute/tsc/diagnostics.go:63 colors
#[derive(Clone, Debug, Default)]
pub struct Colors {
    show_colors: bool,

    is_windows: bool,
    is_windows_terminal: bool,
    is_vs_code: bool,
    supports_richer_colors: bool,
}

// Go: execute/tsc/diagnostics.go:72 createColors
pub fn create_colors(sys: &dyn System) -> Colors {
    if !default_is_pretty(sys) {
        return Colors {
            show_colors: false,
            ..Colors::default()
        };
    }

    let os = sys.get_environment_variable("OS");
    let is_windows = os.to_lowercase().contains("windows");
    let is_windows_terminal = !sys.get_environment_variable("WT_SESSION").is_empty();
    let is_vs_code = sys.get_environment_variable("TERM_PROGRAM") == "vscode";
    let supports_richer_colors = sys.get_environment_variable("COLORTERM") == "truecolor"
        || sys.get_environment_variable("TERM") == "xterm-256color";

    Colors {
        show_colors: true,
        is_windows,
        is_windows_terminal,
        is_vs_code,
        supports_richer_colors,
    }
}

impl Colors {
    // Go: execute/tsc/diagnostics.go:93 (*colors).bold
    pub fn bold(&self, str: &str) -> String {
        if !self.show_colors {
            return str.to_string();
        }
        format!("\x1b[1m{str}\x1b[22m")
    }

    // Go: execute/tsc/diagnostics.go:100 (*colors).blue
    pub fn blue(&self, str: &str) -> String {
        if !self.show_colors {
            return str.to_string();
        }

        // Effectively Powershell and Command prompt users use cyan instead
        // of blue because the default theme doesn't show blue with enough contrast.
        if self.is_windows && !self.is_windows_terminal && !self.is_vs_code {
            return self.bright_white(str);
        }
        format!("\x1b[94m{str}\x1b[39m")
    }

    // Go: execute/tsc/diagnostics.go:113 (*colors).blueBackground
    pub fn blue_background(&self, str: &str) -> String {
        if !self.show_colors {
            return str.to_string();
        }
        if self.supports_richer_colors {
            format!("\x1B[48;5;68m{str}\x1B[39;49m")
        } else {
            format!("\x1b[44m{str}\x1B[39;49m")
        }
    }

    // Go: execute/tsc/diagnostics.go:124 (*colors).brightWhite
    pub fn bright_white(&self, str: &str) -> String {
        if !self.show_colors {
            return str.to_string();
        }
        format!("\x1b[97m{str}\x1b[39m")
    }
}

// Go: execute/tsc/diagnostics.go:131 DiagnosticsReporter
pub type DiagnosticsReporter = Rc<dyn Fn(&[Diagnostic])>;

// Go: execute/tsc/diagnostics.go:133 QuietDiagnosticsReporter
pub fn quiet_diagnostics_reporter() -> DiagnosticsReporter {
    Rc::new(|_diagnostics: &[Diagnostic]| {})
}

// Go: execute/tsc/diagnostics.go:135 CreateReportErrorSummary
// PORT: Go reads `sys.Writer()` on each report. The reporter cannot keep
// `sys`, so it reads the writer when it is made. A system's writer does
// not change after the system is made.
pub fn create_report_error_summary(
    sys: &dyn System,
    options: Option<&CompilerOptions>,
) -> DiagnosticsReporter {
    if should_be_pretty(sys, options) {
        let format_opts = get_format_opts_of_sys(sys);
        let writer = sys.writer();
        return Rc::new(move |diagnostics: &[Diagnostic]| {
            write_error_summary_text(&writer, diagnostics, &format_opts);
        });
    }
    quiet_diagnostics_reporter()
}

// Go: execute/tsc/diagnostics.go:145 CreateBuilderStatusReporter
// PORT: Go `options` can be nil only through `shouldBePretty`; the quiet
// check reads it, so it is required here.
pub fn create_builder_status_reporter(
    sys: Rc<dyn System>,
    w: Writer,
    options: &CompilerOptions,
) -> DiagnosticReporter {
    if options.quiet.is_true() {
        return quiet_diagnostic_reporter();
    }

    let format_opts = get_format_opts_of_sys(sys.as_ref());
    let write_status: fn(&Writer, &str, &Diagnostic, &FormattingOptions) =
        if should_be_pretty(sys.as_ref(), Some(options)) {
            format_diagnostics_status_with_color_and_time
        } else {
            format_diagnostics_status_and_time
        };
    Rc::new(move |diagnostic: &Diagnostic| {
        write_status(&w, &format_status_time(sys.now()), diagnostic, &format_opts);
        write_str(
            &w,
            &format!("{}{}", format_opts.new_line, format_opts.new_line),
        );
    })
}

// Go: execute/tsc/diagnostics.go:161 CreateWatchStatusReporter
pub fn create_watch_status_reporter(
    sys: Rc<dyn System>,
    options: Rc<CompilerOptions>,
) -> DiagnosticReporter {
    let format_opts = get_format_opts_of_sys(sys.as_ref());
    let write_status: fn(&Writer, &str, &Diagnostic, &FormattingOptions) =
        if should_be_pretty(sys.as_ref(), Some(&options)) {
            format_diagnostics_status_with_color_and_time
        } else {
            format_diagnostics_status_and_time
        };
    Rc::new(move |diagnostic: &Diagnostic| {
        let writer = sys.writer();
        try_clear_screen(&writer, diagnostic, &options);
        write_status(
            &writer,
            &format_status_time(sys.now()),
            diagnostic,
            &format_opts,
        );
        write_str(
            &writer,
            &format!("{}{}", format_opts.new_line, format_opts.new_line),
        );
    })
}

/// Go `sys.Now().Format("03:04:05 PM")`.
/// PORT: Go formats the local time. The port has no time zone data, so this
/// formats UTC. Compare status lines with the time masked.
pub fn format_status_time(now: SystemTime) -> String {
    let seconds = now
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or_default()
        % 86_400;
    let hour = seconds / 3600;
    let minute = seconds % 3600 / 60;
    let second = seconds % 60;
    let hour12 = if hour % 12 == 0 { 12 } else { hour % 12 };
    let meridiem = if hour >= 12 { "PM" } else { "AM" };
    format!("{hour12:02}:{minute:02}:{second:02} {meridiem}")
}

// ---------------------------------------------------------------------------
// Go diagnosticwriter/diagnosticwriter.go (the pieces the reporters call)
// ---------------------------------------------------------------------------

// Go: diagnosticwriter/diagnosticwriter.go:108 foregroundColorEscapeGrey
const FOREGROUND_COLOR_ESCAPE_GREY: &str = "\u{1b}[90m";
// Go: diagnosticwriter/diagnosticwriter.go:109 foregroundColorEscapeRed
const FOREGROUND_COLOR_ESCAPE_RED: &str = "\u{1b}[91m";
// Go: diagnosticwriter/diagnosticwriter.go:110 foregroundColorEscapeYellow
const FOREGROUND_COLOR_ESCAPE_YELLOW: &str = "\u{1b}[93m";
// Go: diagnosticwriter/diagnosticwriter.go:111 foregroundColorEscapeBlue
const FOREGROUND_COLOR_ESCAPE_BLUE: &str = "\u{1b}[94m";
// Go: diagnosticwriter/diagnosticwriter.go:112 foregroundColorEscapeCyan
const FOREGROUND_COLOR_ESCAPE_CYAN: &str = "\u{1b}[96m";

// Go: diagnosticwriter/diagnosticwriter.go:116 gutterStyleSequence
const GUTTER_STYLE_SEQUENCE: &str = "\u{1b}[7m";
// Go: diagnosticwriter/diagnosticwriter.go:117 gutterSeparator
const GUTTER_SEPARATOR: &str = " ";
// Go: diagnosticwriter/diagnosticwriter.go:118 resetEscapeSequence
const RESET_ESCAPE_SEQUENCE: &str = "\u{1b}[0m";
// Go: diagnosticwriter/diagnosticwriter.go:119 ellipsis
const ELLIPSIS: &str = "...";

/// PORT: on the legacy frontend (`GOPORT_FRONTEND=legacy`) a diagnostic in
/// the config file has a nil file. Its location is in a program side table
/// that only `program::format_diagnostic` reads. The pretty writers cannot
/// tell it from a global diagnostic, so they stop at every diagnostic
/// without a file on that path.
fn is_legacy_diagnostic_without_file(diagnostic: &Diagnostic) -> bool {
    diagnostic.file.is_nil() && try_prog().is_some() && go_frontend_program().is_none()
}

// Go: diagnosticwriter/diagnosticwriter.go:134 FormatDiagnosticWithColorAndContext
pub fn format_diagnostic_with_color_and_context(
    output: &Writer,
    diagnostic: &Diagnostic,
    format_opts: &FormattingOptions,
) {
    if diagnostic.file.is_some() {
        let file = diagnostic.file;
        let pos = diagnostic.pos;
        write_location(
            output,
            file,
            pos,
            Some(format_opts),
            write_with_style_and_reset,
        );
        write_str(output, " - ");
    } else if is_legacy_diagnostic_without_file(diagnostic) {
        unported!("FormatDiagnosticWithColorAndContext of a legacy frontend config diagnostic");
    }

    write_with_style_and_reset(
        output,
        diagnostic.category.name(),
        get_category_format(diagnostic.category),
    );
    write_str(
        output,
        &format!(
            "{FOREGROUND_COLOR_ESCAPE_GREY} TS{}: {RESET_ESCAPE_SEQUENCE}",
            diagnostic.code
        ),
    );
    write_flattened_diagnostic_message(output, diagnostic, &format_opts.new_line);

    if diagnostic.file.is_some() && diagnostic.code != diag::File_appears_to_be_binary.code() as i32
    {
        write_str(output, &format_opts.new_line);
        write_code_snippet(
            output,
            diagnostic.file,
            diagnostic.pos,
            diagnostic.len(),
            get_category_format(diagnostic.category),
            "",
            format_opts,
        );
        write_str(output, &format_opts.new_line);
    }

    if !diagnostic.related_information.is_empty() {
        for related_information in &diagnostic.related_information {
            let file = related_information.file;
            if file.is_some() {
                write_str(output, &format_opts.new_line);
                write_str(output, "  ");
                let pos = related_information.pos;
                write_location(
                    output,
                    file,
                    pos,
                    Some(format_opts),
                    write_with_style_and_reset,
                );
                write_str(output, " - ");
                write_flattened_diagnostic_message(
                    output,
                    related_information,
                    &format_opts.new_line,
                );
                write_code_snippet(
                    output,
                    file,
                    pos,
                    related_information.len(),
                    FOREGROUND_COLOR_ESCAPE_CYAN,
                    "    ",
                    format_opts,
                );
            } else if is_legacy_diagnostic_without_file(related_information) {
                unported!(
                    "FormatDiagnosticWithColorAndContext of a legacy frontend config diagnostic"
                );
            }
            write_str(output, &format_opts.new_line);
        }
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:169 writeCodeSnippet
fn write_code_snippet(
    writer: &Writer,
    source_file: Node,
    start: i32,
    length: i32,
    squiggle_color: &str,
    indent: &str,
    format_opts: &FormattingOptions,
) {
    let (first_line, first_line_char) =
        get_ecma_line_and_utf16_character_of_position(source_file, start);
    let (last_line, mut last_line_char) =
        get_ecma_line_and_utf16_character_of_position(source_file, start + length);
    if length == 0 {
        last_line_char += 1; // When length is zero, squiggle the character right after the start position.
    }

    let text = source_file_text(source_file);
    let last_line_of_file = get_ecma_line_of_position(source_file, text.len() as i32);

    let has_more_than_five_lines = last_line - first_line >= 4;
    let mut gutter_width = (last_line + 1).to_string().len() as i32;
    if has_more_than_five_lines {
        gutter_width = (ELLIPSIS.len() as i32).max(gutter_width);
    }

    let mut i = first_line;
    while i <= last_line {
        write_str(writer, &format_opts.new_line);

        // If the error spans over 5 lines, we'll only show the first 2 and last 2 lines,
        // so we'll skip ahead to the second-to-last line.
        if has_more_than_five_lines && first_line + 1 < i && i < last_line - 1 {
            write_str(writer, indent);
            write_str(writer, GUTTER_STYLE_SEQUENCE);
            write_str(writer, &go_pad(ELLIPSIS, gutter_width, false));
            write_str(writer, RESET_ESCAPE_SEQUENCE);
            write_str(writer, GUTTER_SEPARATOR);
            write_str(writer, &format_opts.new_line);
            i = last_line - 1;
        }

        // Go scanner.GetECMAPositionOfLineAndByteOffset
        let line_starts = get_ecma_line_starts(source_file);
        let line_start = compute_position_of_line_and_byte_offset(line_starts, i, 0);
        let line_end = if i < last_line_of_file {
            compute_position_of_line_and_byte_offset(line_starts, i + 1, 0)
        } else {
            text.len() as i32
        };

        // Go `unicode.IsSpace` is the Unicode White_Space property, like
        // `char::is_whitespace`.
        let line_content =
            text[line_start as usize..line_end as usize].trim_end_matches(char::is_whitespace); // trim from end
        let line_content = line_content.replace('\t', " "); // convert tabs to single spaces

        // Output the gutter and the actual contents of the line.
        write_str(writer, indent);
        write_str(writer, GUTTER_STYLE_SEQUENCE);
        write_str(writer, &go_pad(&(i + 1).to_string(), gutter_width, false));
        write_str(writer, RESET_ESCAPE_SEQUENCE);
        write_str(writer, GUTTER_SEPARATOR);
        write_str(writer, &line_content);
        write_str(writer, &format_opts.new_line);

        // Output the gutter and the error span for the line using tildes.
        write_str(writer, indent);
        write_str(writer, GUTTER_STYLE_SEQUENCE);
        write_str(writer, &go_pad("", gutter_width, false));
        write_str(writer, RESET_ESCAPE_SEQUENCE);
        write_str(writer, GUTTER_SEPARATOR);
        write_str(writer, squiggle_color);
        if i == first_line {
            // If we're on the last line, then limit it to the last character of the last line.
            // Otherwise, we'll just squiggle the rest of the line, giving 'slice' no end position.
            let last_char_for_line = if i == last_line {
                last_line_char
            } else {
                utf16_len(&line_content)
            };

            // Fill with spaces until the first character,
            // then squiggle the remainder of the line.
            write_str(writer, &go_repeat(" ", first_line_char));
            write_str(
                writer,
                &go_repeat("~", last_char_for_line - first_line_char),
            );
        } else if i == last_line {
            // Squiggle until the final character.
            write_str(writer, &go_repeat("~", last_line_char));
        } else {
            // Squiggle the entire line.
            write_str(writer, &go_repeat("~", utf16_len(&line_content)));
        }

        write_str(writer, RESET_ESCAPE_SEQUENCE);
        i += 1;
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:263 WriteFlattenedDiagnosticMessage
pub fn write_flattened_diagnostic_message(writer: &Writer, diagnostic: &Diagnostic, newline: &str) {
    write_str(writer, &diagnostic.localize());

    for chain in &diagnostic.message_chain {
        flatten_diagnostic_message_chain(writer, chain, newline, 1);
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:271 flattenDiagnosticMessageChain
fn flatten_diagnostic_message_chain(
    writer: &Writer,
    chain: &Diagnostic,
    new_line: &str,
    level: usize,
) {
    write_str(writer, new_line);
    for _ in 0..level {
        write_str(writer, "  ");
    }

    write_str(writer, &chain.localize());
    for child in &chain.message_chain {
        flatten_diagnostic_message_chain(writer, child, new_line, level + 1);
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:283 getCategoryFormat
// PORT: Go panics on an unhandled category. The Rust match is exhaustive.
fn get_category_format(category: Category) -> &'static str {
    match category {
        Category::Error => FOREGROUND_COLOR_ESCAPE_RED,
        Category::Warning => FOREGROUND_COLOR_ESCAPE_YELLOW,
        Category::Suggestion => FOREGROUND_COLOR_ESCAPE_GREY,
        Category::Message => FOREGROUND_COLOR_ESCAPE_BLUE,
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:297 FormattedWriter
pub type FormattedWriter = fn(output: &Writer, text: &str, format_style: &str);

// Go: diagnosticwriter/diagnosticwriter.go:299 writeWithStyleAndReset
fn write_with_style_and_reset(output: &Writer, text: &str, format_style: &str) {
    write_str(output, format_style);
    write_str(output, text);
    write_str(output, RESET_ESCAPE_SEQUENCE);
}

// Go: diagnosticwriter/diagnosticwriter.go:305 WriteLocation
pub fn write_location(
    output: &Writer,
    file: Node,
    pos: i32,
    format_opts: Option<&FormattingOptions>,
    write_with_style_and_reset: FormattedWriter,
) {
    let (first_line, first_char) = get_ecma_line_and_utf16_character_of_position(file, pos);
    let relative_file_name = match format_opts {
        Some(format_opts) => convert_to_relative_path(
            source_file_file_name(file),
            &format_opts.compare_paths_options,
        ),
        None => source_file_file_name(file).to_string(),
    };

    write_with_style_and_reset(output, &relative_file_name, FOREGROUND_COLOR_ESCAPE_CYAN);
    write_str(output, ":");
    write_with_style_and_reset(
        output,
        &(first_line + 1).to_string(),
        FOREGROUND_COLOR_ESCAPE_YELLOW,
    );
    write_str(output, ":");
    write_with_style_and_reset(
        output,
        &(first_char + 1).to_string(),
        FOREGROUND_COLOR_ESCAPE_YELLOW,
    );
}

// Some of these lived in watch.ts, but they're not specific to the watch API.

// Go: diagnosticwriter/diagnosticwriter.go:323 ErrorSummary
// PORT: Go keys `ErrorsByFile` by the file (a `FileLike`). Here the key is
// the file node, and the lists borrow the diagnostics.
struct ErrorSummary<'a> {
    total_error_count: i32,
    global_errors: Vec<&'a Diagnostic>,
    errors_by_file: FxHashMap<Node, Vec<&'a Diagnostic>>,
    sorted_files: Vec<Node>,
}

// Go: diagnosticwriter/diagnosticwriter.go:330 WriteErrorSummaryText
pub fn write_error_summary_text(
    output: &Writer,
    all_diagnostics: &[Diagnostic],
    format_opts: &FormattingOptions,
) {
    // Roughly corresponds to 'getErrorSummaryText' from watch.ts

    let error_summary = get_error_summary(all_diagnostics);
    let total_error_count = error_summary.total_error_count;
    if total_error_count == 0 {
        return;
    }

    let first_file = error_summary
        .sorted_files
        .first()
        .copied()
        .unwrap_or(Node::NIL);
    let first_file_name = pretty_path_for_file_error(
        first_file,
        error_summary
            .errors_by_file
            .get(&first_file)
            .map(Vec::as_slice)
            .unwrap_or_default(),
        format_opts,
    );
    let num_erroring_files = error_summary.errors_by_file.len();

    let message = if total_error_count == 1 {
        // Special-case a single error.
        if !error_summary.global_errors.is_empty() || first_file_name.is_empty() {
            localize(diag::Found_1_error, &[])
        } else {
            localize(diag::Found_1_error_in_0, &args![first_file_name])
        }
    } else {
        match num_erroring_files {
            // No file-specific errors.
            0 => localize(diag::Found_0_errors, &args![total_error_count]),
            // One file with errors.
            1 => localize(
                diag::Found_0_errors_in_the_same_file_starting_at_Colon_1,
                &args![total_error_count, first_file_name],
            ),
            // Multiple files with errors.
            _ => localize(
                diag::Found_0_errors_in_1_files,
                &args![total_error_count, num_erroring_files],
            ),
        }
    };
    write_str(output, &format_opts.new_line);
    write_str(output, &message);
    write_str(output, &format_opts.new_line);
    write_str(output, &format_opts.new_line);
    if num_erroring_files > 1 {
        write_tabular_errors_display(output, &error_summary, format_opts);
        write_str(output, &format_opts.new_line);
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:377 getErrorSummary
fn get_error_summary(diags: &[Diagnostic]) -> ErrorSummary<'_> {
    let mut total_error_count = 0;
    let mut global_errors = Vec::new();
    let mut errors_by_file: FxHashMap<Node, Vec<&Diagnostic>> = FxHashMap::default();

    for diagnostic in diags {
        if diagnostic.category != Category::Error {
            continue;
        }

        total_error_count += 1;
        if diagnostic.file.is_nil() {
            if is_legacy_diagnostic_without_file(diagnostic) {
                unported!("WriteErrorSummaryText of a legacy frontend config diagnostic");
            }
            global_errors.push(diagnostic);
        } else {
            errors_by_file
                .entry(diagnostic.file)
                .or_default()
                .push(diagnostic);
        }
    }

    // !!!
    // Need an ordered map here, but sorting for consistency.
    let mut sorted_files: Vec<Node> = errors_by_file.keys().copied().collect();
    sorted_files.sort_by(|a, b| source_file_file_name(*a).cmp(source_file_file_name(*b)));

    ErrorSummary {
        total_error_count,
        global_errors,
        errors_by_file,
        sorted_files,
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:412 writeTabularErrorsDisplay
fn write_tabular_errors_display(
    output: &Writer,
    error_summary: &ErrorSummary<'_>,
    format_opts: &FormattingOptions,
) {
    let sorted_files = &error_summary.sorted_files;

    let mut max_errors = 0;
    for errors_for_file in error_summary.errors_by_file.values() {
        max_errors = max_errors.max(errors_for_file.len());
    }

    // !!!
    // TODO (drosen): This was never localized.
    // Should make this better.
    let header_row = localize(diag::Errors_Files, &[]);
    let left_column_heading_length = header_row.split(' ').next().unwrap_or_default().len() as i32;
    let length_of_biggest_error_count = max_errors.to_string().len() as i32;
    let left_padding_goal = left_column_heading_length.max(length_of_biggest_error_count);
    let header_padding = (length_of_biggest_error_count - left_column_heading_length).max(0);

    write_str(output, &go_repeat(" ", header_padding));
    write_str(output, &header_row);
    write_str(output, &format_opts.new_line);

    for file in sorted_files {
        let file_errors = &error_summary.errors_by_file[file];
        let error_count = file_errors.len();

        write_str(
            output,
            &format!(
                "{}  ",
                go_pad(&error_count.to_string(), left_padding_goal, false)
            ),
        );
        write_str(
            output,
            &pretty_path_for_file_error(*file, file_errors, format_opts),
        );
        write_str(output, &format_opts.new_line);
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:443 prettyPathForFileError
fn pretty_path_for_file_error(
    file: Node,
    file_errors: &[&Diagnostic],
    format_opts: &FormattingOptions,
) -> String {
    if file.is_nil() || file_errors.is_empty() {
        return String::new();
    }
    let line = get_ecma_line_of_position(file, file_errors[0].pos);
    let mut file_name = source_file_file_name(file).to_string();
    if path_is_absolute(&file_name)
        && path_is_absolute(&format_opts.compare_paths_options.current_directory)
    {
        file_name = convert_to_relative_path(
            source_file_file_name(file),
            &format_opts.compare_paths_options,
        );
    }
    format!(
        "{}{}:{}{}",
        file_name,
        FOREGROUND_COLOR_ESCAPE_GREY,
        line + 1,
        RESET_ESCAPE_SEQUENCE,
    )
}

// Go: diagnosticwriter/diagnosticwriter.go:467 WriteFormatDiagnostic
// PORT: with a program installed, a diagnostic goes through
// `program::format_diagnostic`: on the legacy frontend a config diagnostic
// has a nil file and its location is in the program's side table. That
// uses the program's current directory, which is the system one.
pub fn write_format_diagnostic(
    output: &Writer,
    diagnostic: &Diagnostic,
    format_opts: &FormattingOptions,
) {
    if try_prog().is_some() {
        write_str(output, &format_diagnostic(diagnostic));
        return;
    }
    if diagnostic.file.is_some() {
        let (line, character) =
            get_ecma_line_and_utf16_character_of_position(diagnostic.file, diagnostic.pos);
        let file_name = source_file_file_name(diagnostic.file);
        let relative_file_name =
            convert_to_relative_path(file_name, &format_opts.compare_paths_options);
        write_str(
            output,
            &format!("{}({},{}): ", relative_file_name, line + 1, character + 1),
        );
    }

    write_str(
        output,
        &format!("{} TS{}: ", diagnostic.category.name(), diagnostic.code),
    );
    write_flattened_diagnostic_message(output, diagnostic, &format_opts.new_line);
    write_str(output, &format_opts.new_line);
}

// Go: diagnosticwriter/diagnosticwriter.go:461 WriteFormatDiagnostics
pub fn write_format_diagnostics_to(
    output: &Writer,
    diagnostics: &[Diagnostic],
    format_opts: &FormattingOptions,
) {
    for diagnostic in diagnostics {
        write_format_diagnostic(output, diagnostic, format_opts);
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:480 FormatDiagnosticsStatusWithColorAndTime
pub fn format_diagnostics_status_with_color_and_time(
    output: &Writer,
    time: &str,
    diag: &Diagnostic,
    format_opts: &FormattingOptions,
) {
    write_str(output, "[");
    write_with_style_and_reset(output, time, FOREGROUND_COLOR_ESCAPE_GREY);
    write_str(output, "] ");
    write_flattened_diagnostic_message(output, diag, &format_opts.new_line);
}

// Go: diagnosticwriter/diagnosticwriter.go:487 FormatDiagnosticsStatusAndTime
pub fn format_diagnostics_status_and_time(
    output: &Writer,
    time: &str,
    diag: &Diagnostic,
    format_opts: &FormattingOptions,
) {
    write_str(output, &format!("{time} - "));
    write_flattened_diagnostic_message(output, diag, &format_opts.new_line);
}

// Go: diagnosticwriter/diagnosticwriter.go:497 TryClearScreen
pub fn try_clear_screen(output: &Writer, diag: &Diagnostic, options: &CompilerOptions) -> bool {
    // Go: diagnosticwriter/diagnosticwriter.go:492 ScreenStartingCodes
    let screen_starting_codes = [
        diag::Starting_compilation_in_watch_mode.code() as i32,
        diag::File_change_detected_Starting_incremental_compilation.code() as i32,
    ];
    if !options.preserve_watch_output.is_true()
        && !options.extended_diagnostics.is_true()
        && !options.diagnostics.is_true()
        && screen_starting_codes.contains(&diag.code)
    {
        write_str(output, "\x1B[2J\x1B[3J\x1B[H"); // Clear screen and move cursor to home position
        return true;
    }
    false
}

// ---------------------------------------------------------------------------
// Go standard library and `diagnostics` helpers used above and below
// ---------------------------------------------------------------------------

// Go: diagnostics/diagnostics.go:67 (*Message).Localize
// PORT: the port has only the default (English) messages, so the locale is
// dropped. Go `Format` panics on a bad placeholder.
fn localize(message: &'static Message, args: &[String]) -> String {
    match message.format(args) {
        Ok(text) => text,
        Err(_) => panic!("Invalid formatting placeholder"),
    }
}

/// Go `fmt.Sprintf("%*s", width, s)`, or `"%-*s"` when `left` is true. Go
/// pads to `width` runes, and a negative width pads on the right.
fn go_pad(s: &str, width: i32, left: bool) -> String {
    let left = left || width < 0;
    let width = width.unsigned_abs() as usize;
    if left {
        format!("{s:<width$}")
    } else {
        format!("{s:>width$}")
    }
}

/// Go `strings.Repeat`, which panics on a negative count.
fn go_repeat(s: &str, count: i32) -> String {
    match usize::try_from(count) {
        Ok(count) => s.repeat(count),
        Err(_) => panic!("strings: negative Repeat count"),
    }
}

// ---------------------------------------------------------------------------
// Go execute/tsc/help.go (PrintVersion, PrintBuildHelp and the helpers they
// call)
// ---------------------------------------------------------------------------
// PORT: Go `PrintHelp`, `getOptionsForHelp`, `printEasyHelp` and
// `printAllHelp` (the `tsc --help` path) are not ported here: no port
// caller uses them yet.

// Go: execute/tsc/help.go:15 PrintVersion
pub fn print_version(sys: &dyn System) {
    write_str(
        &sys.writer(),
        &format!("{}\n", localize(diag::Version_0, &args![version()])),
    );
}

// Go: execute/tsc/help.go:44 getHeader
fn get_header(sys: &dyn System, message: &str) -> Vec<String> {
    let colors = create_colors(sys);
    let mut header = Vec::with_capacity(3);
    let terminal_width = sys.get_width_of_terminal();
    const TS_ICON: &str = "     ";
    const TS_ICON_TS: &str = "  TS ";
    const TS_ICON_LENGTH: i32 = TS_ICON.len() as i32;

    let ts_icon_first_line = colors.blue_background(TS_ICON);
    let ts_icon_second_line = colors.blue_background(&colors.bright_white(TS_ICON_TS));
    // If we have enough space, print TS icon.
    if terminal_width >= message.len() as i32 + TS_ICON_LENGTH {
        // right align of the icon is 120 at most.
        let right_align = if terminal_width > 120 {
            120
        } else {
            terminal_width
        };
        let left_align = right_align - TS_ICON_LENGTH;
        header.extend([
            go_pad(message, left_align, true),
            ts_icon_first_line,
            "\n".to_string(),
        ]);
        header.extend([
            go_repeat(" ", left_align),
            ts_icon_second_line,
            "\n".to_string(),
        ]);
    } else {
        header.extend([message.to_string(), "\n".to_string(), "\n".to_string()]);
    }
    header
}

// Go: execute/tsc/help.go:135 PrintBuildHelp
pub fn print_build_help(sys: &dyn System, build_options: &[&'static CommandLineOption]) {
    let mut output: Vec<String> = Vec::new();
    output.extend(get_header(
        sys,
        &format!(
            "{} - {}",
            localize(diag::X_tsc_Colon_The_TypeScript_Compiler, &[]),
            localize(diag::Version_0, &args![version()])
        ),
    ));
    let before = localize(
        diag::Using_build_b_will_make_tsc_behave_more_like_a_build_orchestrator_than_a_compiler_This_is_used_to_trigger_building_composite_projects_which_you_can_learn_more_about_at_0,
        &args!["https://aka.ms/tsc-composite-builds"],
    );
    let options: Vec<&'static CommandLineOption> = build_options
        .iter()
        .copied()
        .filter(|option| !std::ptr::eq(*option, &*TSC_BUILD_OPTION))
        .collect();
    output.extend(generate_section_options_output(
        sys,
        &localize(diag::BUILD_OPTIONS, &[]),
        &options,
        false,
        Some(&before),
        None,
    ));

    let writer = sys.writer();
    for chunk in &output {
        write_str(&writer, chunk);
    }
}

// Go: execute/tsc/help.go:149 generateSectionOptionsOutput
fn generate_section_options_output(
    sys: &dyn System,
    section_name: &str,
    options: &[&'static CommandLineOption],
    sub_category: bool,
    before_options_description: Option<&str>,
    after_options_description: Option<&str>,
) -> Vec<String> {
    let mut output = vec![
        create_colors(sys).bold(section_name),
        "\n".to_string(),
        "\n".to_string(),
    ];

    if let Some(before_options_description) = before_options_description {
        output.extend([
            before_options_description.to_string(),
            "\n".to_string(),
            "\n".to_string(),
        ]);
    }
    if !sub_category {
        output.extend(generate_group_option_output(sys, options));
        if let Some(after_options_description) = after_options_description {
            output.extend([
                after_options_description.to_string(),
                "\n".to_string(),
                "\n".to_string(),
            ]);
        }
        return output;
    }
    // PORT: Go keeps a map and a separate `categoryOrder` slice. An
    // `IndexMap` keeps both.
    let mut category_map: IndexMap<String, Vec<&'static CommandLineOption>> = IndexMap::new();
    for &option in options {
        let Some(category) = option.category else {
            continue;
        };
        let cur_category = localize(category, &[]);
        category_map.entry(cur_category).or_default().push(option);
    }
    for (key, value) in &category_map {
        output.extend([
            "### ".to_string(),
            key.clone(),
            "\n".to_string(),
            "\n".to_string(),
        ]);
        output.extend(generate_group_option_output(sys, value));
    }
    if let Some(after_options_description) = after_options_description {
        output.extend([
            after_options_description.to_string(),
            "\n".to_string(),
            "\n".to_string(),
        ]);
    }

    output
}

// Go: execute/tsc/help.go:194 generateGroupOptionOutput
fn generate_group_option_output(
    sys: &dyn System,
    options_list: &[&'static CommandLineOption],
) -> Vec<String> {
    let mut max_length = 0;
    for option in options_list {
        let cur_lenght = get_display_name_text_of_option(option).len() as i32;
        max_length = max_length.max(cur_lenght);
    }

    // left part should be right align, right part should be left align

    // assume 2 space between left margin and left part.
    let right_align_of_left_part = max_length + 2;
    // assume 2 space between left and right part
    let left_align_of_right_part = right_align_of_left_part + 2;

    let mut lines = Vec::new();
    for option in options_list {
        let tmp = generate_option_output(
            sys,
            option,
            right_align_of_left_part,
            left_align_of_right_part,
        );
        lines.extend(tmp);
    }

    // make sure always a blank line in the end.
    if lines.len() < 2 || lines[lines.len() - 2] != "\n" {
        lines.push("\n".to_string());
    }

    lines
}

// Go: execute/tsc/help.go:222 generateOptionOutput
fn generate_option_output(
    sys: &dyn System,
    option: &CommandLineOption,
    right_align_of_left: i32,
    left_align_of_right: i32,
) -> Vec<String> {
    let mut text: Vec<String> = Vec::new();
    let colors = create_colors(sys);

    // name and description
    let name = get_display_name_text_of_option(option);

    // value type and possible value
    let value_candidates = get_value_candidate(option);

    let default_value_description =
        if let CompilerOptionsValue::Message(msg) = option.default_value_description {
            localize(msg, &[])
        } else {
            // Go evaluates both `core.IfElse` arguments.
            let elements = option.elements();
            format_default_value(
                &option.default_value_description,
                if option.kind == CommandLineOptionKind::LIST
                    || option.kind == CommandLineOptionKind::LIST_OR_ELEMENT
                {
                    elements
                } else {
                    Some(option)
                },
            )
        };

    let terminal_width = sys.get_width_of_terminal();

    if terminal_width >= 80 {
        let description = match option.description {
            Some(description) => localize(description, &[]),
            None => String::new(),
        };
        text.extend(get_pretty_output(
            &colors,
            &name,
            &description,
            right_align_of_left,
            left_align_of_right,
            terminal_width,
            true, /*colorLeft*/
        ));
        text.push("\n".to_string());
        if show_additional_info_output(value_candidates.as_ref(), option) {
            if let Some(value_candidates) = &value_candidates {
                text.extend(get_pretty_output(
                    &colors,
                    &value_candidates.value_type,
                    &value_candidates.possible_values,
                    right_align_of_left,
                    left_align_of_right,
                    terminal_width,
                    false, /*colorLeft*/
                ));
                text.push("\n".to_string());
            }
            if !default_value_description.is_empty() {
                text.extend(get_pretty_output(
                    &colors,
                    &localize(diag::X_default_Colon, &[]),
                    &default_value_description,
                    right_align_of_left,
                    left_align_of_right,
                    terminal_width,
                    false, /*colorLeft*/
                ));
                text.push("\n".to_string());
            }
        }
        text.push("\n".to_string());
    } else {
        text.extend([colors.blue(&name), "\n".to_string()]);
        if let Some(description) = option.description {
            text.push(localize(description, &[]));
        }
        text.push("\n".to_string());
        if show_additional_info_output(value_candidates.as_ref(), option) {
            if let Some(value_candidates) = &value_candidates {
                text.extend([
                    value_candidates.value_type.clone(),
                    " ".to_string(),
                    value_candidates.possible_values.clone(),
                ]);
            }
            if !default_value_description.is_empty() {
                if value_candidates.is_some() {
                    text.push("\n".to_string());
                }
                text.extend([
                    localize(diag::X_default_Colon, &[]),
                    " ".to_string(),
                    default_value_description,
                ]);
            }

            text.push("\n".to_string());
        }
        text.push("\n".to_string());
    }

    text
}

// Go: execute/tsc/help.go:295 formatDefaultValue
// PORT: Go `option` is a pointer that can be nil (`Elements()` of a list
// without elements); Go dereferences it after the nil value check.
fn format_default_value(
    default_value: &CompilerOptionsValue,
    option: Option<&CommandLineOption>,
) -> String {
    if default_value.is_nil() || *default_value == CompilerOptionsValue::Tristate(Tristate::Unknown)
    {
        return "undefined".to_string();
    }

    let option = option.expect("nil option dereference");
    if option.kind == CommandLineOptionKind::ENUM {
        // e.g. ScriptTarget.ES2015 -> "es6/es2015"
        let mut names: Vec<&str> = Vec::new();
        for (name, value) in option.enum_map().expect("nil enum map dereference") {
            if value == default_value {
                names.push(name.as_str());
            }
        }
        return names.join("/");
    }
    // Go `fmt.Sprintf("%v", defaultValue)`.
    // PORT: only the dynamic types that the option declarations use as a
    // non-enum default value are formatted. Others need Go `%v` rules.
    match default_value {
        CompilerOptionsValue::Bool(value) => value.to_string(),
        CompilerOptionsValue::Int(value) => value.to_string(),
        CompilerOptionsValue::String(value) => value.clone(),
        _ => unported!("formatDefaultValue: fmt %v of this default value type"),
    }
}

// Go: execute/tsc/help.go:313 valueCandidate
struct ValueCandidate {
    // "one or more" or "any of"
    value_type: String,
    possible_values: String,
}

// Go: execute/tsc/help.go:319 showAdditionalInfoOutput
fn show_additional_info_output(
    value_candidates: Option<&ValueCandidate>,
    option: &CommandLineOption,
) -> bool {
    if option
        .category
        .is_some_and(|category| std::ptr::eq(category, diag::Command_line_Options))
    {
        return false;
    }
    if let Some(value_candidates) = value_candidates
        && value_candidates.possible_values == "string"
        && (option.default_value_description.is_nil()
            || matches!(
                &option.default_value_description,
                CompilerOptionsValue::String(value) if value == "false" || value == "n/a"
            ))
    {
        return false;
    }
    true
}

// Go: execute/tsc/help.go:332 getValueCandidate
// PORT: Go also takes `sys`, which it does not read.
fn get_value_candidate(option: &CommandLineOption) -> Option<ValueCandidate> {
    // option.type might be "string" | "number" | "boolean" | "object" | "list" | Map<string, number | string>
    // string -- any of: string
    // number -- any of: number
    // boolean -- any of: boolean
    // object -- null
    // list -- one or more: , content depends on `option.element.type`, the same as others
    // Map<string, number | string> -- any of: key1, key2, ....
    if option.kind == CommandLineOptionKind::OBJECT {
        return None;
    }

    if option.kind == CommandLineOptionKind::LIST_OR_ELEMENT {
        // assert(option.type !== "listOrElement")
        panic!("no value candidate for list or element");
    }

    let value_type = if option.kind == CommandLineOptionKind::STRING
        || option.kind == CommandLineOptionKind::NUMBER
        || option.kind == CommandLineOptionKind::BOOLEAN
    {
        localize(diag::X_type_Colon, &[])
    } else if option.kind == CommandLineOptionKind::LIST {
        localize(diag::X_one_or_more_Colon, &[])
    } else {
        localize(diag::X_one_of_Colon, &[])
    };

    Some(ValueCandidate {
        value_type,
        possible_values: get_possible_values(option),
    })
}

// Go: execute/tsc/help.go:366 getPossibleValues
fn get_possible_values(option: &CommandLineOption) -> String {
    if option.kind == CommandLineOptionKind::STRING
        || option.kind == CommandLineOptionKind::NUMBER
        || option.kind == CommandLineOptionKind::BOOLEAN
    {
        return option.kind.0.to_string();
    }
    if option.kind == CommandLineOptionKind::LIST
        || option.kind == CommandLineOptionKind::LIST_OR_ELEMENT
    {
        return get_possible_values(option.elements().expect("nil option dereference"));
    }
    if option.kind == CommandLineOptionKind::OBJECT {
        return String::new();
    }
    // Map<string, number | string>
    // Group synonyms: es6/es2015
    let enum_map = option.enum_map().expect("nil enum map dereference");
    // PORT: Go uses an ordered map keyed by the `any` value. The values are
    // not hashable here, so this is a list in insertion order.
    let mut inverted: Vec<(&CompilerOptionsValue, Vec<&str>)> = Vec::with_capacity(enum_map.len());
    let deprecated_keys = option.deprecated_keys();

    for (name, value) in enum_map {
        if !deprecated_keys.is_some_and(|keys| keys.contains(name)) {
            match inverted.iter_mut().find(|(key, _)| *key == value) {
                Some((_, names)) => names.push(name.as_str()),
                None => inverted.push((value, vec![name.as_str()])),
            }
        }
    }
    let syns: Vec<String> = inverted
        .iter()
        .map(|(_, synonyms)| synonyms.join("/"))
        .collect();
    syns.join(", ")
}

// Go: execute/tsc/help.go:397 getPrettyOutput
// PORT: Go cuts `right` at a byte index. A cut inside a UTF-8 sequence
// writes invalid UTF-8, which a Rust `String` cannot hold.
fn get_pretty_output(
    colors: &Colors,
    left: &str,
    right: &str,
    right_align_of_left: i32,
    left_align_of_right: i32,
    terminal_width: i32,
    color_left: bool,
) -> Vec<String> {
    // !!! How does terminalWidth interact with UTF-8 encoding? Strada just assumed UTF-16.
    let mut res = Vec::with_capacity(4);
    let mut is_first_line = true;
    let mut remain_right = right;
    let right_character_number = terminal_width - left_align_of_right;
    while !remain_right.is_empty() {
        let cur_left = if is_first_line {
            let cur_left = go_pad(left, right_align_of_left, false);
            let cur_left = go_pad(&cur_left, left_align_of_right, true);
            if color_left {
                colors.blue(&cur_left)
            } else {
                cur_left
            }
        } else {
            go_repeat(" ", left_align_of_right)
        };

        let idx = right_character_number.min(remain_right.len() as i32);
        let Ok(idx) = usize::try_from(idx) else {
            panic!("slice bounds out of range [:{idx}]");
        };
        if !remain_right.is_char_boundary(idx) {
            unported!("getPrettyOutput cut inside a UTF-8 sequence");
        }
        let (cur_right, rest) = remain_right.split_at(idx);
        remain_right = rest;
        res.extend([cur_left, cur_right.to_string(), "\n".to_string()]);
        is_first_line = false;
    }
    res
}

// Go: execute/tsc/help.go:424 getDisplayNameTextOfOption
fn get_display_name_text_of_option(option: &CommandLineOption) -> String {
    format!(
        "--{}{}",
        option.name,
        if !option.short_name.is_empty() {
            format!(", -{}", option.short_name)
        } else {
            String::new()
        }
    )
}
