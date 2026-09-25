//! Go: execute/tsc/diagnostics.go (diagnostic, error summary and status
//! reporters), with the non-pretty `diagnosticwriter` pieces they call.
//!
//! PORT: the pretty (color and code snippet) writers are out of scope. A
//! pretty reporter calls `unported!` when it writes. Pass `--pretty false`
//! (or run with stdout that is not a terminal) to stay on ported paths.
//! The locale parameters are dropped: the port has only English messages.

use crate::prelude::*;

use std::time::{SystemTime, UNIX_EPOCH};

use super::compile::{System, Writer, write_str};
use crate::frontend::tspath::ComparePathsOptions;

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
        return Rc::new(move |_diagnostic: &Diagnostic| {
            unported!("FormatDiagnosticWithColorAndContext");
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
pub fn create_report_error_summary(
    sys: &dyn System,
    options: Option<&CompilerOptions>,
) -> DiagnosticsReporter {
    if should_be_pretty(sys, options) {
        return Rc::new(|_diagnostics: &[Diagnostic]| {
            unported!("WriteErrorSummaryText");
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
// Go: diagnosticwriter/diagnosticwriter.go:112 resetEscapeSequence
const RESET_ESCAPE_SEQUENCE: &str = "\u{1b}[0m";

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

// Go: diagnosticwriter/diagnosticwriter.go:299 writeWithStyleAndReset
fn write_with_style_and_reset(output: &Writer, text: &str, format_style: &str) {
    write_str(output, format_style);
    write_str(output, text);
    write_str(output, RESET_ESCAPE_SEQUENCE);
}

// Go: diagnosticwriter/diagnosticwriter.go:467 WriteFormatDiagnostic
// PORT: a diagnostic with a file (or a config diagnostic whose location is
// in the program's side table) needs the installed program, so it goes
// through `program::format_diagnostic`. That uses the program's current
// directory, which is the system one. Without a program, a diagnostic has
// no location to write.
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
        unported!("WriteFormatDiagnostic without a program");
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
