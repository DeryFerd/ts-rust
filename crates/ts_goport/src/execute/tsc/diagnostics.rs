//! Go: execute/tsc/diagnostics.go (diagnostic, error summary and status
//! reporters), with the `diagnosticwriter` pieces they call. The help and
//! version printers (execute/tsc/help.go) are in help.rs.
//!
//! PORT: Go `diagnosticwriter.FileLike` is the diagnostic's source file
//! node, and Go `diagnosticwriter.Diagnostic` is the `*ast.Diagnostic` itself
//! (Go `WrapASTDiagnostic` and `FromASTDiagnostics` add nothing).

use crate::prelude::*;

use std::sync::OnceLock;
use std::time::SystemTime;

use super::compile::{System, Writer, write_str};
// PORT: testing (the status reporters)
use super::compile::CommandLineTesting;
use crate::diagnostics_loc::{localize, message_localize};
use crate::frontend::tspath::{ComparePathsOptions, convert_to_relative_path, path_is_absolute};
use crate::locale::Locale;
use ts_diagnostics::Category;

// Go: diagnosticwriter/diagnosticwriter.go:101 FormattingOptions
#[derive(Clone, Debug, Default)]
pub struct FormattingOptions {
    pub new_line: String,
    pub compare_paths_options: ComparePathsOptions,
    pub locale: Locale,
}

// Go: execute/tsc/diagnostics.go:15 getFormatOptsOfSys
fn get_format_opts_of_sys(sys: &dyn System, locale: &Locale) -> FormattingOptions {
    FormattingOptions {
        new_line: "\n".to_string(),
        compare_paths_options: ComparePathsOptions {
            current_directory: sys.get_current_directory(),
            use_case_sensitive_file_names: sys.fs().use_case_sensitive_file_names(),
        },
        locale: locale.clone(),
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
    locale: &Locale,
    options: &CompilerOptions,
) -> DiagnosticReporter {
    if options.quiet.is_true() {
        return quiet_diagnostic_reporter();
    }
    let format_opts = get_format_opts_of_sys(sys, locale);
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

// Go: execute/tsc/diagnostics.go:134 CreateReportErrorSummary
// PORT: Go reads `sys.Writer()` on each report. The reporter cannot keep
// `sys`, so it reads the writer when it is made. A system's writer does
// not change after the system is made.
pub fn create_report_error_summary(
    sys: &dyn System,
    locale: &Locale,
    options: Option<&CompilerOptions>,
) -> DiagnosticsReporter {
    if should_be_pretty(sys, options) {
        let format_opts = get_format_opts_of_sys(sys, locale);
        let writer = sys.writer();
        return Rc::new(move |diagnostics: &[Diagnostic]| {
            write_error_summary_text(&writer, diagnostics, &format_opts);
        });
    }
    quiet_diagnostics_reporter()
}

// Go: execute/tsc/diagnostics.go:144 CreateBuilderStatusReporter
// PORT: Go `options` can be nil only through `shouldBePretty`; the quiet
// check reads it, so it is required here.
pub fn create_builder_status_reporter(
    sys: Rc<dyn System>,
    w: Writer,
    locale: &Locale,
    options: &CompilerOptions,
    testing: Option<Rc<dyn CommandLineTesting>>,
) -> DiagnosticReporter {
    if options.quiet.is_true() {
        return quiet_diagnostic_reporter();
    }

    let format_opts = get_format_opts_of_sys(sys.as_ref(), locale);
    let write_status: fn(&Writer, &str, &Diagnostic, &FormattingOptions) =
        if should_be_pretty(sys.as_ref(), Some(options)) {
            format_diagnostics_status_with_color_and_time
        } else {
            format_diagnostics_status_and_time
        };
    Rc::new(move |diagnostic: &Diagnostic| {
        // PORT: testing. Go `defer testing.OnBuildStatusReportEnd(w)`.
        if let Some(testing) = &testing {
            testing.on_build_status_report_start(&w);
        }
        write_status(&w, &format_status_time(sys.now()), diagnostic, &format_opts);
        write_str(
            &w,
            &format!("{}{}", format_opts.new_line, format_opts.new_line),
        );
        if let Some(testing) = &testing {
            testing.on_build_status_report_end(&w);
        }
    })
}

// Go: execute/tsc/diagnostics.go:162 CreateWatchStatusReporter
pub fn create_watch_status_reporter(
    sys: Rc<dyn System>,
    locale: &Locale,
    options: Rc<CompilerOptions>,
    testing: Option<Rc<dyn CommandLineTesting>>,
) -> DiagnosticReporter {
    let format_opts = get_format_opts_of_sys(sys.as_ref(), locale);
    let write_status: fn(&Writer, &str, &Diagnostic, &FormattingOptions) =
        if should_be_pretty(sys.as_ref(), Some(&options)) {
            format_diagnostics_status_with_color_and_time
        } else {
            format_diagnostics_status_and_time
        };
    Rc::new(move |diagnostic: &Diagnostic| {
        let writer = sys.writer();
        // PORT: testing. Go `defer testing.OnWatchStatusReportEnd()`.
        if let Some(testing) = &testing {
            testing.on_watch_status_report_start();
        }
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
        if let Some(testing) = &testing {
            testing.on_watch_status_report_end();
        }
    })
}

/// Go `sys.Now().Format("03:04:05 PM")`. Go `time.Now()` is in `time.Local`.
// Go (go1.26, the oracle toolchain): time/format.go:667
// (Time).appendFormat, the stdZeroHour12 (:756), stdZeroMinute (:765),
// stdZeroSecond (:769) and stdPM (:771) cases.
// PORT: jiff converts the time to the zone's civil time (Go
// `Time.locabs`). A time outside the jiff range (years -9999 to 9999) is
// not ported.
pub fn format_status_time(now: SystemTime) -> String {
    let Ok(timestamp) = jiff::Timestamp::try_from(now) else {
        unported!("Time.Format of a time outside years -9999 to 9999");
    };
    let datetime = local_location().to_datetime(timestamp);
    let hour = datetime.hour();
    // Noon is 12PM, midnight is 12AM.
    let mut hr = hour % 12;
    if hr == 0 {
        hr = 12;
    }
    let pm = if hour >= 12 { "PM" } else { "AM" };
    format!(
        "{hr:02}:{:02}:{:02} {pm}",
        datetime.minute(),
        datetime.second()
    )
}

// ---------------------------------------------------------------------------
// Go time.Local (go1.26 time/zoneinfo_unix.go), for the status clock
// ---------------------------------------------------------------------------
// PORT: Go `time.Location` is a `jiff::tz::TimeZone`. Go parses zone files
// with `LoadLocationFromTZData`; jiff parses the same TZif data (the
// transitions and the POSIX TZ footer) with `TimeZone::tzif`. This is the
// Unix path (zoneinfo_unix.go); the port targets Linux.

// Go: time/zoneinfo.go:88 localLoc, :89 localOnce, :91 (*Location).get
static LOCAL_LOC: OnceLock<jiff::tz::TimeZone> = OnceLock::new();

/// Go `time.Local`.
fn local_location() -> &'static jiff::tz::TimeZone {
    LOCAL_LOC.get_or_init(init_local)
}

// Go: time/zoneinfo_unix.go:21 platformZoneSources
// Many systems use /usr/share/zoneinfo, Solaris 2 has
// /usr/share/lib/zoneinfo, IRIX 6 has /usr/lib/locale/TZ,
// NixOS has /etc/zoneinfo.
const PLATFORM_ZONE_SOURCES: &[&str] = &[
    "/usr/share/zoneinfo/",
    "/usr/share/lib/zoneinfo/",
    "/usr/lib/locale/TZ/",
    "/etc/zoneinfo",
];

// Go: time/zoneinfo_unix.go:28 initLocal
// PORT: Go `syscall.Getenv` gives the raw bytes of the value; so does
// `as_encoded_bytes` on Unix.
fn init_local() -> jiff::tz::TimeZone {
    // consult $TZ to find the time zone to use.
    // no $TZ means use the system default /etc/localtime.
    // $TZ="" means use UTC.
    // $TZ="foo" or $TZ=":foo" if foo is an absolute path, then the file pointed
    // by foo will be used to initialize timezone; otherwise, file
    // /usr/share/zoneinfo/foo will be used.

    let tz = std::env::var_os("TZ");
    match tz.as_ref().map(|tz| tz.as_encoded_bytes()) {
        None => {
            if let Some(z) = load_location(b"localtime", &["/etc"]) {
                return z;
            }
        }
        Some(tz) if !tz.is_empty() => {
            let tz = tz.strip_prefix(b":").unwrap_or(tz);
            if tz.first() == Some(&b'/') {
                if let Some(z) = load_location(tz, &[""]) {
                    return z;
                }
            } else if !tz.is_empty() && tz != b"UTC" {
                if let Some(z) = load_location(tz, PLATFORM_ZONE_SOURCES) {
                    return z;
                }
            }
        }
        Some(_) => {}
    }

    // Fall back to UTC.
    jiff::tz::TimeZone::UTC
}

// Go: time/zoneinfo_read.go:531 loadLocation
// PORT: `initLocal` reads only whether it failed, so the Go first-error
// bookkeeping is dropped. After the sources Go tries the embedded
// `time/tzdata`, which tsgo does not import, and
// `runtime.GOROOT()/lib/time/zoneinfo.zip`. The port has no Go root, so
// that zip is not ported. It changes the result only for a zone name that
// no system source has.
fn load_location(name: &[u8], sources: &[&str]) -> Option<jiff::tz::TimeZone> {
    for source in sources {
        if let Some(zone_data) = load_tzinfo(name, source) {
            // Go: time/zoneinfo_read.go:118 LoadLocationFromTZData
            if let Ok(z) = jiff::tz::TimeZone::tzif(&String::from_utf8_lossy(name), &zone_data) {
                return Some(z);
            }
        }
    }
    None
}

// Go: time/zoneinfo_read.go:520 loadTzinfo
// Go: time/zoneinfo_read.go:367 loadTzinfoFromDirOrZip
// PORT: Go reads a source that ends in "tzdata" (Android) or ".zip" as an
// archive. No source in `initLocal` does, so only the directory case is
// ported.
fn load_tzinfo(name: &[u8], source: &str) -> Option<Vec<u8>> {
    let mut path = Vec::new();
    if !source.is_empty() {
        path.extend_from_slice(source.as_bytes());
        path.push(b'/');
    }
    path.extend_from_slice(name);
    read_file(&path)
}

// Go: time/zoneinfo_read.go:37 maxFileSize
const MAX_FILE_SIZE: usize = 10 << 20;

// Go: time/zoneinfo_read.go:575 readFile
// PORT: the path is raw bytes, as in Go. Go stops reading past
// `maxFileSize` and fails; this reads the file and then checks the size.
fn read_file(name: &[u8]) -> Option<Vec<u8>> {
    use std::os::unix::ffi::OsStrExt;
    let data = std::fs::read(std::ffi::OsStr::from_bytes(name)).ok()?;
    if data.len() > MAX_FILE_SIZE {
        return None;
    }
    Some(data)
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
    write_flattened_diagnostic_message(
        output,
        diagnostic,
        &format_opts.new_line,
        &format_opts.locale,
    );

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
                    &format_opts.locale,
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
pub fn write_flattened_diagnostic_message(
    writer: &Writer,
    diagnostic: &Diagnostic,
    newline: &str,
    locale: &Locale,
) {
    write_str(writer, &diagnostic_localize(diagnostic, locale));

    for chain in &diagnostic.message_chain {
        flatten_diagnostic_message_chain(writer, chain, newline, locale, 1);
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:271 flattenDiagnosticMessageChain
fn flatten_diagnostic_message_chain(
    writer: &Writer,
    chain: &Diagnostic,
    new_line: &str,
    locale: &Locale,
    level: usize,
) {
    write_str(writer, new_line);
    for _ in 0..level {
        write_str(writer, "  ");
    }

    write_str(writer, &diagnostic_localize(chain, locale));
    for child in &chain.message_chain {
        flatten_diagnostic_message_chain(writer, child, new_line, locale, level + 1);
    }
}

// Go: ast/diagnostic.go:101 (*Diagnostic).Localize, which the writer calls
// through the Go `diagnosticwriter.Diagnostic` interface.
// PORT: the Rust `Diagnostic::localize` (ast/misc.rs) takes no locale and
// writes English, so the writer calls Go `diagnostics.Localize` here. The
// port resolves the message when it makes the diagnostic, so the Go
// `messageKey` is never read.
fn diagnostic_localize(diagnostic: &Diagnostic, locale: &Locale) -> String {
    localize(
        locale,
        Some(diagnostic.message),
        "",
        &diagnostic.message_args,
    )
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

    let locale = &format_opts.locale;
    let message = if total_error_count == 1 {
        // Special-case a single error.
        if !error_summary.global_errors.is_empty() || first_file_name.is_empty() {
            message_localize(diag::Found_1_error, locale, &[])
        } else {
            message_localize(diag::Found_1_error_in_0, locale, &args![first_file_name])
        }
    } else {
        match num_erroring_files {
            // No file-specific errors.
            0 => message_localize(diag::Found_0_errors, locale, &args![total_error_count]),
            // One file with errors.
            1 => message_localize(
                diag::Found_0_errors_in_the_same_file_starting_at_Colon_1,
                locale,
                &args![total_error_count, first_file_name],
            ),
            // Multiple files with errors.
            _ => message_localize(
                diag::Found_0_errors_in_1_files,
                locale,
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
    // PORT: Go compares the bytes of the names (see `compare_go_bytes`).
    sorted_files
        .sort_by(|a, b| compare_go_bytes(source_file_file_name(*a), source_file_file_name(*b)));

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
    let header_row = message_localize(diag::Errors_Files, &format_opts.locale, &[]);
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
pub fn write_format_diagnostic(
    output: &Writer,
    diagnostic: &Diagnostic,
    format_opts: &FormattingOptions,
) {
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
    write_flattened_diagnostic_message(
        output,
        diagnostic,
        &format_opts.new_line,
        &format_opts.locale,
    );
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
    write_flattened_diagnostic_message(output, diag, &format_opts.new_line, &format_opts.locale);
}

// Go: diagnosticwriter/diagnosticwriter.go:487 FormatDiagnosticsStatusAndTime
pub fn format_diagnostics_status_and_time(
    output: &Writer,
    time: &str,
    diag: &Diagnostic,
    format_opts: &FormattingOptions,
) {
    write_str(output, &format!("{time} - "));
    write_flattened_diagnostic_message(output, diag, &format_opts.new_line, &format_opts.locale);
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
// Go standard library helpers used above and in help.rs
// ---------------------------------------------------------------------------

/// Go `fmt.Sprintf("%*s", width, s)`, or `"%-*s"` when `left` is true. Go
/// pads to `width` runes, and a negative width pads on the right.
pub(super) fn go_pad(s: &str, width: i32, left: bool) -> String {
    let left = left || width < 0;
    let width = width.unsigned_abs() as usize;
    if left {
        format!("{s:<width$}")
    } else {
        format!("{s:>width$}")
    }
}

/// Go `strings.Repeat`, which panics on a negative count.
pub(super) fn go_repeat(s: &str, count: i32) -> String {
    match usize::try_from(count) {
        Ok(count) => s.repeat(count),
        Err(_) => panic!("strings: negative Repeat count"),
    }
}
