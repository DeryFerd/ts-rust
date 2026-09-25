//! Go: execute/tsc/compile.go (the `tsc` system interface, exit status and
//! compile result types), plus the `osSys` system of cmd/tsgo/sys.go.
//!
//! PORT: Go `io.Writer` is `Writer` (a shared `std::io::Write`). The
//! frontend file system is `Rc`, so the system and the writers are `Rc`
//! too and stay on one thread. A build runs each project in its own worker
//! process, so no writer is shared across threads.

use crate::prelude::*;

use std::time::{Duration, SystemTime};

use crate::emitter::program_emit::EmitResult;
use crate::frontend::vfs::Fs;

/// Go `io.Writer`. A caller that wants the text back (Go `bytes.Buffer`)
/// keeps its own `Rc<RefCell<Vec<u8>>>` and passes a clone as a `Writer`.
pub type Writer = Rc<RefCell<dyn std::io::Write>>;

/// Writes `text` to `w`. Go ignores the `fmt.Fprint` error, so this does too.
pub fn write_str(w: &Writer, text: &str) {
    let _ = w.borrow_mut().write_all(text.as_bytes());
}

// Go: execute/tsc/compile.go:17 System
// PORT: Go `FS()` returns the shared `vfs.FS`. Go `time.Time` is
// `SystemTime` and `time.Duration` is `Duration`.
pub trait System {
    fn writer(&self) -> Writer;
    fn fs(&self) -> Rc<dyn Fs>;
    fn default_library_path(&self) -> String;
    fn get_current_directory(&self) -> String;
    fn write_output_is_tty(&self) -> bool;
    fn get_width_of_terminal(&self) -> i32;
    fn get_environment_variable(&self, name: &str) -> String;

    fn now(&self) -> SystemTime;
    fn since_start(&self) -> Duration;
}

// Go: execute/tsc/compile.go:30 ExitStatus
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(i32)]
pub enum ExitStatus {
    #[default]
    Success = 0,
    DiagnosticsPresentOutputsSkipped = 1,
    DiagnosticsPresentOutputsGenerated = 2,
    InvalidProjectOutputsSkipped = 3,
    ProjectReferenceCycleOutputsSkipped = 4,
    NotImplemented = 5,
}

impl ExitStatus {
    /// The process exit code (Go `os.Exit(int(status))`).
    pub fn code(self) -> i32 {
        self as i32
    }

    /// The status for an exit code, or `None` for an unknown code. The build
    /// worker protocol uses it to read a status back.
    pub fn from_code(code: i32) -> Option<ExitStatus> {
        Some(match code {
            0 => ExitStatus::Success,
            1 => ExitStatus::DiagnosticsPresentOutputsSkipped,
            2 => ExitStatus::DiagnosticsPresentOutputsGenerated,
            3 => ExitStatus::InvalidProjectOutputsSkipped,
            4 => ExitStatus::ProjectReferenceCycleOutputsSkipped,
            5 => ExitStatus::NotImplemented,
            _ => return None,
        })
    }
}

// Go: execute/tsc/compile.go:41 Watcher
// PORT: watch mode is out of scope; the trait exists for `CommandLineResult`.
pub trait Watcher {
    fn do_cycle(&mut self);
}

// Go: execute/tsc/compile.go:45 CommandLineResult
#[derive(Default)]
pub struct CommandLineResult {
    pub status: ExitStatus,
    pub watcher: Option<Box<dyn Watcher>>,
}

// PORT: Go execute/tsc/compile.go:50 CommandLineTesting is the Go test
// harness hook. It is not ported: every Go caller outside tests passes nil,
// so the port always takes the nil paths.

// Go: execute/tsc/compile.go:66 CompileTimes
// PORT: the unexported Go fields are `pub(crate)`.
#[derive(Clone, Debug, Default)]
pub struct CompileTimes {
    pub config_time: Duration,
    pub parse_time: Duration,
    pub(crate) bind_time: Duration,
    pub(crate) check_time: Duration,
    pub(crate) total_time: Duration,
    pub(crate) emit_time: Duration,
    pub build_info_read_time: Duration,
    pub changes_compute_time: Duration,
}

// Go: execute/tsc/compile.go:76 CompileAndEmitResult
// PORT: Go `*compiler.EmitResult` is never nil after `EmitFilesAndReportErrors`,
// so it is a value here (`Default` for the Go zero result). Go `times` is a
// pointer shared with the caller's `CompileTimes`.
#[derive(Clone, Default)]
pub struct CompileAndEmitResult {
    pub diagnostics: Vec<Diagnostic>,
    pub emit_result: EmitResult,
    pub status: ExitStatus,
    pub(crate) times: Rc<RefCell<CompileTimes>>,
}

// Go: cmd/tsgo/sys.go:17 osSys
// PORT: added here so the library and the bins share one system. Go reads
// the terminal size with `golang.org/x/term`; the port has no terminal API,
// so the width is 0 (the Go result when the size cannot be read).
pub struct OsSystem {
    writer: Writer,
    fs: Rc<dyn Fs>,
    default_library_path: String,
    cwd: String,
    start: std::time::Instant,
}

// Go: cmd/tsgo/sys.go:62 newSystem
// PORT: Go exits with `ExitStatusInvalidProject_OutputsSkipped` when the
// current directory cannot be read; this returns that status instead.
pub fn new_os_system() -> Result<OsSystem, ExitStatus> {
    let cwd = match std::env::current_dir() {
        Ok(cwd) => cwd,
        Err(err) => {
            eprintln!("Error getting current directory: {err}");
            return Err(ExitStatus::InvalidProjectOutputsSkipped);
        }
    };
    Ok(OsSystem {
        cwd: crate::frontend::tspath::normalize_path(&cwd.to_string_lossy()),
        fs: crate::frontend::bundled::wrap_fs(crate::frontend::vfs::osvfs_fs()),
        default_library_path: crate::frontend::bundled::lib_path(),
        writer: Rc::new(RefCell::new(std::io::stdout())),
        start: std::time::Instant::now(),
    })
}

impl OsSystem {
    /// The system with `writer` in place of stdout. The build worker writes
    /// its report into a buffer this way.
    pub fn with_writer(mut self, writer: Writer) -> OsSystem {
        self.writer = writer;
        self
    }
}

impl System for OsSystem {
    // Go: cmd/tsgo/sys.go:47 Writer
    fn writer(&self) -> Writer {
        self.writer.clone()
    }
    // Go: cmd/tsgo/sys.go:35 FS
    fn fs(&self) -> Rc<dyn Fs> {
        self.fs.clone()
    }
    // Go: cmd/tsgo/sys.go:39 DefaultLibraryPath
    fn default_library_path(&self) -> String {
        self.default_library_path.clone()
    }
    // Go: cmd/tsgo/sys.go:43 GetCurrentDirectory
    fn get_current_directory(&self) -> String {
        self.cwd.clone()
    }
    // Go: cmd/tsgo/sys.go:51 WriteOutputIsTTY
    fn write_output_is_tty(&self) -> bool {
        use std::io::IsTerminal;
        std::io::stdout().is_terminal()
    }
    // Go: cmd/tsgo/sys.go:55 GetWidthOfTerminal
    fn get_width_of_terminal(&self) -> i32 {
        0
    }
    // Go: cmd/tsgo/sys.go:60 GetEnvironmentVariable
    fn get_environment_variable(&self, name: &str) -> String {
        std::env::var(name).unwrap_or_default()
    }
    // Go: cmd/tsgo/sys.go:31 Now
    fn now(&self) -> SystemTime {
        SystemTime::now()
    }
    // Go: cmd/tsgo/sys.go:27 SinceStart
    fn since_start(&self) -> Duration {
        self.start.elapsed()
    }
}
