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
// PORT: testing (`CommandLineTesting`)
use crate::execute::build::build_task::WorkerCompileResult;
use crate::frontend::compiler::TraceFn;
use crate::frontend::tspath::Path;
use crate::frontend::vfs::CachedFsState;
use crate::locale::Locale;
use std::sync::{Arc, Mutex};

/// Go `io.Writer`. A caller that wants the text back (Go `bytes.Buffer`)
/// keeps its own `Rc<RefCell<Vec<u8>>>` and passes a clone as a `Writer`.
pub type Writer = Rc<RefCell<dyn std::io::Write>>;

/// Writes `text` to `w`. Go ignores the `fmt.Fprint` error, so this does too.
// PORT: `text` is the port form of a Go string (see
// `scanner_util::GO_STRING_MARKER`), and a writer keeps that form. The
// process output writes the Go bytes (`GoOutput`, `write_go_output`).
pub fn write_str(w: &Writer, text: &str) {
    let _ = w.borrow_mut().write_all(text.as_bytes());
}

/// Writes the Go bytes of the port form output `bytes` to `out` (see
/// `scanner_util::GO_STRING_MARKER`). Bytes that are not UTF-8 are written
/// unchanged.
pub fn write_go_output(out: &mut dyn std::io::Write, bytes: &[u8]) -> std::io::Result<()> {
    match std::str::from_utf8(bytes) {
        Ok(text) => out.write_all(&go_string_bytes(text)),
        Err(_) => out.write_all(bytes),
    }
}

/// Go `os.Stdout` as the system writer: it writes the Go bytes of each port
/// form write (see `write_go_output`). `write_str` writes whole strings, so a
/// write never splits a unit.
pub struct GoOutput;

impl std::io::Write for GoOutput {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        write_go_output(&mut std::io::stdout().lock(), buf)?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        std::io::stdout().flush()
    }
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

/// The exit code of a goport bin that hit unported code, another panic or
/// a failed worker. It is outside the Go `ExitStatus` range (0 to 5), so it
/// never looks like a tsgo status. 70 is `EX_SOFTWARE` (internal software
/// error). The build worker also exits with it after its result line when
/// it reached unported code.
pub const EXIT_UNPORTED: i32 = 70;

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

// Go: execute/tsc/compile.go:50 CommandLineTesting
// PORT: testing. The Go test harness hook (tsctests/sys.go `TestSys`).
// Every real run passes `None` (Go nil), so it takes the Go nil paths. Go
// `io.Writer` is `Writer`. Go `*collections.SyncMap[tspath.Path,
// time.Time]` is the build host `m_times`, a `Mutex` (`None` is the Go zero
// time).
// The last three methods have no Go equivalent and do nothing by default:
// the port compiles each build project in a worker process
// (build/worker.rs), so a test can run the worker itself and gets the
// task's program and emitted files back on the orchestrator side.
pub trait CommandLineTesting {
    // Ensure that all emitted files are timestamped in order to ensure they are deterministic for test baseline
    fn on_emitted_files(
        &self,
        result: &EmitResult,
        m_times_cache: Option<&Mutex<FxHashMap<Path, Option<SystemTime>>>>,
    );
    fn on_list_files_start(&self, w: &Writer);
    fn on_list_files_end(&self, w: &Writer);
    fn on_statistics_start(&self, w: &Writer);
    fn on_statistics_end(&self, w: &Writer);
    fn on_build_status_report_start(&self, w: &Writer);
    fn on_build_status_report_end(&self, w: &Writer);
    fn on_watch_status_report_start(&self);
    fn on_watch_status_report_end(&self);
    fn get_trace(&self, w: Writer, locale: Locale) -> TraceFn;
    fn on_program(&self, program: &crate::execute::incremental::program::Program);

    /// PORT: testing, no Go equivalent. The runner that replaces the build
    /// worker process (see `BuildWorkerRunner`). `None` keeps the process.
    fn build_worker_runner(&self) -> Option<BuildWorkerRunner> {
        None
    }

    /// PORT: testing. Go `Testing.OnProgram(t.result.program)` when the
    /// build task of `config` reports (build/buildtask.go:109). The program
    /// is in the worker, so the test keeps what its worker saw.
    fn on_build_task_program(&self, _config: &str) {}

    /// PORT: testing. The orchestrator part of Go `OnEmittedFiles` for a
    /// build worker's `emitted_files`: Go updates the orchestrator host
    /// `mTimes` (`TestingMTimesCache`, build/buildtask.go:230).
    fn on_worker_emitted_files(
        &self,
        _emitted_files: &[String],
        _m_times: &Mutex<FxHashMap<Path, Option<SystemTime>>>,
    ) {
    }
}

/// PORT: testing, no Go equivalent. Runs one build worker in place of the
/// worker process (`WorkerLauncher::run`): it gets the task config, the
/// orchestrator's cached file system as JSON (shared_fs.rs) and the
/// callback for the program's cache entries, and returns the worker result.
/// The orchestrator calls it on its own thread, one task at a time, so a
/// test file system and clock see one ordered sequence.
pub type BuildWorkerRunner =
    Arc<dyn Fn(&str, &str, &mut dyn FnMut(CachedFsState)) -> WorkerCompileResult + Send + Sync>;

// Go: execute/tsc/compile.go:66 CompileTimes
// PORT: Go keeps `bindTime`, `checkTime`, `totalTime` and `emitTime`
// unexported; the bins set them, so all fields are public.
#[derive(Clone, Copy, Debug, Default)]
pub struct CompileTimes {
    pub config_time: Duration,
    pub parse_time: Duration,
    pub bind_time: Duration,
    pub check_time: Duration,
    pub total_time: Duration,
    pub emit_time: Duration,
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
// PORT: added here so the library and the bins share one system.
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
    let cwd = match crate::frontend::vfs::os_current_dir() {
        Ok(cwd) => cwd,
        Err(err) => {
            eprintln!("Error getting current directory: {err}");
            return Err(ExitStatus::InvalidProjectOutputsSkipped);
        }
    };
    Ok(OsSystem {
        cwd: crate::frontend::tspath::normalize_path(&cwd),
        fs: crate::frontend::bundled::wrap_fs(crate::frontend::vfs::osvfs_fs()),
        default_library_path: crate::frontend::bundled::lib_path(),
        writer: Rc::new(RefCell::new(GoOutput)),
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

    /// The system with `start` as its start time. Go `SinceStart` counts
    /// from the process start, which a bin can read before it makes the
    /// system.
    pub fn with_start(mut self, start: std::time::Instant) -> OsSystem {
        self.start = start;
        self
    }
}

impl System for OsSystem {
    // Go: cmd/tsgo/sys.go:45 Writer
    fn writer(&self) -> Writer {
        self.writer.clone()
    }
    // Go: cmd/tsgo/sys.go:33 FS
    fn fs(&self) -> Rc<dyn Fs> {
        self.fs.clone()
    }
    // Go: cmd/tsgo/sys.go:37 DefaultLibraryPath
    fn default_library_path(&self) -> String {
        self.default_library_path.clone()
    }
    // Go: cmd/tsgo/sys.go:41 GetCurrentDirectory
    fn get_current_directory(&self) -> String {
        self.cwd.clone()
    }
    // Go: cmd/tsgo/sys.go:49 WriteOutputIsTTY
    fn write_output_is_tty(&self) -> bool {
        use std::io::IsTerminal;
        std::io::stdout().is_terminal()
    }
    // Go: cmd/tsgo/sys.go:53 GetWidthOfTerminal
    // Go `term.GetSize(int(os.Stdout.Fd()))` is the TIOCGWINSZ ioctl on
    // stdout, and gives width 0 on error (golang.org/x/term v0.44.0
    // term_unix.go:59 getSize).
    // PORT: `rustix::termios::tcgetwinsize` makes the same ioctl, so this
    // crate needs no unsafe code. This is the Unix path; the port targets
    // Linux.
    fn get_width_of_terminal(&self) -> i32 {
        match rustix::termios::tcgetwinsize(std::io::stdout()) {
            Ok(ws) => i32::from(ws.ws_col),
            Err(_) => 0,
        }
    }
    // Go: cmd/tsgo/sys.go:58 GetEnvironmentVariable
    fn get_environment_variable(&self, name: &str) -> String {
        std::env::var(name).unwrap_or_default()
    }
    // Go: cmd/tsgo/sys.go:29 Now
    fn now(&self) -> SystemTime {
        SystemTime::now()
    }
    // Go: cmd/tsgo/sys.go:25 SinceStart
    fn since_start(&self) -> Duration {
        self.start.elapsed()
    }
}
