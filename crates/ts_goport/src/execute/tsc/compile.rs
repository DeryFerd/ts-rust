//! Go: execute/tsc/compile.go (the `tsc` system interface, exit status and
//! compile result types), plus the `osSys` system of cmd/tsgo/sys.go.
//!
//! PORT: Go `io.Writer` is `Writer` (a shared `std::io::Write`). The
//! frontend file system is `Rc`, so the system and the writers are `Rc`
//! too and stay on one thread. A build compiles every project on the
//! orchestrator thread, so no writer is shared across threads. The one
//! exception is Go `ErrorWriter()` (`ErrorWriter`): the content mapper
//! logger writes to it from the thread that reads a mapper's stderr.

use crate::prelude::*;

use std::time::{Duration, SystemTime};

use crate::contentmapper::{
    self, Host as ContentMapperHost, HostOptions as ContentMapperHostOptions,
    Logger as ContentMapperLogger, ProcessExitState, Spawner as ContentMapperSpawner,
};
use crate::emitter::program_emit::EmitResult;
use crate::frontend::tsoptions::ParseConfigHost;
use crate::frontend::vfs::Fs;
use crate::gostd::{Context, GoError};
// PORT: testing (`CommandLineTesting`)
use crate::frontend::compiler::TraceFn;
use crate::frontend::tspath::Path;
use crate::locale::Locale;
use std::sync::{Arc, Mutex, PoisonError};

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

/// Go `os.Stderr` as the system error writer: it writes the Go bytes of
/// each port form write, as `GoOutput` does for stdout.
pub struct GoErrorOutput;

impl std::io::Write for GoErrorOutput {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        write_go_output(&mut std::io::stderr().lock(), buf)?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        std::io::stderr().flush()
    }
}

/// Go `io.Writer` of `System.ErrorWriter()`. The content mapper logger
/// writes to it from a mapper's stderr thread, so it is `Send` and has its
/// own lock.
pub type ErrorWriter = Arc<Mutex<dyn std::io::Write + Send>>;

// Go: execute/tsc/compile.go:22 System
// PORT: Go `FS()` returns the shared `vfs.FS`. Go `time.Time` is
// `SystemTime` and `time.Duration` is `Duration`. Go `Spawn` returns an
// `io.ReadWriteCloser`; here it is the content mapper's
// `ProcessExitState` (an `ipc::ReadWriteCloser`, see there), and Go
// `stderr` `io.Discard` is `None`, as in `contentmapper::Spawner`.
pub trait System {
    fn writer(&self) -> Writer;
    fn error_writer(&self) -> ErrorWriter;
    fn fs(&self) -> Rc<dyn Fs>;
    fn default_library_path(&self) -> String;
    fn get_current_directory(&self) -> String;
    fn write_output_is_tty(&self) -> bool;
    fn get_width_of_terminal(&self) -> i32;
    fn get_environment_variable(&self, name: &str) -> String;
    fn spawn(
        &self,
        command: &[String],
        dir: &str,
        stderr: Option<Box<dyn std::io::Write + Send>>,
    ) -> Result<Arc<dyn ProcessExitState>, GoError>;

    fn now(&self) -> SystemTime;
    fn since_start(&self) -> Duration;
}

// Go: execute/tsc/compile.go:37 newContentMapperLogger
// PORT: Go `mu` guards the writes; the `ErrorWriter` lock does that here.
// Go `fmt.Fprintln(writer, message)` is one write of the line.
pub(crate) fn new_content_mapper_logger(sys: &dyn System) -> Option<ContentMapperLogger> {
    if sys
        .get_environment_variable("TS_CONTENT_MAPPER_DEBUG")
        .is_empty()
    {
        return None;
    }
    let writer = sys.error_writer();
    Some(Arc::new(move |message: &str| {
        let mut writer = writer.lock().unwrap_or_else(PoisonError::into_inner);
        let _ = writer.write_all(format!("{message}\n").as_bytes());
    }))
}

/// Go `tsc.System` as the `contentmapper.Spawner` of the host (Go passes
/// `sys`, whose `Spawn` method makes it a `Spawner`).
struct SystemSpawner(Rc<dyn System>);

impl ContentMapperSpawner for SystemSpawner {
    fn spawn(
        &self,
        command: &[String],
        dir: &str,
        stderr: Option<Box<dyn std::io::Write + Send>>,
    ) -> Result<Arc<dyn ProcessExitState>, GoError> {
        self.0.spawn(command, dir, stderr)
    }
}

// Go: execute/tsc/compile.go:89 NewContentMapperHost
// NewContentMapperHost creates a content mapper host when content mappers are enabled via the
// --runExternalCode flag, spawning mapper processes through the system's Spawn. It returns
// nil otherwise, in which case no content-mapped files can be loaded. The caller owns the host and must
// Close it when the compilation session ends.
// PORT: Go nil is `None`. `sys` is the `Rc` so that the host can keep it
// as its spawner.
pub fn new_content_mapper_host(
    ctx: &Context,
    sys: &Rc<dyn System>,
    options: &CompilerOptions,
) -> Option<Rc<dyn ContentMapperHost>> {
    if !options.run_external_code.is_true() {
        return None;
    }
    let (diagnostic_locale, _) = crate::locale::parse(&options.locale);
    Some(contentmapper::new_host_with_options(
        ctx,
        Rc::new(SystemSpawner(sys.clone())),
        diagnostic_locale,
        ContentMapperHostOptions {
            logger: new_content_mapper_logger(&**sys),
        },
    ))
}

/// Go `tsc.System` as a `tsoptions.ParseConfigHost` (Go passes `sys`
/// where a `ParseConfigHost` is needed; it has `FS()` and
/// `GetCurrentDirectory()`).
pub struct SystemParseConfigHost<'a>(pub &'a dyn System);

impl ParseConfigHost for SystemParseConfigHost<'_> {
    fn fs(&self) -> Rc<dyn Fs> {
        self.0.fs()
    }

    fn get_current_directory(&self) -> String {
        self.0.get_current_directory()
    }
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

    /// The status for an exit code, or `None` for an unknown code. The Go
    /// baseline runner uses it to read a child's status back.
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

/// The exit code of a goport bin that hit unported code or another panic,
/// or whose work thread failed. It is outside the Go `ExitStatus` range (0
/// to 5), so it never looks like a tsgo status. 70 is `EX_SOFTWARE`
/// (internal software error).
pub const EXIT_UNPORTED: i32 = 70;

// Go: execute/tsc/compile.go:61 Watcher
pub trait Watcher {
    fn do_cycle(&mut self);

    /// PORT: not in Go. Go tests assert the concrete type
    /// (`result.Watcher.(*execute.Watcher)`); a Rust test downcasts this.
    fn as_any(&self) -> &dyn std::any::Any;
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
}

// Go: execute/tsc/compile.go:99 CompileTimes
// PORT: Go keeps `bindTime`, `checkTime`, `totalTime` and `emitTime`
// unexported; the bins set them, so all fields are public.
#[derive(Clone, Debug, Default)]
pub struct CompileTimes {
    pub config_time: Duration,
    pub parse_time: Duration,
    pub content_mapper_times: contentmapper::Timings,
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
    /// The system with `writer` in place of stdout. A bin that keeps its
    /// output in a buffer, or streams it, uses this.
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
    // Go: cmd/tsgo/sys.go:47 Writer
    fn writer(&self) -> Writer {
        self.writer.clone()
    }
    // Go: cmd/tsgo/sys.go:51 ErrorWriter (tsgo#4712)
    fn error_writer(&self) -> ErrorWriter {
        Arc::new(Mutex::new(GoErrorOutput))
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
    // Go: cmd/tsgo/sys.go:64 GetEnvironmentVariable
    fn get_environment_variable(&self, name: &str) -> String {
        std::env::var(name).unwrap_or_default()
    }
    // Go: cmd/tsgo/sys.go:68 Spawn (tsgo#4712)
    fn spawn(
        &self,
        command: &[String],
        dir: &str,
        stderr: Option<Box<dyn std::io::Write + Send>>,
    ) -> Result<Arc<dyn ProcessExitState>, GoError> {
        spawn_process(command, dir, stderr)
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

/// Go `cmd.WaitDelay = time.Second` in `spawnProcess`: how long `Close`
/// waits for the stderr copy after the process exits.
const CHILD_PROCESS_WAIT_DELAY: Duration = Duration::from_secs(1);

// Go: cmd/tsgo/sys.go:74 spawnProcess (tsgo#4712)
// spawnProcess launches a process and adapts its stdio to an io.ReadWriteCloser (Read is its stdout,
// Write is its stdin).
// PORT: Go `exec.Command` looks a name without a slash up in PATH
// (`look_path`), and `Start` checks `Dir` first. Their Go error texts reach
// the content mapper diagnostics, so this makes the same texts. The child's
// stdin, stdout and stderr are Unix socket pairs, not pipes: Go's `Close`
// closes the parent ends while the connection may still read and the
// stderr copy may still run, and a socket `shutdown` ends those blocked
// calls in safe Rust. Go `stderr` `io.Discard` is `None` (the null device
// here). Go `cmd.Env` nil and the argv[0] of the name are kept.
pub fn spawn_process(
    command: &[String],
    dir: &str,
    stderr: Option<Box<dyn std::io::Write + Send>>,
) -> Result<Arc<dyn ProcessExitState>, GoError> {
    use std::os::fd::OwnedFd;
    use std::os::unix::net::UnixStream;
    use std::os::unix::process::CommandExt;
    use std::process::{Command, Stdio};

    let name = command.first().map_or("", String::as_str);
    // Go `Start`: "exec: no command" for an empty path.
    if name.is_empty() {
        return Err(crate::gostd::errors::new("exec: no command"));
    }
    // Go `exec.Command` calls `LookPath` only when the name has no slash.
    let program = if name.contains('/') {
        name.to_string()
    } else {
        look_path(name)?
    };
    // Go os/exec_posix.go startProcess: the `Dir` check with op "chdir".
    if !dir.is_empty()
        && let Err(err) = std::fs::metadata(dir)
    {
        return Err(crate::gostd::errors::new(format!(
            "chdir {dir}: {}",
            go_errno_text(&err)
        )));
    }
    let io_error = |err: std::io::Error| crate::gostd::errors::new(go_errno_text(&err));
    let (stdin, child_stdin) = UnixStream::pair().map_err(io_error)?;
    let (stdout, child_stdout) = UnixStream::pair().map_err(io_error)?;
    let mut cmd = Command::new(&program);
    cmd.arg0(name).args(&command[1..]);
    if !dir.is_empty() {
        cmd.current_dir(dir);
    }
    cmd.stdin(Stdio::from(OwnedFd::from(child_stdin)));
    cmd.stdout(Stdio::from(OwnedFd::from(child_stdout)));
    let mut stderr_copy = None;
    match stderr {
        Some(writer) => {
            let (ours, child_stderr) = UnixStream::pair().map_err(io_error)?;
            let reader = ours.try_clone().map_err(io_error)?;
            cmd.stderr(Stdio::from(OwnedFd::from(child_stderr)));
            stderr_copy = Some((ours, reader, writer));
        }
        None => {
            cmd.stderr(Stdio::null());
        }
    }
    let spawned = cmd.spawn();
    // The command holds the child's ends; drop them so that a read sees the
    // end of the stream when the child exits.
    drop(cmd);
    let child = spawned.map_err(|err| {
        crate::gostd::errors::new(format!("fork/exec {program}: {}", go_errno_text(&err)))
    })?;
    // Go copies a non-file `cmd.Stderr` on a goroutine.
    let stderr = stderr_copy.map(|(stream, reader, mut writer)| {
        let (done_tx, done) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let _ = std::io::copy(&mut &reader, &mut writer);
            let _ = done_tx.send(());
        });
        ChildStderr { stream, done }
    });
    Ok(Arc::new(ChildProcess {
        child: Mutex::new(Some(child)),
        stdin,
        stdout,
        stderr: Mutex::new(stderr),
        exit_code: Mutex::new(None),
    }))
}

// Go: cmd/tsgo/sys.go:95 childProcess (tsgo#4712)
// childProcess adapts a spawned process's stdout (read) and stdin (write) into one io.ReadWriteCloser.
// Close kills and reaps the process.
// PORT: Go `cmd.ProcessState` after `Wait` is `exit_code` (the Go
// `ExitCode()` value). `child` is `None` after `Close`.
struct ChildProcess {
    child: Mutex<Option<std::process::Child>>,
    stdin: std::os::unix::net::UnixStream,
    stdout: std::os::unix::net::UnixStream,
    stderr: Mutex<Option<ChildStderr>>,
    exit_code: Mutex<Option<i32>>,
}

/// The parent end of the child's stderr and the end signal of its copy.
struct ChildStderr {
    stream: std::os::unix::net::UnixStream,
    done: std::sync::mpsc::Receiver<()>,
}

impl crate::ipc::ReadWriteCloser for ChildProcess {
    // Go: cmd/tsgo/sys.go:101 childProcess.Read
    fn read(&self, buf: &mut [u8]) -> std::io::Result<usize> {
        std::io::Read::read(&mut &self.stdout, buf)
    }

    // Go: cmd/tsgo/sys.go:102 childProcess.Write
    fn write(&self, buf: &[u8]) -> std::io::Result<usize> {
        std::io::Write::write(&mut &self.stdin, buf)
    }

    fn flush(&self) -> std::io::Result<()> {
        std::io::Write::flush(&mut &self.stdin)
    }

    // Go: cmd/tsgo/sys.go:111 childProcess.Close
    // PORT: Go `Wait` closes the stdout pipe after the process exits, and
    // waits up to `WaitDelay` for the stderr copy; then it closes that pipe
    // and returns `ErrWaitDelay`, which Close ignores. An `ExitError` is
    // `Ok` here too. A second Close is Go's second `Wait`.
    fn close(&self) -> Result<(), GoError> {
        use std::net::Shutdown;
        let _ = self.stdin.shutdown(Shutdown::Both);
        let Some(mut child) = self
            .child
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take()
        else {
            return Err(crate::gostd::errors::new("exec: Wait was already called"));
        };
        let _ = child.kill();
        let waited = child.wait();
        let _ = self.stdout.shutdown(Shutdown::Both);
        let stderr = self
            .stderr
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take();
        if let Some(stderr) = stderr {
            let _ = stderr.done.recv_timeout(CHILD_PROCESS_WAIT_DELAY);
            let _ = stderr.stream.shutdown(Shutdown::Both);
        }
        match waited {
            Ok(status) => {
                // Go `ProcessState.ExitCode()`: -1 for a signal.
                *self.exit_code.lock().unwrap_or_else(PoisonError::into_inner) =
                    Some(status.code().unwrap_or(-1));
                Ok(())
            }
            Err(err) => Err(crate::gostd::errors::new(format!(
                "wait: {}",
                go_errno_text(&err)
            ))),
        }
    }
}

impl ProcessExitState for ChildProcess {
    // Go: cmd/tsgo/sys.go:104 childProcess.ExitCode
    fn exit_code(&self) -> (i32, bool) {
        match *self.exit_code.lock().unwrap_or_else(PoisonError::into_inner) {
            Some(code) => (code, true),
            None => (0, false),
        }
    }
}

/// Go `exec.LookPath(file)` (os/exec/lp_unix.go, go1.26) for a name without
/// a slash, with the Go `exec.Error` texts.
// PORT: Go `execerrdot` is its default: a match in a relative PATH entry is
// the `ErrDot` error.
fn look_path(file: &str) -> Result<String, GoError> {
    let exec_error = |text: &str| {
        crate::gostd::errors::new(format!(
            "exec: {}: {text}",
            crate::gostd::strconv::quote(file)
        ))
    };
    let path = std::env::var("PATH").unwrap_or_default();
    // Go `filepath.SplitList("")` is empty.
    if !path.is_empty() {
        for dir in path.split(':') {
            // Unix shell semantics: path element "" means "."
            let dir = if dir.is_empty() { "." } else { dir };
            let candidate = go_path_clean(&format!("{dir}/{file}"));
            if find_executable(&candidate) {
                if !candidate.starts_with('/') {
                    return Err(exec_error(
                        "cannot run executable found relative to current directory",
                    ));
                }
                return Ok(candidate);
            }
        }
    }
    Err(exec_error("executable file not found in $PATH"))
}

/// Go os/exec/lp_unix.go `findExecutable(file) == nil`.
fn find_executable(file: &str) -> bool {
    use rustix::fs::{Access, AtFlags, CWD, accessat};
    use rustix::io::Errno;
    use std::os::unix::fs::PermissionsExt;
    let Ok(metadata) = std::fs::metadata(file) else {
        return false;
    };
    if metadata.is_dir() {
        return false;
    }
    match accessat(CWD, file, Access::EXEC_OK, AtFlags::EACCESS) {
        Ok(()) => true,
        // ENOSYS means Eaccess is not available or not implemented.
        // EPERM can be returned by Linux containers employing seccomp.
        // In both cases, fall back to checking the permission bits.
        Err(Errno::NOSYS | Errno::PERM) => metadata.permissions().mode() & 0o111 != 0,
        Err(_) => false,
    }
}

/// Go `path.Clean` (the Unix `filepath.Clean`).
fn go_path_clean(path: &str) -> String {
    if path.is_empty() {
        return ".".to_string();
    }
    let path = path.as_bytes();
    let rooted = path[0] == b'/';
    let n = path.len();
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let (mut r, mut dotdot) = (0, 0);
    if rooted {
        out.push(b'/');
        (r, dotdot) = (1, 1);
    }
    while r < n {
        if path[r] == b'/' {
            r += 1;
        } else if path[r] == b'.' && (r + 1 == n || path[r + 1] == b'/') {
            r += 1;
        } else if path[r] == b'.'
            && path[r + 1] == b'.'
            && (r + 2 == n || path[r + 2] == b'/')
        {
            r += 2;
            if out.len() > dotdot {
                // Go drops bytes up to and with the last '/'.
                let mut last = out.pop();
                while out.len() > dotdot && last != Some(b'/') {
                    last = out.pop();
                }
            } else if !rooted {
                if !out.is_empty() {
                    out.push(b'/');
                }
                out.extend_from_slice(b"..");
                dotdot = out.len();
            }
        } else {
            if (rooted && out.len() != 1) || (!rooted && !out.is_empty()) {
                out.push(b'/');
            }
            while r < n && path[r] != b'/' {
                out.push(path[r]);
                r += 1;
            }
        }
    }
    if out.is_empty() {
        return ".".to_string();
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// The Go text of an OS error: Go's errno table is the C text with a
/// lowercase first letter, without Rust's " (os error N)".
fn go_errno_text(err: &std::io::Error) -> String {
    let text = err.to_string();
    let text = match err.raw_os_error() {
        Some(code) => text
            .strip_suffix(&format!(" (os error {code})"))
            .unwrap_or(&text)
            .to_string(),
        None => text,
    };
    let mut chars = text.chars();
    match chars.next() {
        Some(first) => first.to_lowercase().chain(chars).collect(),
        None => String::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    // Go: execute/tsc/emit_test.go:22 contentMapperLoggingTestSystem (tsgo#4712)
    // PORT: Go embeds `timingTestSystem`. The logger reads only
    // `GetEnvironmentVariable` and `ErrorWriter`; the file system is Go's
    // nil `fs` there, and here a call to it fails the test.
    struct ContentMapperLoggingTestSystem {
        enabled: Cell<bool>,
        stderr: Arc<Mutex<Vec<u8>>>,
    }

    impl System for ContentMapperLoggingTestSystem {
        fn writer(&self) -> Writer {
            Rc::new(RefCell::new(std::io::sink()))
        }
        fn error_writer(&self) -> ErrorWriter {
            self.stderr.clone()
        }
        fn fs(&self) -> Rc<dyn Fs> {
            unreachable!("the content mapper logger reads no file system")
        }
        fn default_library_path(&self) -> String {
            "/lib".to_string()
        }
        fn get_current_directory(&self) -> String {
            "/project".to_string()
        }
        fn write_output_is_tty(&self) -> bool {
            false
        }
        fn get_width_of_terminal(&self) -> i32 {
            0
        }
        fn get_environment_variable(&self, name: &str) -> String {
            if name == "TS_CONTENT_MAPPER_DEBUG" && self.enabled.get() {
                return "1".to_string();
            }
            String::new()
        }
        fn spawn(
            &self,
            _command: &[String],
            _dir: &str,
            _stderr: Option<Box<dyn std::io::Write + Send>>,
        ) -> Result<Arc<dyn ProcessExitState>, GoError> {
            Err(crate::gostd::errors::new(
                "spawn not implemented in timingTestSystem",
            ))
        }
        fn now(&self) -> SystemTime {
            SystemTime::UNIX_EPOCH
        }
        fn since_start(&self) -> Duration {
            Duration::ZERO
        }
    }

    // Go: execute/tsc/emit_test.go:39 TestContentMapperLoggerEnvironmentVariable (tsgo#4712)
    #[test]
    fn test_content_mapper_logger_environment_variable() {
        let sys = ContentMapperLoggingTestSystem {
            enabled: Cell::new(false),
            stderr: Arc::default(),
        };
        assert!(new_content_mapper_logger(&sys).is_none());
        sys.enabled.set(true);
        let logger = new_content_mapper_logger(&sys).expect("logger");
        std::thread::scope(|scope| {
            for _ in 0..10 {
                let logger = logger.clone();
                scope.spawn(move || logger("mapper log"));
            }
        });
        let stderr = sys.stderr.lock().unwrap_or_else(PoisonError::into_inner);
        assert_eq!(
            String::from_utf8_lossy(&stderr),
            "mapper log\n".repeat(10)
        );
    }

    // Go: cmd/tsgo/sys_unix_test.go:17 TestChildProcessCloseDoesNotWaitForLauncherDescendants (tsgo#4712)
    // PORT: Go reads the first line with `bufio.Reader`; this reads bytes
    // up to the newline. Go `syscall.Kill` is rustix `kill_process`.
    #[test]
    fn test_child_process_close_does_not_wait_for_launcher_descendants() {
        use crate::cmd::tsgo::prelude::is_process_alive;
        use rustix::process::{Pid, Signal, kill_process};

        let command: Vec<String> = ["sh", "-c", "nohup sleep 60 & echo $!; wait"]
            .iter()
            .map(|arg| (*arg).to_string())
            .collect();
        let process = spawn_process(&command, "", Some(Box::new(Vec::<u8>::new())))
            .expect("spawnProcess");
        let mut pid_text = Vec::new();
        let mut byte = [0u8; 1];
        loop {
            let n = process.read(&mut byte).expect("ReadString");
            assert_ne!(n, 0, "EOF before the pid line");
            if byte[0] == b'\n' {
                break;
            }
            pid_text.push(byte[0]);
        }
        let descendant_pid: i32 = String::from_utf8_lossy(&pid_text)
            .trim()
            .parse()
            .expect("strconv.Atoi");
        let kill = |pid: i32| {
            if let Some(pid) = Pid::from_raw(pid) {
                let _ = kill_process(pid, Signal::KILL);
            }
        };
        let (done_tx, done) = std::sync::mpsc::channel();
        {
            let process = process.clone();
            std::thread::spawn(move || {
                let _ = done_tx.send(process.close());
            });
        }

        let completed = match done.recv_timeout(Duration::from_secs(2)) {
            Ok(result) => {
                assert!(result.is_ok(), "Close: {:?}", result.err().map(|e| e.error()));
                true
            }
            Err(_) => {
                kill(descendant_pid);
                let _ = done.recv();
                false
            }
        };
        assert!(
            completed,
            "child process shutdown waited for a launcher descendant"
        );
        if is_process_alive(descendant_pid) {
            kill(descendant_pid);
        }
    }
}
