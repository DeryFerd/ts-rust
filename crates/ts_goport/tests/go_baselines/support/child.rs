//! The process protocol of the tsc runner. No Go
//! equivalent: Go runs every `execute.CommandLine` and every build task in
//! the test process.
//!
//! PORT: a plain `tsc` run installs one program for the process
//! (`core::set_prog`), the OS override (`install_os_override`) is for the
//! whole process, and a `tsc -b` build compiles each project in a build
//! worker. So the runner runs each command in a child process (this test
//! binary again, test `__tsctest_child`), and a child's build runs each
//! worker in a process of its own (test `__tsctest_build_worker`), one at a
//! time on the orchestrator thread, so the one map file system and the fake
//! clock see one ordered sequence.
//!
//! ```text
//! runner (TestSys: map file system, clock, written files, default libs,
//!         FS differ, output)
//!   -> child: request with the command line and the state; the child
//!      installs the osvfs override, rebuilds the TestSys and runs
//!      execute_tsc::command_line with the TestSys as the Go `testing`;
//!      response with the exit status, the state, the output, the program
//!      baselines, whether it has a watcher and the watch state.
//!      A child with a watcher stays. Each edit sends it a watch request
//!      (changed paths, state); it sends the paths to its MockWatchBackend,
//!      runs DoCycle and sends a response (state, watch state).
//!      -> build worker (tsc -b only, TestSys::build_worker_runner):
//!         request (TSCTEST_WORKER_REQUEST): state, config, build command
//!         line, cached file system JSON; the worker runs
//!         compile_and_emit_worker; response (TSCTEST_WORKER_RESPONSE):
//!         state, result line, program cache line, the program baseline
//!         and the emitted file times.
//! ```
//!
//! Requests and responses are files under `TSCTEST_TMP` (default
//! `target/continuation-r97-goport/go-baseline-tests/tmp`), deleted after
//! use unless `TSCTEST_KEEP_CHILD_FILES=1`. The runner sends a command
//! child each file pair as a line on its stdin, and the child prints
//! `READY_MARKER` when the response is written. A build worker gets its
//! pair in the environment. The encoding is length prefixed bytes (little
//! endian lengths), so file data keeps its Go bytes.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::io::BufReader;
use std::path::{Path as OsPath, PathBuf};
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use rustc_hash::{FxHashMap, FxHashSet};
use ts_goport::core::{record_unported, unported_report};
use ts_goport::emitter::program_emit::{WriteFile, WriteFileData};
use ts_goport::execute::build::build_task::WorkerCompileResult;
use ts_goport::execute::build::worker::{
    WORKER_SINCE_START_ENV, WORKER_TTY_ENV, compile_and_emit_worker, marshal_worker_compile_result,
    marshal_worker_program_fs_cache, parse_worker_compile_result, parse_worker_program_fs_cache,
    read_worker_fs_cache,
};
use ts_goport::execute::execute_tsc::{TscCompilationHooks, command_line};
use ts_goport::execute::tsc::compile::{CommandLineResult, CommandLineTesting, ExitStatus, System};
use ts_goport::execute::watcher::set_test_watch_backend;
use ts_goport::frontend::vfs::{CachedFsState, Fs, OsOverride, install_os_override, osvfs_fs};
use ts_goport::gostd::{Context, context};

use crate::support::fsbaselineutil::FileChange;
use crate::support::runner::{FileMap, TscInput};
use crate::support::test_sys::{
    ClockState, ProgramParts, SerializedMtimes, SharedFs, SysMode, TestClock, TestSys,
    fs_error_text, lock, new_test_sys,
};
use crate::support::vfstest::{MapFs, MapFsState, MapFsStateFile, from_unix_nanos, unix_nanos};

/// The test that runs one command (see main.rs).
const CHILD_TEST: &str = "__tsctest_child";
/// The test that runs one build worker (see main.rs).
const BUILD_WORKER_TEST: &str = "__tsctest_build_worker";

/// Set for a command child (see `CommandChildProcess`).
const COMMAND_CHILD_ENV: &str = "TSCTEST_COMMAND_CHILD";
/// The libtest name of the test that `run_test_in_child` runs in this
/// process.
const IN_CHILD_ENV: &str = "TSCTEST_IN_CHILD";
const WORKER_REQUEST_ENV: &str = "TSCTEST_WORKER_REQUEST";
const WORKER_RESPONSE_ENV: &str = "TSCTEST_WORKER_RESPONSE";
const TMP_ENV: &str = "TSCTEST_TMP";
const KEEP_FILES_ENV: &str = "TSCTEST_KEEP_CHILD_FILES";
const DEFAULT_TMP: &str =
    "/home/theo/Code/sandbox/ts-rust/target/continuation-r97-goport/go-baseline-tests/tmp";

/// The stack of the compile thread in a child. The checker recurses
/// deeply, and the bins use the same size.
const STACK_SIZE: usize = 1 << 30;

/// Lines of the child's stderr that a failure shows.
const STDERR_TAIL_LINES: usize = 40;

const REQUEST_MAGIC: &[u8] = b"TSCTEST-REQUEST-2";
const RESPONSE_MAGIC: &[u8] = b"TSCTEST-RESPONSE-2";
const WATCH_REQUEST_MAGIC: &[u8] = b"TSCTEST-WATCH-REQUEST-1";
const WATCH_RESPONSE_MAGIC: &[u8] = b"TSCTEST-WATCH-RESPONSE-1";
/// The stdout line of a command child after each response file.
const READY_MARKER: &str = "TSCTEST-CHILD-RESPONSE-READY";
const WORKER_REQUEST_MAGIC: &[u8] = b"TSCTEST-WORKER-REQUEST-1";
const WORKER_RESPONSE_MAGIC: &[u8] = b"TSCTEST-WORKER-RESPONSE-1";

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

/// The plain state of a `TestSys` that moves between processes.
pub struct SysState {
    pub cwd: String,
    pub env: BTreeMap<String, String>,
    pub default_library_path: String,
    pub use_case_sensitive_file_names: bool,
    pub for_incremental_correctness: bool,
    pub clock: ClockState,
    pub map_fs: MapFsState,
    pub written_files: Vec<String>,
    /// `None` is Go `defaultLibs == nil`.
    pub default_libs: Option<Vec<String>>,
    /// The output buffer (port form bytes).
    pub output: Vec<u8>,
    pub program_baselines: String,
    pub program_include_baselines: String,
    /// The modification times of the runner's last FS baseline (Go
    /// `fsDiffer.SerializedDiff()`), for `OnEmittedFiles`.
    pub serialized_mtimes: Option<Vec<(String, Option<SystemTime>)>>,
}

/// The state of `sys` for a request or a response.
fn export_state(sys: &TestSys) -> SysState {
    let shared = sys.shared();
    let mut written_files: Vec<String> = lock(&shared.written_files).iter().cloned().collect();
    written_files.sort();
    let default_libs = lock(&shared.default_libs).as_ref().map(|libs| {
        let mut libs: Vec<String> = libs.iter().cloned().collect();
        libs.sort();
        libs
    });
    let (program_baselines, program_include_baselines) = sys.program_baseline_texts();
    let serialized_mtimes = sys.serialized_mtimes().map(|mtimes| {
        let mut mtimes: Vec<(String, Option<SystemTime>)> = mtimes.into_iter().collect();
        mtimes.sort();
        mtimes
    });
    SysState {
        cwd: sys.get_current_directory(),
        env: sys.env().clone(),
        default_library_path: sys.default_library_path(),
        use_case_sensitive_file_names: shared.map_fs.use_case_sensitive_file_names(),
        for_incremental_correctness: sys.for_incremental_correctness(),
        clock: shared.clock.state(),
        map_fs: shared.map_fs.export_state(),
        written_files,
        default_libs,
        output: sys.output_bytes(),
        program_baselines,
        program_include_baselines,
        serialized_mtimes,
    }
}

/// Applies the changing part of a state (clock, files, written files,
/// default libs) to `shared`.
fn apply_shared_state(shared: &SharedFs, state: &mut SysState) {
    shared.clock.set_state(state.clock);
    shared
        .map_fs
        .import_state(std::mem::take(&mut state.map_fs));
    *lock(&shared.written_files) = state.written_files.drain(..).collect();
    *lock(&shared.default_libs) = state
        .default_libs
        .take()
        .map(|libs| libs.into_iter().collect::<FxHashSet<String>>());
}

/// Applies a child's response state to the runner's `sys`.
fn apply_state(sys: &TestSys, mut state: SysState) {
    apply_shared_state(sys.shared(), &mut state);
    sys.set_output_bytes(state.output);
    sys.set_program_baseline_texts(state.program_baselines, state.program_include_baselines);
}

/// Applies the runner's state for a watch cycle to a command child's
/// `sys` (as `apply_state`, and the modification times of the runner's
/// last FS baseline).
fn apply_child_state(sys: &TestSys, mut state: SysState) {
    sys.set_child_serialized_mtimes(
        state
            .serialized_mtimes
            .take()
            .map(|mtimes| mtimes.into_iter().collect::<FxHashMap<_, _>>()),
    );
    apply_state(sys, state);
}

/// The test system that a child or a build worker rebuilds from `state`.
fn sys_from_state(state: SysState, mode: SysMode) -> TestSys {
    let clock = Arc::new(TestClock::new(state.clock.start));
    clock.set_state(state.clock);
    let map_fs = MapFs::from_map_with_clock(
        FileMap::new(),
        state.use_case_sensitive_file_names,
        clock.clone(),
    );
    map_fs.import_state(state.map_fs);
    let shared = SharedFs {
        map_fs,
        clock,
        default_libs: Arc::new(Mutex::new(
            state
                .default_libs
                .map(|libs| libs.into_iter().collect::<FxHashSet<String>>()),
        )),
        written_files: Arc::new(Mutex::new(state.written_files.into_iter().collect())),
    };
    let sys = TestSys::new(
        shared,
        state.cwd,
        state.default_library_path,
        state.env,
        state.for_incremental_correctness,
        mode,
    );
    sys.set_output_bytes(state.output);
    sys.set_program_baseline_texts(state.program_baselines, state.program_include_baselines);
    sys.set_child_serialized_mtimes(
        state
            .serialized_mtimes
            .map(|mtimes| mtimes.into_iter().collect::<FxHashMap<_, _>>()),
    );
    sys
}

/// Installs the osvfs override of a child or a build worker: every thread
/// that reads the OS file system gets a `testFs` view of `shared`.
fn install_override(shared: &SharedFs, current_directory: String) {
    let shared = shared.clone();
    install_os_override(OsOverride {
        fs: Arc::new(move || -> Rc<dyn Fs> { shared.test_fs() }),
        current_directory,
    });
}

// ---------------------------------------------------------------------------
// Encoding
// ---------------------------------------------------------------------------

#[derive(Default)]
struct Enc {
    buf: Vec<u8>,
}

impl Enc {
    fn u8(&mut self, v: u8) {
        self.buf.push(v);
    }
    fn bool(&mut self, v: bool) {
        self.u8(u8::from(v));
    }
    fn u32(&mut self, v: u32) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }
    fn u64(&mut self, v: u64) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }
    fn i64(&mut self, v: i64) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }
    fn len(&mut self, n: usize) {
        self.u64(n as u64);
    }
    fn bytes(&mut self, v: &[u8]) {
        self.len(v.len());
        self.buf.extend_from_slice(v);
    }
    /// A port form string, as its UTF-8 bytes.
    fn str(&mut self, v: &str) {
        self.bytes(v.as_bytes());
    }
    fn strs(&mut self, v: &[String]) {
        self.len(v.len());
        for s in v {
            self.str(s);
        }
    }
    fn opt_str(&mut self, v: Option<String>) {
        match v {
            Some(s) => {
                self.bool(true);
                self.str(&s);
            }
            None => self.bool(false),
        }
    }
    fn time(&mut self, v: SystemTime) {
        self.i64(unix_nanos(v));
    }
    fn opt_time(&mut self, v: Option<SystemTime>) {
        match v {
            Some(t) => {
                self.bool(true);
                self.time(t);
            }
            None => self.bool(false),
        }
    }
    fn opt_i64(&mut self, v: Option<i64>) {
        match v {
            Some(n) => {
                self.bool(true);
                self.i64(n);
            }
            None => self.bool(false),
        }
    }

    fn map_fs(&mut self, state: &MapFsState) {
        self.bool(state.use_case_sensitive_file_names);
        self.len(state.files.len());
        for file in &state.files {
            self.str(&file.canonical);
            self.bytes(&file.data);
            self.u32(file.mode);
            self.opt_time(file.mod_time);
            self.str(&file.realpath);
            self.opt_i64(file.sys_original);
        }
        self.len(state.symlinks.len());
        for (from, to) in &state.symlinks {
            self.str(from);
            self.str(to);
        }
    }

    fn sys_state(&mut self, state: &SysState) {
        self.str(&state.cwd);
        self.len(state.env.len());
        for (name, value) in &state.env {
            self.str(name);
            self.str(value);
        }
        self.str(&state.default_library_path);
        self.bool(state.use_case_sensitive_file_names);
        self.bool(state.for_incremental_correctness);
        self.time(state.clock.start);
        self.opt_time(state.clock.now);
        self.map_fs(&state.map_fs);
        self.strs(&state.written_files);
        match &state.default_libs {
            Some(libs) => {
                self.bool(true);
                self.strs(libs);
            }
            None => self.bool(false),
        }
        self.bytes(&state.output);
        self.str(&state.program_baselines);
        self.str(&state.program_include_baselines);
        match &state.serialized_mtimes {
            Some(mtimes) => {
                self.bool(true);
                self.len(mtimes.len());
                for (path, mtime) in mtimes {
                    self.str(path);
                    self.opt_time(*mtime);
                }
            }
            None => self.bool(false),
        }
    }

    fn program_parts(&mut self, parts: &[ProgramParts]) {
        self.len(parts.len());
        for part in parts {
            self.str(&part.config_file_path);
            self.str(&part.body);
            self.str(&part.include_body);
        }
    }

    fn unported(&mut self, unported: &[(&'static str, u64)]) {
        self.len(unported.len());
        for (name, count) in unported {
            self.str(name);
            self.u64(*count);
        }
    }
}

struct Dec<'a> {
    buf: &'a [u8],
    pos: usize,
}

type DecResult<T> = Result<T, String>;

impl<'a> Dec<'a> {
    fn new(buf: &'a [u8]) -> Dec<'a> {
        Dec { buf, pos: 0 }
    }
    fn take(&mut self, n: usize) -> DecResult<&'a [u8]> {
        let end = self
            .pos
            .checked_add(n)
            .filter(|&end| end <= self.buf.len())
            .ok_or_else(|| format!("truncated at byte {}", self.pos))?;
        let slice = &self.buf[self.pos..end];
        self.pos = end;
        Ok(slice)
    }
    fn magic(&mut self, magic: &[u8]) -> DecResult<()> {
        if self.take(magic.len())? != magic {
            return Err("bad magic".to_string());
        }
        Ok(())
    }
    fn u8(&mut self) -> DecResult<u8> {
        Ok(self.take(1)?[0])
    }
    fn bool(&mut self) -> DecResult<bool> {
        Ok(self.u8()? != 0)
    }
    fn u32(&mut self) -> DecResult<u32> {
        let bytes: [u8; 4] = self.take(4)?.try_into().expect("4 bytes");
        Ok(u32::from_le_bytes(bytes))
    }
    fn u64(&mut self) -> DecResult<u64> {
        let bytes: [u8; 8] = self.take(8)?.try_into().expect("8 bytes");
        Ok(u64::from_le_bytes(bytes))
    }
    fn i64(&mut self) -> DecResult<i64> {
        let bytes: [u8; 8] = self.take(8)?.try_into().expect("8 bytes");
        Ok(i64::from_le_bytes(bytes))
    }
    fn len(&mut self) -> DecResult<usize> {
        usize::try_from(self.u64()?).map_err(|err| err.to_string())
    }
    fn bytes(&mut self) -> DecResult<Vec<u8>> {
        let n = self.len()?;
        Ok(self.take(n)?.to_vec())
    }
    fn str(&mut self) -> DecResult<String> {
        String::from_utf8(self.bytes()?).map_err(|err| err.to_string())
    }
    fn strs(&mut self) -> DecResult<Vec<String>> {
        let n = self.len()?;
        (0..n).map(|_| self.str()).collect()
    }
    fn opt_str(&mut self) -> DecResult<Option<String>> {
        Ok(if self.bool()? {
            Some(self.str()?)
        } else {
            None
        })
    }
    fn time(&mut self) -> DecResult<SystemTime> {
        Ok(from_unix_nanos(self.i64()?))
    }
    fn opt_time(&mut self) -> DecResult<Option<SystemTime>> {
        Ok(if self.bool()? {
            Some(self.time()?)
        } else {
            None
        })
    }
    fn opt_i64(&mut self) -> DecResult<Option<i64>> {
        Ok(if self.bool()? {
            Some(self.i64()?)
        } else {
            None
        })
    }
    fn end(&self) -> DecResult<()> {
        if self.pos != self.buf.len() {
            return Err(format!("{} bytes left over", self.buf.len() - self.pos));
        }
        Ok(())
    }

    fn map_fs(&mut self) -> DecResult<MapFsState> {
        let use_case_sensitive_file_names = self.bool()?;
        let n = self.len()?;
        let mut files = Vec::with_capacity(n);
        for _ in 0..n {
            files.push(MapFsStateFile {
                canonical: self.str()?,
                data: self.bytes()?,
                mode: self.u32()?,
                mod_time: self.opt_time()?,
                realpath: self.str()?,
                sys_original: self.opt_i64()?,
            });
        }
        let n = self.len()?;
        let mut symlinks = Vec::with_capacity(n);
        for _ in 0..n {
            symlinks.push((self.str()?, self.str()?));
        }
        Ok(MapFsState {
            use_case_sensitive_file_names,
            files,
            symlinks,
        })
    }

    fn sys_state(&mut self) -> DecResult<SysState> {
        let cwd = self.str()?;
        let n = self.len()?;
        let mut env = BTreeMap::new();
        for _ in 0..n {
            let name = self.str()?;
            let value = self.str()?;
            env.insert(name, value);
        }
        let default_library_path = self.str()?;
        let use_case_sensitive_file_names = self.bool()?;
        let for_incremental_correctness = self.bool()?;
        let clock = ClockState {
            start: self.time()?,
            now: self.opt_time()?,
        };
        let map_fs = self.map_fs()?;
        let written_files = self.strs()?;
        let default_libs = if self.bool()? {
            Some(self.strs()?)
        } else {
            None
        };
        let output = self.bytes()?;
        let program_baselines = self.str()?;
        let program_include_baselines = self.str()?;
        let serialized_mtimes = if self.bool()? {
            let n = self.len()?;
            let mut mtimes = Vec::with_capacity(n);
            for _ in 0..n {
                mtimes.push((self.str()?, self.opt_time()?));
            }
            Some(mtimes)
        } else {
            None
        };
        Ok(SysState {
            cwd,
            env,
            default_library_path,
            use_case_sensitive_file_names,
            for_incremental_correctness,
            clock,
            map_fs,
            written_files,
            default_libs,
            output,
            program_baselines,
            program_include_baselines,
            serialized_mtimes,
        })
    }

    fn program_parts(&mut self) -> DecResult<Vec<ProgramParts>> {
        let n = self.len()?;
        let mut parts = Vec::with_capacity(n);
        for _ in 0..n {
            parts.push(ProgramParts {
                config_file_path: self.str()?,
                body: self.str()?,
                include_body: self.str()?,
            });
        }
        Ok(parts)
    }

    fn unported(&mut self) -> DecResult<Vec<(String, u64)>> {
        let n = self.len()?;
        let mut unported = Vec::with_capacity(n);
        for _ in 0..n {
            unported.push((self.str()?, self.u64()?));
        }
        Ok(unported)
    }
}

fn unported_text(unported: &[(String, u64)]) -> String {
    unported
        .iter()
        .map(|(name, count)| format!("{name} {count}"))
        .collect::<Vec<_>>()
        .join(", ")
}

// ---------------------------------------------------------------------------
// Processes
// ---------------------------------------------------------------------------

fn tmp_dir() -> PathBuf {
    match std::env::var_os(TMP_ENV) {
        Some(dir) if !dir.is_empty() => PathBuf::from(dir),
        _ => PathBuf::from(DEFAULT_TMP),
    }
}

fn keep_files() -> bool {
    std::env::var_os(KEEP_FILES_ENV).is_some_and(|value| value == "1")
}

/// A new request path and response path under `TSCTEST_TMP`.
fn new_file_pair(kind: &str) -> (PathBuf, PathBuf) {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let dir = tmp_dir();
    let _ = std::fs::create_dir_all(&dir);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let stem = format!("{}-{id}-{kind}", std::process::id());
    (
        dir.join(format!("{stem}.request")),
        dir.join(format!("{stem}.response")),
    )
}

fn remove_file(path: &OsPath) {
    if !keep_files() {
        let _ = std::fs::remove_file(path);
    }
}

/// Runs `test` of this test binary with the request file and returns the
/// response bytes. No response is an `Err` with the tail of the process's
/// stderr.
fn run_test_process(
    test: &str,
    request_env: &str,
    response_env: &str,
    kind: &str,
    request: &[u8],
) -> Result<Vec<u8>, String> {
    let (request_path, response_path) = new_file_pair(kind);
    std::fs::write(&request_path, request)
        .map_err(|err| format!("cannot write {}: {err}", request_path.display()))?;
    let _ = std::fs::remove_file(&response_path);
    let exe = std::env::current_exe().map_err(|err| format!("current test binary: {err}"))?;
    let output = std::process::Command::new(exe)
        .args(["--exact", test, "--nocapture", "--test-threads", "1"])
        .env_remove(WORKER_REQUEST_ENV)
        .env_remove(WORKER_RESPONSE_ENV)
        .env(request_env, &request_path)
        .env(response_env, &response_path)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output();
    remove_file(&request_path);
    let output = output.map_err(|err| format!("cannot run {test}: {err}"))?;
    if let Ok(response) = std::fs::read(&response_path) {
        remove_file(&response_path);
        // Pass on what a build worker wrote to stderr (a panic in a
        // checker thread, unported code) so the runner's failure shows
        // it.
        if !output.stderr.is_empty() && test == BUILD_WORKER_TEST {
            use std::io::Write;
            let _ = std::io::stderr().write_all(&output.stderr);
        }
        Ok(response)
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let lines: Vec<&str> = stderr.lines().collect();
        let tail = lines[lines.len().saturating_sub(STDERR_TAIL_LINES)..].join("\n");
        Err(format!(
            "{test} ended with {} and no response; stderr tail:\n{tail}",
            output.status
        ))
    }
}

/// Runs `f` on a thread with a large stack (like the bins) and waits. A
/// panic goes on to the caller, so the libtest test fails.
fn run_on_compile_thread(name: &str, f: impl FnOnce() + Send + 'static) {
    let handle = std::thread::Builder::new()
        .name(name.to_string())
        .stack_size(STACK_SIZE)
        .spawn(f)
        .expect("spawn the compile thread");
    if let Err(payload) = handle.join() {
        std::panic::resume_unwind(payload);
    }
}

fn read_request(path: &OsString) -> Vec<u8> {
    std::fs::read(path).unwrap_or_else(|err| panic!("cannot read request {path:?}: {err}"))
}

fn write_response(path: &OsString, bytes: &[u8]) {
    std::fs::write(path, bytes)
        .unwrap_or_else(|err| panic!("cannot write response {path:?}: {err}"));
}

// ---------------------------------------------------------------------------
// Command child
// ---------------------------------------------------------------------------

/// The hooks of a command child: Go `execute.CommandLine(ctx, sys,
/// commandLineArgs, sys)`.
pub struct ChildHooks {
    pub testing: Rc<TestSys>,
}

impl TscCompilationHooks for ChildHooks {
    fn build_mode(&self) -> bool {
        true
    }

    // Go writes emit output through the program host's FS, which is
    // `sys.FS()`. PORT: emit runs on checker threads and cannot hold the
    // `Rc` file system; like `GoTsc`, it writes through `osvfs_fs()`,
    // which the override makes a `testFs` view of the same state.
    fn write_file(&self) -> Option<WriteFile> {
        Some(Arc::new(
            |file_name: &str, text: &str, _data: &mut WriteFileData| -> Result<(), String> {
                osvfs_fs()
                    .write_file(file_name, text)
                    .map_err(|err| fs_error_text(&err))
            },
        ))
    }

    fn testing(&self) -> Option<Rc<dyn CommandLineTesting>> {
        Some(self.testing.clone())
    }
}

/// Go `execute.CommandLine(ctx, sys, commandLineArgs, sys)` in this
/// process. A watcher that the command makes uses `sys`'s
/// `MockWatchBackend` (Go `TestSys.WatchBackend`), through
/// `watcher::set_test_watch_backend` for this thread. The OS override must
/// already be installed for `sys` (see `install_override`).
pub fn command_line_in_process(
    ctx: &Context,
    sys: &Rc<TestSys>,
    command_line_args: &[String],
) -> CommandLineResult {
    set_test_watch_backend(sys.mock_watch_backend().clone());
    let hooks = ChildHooks {
        testing: sys.clone(),
    };
    command_line(ctx, sys.clone(), command_line_args, &hooks)
}

/// Go `newTestSys(input, false)` for a test that runs the compiler in this
/// process, which must be a child process of its own (see
/// `run_test_in_child`): it installs the OS override for the new system.
/// `command_line_args` is the command line that a `-b` build passes to its
/// build workers.
pub fn new_in_process_test_sys(input: &TscInput, command_line_args: &[&str]) -> Rc<TestSys> {
    let state = export_state(&new_test_sys(input, false));
    let sys = Rc::new(sys_from_state(
        state,
        SysMode::Child {
            command_line_args: command_line_args
                .iter()
                .map(|arg| arg.to_string())
                .collect(),
        },
    ));
    install_override(sys.shared(), sys.get_current_directory());
    sys
}

/// Runs `body` in a child process of its own (this test binary again,
/// test `test`, the libtest name of the calling test) and fails when that
/// process fails. In that child it runs `body` on a thread with a large
/// stack. A test that compiles in its own process uses this, because the
/// OS override is for the whole process.
pub fn run_test_in_child(test: &str, body: impl FnOnce() + Send + 'static) {
    if std::env::var_os(IN_CHILD_ENV).is_some_and(|value| value == test) {
        run_on_compile_thread(test, body);
        return;
    }
    let exe = std::env::current_exe().expect("current test binary");
    let output = std::process::Command::new(exe)
        .args(["--exact", test, "--nocapture", "--test-threads", "1"])
        .env_remove(WORKER_REQUEST_ENV)
        .env_remove(WORKER_RESPONSE_ENV)
        .env(IN_CHILD_ENV, test)
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap_or_else(|err| panic!("cannot run {test}: {err}"));
    // `--exact` with a wrong name runs no test and still succeeds.
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("1 passed"),
        "{test} failed in its child process ({}); stdout tail:\n{}\nstderr tail:\n{}",
        output.status,
        tail(&stdout),
        tail(&String::from_utf8_lossy(&output.stderr)),
    );
}

/// The last `STDERR_TAIL_LINES` lines of `text`.
fn tail(text: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    lines[lines.len().saturating_sub(STDERR_TAIL_LINES)..].join("\n")
}

/// The result of one command in a child process.
pub struct ChildRun {
    /// Go `result.Status`.
    pub status: ExitStatus,
    /// The unported Go code that the command reached (`name count`, ...),
    /// or `None`. A run with any is not a match.
    pub unported: Option<String>,
    /// Go `sys.mockWatchBackend.WatchState()` when the command made a
    /// watcher and the backend has watches, else `None`.
    pub watch_state: Option<String>,
    /// Go `result.Watcher`: the child keeps running while this lives.
    pub watcher: Option<WatchChild>,
}

/// The result of one watch cycle in a child (`WatchChild::do_cycle`).
pub struct WatchCycle {
    /// As `ChildRun::unported`, for the whole child so far.
    pub unported: Option<String>,
    /// As `ChildRun::watch_state`.
    pub watch_state: Option<String>,
}

/// A command child that holds a watcher (Go `result.Watcher`). Each
/// `do_cycle` sends it the runner's state and the changed paths; dropping
/// it ends the child.
pub struct WatchChild {
    process: CommandChildProcess,
}

impl WatchChild {
    /// Go `sys.mockWatchBackend.SendChangedPaths(changedPaths)` and
    /// `result.Watcher.DoCycle()` in the child. The child's state, output
    /// and program baselines replace those of `sys`. An `Err` is a child
    /// that ended without a response.
    pub fn do_cycle(
        &mut self,
        sys: &TestSys,
        changes: &[FileChange],
    ) -> Result<WatchCycle, String> {
        let mut enc = Enc::default();
        enc.buf.extend_from_slice(WATCH_REQUEST_MAGIC);
        enc.len(changes.len());
        for change in changes {
            enc.str(&change.path);
            enc.bool(change.deleted);
        }
        enc.sys_state(&export_state(sys));
        let response = self.process.step(&enc.buf)?;

        let mut dec = Dec::new(&response);
        let decoded = (|| -> DecResult<(SysState, Vec<(String, u64)>, Option<String>)> {
            dec.magic(WATCH_RESPONSE_MAGIC)?;
            let state = dec.sys_state()?;
            let unported = dec.unported()?;
            let watch_state = dec.opt_str()?;
            dec.end()?;
            Ok((state, unported, watch_state))
        })();
        let (state, unported, watch_state) =
            decoded.map_err(|err| format!("bad watch child response: {err}"))?;
        apply_state(sys, state);
        Ok(WatchCycle {
            unported: (!unported.is_empty()).then(|| unported_text(&unported)),
            watch_state,
        })
    }
}

/// A running command child. The runner sends it each request as a line
/// on its stdin (`<request path>\t<response path>`); the child writes the
/// response file and then prints `READY_MARKER` on its stdout. Closing
/// its stdin ends it.
struct CommandChildProcess {
    child: std::process::Child,
    stdin: Option<std::process::ChildStdin>,
    stdout: BufReader<std::process::ChildStdout>,
    stderr: Option<std::thread::JoinHandle<Vec<u8>>>,
}

impl CommandChildProcess {
    /// Starts a command child and returns it with its first response.
    fn start(request: &[u8]) -> Result<(CommandChildProcess, Vec<u8>), String> {
        let exe = std::env::current_exe().map_err(|err| format!("current test binary: {err}"))?;
        let mut child = std::process::Command::new(exe)
            .args(["--exact", CHILD_TEST, "--nocapture", "--test-threads", "1"])
            .env_remove(WORKER_REQUEST_ENV)
            .env_remove(WORKER_RESPONSE_ENV)
            .env_remove(IN_CHILD_ENV)
            .env(COMMAND_CHILD_ENV, "1")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .map_err(|err| format!("cannot run {CHILD_TEST}: {err}"))?;
        let stdin = child.stdin.take().expect("piped stdin");
        let stdout = BufReader::new(child.stdout.take().expect("piped stdout"));
        let mut stderr = child.stderr.take().expect("piped stderr");
        let stderr = std::thread::spawn(move || {
            let mut bytes = Vec::new();
            let _ = std::io::Read::read_to_end(&mut stderr, &mut bytes);
            bytes
        });
        let mut process = CommandChildProcess {
            child,
            stdin: Some(stdin),
            stdout,
            stderr: Some(stderr),
        };
        let response = process.step(request)?;
        Ok((process, response))
    }

    /// Sends one request and waits for its response. No response is an
    /// `Err` with the tail of the child's stderr.
    fn step(&mut self, request: &[u8]) -> Result<Vec<u8>, String> {
        use std::io::{BufRead, Write};
        let (request_path, response_path) = new_file_pair("child");
        std::fs::write(&request_path, request)
            .map_err(|err| format!("cannot write {}: {err}", request_path.display()))?;
        let _ = std::fs::remove_file(&response_path);
        let sent = self.stdin.as_mut().is_some_and(|stdin| {
            writeln!(
                stdin,
                "{}\t{}",
                request_path.display(),
                response_path.display()
            )
            .and_then(|()| stdin.flush())
            .is_ok()
        });
        let mut ready = false;
        if sent {
            let mut line = String::new();
            loop {
                line.clear();
                match self.stdout.read_line(&mut line) {
                    Ok(0) | Err(_) => break,
                    Ok(_) if line.trim_end().ends_with(READY_MARKER) => {
                        ready = true;
                        break;
                    }
                    Ok(_) => {}
                }
            }
        }
        remove_file(&request_path);
        let response = if ready {
            std::fs::read(&response_path).ok()
        } else {
            None
        };
        remove_file(&response_path);
        match response {
            Some(response) => Ok(response),
            None => {
                let (status, stderr) = self.finish();
                Err(format!(
                    "{CHILD_TEST} ended with {status} and no response; stderr tail:\n{}",
                    tail(&String::from_utf8_lossy(&stderr))
                ))
            }
        }
    }

    /// Closes the child's stdin and waits for it to end. Returns its exit
    /// status text and its stderr.
    fn finish(&mut self) -> (String, Vec<u8>) {
        self.stdin = None;
        let status = match self.child.wait() {
            Ok(status) => status.to_string(),
            Err(err) => format!("no exit status ({err})"),
        };
        let stderr = self
            .stderr
            .take()
            .and_then(|stderr| stderr.join().ok())
            .unwrap_or_default();
        (status, stderr)
    }
}

impl Drop for CommandChildProcess {
    fn drop(&mut self) {
        if self.stderr.is_some() {
            self.finish();
        }
    }
}

/// Go `execute.CommandLine(context.Background(), sys, commandLineArgs,
/// sys)` for the runner's `sys`, in a child process. The child's state,
/// output and program baselines replace those of `sys`. An `Err` is a
/// child without a response (a panic, for example unported code), with the
/// tail of its stderr. When the command makes a watcher, the child keeps
/// running in `ChildRun::watcher`.
pub fn run_command_in_child(
    sys: &TestSys,
    command_line_args: &[String],
) -> Result<ChildRun, String> {
    let mut enc = Enc::default();
    enc.buf.extend_from_slice(REQUEST_MAGIC);
    enc.strs(command_line_args);
    enc.sys_state(&export_state(sys));
    let (mut process, response) = CommandChildProcess::start(&enc.buf)?;

    let mut dec = Dec::new(&response);
    // (exit code, state, unported notes, has watcher, watch state)
    type Response = (i64, SysState, Vec<(String, u64)>, bool, Option<String>);
    let decoded = (|| -> DecResult<Response> {
        dec.magic(RESPONSE_MAGIC)?;
        let code = dec.i64()?;
        let state = dec.sys_state()?;
        let unported = dec.unported()?;
        let has_watcher = dec.bool()?;
        let watch_state = dec.opt_str()?;
        dec.end()?;
        Ok((code, state, unported, has_watcher, watch_state))
    })();
    let (code, state, unported, has_watcher, watch_state) =
        decoded.map_err(|err| format!("bad child response: {err}"))?;
    apply_state(sys, state);
    let status = i32::try_from(code)
        .ok()
        .and_then(ExitStatus::from_code)
        .ok_or_else(|| format!("UnknownExitStatus {code}"))?;
    let watcher = if has_watcher {
        Some(WatchChild { process })
    } else {
        process.finish();
        None
    };
    Ok(ChildRun {
        status,
        unported: (!unported.is_empty()).then(|| unported_text(&unported)),
        watch_state,
        watcher,
    })
}

/// Go `sys.mockWatchBackend.WatchState()` when the backend has watches.
fn watch_state_of(sys: &TestSys) -> Option<String> {
    let backend = sys.mock_watch_backend();
    backend.has_watches().then(|| backend.watch_state())
}

/// Tells the runner that the response file is written (see
/// `CommandChildProcess`). The leading newline ends a libtest line that
/// has no newline yet.
fn signal_ready() {
    use std::io::Write;
    let mut stdout = std::io::stdout().lock();
    let _ = write!(stdout, "\n{READY_MARKER}\n");
    let _ = stdout.flush();
}

/// The next `(request path, response path)` line on stdin, or `None` when
/// the runner closed stdin.
fn next_request() -> Option<(OsString, OsString)> {
    let mut line = String::new();
    match std::io::stdin().read_line(&mut line) {
        Ok(0) | Err(_) => None,
        Ok(_) => {
            let (request, response) = line.trim_end_matches('\n').split_once('\t')?;
            Some((OsString::from(request), OsString::from(response)))
        }
    }
}

/// The entry of a command child (`__tsctest_child` in main.rs). Returns at
/// once unless the runner started this process.
pub fn command_child_entry() {
    if std::env::var_os(COMMAND_CHILD_ENV).is_none() {
        return;
    }
    run_on_compile_thread("tsctest-child", move || {
        let Some((request_path, response_path)) = next_request() else {
            return;
        };
        let request = read_request(&request_path);
        let mut dec = Dec::new(&request);
        let decoded = (|| -> DecResult<(Vec<String>, SysState)> {
            dec.magic(REQUEST_MAGIC)?;
            let args = dec.strs()?;
            let state = dec.sys_state()?;
            dec.end()?;
            Ok((args, state))
        })();
        let (args, state) = decoded.unwrap_or_else(|err| panic!("bad child request: {err}"));

        let sys = Rc::new(sys_from_state(
            state,
            SysMode::Child {
                command_line_args: args.clone(),
            },
        ));
        // Before any compiler call (see `install_override`).
        install_override(sys.shared(), sys.get_current_directory());

        let result = command_line_in_process(&context::background(), &sys, &args);

        let mut enc = Enc::default();
        enc.buf.extend_from_slice(RESPONSE_MAGIC);
        enc.i64(i64::from(result.status.code()));
        enc.sys_state(&export_state(&sys));
        enc.unported(&unported_report());
        enc.bool(result.watcher.is_some());
        enc.opt_str(result.watcher.as_ref().and_then(|_| watch_state_of(&sys)));
        write_response(&response_path, &enc.buf);
        signal_ready();

        // Go runner.go:105: each edit sends the changed paths to the mock
        // backend and runs one `DoCycle`.
        let Some(mut watcher) = result.watcher else {
            return;
        };
        while let Some((request_path, response_path)) = next_request() {
            let request = read_request(&request_path);
            let mut dec = Dec::new(&request);
            let decoded = (|| -> DecResult<(Vec<FileChange>, SysState)> {
                dec.magic(WATCH_REQUEST_MAGIC)?;
                let n = dec.len()?;
                let mut changes = Vec::with_capacity(n);
                for _ in 0..n {
                    changes.push(FileChange {
                        path: dec.str()?,
                        deleted: dec.bool()?,
                    });
                }
                let state = dec.sys_state()?;
                dec.end()?;
                Ok((changes, state))
            })();
            let (changes, state) =
                decoded.unwrap_or_else(|err| panic!("bad watch child request: {err}"));
            // Go `sys.clearOutput()` also resets the tracer of the one
            // system.
            sys.clear_output();
            apply_child_state(&sys, state);

            sys.mock_watch_backend().send_changed_paths(&changes);
            watcher.do_cycle();

            let mut enc = Enc::default();
            enc.buf.extend_from_slice(WATCH_RESPONSE_MAGIC);
            enc.sys_state(&export_state(&sys));
            enc.unported(&unported_report());
            enc.opt_str(watch_state_of(&sys));
            write_response(&response_path, &enc.buf);
            signal_ready();
        }
    });
}

// ---------------------------------------------------------------------------
// Build worker
// ---------------------------------------------------------------------------

/// What a command child's build worker runner needs (`Send + Sync`, see
/// `TestSys::build_worker_runner`).
pub struct WorkerContext {
    pub shared: SharedFs,
    pub cwd: String,
    pub env: BTreeMap<String, String>,
    pub default_library_path: String,
    /// The child's `-b` command line (Go `o.opts.Command`).
    pub build_command_line: Vec<String>,
    /// The child's `TestSys::child_serialized_mtimes`, read when a worker
    /// starts.
    pub serialized_mtimes: SerializedMtimes,
    pub results: Arc<Mutex<crate::support::test_sys::WorkerResults>>,
}

/// Runs one build worker for `config` in a process of its own and applies
/// its state to the child (`BuildWorkerRunner`, called by the orchestrator
/// on its own thread). A worker without a response is reported like a
/// failed worker process (`WorkerLauncher::run`): `NotImplemented`, and the
/// child counts it as unported.
pub fn run_build_worker(
    context: &WorkerContext,
    config: &str,
    fs_cache: &str,
    on_program_fs_cache: &mut dyn FnMut(CachedFsState),
) -> WorkerCompileResult {
    let failed = |message: String| {
        eprintln!("tsctest: build worker for {config} failed: {message}");
        record_unported("build worker");
        WorkerCompileResult {
            exit_status: ExitStatus::NotImplemented,
            output: String::new(),
            diagnostics: Vec::new(),
            diagnostic_file_texts: Vec::new(),
            emitted_files: Vec::new(),
            has_changed_dts_file: false,
            build_info_emit: None,
            statistics: None,
            output_time_stamps: Vec::new(),
            fs_cache: CachedFsState::default(),
        }
    };

    // The worker's system gives the orchestrator's answers: Go `TestSys`
    // output is a TTY, and `SinceStart` is the test clock's.
    let mut env = context.env.clone();
    env.insert(WORKER_TTY_ENV.to_string(), "1".to_string());
    env.insert(WORKER_SINCE_START_ENV.to_string(), "0".to_string());
    let shared = &context.shared;
    let mut written_files: Vec<String> = lock(&shared.written_files).iter().cloned().collect();
    written_files.sort();
    let default_libs = lock(&shared.default_libs).as_ref().map(|libs| {
        let mut libs: Vec<String> = libs.iter().cloned().collect();
        libs.sort();
        libs
    });
    let serialized_mtimes = lock(&context.serialized_mtimes).clone().flatten();
    let serialized_mtimes = serialized_mtimes.as_ref().map(|mtimes| {
        let mut mtimes: Vec<(String, Option<SystemTime>)> =
            mtimes.iter().map(|(k, v)| (k.clone(), *v)).collect();
        mtimes.sort();
        mtimes
    });
    let state = SysState {
        cwd: context.cwd.clone(),
        env,
        default_library_path: context.default_library_path.clone(),
        use_case_sensitive_file_names: shared.map_fs.use_case_sensitive_file_names(),
        for_incremental_correctness: false,
        clock: shared.clock.state(),
        map_fs: shared.map_fs.export_state(),
        written_files,
        default_libs,
        output: Vec::new(),
        program_baselines: String::new(),
        program_include_baselines: String::new(),
        serialized_mtimes,
    };

    let mut enc = Enc::default();
    enc.buf.extend_from_slice(WORKER_REQUEST_MAGIC);
    enc.str(config);
    enc.strs(&context.build_command_line);
    enc.bytes(fs_cache.as_bytes());
    enc.sys_state(&state);
    let response = match run_test_process(
        BUILD_WORKER_TEST,
        WORKER_REQUEST_ENV,
        WORKER_RESPONSE_ENV,
        "worker",
        &enc.buf,
    ) {
        Ok(response) => response,
        Err(message) => return failed(message),
    };

    let mut dec = Dec::new(&response);
    let decoded = (|| -> DecResult<WorkerResponse> {
        dec.magic(WORKER_RESPONSE_MAGIC)?;
        let state = dec.sys_state()?;
        let result_line = dec.str()?;
        let program_line = dec.str()?;
        let programs = dec.program_parts()?;
        let n = dec.len()?;
        let mut emitted_times = Vec::with_capacity(n);
        for _ in 0..n {
            emitted_times.push((dec.str()?, dec.time()?));
        }
        let unported = dec.unported()?;
        dec.end()?;
        Ok(WorkerResponse {
            state,
            result_line,
            program_line,
            programs,
            emitted_times,
            unported,
        })
    })();
    let mut response = match decoded {
        Ok(response) => response,
        Err(err) => return failed(format!("bad worker response: {err}")),
    };

    // The worker wrote through the same file system and clock.
    apply_shared_state(shared, &mut response.state);
    {
        let mut results = lock(&context.results);
        results
            .programs
            .entry(config.to_string())
            .or_default()
            .extend(response.programs);
        results.emitted_times.extend(response.emitted_times);
    }
    if !response.unported.is_empty() {
        eprintln!(
            "tsctest: build worker for {config} reached unported code: {}",
            unported_text(&response.unported)
        );
        // Like `WorkerLauncher::run` after `EXIT_UNPORTED`.
        record_unported("build worker");
    }
    if let Some(state) = parse_worker_program_fs_cache(response.program_line.as_bytes()) {
        on_program_fs_cache(state);
    }
    match parse_worker_compile_result(&response.result_line) {
        Some(result) => result,
        None => failed("bad worker result line".to_string()),
    }
}

struct WorkerResponse {
    state: SysState,
    result_line: String,
    program_line: String,
    programs: Vec<ProgramParts>,
    emitted_times: Vec<(String, SystemTime)>,
    unported: Vec<(String, u64)>,
}

/// The entry of a build worker (`__tsctest_build_worker` in main.rs).
/// Returns at once unless a command child started this process.
pub fn build_worker_entry() {
    let Some(request_path) = std::env::var_os(WORKER_REQUEST_ENV) else {
        return;
    };
    let response_path = std::env::var_os(WORKER_RESPONSE_ENV)
        .expect("TSCTEST_WORKER_RESPONSE is set with TSCTEST_WORKER_REQUEST");
    run_on_compile_thread("tsctest-build-worker", move || {
        let request = read_request(&request_path);
        let mut dec = Dec::new(&request);
        let decoded = (|| -> DecResult<(String, Vec<String>, Vec<u8>, SysState)> {
            dec.magic(WORKER_REQUEST_MAGIC)?;
            let config = dec.str()?;
            let build_command_line = dec.strs()?;
            let fs_cache = dec.bytes()?;
            let state = dec.sys_state()?;
            dec.end()?;
            Ok((config, build_command_line, fs_cache, state))
        })();
        let (config, build_command_line, fs_cache, state) =
            decoded.unwrap_or_else(|err| panic!("bad build worker request: {err}"));

        let sys = Rc::new(sys_from_state(state, SysMode::Worker));
        // Before any compiler call (see `install_override`).
        install_override(sys.shared(), sys.get_current_directory());

        let fs_cache = read_worker_fs_cache(&mut fs_cache.as_slice())
            .unwrap_or_else(|message| panic!("build worker: bad file system cache: {message}"));
        let mut program_line = String::new();
        let mut record = |state: &CachedFsState| {
            program_line = marshal_worker_program_fs_cache(state);
        };
        let result = compile_and_emit_worker(
            sys.clone(),
            &config,
            &build_command_line,
            &fs_cache,
            &mut record,
            Some(sys.clone()),
        );

        let mut enc = Enc::default();
        enc.buf.extend_from_slice(WORKER_RESPONSE_MAGIC);
        enc.sys_state(&export_state(&sys));
        enc.str(&marshal_worker_compile_result(&result));
        enc.str(&program_line);
        enc.program_parts(&sys.take_worker_programs());
        let emitted_times = sys.take_emitted_times();
        enc.len(emitted_times.len());
        for (file, time) in &emitted_times {
            enc.str(file);
            enc.time(*time);
        }
        enc.unported(&unported_report());
        write_response(&response_path, &enc.buf);
    });
}
