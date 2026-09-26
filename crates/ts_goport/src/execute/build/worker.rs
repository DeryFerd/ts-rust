//! The build worker (plan D1): the program part of Go `compileAndEmit`
//! (execute/build/buildtask.go:179) for one project, in its own process.
//!
//! The program state is process-wide (`core::PROGRAM`), so a build cannot
//! make one program per project in one process. The orchestrator process
//! runs `<exe> --build-worker <config> <build command line...>` for each
//! project that needs a compile. The worker parses the same build command
//! line, makes the same build host, runs `ReadBuildInfoProgram`,
//! `NewProgram`, `incremental.NewProgram` and `EmitAndReportStatistics`
//! with the task writer and `writeFile` of the Go task, and prints one JSON
//! line with the `WorkerCompileResult`. The orchestrator applies that result
//! in `BuildTask::compile_and_emit_finish`.
//!
//! Protocol (stdout, one line, compact JSON):
//! `{"exitStatus":0,"output":"...","diagnosticsCount":0,"emittedFiles":[...],
//!   "hasChangedDtsFile":false,"buildInfoFileName":"..." | null,
//!   "fsCache":{...}}`
//! Before it, right after the program is made, the worker writes one
//! `{"fsCacheProgram":{...}}` line: the cached file system entries the
//! program load added. The worker writes nothing else to stdout. On stdin
//! the orchestrator sends the build's cached file system (see
//! shared_fs.rs); `fsCache` is what the worker added after the program
//! line. Traces and diagnostics go to
//! `output`. Unported code and panics are reported on stderr, which the
//! worker shares with the orchestrator.

use crate::emitter::program_emit::{WriteFile, WriteFileData};
use crate::execute::build::build_task::WorkerCompileResult;
use crate::execute::build::command_line::parse_build_command_line;
use crate::execute::build::host::{BuildCompilerHost, BuildHost};
use crate::execute::build::shared_fs::{decode_cached_fs_state, marshal_cached_fs_state};
use crate::execute::incremental::incremental::Host as IncrementalHost;
use crate::execute::incremental::program::{
    new_program as new_incremental_program, read_build_info_program,
};
use crate::execute::tsc::compile::{CompileTimes, EXIT_UNPORTED, ExitStatus, System, Writer};
use crate::execute::tsc::diagnostics::{create_diagnostic_reporter, quiet_diagnostics_reporter};
use crate::execute::tsc::emit::{
    EmitInput, emit_and_report_statistics, get_trace_with_writer_from_sys,
};
use crate::frontend::prelude::*;
use std::sync::{Arc, Mutex};

/// The first argument that selects the worker entry of the build binary.
pub const BUILD_WORKER_FLAG: &str = "--build-worker";

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

/// The Go `comparePathsOptions` of `NewOrchestrator` (orchestrator.go:612).
pub fn compare_paths_options_of_sys(sys: &dyn System) -> ComparePathsOptions {
    ComparePathsOptions {
        current_directory: sys.get_current_directory(),
        use_case_sensitive_file_names: sys.fs().use_case_sensitive_file_names(),
    }
}

// Go: build/buildtask.go:179 (*BuildTask).compileAndEmit, the program part
// (from `ReadBuildInfoProgram` to `EmitAndReportStatistics`), with the
// build info branch of build/buildtask.go:785 (*BuildTask).writeFile.
//
// `build_command_line` is the full `-b` command line of the orchestrator
// (Go `o.opts.Command`). `config` is the task config name (Go `t.config`).
// `fs_cache` is the orchestrator's cached file system (Go `o.host.FS()`,
// see shared_fs.rs); it is loaded before the config is parsed.
// `report_program_fs_cache` gets the entries that `NewProgram` added, as
// soon as the program is made.
//
// PORT: Go `t.reportDiagnostic` also appends to `t.errors`; the worker has
// no task, so only the count goes back (see `WorkerCompileResult`).
// Statistics are out of scope (see build_task.rs); the compile times are
// still filled in as Go does.
pub fn compile_and_emit_worker(
    sys: Rc<dyn System>,
    config: &str,
    build_command_line: &[String],
    fs_cache: &CachedFsState,
    report_program_fs_cache: &mut dyn FnMut(&CachedFsState),
) -> WorkerCompileResult {
    let command = Rc::new(parse_build_command_line(
        build_command_line,
        &SystemParseConfigHost(&*sys),
    ));
    let host = Rc::new(BuildHost::new(
        sys.clone(),
        command.clone(),
        compare_paths_options_of_sys(&*sys),
    ));
    host.cached_fs.load_state(fs_cache);
    let path = host.to_path(config);
    // Go `t.resolved`, parsed by the orchestrator host in createBuildTasks.
    let resolved = host
        .get_resolved_project_reference(config, &path)
        .unwrap_or_else(|| panic!("build worker: cannot parse config {config}"));

    // Go `&t.result.builder`
    let builder: Rc<RefCell<Vec<u8>>> = Rc::new(RefCell::new(Vec::new()));
    let writer: Writer = builder.clone();
    // Go `t.result.diagnosticReporter`: orchestrator.go:597 createDiagnosticReporter(task)
    let report_diagnostic =
        create_diagnostic_reporter(&*sys, writer.clone(), &command.compiler_options);

    // Real build
    let compile_times = Rc::new(RefCell::new(CompileTimes::default()));
    let config_time = host
        .config_times
        .borrow()
        .get(&path)
        .copied()
        .unwrap_or_default();
    compile_times.borrow_mut().config_time = config_time;
    let build_info_read_start = sys.now();
    let mut old_program = None;
    if !command.build_options.force.is_true() {
        let compiler_host_rc: Rc<dyn CompilerHost> = host.clone();
        old_program = read_build_info_program(&resolved, &*host, &*compiler_host_rc);
    }
    compile_times.borrow_mut().build_info_read_time = sys
        .now()
        .duration_since(build_info_read_start)
        .unwrap_or_default();
    let parse_start = sys.now();
    let compiler_host: Rc<dyn CompilerHost> = Rc::new(BuildCompilerHost {
        host: host.clone(),
        trace: get_trace_with_writer_from_sys(writer.clone()),
    });
    // Go: compiler.NewProgram(compiler.ProgramOptions{Config, Host})
    // PORT: the process has one program, so the new program is installed
    // for the process (see PORTING.md "Program").
    if let Err(message) = crate::program::install_new_program(ProgramOptions {
        host: compiler_host,
        config: resolved.clone(),
        use_source_of_project_reference: false,
        single_threaded: Tristate::Unknown,
        typings_location: String::new(),
        project_name: String::new(),
    }) {
        panic!("build worker: cannot load program for {config}: {message}");
    }
    compile_times.borrow_mut().parse_time =
        sys.now().duration_since(parse_start).unwrap_or_default();
    // PORT: in Go the program's lookups are in the shared cache as they
    // happen; send them now, not only when the worker ends (shared_fs.rs).
    let program_fs_cache = host.cached_fs.state_excluding(&[fs_cache]);
    report_program_fs_cache(&program_fs_cache);
    let changes_compute_start = sys.now();
    let program = new_incremental_program(
        old_program.as_ref(),
        host.clone() as Rc<dyn IncrementalHost>,
        false,
    );
    compile_times.borrow_mut().changes_compute_time = sys
        .now()
        .duration_since(changes_compute_start)
        .unwrap_or_default();

    let written_build_info: Arc<Mutex<Option<String>>> = Arc::new(Mutex::new(None));
    let write_file = new_task_write_file(
        resolved.get_build_info_file_name(),
        written_build_info.clone(),
    );
    // PORT: Go keeps the statistics in the task result for the build
    // aggregate (buildtask.go:233). The worker result does not carry them,
    // and the aggregate report is unported (see orchestrator.rs).
    let (result, _statistics) = emit_and_report_statistics(&EmitInput {
        sys: &*sys,
        program_like: &program,
        config: Some(&resolved),
        report_diagnostic,
        report_error_summary: quiet_diagnostics_reporter(),
        writer: writer.clone(),
        write_file: Some(write_file),
        compile_times,
    });

    let output = String::from_utf8_lossy(&builder.borrow()).into_owned();
    let build_info_file_name = written_build_info
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clone();
    WorkerCompileResult {
        exit_status: result.status,
        output,
        diagnostics_count: result.diagnostics.len(),
        emitted_files: result.emit_result.emitted_files.clone(),
        has_changed_dts_file: program.has_changed_dts_file(),
        build_info_file_name,
        fs_cache: host.cached_fs.state_excluding(&[fs_cache, &program_fs_cache]),
    }
}

// Go: build/buildtask.go:785 (*BuildTask).writeFile
// PORT: emit runs on the checker threads, so the callback must be `Send`
// and cannot hold the `Rc` file system. Go writes through
// `orchestrator.host.FS()` (cachedvfs over bundled over osvfs); both
// wrappers pass a write of a real path to osvfs, so this writes with the
// osvfs of the calling thread.
// PORT: Go tests `data.BuildInfo != nil`. The Rust `WriteFileData` has no
// build info field. Go sets it only for the write of
// `config.GetBuildInfoFileName()` (incremental/program.go emitBuildInfo),
// so the file name is compared instead. The worker has no task, so the
// `onBuildInfoEmit` call is recorded as the written file name and runs in
// the orchestrator. The `storeOutputTimeStamp` branch is watch only.
fn new_task_write_file(
    build_info_file_name: String,
    written_build_info: Arc<Mutex<Option<String>>>,
) -> WriteFile {
    Arc::new(
        move |file_name: &str, text: &str, _data: &mut WriteFileData| -> Result<(), String> {
            match osvfs_fs().write_file(file_name, text) {
                Ok(()) => {
                    if !build_info_file_name.is_empty() && file_name == build_info_file_name {
                        *written_build_info
                            .lock()
                            .unwrap_or_else(std::sync::PoisonError::into_inner) =
                            Some(file_name.to_string());
                    }
                    Ok(())
                }
                Err(err) => Err(fs_error_text(&err)),
            }
        },
    )
}

/// Go `err.Error()` of a vfs error.
fn fs_error_text(err: &FsError) -> String {
    match err {
        FsError::Path { op, path, err } => format!("{op} {path}: {err}"),
        FsError::Other(message) => message.clone(),
        other => format!("{other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Protocol
// ---------------------------------------------------------------------------

impl MarshalerTo for WorkerCompileResult {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        enc.push_str("{\"exitStatus\":");
        enc.push_str(&self.exit_status.code().to_string());
        enc.push_str(",\"output\":");
        self.output.marshal_json_to(enc)?;
        enc.push_str(",\"diagnosticsCount\":");
        enc.push_str(&self.diagnostics_count.to_string());
        enc.push_str(",\"emittedFiles\":");
        self.emitted_files.marshal_json_to(enc)?;
        enc.push_str(",\"hasChangedDtsFile\":");
        self.has_changed_dts_file.marshal_json_to(enc)?;
        enc.push_str(",\"buildInfoFileName\":");
        match &self.build_info_file_name {
            Some(name) => name.marshal_json_to(enc)?,
            None => enc.push_str("null"),
        }
        enc.push_str(",\"fsCache\":");
        marshal_cached_fs_state(&self.fs_cache, enc)?;
        enc.push('}');
        Ok(())
    }
}

/// The protocol line for `result` (no trailing newline).
pub fn marshal_worker_compile_result(result: &WorkerCompileResult) -> String {
    json_marshal(result, &[]).expect("worker result marshals")
}

/// Reads a protocol line back. `None` when the line is not a valid result.
pub fn parse_worker_compile_result(line: &str) -> Option<WorkerCompileResult> {
    let mut dec = json_new_decoder(line.as_bytes());
    let result = decode_worker_compile_result(&mut dec).ok()?;
    dec.check_eof().ok()?;
    Some(result)
}

fn decode_worker_compile_result(
    dec: &mut JsonDecoder<'_>,
) -> Result<WorkerCompileResult, JsonError> {
    let invalid = || JsonError {
        message: "invalid build worker result".to_string(),
    };
    let mut result = WorkerCompileResult {
        exit_status: ExitStatus::Success,
        output: String::new(),
        diagnostics_count: 0,
        emitted_files: Vec::new(),
        has_changed_dts_file: false,
        build_info_file_name: None,
        fs_cache: CachedFsState::default(),
    };
    if dec.read_token()? != JsonToken::BeginObject {
        return Err(invalid());
    }
    while dec.peek_kind() != b'}' {
        let mut key = String::new();
        json_unmarshal_decode(dec, &mut key)?;
        match key.as_str() {
            "exitStatus" => {
                let mut code = 0.0f64;
                json_unmarshal_decode(dec, &mut code)?;
                result.exit_status = ExitStatus::from_code(code as i32).ok_or_else(invalid)?;
            }
            "output" => json_unmarshal_decode(dec, &mut result.output)?,
            "diagnosticsCount" => {
                let mut count = 0.0f64;
                json_unmarshal_decode(dec, &mut count)?;
                result.diagnostics_count = count as usize;
            }
            "emittedFiles" => {
                if dec.read_token()? != JsonToken::BeginArray {
                    return Err(invalid());
                }
                while dec.peek_kind() != b']' {
                    let mut file = String::new();
                    json_unmarshal_decode(dec, &mut file)?;
                    result.emitted_files.push(file);
                }
                dec.read_token()?;
            }
            "hasChangedDtsFile" => json_unmarshal_decode(dec, &mut result.has_changed_dts_file)?,
            "buildInfoFileName" => {
                if dec.peek_kind() == b'n' {
                    dec.read_token()?;
                    result.build_info_file_name = None;
                } else {
                    let mut name = String::new();
                    json_unmarshal_decode(dec, &mut name)?;
                    result.build_info_file_name = Some(name);
                }
            }
            "fsCache" => result.fs_cache = decode_cached_fs_state(dec)?,
            _ => dec.skip_value()?,
        }
    }
    dec.read_token()?;
    Ok(result)
}

// ---------------------------------------------------------------------------
// Orchestrator side
// ---------------------------------------------------------------------------

/// Starts build workers. It is `Send`, so the orchestrator can wait for
/// several workers on helper threads (Go runs tasks on goroutines).
#[derive(Clone, Debug)]
pub struct WorkerLauncher {
    /// The build binary.
    pub exe: std::path::PathBuf,
    /// The orchestrator's full `-b` command line, passed on to each worker.
    pub build_command_line: Vec<String>,
}

impl WorkerLauncher {
    /// A launcher that re-runs the current executable.
    pub fn current(build_command_line: Vec<String>) -> WorkerLauncher {
        WorkerLauncher {
            exe: std::env::current_exe().expect("current executable path"),
            build_command_line,
        }
    }

    /// Runs one worker for `config` and waits for its result. `fs_cache` is
    /// the orchestrator's cached file system as JSON (shared_fs.rs); the
    /// worker reads it from stdin. `on_program_fs_cache` gets the worker's
    /// `fsCacheProgram` line while the worker still runs.
    // PORT: a worker that fails (unported code, a panic, or no result line)
    // has no Go equivalent. Its stderr already shows the reason; the task
    // gets `ExitStatus::NotImplemented` and the worker's stdout as output,
    // so the build goes on. The failure is counted as unported, so the
    // process exits with `EXIT_UNPORTED`.
    pub fn run(
        &self,
        config: &str,
        fs_cache: &str,
        on_program_fs_cache: &mut dyn FnMut(CachedFsState),
    ) -> WorkerCompileResult {
        let output = std::process::Command::new(&self.exe)
            .arg(BUILD_WORKER_FLAG)
            .arg(config)
            .args(&self.build_command_line)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::inherit())
            .spawn()
            .and_then(|mut child| {
                // The worker reads all of stdin before it writes to stdout,
                // so writing first cannot block on a full stdout pipe. A
                // worker that exits early closes stdin; its status reports
                // that, so the write error is ignored.
                if let Some(mut stdin) = child.stdin.take() {
                    use std::io::Write;
                    let _ = stdin.write_all(fs_cache.as_bytes());
                }
                // Read stdout line by line so the program line arrives
                // while the worker still checks and emits.
                let mut stdout = Vec::new();
                if let Some(pipe) = child.stdout.take() {
                    use std::io::BufRead;
                    let mut reader = std::io::BufReader::new(pipe);
                    loop {
                        let start = stdout.len();
                        if reader.read_until(b'\n', &mut stdout)? == 0 {
                            break;
                        }
                        if let Some(state) = parse_worker_program_fs_cache(&stdout[start..]) {
                            on_program_fs_cache(state);
                            stdout.truncate(start);
                        }
                    }
                }
                let status = child.wait()?;
                Ok(std::process::Output {
                    status,
                    stdout,
                    stderr: Vec::new(),
                })
            });
        let failed = |message: String, output: String| {
            eprintln!("goport_build: build worker for {config} failed: {message}");
            crate::core::record_unported("build worker");
            WorkerCompileResult {
                exit_status: ExitStatus::NotImplemented,
                output,
                diagnostics_count: 0,
                emitted_files: Vec::new(),
                has_changed_dts_file: false,
                build_info_file_name: None,
                fs_cache: CachedFsState::default(),
            }
        };
        let output = match output {
            Ok(output) => output,
            Err(err) => return failed(err.to_string(), String::new()),
        };
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let last_line = stdout.lines().rev().find(|line| !line.trim().is_empty());
        match last_line.and_then(parse_worker_compile_result) {
            Some(result) if output.status.success() => result,
            // The worker finished but reached unported code (its stderr
            // lists it). Keep the result and mark this process too.
            Some(result) if output.status.code() == Some(EXIT_UNPORTED) => {
                crate::core::record_unported("build worker");
                result
            }
            _ => failed(format!("{}", output.status), stdout),
        }
    }
}

/// Reads the cached file system that the orchestrator sends on stdin (see
/// `WorkerLauncher::run`). Empty input (or a terminal) is an empty cache.
pub fn read_worker_fs_cache(input: &mut dyn std::io::Read) -> Result<CachedFsState, String> {
    let mut bytes = Vec::new();
    input
        .read_to_end(&mut bytes)
        .map_err(|err| err.to_string())?;
    if bytes.iter().all(u8::is_ascii_whitespace) {
        return Ok(CachedFsState::default());
    }
    let mut dec = json_new_decoder(&bytes);
    let state = decode_cached_fs_state(&mut dec).map_err(|err| err.message)?;
    dec.check_eof().map_err(|err| err.message)?;
    Ok(state)
}

const PROGRAM_FS_CACHE_PREFIX: &str = "{\"fsCacheProgram\":";

/// The worker's `fsCacheProgram` line (no trailing newline).
pub fn marshal_worker_program_fs_cache(state: &CachedFsState) -> String {
    let mut text = PROGRAM_FS_CACHE_PREFIX.to_string();
    marshal_cached_fs_state(state, &mut text).expect("file system cache marshals");
    text.push('}');
    text
}

/// Reads a `fsCacheProgram` line back. `None` for any other line.
fn parse_worker_program_fs_cache(line: &[u8]) -> Option<CachedFsState> {
    if !line.starts_with(PROGRAM_FS_CACHE_PREFIX.as_bytes()) {
        return None;
    }
    let mut dec = json_new_decoder(line);
    let mut state = None;
    if dec.read_token().ok()? != JsonToken::BeginObject {
        return None;
    }
    while dec.peek_kind() != b'}' {
        let mut key = String::new();
        json_unmarshal_decode(&mut dec, &mut key).ok()?;
        if key == "fsCacheProgram" {
            state = Some(decode_cached_fs_state(&mut dec).ok()?);
        } else {
            dec.skip_value().ok()?;
        }
    }
    dec.read_token().ok()?;
    dec.check_eof().ok()?;
    state
}

/// The orchestrator's cached file system as worker input (shared_fs.rs).
pub fn marshal_worker_fs_cache(state: &CachedFsState) -> String {
    let mut text = String::new();
    marshal_cached_fs_state(state, &mut text).expect("file system cache marshals");
    text
}
