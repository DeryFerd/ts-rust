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
//! Go tasks use the orchestrator's `Sys`. The worker's system gives the
//! orchestrator's answers where a worker process differs (see
//! `WorkerSystem`); the launcher passes them in the environment.
//!
//! Protocol (stdout, one line, compact JSON):
//! `{"exitStatus":0,"output":"...","diagnostics":[[code,category,
//!   fileName | null,pos,end,[args...]]...],"diagnosticFileTexts":
//!   [[fileName,text]...],"emittedFiles":[...],
//!   "hasChangedDtsFile":false,"buildInfoFileName":"..." | null,
//!   "statistics":{...} | null,
//!   "outputTimeStamps":[["<file>",<unix seconds>,<nanoseconds>],...],
//!   "fsCache":{...}}`
//! Before it, right after the program is made, the worker writes one
//! `{"fsCacheProgram":{...}}` line: the cached file system entries the
//! program load added. The worker writes nothing else to stdout. On stdin
//! the orchestrator sends the build's cached file system (see
//! shared_fs.rs); `fsCache` is what the worker added after the program
//! line. Traces and diagnostics go to
//! `output`. Unported code and panics are reported on stderr, which the
//! worker shares with the orchestrator. After a Go panic
//! (`core::go_panic`) the worker prints it on stderr and exits
//! `core::EXIT_GO_PANIC` with no result line.

use crate::core::EXIT_GO_PANIC;
use crate::emitter::program_emit::{WriteFile, WriteFileData};
use crate::execute::build::build_task::{WorkerCompileResult, WorkerDiagnostic};
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
use crate::execute::tsc::statistics::decode_statistics;
use crate::frontend::prelude::*;
use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// The first argument that selects the worker entry of the build binary.
pub const BUILD_WORKER_FLAG: &str = "--build-worker";

/// The orchestrator's `WriteOutputIsTTY` for a worker: "1" or "0".
const WORKER_TTY_ENV: &str = "GOPORT_BUILD_WORKER_TTY";
/// The orchestrator's `SinceStart` when it started a worker, in nanoseconds.
const WORKER_SINCE_START_ENV: &str = "GOPORT_BUILD_WORKER_SINCE_START_NS";

// PORT: Go tasks use the orchestrator's `Sys`. A worker process differs in
// two answers. Its stdout is a pipe to the orchestrator, so its own
// `WriteOutputIsTTY` is false when the orchestrator's is true, and the
// default `--pretty` would differ. Its `SinceStart` counts from the worker
// start, not the build start, so the project's statistics "Total time"
// would differ. This system gives the orchestrator's answers, which
// `WorkerLauncher::run` passes in the environment, and passes everything
// else to the worker's own system. Without them (a worker started by
// hand), the output is not a TTY and the build starts with the worker.
struct WorkerSystem {
    sys: Rc<dyn System>,
    write_output_is_tty: bool,
    since_start_at_launch: Duration,
}

impl WorkerSystem {
    fn new(sys: Rc<dyn System>) -> WorkerSystem {
        let write_output_is_tty = sys.get_environment_variable(WORKER_TTY_ENV) == "1";
        let since_start_at_launch = sys
            .get_environment_variable(WORKER_SINCE_START_ENV)
            .parse()
            .map(Duration::from_nanos)
            .unwrap_or_default();
        WorkerSystem {
            sys,
            write_output_is_tty,
            since_start_at_launch,
        }
    }
}

impl System for WorkerSystem {
    fn writer(&self) -> Writer {
        self.sys.writer()
    }
    fn fs(&self) -> Rc<dyn Fs> {
        self.sys.fs()
    }
    fn default_library_path(&self) -> String {
        self.sys.default_library_path()
    }
    fn get_current_directory(&self) -> String {
        self.sys.get_current_directory()
    }
    fn write_output_is_tty(&self) -> bool {
        self.write_output_is_tty
    }
    fn get_width_of_terminal(&self) -> i32 {
        self.sys.get_width_of_terminal()
    }
    fn get_environment_variable(&self, name: &str) -> String {
        self.sys.get_environment_variable(name)
    }
    fn now(&self) -> SystemTime {
        self.sys.now()
    }
    fn since_start(&self) -> Duration {
        self.since_start_at_launch + self.sys.since_start()
    }
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
// no task, so the reported diagnostics go back in the result
// (`worker_diagnostics`) and the orchestrator appends them (build_task.rs
// `compile_and_emit_finish`). `sys` is the worker's own system; it is
// wrapped in `WorkerSystem`.
pub fn compile_and_emit_worker(
    sys: Rc<dyn System>,
    config: &str,
    build_command_line: &[String],
    fs_cache: &CachedFsState,
    report_program_fs_cache: &mut dyn FnMut(&CachedFsState),
) -> WorkerCompileResult {
    let sys: Rc<dyn System> = Rc::new(WorkerSystem::new(sys));
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
    let report_diagnostic = create_diagnostic_reporter(
        &*sys,
        writer.clone(),
        &command.locale(),
        &command.compiler_options,
    );

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
        trace: get_trace_with_writer_from_sys(writer.clone(), command.locale()),
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
    // Go: build/buildtask.go:779 (*BuildTask).storeOutputTimeStamp
    let store_output_time_stamp =
        command.compiler_options.watch.is_true() && !resolved.compiler_options().is_incremental();
    let output_time_stamps: Arc<Mutex<Vec<(String, SystemTime)>>> =
        Arc::new(Mutex::new(Vec::new()));
    let write_file = new_task_write_file(
        resolved.get_build_info_file_name(),
        written_build_info.clone(),
        store_output_time_stamp,
        output_time_stamps.clone(),
    );
    // Go keeps the statistics in the task result for the build aggregate
    // (buildtask.go:233); they go back in the worker result.
    let (result, statistics) = emit_and_report_statistics(&EmitInput {
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
    let (diagnostics, diagnostic_file_texts) = worker_diagnostics(&result.diagnostics);
    let output_time_stamps = std::mem::take(
        &mut *output_time_stamps
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner),
    );
    WorkerCompileResult {
        exit_status: result.status,
        output,
        diagnostics,
        diagnostic_file_texts,
        emitted_files: result.emit_result.emitted_files.clone(),
        has_changed_dts_file: program.has_changed_dts_file(),
        build_info_file_name,
        statistics,
        output_time_stamps,
        fs_cache: host
            .cached_fs
            .state_excluding(&[fs_cache, &program_fs_cache]),
    }
}

// The worker result form of `result.Diagnostics` (see `WorkerDiagnostic`),
// and the name and text of each file that they name, in first use order.
fn worker_diagnostics(
    diagnostics: &[Diagnostic],
) -> (Vec<WorkerDiagnostic>, Vec<(String, String)>) {
    let mut file_texts: Vec<(String, String)> = Vec::new();
    let mut seen: FxHashSet<&'static str> = FxHashSet::default();
    let diagnostics = diagnostics
        .iter()
        .map(|diagnostic| {
            let file_name = if diagnostic.file.is_nil() {
                None
            } else {
                let file_name = source_file_file_name(diagnostic.file);
                if seen.insert(file_name) {
                    file_texts.push((
                        file_name.to_string(),
                        source_file_text(diagnostic.file).to_string(),
                    ));
                }
                Some(file_name.to_string())
            };
            WorkerDiagnostic {
                file_name,
                pos: diagnostic.pos,
                end: diagnostic.end,
                code: diagnostic.code,
                category: diagnostic.category,
                message_args: diagnostic.message_args.clone(),
            }
        })
        .collect();
    (diagnostics, file_texts)
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
// the orchestrator. The `storeOutputTimeStamp` branch (watch mode) is
// recorded in `output_time_stamps`, and the orchestrator stores the times
// (`BuildTask::compile_and_emit_finish`).
fn new_task_write_file(
    build_info_file_name: String,
    written_build_info: Arc<Mutex<Option<String>>>,
    store_output_time_stamp: bool,
    output_time_stamps: Arc<Mutex<Vec<(String, SystemTime)>>>,
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
                    } else if store_output_time_stamp {
                        // Store time stamps
                        // PORT: Go `orchestrator.opts.Sys.Now()`. The
                        // callback runs on a checker thread and cannot hold
                        // the `Rc` system; the OS system's `Now` is
                        // `SystemTime::now`.
                        output_time_stamps
                            .lock()
                            .unwrap_or_else(std::sync::PoisonError::into_inner)
                            .push((file_name.to_string(), SystemTime::now()));
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
        // PORT: the protocol keeps each string in the port form (see
        // `scanner_util::GO_STRING_MARKER`, `json_new_port_form_decoder`).
        // The parent writes the output's Go bytes.
        append_json_quote_port_form(enc, &self.output);
        enc.push_str(",\"diagnostics\":");
        self.diagnostics.marshal_json_to(enc)?;
        enc.push_str(",\"diagnosticFileTexts\":[");
        for (i, (file_name, text)) in self.diagnostic_file_texts.iter().enumerate() {
            if i > 0 {
                enc.push(',');
            }
            enc.push('[');
            append_json_quote_port_form(enc, file_name);
            enc.push(',');
            append_json_quote_port_form(enc, text);
            enc.push(']');
        }
        enc.push(']');
        enc.push_str(",\"emittedFiles\":");
        append_json_quote_port_form_list(enc, &self.emitted_files);
        enc.push_str(",\"hasChangedDtsFile\":");
        self.has_changed_dts_file.marshal_json_to(enc)?;
        enc.push_str(",\"buildInfoFileName\":");
        match &self.build_info_file_name {
            Some(name) => append_json_quote_port_form(enc, name),
            None => enc.push_str("null"),
        }
        enc.push_str(",\"statistics\":");
        match &self.statistics {
            Some(statistics) => statistics.marshal_json_to(enc)?,
            None => enc.push_str("null"),
        }
        enc.push_str(",\"outputTimeStamps\":[");
        for (i, (file_name, m_time)) in self.output_time_stamps.iter().enumerate() {
            if i > 0 {
                enc.push(',');
            }
            let since_epoch = m_time.duration_since(UNIX_EPOCH).unwrap_or_default();
            enc.push('[');
            file_name.marshal_json_to(enc)?;
            enc.push(',');
            enc.push_str(&since_epoch.as_secs().to_string());
            enc.push(',');
            enc.push_str(&since_epoch.subsec_nanos().to_string());
            enc.push(']');
        }
        enc.push(']');
        enc.push_str(",\"fsCache\":");
        marshal_cached_fs_state(&self.fs_cache, enc)?;
        enc.push('}');
        Ok(())
    }
}

// `[code,category,fileName|null,pos,end,[args...]]`. The category is the Go
// value (0 warning, 1 error, 2 suggestion, 3 message). The strings keep the
// port form (see `WorkerCompileResult`).
impl MarshalerTo for WorkerDiagnostic {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        enc.push('[');
        enc.push_str(&self.code.to_string());
        enc.push(',');
        enc.push_str(&(self.category as u8).to_string());
        enc.push(',');
        match &self.file_name {
            Some(file_name) => append_json_quote_port_form(enc, file_name),
            None => enc.push_str("null"),
        }
        enc.push(',');
        enc.push_str(&self.pos.to_string());
        enc.push(',');
        enc.push_str(&self.end.to_string());
        enc.push(',');
        append_json_quote_port_form_list(enc, &self.message_args);
        enc.push(']');
        Ok(())
    }
}

fn decode_worker_diagnostic(dec: &mut JsonDecoder<'_>) -> Result<WorkerDiagnostic, JsonError> {
    let invalid = || JsonError {
        message: "invalid build worker diagnostic".to_string(),
    };
    fn number(dec: &mut JsonDecoder<'_>) -> Result<i32, JsonError> {
        let mut value = 0.0f64;
        json_unmarshal_decode(dec, &mut value)?;
        Ok(value as i32)
    }
    if dec.read_token()? != JsonToken::BeginArray {
        return Err(invalid());
    }
    let code = number(dec)?;
    let category = match number(dec)? {
        0 => ts_diagnostics::Category::Warning,
        1 => ts_diagnostics::Category::Error,
        2 => ts_diagnostics::Category::Suggestion,
        3 => ts_diagnostics::Category::Message,
        _ => return Err(invalid()),
    };
    let file_name = if dec.peek_kind() == b'n' {
        dec.read_token()?;
        None
    } else {
        let mut file_name = String::new();
        json_unmarshal_decode(dec, &mut file_name)?;
        Some(file_name)
    };
    let pos = number(dec)?;
    let end = number(dec)?;
    if dec.read_token()? != JsonToken::BeginArray {
        return Err(invalid());
    }
    let mut message_args = Vec::new();
    while dec.peek_kind() != b']' {
        let mut arg = String::new();
        json_unmarshal_decode(dec, &mut arg)?;
        message_args.push(arg);
    }
    dec.read_token()?;
    if dec.read_token()? != JsonToken::EndArray {
        return Err(invalid());
    }
    Ok(WorkerDiagnostic {
        file_name,
        pos,
        end,
        code,
        category,
        message_args,
    })
}

/// The protocol line for `result` (no trailing newline).
pub fn marshal_worker_compile_result(result: &WorkerCompileResult) -> String {
    json_marshal(result, &[]).expect("worker result marshals")
}

/// Reads a protocol line back. `None` when the line is not a valid result.
pub fn parse_worker_compile_result(line: &str) -> Option<WorkerCompileResult> {
    let mut dec = json_new_port_form_decoder(line.as_bytes());
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
        diagnostics: Vec::new(),
        diagnostic_file_texts: Vec::new(),
        emitted_files: Vec::new(),
        has_changed_dts_file: false,
        build_info_file_name: None,
        statistics: None,
        output_time_stamps: Vec::new(),
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
            "diagnostics" => {
                if dec.read_token()? != JsonToken::BeginArray {
                    return Err(invalid());
                }
                while dec.peek_kind() != b']' {
                    result.diagnostics.push(decode_worker_diagnostic(dec)?);
                }
                dec.read_token()?;
            }
            "diagnosticFileTexts" => {
                if dec.read_token()? != JsonToken::BeginArray {
                    return Err(invalid());
                }
                while dec.peek_kind() != b']' {
                    if dec.read_token()? != JsonToken::BeginArray {
                        return Err(invalid());
                    }
                    let mut file_name = String::new();
                    json_unmarshal_decode(dec, &mut file_name)?;
                    let mut text = String::new();
                    json_unmarshal_decode(dec, &mut text)?;
                    if dec.read_token()? != JsonToken::EndArray {
                        return Err(invalid());
                    }
                    result.diagnostic_file_texts.push((file_name, text));
                }
                dec.read_token()?;
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
            "statistics" => {
                if dec.peek_kind() == b'n' {
                    dec.read_token()?;
                    result.statistics = None;
                } else {
                    result.statistics = Some(decode_statistics(dec)?);
                }
            }
            "outputTimeStamps" => {
                if dec.read_token()? != JsonToken::BeginArray {
                    return Err(invalid());
                }
                while dec.peek_kind() != b']' {
                    if dec.read_token()? != JsonToken::BeginArray {
                        return Err(invalid());
                    }
                    let mut file_name = String::new();
                    json_unmarshal_decode(dec, &mut file_name)?;
                    let mut seconds = 0.0f64;
                    json_unmarshal_decode(dec, &mut seconds)?;
                    let mut nanoseconds = 0.0f64;
                    json_unmarshal_decode(dec, &mut nanoseconds)?;
                    if dec.read_token()? != JsonToken::EndArray {
                        return Err(invalid());
                    }
                    let m_time = UNIX_EPOCH + Duration::new(seconds as u64, nanoseconds as u32);
                    result.output_time_stamps.push((file_name, m_time));
                }
                dec.read_token()?;
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
    /// The orchestrator's `WriteOutputIsTTY` (see `WorkerSystem`).
    pub write_output_is_tty: bool,
    /// The orchestrator's start, for its `SinceStart` (see `WorkerSystem`).
    pub start: std::time::Instant,
}

impl WorkerLauncher {
    /// A launcher that re-runs the current executable.
    // PORT: `tsc_build_compilation` makes the launcher without its system.
    // The answers are the ones of the `OsSystem` that the build binary
    // uses: `WriteOutputIsTTY` is whether stdout is a terminal (Go
    // cmd/tsgo/sys.go:51), and the start is now, right after the binary
    // made its system and parsed the command line.
    pub fn current(build_command_line: Vec<String>) -> WorkerLauncher {
        use std::io::IsTerminal;
        WorkerLauncher {
            exe: std::env::current_exe().expect("current executable path"),
            build_command_line,
            write_output_is_tty: std::io::stdout().is_terminal(),
            start: std::time::Instant::now(),
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
    // A worker that exits `EXIT_GO_PANIC` with no result line hit a Go panic
    // (`core::go_panic`) and printed it. Go panics in the build task
    // goroutine, which ends the process, so this ends the process too: the
    // output so far stays, the task never reports, and the exit code is the
    // Go runtime one. PORT: other running workers are not stopped.
    pub fn run(
        &self,
        config: &str,
        fs_cache: &str,
        on_program_fs_cache: &mut dyn FnMut(CachedFsState),
    ) -> WorkerCompileResult {
        let output = std::process::Command::new(&self.exe)
            .arg(BUILD_WORKER_FLAG)
            // The worker reads its arguments into the port form again.
            .arg(os_path(config).as_os_str())
            .args(
                self.build_command_line
                    .iter()
                    .map(|arg| os_path(arg).into_owned()),
            )
            .env(
                WORKER_TTY_ENV,
                if self.write_output_is_tty { "1" } else { "0" },
            )
            .env(
                WORKER_SINCE_START_ENV,
                self.start.elapsed().as_nanos().to_string(),
            )
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
            use std::io::Write;
            let bin = self
                .exe
                .file_name()
                .map_or_else(|| "goport".into(), |name| name.to_string_lossy());
            // `config` is the port form of a Go string: print its Go bytes.
            let text = format!("{bin}: build worker for {config} failed: {message}\n");
            let _ = std::io::stderr().write_all(&crate::scanner_util::go_string_bytes(&text));
            crate::core::record_unported("build worker");
            WorkerCompileResult {
                exit_status: ExitStatus::NotImplemented,
                output,
                diagnostics: Vec::new(),
                diagnostic_file_texts: Vec::new(),
                emitted_files: Vec::new(),
                has_changed_dts_file: false,
                build_info_file_name: None,
                statistics: None,
                output_time_stamps: Vec::new(),
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
            None if output.status.code() == Some(EXIT_GO_PANIC) => exit_after_go_panic(),
            _ => failed(format!("{}", output.status), stdout),
        }
    }
}

/// Ends the process after a build worker's Go panic (see
/// `WorkerLauncher::run`): flushes stdout, prints the unported counts, and
/// exits `EXIT_GO_PANIC`, or `EXIT_UNPORTED` when this process reached
/// unported code.
fn exit_after_go_panic() -> ! {
    use std::io::Write;
    let _ = std::io::stdout().flush();
    let unported = crate::core::unported_report();
    for (name, count) in &unported {
        eprintln!("unported: {name} {count}");
    }
    std::process::exit(if unported.is_empty() {
        EXIT_GO_PANIC
    } else {
        EXIT_UNPORTED
    });
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
    let mut dec = json_new_port_form_decoder(&bytes);
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
    let mut dec = json_new_port_form_decoder(line);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn worker_result_diagnostics_round_trip() {
        let result = WorkerCompileResult {
            exit_status: ExitStatus::DiagnosticsPresentOutputsGenerated,
            output: String::new(),
            diagnostics: vec![
                WorkerDiagnostic {
                    file_name: Some("/p/a.ts".to_string()),
                    pos: 4,
                    end: 5,
                    code: 2322,
                    category: ts_diagnostics::Category::Error,
                    // An invalid byte unit and a real U+FDD0 keep their
                    // port form (see `scanner_util::GO_STRING_MARKER`).
                    message_args: vec![
                        "\u{FDD0}\u{10F7FE}x".to_string(),
                        "\u{FDD0}\u{FDD0}".to_string(),
                    ],
                },
                WorkerDiagnostic {
                    file_name: None,
                    pos: 0,
                    end: 0,
                    code: 18003,
                    category: ts_diagnostics::Category::Error,
                    message_args: Vec::new(),
                },
            ],
            diagnostic_file_texts: vec![(
                "/p/a.ts".to_string(),
                "let x: number =\n  \"\u{FDD0}\u{10F7FF}\";\n".to_string(),
            )],
            emitted_files: Vec::new(),
            has_changed_dts_file: false,
            build_info_file_name: None,
            statistics: None,
            output_time_stamps: Vec::new(),
            fs_cache: CachedFsState::default(),
        };
        let line = marshal_worker_compile_result(&result);
        let back = parse_worker_compile_result(&line).expect("the result line parses");
        assert_eq!(back.diagnostics.len(), 2);
        assert_eq!(back.diagnostics[1].file_name, None);
        assert_eq!(
            back.diagnostics[0].message_args,
            result.diagnostics[0].message_args
        );
        assert_eq!(back.diagnostic_file_texts, result.diagnostic_file_texts);
        assert_eq!(marshal_worker_compile_result(&back), line);
    }
}
