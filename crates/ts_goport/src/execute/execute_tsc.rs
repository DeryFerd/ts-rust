//! Go: execute/tsc.go, the `tsc` command line: `CommandLine`,
//! `tscBuildCompilation`, `tscCompilation`, `findConfigFile`,
//! `getTraceFromSys`, `performIncrementalCompilation`, `performCompilation`
//! and `showConfig`. `startTracingIfNeeded` and `stopTracing` write the
//! warnings of the process session in `crate::tracing`.
//!
//! Every bin runs this code. `tsgo` runs it as Go does (`GoTsc`).
//! `goport` and `goport_emit` pass their own `TscCompilationHooks`.
//! `goport_build` runs `tsc_build_compilation`.
//!
//! PORT: Go `ctx` is only used by watch mode and the build orchestrator,
//! which take none in the port, and Go `testing` is nil outside Go tests,
//! so both are dropped (see compile.rs).
//!
//! PORT: the program state is process-wide, so Go `compiler.NewProgram` is
//! `crate::program::install_new_program`, as in build/worker.rs (see
//! PORTING.md "Program"). Call `tsc_compilation` once per process, on the
//! thread that should own the program and the checker pool. Go catches no
//! panic here; the bins guard unported code.

use crate::frontend::prelude::*;

use std::sync::Arc;
use std::time::SystemTime;

use crate::emitter::program_emit::{WriteFile, WriteFileData};
use crate::execute::build::command_line::parse_build_command_line;
use crate::execute::build::host::TscExtendedConfigCache;
use crate::execute::build::orchestrator::{Options as OrchestratorOptions, new_orchestrator};
use crate::execute::build::worker::{SystemParseConfigHost, WorkerLauncher};
use crate::execute::incremental::emit_files::fs_error_text;
use crate::execute::incremental::incremental::{create_host, new_build_info_reader};
use crate::execute::incremental::program::{
    new_program as new_incremental_program, read_build_info_program,
};
use crate::execute::tsc::{
    CommandLineResult, CompileTimes, CompilerProgram, DiagnosticReporter, DiagnosticsReporter,
    EmitInput, ExitStatus, ProgramLike, System, create_diagnostic_reporter,
    create_report_error_summary, emit_and_report_statistics, get_trace_with_writer_from_sys,
    print_build_help, print_help, print_version, write_config_file, write_str,
};
use crate::frontend::json::json_marshal_indent_write;
use crate::frontend::tsoptions::convert_to_ts_config;

/// The bin part of the compile step of `tscCompilation`.
// PORT: no Go equivalent. Go has one `tsc`. `tsgo` uses the defaults
// (`GoTsc`). `goport` and `goport_emit` run on read-only project inputs,
// so they change the config, guard each program step and write only where
// they allow.
pub trait TscCompilationHooks {
    /// Whether a `-b` command line runs Go `tscBuildCompilation`. When
    /// false, it is `unported!`: the build writes outputs, and its workers
    /// re-run the bin.
    fn build_mode(&self) -> bool {
        true
    }

    /// Runs after the command line parse, before `tscCompilation` reads the
    /// result. The bin may edit it. The default keeps it as parsed.
    fn command_line_parsed(&self, _command_line: &mut ParsedCommandLine) {}

    /// Runs when the compile step starts, after the init, version, help and
    /// showConfig branches, before the compiler host and `NewProgram`.
    /// `config` is the config for the compilation, and the bin may edit
    /// it. `config_file_name` is "" when there is no config file. An `Err`
    /// ends the run with that status.
    fn prepare_compilation(
        &self,
        _sys: &dyn System,
        _command_line_options: &CompilerOptions,
        _config_file_name: &str,
        _config: &mut ParsedCommandLine,
    ) -> Result<(), ExitStatus> {
        Ok(())
    }

    /// Runs after `NewProgram`, before `EmitAndReportStatistics`. An `Err`
    /// ends the run with that status.
    fn program_created(&self) -> Result<(), ExitStatus> {
        Ok(())
    }

    /// The Go `ProgramLike` that `EmitAndReportStatistics` gets. `None` is
    /// Go's: the program, or for an incremental config the
    /// `incremental.Program`. `Some` replaces both, and then the
    /// incremental compile does not call `incremental.ReadBuildInfoProgram`
    /// or `incremental.NewProgram`, so it reads and writes no build info.
    fn program_like(&self) -> Option<&dyn ProgramLike> {
        None
    }

    /// The Go host `WriteFile` for the emit. `None` is the emit host
    /// default, which refuses every write (program.rs emitHost
    /// `write_file`).
    fn write_file(&self) -> Option<WriteFile>;
}

/// Go `tsc`: no bin step, the Go program, and emit writes through the OS
/// file system. `tsgo` runs this.
pub struct GoTsc;

impl TscCompilationHooks for GoTsc {
    fn write_file(&self) -> Option<WriteFile> {
        Some(os_write_file())
    }
}

/// `sys.Now().Sub(start)`.
fn since(sys: &dyn System, start: SystemTime) -> std::time::Duration {
    sys.now().duration_since(start).unwrap_or_default()
}

/// `tsc.CommandLineResult{Status: status}`.
fn result(status: ExitStatus) -> CommandLineResult {
    CommandLineResult {
        status,
        watcher: None,
    }
}

// Go: execute/tsc.go:27 startTracingIfNeeded, the warning part. The session
// is the process session in `crate::tracing`.
fn start_tracing_if_needed(sys: &dyn System, config: &ParsedCommandLine) {
    if let Some(warning) = crate::tracing::start_tracing_if_needed(config, false) {
        write_str(&sys.writer(), &warning);
    }
}

// Go: execute/tsc.go:43 stopTracing
fn stop_tracing(sys: &dyn System) {
    if let Some(warning) = crate::tracing::stop_tracing() {
        write_str(&sys.writer(), &warning);
    }
}

// Go: execute/tsc.go:52 CommandLine
// PORT: Go parses the build command line here and passes it on; the port
// passes the arguments, because the build workers get the same command line
// (see `tsc_build_compilation`). `hooks.build_mode` and
// `hooks.command_line_parsed` are the bin's steps (not in Go).
pub fn command_line(
    sys: Rc<dyn System>,
    command_line_args: &[String],
    hooks: &dyn TscCompilationHooks,
) -> CommandLineResult {
    if let Some(first) = command_line_args.first() {
        match first.to_lowercase().as_str() {
            "-b" | "--b" | "-build" | "--build" => {
                if !hooks.build_mode() {
                    unported!("tscBuildCompilation");
                }
                return tsc_build_compilation(sys, command_line_args);
            }
            // case "-f":
            // 	return fmtMain(sys, commandLineArgs[1], commandLineArgs[1])
            _ => {}
        }
    }

    let mut parsed = parse_command_line(command_line_args, &SystemParseConfigHost(&*sys));
    hooks.command_line_parsed(&mut parsed);
    tsc_compilation(sys, parsed, hooks)
}

// Go: execute/tsc.go:65 fmtMain
// PORT: not ported. Its only call (the `-f` case in `CommandLine`) is
// commented out in Go, so it is dead code, and the formatter is not ported.

// Go: execute/tsc.go:90 tscBuildCompilation
// PORT: Go `CommandLine` parses the build command line and passes it in;
// here it is the first step, which runs in the same order.
// `command_line_args` is the full command line (Go `commandLineArgs`),
// which the build workers get too (build/worker.rs).
pub fn tsc_build_compilation(
    sys: Rc<dyn System>,
    command_line_args: &[String],
) -> CommandLineResult {
    let build_command = parse_build_command_line(command_line_args, &SystemParseConfigHost(&*sys));
    let locale = build_command.locale();
    let report_diagnostic = create_diagnostic_reporter(
        &*sys,
        sys.writer(),
        &locale,
        &build_command.compiler_options,
    );

    if !build_command.errors.is_empty() {
        for err in &build_command.errors {
            report_diagnostic(err);
        }
        return result(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }

    // PORT: Go `defer profileSession.Stop()`. The session stops when it
    // drops at the end of this function (see `crate::pprof`).
    let _profile_session = if build_command.compiler_options.pprof_dir.is_empty() {
        None
    } else {
        // !!! stderr?
        Some(crate::pprof::begin_profiling(
            &build_command.compiler_options.pprof_dir,
            sys.writer(),
        ))
    };

    if build_command.compiler_options.help.is_true() {
        print_version(&*sys, &locale);
        print_build_help(&*sys, &locale, BUILD_OPTS.as_slice());
        return result(ExitStatus::Success);
    }

    let mut orchestrator = new_orchestrator(OrchestratorOptions {
        sys,
        command: Rc::new(build_command),
        worker: WorkerLauncher::current(command_line_args.to_vec()),
    });
    orchestrator.start()
}

// Go: execute/tsc.go:121 tscCompilation
// PORT: `hooks.prepare_compilation` is the bin's step (not in Go).
pub fn tsc_compilation(
    sys: Rc<dyn System>,
    command_line: ParsedCommandLine,
    hooks: &dyn TscCompilationHooks,
) -> CommandLineResult {
    let mut config_file_name = String::new();
    let locale = command_line.locale();
    let mut report_diagnostic: DiagnosticReporter = create_diagnostic_reporter(
        &*sys,
        sys.writer(),
        &locale,
        command_line.compiler_options(),
    );

    if !command_line.errors.is_empty() {
        for e in &command_line.errors {
            report_diagnostic(e);
        }
        return result(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }

    // PORT: Go `defer profileSession.Stop()`. The session stops when it
    // drops at the end of this function (see `crate::pprof`).
    let _profile_session = if command_line.compiler_options().pprof_dir.is_empty() {
        None
    } else {
        // !!! stderr?
        Some(crate::pprof::begin_profiling(
            &command_line.compiler_options().pprof_dir,
            sys.writer(),
        ))
    };

    if command_line.compiler_options().init.is_true() {
        // Go: `commandLine.Raw.(*collections.OrderedMap[string, any])`, a
        // type assertion that panics on another type. `parse_command_line`
        // always stores a map.
        let CompilerOptionsValue::Map(raw) = &command_line.raw else {
            panic!(
                "interface conversion: commandLine.Raw is not *collections.OrderedMap[string,any]"
            );
        };
        write_config_file(&*sys, &locale, &report_diagnostic, raw);
        return result(ExitStatus::Success);
    }

    if command_line.compiler_options().version.is_true() {
        print_version(&*sys, &locale);
        return result(ExitStatus::Success);
    }

    if command_line.compiler_options().help.is_true()
        || command_line.compiler_options().all.is_true()
    {
        print_help(&*sys, &locale, &command_line);
        return result(ExitStatus::Success);
    }

    if command_line.compiler_options().watch.is_true()
        && command_line.compiler_options().list_files_only.is_true()
    {
        report_diagnostic(&new_compiler_diagnostic(
            diag::Options_0_and_1_cannot_be_combined,
            args!["watch", "listFilesOnly"],
        ));
        return result(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }

    if !command_line.compiler_options().project.is_empty() {
        if !command_line.file_names().is_empty() {
            report_diagnostic(&new_compiler_diagnostic(
                diag::Option_project_cannot_be_mixed_with_source_files_on_a_command_line,
                Vec::new(),
            ));
            return result(ExitStatus::DiagnosticsPresentOutputsSkipped);
        }

        let file_or_directory = normalize_path(&command_line.compiler_options().project);
        if sys.fs().directory_exists(&file_or_directory) {
            config_file_name = combine_paths(&file_or_directory, &["tsconfig.json"]);
            if !sys.fs().file_exists(&config_file_name) {
                report_diagnostic(&new_compiler_diagnostic(
                    diag::Cannot_find_a_tsconfig_json_file_at_the_current_directory_Colon_0,
                    args![config_file_name],
                ));
                return result(ExitStatus::DiagnosticsPresentOutputsSkipped);
            }
        } else {
            config_file_name = file_or_directory.clone();
            if !sys.fs().file_exists(&config_file_name) {
                report_diagnostic(&new_compiler_diagnostic(
                    diag::The_specified_path_does_not_exist_Colon_0,
                    args![file_or_directory],
                ));
                return result(ExitStatus::DiagnosticsPresentOutputsSkipped);
            }
        }
    } else if !command_line.compiler_options().ignore_config.is_true()
        || command_line.file_names().is_empty()
    {
        let search_path = normalize_path(&sys.get_current_directory());
        let fs = sys.fs();
        config_file_name =
            find_config_file(&search_path, |name| fs.file_exists(name), "tsconfig.json");
        if !command_line.file_names().is_empty() {
            if !config_file_name.is_empty() {
                // Error to not specify config file
                report_diagnostic(&new_compiler_diagnostic(
                    diag::X_tsconfig_json_is_present_but_will_not_be_loaded_if_files_are_specified_on_commandline_Use_ignoreConfig_to_skip_this_error,
                    Vec::new(),
                ));
                return result(ExitStatus::DiagnosticsPresentOutputsSkipped);
            }
        } else if config_file_name.is_empty() {
            if command_line.compiler_options().show_config.is_true() {
                report_diagnostic(&new_compiler_diagnostic(
                    diag::Cannot_find_a_tsconfig_json_file_at_the_current_directory_Colon_0,
                    args![normalize_path(&sys.get_current_directory())],
                ));
            } else {
                print_version(&*sys, &locale);
                print_help(&*sys, &locale, &command_line);
            }
            return result(ExitStatus::DiagnosticsPresentOutputsSkipped);
        }
    }

    // !!! convert to options with absolute paths is usually done here, but for ease of implementation, it's done in `tsoptions.ParseCommandLine()`
    let compiler_options_from_command_line = command_line.compiler_options().clone();
    let extended_config_cache = Rc::new(TscExtendedConfigCache::default());
    // PORT: Go `*tsc.CompileTimes` is shared with the emit result (see
    // `CompileAndEmitResult.times`).
    let compile_times = Rc::new(RefCell::new(CompileTimes::default()));
    let mut command_line_raw: Option<IndexMap<String, CompilerOptionsValue>> = None;
    let mut config_for_compilation = if !config_file_name.is_empty() {
        let config_start = sys.now();
        if let CompilerOptionsValue::Map(raw) = &command_line.raw {
            // Wrap command line options in a "compilerOptions" key to match tsconfig.json structure
            let mut wrapped = IndexMap::new();
            wrapped.insert(
                "compilerOptions".to_string(),
                CompilerOptionsValue::Map(raw.clone()),
            );
            command_line_raw = Some(wrapped);
        }
        let extended_config_cache_ref: &dyn ExtendedConfigCache = &*extended_config_cache;
        let (config_parse_result, errors) = get_parsed_command_line_of_config_file(
            &config_file_name,
            Some(&*compiler_options_from_command_line),
            command_line_raw.as_ref(),
            &SystemParseConfigHost(&*sys),
            Some(extended_config_cache_ref),
        );
        compile_times.borrow_mut().config_time = since(&*sys, config_start);
        if !errors.is_empty() {
            // these are unrecoverable errors--exit to report them as diagnostics
            for e in &errors {
                report_diagnostic(e);
            }
            return result(ExitStatus::DiagnosticsPresentOutputsGenerated);
        }
        // Updater to reflect pretty
        report_diagnostic = create_diagnostic_reporter(
            &*sys,
            sys.writer(),
            &locale,
            command_line.compiler_options(),
        );
        // PORT: Go returns a non-nil config whenever there are no errors.
        config_parse_result
            .expect("GetParsedCommandLineOfConfigFile returns a config without errors")
    } else {
        command_line
    };

    let report_error_summary: DiagnosticsReporter = create_report_error_summary(
        &*sys,
        &locale,
        Some(&**config_for_compilation.compiler_options()),
    );
    if compiler_options_from_command_line.show_config.is_true() {
        show_config(&*sys, &config_for_compilation, &config_file_name);
        return result(ExitStatus::Success);
    }
    // PORT: the compile step of the bin starts here (see
    // `TscCompilationHooks::prepare_compilation`). `goport` forces noEmit
    // here, so `--showConfig` above shows the options as Go does.
    if let Err(status) = hooks.prepare_compilation(
        &*sys,
        &compiler_options_from_command_line,
        &config_file_name,
        &mut config_for_compilation,
    ) {
        return result(status);
    }
    if config_for_compilation.compiler_options().watch.is_true() {
        return create_watcher(
            sys,
            Rc::new(config_for_compilation),
            compiler_options_from_command_line,
            command_line_raw,
            report_diagnostic,
            report_error_summary,
        );
    } else if config_for_compilation.compiler_options().is_incremental() {
        return perform_incremental_compilation(
            &*sys,
            config_for_compilation,
            report_diagnostic,
            report_error_summary,
            extended_config_cache,
            compile_times,
            hooks,
        );
    }
    perform_compilation(
        &*sys,
        config_for_compilation,
        report_diagnostic,
        report_error_summary,
        extended_config_cache,
        compile_times,
        hooks,
    )
}

// Go: execute/tsc.go:233 createWatcher(...) + watcher.start(ctx), and the
// `CommandLineResult{Status: ExitStatusSuccess, Watcher: watcher}` return.
// PORT: watch mode (Go execute/watcher.go) belongs to the watch track,
// which is still porting it. This is the one place it plugs in: that track
// replaces the body with Go `createWatcher`, `watcher.start` and the
// result above. The parameters are Go's, without `testing`.
fn create_watcher(
    sys: Rc<dyn System>,
    config_parse_result: Rc<ParsedCommandLine>,
    compiler_options_from_command_line: Rc<CompilerOptions>,
    command_line_raw: Option<IndexMap<String, CompilerOptionsValue>>,
    report_diagnostic: DiagnosticReporter,
    report_error_summary: DiagnosticsReporter,
) -> CommandLineResult {
    unported!("createWatcher");
}

// Go: execute/tsc.go:266 findConfigFile
fn find_config_file(
    search_path: &str,
    file_exists: impl Fn(&str) -> bool,
    config_name: &str,
) -> String {
    let (result, ok) = for_each_ancestor_directory(search_path, |ancestor| {
        let full_config_name = combine_paths(ancestor, &[config_name]);
        if file_exists(full_config_name.as_str()) {
            return (full_config_name, true);
        }
        (full_config_name, false)
    });
    if !ok {
        return String::new();
    }
    result
}

// Go: execute/tsc.go:280 getTraceFromSys
fn get_trace_from_sys(sys: &dyn System, locale: crate::locale::Locale) -> TraceFn {
    get_trace_with_writer_from_sys(sys.writer(), locale)
}

/// Go `compiler.NewProgram(compiler.ProgramOptions{Config, Host, Tracing})`.
// PORT: the new program is installed for the process (see the module
// comment). Go `NewProgram` cannot fail; the Rust install fails only when
// the current directory cannot be read, and that ends the run.
fn install_program(host: Rc<dyn CompilerHost>, config: Rc<ParsedCommandLine>) {
    if let Err(message) = crate::program::install_new_program(ProgramOptions {
        host,
        config,
        use_source_of_project_reference: false,
        single_threaded: Tristate::Unknown,
        typings_location: String::new(),
        project_name: String::new(),
    }) {
        panic!("cannot load program: {message}");
    }
}

// Go: execute/tsc.go:284 performIncrementalCompilation
// PORT: the incremental program reads back the installed program. A bin
// that replaces the program (`TscCompilationHooks::program_like`) skips
// `incremental.ReadBuildInfoProgram` and `incremental.NewProgram`: `goport`
// and `goport_emit` run on read-only Query inputs, which are composite and
// incremental, and the Go incremental program would write build info next
// to them. Their steps are still timed (empty), so the statistics table
// has the same rows as Go. `testing.OnProgram` is a test hook.
fn perform_incremental_compilation(
    sys: &dyn System,
    config: ParsedCommandLine,
    report_diagnostic: DiagnosticReporter,
    report_error_summary: DiagnosticsReporter,
    extended_config_cache: Rc<TscExtendedConfigCache>,
    compile_times: Rc<RefCell<CompileTimes>>,
    hooks: &dyn TscCompilationHooks,
) -> CommandLineResult {
    let host = new_cached_fs_compiler_host(
        &sys.get_current_directory(),
        sys.fs(),
        &sys.default_library_path(),
        Some(extended_config_cache as Rc<dyn ExtendedConfigCache>),
        Some(get_trace_from_sys(sys, config.locale())),
    );
    let config = Rc::new(config);
    let replacement = hooks.program_like();
    let build_info_read_start = sys.now();
    let old_program = match replacement {
        Some(_) => None,
        None => read_build_info_program(&config, &*new_build_info_reader(host.clone()), &*host),
    };
    compile_times.borrow_mut().build_info_read_time = since(sys, build_info_read_start);

    start_tracing_if_needed(sys, &config);

    let parse_start = sys.now();
    install_program(host.clone(), config.clone());
    compile_times.borrow_mut().parse_time = since(sys, parse_start);
    let changes_compute_start = sys.now();
    let incremental_program = match replacement {
        Some(_) => None,
        None => Some(new_incremental_program(
            old_program.as_ref(),
            create_host(host),
            false,
        )),
    };
    compile_times.borrow_mut().changes_compute_time = since(sys, changes_compute_start);
    // PORT: the bin check after NewProgram (see `TscCompilationHooks`).
    if let Err(status) = hooks.program_created() {
        stop_tracing(sys);
        return result(status);
    }
    let program_like: &dyn ProgramLike = match &incremental_program {
        Some(incremental_program) => incremental_program,
        None => replacement.expect("a bin without an incremental program replaces it"),
    };
    let (emit_result, _) = emit_and_report_statistics(&EmitInput {
        sys,
        program_like,
        config: Some(&*config),
        report_diagnostic,
        report_error_summary,
        writer: sys.writer(),
        write_file: hooks.write_file(),
        compile_times,
    });

    stop_tracing(sys);

    result(emit_result.status)
}

// Go: execute/tsc.go:333 performCompilation
fn perform_compilation(
    sys: &dyn System,
    config: ParsedCommandLine,
    report_diagnostic: DiagnosticReporter,
    report_error_summary: DiagnosticsReporter,
    extended_config_cache: Rc<TscExtendedConfigCache>,
    compile_times: Rc<RefCell<CompileTimes>>,
    hooks: &dyn TscCompilationHooks,
) -> CommandLineResult {
    let host = new_cached_fs_compiler_host(
        &sys.get_current_directory(),
        sys.fs(),
        &sys.default_library_path(),
        Some(extended_config_cache as Rc<dyn ExtendedConfigCache>),
        Some(get_trace_from_sys(sys, config.locale())),
    );
    let config = Rc::new(config);

    start_tracing_if_needed(sys, &config);

    let parse_start = sys.now();
    install_program(host, config.clone());
    compile_times.borrow_mut().parse_time = since(sys, parse_start);
    // PORT: the bin check after NewProgram (see `TscCompilationHooks`).
    if let Err(status) = hooks.program_created() {
        stop_tracing(sys);
        return result(status);
    }
    let (emit_result, _) = emit_and_report_statistics(&EmitInput {
        sys,
        program_like: hooks.program_like().unwrap_or(&CompilerProgram),
        config: Some(&*config),
        report_diagnostic,
        report_error_summary,
        writer: sys.writer(),
        write_file: hooks.write_file(),
        compile_times,
    });

    stop_tracing(sys);

    result(emit_result.status)
}

// Go: execute/tsc.go:373 showConfig
fn show_config(sys: &dyn System, config: &ParsedCommandLine, config_file_name: &str) {
    let ts_config = convert_to_ts_config(config, config_file_name);
    let writer = sys.writer();
    let _ = json_marshal_indent_write(&mut *writer.borrow_mut(), &ts_config, "", "    ");
}

// PORT: added for `GoTsc`. Go passes no `WriteFile`, so `emitHost.WriteFile`
// (compiler/emitHost.go:120) writes through `program.Host().FS()`
// (cachedvfs over bundled over osvfs). The port's emit host refuses a
// write without a callback (program.rs emitHost `write_file`), and emit
// runs on the checker threads, so the callback must be `Send` and cannot
// hold the `Rc` file system. Both wrappers pass a write of a real path to
// osvfs (cachedvfs.go:148 WriteFile), so this writes with the osvfs of the
// calling thread, like `new_task_write_file` in build/worker.rs without the
// build info tracking. There is no outDir or input guard: tsgo writes next
// to the sources or into outDir, as Go does.
fn os_write_file() -> WriteFile {
    Arc::new(
        |file_name: &str, text: &str, _data: &mut WriteFileData| -> Result<(), String> {
            osvfs_fs()
                .write_file(file_name, text)
                .map_err(|err| fs_error_text(&err))
        },
    )
}
