use std::{
    collections::BTreeSet,
    env, fs, io,
    path::{Path, PathBuf},
    process::ExitCode,
};

use ts_cli::{
    BuildOptions, Command, CompilerOptions as CliOptions, ExitStatus, VERSION, expand_command_line,
    parse_command_line,
};
use ts_compiler::{Program, ProgramDiagnostic, ProgramOptionsOverride};
use ts_diagnostic_writer::{
    Diagnostic, DiagnosticCategory, FormattingOptions, format_diagnostic_with_related,
    format_diagnostics,
};
use ts_module::ResolutionOptions;
use ts_project::{CompiledProject, ProjectDiagnostic, build_projects, load_project_graph};
use ts_scanner::Scanner;
use ts_vfs::{FileSystem, OsFileSystem, normalize_path};
use ts_watch::{
    CompileCycle, Coordinator, FsEventSource, WatchCompiler, WatchError, WatchMode, WatchPath,
    watch_paths_for_program,
};

fn main() -> ExitCode {
    let args: Vec<_> = env::args().skip(1).collect();
    if args
        .first()
        .is_some_and(|argument| argument == "--tokenize")
    {
        return tokenize(args.get(1));
    }
    if args.first().is_some_and(|argument| argument == "--parse") {
        return parse(args.get(1));
    }
    if args
        .first()
        .is_some_and(|argument| argument == "--compile-dev")
    {
        return compile_development(&args[1..]);
    }
    if args
        .first()
        .is_some_and(|argument| argument == "--check-canonical")
    {
        return check_canonical_project(&args[1..]);
    }
    let expanded = expand_command_line(&args, read_response_file);
    let quiet = expanded
        .as_ref()
        .map_or_else(|_| quiet_requested(&args), |args| quiet_requested(args));
    match expanded.and_then(|arguments| parse_command_line(&arguments, read_response_file)) {
        Ok(Command::Version) => {
            println!("Version {VERSION}");
            ExitCode::SUCCESS
        }
        Ok(Command::Build(options)) if options.help => {
            print_help();
            ExitCode::SUCCESS
        }
        Ok(Command::Build(options)) if options.clean => clean(&options),
        Ok(Command::Build(options)) if options.watch => watch_build(options),
        Ok(Command::Build(options)) => build(&options),
        Ok(Command::Help) => {
            print_help();
            if args.is_empty() {
                ExitCode::from(ExitStatus::DiagnosticsPresentOutputsSkipped as u8)
            } else {
                ExitCode::SUCCESS
            }
        }
        Ok(Command::Lsp) => run_lsp(),
        Ok(Command::Compile(options)) if options.watch => watch_compile(*options),
        Ok(Command::Compile(options)) => compile(&options),
        Err(error) => {
            if !quiet {
                println!("{}", error.render());
            }
            ExitCode::from(ExitStatus::DiagnosticsPresentOutputsSkipped as u8)
        }
    }
}

fn read_response_file(path: &Path) -> io::Result<String> {
    OsFileSystem::default().read_file(&path.to_string_lossy())
}

fn quiet_requested(args: &[String]) -> bool {
    args.iter()
        .enumerate()
        .filter(|(_, argument)| {
            argument.eq_ignore_ascii_case("--quiet") || argument.eq_ignore_ascii_case("-q")
        })
        .fold(false, |_, (index, _)| {
            !args
                .get(index + 1)
                .is_some_and(|value| value.eq_ignore_ascii_case("false"))
        })
}

fn build_project_roots(options: &BuildOptions) -> Vec<String> {
    if options.projects.is_empty() {
        vec!["tsconfig.json".to_owned()]
    } else {
        options.projects.clone()
    }
}

fn build(options: &BuildOptions) -> ExitCode {
    let Ok(current_directory) = env::current_dir() else {
        eprintln!("error: could not determine the current directory");
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    };
    let current_directory_text = current_directory.to_string_lossy();
    let roots = build_project_roots(options);
    let file_system = OsFileSystem::default();
    if options.dry {
        return dry_build(file_system, &current_directory_text, &roots, options);
    }
    let overrides = ProgramOptionsOverride {
        no_check: options.no_check,
        no_emit: options.no_emit.then_some(true),
        ..ProgramOptionsOverride::default()
    };
    let mut result = build_projects(
        &file_system,
        &current_directory_text,
        &roots,
        overrides,
        options.incremental,
    );
    if options.force && result.graph.diagnostics.is_empty() {
        if let Err(error) =
            invalidate_project_build_info(file_system, &current_directory_text, &roots, overrides)
        {
            eprintln!("{error}");
            return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
        }
        result = build_projects(
            &file_system,
            &current_directory_text,
            &roots,
            overrides,
            options.incremental,
        );
    }
    let pretty = options.pretty.unwrap_or(false);
    print_project_diagnostics(
        &result.graph.diagnostics,
        &current_directory_text,
        pretty,
        options.quiet,
    );
    if !result.graph.diagnostics.is_empty() {
        return if result.graph.has_cycle {
            exit(ExitStatus::ProjectReferenceCycleOutputsSkipped)
        } else {
            exit(ExitStatus::DiagnosticsPresentOutputsSkipped)
        };
    }

    let mut had_diagnostics = false;
    let mut generated_output = false;
    for project in result.projects {
        let CompiledProject {
            program,
            emit,
            build_info,
            ..
        } = project;
        print_diagnostics(
            &program,
            program.diagnostics(),
            &current_directory_text,
            pretty,
            options.quiet,
        );
        print_diagnostics(
            &program,
            &emit.diagnostics,
            &current_directory_text,
            pretty,
            options.quiet,
        );
        had_diagnostics |= !program.diagnostics().is_empty() || !emit.diagnostics.is_empty();
        for output in emit.files {
            if let Err(error) = write_output(&output.file_name, output.text) {
                eprintln!("{error}");
                return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
            }
            if options.list_emitted_files {
                println!("TSFILE:  {}", output.file_name);
            }
            generated_output = true;
        }
        if let Some(build_info) = build_info {
            if let Err(error) = write_output(&build_info.file_name, build_info.text) {
                eprintln!("{error}");
                return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
            }
            if options.list_emitted_files {
                println!("TSFILE:  {}", build_info.file_name);
            }
        }
        if options.list_files {
            print_source_files(&program);
        }
    }
    diagnostic_exit(had_diagnostics, generated_output)
}

fn dry_build(
    file_system: OsFileSystem,
    current_directory: &str,
    roots: &[String],
    options: &BuildOptions,
) -> ExitCode {
    let graph = load_project_graph(&file_system, current_directory, roots);
    print_project_diagnostics(
        &graph.diagnostics,
        current_directory,
        options.pretty.unwrap_or(false),
        options.quiet,
    );
    if !graph.diagnostics.is_empty() {
        return if graph.has_cycle {
            exit(ExitStatus::ProjectReferenceCycleOutputsSkipped)
        } else {
            exit(ExitStatus::DiagnosticsPresentOutputsSkipped)
        };
    }
    if !options.quiet {
        for project in graph.projects {
            println!("A non-dry build would build project '{project}'");
        }
    }
    ExitCode::SUCCESS
}

fn clean(options: &BuildOptions) -> ExitCode {
    let Ok(current_directory) = env::current_dir() else {
        eprintln!("error: could not determine the current directory");
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    };
    let current_directory_text = current_directory.to_string_lossy();
    let roots = build_project_roots(options);
    let file_system = OsFileSystem::default();
    let graph = load_project_graph(&file_system, &current_directory_text, &roots);
    print_project_diagnostics(
        &graph.diagnostics,
        &current_directory_text,
        options.pretty.unwrap_or(false),
        options.quiet,
    );
    if !graph.diagnostics.is_empty() {
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }

    let mut outputs = Vec::new();
    let mut inputs = BTreeSet::new();
    for config_path in graph.projects {
        let program = Program::from_config_with_options(
            &file_system,
            &config_path,
            ProgramOptionsOverride {
                no_check: Some(true),
                no_emit: Some(false),
                ..ProgramOptionsOverride::default()
            },
        );
        inputs.extend(
            program
                .source_files()
                .iter()
                .map(|source| file_system.realpath(&source.file_name)),
        );
        outputs.extend(
            program
                .emit()
                .files
                .into_iter()
                .map(|output| PathBuf::from(output.file_name)),
        );
        outputs.push(project_build_info_path(&program, &config_path));
    }

    for path in outputs
        .into_iter()
        .filter(|path| path.is_file())
        .filter(|path| !inputs.contains(&file_system.realpath(&path.to_string_lossy())))
    {
        if options.dry {
            if !options.quiet {
                println!("A non-dry build would delete '{}'", path.display());
            }
            continue;
        }
        if let Err(error) = fs::remove_file(&path) {
            eprintln!("error: could not remove '{}': {error}", path.display());
            return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
        }
    }
    ExitCode::SUCCESS
}

fn compile(options: &CliOptions) -> ExitCode {
    let Ok(current_directory) = env::current_dir() else {
        eprintln!("error: could not determine the current directory");
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    };
    let pretty = options.pretty.unwrap_or(false);
    if options.project.is_some() && !options.files.is_empty() {
        print_command_line_diagnostic(
            5042,
            "Option 'project' cannot be mixed with source files on a command line.",
            &current_directory,
            pretty,
            options.quiet,
        );
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }

    let discovered_config = (!options.ignore_config)
        .then(|| find_config_file(&current_directory))
        .flatten();
    if !options.files.is_empty() && options.project.is_none() && discovered_config.is_some() {
        print_command_line_diagnostic(
            5112,
            "tsconfig.json is present but will not be loaded if files are specified on commandline. Use '--ignoreConfig' to skip this error.",
            &current_directory,
            pretty,
            options.quiet,
        );
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }

    let project_path = if let Some(project) = options.project.as_deref() {
        match resolve_project_path(&current_directory, project, pretty, options.quiet) {
            Ok(path) => Some(path),
            Err(status) => return status,
        }
    } else {
        discovered_config
    };
    if options.files.is_empty() && project_path.is_none() {
        print_help();
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }

    let current_directory_text = current_directory.to_string_lossy();
    let program = compiler_program(
        OsFileSystem::default(),
        &current_directory_text,
        options,
        project_path.as_deref(),
    );

    print_diagnostics(
        &program,
        program.diagnostics(),
        &current_directory_text,
        pretty,
        options.quiet,
    );
    if options.list_files_only {
        print_source_files(&program);
        return diagnostic_exit(!program.diagnostics().is_empty(), false);
    }
    let emitted = program.emit();
    print_diagnostics(
        &program,
        &emitted.diagnostics,
        &current_directory_text,
        pretty,
        options.quiet,
    );
    let had_diagnostics = !program.diagnostics().is_empty() || !emitted.diagnostics.is_empty();
    let mut generated_output = false;
    for output in emitted.files {
        if let Err(error) = write_output(&output.file_name, output.text) {
            eprintln!("{error}");
            return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
        }
        if options.list_emitted_files {
            println!("TSFILE:  {}", output.file_name);
        }
        generated_output = true;
    }
    if options.list_files {
        print_source_files(&program);
    }
    diagnostic_exit(had_diagnostics, generated_output)
}

fn compiler_program(
    file_system: OsFileSystem,
    current_directory: &str,
    options: &CliOptions,
    project_path: Option<&Path>,
) -> Program {
    if let Some(config_path) = project_path {
        return Program::from_config_with_command_line_options(
            &file_system,
            &config_path.to_string_lossy(),
            compiler_options_overrides(options),
            &options.compiler_options,
            &options.specified_options,
        );
    }

    let mut compiler_options = options.compiler_options.clone();
    if options.list_files_only {
        compiler_options.no_check = true;
        compiler_options.no_emit = true;
    }
    Program::new_with_options(
        &file_system,
        current_directory,
        &options.files,
        compiler_options,
    )
}

fn compiler_options_overrides(options: &CliOptions) -> ProgramOptionsOverride {
    ProgramOptionsOverride {
        no_check: (options.no_check || options.list_files_only).then_some(true),
        no_emit: (options.no_emit || options.list_files_only).then_some(true),
        no_lib: options.no_lib.then_some(true),
    }
}

struct FileWatchCompiler {
    options: CliOptions,
    current_directory: PathBuf,
    project_path: Option<PathBuf>,
}

impl WatchCompiler for FileWatchCompiler {
    fn compile(&mut self) -> Result<CompileCycle, WatchError> {
        let current_directory = self.current_directory.to_string_lossy();
        let program = compiler_program(
            OsFileSystem::default(),
            &current_directory,
            &self.options,
            self.project_path.as_deref(),
        );
        let pretty = self.options.pretty.unwrap_or(false);
        print_diagnostics(
            &program,
            program.diagnostics(),
            &current_directory,
            pretty,
            self.options.quiet,
        );
        let emitted = program.emit();
        print_diagnostics(
            &program,
            &emitted.diagnostics,
            &current_directory,
            pretty,
            self.options.quiet,
        );
        let error_count = program.diagnostics().len() + emitted.diagnostics.len();
        for output in emitted.files {
            write_output(&output.file_name, output.text).map_err(WatchError::Compile)?;
        }
        Ok(CompileCycle {
            error_count,
            watch_paths: watch_paths_for_program(
                &program,
                &self.current_directory,
                self.project_path.as_deref(),
                &self.options.files,
            ),
        })
    }
}

fn watch_compile(options: CliOptions) -> ExitCode {
    let Ok(current_directory) = env::current_dir() else {
        eprintln!("error: could not determine the current directory");
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    };
    if options.project.is_some() && !options.files.is_empty() {
        print_command_line_diagnostic(
            5042,
            "Option 'project' cannot be mixed with source files on a command line.",
            &current_directory,
            options.pretty.unwrap_or(false),
            options.quiet,
        );
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }
    let discovered_config = (!options.ignore_config)
        .then(|| find_config_file(&current_directory))
        .flatten();
    if !options.files.is_empty() && options.project.is_none() && discovered_config.is_some() {
        print_command_line_diagnostic(
            5112,
            "tsconfig.json is present but will not be loaded if files are specified on commandline. Use '--ignoreConfig' to skip this error.",
            &current_directory,
            options.pretty.unwrap_or(false),
            options.quiet,
        );
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }
    let project_path = if let Some(project) = options.project.as_deref() {
        match resolve_project_path(
            &current_directory,
            project,
            options.pretty.unwrap_or(false),
            options.quiet,
        ) {
            Ok(path) => Some(path),
            Err(status) => return status,
        }
    } else {
        discovered_config
    };
    if options.files.is_empty() && project_path.is_none() {
        print_help();
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }
    let compiler = FileWatchCompiler {
        options,
        current_directory,
        project_path,
    };
    run_watch(compiler)
}

struct BuildWatchCompiler {
    options: BuildOptions,
    current_directory: PathBuf,
    roots: Vec<String>,
}

impl WatchCompiler for BuildWatchCompiler {
    fn compile(&mut self) -> Result<CompileCycle, WatchError> {
        let file_system = OsFileSystem::default();
        let current_directory = self.current_directory.to_string_lossy();
        let overrides = ProgramOptionsOverride {
            no_check: self.options.no_check,
            no_emit: self.options.no_emit.then_some(true),
            ..ProgramOptionsOverride::default()
        };
        let mut result = build_projects(
            &file_system,
            &current_directory,
            &self.roots,
            overrides,
            self.options.incremental,
        );
        if self.options.force && result.graph.diagnostics.is_empty() {
            invalidate_project_build_info(file_system, &current_directory, &self.roots, overrides)
                .map_err(WatchError::Compile)?;
            self.options.force = false;
            result = build_projects(
                &file_system,
                &current_directory,
                &self.roots,
                overrides,
                self.options.incremental,
            );
        }
        let pretty = self.options.pretty.unwrap_or(false);
        print_project_diagnostics(
            &result.graph.diagnostics,
            &current_directory,
            pretty,
            self.options.quiet,
        );
        let mut error_count = result.graph.diagnostics.len();
        let mut watch_paths = vec![WatchPath::new(
            self.current_directory.clone(),
            WatchMode::NonRecursive,
        )];
        for config_path in &result.skipped {
            let program = Program::from_config_with_options(&file_system, config_path, overrides);
            watch_paths.extend(watch_paths_for_program(
                &program,
                &self.current_directory,
                Some(Path::new(config_path)),
                &[],
            ));
        }
        for CompiledProject {
            config_path,
            program,
            emit,
            build_info,
            ..
        } in result.projects
        {
            print_diagnostics(
                &program,
                program.diagnostics(),
                &current_directory,
                pretty,
                self.options.quiet,
            );
            print_diagnostics(
                &program,
                &emit.diagnostics,
                &current_directory,
                pretty,
                self.options.quiet,
            );
            error_count += program.diagnostics().len() + emit.diagnostics.len();
            watch_paths.extend(watch_paths_for_program(
                &program,
                &self.current_directory,
                Some(Path::new(&config_path)),
                &[],
            ));
            for output in emit.files {
                write_output(&output.file_name, output.text).map_err(WatchError::Compile)?;
            }
            if let Some(build_info) = build_info {
                write_output(&build_info.file_name, build_info.text)
                    .map_err(WatchError::Compile)?;
            }
        }
        watch_paths.sort_by(|left, right| left.directory.cmp(&right.directory));
        watch_paths.dedup_by(|left, right| left.directory == right.directory);
        Ok(CompileCycle {
            error_count,
            watch_paths,
        })
    }
}

fn watch_build(options: BuildOptions) -> ExitCode {
    let Ok(current_directory) = env::current_dir() else {
        eprintln!("error: could not determine the current directory");
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    };
    let roots = build_project_roots(&options);
    run_watch(BuildWatchCompiler {
        options,
        current_directory,
        roots,
    })
}

fn run_watch(compiler: impl WatchCompiler) -> ExitCode {
    let reporter = |status: ts_watch::WatchStatus| println!("{}", status.message());
    let mut coordinator = Coordinator::new(compiler, FsEventSource::default(), reporter);
    match coordinator.run() {
        Ok(summary) if summary.last_error_count == 0 => ExitCode::SUCCESS,
        Ok(_) => exit(ExitStatus::DiagnosticsPresentOutputsSkipped),
        Err(error) => {
            eprintln!("error: {error}");
            exit(ExitStatus::DiagnosticsPresentOutputsSkipped)
        }
    }
}

fn diagnostic_exit(had_diagnostics: bool, generated_output: bool) -> ExitCode {
    if had_diagnostics {
        if generated_output {
            exit(ExitStatus::DiagnosticsPresentOutputsGenerated)
        } else {
            exit(ExitStatus::DiagnosticsPresentOutputsSkipped)
        }
    } else {
        ExitCode::SUCCESS
    }
}

fn write_output(file_name: &str, text: String) -> Result<(), String> {
    let output_path = Path::new(file_name);
    if let Some(parent) = output_path.parent()
        && !parent.as_os_str().is_empty()
    {
        fs::create_dir_all(parent)
            .map_err(|error| format!("error: could not create '{}': {error}", parent.display()))?;
    }
    fs::write(output_path, text)
        .map_err(|error| format!("error: could not write '{file_name}': {error}"))
}

fn find_config_file(start: &Path) -> Option<PathBuf> {
    start
        .ancestors()
        .map(|directory| directory.join("tsconfig.json"))
        .find(|path| path.is_file())
}

fn resolve_project_path(
    current_directory: &Path,
    project: &str,
    pretty: bool,
    quiet: bool,
) -> Result<PathBuf, ExitCode> {
    let path = PathBuf::from(normalize_path(
        &current_directory.join(project).to_string_lossy(),
    ));
    if path.is_dir() {
        let config_path = path.join("tsconfig.json");
        if config_path.is_file() {
            return Ok(config_path);
        }
        print_command_line_diagnostic(
            5081,
            &format!(
                "Cannot find a tsconfig.json file at the current directory: {}.",
                config_path.display()
            ),
            current_directory,
            pretty,
            quiet,
        );
    } else if path.is_file() {
        return Ok(path);
    } else {
        print_command_line_diagnostic(
            5058,
            &format!("The specified path does not exist: '{}'.", path.display()),
            current_directory,
            pretty,
            quiet,
        );
    }
    Err(exit(ExitStatus::DiagnosticsPresentOutputsSkipped))
}

fn invalidate_project_build_info(
    file_system: OsFileSystem,
    current_directory: &str,
    roots: &[String],
    overrides: ProgramOptionsOverride,
) -> Result<(), String> {
    let graph = load_project_graph(&file_system, current_directory, roots);
    let mut inputs = BTreeSet::new();
    let mut build_info_paths = Vec::new();
    for config_path in graph.projects {
        let program = Program::from_config_with_options(&file_system, &config_path, overrides);
        inputs.extend(
            program
                .source_files()
                .iter()
                .map(|source| file_system.realpath(&source.file_name)),
        );
        build_info_paths.push(project_build_info_path(&program, &config_path));
    }
    for build_info_path in build_info_paths
        .into_iter()
        .filter(|path| !inputs.contains(&file_system.realpath(&path.to_string_lossy())))
    {
        if let Err(error) = fs::remove_file(&build_info_path)
            && error.kind() != io::ErrorKind::NotFound
        {
            return Err(format!(
                "error: could not remove '{}': {error}",
                build_info_path.display()
            ));
        }
    }
    Ok(())
}

fn project_build_info_path(program: &Program, config_path: &str) -> PathBuf {
    PathBuf::from(ts_project::project_build_info_path(
        &OsFileSystem::default(),
        program,
        config_path,
    ))
}

fn print_source_files(program: &Program) {
    for source_file in program.source_files() {
        println!("{}", source_file.file_name);
    }
}

fn print_command_line_diagnostic(
    code: u32,
    message: &str,
    current_directory: &Path,
    pretty: bool,
    quiet: bool,
) {
    if quiet {
        return;
    }
    let diagnostic = Diagnostic {
        file_name: None,
        source_text: None,
        range: None,
        code: Some(code),
        category: DiagnosticCategory::Error,
        message,
    };
    print!(
        "{}",
        format_diagnostics(
            &[diagnostic],
            FormattingOptions {
                current_directory: &current_directory.to_string_lossy(),
                pretty,
                ..FormattingOptions::default()
            }
        )
    );
}

fn print_project_diagnostics(
    project_diagnostics: &[ProjectDiagnostic],
    current_directory: &str,
    pretty: bool,
    quiet: bool,
) {
    if quiet {
        return;
    }
    let diagnostics = project_diagnostics
        .iter()
        .map(|diagnostic| Diagnostic {
            file_name: diagnostic.file_name.as_deref(),
            source_text: None,
            range: diagnostic.range,
            code: Some(diagnostic.code),
            category: DiagnosticCategory::Error,
            message: &diagnostic.message,
        })
        .collect::<Vec<_>>();
    print!(
        "{}",
        format_diagnostics(
            &diagnostics,
            FormattingOptions {
                current_directory,
                pretty,
                ..FormattingOptions::default()
            }
        )
    );
}

fn exit(status: ExitStatus) -> ExitCode {
    ExitCode::from(status as u8)
}

fn run_lsp() -> ExitCode {
    let stdin = io::stdin();
    let stdout = io::stdout();
    match ts_lsp::run_framed_session(stdin.lock(), stdout.lock()) {
        Ok(result) => match result.exit_status {
            ts_lsp::ExitStatus::Success => ExitCode::SUCCESS,
            ts_lsp::ExitStatus::Failure => ExitCode::from(1),
        },
        Err(error) => {
            eprintln!("error: LSP session failed: {error}");
            ExitCode::from(1)
        }
    }
}

fn compile_development(files: &[String]) -> ExitCode {
    if files.is_empty() {
        eprintln!("error: --compile-dev requires at least one source file");
        return ExitCode::from(2);
    }
    let Ok(current_directory) = env::current_dir() else {
        eprintln!("error: could not determine the current directory");
        return ExitCode::from(2);
    };
    let file_system = OsFileSystem::default();
    let program = Program::new_with_module_resolution(
        &file_system,
        &current_directory.to_string_lossy(),
        files,
        ResolutionOptions::default(),
    );
    if !program.diagnostics().is_empty() {
        print_program_diagnostics(&program, &current_directory.to_string_lossy());
        return ExitCode::from(ExitStatus::DiagnosticsPresentOutputsSkipped as u8);
    }
    let emitted = program.emit();
    if !emitted.diagnostics.is_empty() {
        for diagnostic in emitted.diagnostics {
            println!("error: {}", diagnostic.message);
        }
        return ExitCode::from(ExitStatus::DiagnosticsPresentOutputsSkipped as u8);
    }
    for output in emitted.files {
        if let Err(error) = fs::write(&output.file_name, output.text) {
            eprintln!("error: could not write '{}': {error}", output.file_name);
            return ExitCode::from(ExitStatus::DiagnosticsPresentOutputsSkipped as u8);
        }
    }
    ExitCode::SUCCESS
}

fn check_canonical_project(arguments: &[String]) -> ExitCode {
    let [project] = arguments else {
        eprintln!("error: --check-canonical requires exactly one project path");
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    };
    let Ok(current_directory) = env::current_dir() else {
        eprintln!("error: could not determine the current directory");
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    };
    let config_path = match resolve_project_path(&current_directory, project, false, false) {
        Ok(path) => path,
        Err(status) => return status,
    };
    let (program, checked) = match Program::try_from_config_with_canonical_checker_and_queries(
        &OsFileSystem::default(),
        &config_path.to_string_lossy(),
        |_, _| (),
    ) {
        Ok(result) => result,
        Err(error) => {
            eprintln!("error {}: {error}", error.failure_class().code());
            return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
        }
    };
    print!(
        "{}",
        format_canonical_diagnostics(
            &program,
            program.diagnostics(),
            &current_directory.to_string_lossy()
        )
    );
    if checked.is_none() {
        if program.options().no_check {
            eprintln!("error: canonical checking was skipped because noCheck is enabled.");
        } else if program.diagnostics().is_empty() {
            eprintln!("error: canonical checking did not run.");
        }
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }
    diagnostic_exit(!program.diagnostics().is_empty(), false)
}

fn format_canonical_diagnostics(
    program: &Program,
    diagnostics: &[ProgramDiagnostic],
    current_directory: &str,
) -> String {
    let options = FormattingOptions {
        current_directory,
        ..FormattingOptions::default()
    };
    let mut output = String::new();
    // Program has already ordered these diagnostics by path, range, and code.
    for diagnostic in diagnostics {
        if let Some(file_name) = diagnostic.file_name.as_deref()
            && (diagnostic.range.is_none() || program.source_file(file_name).is_none())
        {
            let path = Path::new(file_name);
            let path = path.strip_prefix(current_directory).unwrap_or(path);
            output.push_str(&path.to_string_lossy().replace('\\', "/"));
            output.push_str(": ");
        }
        output.push_str(&format_program_diagnostic(program, diagnostic, options));
    }
    output
}

fn print_program_diagnostics(program: &Program, current_directory: &str) {
    print_diagnostics(
        program,
        program.diagnostics(),
        current_directory,
        false,
        false,
    );
}

fn print_diagnostics(
    program: &Program,
    program_diagnostics: &[ProgramDiagnostic],
    current_directory: &str,
    pretty: bool,
    quiet: bool,
) {
    if quiet {
        return;
    }
    let mut ordered = program_diagnostics.iter().collect::<Vec<_>>();
    ordered.sort_by(|left, right| {
        left.file_name
            .cmp(&right.file_name)
            .then_with(|| {
                left.range
                    .map(|range| range.start)
                    .cmp(&right.range.map(|range| range.start))
            })
            .then_with(|| left.code.cmp(&right.code))
    });
    let options = FormattingOptions {
        current_directory,
        pretty,
        ..FormattingOptions::default()
    };
    for diagnostic in ordered {
        print!(
            "{}",
            format_program_diagnostic(program, diagnostic, options)
        );
    }
}

fn format_program_diagnostic(
    program: &Program,
    diagnostic: &ProgramDiagnostic,
    options: FormattingOptions<'_>,
) -> String {
    let related_information = diagnostic
        .related_information
        .iter()
        .map(|related| writer_diagnostic(program, related))
        .collect::<Vec<_>>();
    format_diagnostic_with_related(
        writer_diagnostic(program, diagnostic),
        &related_information,
        options,
    )
}

fn writer_diagnostic<'source>(
    program: &'source Program,
    diagnostic: &'source ProgramDiagnostic,
) -> Diagnostic<'source> {
    let source_text = diagnostic
        .file_name
        .as_deref()
        .and_then(|file_name| program.source_file(file_name))
        .map(|source_file| source_file.source_text.as_str());
    let category = match diagnostic.category.name() {
        "warning" => DiagnosticCategory::Warning,
        "suggestion" => DiagnosticCategory::Suggestion,
        "message" => DiagnosticCategory::Message,
        _ => DiagnosticCategory::Error,
    };
    Diagnostic {
        file_name: diagnostic.file_name.as_deref(),
        source_text,
        range: diagnostic.range,
        code: diagnostic.code,
        category,
        message: &diagnostic.message,
    }
}

fn parse(path: Option<&String>) -> ExitCode {
    let Some(path) = path else {
        eprintln!("error: --parse requires a source file");
        return ExitCode::from(2);
    };
    let Ok(source) = fs::read_to_string(path) else {
        eprintln!("error: could not read '{path}'");
        return ExitCode::from(2);
    };
    let result = ts_parser::parse_source_file(&source);
    let line_starts = line_starts(&source);
    println!(
        "parsed {} AST nodes with {} diagnostics",
        result.arena.len(),
        result.diagnostics.len()
    );
    for diagnostic in result.diagnostics {
        let (line, column) = line_and_column(&source, &line_starts, diagnostic.range.start.get());
        println!("{path}({line},{column}): error: {}", diagnostic.message);
    }
    ExitCode::SUCCESS
}

fn line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    starts.extend(
        source
            .bytes()
            .enumerate()
            .filter_map(|(index, byte)| (byte == b'\n').then_some(index + 1)),
    );
    starts
}

fn line_and_column(source: &str, line_starts: &[usize], byte_position: u32) -> (usize, usize) {
    let position = usize::try_from(byte_position)
        .unwrap_or(source.len())
        .min(source.len());
    let line_index = line_starts
        .partition_point(|line_start| *line_start <= position)
        .saturating_sub(1);
    let column = source[line_starts[line_index]..position]
        .encode_utf16()
        .count()
        + 1;
    (line_index + 1, column)
}

fn tokenize(path: Option<&String>) -> ExitCode {
    let Some(path) = path else {
        eprintln!("error: --tokenize requires a source file");
        return ExitCode::from(2);
    };
    let Ok(source) = fs::read_to_string(path) else {
        eprintln!("error: could not read '{path}'");
        return ExitCode::from(2);
    };
    let mut scanner = Scanner::new(&source);
    loop {
        let token = scanner.scan();
        println!(
            "{:?} {}..{} {:?}",
            token.kind,
            token.range.start.get(),
            token.range.end.get(),
            token.text
        );
        if token.kind == ts_ast::SyntaxKind::EndOfFile {
            break;
        }
    }
    if scanner.diagnostics().is_empty() {
        ExitCode::SUCCESS
    } else {
        for diagnostic in scanner.diagnostics() {
            eprintln!(
                "error at {}: {}",
                diagnostic.range.start.get(),
                diagnostic.message
            );
        }
        ExitCode::from(2)
    }
}

fn print_help() {
    println!("tsgo: TypeScript compiler written in Rust");
    println!("\nUsage: tsgo [options] [files...]\n");
    println!("Options:");
    println!("  -h, --help         Print this message");
    println!("  -v, --version      Print the compiler version");
    println!("  -p, --project PATH Compile the project at PATH");
    println!("  -b, --build PATH   Build a project and its references");
    println!("  -f, --force        Rebuild projects even when they are up to date");
    println!("  -w, --watch        Watch input files and rebuild on changes");
    println!("      --incremental  Reuse project build information");
    println!("      --ignoreConfig Ignore tsconfig.json when compiling files");
    println!("      --listFiles    Print all files included in the compilation");
    println!("      --listFilesOnly Print included files without checking or emitting");
    println!("      --listEmittedFiles Print the paths of generated output files");
    println!("      --maxNodeModuleJsDepth NUMBER Limit JavaScript node_modules traversal");
    println!("      --noCheck      Skip semantic type checking");
    println!("      --noEmit       Do not write output files");
    println!("      --noLib        Do not include the default library");
    println!("      --target NAME  Select the ECMAScript target");
    println!("      --module NAME  Select the module format");
    println!("      --moduleResolution NAME  Select module resolution");
    println!("      --jsx NAME     Select JSX emission");
    println!("      --outDir PATH  Redirect emitted files");
    println!("      --rootDir PATH Set the source root");
    println!("      --declaration  Emit declaration files");
    println!("      --sourceMap    Emit source maps");
    println!("      --allowJs      Include JavaScript files");
    println!("      --checkJs      Check JavaScript files");
    println!("      --pretty BOOL  Enable or disable formatted diagnostics");
    println!("      --lsp          Run the language server over stdin/stdout");
    println!("      --parse        Parse one source file (development)");
    println!("      --compile-dev  Run the development compiler pipeline");
    println!(
        "      --check-canonical PROJECT Check a project with the canonical checker (development)"
    );
    println!("      --tokenize     Print the token stream for one source file");
}

#[cfg(test)]
mod tests {
    use std::{fs, path::PathBuf};

    use ts_cli::BuildOptions;
    use ts_compiler::{Program, ProgramDiagnostic};
    use ts_diagnostic_writer::FormattingOptions;
    use ts_vfs::{FileSystem, MemoryFileSystem, OsFileSystem};
    use ts_watch::WatchCompiler;

    use super::{BuildWatchCompiler, format_canonical_diagnostics, format_program_diagnostic};

    struct TestDirectory(PathBuf);

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn canonical_diagnostics_keep_range_order_before_code_order() {
        let file_system = MemoryFileSystem::new(true);
        file_system
            .write_file("/project/main.ts", "const value: string = 1;\n")
            .unwrap();
        let program = Program::new_with_options(
            &file_system,
            "/project",
            &["main.ts".to_owned()],
            ts_options::CompilerOptions {
                no_lib: true,
                ..ts_options::CompilerOptions::default()
            },
        );
        let mut short = program
            .diagnostics()
            .iter()
            .find(|diagnostic| diagnostic.code == Some(2322))
            .cloned()
            .unwrap();
        let source = program.source_file("/project/main.ts").unwrap();
        short.range = source.parse.arena.iter().find_map(|(_, node)| {
            matches!(
                &node.data,
                ts_ast::NodeData::Identifier(identifier) if identifier.text == "value"
            )
            .then_some(node.range)
        });
        let mut long = short.clone();
        long.range = source.parse.arena.iter().find_map(|(_, node)| {
            matches!(&node.data, ts_ast::NodeData::VariableDeclaration(_)).then_some(node.range)
        });
        long.code = Some(1005);
        long.message = "Longer range.".to_owned();
        assert_eq!(short.range.unwrap().start, long.range.unwrap().start);
        assert!(short.range.unwrap().end < long.range.unwrap().end);

        let output = format_canonical_diagnostics(&program, &[short, long], "/project");

        assert_eq!(
            output,
            "main.ts(1,7): error TS2322: Type 'number' is not assignable to type 'string'.\n\
             main.ts(1,7): error TS1005: Longer range.\n"
        );
    }

    #[test]
    fn build_watch_keeps_skipped_project_source_directories() {
        let directory = TestDirectory(std::env::temp_dir().join(format!(
            "tsgo-build-watch-skipped-projects-{}",
            std::process::id()
        )));
        let library_sources = directory.0.join("packages/lib/src");
        let application_sources = directory.0.join("packages/app/src");
        fs::create_dir_all(&library_sources).unwrap();
        fs::create_dir_all(&application_sources).unwrap();
        fs::write(
            directory.0.join("tsconfig.json"),
            r#"{"files":[],"references":[{"path":"./packages/app"},{"path":"./packages/lib"}]}"#,
        )
        .unwrap();
        fs::write(
            directory.0.join("packages/lib/tsconfig.json"),
            r#"{"files":["src/index.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist"}}"#,
        )
        .unwrap();
        fs::write(
            directory.0.join("packages/app/tsconfig.json"),
            r#"{"files":["src/index.ts"],"references":[{"path":"../lib"}],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist"}}"#,
        )
        .unwrap();
        fs::write(
            library_sources.join("index.ts"),
            "export const libraryValue = 1;\n",
        )
        .unwrap();
        fs::write(
            application_sources.join("index.ts"),
            "export const applicationValue = 2;\n",
        )
        .unwrap();

        let mut compiler = BuildWatchCompiler {
            options: BuildOptions {
                incremental: true,
                ..BuildOptions::default()
            },
            current_directory: directory.0.clone(),
            roots: vec!["tsconfig.json".to_owned()],
        };
        let first_cycle = compiler.compile().unwrap();
        let second_cycle = compiler.compile().unwrap();

        for source_directory in [&library_sources, &application_sources] {
            assert!(
                first_cycle
                    .watch_paths
                    .iter()
                    .any(|path| path.directory == *source_directory),
                "first cycle does not watch {}",
                source_directory.display()
            );
            assert!(
                second_cycle
                    .watch_paths
                    .iter()
                    .any(|path| path.directory == *source_directory),
                "up-to-date cycle no longer watches {}",
                source_directory.display()
            );
        }
    }

    #[test]
    fn pretty_diagnostics_include_cross_file_related_source() {
        let directory = TestDirectory(
            std::env::temp_dir().join(format!("tsgo-related-diagnostic-{}", std::process::id())),
        );
        fs::create_dir_all(&directory.0).unwrap();
        fs::write(
            directory.0.join("target.ts"),
            "export function pair(left: string, right: number): number { return right; }\n",
        )
        .unwrap();
        fs::write(
            directory.0.join("importer.ts"),
            "import { pair } from './target';\npair('left');\n",
        )
        .unwrap();
        let current_directory = directory.0.to_string_lossy();
        let program = Program::new_with_options(
            &OsFileSystem::default(),
            &current_directory,
            &["importer.ts".to_owned(), "target.ts".to_owned()],
            ts_options::CompilerOptions {
                no_lib: true,
                ..ts_options::CompilerOptions::default()
            },
        );
        let mut diagnostic = program
            .diagnostics()
            .iter()
            .find(|diagnostic| diagnostic.code == Some(2554))
            .cloned()
            .unwrap();
        let target_path = directory.0.join("target.ts");
        let target_source = program.source_file(&target_path.to_string_lossy()).unwrap();
        let related_range = target_source
            .parse
            .arena
            .iter()
            .find_map(|(_, node)| {
                matches!(
                    &node.data,
                    ts_ast::NodeData::Identifier(identifier) if identifier.text == "right"
                )
                .then_some(node.range)
            })
            .unwrap();
        diagnostic.related_information.push(ProgramDiagnostic {
            file_name: Some(target_source.file_name.clone()),
            range: Some(related_range),
            code: Some(6210),
            category: diagnostic.category,
            message: "An argument for 'right' was not provided.".to_owned(),
            related_information: Vec::new(),
        });

        let pretty = format_program_diagnostic(
            &program,
            &diagnostic,
            FormattingOptions {
                current_directory: &current_directory,
                pretty: true,
                ..FormattingOptions::default()
            },
        );
        assert!(pretty.contains("importer.ts"));
        assert!(pretty.contains("target.ts"));
        assert!(pretty.contains("An argument for 'right' was not provided."));
        assert!(pretty.contains("export function pair(left: string, right: number)"));

        let plain = format_program_diagnostic(
            &program,
            &diagnostic,
            FormattingOptions {
                current_directory: &current_directory,
                ..FormattingOptions::default()
            },
        );
        assert!(plain.contains("importer.ts"));
        assert!(!plain.contains("target.ts"));
        assert!(!plain.contains("An argument for 'right' was not provided."));
    }
}
