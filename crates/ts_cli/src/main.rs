use std::{
    env, fs, io,
    path::{Path, PathBuf},
    process::ExitCode,
};

use ts_cli::{Command, CompilerOptions as CliOptions, ExitStatus, VERSION, parse_command_line};
use ts_compiler::{Program, ProgramDiagnostic, ProgramOptionsOverride};
use ts_diagnostic_writer::{Diagnostic, DiagnosticCategory, FormattingOptions, format_diagnostics};
use ts_module::ResolutionOptions;
use ts_options::CompilerOptions;
use ts_scanner::Scanner;
use ts_vfs::OsFileSystem;

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
    match parse_command_line(&args, |path| fs::read_to_string(path)) {
        Ok(Command::Version) => {
            println!("Version {VERSION}");
            ExitCode::SUCCESS
        }
        Ok(Command::Help) => {
            print_help();
            if args.is_empty() {
                ExitCode::from(ExitStatus::DiagnosticsPresentOutputsSkipped as u8)
            } else {
                ExitCode::SUCCESS
            }
        }
        Ok(Command::Lsp) => run_lsp(),
        Ok(Command::Compile(options)) => compile(&options),
        Err(error) => {
            println!("{}", error.render());
            ExitCode::from(ExitStatus::DiagnosticsPresentOutputsSkipped as u8)
        }
    }
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
        );
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }

    let file_system = OsFileSystem::default();
    let overrides = ProgramOptionsOverride {
        no_check: options.no_check.then_some(true),
        no_emit: options.no_emit.then_some(true),
        no_lib: options.no_lib.then_some(true),
    };
    let project_path = options
        .project
        .as_deref()
        .map(|path| resolve_project_path(&current_directory, path))
        .or(discovered_config);
    if options.files.is_empty() && project_path.is_none() {
        print_help();
        return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
    }

    let current_directory_text = current_directory.to_string_lossy();
    let program = if let Some(config_path) = project_path {
        Program::from_config_with_options(&file_system, &config_path.to_string_lossy(), overrides)
    } else {
        Program::new_with_options(
            &file_system,
            &current_directory_text,
            &options.files,
            CompilerOptions {
                no_check: options.no_check,
                no_emit: options.no_emit,
                no_lib: options.no_lib,
                ..CompilerOptions::default()
            },
        )
    };

    print_diagnostics(
        &program,
        program.diagnostics(),
        &current_directory_text,
        pretty,
    );
    let emitted = program.emit();
    print_diagnostics(
        &program,
        &emitted.diagnostics,
        &current_directory_text,
        pretty,
    );
    let had_diagnostics = !program.diagnostics().is_empty() || !emitted.diagnostics.is_empty();
    let mut generated_output = false;
    for output in emitted.files {
        let output_path = Path::new(&output.file_name);
        if let Some(parent) = output_path.parent()
            && !parent.as_os_str().is_empty()
            && let Err(error) = fs::create_dir_all(parent)
        {
            eprintln!("error: could not create '{}': {error}", parent.display());
            return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
        }
        if let Err(error) = fs::write(output_path, output.text) {
            eprintln!("error: could not write '{}': {error}", output.file_name);
            return exit(ExitStatus::DiagnosticsPresentOutputsSkipped);
        }
        generated_output = true;
    }

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

fn find_config_file(start: &Path) -> Option<PathBuf> {
    start
        .ancestors()
        .map(|directory| directory.join("tsconfig.json"))
        .find(|path| path.is_file())
}

fn resolve_project_path(current_directory: &Path, project: &str) -> PathBuf {
    let path = current_directory.join(project);
    if path.is_dir() {
        path.join("tsconfig.json")
    } else {
        path
    }
}

fn print_command_line_diagnostic(code: u32, message: &str, current_directory: &Path, pretty: bool) {
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

fn print_program_diagnostics(program: &Program, current_directory: &str) {
    print_diagnostics(program, program.diagnostics(), current_directory, false);
}

fn print_diagnostics(
    program: &Program,
    program_diagnostics: &[ProgramDiagnostic],
    current_directory: &str,
    pretty: bool,
) {
    let diagnostics: Vec<_> = program_diagnostics
        .iter()
        .map(|diagnostic| {
            let source_text = diagnostic
                .file_name
                .as_deref()
                .and_then(|file_name| program.source_file(file_name))
                .map(|source_file| source_file.source_text.as_str());
            Diagnostic {
                file_name: diagnostic.file_name.as_deref(),
                source_text,
                range: diagnostic.range,
                code: diagnostic.code,
                category: DiagnosticCategory::Error,
                message: &diagnostic.message,
            }
        })
        .collect();
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
    println!("      --ignoreConfig Ignore tsconfig.json when compiling files");
    println!("      --noCheck      Skip semantic type checking");
    println!("      --noEmit       Do not write output files");
    println!("      --noLib        Do not include the default library");
    println!("      --pretty BOOL  Enable or disable formatted diagnostics");
    println!("      --lsp          Run the language server over stdin/stdout");
    println!("      --parse        Parse one source file (development)");
    println!("      --compile-dev  Run the development compiler pipeline");
    println!("      --tokenize     Print the token stream for one source file");
}
