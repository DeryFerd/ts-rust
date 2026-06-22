use std::{env, fs, process::ExitCode};

use ts_cli::{Command, ExitStatus, VERSION, parse_command_line};
use ts_compiler::Program;
use ts_module::ResolutionOptions;
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
        Ok(Command::Compile(options)) => {
            let input = options.files.first().map_or("<project>", String::as_str);
            println!("error: compilation is not implemented yet (received '{input}')");
            ExitCode::from(ExitStatus::NotImplemented as u8)
        }
        Err(error) => {
            println!("{}", error.render());
            ExitCode::from(ExitStatus::DiagnosticsPresentOutputsSkipped as u8)
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
        for diagnostic in program.diagnostics() {
            let code = diagnostic
                .code
                .map_or(String::new(), |code| format!(" TS{code}"));
            let file = diagnostic
                .file_name
                .as_deref()
                .map_or(String::new(), |file| format!("{file}: "));
            println!("{file}error{code}: {}", diagnostic.message);
        }
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
    println!(
        "parsed {} AST nodes with {} diagnostics",
        result.arena.len(),
        result.diagnostics.len()
    );
    for diagnostic in result.diagnostics {
        let (line, column) = line_and_column(&source, diagnostic.range.start.get());
        println!("{path}({line},{column}): error: {}", diagnostic.message);
    }
    ExitCode::SUCCESS
}

fn line_and_column(source: &str, byte_position: u32) -> (usize, usize) {
    let position = usize::try_from(byte_position)
        .unwrap_or(source.len())
        .min(source.len());
    let prefix = &source[..position];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let line_start = prefix.rfind(['\n', '\r']).map_or(0, |index| index + 1);
    let column = prefix[line_start..].encode_utf16().count() + 1;
    (line, column)
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
    println!("  -h, --help       Print this message");
    println!("  -v, --version    Print the compiler version");
    println!("      --parse      Parse one source file (development)");
    println!("      --compile-dev  Run the development compiler pipeline");
    println!("      --tokenize   Print the token stream for one source file");
}
