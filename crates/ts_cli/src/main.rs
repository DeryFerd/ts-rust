use std::{env, fs, process::ExitCode};

use ts_scanner::Scanner;

fn main() -> ExitCode {
    let mut args = env::args().skip(1);
    match args.next().as_deref() {
        Some("--version" | "-v") => {
            println!("Version {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        Some("--help" | "-h") | None => {
            print_help();
            ExitCode::SUCCESS
        }
        Some("--tokenize") => {
            let Some(path) = args.next() else {
                eprintln!("error: --tokenize requires a source file");
                return ExitCode::from(2);
            };
            let Ok(source) = fs::read_to_string(&path) else {
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
        Some(argument) => {
            eprintln!("error: compilation is not implemented yet (received '{argument}')");
            ExitCode::from(2)
        }
    }
}

fn print_help() {
    println!("tsgo: TypeScript compiler written in Rust");
    println!("\nUsage: tsgo [options] [files...]\n");
    println!("Options:");
    println!("  -h, --help       Print this message");
    println!("  -v, --version    Print the compiler version");
    println!("      --tokenize   Print the token stream for one source file");
}
