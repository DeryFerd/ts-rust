use std::{
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use ts_ast_codegen::generate_syntax_kind_file;

fn main() {
    if let Err(error) = run(std::env::args_os().skip(1)) {
        eprintln!("ts_ast_codegen: {error}");
        std::process::exit(1);
    }
}

fn run(args: impl Iterator<Item = std::ffi::OsString>) -> Result<(), String> {
    let args: Vec<_> = args.collect();
    let default_schema = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("spec/ast.json");
    match args.as_slice() {
        [command] if command == "emit" => emit(&default_schema, None),
        [command, output] if command == "emit" => emit(&default_schema, Some(Path::new(output))),
        [command, output] if command == "check" => check(&default_schema, Path::new(output)),
        [command, schema, output] if command == "emit" => {
            emit(Path::new(schema), Some(Path::new(output)))
        }
        [command, schema, output] if command == "check" => {
            check(Path::new(schema), Path::new(output))
        }
        _ => Err(
            "usage: ts_ast_codegen emit [SCHEMA OUTPUT] | emit [OUTPUT] | check [SCHEMA] OUTPUT"
                .to_owned(),
        ),
    }
}

fn emit(schema: &Path, output: Option<&Path>) -> Result<(), String> {
    let generated = format_rust(&generate_syntax_kind_file(schema)?)?;
    if let Some(output) = output {
        std::fs::write(output, generated)
            .map_err(|error| format!("failed to write {}: {error}", output.display()))?;
    } else {
        print!("{generated}");
    }
    Ok(())
}

fn check(schema: &Path, output: &Path) -> Result<(), String> {
    let generated = format_rust(&generate_syntax_kind_file(schema)?)?;
    let existing = std::fs::read_to_string(output)
        .map_err(|error| format!("failed to read {}: {error}", output.display()))?;
    if generated == existing {
        Ok(())
    } else {
        Err(format!(
            "{} is stale; regenerate it with `ts_ast_codegen emit {}`",
            output.display(),
            output.display()
        ))
    }
}

fn format_rust(source: &str) -> Result<String, String> {
    let mut child = Command::new("rustfmt")
        .args(["--edition", "2024", "--emit", "stdout"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("failed to start rustfmt: {error}"))?;
    child
        .stdin
        .take()
        .ok_or_else(|| "rustfmt stdin is unavailable".to_owned())?
        .write_all(source.as_bytes())
        .map_err(|error| format!("failed to write to rustfmt: {error}"))?;
    let output = child
        .wait_with_output()
        .map_err(|error| format!("failed to wait for rustfmt: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "rustfmt failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    String::from_utf8(output.stdout)
        .map_err(|error| format!("rustfmt returned invalid UTF-8: {error}"))
}
