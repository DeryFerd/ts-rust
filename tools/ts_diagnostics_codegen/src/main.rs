use std::{env, fs, path::PathBuf, process::ExitCode};

use ts_diagnostics_codegen::{generate_rust, read_go_catalog, read_json_catalog};

fn main() -> ExitCode {
    match run(env::args().skip(1)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(2)
        }
    }
}

fn run(arguments: impl Iterator<Item = String>) -> Result<(), String> {
    let mut inputs = Vec::new();
    let mut go_generated = None;
    let mut output = None;
    let mut provenance = None;
    let mut arguments = arguments;
    while let Some(argument) = arguments.next() {
        let value = arguments
            .next()
            .ok_or_else(|| format!("{argument} requires a value"))?;
        match argument.as_str() {
            "--input" => inputs.push(PathBuf::from(value)),
            "--go-generated" => go_generated = Some(PathBuf::from(value)),
            "--output" => output = Some(PathBuf::from(value)),
            "--provenance" => provenance = Some(value),
            _ => return Err(format!("unknown argument {argument:?}")),
        }
    }

    let output = output.ok_or_else(|| "--output is required".to_owned())?;
    let provenance = provenance.unwrap_or_else(|| "TypeScript diagnostic catalog".to_owned());
    let entries = match (inputs.is_empty(), go_generated) {
        (false, None) => read_json_catalog(&inputs).map_err(|error| error.to_string())?,
        (true, Some(path)) => read_go_catalog(path).map_err(|error| error.to_string())?,
        (false, Some(_)) => return Err("use either --input or --go-generated, not both".into()),
        (true, None) => return Err("at least one --input or --go-generated is required".into()),
    };
    let generated = generate_rust(&entries, &provenance);
    fs::write(&output, generated)
        .map_err(|error| format!("failed to write {}: {error}", output.display()))
}
