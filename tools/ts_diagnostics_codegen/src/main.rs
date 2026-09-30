use std::{
    env, fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

use ts_diagnostics_codegen::{
    generate_names_rust, generate_rust, has_lazy_key_map, read_go_catalog, read_go_names,
    read_json_catalog, read_removed,
};

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
    let mut names_output = None;
    let mut removed = None;
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
            "--names-output" => names_output = Some(PathBuf::from(value)),
            "--removed" => removed = Some(PathBuf::from(value)),
            "--provenance" => provenance = Some(value),
            _ => return Err(format!("unknown argument {argument:?}")),
        }
    }

    let output = output.ok_or_else(|| "--output is required".to_owned())?;
    // The Go variable names are only in the Go file.
    if names_output.is_some() && go_generated.is_none() {
        return Err("--names-output requires --go-generated".into());
    }
    if removed.is_some() && names_output.is_none() {
        return Err("--removed requires --names-output".into());
    }
    let provenance = provenance.unwrap_or_else(|| "TypeScript diagnostic catalog".to_owned());
    let entries = match (inputs.is_empty(), &go_generated) {
        (false, None) => read_json_catalog(&inputs).map_err(|error| error.to_string())?,
        (true, Some(path)) => read_go_catalog(path).map_err(|error| error.to_string())?,
        (false, Some(_)) => return Err("use either --input or --go-generated, not both".into()),
        (true, None) => return Err("at least one --input or --go-generated is required".into()),
    };
    write(&output, &generate_rust(&entries, &provenance))?;
    if let (Some(names_output), Some(go_generated)) = (names_output, go_generated) {
        let names = read_go_names(&go_generated).map_err(|error| error.to_string())?;
        let lazy_key_map = has_lazy_key_map(&go_generated).map_err(|error| error.to_string())?;
        let removed = match removed {
            Some(path) => read_removed(path).map_err(|error| error.to_string())?,
            None => Vec::new(),
        };
        let generated = generate_names_rust(&names, &entries, &removed, lazy_key_map, &provenance)
            .map_err(|error| error.to_string())?;
        write(&names_output, &generated)?;
    }
    Ok(())
}

fn write(path: &Path, contents: &str) -> Result<(), String> {
    fs::write(path, contents)
        .map_err(|error| format!("failed to write {}: {error}", path.display()))
}
