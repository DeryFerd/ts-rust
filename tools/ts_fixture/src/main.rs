use std::{env, io, path::PathBuf, process::ExitCode};

use ts_fixture::{RunnerOptions, run_upstream_baselines};

fn main() -> ExitCode {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    let options = match parse_arguments(&arguments) {
        Ok(Some(options)) => options,
        Ok(None) => {
            print_help();
            return ExitCode::SUCCESS;
        }
        Err(error) => {
            eprintln!("error: {error}");
            return ExitCode::from(2);
        }
    };
    let Some(repository) = env::var_os("TS_GO_REPO").map(PathBuf::from) else {
        eprintln!("error: TS_GO_REPO is not set");
        return ExitCode::from(2);
    };
    match run_upstream_baselines(&repository, &options, &mut io::stdout().lock()) {
        Ok(summary) if summary.is_success() => ExitCode::SUCCESS,
        Ok(_) => ExitCode::from(1),
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(2)
        }
    }
}

fn parse_arguments(arguments: &[String]) -> Result<Option<RunnerOptions>, String> {
    let mut options = RunnerOptions::default();
    let mut index = 0;
    while index < arguments.len() {
        match arguments[index].as_str() {
            "--help" | "-h" => return Ok(None),
            "--filter" => {
                index += 1;
                options.filter = Some(required_value(arguments, index, "--filter")?);
            }
            "--limit" => {
                index += 1;
                let value = required_value(arguments, index, "--limit")?;
                options.limit = Some(
                    value
                        .parse::<usize>()
                        .map_err(|_| format!("invalid --limit value '{value}'"))?,
                );
            }
            argument => return Err(format!("unknown option '{argument}'")),
        }
        index += 1;
    }
    Ok(Some(options))
}

fn required_value(arguments: &[String], index: usize, option: &str) -> Result<String, String> {
    arguments
        .get(index)
        .filter(|value| !value.starts_with('-'))
        .cloned()
        .ok_or_else(|| format!("{option} expects a value"))
}

fn print_help() {
    println!("Usage: ts_fixture_baseline [--filter TEXT] [--limit COUNT]");
    println!("Reads cases and reference baselines below TS_GO_REPO.");
}

#[cfg(test)]
mod tests {
    use super::parse_arguments;

    #[test]
    fn parses_filter_and_limit() {
        let options = parse_arguments(&[
            "--filter".into(),
            "modules".into(),
            "--limit".into(),
            "25".into(),
        ])
        .unwrap()
        .unwrap();
        assert_eq!(options.filter.as_deref(), Some("modules"));
        assert_eq!(options.limit, Some(25));
    }

    #[test]
    fn rejects_invalid_arguments() {
        assert!(parse_arguments(&["--limit".into(), "many".into()]).is_err());
        assert!(parse_arguments(&["--unknown".into()]).is_err());
    }
}
