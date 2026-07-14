use std::{env, io, path::PathBuf, process::ExitCode};

use ts_fixture::{
    RunnerOptions, discover_upstream_manifest, run_upstream_baselines,
    run_upstream_diagnostic_baselines,
};

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
    if options.manifest {
        return match discover_upstream_manifest(&repository)
            .and_then(|manifest| manifest.write_to(&mut io::stdout().lock()))
        {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("error: {error}");
                ExitCode::from(2)
            }
        };
    }
    let result = if options.diagnostics {
        run_upstream_diagnostic_baselines(&repository, &options, &mut io::stdout().lock())
    } else {
        run_upstream_baselines(&repository, &options, &mut io::stdout().lock())
    };
    match result {
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
            "--diagnostics" => options.diagnostics = true,
            "--manifest" => options.manifest = true,
            "--scorecard-json" => {
                index += 1;
                options.scorecard_json = Some(PathBuf::from(required_value(
                    arguments,
                    index,
                    "--scorecard-json",
                )?));
            }
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
            "--skip" => {
                index += 1;
                let value = required_value(arguments, index, "--skip")?;
                options.skip = value
                    .parse::<usize>()
                    .map_err(|_| format!("invalid --skip value '{value}'"))?;
            }
            argument => return Err(format!("unknown option '{argument}'")),
        }
        index += 1;
    }
    if options.scorecard_json.is_some() && !options.diagnostics {
        return Err("--scorecard-json requires --diagnostics".to_owned());
    }
    if options.scorecard_json.is_some() && options.manifest {
        return Err("--scorecard-json cannot be used with --manifest".to_owned());
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
    println!(
        "Usage: ts_fixture_baseline [--diagnostics] [--scorecard-json FILE] [--manifest] [--filter TEXT] [--skip COUNT] [--limit COUNT]"
    );
    println!(
        "Reads the pinned typescript-go compiler/conformance corpus and actual baselines below TS_GO_REPO."
    );
}

#[cfg(test)]
mod tests {
    use super::parse_arguments;

    #[test]
    fn parses_filter_skip_and_limit() {
        let options = parse_arguments(&[
            "--filter".into(),
            "modules".into(),
            "--skip".into(),
            "10".into(),
            "--limit".into(),
            "25".into(),
            "--diagnostics".into(),
            "--scorecard-json".into(),
            "scorecard.json".into(),
        ])
        .unwrap()
        .unwrap();
        assert_eq!(options.filter.as_deref(), Some("modules"));
        assert_eq!(options.skip, 10);
        assert_eq!(options.limit, Some(25));
        assert!(options.diagnostics);
        assert_eq!(
            options.scorecard_json.as_deref(),
            Some(std::path::Path::new("scorecard.json"))
        );
        assert!(!options.manifest);
    }

    #[test]
    fn rejects_invalid_arguments() {
        assert!(
            parse_arguments(&["--manifest".into()])
                .unwrap()
                .unwrap()
                .manifest
        );
        assert!(parse_arguments(&["--limit".into(), "many".into()]).is_err());
        assert!(parse_arguments(&["--skip".into(), "many".into()]).is_err());
        assert!(parse_arguments(&["--unknown".into()]).is_err());
        assert!(parse_arguments(&["--scorecard-json".into(), "scorecard.json".into()]).is_err());
        assert!(
            parse_arguments(&[
                "--diagnostics".into(),
                "--manifest".into(),
                "--scorecard-json".into(),
                "scorecard.json".into(),
            ])
            .is_err()
        );
    }
}
