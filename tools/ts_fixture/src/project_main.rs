use std::{
    env, fs,
    io::{self, Write},
    path::PathBuf,
    process::ExitCode,
};

use ts_fixture::project::{ProjectCensusOptions, run_project, run_project_census};

const USAGE: &str = "Usage: ts_project_oracle --project <absolute-tsconfig> --run-id <id> [--output <new-report.json>] [--header <name>] [--build-record <json>] [--cold-root-census --output <new-report.jsonl> [--census-soft-deadline-ms <milliseconds>]]";

struct Arguments {
    project: PathBuf,
    output: Option<PathBuf>,
    header: Option<String>,
    run_id: String,
    build_record: Option<PathBuf>,
    cold_root_census: bool,
    census_soft_deadline_ms: Option<u64>,
}

fn parse_arguments(
    arguments: impl IntoIterator<Item = String>,
) -> Result<Option<Arguments>, String> {
    let mut arguments = arguments.into_iter();
    let mut project = None;
    let mut output = None;
    let mut header = None;
    let mut run_id = None;
    let mut build_record = None;
    let mut cold_root_census = false;
    let mut census_soft_deadline_ms = None;
    while let Some(flag) = arguments.next() {
        if flag == "--help" || flag == "-h" {
            return Ok(None);
        }
        if flag == "--cold-root-census" {
            if cold_root_census {
                return Err(format!("repeated argument: {flag}"));
            }
            cold_root_census = true;
            continue;
        }
        let value = arguments
            .next()
            .ok_or_else(|| format!("{flag} requires a value"))?;
        let duplicate = match flag.as_str() {
            "--project" => project.replace(PathBuf::from(value)).is_some(),
            "--output" => output.replace(PathBuf::from(value)).is_some(),
            "--header" => header.replace(value).is_some(),
            "--run-id" => run_id.replace(value).is_some(),
            "--build-record" => build_record.replace(PathBuf::from(value)).is_some(),
            "--census-soft-deadline-ms" => census_soft_deadline_ms
                .replace(
                    value
                        .parse::<u64>()
                        .map_err(|_| "--census-soft-deadline-ms requires unsigned milliseconds")?,
                )
                .is_some(),
            _ => return Err(format!("unknown argument: {flag}")),
        };
        if duplicate {
            return Err(format!("repeated argument: {flag}"));
        }
    }
    let project = project.ok_or("--project is required")?;
    if census_soft_deadline_ms.is_some() && !cold_root_census {
        return Err("--census-soft-deadline-ms requires --cold-root-census".to_owned());
    }
    if cold_root_census && output.is_none() {
        return Err("--cold-root-census requires --output with a new JSON-line file".to_owned());
    }
    let run_id = run_id
        .filter(|value| !value.trim().is_empty())
        .ok_or("--run-id requires a non-empty value")?;
    Ok(Some(Arguments {
        project,
        output,
        header,
        run_id,
        build_record,
        cold_root_census,
        census_soft_deadline_ms,
    }))
}

fn run(arguments: Arguments) -> io::Result<ExitCode> {
    let build_record = arguments
        .build_record
        .map(fs::read)
        .transpose()?
        .map(|bytes| {
            serde_json::from_slice::<serde_json::Value>(&bytes)
                .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
        })
        .transpose()?;
    if arguments.cold_root_census {
        let path = arguments.output.ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "the census requires a new output path",
            )
        })?;
        let mut writer = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)?;
        let status = run_project_census(
            &arguments.project,
            arguments.header.as_deref(),
            &arguments.run_id,
            &ProjectCensusOptions {
                soft_deadline: arguments
                    .census_soft_deadline_ms
                    .map(std::time::Duration::from_millis),
                supplied_build_record: build_record,
            },
            &mut writer,
        )?;
        return Ok(
            if status.has_invariant_failure || status.completion == "stopped" {
                ExitCode::from(2)
            } else {
                ExitCode::SUCCESS
            },
        );
    }
    let mut report = run_project(
        &arguments.project,
        arguments.header.as_deref(),
        &arguments.run_id,
    )?;
    report.provenance.supplied_build_record = build_record;
    let invariant = report.has_invariant_failure();
    let mut writer: Box<dyn Write> = match arguments.output {
        Some(path) => Box::new(
            fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(path)?,
        ),
        None => Box::new(io::stdout().lock()),
    };
    serde_json::to_writer_pretty(&mut writer, &report).map_err(io::Error::other)?;
    writeln!(writer)?;
    writer.flush()?;
    Ok(if invariant {
        ExitCode::from(2)
    } else {
        ExitCode::SUCCESS
    })
}

fn main() -> ExitCode {
    match parse_arguments(env::args().skip(1)) {
        Ok(None) => {
            println!("{USAGE}");
            ExitCode::SUCCESS
        }
        Ok(Some(arguments)) => run(arguments).unwrap_or_else(|error| {
            eprintln!("ts_project_oracle: {error}");
            ExitCode::from(1)
        }),
        Err(error) => {
            eprintln!("{error}\n{USAGE}");
            ExitCode::from(1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::parse_arguments;

    #[test]
    fn project_arguments_require_an_explicit_run_and_reject_duplicates() {
        let parse =
            |values: &[&str]| parse_arguments(values.iter().map(|value| (*value).to_owned()));
        assert!(parse(&["--project", "/repo/tsconfig.json"]).is_err());
        assert!(
            parse(&[
                "--project",
                "/a.json",
                "--project",
                "/b.json",
                "--run-id",
                "one"
            ])
            .is_err()
        );
        assert!(parse(&["--project", "/a.json", "--run-id", " "]).is_err());
        assert!(parse(&["--unknown", "x"]).is_err());
        assert!(parse(&["--help"]).unwrap().is_none());
        let args = parse(&["--project", "/a.json", "--run-id", "one"])
            .unwrap()
            .unwrap();
        assert_eq!(args.run_id, "one");
    }

    #[test]
    fn census_arguments_keep_the_mode_and_deadline_explicit() {
        let parse =
            |values: &[&str]| parse_arguments(values.iter().map(|value| (*value).to_owned()));
        let base = ["--project", "/repo/tsconfig.json", "--run-id", "census"];
        assert!(parse(&[base.as_slice(), &["--cold-root-census"]].concat()).is_err());
        assert!(parse(&[base.as_slice(), &["--census-soft-deadline-ms", "1"]].concat()).is_err());
        let flags = [
            base.as_slice(),
            &[
                "--cold-root-census",
                "--output",
                "/new.jsonl",
                "--census-soft-deadline-ms",
                "0",
            ],
        ]
        .concat();
        let arguments = parse(&flags).unwrap().unwrap();
        assert!(arguments.cold_root_census);
        assert_eq!(arguments.census_soft_deadline_ms, Some(0));
        assert!(parse(&[flags.as_slice(), &["--cold-root-census"]].concat()).is_err());
        assert!(parse(&[flags.as_slice(), &["--census-soft-deadline-ms", "2"]].concat()).is_err());
        assert!(
            parse(
                &[
                    base.as_slice(),
                    &[
                        "--cold-root-census",
                        "--output",
                        "/new.jsonl",
                        "--census-soft-deadline-ms",
                        "-1"
                    ]
                ]
                .concat()
            )
            .is_err()
        );
    }

    #[test]
    fn census_output_is_opened_before_any_config_check() {
        let path = std::env::temp_dir().join(format!(
            "ts-census-existing-{}-{}.jsonl",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::write(&path, b"unchanged output").unwrap();
        let arguments = super::Arguments {
            project: std::path::PathBuf::from("relative-and-invalid.json"),
            output: Some(path.clone()),
            header: None,
            run_id: "existing-output".to_owned(),
            build_record: None,
            cold_root_census: true,
            census_soft_deadline_ms: None,
        };
        let error = super::run(arguments).unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);
        assert_eq!(std::fs::read(&path).unwrap(), b"unchanged output");
        std::fs::remove_file(path).unwrap();
    }
}
