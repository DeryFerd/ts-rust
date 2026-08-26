use std::{
    env, fs,
    io::{self, Write},
    path::PathBuf,
    process::ExitCode,
};

use ts_fixture::project::run_project;

const USAGE: &str = "Usage: ts_project_oracle --project <absolute-tsconfig> --run-id <id> [--output <new-report.json>] [--header <name>] [--build-record <json>]";

struct Arguments {
    project: PathBuf,
    output: Option<PathBuf>,
    header: Option<String>,
    run_id: String,
    build_record: Option<PathBuf>,
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
    while let Some(flag) = arguments.next() {
        if flag == "--help" || flag == "-h" {
            return Ok(None);
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
            _ => return Err(format!("unknown argument: {flag}")),
        };
        if duplicate {
            return Err(format!("repeated argument: {flag}"));
        }
    }
    let project = project.ok_or("--project is required")?;
    let run_id = run_id
        .filter(|value| !value.trim().is_empty())
        .ok_or("--run-id requires a non-empty value")?;
    Ok(Some(Arguments {
        project,
        output,
        header,
        run_id,
        build_record,
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
}
