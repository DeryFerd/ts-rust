//! Black-box differential runner for the Go oracle and Rust compiler.

use std::{env, ffi::OsString, path::Path, process::Command};

#[derive(Debug, Eq, PartialEq)]
struct Output {
    status: Option<i32>,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

fn main() {
    let arguments: Vec<_> = env::args_os().skip(1).collect();
    if let Err(error) = run(&arguments) {
        eprintln!("ts_compare: {error}");
        std::process::exit(2);
    }
}

fn run(arguments: &[OsString]) -> Result<(), String> {
    let separator = arguments
        .iter()
        .position(|argument| argument == "--")
        .ok_or_else(usage)?;
    if separator != 2 {
        return Err(usage());
    }
    let oracle = Path::new(&arguments[0]);
    let candidate = Path::new(&arguments[1]);
    let compiler_arguments = &arguments[separator + 1..];
    let oracle_output = execute(oracle, compiler_arguments)?;
    let candidate_output = execute(candidate, compiler_arguments)?;
    if oracle_output == candidate_output {
        println!("match");
        return Ok(());
    }
    print_difference(
        "exit status",
        &oracle_output.status,
        &candidate_output.status,
    );
    print_bytes_difference("stdout", &oracle_output.stdout, &candidate_output.stdout);
    print_bytes_difference("stderr", &oracle_output.stderr, &candidate_output.stderr);
    std::process::exit(1);
}

fn usage() -> String {
    "usage: ts_compare ORACLE CANDIDATE -- [compiler arguments...]".to_owned()
}

fn execute(program: &Path, arguments: &[OsString]) -> Result<Output, String> {
    let output = Command::new(program)
        .args(arguments)
        .env("NO_COLOR", "1")
        .env("FORCE_COLOR", "0")
        .output()
        .map_err(|error| format!("failed to run {}: {error}", program.display()))?;
    Ok(Output {
        status: output.status.code(),
        stdout: output.stdout,
        stderr: output.stderr,
    })
}

fn print_difference<T: std::fmt::Debug + PartialEq>(name: &str, oracle: &T, candidate: &T) {
    if oracle != candidate {
        eprintln!("{name} differs:\n  oracle:    {oracle:?}\n  candidate: {candidate:?}");
    }
}

fn print_bytes_difference(name: &str, oracle: &[u8], candidate: &[u8]) {
    if oracle != candidate {
        eprintln!(
            "{name} differs:\n--- oracle\n{}\n--- candidate\n{}",
            String::from_utf8_lossy(oracle),
            String::from_utf8_lossy(candidate)
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{Output, execute};
    use std::{ffi::OsString, path::Path};

    #[test]
    fn captures_process_status_and_streams() {
        let output = execute(
            Path::new("/bin/sh"),
            &[
                OsString::from("-c"),
                OsString::from("printf out; printf err >&2; exit 7"),
            ],
        )
        .unwrap();
        assert_eq!(
            output,
            Output {
                status: Some(7),
                stdout: b"out".to_vec(),
                stderr: b"err".to_vec(),
            }
        );
    }
}
