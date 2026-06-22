use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

const FALLBACK_ORACLE: &str = "/home/theo/.local/bin/tsgo-oracle";
static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TestDirectory(PathBuf);

impl TestDirectory {
    fn new(name: &str) -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("tsgo-cli-{name}-{}-{sequence}", std::process::id()));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }
}

impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn run(program: &str, directory: &Path, arguments: &[&str]) -> Output {
    Command::new(program)
        .args(arguments)
        .current_dir(directory)
        .output()
        .unwrap()
}

fn assert_matches_oracle(directory: &Path, arguments: &[&str]) {
    let actual = run(env!("CARGO_BIN_EXE_tsgo"), directory, arguments);
    let Some(oracle) = std::env::var_os("TS_GO_ORACLE")
        .map(PathBuf::from)
        .filter(|path| path.is_file())
        .or_else(|| {
            Path::new(FALLBACK_ORACLE)
                .is_file()
                .then(|| FALLBACK_ORACLE.into())
        })
    else {
        return;
    };
    let expected = run(&oracle.to_string_lossy(), directory, arguments);
    assert_eq!(actual.status.code(), expected.status.code());
    assert_eq!(actual.stdout, expected.stdout);
    assert_eq!(actual.stderr, expected.stderr);
}

#[test]
fn direct_file_no_emit_matches_oracle() {
    let directory = TestDirectory::new("direct");
    fs::write(directory.0.join("main.ts"), "const answer: number = 42;\n").unwrap();
    assert_matches_oracle(
        &directory.0,
        &["main.ts", "--ignoreConfig", "--noEmit", "--pretty", "false"],
    );
}

#[test]
fn project_no_emit_matches_oracle() {
    let directory = TestDirectory::new("project");
    fs::write(directory.0.join("main.ts"), "export const answer = 42;\n").unwrap();
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"compilerOptions":{"target":"esnext"},"files":["main.ts"]}"#,
    )
    .unwrap();
    assert_matches_oracle(
        &directory.0,
        &[
            "--project",
            "tsconfig.json",
            "--noEmit",
            "--pretty",
            "false",
        ],
    );
}

#[test]
fn project_and_files_conflict_matches_oracle() {
    let directory = TestDirectory::new("project-conflict");
    fs::write(directory.0.join("main.ts"), "const value = 1;\n").unwrap();
    fs::write(directory.0.join("tsconfig.json"), "{}").unwrap();
    assert_matches_oracle(
        &directory.0,
        &["main.ts", "--project", "tsconfig.json", "--pretty", "false"],
    );
}

#[test]
fn explicit_file_with_config_matches_oracle() {
    let directory = TestDirectory::new("config-bypass");
    fs::write(directory.0.join("main.ts"), "const value = 1;\n").unwrap();
    fs::write(directory.0.join("tsconfig.json"), "{}").unwrap();
    assert_matches_oracle(&directory.0, &["main.ts", "--noEmit", "--pretty", "false"]);
}

#[test]
fn emits_direct_file() {
    let directory = TestDirectory::new("emit-direct");
    fs::write(directory.0.join("main.ts"), "const answer: number = 42;\n").unwrap();
    let output = run(
        env!("CARGO_BIN_EXE_tsgo"),
        &directory.0,
        &["main.ts", "--ignoreConfig", "--pretty", "false"],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let javascript = fs::read_to_string(directory.0.join("main.js")).unwrap();
    assert!(javascript.contains("answer"));
    assert!(!javascript.contains(": number"));
}

#[test]
fn creates_project_output_directory() {
    let directory = TestDirectory::new("emit-project");
    fs::write(directory.0.join("main.ts"), "export const answer = 42;\n").unwrap();
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"compilerOptions":{"outDir":"dist"},"files":["main.ts"]}"#,
    )
    .unwrap();
    let output = run(
        env!("CARGO_BIN_EXE_tsgo"),
        &directory.0,
        &["--project", "tsconfig.json", "--pretty", "false"],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(directory.0.join("dist/main.js").is_file());
}

#[test]
fn no_check_skips_semantic_diagnostics_and_emits() {
    let directory = TestDirectory::new("no-check");
    fs::write(
        directory.0.join("main.ts"),
        "import { missing } from './absent'; const value: string = 1;\n",
    )
    .unwrap();
    assert_matches_oracle(
        &directory.0,
        &[
            "main.ts",
            "--ignoreConfig",
            "--noCheck",
            "--pretty",
            "false",
        ],
    );
    assert!(directory.0.join("main.js").is_file());
}

#[test]
fn pretty_formats_diagnostics() {
    let directory = TestDirectory::new("pretty");
    fs::write(directory.0.join("main.ts"), "const value: string = 1;\n").unwrap();
    let output = run(
        env!("CARGO_BIN_EXE_tsgo"),
        &directory.0,
        &["main.ts", "--ignoreConfig", "--noEmit", "--pretty", "true"],
    );
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.windows(2).any(|bytes| bytes == b"\x1b["));
}
