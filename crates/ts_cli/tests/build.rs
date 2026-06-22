use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TestDirectory(PathBuf);

impl TestDirectory {
    fn new(name: &str) -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "tsgo-build-{name}-{}-{sequence}",
            std::process::id()
        ));
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

fn run(directory: &Path, arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_tsgo"))
        .args(arguments)
        .current_dir(directory)
        .output()
        .unwrap()
}

fn write_project(directory: &Path) {
    fs::create_dir_all(directory.join("packages/lib")).unwrap();
    fs::create_dir_all(directory.join("packages/app")).unwrap();
    fs::write(
        directory.join("tsconfig.json"),
        r#"{"files":[],"include":[],"references":[{"path":"./packages/app"},{"path":"./packages/lib"}]}"#,
    )
    .unwrap();
    fs::write(
        directory.join("packages/lib/tsconfig.json"),
        r#"{"files":["index.ts"],"compilerOptions":{"outDir":"dist","noLib":true}}"#,
    )
    .unwrap();
    fs::write(
        directory.join("packages/lib/index.ts"),
        "export const libraryValue = 1;\n",
    )
    .unwrap();
    fs::write(
        directory.join("packages/app/tsconfig.json"),
        r#"{"files":["index.ts"],"references":[{"path":"../lib"}],"compilerOptions":{"outDir":"dist","noLib":true}}"#,
    )
    .unwrap();
    fs::write(
        directory.join("packages/app/index.ts"),
        "export const applicationValue = 2;\n",
    )
    .unwrap();
}

#[test]
fn builds_referenced_projects() {
    let directory = TestDirectory::new("multi-project");
    write_project(&directory.0);
    let output = run(
        &directory.0,
        &["--build", "tsconfig.json", "--pretty", "false"],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(directory.0.join("packages/lib/dist/index.js").is_file());
    assert!(directory.0.join("packages/app/dist/index.js").is_file());
}

#[test]
fn build_no_emit_writes_no_outputs() {
    let directory = TestDirectory::new("no-emit");
    write_project(&directory.0);
    let output = run(&directory.0, &["-b", "--noEmit", "--pretty", "false"]);
    assert!(output.status.success());
    assert!(!directory.0.join("packages/lib/dist/index.js").exists());
    assert!(!directory.0.join("packages/app/dist/index.js").exists());
}

#[test]
fn build_reports_reference_cycles_with_status_four() {
    let directory = TestDirectory::new("cycle");
    fs::create_dir_all(directory.0.join("child")).unwrap();
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":[],"references":[{"path":"./child"}]}"#,
    )
    .unwrap();
    fs::write(
        directory.0.join("child/tsconfig.json"),
        r#"{"files":[],"references":[{"path":".."}]}"#,
    )
    .unwrap();
    let output = run(
        &directory.0,
        &["--build", "tsconfig.json", "--pretty", "false"],
    );
    assert_eq!(output.status.code(), Some(4));
    assert!(String::from_utf8_lossy(&output.stdout).contains("error TS6202:"));
}

#[test]
fn build_reports_missing_referenced_config() {
    let directory = TestDirectory::new("missing");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":[],"references":[{"path":"./missing"}]}"#,
    )
    .unwrap();
    let output = run(
        &directory.0,
        &["--build", "tsconfig.json", "--pretty", "false"],
    );
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("error TS6053:"));
    assert!(stdout.contains("missing/tsconfig.json"));
}

#[test]
fn incremental_build_skips_unchanged_and_invalidates_consumers() {
    let directory = TestDirectory::new("incremental");
    write_project(&directory.0);
    let arguments = ["--build", "--incremental", "--pretty", "false"];
    let first = run(&directory.0, &arguments);
    assert!(first.status.success());
    let library_output = directory.0.join("packages/lib/dist/index.js");
    let application_output = directory.0.join("packages/app/dist/index.js");
    let library_info = directory.0.join("packages/lib/tsconfig.tsbuildinfo");
    let application_info = directory.0.join("packages/app/tsconfig.tsbuildinfo");
    assert!(library_info.is_file());
    assert!(application_info.is_file());

    fs::write(&library_output, "unchanged sentinel").unwrap();
    fs::write(&application_output, "unchanged sentinel").unwrap();
    let second = run(&directory.0, &arguments);
    assert!(second.status.success());
    assert_eq!(
        fs::read_to_string(&library_output).unwrap(),
        "unchanged sentinel"
    );
    assert_eq!(
        fs::read_to_string(&application_output).unwrap(),
        "unchanged sentinel"
    );

    fs::write(
        directory.0.join("packages/lib/index.ts"),
        "export const libraryValue = 3;\n",
    )
    .unwrap();
    let third = run(&directory.0, &arguments);
    assert!(third.status.success());
    assert_ne!(
        fs::read_to_string(&library_output).unwrap(),
        "unchanged sentinel"
    );
    assert_ne!(
        fs::read_to_string(&application_output).unwrap(),
        "unchanged sentinel"
    );
}

#[test]
fn composite_project_uses_configured_build_info_path() {
    let directory = TestDirectory::new("composite");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist","tsBuildInfoFile":"cache/state.tsbuildinfo"}}"#,
    )
    .unwrap();
    fs::write(directory.0.join("main.ts"), "export const value = 1;\n").unwrap();
    let arguments = ["--build", "--pretty", "false"];
    assert!(run(&directory.0, &arguments).status.success());
    let output = directory.0.join("dist/main.js");
    assert!(directory.0.join("cache/state.tsbuildinfo").is_file());
    fs::write(&output, "composite sentinel").unwrap();
    assert!(run(&directory.0, &arguments).status.success());
    assert_eq!(fs::read_to_string(output).unwrap(), "composite sentinel");
}
