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
fn build_no_check_skips_semantic_diagnostics() {
    let directory = TestDirectory::new("no-check");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"noLib":true,"outDir":"dist"}}"#,
    )
    .unwrap();
    fs::write(
        directory.0.join("main.ts"),
        "export const value: string = 1;\n",
    )
    .unwrap();

    let output = run(&directory.0, &["--build", "--noCheck", "--pretty", "false"]);

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(directory.0.join("dist/main.js").is_file());
}

#[test]
fn build_checks_side_effect_imports_by_default_and_honors_explicit_false() {
    let directory = TestDirectory::new("side-effect-imports");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"noEmit":true}}"#,
    )
    .unwrap();
    fs::write(directory.0.join("main.ts"), "import './missing.css';\n").unwrap();

    let checked = run(&directory.0, &["--build", "--pretty", "false"]);
    assert_eq!(checked.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&checked.stdout).contains(
        "error TS2882: Cannot find module or type declarations for side-effect import of './missing.css'."
    ));

    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"noEmit":true,"noUncheckedSideEffectImports":false}}"#,
    )
    .unwrap();
    let disabled = run(&directory.0, &["--build", "--pretty", "false"]);
    assert!(disabled.status.success());
    assert!(disabled.stdout.is_empty());
}

#[test]
fn build_force_rebuilds_an_up_to_date_project() {
    let directory = TestDirectory::new("force");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist","tsBuildInfoFile":"cache/state.tsbuildinfo"}}"#,
    )
    .unwrap();
    fs::write(directory.0.join("main.ts"), "export const value = 1;\n").unwrap();
    let ordinary = ["--build", "--pretty", "false"];
    assert!(run(&directory.0, &ordinary).status.success());

    let output_path = directory.0.join("dist/main.js");
    fs::write(&output_path, "up-to-date sentinel").unwrap();
    assert!(run(&directory.0, &ordinary).status.success());
    assert_eq!(
        fs::read_to_string(&output_path).unwrap(),
        "up-to-date sentinel"
    );

    let forced = run(&directory.0, &["--build", "--force", "--pretty", "false"]);
    assert!(
        forced.status.success(),
        "{}",
        String::from_utf8_lossy(&forced.stdout)
    );
    assert_ne!(
        fs::read_to_string(&output_path).unwrap(),
        "up-to-date sentinel"
    );
    assert!(directory.0.join("cache/state.tsbuildinfo").is_file());
}

#[test]
fn build_info_cannot_overwrite_project_input() {
    let directory = TestDirectory::new("build-info-input-collision");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist","tsBuildInfoFile":"main.ts"}}"#,
    )
    .unwrap();
    let source = directory.0.join("main.ts");
    let original_source = "export const value = 1;\n";
    fs::write(&source, original_source).unwrap();

    let output = run(&directory.0, &["--build", "--pretty", "false"]);

    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stdout).contains("error TS5055:"));
    assert_eq!(fs::read_to_string(&source).unwrap(), original_source);
    assert!(!directory.0.join("dist/main.js").exists());
}

#[test]
fn forced_build_cannot_delete_project_input() {
    let directory = TestDirectory::new("force-build-info-input-collision");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist","tsBuildInfoFile":"main.ts"}}"#,
    )
    .unwrap();
    let source = directory.0.join("main.ts");
    let original_source = "export const value = 1;\n";
    fs::write(&source, original_source).unwrap();

    let output = run(&directory.0, &["--build", "--force", "--pretty", "false"]);

    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stdout).contains("error TS5055:"));
    assert_eq!(fs::read_to_string(&source).unwrap(), original_source);
    assert!(!directory.0.join("dist/main.js").exists());
}

#[test]
fn build_info_cannot_overwrite_javascript_or_declarations() {
    for (kind, file_name) in [("javascript", "main.js"), ("declaration", "main.d.ts")] {
        let directory = TestDirectory::new(&format!("build-info-{kind}-collision"));
        fs::write(
            directory.0.join("tsconfig.json"),
            format!(
                r#"{{"files":["main.ts"],"compilerOptions":{{"composite":true,"noLib":true,"outDir":"dist","tsBuildInfoFile":"dist/{file_name}"}}}}"#
            ),
        )
        .unwrap();
        fs::write(directory.0.join("main.ts"), "export const value = 1;\n").unwrap();
        let output_path = directory.0.join("dist").join(file_name);
        fs::create_dir_all(output_path.parent().unwrap()).unwrap();
        fs::write(&output_path, "existing generated output").unwrap();

        for arguments in [
            &["--build", "--pretty", "false"][..],
            &["--build", "--force", "--pretty", "false"][..],
        ] {
            let output = run(&directory.0, arguments);

            assert_eq!(output.status.code(), Some(1), "{kind}");
            assert!(
                String::from_utf8_lossy(&output.stdout).contains("error TS5056:"),
                "{kind}: {}",
                String::from_utf8_lossy(&output.stdout)
            );
            assert_eq!(
                fs::read_to_string(&output_path).unwrap(),
                "existing generated output"
            );
        }
    }
}

#[test]
fn referenced_projects_cannot_share_build_info() {
    let directory = TestDirectory::new("shared-build-info");
    fs::create_dir_all(directory.0.join("lib")).unwrap();
    fs::create_dir_all(directory.0.join("app")).unwrap();
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":[],"references":[{"path":"./app"}]}"#,
    )
    .unwrap();
    fs::write(
        directory.0.join("lib/tsconfig.json"),
        r#"{"files":["index.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist","tsBuildInfoFile":"../shared.tsbuildinfo"}}"#,
    )
    .unwrap();
    fs::write(
        directory.0.join("app/tsconfig.json"),
        r#"{"files":["index.ts"],"references":[{"path":"../lib"}],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist","tsBuildInfoFile":"../shared.tsbuildinfo"}}"#,
    )
    .unwrap();
    fs::write(directory.0.join("lib/index.ts"), "export const lib = 1;\n").unwrap();
    fs::write(directory.0.join("app/index.ts"), "export const app = 1;\n").unwrap();
    let build_info = directory.0.join("shared.tsbuildinfo");
    fs::write(&build_info, "existing incremental state").unwrap();

    for arguments in [
        &["--build", "--pretty", "false"][..],
        &["--build", "--force", "--pretty", "false"][..],
    ] {
        let output = run(&directory.0, arguments);

        assert_eq!(output.status.code(), Some(1));
        assert!(
            String::from_utf8_lossy(&output.stdout).contains("error TS6377:"),
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
        assert_eq!(
            fs::read_to_string(&build_info).unwrap(),
            "existing incremental state"
        );
        assert!(!directory.0.join("lib/dist/index.js").exists());
        assert!(!directory.0.join("app/dist/index.js").exists());
    }
}

#[test]
fn build_clean_removes_outputs_and_incremental_state() {
    let directory = TestDirectory::new("clean");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist","tsBuildInfoFile":"cache/state.tsbuildinfo"}}"#,
    )
    .unwrap();
    fs::write(directory.0.join("main.ts"), "export const value = 1;\n").unwrap();
    assert!(
        run(&directory.0, &["--build", "--pretty", "false"])
            .status
            .success()
    );
    assert!(directory.0.join("dist/main.js").is_file());
    assert!(directory.0.join("cache/state.tsbuildinfo").is_file());

    let cleaned = run(&directory.0, &["--build", "--clean", "--pretty", "false"]);

    assert!(
        cleaned.status.success(),
        "{}",
        String::from_utf8_lossy(&cleaned.stdout)
    );
    assert!(!directory.0.join("dist/main.js").exists());
    assert!(!directory.0.join("cache/state.tsbuildinfo").exists());
    assert!(directory.0.join("main.ts").is_file());
}

#[test]
fn clean_cannot_delete_project_input_used_as_build_info() {
    let directory = TestDirectory::new("clean-build-info-input-collision");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist","tsBuildInfoFile":"main.ts"}}"#,
    )
    .unwrap();
    let source = directory.0.join("main.ts");
    let original_source = "export const value = 1;\n";
    fs::write(&source, original_source).unwrap();
    let generated_output = directory.0.join("dist/main.js");
    fs::create_dir_all(generated_output.parent().unwrap()).unwrap();
    fs::write(&generated_output, "generated output").unwrap();

    let output = run(&directory.0, &["--build", "--clean", "--pretty", "false"]);

    assert!(output.status.success());
    assert_eq!(fs::read_to_string(&source).unwrap(), original_source);
    assert!(!generated_output.exists());
}

#[test]
fn build_dry_run_never_creates_or_removes_outputs() {
    let directory = TestDirectory::new("dry-run");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist"}}"#,
    )
    .unwrap();
    fs::write(directory.0.join("main.ts"), "export const value = 1;\n").unwrap();
    let output = directory.0.join("dist/main.js");
    let build_info = directory.0.join("dist/tsconfig.tsbuildinfo");

    let dry_build = run(
        &directory.0,
        &["--build", "--dry", "--quiet", "--pretty", "false"],
    );
    assert!(dry_build.status.success());
    assert!(!output.exists());
    assert!(!build_info.exists());

    assert!(
        run(&directory.0, &["--build", "--pretty", "false"])
            .status
            .success()
    );
    let dry_clean = run(
        &directory.0,
        &[
            "--build", "--clean", "--dry", "--quiet", "--pretty", "false",
        ],
    );
    assert!(dry_clean.status.success());
    assert!(output.is_file());
    assert!(build_info.is_file());
}

#[test]
fn build_help_exits_successfully() {
    let directory = TestDirectory::new("help");
    let output = run(&directory.0, &["--build", "--help"]);

    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("--build"));
}

#[test]
fn quiet_build_preserves_failure_status_without_printing_diagnostics() {
    let directory = TestDirectory::new("quiet");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"noLib":true}}"#,
    )
    .unwrap();
    fs::write(directory.0.join("main.ts"), "const value: string = 1;\n").unwrap();

    let output = run(
        &directory.0,
        &["--build", "--quiet", "--noEmit", "--pretty", "false"],
    );

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
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
    let library_info = directory.0.join("packages/lib/dist/tsconfig.tsbuildinfo");
    let application_info = directory.0.join("packages/app/dist/tsconfig.tsbuildinfo");
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

#[test]
fn default_build_info_in_out_dir_supports_force_and_clean() {
    let directory = TestDirectory::new("default-build-info");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist"}}"#,
    )
    .unwrap();
    fs::write(directory.0.join("main.ts"), "export const value = 1;\n").unwrap();
    let arguments = ["--build", "--pretty", "false"];
    assert!(run(&directory.0, &arguments).status.success());

    let output = directory.0.join("dist/main.js");
    let build_info = directory.0.join("dist/tsconfig.tsbuildinfo");
    assert!(build_info.is_file());
    assert!(!directory.0.join("tsconfig.tsbuildinfo").exists());

    fs::write(&output, "up-to-date sentinel").unwrap();
    assert!(run(&directory.0, &arguments).status.success());
    assert_eq!(fs::read_to_string(&output).unwrap(), "up-to-date sentinel");

    let forced = run(&directory.0, &["--build", "--force", "--pretty", "false"]);
    assert!(forced.status.success());
    assert_ne!(fs::read_to_string(&output).unwrap(), "up-to-date sentinel");
    assert!(build_info.is_file());

    let cleaned = run(&directory.0, &["--build", "--clean", "--pretty", "false"]);
    assert!(cleaned.status.success());
    assert!(!output.exists());
    assert!(!build_info.exists());
}

#[test]
fn nested_configs_keep_build_info_relative_to_root_dir() {
    let directory = TestDirectory::new("nested-build-info");
    let project = directory.0.join("packages/app");
    fs::create_dir_all(&project).unwrap();
    fs::write(
        project.join("tsconfig.app.json"),
        r#"{"files":["index.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"../../dist","rootDir":".."}}"#,
    )
    .unwrap();
    fs::write(project.join("index.ts"), "export const value = 1;\n").unwrap();

    let arguments = [
        "--build",
        "packages/app/tsconfig.app.json",
        "--pretty",
        "false",
    ];
    let built = run(&directory.0, &arguments);
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stdout)
    );

    let output = directory.0.join("dist/app/index.js");
    let build_info = directory.0.join("dist/app/tsconfig.app.tsbuildinfo");
    assert!(output.is_file());
    assert!(build_info.is_file());
    assert!(!project.join("tsconfig.app.tsbuildinfo").exists());

    let cleaned = run(
        &directory.0,
        &[
            "--build",
            "packages/app/tsconfig.app.json",
            "--clean",
            "--pretty",
            "false",
        ],
    );
    assert!(cleaned.status.success());
    assert!(!output.exists());
    assert!(!build_info.exists());
}

#[test]
fn implementation_only_changes_do_not_rebuild_consumers() {
    let directory = TestDirectory::new("implementation-signature");
    write_project(&directory.0);
    fs::write(
        directory.0.join("packages/lib/index.ts"),
        "export function libraryValue(): number { return 1; }\n",
    )
    .unwrap();
    let arguments = ["--build", "--incremental", "--pretty", "false"];
    assert!(run(&directory.0, &arguments).status.success());
    let library_output = directory.0.join("packages/lib/dist/index.js");
    let application_output = directory.0.join("packages/app/dist/index.js");
    fs::write(&library_output, "library sentinel").unwrap();
    fs::write(&application_output, "application sentinel").unwrap();

    fs::write(
        directory.0.join("packages/lib/index.ts"),
        "export function libraryValue(): number { return 2; }\n",
    )
    .unwrap();
    assert!(run(&directory.0, &arguments).status.success());
    assert_ne!(
        fs::read_to_string(library_output).unwrap(),
        "library sentinel"
    );
    assert_eq!(
        fs::read_to_string(application_output).unwrap(),
        "application sentinel"
    );
}

#[test]
fn stale_or_missing_outputs_are_rebuilt_with_deterministic_build_info() {
    let directory = TestDirectory::new("output-freshness");
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist"}}"#,
    )
    .unwrap();
    let source = directory.0.join("main.ts");
    fs::write(&source, "export const value: number = 1;\n").unwrap();
    let arguments = ["--build", "--pretty", "false"];
    assert!(run(&directory.0, &arguments).status.success());
    let output = directory.0.join("dist/main.js");
    let build_info = directory.0.join("dist/tsconfig.tsbuildinfo");
    let original_build_info = fs::read_to_string(&build_info).unwrap();

    fs::remove_file(&output).unwrap();
    assert!(run(&directory.0, &arguments).status.success());
    assert!(output.is_file());
    assert_eq!(
        fs::read_to_string(&build_info).unwrap(),
        original_build_info
    );

    fs::write(&output, "stale sentinel").unwrap();
    fs::write(&source, "export const value: number = 1;\n").unwrap();
    assert!(run(&directory.0, &arguments).status.success());
    assert_ne!(fs::read_to_string(output).unwrap(), "stale sentinel");
    assert_eq!(fs::read_to_string(build_info).unwrap(), original_build_info);
}
