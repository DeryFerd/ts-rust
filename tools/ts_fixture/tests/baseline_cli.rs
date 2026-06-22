use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TestRepository(PathBuf);

impl TestRepository {
    fn new() -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ts-fixture-cli-{}-{sequence}", std::process::id()));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(path.join("tests/cases/compiler")).unwrap();
        fs::create_dir_all(path.join("tests/baselines/reference")).unwrap();
        Self(path)
    }

    fn write_case(&self, name: &str, source: &str, baseline: Option<&str>) {
        fs::write(
            self.0
                .join("tests/cases/compiler")
                .join(format!("{name}.ts")),
            source,
        )
        .unwrap();
        if let Some(baseline) = baseline {
            fs::write(
                self.0
                    .join("tests/baselines/reference")
                    .join(format!("{name}.js")),
                baseline,
            )
            .unwrap();
        }
    }

    fn write_baseline(&self, file_name: &str, baseline: &str) {
        fs::write(
            self.0.join("tests/baselines/reference").join(file_name),
            baseline,
        )
        .unwrap();
    }
}

impl Drop for TestRepository {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn run(repository: &Path, arguments: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_ts_fixture_baseline"))
        .args(arguments)
        .env("TS_GO_REPO", repository)
        .output()
        .unwrap()
}

#[test]
fn filters_limits_and_reports_matches() {
    let repository = TestRepository::new();
    repository.write_case(
        "matching",
        "// @target: esnext\n// @module: esnext\n// @noLib: true\nconst value: number = 1;\n",
        Some("//// [matching.js] ////\n\"use strict\";\nconst value = 1;\n"),
    );
    repository.write_case("ignored", "// @noLib: true\nconst ignored = 1;\n", None);
    let output = run(&repository.0, &["--filter", "matching", "--limit", "1"]);
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "summary: matched=1 mismatched=0 missing=0 content=0 missing_sections=0 unexpected_sections=0 diagnostics=0\n"
    );
}

#[test]
fn reports_the_first_actionable_mismatch() {
    let repository = TestRepository::new();
    repository.write_case(
        "mismatch",
        "// @target: esnext\n// @module: esnext\n// @noLib: true\nconst value: number = 1;\n",
        Some("//// [mismatch.js] ////\n\"use strict\";\nconst value = 2;\n"),
    );
    let output = run(&repository.0, &[]);
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("MISMATCH tests/cases/compiler/mismatch.ts"));
    assert!(stdout.contains("differs at line 2"));
    assert!(stdout.contains("expected \"const value = 2;\""));
    assert!(stdout.contains("actual \"const value = 1;\""));
    assert!(stdout.contains(
        "summary: matched=0 mismatched=1 missing=0 content=1 missing_sections=0 unexpected_sections=0 diagnostics=0"
    ));
}

#[test]
fn reports_missing_baselines() {
    let repository = TestRepository::new();
    repository.write_case("missing", "// @noLib: true\nconst value = 1;\n", None);
    let output = run(&repository.0, &[]);
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("MISSING tests/cases/compiler/missing.ts"));
    assert!(stdout.contains(
        "summary: matched=0 mismatched=0 missing=1 content=0 missing_sections=0 unexpected_sections=0 diagnostics=0"
    ));
}

#[test]
fn compiles_and_matches_option_variants() {
    let repository = TestRepository::new();
    repository.write_case(
        "matrix",
        "// @target: es5, esnext\n// @module: esnext\n// @noLib: true\nconst value = 1;\n",
        None,
    );
    repository.write_baseline(
        "matrix(target=es5).js",
        "//// [matrix.js] ////\n\"use strict\";\nvar value = 1;\n",
    );
    repository.write_baseline(
        "matrix(target=esnext).js",
        "//// [matrix.js] ////\n\"use strict\";\nconst value = 1;\n",
    );
    let output = run(&repository.0, &[]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "summary: matched=2 mismatched=0 missing=0 content=0 missing_sections=0 unexpected_sections=0 diagnostics=0\n"
    );
}

#[test]
fn reports_compilation_diagnostic_for_missing_emitted_section() {
    let repository = TestRepository::new();
    repository.write_case(
        "diagnostic",
        concat!(
            "// @noLib: true\n",
            "// @noEmitOnError: true\n",
            "const value: string = 1;\n",
        ),
        Some("//// [diagnostic.js] ////\nvar value = 1;\n"),
    );
    let output = run(&repository.0, &[]);
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("MISMATCH tests/cases/compiler/diagnostic.ts: diagnostic TS2322"));
    assert!(stdout.contains("/case/diagnostic.ts"));
    assert!(stdout.contains("Type '1' is not assignable to type 'string'."));
    assert!(stdout.contains(
        "summary: matched=0 mismatched=1 missing=0 content=0 missing_sections=0 unexpected_sections=0 diagnostics=1"
    ));
}

#[test]
fn prioritizes_emit_diagnostic_for_unsupported_output() {
    let repository = TestRepository::new();
    repository.write_case(
        "unsupported",
        "// @noLib: true\nnamespace N { export const value = 1; }\n",
        Some("//// [unsupported.js] ////\nvar N;\n"),
    );
    let output = run(&repository.0, &[]);
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("diagnostic no code /case/unsupported.ts"));
    assert!(stdout.contains("unsupported ModuleDeclaration node"));
    assert!(stdout.contains("diagnostics=1"));
}

#[test]
fn counts_missing_and_unexpected_output_sections() {
    let repository = TestRepository::new();
    repository.write_case(
        "missingSection",
        "// @noEmit: true\nconst value = 1;\n",
        Some("//// [missingSection.js] ////\nvar value = 1;\n"),
    );
    let missing = run(&repository.0, &["--filter", "missingSection"]);
    assert_eq!(missing.status.code(), Some(1));
    assert!(
        String::from_utf8(missing.stdout)
            .unwrap()
            .contains("content=0 missing_sections=1 unexpected_sections=0 diagnostics=0")
    );

    repository.write_case(
        "unexpectedSection",
        "// @declaration: true\nconst value = 1;\n",
        Some("//// [unexpectedSection.js] ////\n\"use strict\";\nvar value = 1;\n"),
    );
    let unexpected = run(&repository.0, &["--filter", "unexpectedSection"]);
    assert_eq!(unexpected.status.code(), Some(1));
    assert!(
        String::from_utf8(unexpected.stdout)
            .unwrap()
            .contains("content=0 missing_sections=0 unexpected_sections=1 diagnostics=0")
    );
}
