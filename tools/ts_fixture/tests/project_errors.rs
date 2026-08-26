use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};

use ts_fixture::project::{ProjectDiagnosticArtifact, ProjectReport, ProjectStage, run_project};

struct TestProject(PathBuf);

impl TestProject {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "ts-project-errors-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, text: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, text).unwrap();
        path
    }

    fn run(&self, config: &str) -> ProjectReport {
        run_project(
            &self.write("tsconfig.json", config),
            None,
            "error-render-test",
        )
        .unwrap()
    }
}

impl Drop for TestProject {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn diagnostics(report: &ProjectReport) -> &ProjectDiagnosticArtifact {
    let ProjectStage::Complete { value } = &report.cold.diagnostics else {
        panic!("missing diagnostics: {:?}", report.cold.diagnostics);
    };
    value
}

#[test]
fn project_error_text_is_owned_and_compared_after_source_replay() {
    let project = TestProject::new();
    let source = project.write(
        "input.ts",
        "const prefix = \"\u{1f642}\";\r\nconst value: number = \"wrong\";\r\n",
    );
    let report =
        project.run(r#"{"compilerOptions":{"noLib":true,"noEmit":true},"files":["input.ts"]}"#);
    assert!(!report.has_invariant_failure());
    let errors = diagnostics(&report);
    assert!(
        errors
            .records
            .iter()
            .any(|diagnostic| diagnostic.code == Some(2322))
    );
    assert_eq!(errors.errors_file_order, [source.to_str().unwrap()]);
    let ProjectStage::Complete { value: text } = &errors.pinned_error_baseline else {
        panic!("missing error text: {:?}", errors.pinned_error_baseline);
    };
    assert!(
        text.text
            .contains("error TS2322: Type 'string' is not assignable to type 'number'.")
    );
    assert!(
        text.text
            .contains(&format!("==== {} (1 errors) ====", source.display()))
    );
    assert_eq!(text.byte_count, text.text.len());
    let ProjectStage::Complete { value: equality } = &report.replay_equality else {
        panic!("missing replay comparison");
    };
    assert_eq!(equality.error_bytes, Some(true));
    assert_eq!(equality.errors_file_order, Some(true));
    assert!(matches!(
        equality.fresh_diagnostics,
        ProjectStage::Unavailable { .. }
    ));
    assert!(matches!(
        report.cross_implementation_comparison,
        ProjectStage::Unavailable { .. }
    ));
}

#[test]
fn project_error_text_appends_the_retained_config_after_source_inputs() {
    let project = TestProject::new();
    let source = project.write("input.ts", "const value = 1;\n");
    let report = project.run(r#"{"compilerOptions":{"noLib":true,"noCheck":true,"jsxFactory":"Element.createElement="},"files":["input.ts"]}"#);
    let errors = diagnostics(&report);
    let config = project.0.join("tsconfig.json");
    assert_eq!(
        errors.errors_file_order,
        [source.to_str().unwrap(), config.to_str().unwrap()]
    );
    assert!(
        errors
            .records
            .iter()
            .any(|diagnostic| diagnostic.code == Some(5067))
    );
    let ProjectStage::Complete { value: text } = &errors.pinned_error_baseline else {
        panic!("missing config text: {:?}", errors.pinned_error_baseline);
    };
    assert!(text.text.contains(&format!("{}(1,", config.display())));
    assert!(
        text.text
            .find(&format!("==== {}", source.display()))
            .unwrap()
            < text
                .text
                .find(&format!("==== {}", config.display()))
                .unwrap()
    );
    let ProjectStage::Complete { value: graph } = &report.graph else {
        panic!("missing graph");
    };
    assert!(
        graph
            .missing_evidence
            .contains(&"config_parse_inputs".to_owned())
    );
    assert!(matches!(
        report.construction,
        ProjectStage::Unavailable { .. }
    ));
}

#[test]
fn empty_project_errors_have_no_text_or_digest() {
    let project = TestProject::new();
    project.write("input.ts", "const value = 1;\n");
    let report =
        project.run(r#"{"compilerOptions":{"noLib":true,"noCheck":true},"files":["input.ts"]}"#);
    let errors = diagnostics(&report);
    assert!(errors.records.is_empty());
    assert!(errors.errors_file_order.is_empty());
    assert!(matches!(
        errors.pinned_error_baseline,
        ProjectStage::NoContent { .. }
    ));
    let value = serde_json::to_value(&errors.pinned_error_baseline).unwrap();
    assert_eq!(value["status"], "no_content");
    assert!(value.get("value").is_none());
    assert!(value.get("text").is_none());
    assert!(value.get("digest").is_none());
    assert!(matches!(
        report.construction,
        ProjectStage::Unavailable { .. }
    ));
}

#[test]
fn config_diagnostics_without_retained_ranges_have_no_error_text() {
    let project = TestProject::new();
    project.write("input.ts", "const value = 1;\n");
    let report = project.run(r#"{"compilerOptions":{"noLib":true,"noCheck":true,"target":"not-a-target"},"files":["input.ts"]}"#);
    let errors = diagnostics(&report);
    assert!(
        errors
            .records
            .iter()
            .any(|diagnostic| diagnostic.code == Some(6046) && diagnostic.range.is_none())
    );
    assert!(
        matches!(&errors.pinned_error_baseline, ProjectStage::Unavailable { detail } if detail.contains("byte range"))
    );
    let value = serde_json::to_value(&errors.pinned_error_baseline).unwrap();
    assert!(value.get("value").is_none());
}
