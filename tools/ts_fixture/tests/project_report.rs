use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};

use ts_fixture::project::{ProjectReport, ProjectStage, run_project};

struct TestProject(PathBuf);

impl TestProject {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "ts-project-report-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, path: &str, text: &str) -> PathBuf {
        let path = self.0.join(path);
        fs::write(&path, text).unwrap();
        path
    }

    fn run(&self, config: &str) -> ProjectReport {
        let path = self.write("tsconfig.json", config);
        run_project(&path, Some("project-test"), "test-process").unwrap()
    }
}

impl Drop for TestProject {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn project_report_forces_replay_and_compares_owned_artifacts_and_identities() {
    let project = TestProject::new();
    project.write("index.ts", "const value: number = 1;\nvalue;\n");
    let report = project.run(
        r#"{
        "compilerOptions": {"noLib": true, "noEmit": true},
        "files": ["index.ts"]
    }"#,
    );
    assert!(matches!(report.construction, ProjectStage::Complete { .. }));
    assert!(!report.has_invariant_failure());
    let ProjectStage::Complete { value: equality } = &report.replay_equality else {
        panic!("replay was not compared: {:?}", report.replay_equality);
    };
    assert!(equality.diagnostic_records);
    assert!(equality.checker_store_identity);
    assert_eq!(equality.type_bytes, Some(true));
    assert_eq!(equality.symbol_bytes, Some(true));
    assert_eq!(equality.type_walk, Some(true));
    assert_eq!(equality.symbol_walk, Some(true));
    assert_eq!(equality.type_identities, Some(true));
    assert_eq!(equality.symbol_identities, Some(true));
    let ProjectStage::Complete { value: graph } = &report.graph else {
        panic!("missing graph");
    };
    assert_eq!(graph.evidence["options"]["no_emit"], true);
    assert_eq!(graph.evidence["options"]["no_lib"], true);
    assert!(
        !graph
            .missing_evidence
            .contains(&"config_extends_inputs".to_owned())
    );
    assert_eq!(
        graph.evidence["configResolutionObservation"]["retentionComplete"],
        true
    );
    assert!(
        graph
            .missing_evidence
            .contains(&"source_real_paths".to_owned())
    );
    assert!(!project.0.join("index.js").exists());
    assert!(matches!(
        report.cross_implementation_comparison,
        ProjectStage::Unavailable { .. }
    ));
    let encoded = serde_json::to_value(&report).unwrap();
    assert!(encoded["cold"]["types"]["walkDigest"].is_string());
    assert!(matches!(
        encoded["cold"]["diagnostics"]["value"]["pinnedErrorBaseline"]["status"].as_str(),
        Some("complete" | "no_content")
    ));
}

#[test]
fn project_report_records_no_check_without_empty_semantic_placeholders() {
    let project = TestProject::new();
    project.write("index.ts", "const value = 1;\n");
    let report = project.run(
        r#"{
        "compilerOptions": {"noLib": true, "noCheck": true},
        "files": ["index.ts"]
    }"#,
    );
    assert!(matches!(
        report.construction,
        ProjectStage::Unavailable { .. }
    ));
    assert!(matches!(report.replay, ProjectStage::Unavailable { .. }));
    assert!(matches!(
        report.cold.types.output,
        ProjectStage::Unavailable { .. }
    ));
    assert_eq!(report.cold.types.visited_nodes, None);
    assert_eq!(report.cold.types.walk_digest, None);
    assert!(
        serde_json::to_value(&report).unwrap()["cold"]["types"]["output"]
            .get("value")
            .is_none()
    );
    assert!(!project.0.join("index.js").exists());
}

#[test]
fn project_report_keeps_unreadable_config_and_unsupported_references_distinct() {
    let project = TestProject::new();
    let missing = run_project(&project.0.join("missing.json"), None, "missing-config").unwrap();
    assert!(matches!(
        missing.construction,
        ProjectStage::Unavailable { .. }
    ));
    let ProjectStage::Complete { value: diagnostics } = &missing.cold.diagnostics else {
        panic!("missing config diagnostic");
    };
    assert!(!diagnostics.records.is_empty());
    project.write("index.ts", "const value = 1;\n");
    let unsupported = project.run(
        r#"{
        "compilerOptions": {"noLib": true, "noEmit": true},
        "files": ["index.ts"], "references": [{"path": "./other"}]
    }"#,
    );
    assert!(matches!(
        unsupported.construction,
        ProjectStage::Unsupported { .. }
    ));
    assert!(matches!(
        unsupported.graph,
        ProjectStage::Unavailable { .. }
    ));
    assert!(matches!(
        unsupported.cold.diagnostics,
        ProjectStage::Unavailable { .. }
    ));
    assert!(matches!(
        unsupported.cold.types.output,
        ProjectStage::Unavailable { .. }
    ));
    assert!(!unsupported.has_invariant_failure());
}

#[test]
fn project_report_keeps_dependency_declarations_in_file_order_and_input_digests() {
    let project = TestProject::new();
    let root = project.write(
        "index.ts",
        "/// <reference path=\"./dependency.d.ts\" />\nconst value = 1;\n",
    );
    let dependency = project.write("dependency.d.ts", "type Dependency = number;\n");
    let report = project.run(
        r#"{
        "compilerOptions": {"noLib": true, "skipLibCheck": true, "noEmit": true},
        "files": ["index.ts"]
    }"#,
    );
    let ProjectStage::Complete { value: graph } = &report.graph else {
        panic!("missing graph");
    };
    assert_eq!(
        graph.evidence["artifactFileOrder"],
        serde_json::json!([root.to_str(), dependency.to_str()])
    );
    let sources = graph.evidence["sources"].as_array().unwrap();
    assert_eq!(sources.len(), 2);
    assert!(sources.iter().all(|source| {
        source["digest"]
            .as_str()
            .is_some_and(|digest| digest.len() == 32)
    }));
    assert!(
        sources
            .iter()
            .any(|source| source["declarationFile"] == true)
    );
}

#[test]
fn project_report_rejects_relative_config_paths() {
    let error = run_project(std::path::Path::new("tsconfig.json"), None, "relative").unwrap_err();
    assert_eq!(error.kind(), std::io::ErrorKind::InvalidInput);
}
