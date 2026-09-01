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
        !graph
            .missing_evidence
            .contains(&"config_parse_inputs".to_owned())
    );
    assert_eq!(
        graph.evidence["configResolutionObservation"]["retentionComplete"],
        true
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

#[test]
fn census_failure_locations_use_the_typed_node_not_the_requested_root() {
    use ts_ast::{NodeRef, SyntaxKind};
    use ts_checker::semantic::{DeclaredTypeError, SourceCheckError, TypeNodeUnavailable};
    use ts_compiler::{CanonicalCensusPhase, CanonicalProgramCheckError, Program};
    use ts_fixture::project::ProjectCensusFailure;
    use ts_options::CompilerOptions;
    use ts_vfs::{FileSystem, MemoryFileSystem};

    let fs = MemoryFileSystem::new(true);
    fs.write_file("/census/root.ts", "const root = 1;\n")
        .unwrap();
    fs.write_file(
        "/census/dependency.ts",
        "const prefix = \"\u{1f642}\";\nconst dependency = 1;\n",
    )
    .unwrap();
    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/census",
        &["root.ts".to_owned(), "dependency.ts".to_owned()],
        CompilerOptions {
            no_lib: true,
            no_check: true,
            ..Default::default()
        },
    )
    .unwrap();
    let source = program.source_file("/census/dependency.ts").unwrap();
    let (id, node) = source
        .parse
        .arena
        .iter()
        .find(|(_, node)| {
            node.kind == SyntaxKind::Identifier
                && source
                    .source_text
                    .get(node.range.start.get() as usize..node.range.end.get() as usize)
                    == Some("dependency")
        })
        .unwrap();
    let reference = NodeRef::new(source.parse.arena.id(), source.id, id);
    let error = CanonicalProgramCheckError::SourceCheck {
        file_name: "/census/root.ts".to_owned(),
        error: SourceCheckError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(
            TypeNodeUnavailable::MissingTypeReference(reference),
        )),
    };
    let failure =
        ProjectCensusFailure::from_error(Some(&program), CanonicalCensusPhase::Source, &error);
    assert_eq!(failure.phase, "source");
    assert_eq!(failure.returned_error, format!("{error:?}"));
    assert_eq!(failure.detail, error.to_string());
    assert_eq!(failure.code, error.failure_class().code());
    assert_eq!(
        failure.reported_file_name.as_deref(),
        Some("/census/root.ts")
    );
    let location = failure.location.unwrap();
    assert_eq!(location.file_name, "/census/dependency.ts");
    assert_eq!(location.file_id, source.id.index());
    assert_eq!(location.syntax_kind, "Identifier");
    assert_eq!(location.start_byte, node.range.start.get());
    assert_eq!(location.end_byte, node.range.end.get());
    assert!(failure.location_unavailable.is_none());
}

#[test]
fn census_failure_locations_reject_foreign_nodes_and_do_not_infer_from_file_ids() {
    use ts_ast::NodeRef;
    use ts_checker::semantic::SourceCheckError;
    use ts_compiler::{CanonicalCensusPhase, CanonicalProgramCheckError, Program};
    use ts_fixture::project::ProjectCensusFailure;
    use ts_options::CompilerOptions;
    use ts_vfs::{FileSystem, MemoryFileSystem};

    let fs = MemoryFileSystem::new(true);
    fs.write_file("/census/input.ts", "const value = 1;\n")
        .unwrap();
    let make = || {
        Program::try_new_with_canonical_checker(
            &fs,
            "/census",
            &["input.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                no_check: true,
                ..Default::default()
            },
        )
        .unwrap()
    };
    let first = make();
    let other = make();
    let source = other.source_file("/census/input.ts").unwrap();
    let node = NodeRef::new(source.parse.arena.id(), source.id, source.parse.source_file);
    assert!(first.node(node).is_none());
    let error = CanonicalProgramCheckError::SourceCheck {
        file_name: "/census/input.ts".to_owned(),
        error: SourceCheckError::Call(node),
    };
    let foreign =
        ProjectCensusFailure::from_error(Some(&first), CanonicalCensusPhase::Source, &error);
    assert!(foreign.location.is_none());
    assert!(
        foreign
            .location_unavailable
            .as_deref()
            .unwrap()
            .contains("valid retained Program range")
    );
    assert_eq!(foreign.returned_error, format!("{error:?}"));
    let no_program = ProjectCensusFailure::from_error(None, CanonicalCensusPhase::Source, &error);
    assert!(no_program.location.is_none());
    assert!(
        no_program
            .location_unavailable
            .as_deref()
            .unwrap()
            .contains("No loaded Program")
    );
    let error = CanonicalProgramCheckError::MissingBoundFile {
        file_name: "/census/input.ts".to_owned(),
        file: first.source_file("/census/input.ts").unwrap().id,
    };
    let no_node =
        ProjectCensusFailure::from_error(Some(&first), CanonicalCensusPhase::Binding, &error);
    assert!(no_node.location.is_none());
    assert!(no_node.location_unavailable.is_some());
    assert_eq!(no_node.phase, "binding");
    assert_eq!(no_node.returned_error, format!("{error:?}"));
}

#[test]
fn census_callable_invariant_location_keeps_the_retained_node_and_error() {
    use ts_ast::{NodeRef, SyntaxKind};
    use ts_checker::semantic::{SourceCheckError, SourceFunctionInvariant};
    use ts_compiler::{CanonicalCensusPhase, CanonicalProgramCheckError, Program};
    use ts_fixture::project::ProjectCensusFailure;
    use ts_options::CompilerOptions;
    use ts_vfs::{FileSystem, MemoryFileSystem};

    let fs = MemoryFileSystem::new(true);
    fs.write_file("/census/root.ts", "const root = 1;\n")
        .unwrap();
    let prefix = "const prefix = \"\u{1f642}\";\r\nconst ";
    fs.write_file(
        "/census/dependency.ts",
        &format!("{prefix}dependency = 1;\r\n"),
    )
    .unwrap();
    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/census",
        &["root.ts".to_owned(), "dependency.ts".to_owned()],
        CompilerOptions {
            no_lib: true,
            no_check: true,
            ..Default::default()
        },
    )
    .unwrap();
    let source = program.source_file("/census/dependency.ts").unwrap();
    let (id, node) = source
        .parse
        .arena
        .iter()
        .find(|(_, node)| {
            node.kind == SyntaxKind::Identifier
                && source
                    .source_text
                    .get(node.range.start.get() as usize..node.range.end.get() as usize)
                    == Some("dependency")
        })
        .unwrap();
    let reference = NodeRef::new(source.parse.arena.id(), source.id, id);
    let error = CanonicalProgramCheckError::SourceCheck {
        file_name: "/census/root.ts".to_owned(),
        error: SourceCheckError::Function(SourceFunctionInvariant::Callable(reference)),
    };
    let failure =
        ProjectCensusFailure::from_error(Some(&program), CanonicalCensusPhase::Source, &error);
    assert_eq!(failure.phase, "source");
    assert_eq!(failure.class, "invariant");
    assert_eq!(failure.code, "INV.SOURCE.FUNCTION");
    assert_eq!(failure.detail, error.to_string());
    assert_eq!(failure.returned_error, format!("{error:?}"));
    assert_eq!(
        failure.reported_file_name.as_deref(),
        Some("/census/root.ts")
    );
    assert!(failure.location_unavailable.is_none());
    let location = failure.location.unwrap();
    assert_eq!(location.file_name, "/census/dependency.ts");
    assert_eq!(location.file_id, source.id.index());
    assert_eq!(location.syntax_kind, "Identifier");
    assert_eq!(location.start_byte, node.range.start.get());
    assert_eq!(location.end_byte, node.range.end.get());
    assert_ne!(prefix.len(), prefix.chars().count());
    assert_eq!(location.start_byte, u32::try_from(prefix.len()).unwrap());
    assert_eq!(
        location.end_byte,
        u32::try_from(prefix.len() + "dependency".len()).unwrap()
    );
}

#[test]
fn census_callable_invariant_location_rejects_foreign_and_unmapped_nodes() {
    use ts_ast::NodeRef;
    use ts_checker::semantic::{SourceCheckError, SourceFunctionInvariant};
    use ts_compiler::{CanonicalCensusPhase, CanonicalProgramCheckError, Program};
    use ts_fixture::project::ProjectCensusFailure;
    use ts_options::CompilerOptions;
    use ts_vfs::{FileSystem, MemoryFileSystem};

    let fs = MemoryFileSystem::new(true);
    fs.write_file("/census/input.ts", "const value = 1;\n")
        .unwrap();
    let make = || {
        Program::try_new_with_canonical_checker(
            &fs,
            "/census",
            &["input.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                no_check: true,
                ..Default::default()
            },
        )
        .unwrap()
    };
    let first = make();
    let other = make();
    let source = first.source_file("/census/input.ts").unwrap();
    let valid = NodeRef::new(source.parse.arena.id(), source.id, source.parse.source_file);
    let source = other.source_file("/census/input.ts").unwrap();
    let foreign = NodeRef::new(source.parse.arena.id(), source.id, source.parse.source_file);
    assert!(first.node(valid).is_some());
    assert!(other.node(foreign).is_some());
    assert!(first.node(foreign).is_none());
    let error = |invariant| CanonicalProgramCheckError::SourceCheck {
        file_name: "/census/input.ts".to_owned(),
        error: SourceCheckError::Function(invariant),
    };
    let foreign_error = error(SourceFunctionInvariant::Callable(foreign));
    let no_program_error = error(SourceFunctionInvariant::Callable(valid));
    let unmapped_error = error(SourceFunctionInvariant::MissingDeclaration(valid));
    for (program, error, reason) in [
        (
            Some(&first),
            &foreign_error,
            "The returned node does not have a valid retained Program range.",
        ),
        (
            None,
            &no_program_error,
            "No loaded Program is available to validate a location.",
        ),
        (
            Some(&first),
            &unmapped_error,
            "This returned error has no supported typed node location.",
        ),
    ] {
        let failure =
            ProjectCensusFailure::from_error(program, CanonicalCensusPhase::Source, error);
        assert!(failure.location.is_none());
        assert_eq!(failure.location_unavailable.as_deref(), Some(reason));
        assert_eq!(failure.phase, "source");
        assert_eq!(failure.class, "invariant");
        assert_eq!(failure.code, "INV.SOURCE.FUNCTION");
        assert_eq!(failure.detail, error.to_string());
        assert_eq!(failure.returned_error, format!("{error:?}"));
        assert_eq!(
            failure.reported_file_name.as_deref(),
            Some("/census/input.ts")
        );
    }
}
