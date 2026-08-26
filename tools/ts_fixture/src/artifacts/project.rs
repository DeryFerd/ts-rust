//! Real project inputs for the pinned type and symbol renderer.

use std::{collections::BTreeSet, error::Error, fmt};

use ts_ast::NodeRef;
use ts_compiler::{CanonicalProgramQueries, Program, SourceFile};

use super::{
    ArtifactIdentity, ArtifactInputKind, ArtifactRenderError, ArtifactWalkError,
    SemanticArtifactKind, SemanticArtifactWalk, artifact_line, render_source_section, walk_source,
};

/// Completed query identities are retained only for same-Program replay checks.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProjectArtifactRun {
    pub(crate) text: Result<String, ArtifactRenderError>,
    pub(crate) visited_nodes: usize,
    pub(crate) rendered_nodes: usize,
    pub(crate) identities: Vec<(NodeRef, ArtifactIdentity)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProjectSemanticArtifacts {
    pub(crate) walk: SemanticArtifactWalk,
    pub(crate) types: ProjectArtifactRun,
    pub(crate) symbols: ProjectArtifactRun,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ProjectArtifactInputError {
    ForeignSource(String),
    DuplicateSource(String),
    DefaultLibrarySource(String),
    MissingSource(String),
    Walk(ArtifactWalkError),
}

impl fmt::Display for ProjectArtifactInputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ForeignSource(path) => {
                write!(
                    formatter,
                    "project artifact source is not owned by this Program: {path}"
                )
            }
            Self::DuplicateSource(path) => {
                write!(
                    formatter,
                    "project artifact order contains a repeated source: {path}"
                )
            }
            Self::DefaultLibrarySource(path) => {
                write!(
                    formatter,
                    "project artifact order contains a default library: {path}"
                )
            }
            Self::MissingSource(path) => {
                write!(
                    formatter,
                    "project artifact order omits a loaded source: {path}"
                )
            }
            Self::Walk(error) => error.fmt(formatter),
        }
    }
}

impl Error for ProjectArtifactInputError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Walk(error) => Some(error),
            _ => None,
        }
    }
}

/// Roots keep config order. Every other loaded non-default source follows by path.
pub(crate) fn ordered_project_sources<'a>(
    program: &'a Program,
    root_file_names: &[String],
) -> Vec<&'a SourceFile> {
    let mut included = BTreeSet::new();
    let mut result = Vec::new();
    for path in root_file_names {
        if let Some(source) = program.source_file(path)
            && !source.is_default_library
            && included.insert(source.id)
        {
            result.push(source);
        }
    }
    let mut remaining = program
        .source_files()
        .iter()
        .filter(|source| !source.is_default_library && !included.contains(&source.id))
        .collect::<Vec<_>>();
    remaining.sort_by(|left, right| left.file_name.cmp(&right.file_name));
    result.extend(remaining);
    result
}

/// Uses the original Program and source text, without fixture input conversion.
pub(crate) fn render_project(
    program: &Program,
    queries: &mut CanonicalProgramQueries<'_>,
    sources: &[&SourceFile],
    header: &str,
    has_diagnostics: bool,
) -> Result<ProjectSemanticArtifacts, ProjectArtifactInputError> {
    validate_sources(program, sources)?;
    let mut walk = SemanticArtifactWalk::default();
    for source in sources {
        walk_source(source, SemanticArtifactKind::Types, &mut walk.types)
            .map_err(ProjectArtifactInputError::Walk)?;
        walk_source(source, SemanticArtifactKind::Symbols, &mut walk.symbols)
            .map_err(ProjectArtifactInputError::Walk)?;
    }
    let has_diagnostics = has_diagnostics || queries.has_diagnostics();
    let types = render_project_baseline(
        program,
        queries,
        sources,
        header,
        SemanticArtifactKind::Types,
        &walk.types,
        has_diagnostics,
    );
    let symbols = render_project_baseline(
        program,
        queries,
        sources,
        header,
        SemanticArtifactKind::Symbols,
        &walk.symbols,
        has_diagnostics,
    );
    Ok(ProjectSemanticArtifacts {
        walk,
        types,
        symbols,
    })
}

fn validate_sources(
    program: &Program,
    sources: &[&SourceFile],
) -> Result<(), ProjectArtifactInputError> {
    let mut seen = BTreeSet::new();
    for source in sources {
        if !program
            .source_file_by_id(source.id)
            .is_some_and(|owned| std::ptr::eq(owned, *source))
        {
            return Err(ProjectArtifactInputError::ForeignSource(
                source.file_name.clone(),
            ));
        }
        if source.is_default_library {
            return Err(ProjectArtifactInputError::DefaultLibrarySource(
                source.file_name.clone(),
            ));
        }
        if !seen.insert(source.id) {
            return Err(ProjectArtifactInputError::DuplicateSource(
                source.file_name.clone(),
            ));
        }
    }
    if let Some(source) = program
        .source_files()
        .iter()
        .find(|source| !source.is_default_library && !seen.contains(&source.id))
    {
        return Err(ProjectArtifactInputError::MissingSource(
            source.file_name.clone(),
        ));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)] // Both artifact kinds use the same ordered walk and renderer.
fn render_project_baseline(
    program: &Program,
    queries: &mut CanonicalProgramQueries<'_>,
    sources: &[&SourceFile],
    header: &str,
    kind: SemanticArtifactKind,
    nodes: &[NodeRef],
    has_diagnostics: bool,
) -> ProjectArtifactRun {
    let mut identities = Vec::with_capacity(nodes.len());
    let mut rendered_nodes = 0;
    let mut sections = String::new();
    let mut remaining = nodes.iter().copied().peekable();
    for source in sources {
        let mut lines = Vec::new();
        while remaining.peek().is_some_and(|node| node.file == source.id) {
            let reference = remaining.next().expect("the next node was just checked");
            match artifact_line(
                program,
                queries,
                source,
                reference,
                kind,
                has_diagnostics,
                ArtifactInputKind::Project,
            ) {
                Ok(result) => {
                    identities.push((reference, result.identity));
                    if let Some(line) = result.line {
                        lines.push(line);
                        rendered_nodes += 1;
                    }
                }
                Err(error) => {
                    return ProjectArtifactRun {
                        text: Err(error),
                        visited_nodes: nodes.len(),
                        rendered_nodes,
                        identities,
                    };
                }
            }
        }
        render_source_section(
            &mut sections,
            &source.file_name,
            &source.source_text,
            &lines,
        );
    }
    let text = if sections.is_empty() {
        "<no content>".to_owned()
    } else {
        format!("//// [{header}] ////\r\n\r\n{sections}")
    };
    ProjectArtifactRun {
        text: Ok(text),
        visited_nodes: nodes.len(),
        rendered_nodes,
        identities,
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicUsize, Ordering},
    };

    use ts_compiler::Program;
    use ts_vfs::OsFileSystem;

    use super::{
        ProjectArtifactInputError, ordered_project_sources, render_project, validate_sources,
    };

    #[test]
    fn project_source_sections_keep_original_crlf_line_positions() {
        let source = "const first = 1;\r\nconst second = 2;\r\n";
        let mut output = String::new();
        super::super::render_source_section(&mut output, "index.ts", source, &[]);
        assert_eq!(output, format!("=== index.ts ===\r\n\r\n{source}\r\n"));
    }

    struct TestProject(PathBuf);

    impl TestProject {
        fn new() -> Self {
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            let path = std::env::temp_dir().join(format!(
                "ts-project-artifacts-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed),
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }

        fn write(&self, name: &str, text: &str) -> String {
            let path = self.0.join(name);
            fs::write(&path, text).unwrap();
            path.to_str().unwrap().to_owned()
        }
    }

    impl Drop for TestProject {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    #[test]
    fn project_artifacts_keep_roots_then_every_loaded_declaration() {
        let project = TestProject::new();
        let second = project.write("second.ts", "const second = 2;\n");
        let first = project.write(
            "first.ts",
            "/// <reference path=\"./z.d.ts\" />\n/// <reference path=\"./a.d.ts\" />\nconst first = 1;\n",
        );
        let a = project.write("a.d.ts", "type A = string;\n");
        let z = project.write("z.d.ts", "type Z = number;\n");
        let config = project.write(
            "tsconfig.json",
            r#"{"compilerOptions":{"noLib":true,"skipLibCheck":true,"noEmit":true},"files":["second.ts","first.ts"]}"#,
        );
        let roots = vec![second, first];
        let expected = vec![roots[0].clone(), roots[1].clone(), a, z];
        let (_, artifacts) = Program::try_from_config_with_canonical_checker_and_queries(
            &OsFileSystem::default(),
            &config,
            |program, queries| {
                let sources = ordered_project_sources(program, &roots);
                assert_eq!(
                    sources
                        .iter()
                        .map(|source| source.file_name.clone())
                        .collect::<Vec<_>>(),
                    expected
                );
                render_project(program, queries, &sources, &config, false)
            },
        )
        .unwrap();
        let artifacts = artifacts.unwrap().unwrap();
        for artifact in [&artifacts.types, &artifacts.symbols] {
            let text = artifact.text.as_ref().unwrap();
            assert!(text.starts_with(&format!("//// [{config}] ////\r\n")));
            let sections = text
                .lines()
                .filter(|line| line.starts_with("=== "))
                .collect::<Vec<_>>();
            let expected = expected
                .iter()
                .map(|path| format!("=== {path} ==="))
                .collect::<Vec<_>>();
            assert_eq!(sections, expected);
            assert_eq!(artifact.identities.len(), artifact.visited_nodes);
        }
    }

    #[test]
    fn project_artifacts_reject_omitted_repeated_and_foreign_sources() {
        let project = TestProject::new();
        project.write("a.ts", "const a = 1;\n");
        project.write("b.ts", "const b = 2;\n");
        let config = project.write(
            "tsconfig.json",
            r#"{"compilerOptions":{"noLib":true,"noEmit":true},"files":["a.ts","b.ts"]}"#,
        );
        let (program, _) = Program::try_from_config_with_canonical_checker_and_queries(
            &OsFileSystem::default(),
            &config,
            |_, _| (),
        )
        .unwrap();
        let (other, _) = Program::try_from_config_with_canonical_checker_and_queries(
            &OsFileSystem::default(),
            &config,
            |_, _| (),
        )
        .unwrap();
        let a = &program.source_files()[0];
        assert!(matches!(
            validate_sources(&program, &[a]),
            Err(ProjectArtifactInputError::MissingSource(_))
        ));
        assert!(matches!(
            validate_sources(&program, &[a, a]),
            Err(ProjectArtifactInputError::DuplicateSource(_))
        ));
        assert!(matches!(
            validate_sources(&program, &[&other.source_files()[0]]),
            Err(ProjectArtifactInputError::ForeignSource(_))
        ));
    }
}
