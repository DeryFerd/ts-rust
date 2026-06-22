//! Project-reference graph loading and conservative ordered builds.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};

use ts_compiler::{EmitOutput, Program, ProgramOptionsOverride};
use ts_config::resolve_config_file;
use ts_core::TextRange;
use ts_diagnostics::message_by_code;
use ts_path::{is_absolute, normalize_path, resolve_path};
use ts_vfs::FileSystem;

/// A diagnostic produced while loading a project graph.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectDiagnostic {
    pub file_name: Option<String>,
    pub range: Option<TextRange>,
    pub code: u32,
    pub message: String,
}

/// Project configurations ordered with every dependency before its consumers.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ProjectGraph {
    pub projects: Vec<String>,
    pub diagnostics: Vec<ProjectDiagnostic>,
    pub has_cycle: bool,
}

/// One project compiled as part of a build.
#[derive(Debug)]
pub struct CompiledProject {
    pub config_path: String,
    pub program: Program,
    pub emit: EmitOutput,
}

/// Result of loading and compiling a project graph.
#[derive(Debug, Default)]
pub struct BuildResult {
    pub graph: ProjectGraph,
    pub projects: Vec<CompiledProject>,
}

/// Loads project references recursively and returns dependency-first order.
#[must_use]
pub fn load_project_graph(
    file_system: &dyn FileSystem,
    current_directory: &str,
    roots: &[String],
) -> ProjectGraph {
    let mut loader = GraphLoader::new(file_system);
    for root in roots {
        let path = resolve_config_path(file_system, current_directory, root);
        loader.visit(&path);
    }
    loader.graph
}

/// Loads and compiles a project graph in dependency order.
#[must_use]
pub fn build_projects(
    file_system: &dyn FileSystem,
    current_directory: &str,
    roots: &[String],
    overrides: ProgramOptionsOverride,
) -> BuildResult {
    let graph = load_project_graph(file_system, current_directory, roots);
    if !graph.diagnostics.is_empty() {
        return BuildResult {
            graph,
            projects: Vec::new(),
        };
    }
    let projects = graph
        .projects
        .iter()
        .map(|config_path| {
            let program = Program::from_config_with_options(file_system, config_path, overrides);
            let emit = program.emit();
            CompiledProject {
                config_path: config_path.clone(),
                program,
                emit,
            }
        })
        .collect();
    BuildResult { graph, projects }
}

struct GraphLoader<'a> {
    file_system: &'a dyn FileSystem,
    graph: ProjectGraph,
    completed: BTreeSet<String>,
    visiting: BTreeMap<String, usize>,
    stack: Vec<String>,
}

impl<'a> GraphLoader<'a> {
    fn new(file_system: &'a dyn FileSystem) -> Self {
        Self {
            file_system,
            graph: ProjectGraph::default(),
            completed: BTreeSet::new(),
            visiting: BTreeMap::new(),
            stack: Vec::new(),
        }
    }

    fn visit(&mut self, config_path: &str) {
        let config_path = normalize_path(config_path);
        if self.completed.contains(&config_path) {
            return;
        }
        if let Some(index) = self.visiting.get(&config_path).copied() {
            self.report_cycle(index);
            return;
        }
        if !self.file_system.file_exists(&config_path) {
            self.report_missing(&config_path);
            self.completed.insert(config_path);
            return;
        }

        self.visiting.insert(config_path.clone(), self.stack.len());
        self.stack.push(config_path.clone());
        let parsed = resolve_config_file(self.file_system, &config_path);
        self.graph
            .diagnostics
            .extend(
                parsed
                    .diagnostics
                    .iter()
                    .map(|diagnostic| ProjectDiagnostic {
                        file_name: Some(diagnostic.file_name.clone()),
                        range: None,
                        code: diagnostic.code(),
                        message: diagnostic.render(),
                    }),
            );
        if let Some(config) = parsed.value {
            for reference in config.resolved_references(self.file_system) {
                let reference_path = resolve_config_path(self.file_system, "/", &reference.path);
                self.visit(&reference_path);
            }
            self.graph.projects.push(config_path.clone());
        }
        self.stack.pop();
        self.visiting.remove(&config_path);
        self.completed.insert(config_path);
    }

    fn report_cycle(&mut self, start: usize) {
        if self.graph.has_cycle {
            return;
        }
        self.graph.has_cycle = true;
        let cycle = self.stack[start..].join("\n");
        self.graph.diagnostics.push(ProjectDiagnostic {
            file_name: None,
            range: None,
            code: 6202,
            message: render_message(6202, &[&cycle]),
        });
    }

    fn report_missing(&mut self, path: &str) {
        self.graph.diagnostics.push(ProjectDiagnostic {
            file_name: None,
            range: None,
            code: 6053,
            message: render_message(6053, &[path]),
        });
    }
}

fn resolve_config_path(
    file_system: &dyn FileSystem,
    current_directory: &str,
    path: &str,
) -> String {
    let path = if is_absolute(path) {
        normalize_path(path)
    } else {
        resolve_path(current_directory, &[path])
    };
    if file_system.directory_exists(&path) || Path::new(&path).extension().is_none() {
        resolve_path(&path, &["tsconfig.json"])
    } else {
        path
    }
}

fn render_message(code: u32, arguments: &[&str]) -> String {
    message_by_code(code)
        .expect("project diagnostic must exist in the generated catalog")
        .format(
            &arguments
                .iter()
                .map(|value| (*value).to_owned())
                .collect::<Vec<_>>(),
        )
        .unwrap_or_else(|error| error.to_string())
}

#[cfg(test)]
mod tests {
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::load_project_graph;

    #[test]
    fn orders_dependencies_before_consumers() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"files":[],"references":[{"path":"./app"},{"path":"./lib"}]}"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/app/tsconfig.json",
            r#"{"files":[],"references":[{"path":"../lib"}]}"#,
        )
        .unwrap();
        fs.write_file("/repo/lib/tsconfig.json", r#"{"files":[]}"#)
            .unwrap();

        let graph = load_project_graph(&fs, "/repo", &["tsconfig.json".into()]);
        assert!(graph.diagnostics.is_empty());
        assert_eq!(
            graph.projects,
            [
                "/repo/lib/tsconfig.json",
                "/repo/app/tsconfig.json",
                "/repo/tsconfig.json"
            ]
        );
    }

    #[test]
    fn detects_cycles() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"files":[],"references":[{"path":"./app"}]}"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/app/tsconfig.json",
            r#"{"files":[],"references":[{"path":".."}]}"#,
        )
        .unwrap();
        let graph = load_project_graph(&fs, "/repo", &["tsconfig.json".into()]);
        assert!(graph.has_cycle);
        assert_eq!(graph.diagnostics[0].code, 6202);
        assert!(
            graph.diagnostics[0]
                .message
                .contains("/repo/app/tsconfig.json")
        );
    }

    #[test]
    fn reports_missing_referenced_configs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"files":[],"references":[{"path":"./missing"}]}"#,
        )
        .unwrap();
        let graph = load_project_graph(&fs, "/repo", &["tsconfig.json".into()]);
        assert_eq!(graph.diagnostics[0].code, 6053);
        assert!(
            graph.diagnostics[0]
                .message
                .contains("missing/tsconfig.json")
        );
    }
}
