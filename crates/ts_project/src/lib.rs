//! Project-reference graph loading and conservative ordered builds.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};

use ts_compiler::{EmitOutput, Program, ProgramOptionsOverride};
use ts_config::resolve_config_file;
use ts_core::TextRange;
use ts_diagnostics::message_by_code;
use ts_incremental::{BuildDecision, BuildInfo, hash_text};
use ts_path::{change_extension, is_absolute, normalize_path, resolve_path};
use ts_printer::emit_declaration_file;
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
    pub references: BTreeMap<String, Vec<String>>,
    pub diagnostics: Vec<ProjectDiagnostic>,
    pub has_cycle: bool,
}

/// One project compiled as part of a build.
#[derive(Debug)]
pub struct CompiledProject {
    pub config_path: String,
    pub program: Program,
    pub emit: EmitOutput,
    pub build_info: Option<IncrementalOutput>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IncrementalOutput {
    pub file_name: String,
    pub text: String,
}

/// Result of loading and compiling a project graph.
#[derive(Debug, Default)]
pub struct BuildResult {
    pub graph: ProjectGraph,
    pub projects: Vec<CompiledProject>,
    pub skipped: Vec<String>,
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
    incremental: bool,
) -> BuildResult {
    let graph = load_project_graph(file_system, current_directory, roots);
    if !graph.diagnostics.is_empty() {
        return BuildResult {
            graph,
            projects: Vec::new(),
            skipped: Vec::new(),
        };
    }
    let mut projects = Vec::new();
    let mut skipped = Vec::new();
    let mut signatures: BTreeMap<String, String> = BTreeMap::new();
    for config_path in &graph.projects {
        let program = Program::from_config_with_options(file_system, config_path, overrides);
        let enabled = incremental || program.options().incremental || program.options().composite;
        let dependencies = graph
            .references
            .get(config_path)
            .into_iter()
            .flatten()
            .filter_map(|path| {
                signatures
                    .get(path)
                    .map(|signature| (path.clone(), signature.clone()))
            })
            .collect::<BTreeMap<_, _>>();
        let build_info_path = ts_outputpaths::build_info_path(program.options())
            .unwrap_or_else(|| change_extension(config_path, ".tsbuildinfo"));
        let previous = enabled
            .then(|| {
                file_system
                    .read_file(&build_info_path)
                    .ok()
                    .and_then(|source| {
                        BuildInfo::from_json(&source, env!("CARGO_PKG_VERSION")).ok()
                    })
            })
            .flatten();
        let preliminary = project_build_info(
            &program,
            dependencies.clone(),
            previous
                .as_ref()
                .map_or_else(Vec::new, |info| info.outputs.clone()),
        );
        if enabled
            && BuildInfo::decision(previous.as_ref(), &preliminary, |path| {
                output_is_current(file_system, path, config_path, &preliminary)
            }) == BuildDecision::UpToDate
            && output_is_current(file_system, &build_info_path, config_path, &preliminary)
        {
            signatures.insert(config_path.clone(), preliminary.project_signature());
            skipped.push(config_path.clone());
            continue;
        }
        let emit = program.emit();
        let current = project_build_info(
            &program,
            dependencies,
            emit.files
                .iter()
                .map(|output| output.file_name.clone())
                .collect(),
        );
        signatures.insert(config_path.clone(), current.project_signature());
        let build_info =
            (enabled && program.diagnostics().is_empty() && emit.diagnostics.is_empty())
                .then(|| {
                    current.to_json().ok().map(|text| IncrementalOutput {
                        file_name: build_info_path,
                        text,
                    })
                })
                .flatten();
        projects.push(CompiledProject {
            config_path: config_path.clone(),
            program,
            emit,
            build_info,
        });
    }
    BuildResult {
        graph,
        projects,
        skipped,
    }
}

fn project_build_info(
    program: &Program,
    dependencies: BTreeMap<String, String>,
    outputs: Vec<String>,
) -> BuildInfo {
    BuildInfo::new(
        env!("CARGO_PKG_VERSION"),
        &format!("{:?}", program.options()),
        program
            .source_files()
            .iter()
            .filter(|source| !source.is_default_library)
            .map(|source| (source.file_name.clone(), source.source_text.clone())),
        dependencies,
        outputs,
    )
    .with_declaration_signature(declaration_signature(program))
}

fn declaration_signature(program: &Program) -> String {
    let mut declarations = program
        .source_files()
        .iter()
        .filter(|source| !source.is_default_library)
        .map(|source| {
            let text = if ts_path::is_declaration_file(&source.file_name) {
                source.source_text.clone()
            } else {
                emit_declaration_file(
                    &source.parse.arena,
                    source.parse.source_file,
                    &source.file_name,
                    &source.source_text,
                    false,
                )
                .map_or_else(|_| source.source_text.clone(), |emitted| emitted.code)
            };
            (source.file_name.as_str(), text)
        })
        .collect::<Vec<_>>();
    declarations.sort_by_key(|(path, _)| *path);
    let mut serialized = String::new();
    for (path, text) in declarations {
        serialized.push_str(&path.len().to_string());
        serialized.push(':');
        serialized.push_str(path);
        serialized.push_str(&text.len().to_string());
        serialized.push(':');
        serialized.push_str(&text);
    }
    hash_text(&serialized)
}

fn output_is_current(
    file_system: &dyn FileSystem,
    output: &str,
    config_path: &str,
    info: &BuildInfo,
) -> bool {
    let Some(output_time) = file_system.modified_time(output) else {
        return false;
    };
    info.files
        .keys()
        .map(String::as_str)
        .chain(std::iter::once(config_path))
        .filter_map(|path| file_system.modified_time(path))
        .all(|input_time| input_time <= output_time)
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
            let references = config
                .resolved_references(self.file_system)
                .into_iter()
                .map(|reference| resolve_config_path(self.file_system, "/", &reference.path))
                .collect::<Vec<_>>();
            self.graph
                .references
                .insert(config_path.clone(), references.clone());
            for reference_path in references {
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
    use ts_compiler::ProgramOptionsOverride;
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::{BuildResult, build_projects, load_project_graph};

    fn write_build_outputs(file_system: &MemoryFileSystem, result: BuildResult) {
        for project in result.projects {
            for output in project.emit.files {
                file_system
                    .write_file(&output.file_name, &output.text)
                    .unwrap();
            }
            if let Some(build_info) = project.build_info {
                file_system
                    .write_file(&build_info.file_name, &build_info.text)
                    .unwrap();
            }
        }
    }

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

    #[test]
    fn only_declaration_changes_invalidate_consumers() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"files":[],"include":[],"references":[{"path":"./app"},{"path":"./lib"}]}"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/lib/tsconfig.json",
            r#"{"files":["index.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist"}}"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/lib/index.ts",
            "export function value(): number { return 1; }\n",
        )
        .unwrap();
        fs.write_file(
            "/repo/app/tsconfig.json",
            r#"{"files":["index.ts"],"references":[{"path":"../lib"}],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist"}}"#,
        )
        .unwrap();
        fs.write_file("/repo/app/index.ts", "export const app = true;\n")
            .unwrap();

        write_build_outputs(
            &fs,
            build_projects(
                &fs,
                "/repo",
                &["tsconfig.json".into()],
                ProgramOptionsOverride::default(),
                true,
            ),
        );
        fs.write_file(
            "/repo/lib/index.ts",
            "export function value(): number { return 2; }\n",
        )
        .unwrap();
        let implementation_change = build_projects(
            &fs,
            "/repo",
            &["tsconfig.json".into()],
            ProgramOptionsOverride::default(),
            true,
        );
        assert_eq!(
            implementation_change
                .projects
                .iter()
                .map(|project| project.config_path.as_str())
                .collect::<Vec<_>>(),
            ["/repo/lib/tsconfig.json"]
        );
        assert_eq!(
            implementation_change.projects[0].config_path,
            "/repo/lib/tsconfig.json"
        );
        write_build_outputs(&fs, implementation_change);

        fs.write_file(
            "/repo/lib/index.ts",
            "export function value(): string { return 'two'; }\n",
        )
        .unwrap();
        let declaration_change = build_projects(
            &fs,
            "/repo",
            &["tsconfig.json".into()],
            ProgramOptionsOverride::default(),
            true,
        );
        assert_eq!(declaration_change.projects.len(), 3);
        assert!(declaration_change.skipped.is_empty());
    }
}
