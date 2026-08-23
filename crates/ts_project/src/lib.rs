//! Project-reference graph loading and conservative ordered builds.

use std::{
    collections::{BTreeMap, BTreeSet},
    io,
    path::Path,
};

use ts_compiler::{EmitOutput, OutputFile, Program, ProgramOptionsOverride};
use ts_config::{parse_config_file, resolve_config_file};
use ts_core::TextRange;
use ts_diagnostics::message_by_code;
use ts_incremental::{BuildDecision, BuildInfo, hash_text};
use ts_path::{CaseSensitivity, canonicalize, is_absolute, normalize_path, resolve_path};
use ts_printer::emit_declaration_file_with_semantics_and_options;
use ts_vfs::{DirectoryEntries, FileSystem};

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

struct BuildFileSystem<'a> {
    backing: &'a dyn FileSystem,
    outputs: BTreeMap<String, OutputFile>,
}

impl<'a> BuildFileSystem<'a> {
    fn new(backing: &'a dyn FileSystem) -> Self {
        Self {
            backing,
            outputs: BTreeMap::new(),
        }
    }

    fn add_outputs(&mut self, outputs: &[OutputFile]) {
        for output in outputs {
            let key = canonical_config_path(self.backing, &output.file_name);
            self.outputs.insert(key, output.clone());
        }
    }

    fn output(&self, path: &str) -> Option<&OutputFile> {
        self.outputs
            .get(&canonical_config_path(self.backing, path))
            .or_else(|| {
                let real_path = self.resolved_output_path(path);
                self.outputs
                    .get(&canonical_config_path(self.backing, &real_path))
            })
    }

    fn contains_output_directory(&self, path: &str) -> bool {
        let directory = canonical_config_path(self.backing, path);
        let real_directory = canonical_config_path(self.backing, &self.resolved_output_path(path));
        [directory, real_directory].into_iter().any(|directory| {
            let prefix = format!("{}/", directory.trim_end_matches('/'));
            self.outputs
                .keys()
                .any(|output| output.starts_with(&prefix))
        })
    }

    fn resolved_output_path(&self, path: &str) -> String {
        let path = normalize_path(path);
        let mut current = Path::new(&path);
        let mut missing: Vec<String> = Vec::new();
        loop {
            let current_path = current.to_string_lossy();
            let resolved = self.backing.realpath(&current_path);
            if resolved != current_path.as_ref()
                || self.backing.file_exists(&current_path)
                || self.backing.directory_exists(&current_path)
            {
                return missing.iter().rev().fold(resolved, |parent, component| {
                    resolve_path(&parent, &[component])
                });
            }
            let Some(component) = current.file_name() else {
                return path;
            };
            let Some(parent) = current.parent() else {
                return path;
            };
            missing.push(component.to_string_lossy().into_owned());
            current = parent;
        }
    }
}

impl FileSystem for BuildFileSystem<'_> {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.backing.use_case_sensitive_file_names()
    }

    fn file_exists(&self, path: &str) -> bool {
        self.output(path).is_some() || self.backing.file_exists(path)
    }

    fn directory_exists(&self, path: &str) -> bool {
        self.backing.directory_exists(path) || self.contains_output_directory(path)
    }

    fn realpath(&self, path: &str) -> String {
        self.output(path).map_or_else(
            || self.backing.realpath(path),
            |_| self.resolved_output_path(path),
        )
    }

    fn modified_time(&self, path: &str) -> Option<u128> {
        self.backing
            .modified_time(path)
            .or_else(|| self.output(path).map(|_| u128::MAX))
    }

    fn read_file(&self, path: &str) -> io::Result<String> {
        self.output(path)
            .map(|output| output.text.clone())
            .map_or_else(|| self.backing.read_file(path), Ok)
    }

    fn write_file(&self, path: &str, contents: &str) -> io::Result<()> {
        self.backing.write_file(path, contents)
    }

    fn read_directory(&self, path: &str) -> io::Result<DirectoryEntries> {
        let mut entries = match self.backing.read_directory(path) {
            Ok(entries) => entries,
            Err(_) if self.contains_output_directory(path) => DirectoryEntries::default(),
            Err(error) => return Err(error),
        };
        let directory = Path::new(path);
        let real_path = self.resolved_output_path(path);
        let real_directory = Path::new(&real_path);
        for output in self.outputs.values() {
            let Ok(relative) = Path::new(&output.file_name)
                .strip_prefix(directory)
                .or_else(|_| Path::new(&output.file_name).strip_prefix(real_directory))
            else {
                continue;
            };
            let mut components = relative.components();
            let Some(component) = components.next() else {
                continue;
            };
            let name = component.as_os_str().to_string_lossy().into_owned();
            if components.next().is_some() {
                entries.directories.push(name);
            } else {
                entries.files.push(name);
            }
        }
        entries.files.sort();
        entries.files.dedup();
        entries.directories.sort();
        entries.directories.dedup();
        Ok(entries)
    }
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
    let mut build_file_system = BuildFileSystem::new(file_system);
    for config_path in &graph.projects {
        if is_solution_project(file_system, &graph, config_path) {
            continue;
        }
        let program = Program::from_config_with_options(&build_file_system, config_path, overrides);
        let enabled = incremental || program.options().incremental || program.options().composite;
        let config_paths = project_config_paths(file_system, config_path);
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
        let build_info_path = project_build_info_path(file_system, &program, config_path);
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
                output_is_current(file_system, path, &config_paths, &preliminary)
            }) == BuildDecision::UpToDate
            && output_is_current(file_system, &build_info_path, &config_paths, &preliminary)
        {
            signatures.insert(config_path.clone(), preliminary.project_signature());
            skipped.push(config_path.clone());
            continue;
        }
        let emit = program.emit();
        build_file_system.add_outputs(&emit.files);
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

/// Returns the project build-info path using the host's path comparison rules.
#[must_use]
pub fn project_build_info_path(
    file_system: &dyn FileSystem,
    program: &Program,
    config_path: &str,
) -> String {
    let case_sensitivity = if file_system.use_case_sensitive_file_names() {
        CaseSensitivity::Sensitive
    } else {
        CaseSensitivity::Insensitive
    };
    ts_outputpaths::build_info_path(program.options(), config_path, case_sensitivity)
}

fn is_solution_project(
    file_system: &dyn FileSystem,
    graph: &ProjectGraph,
    config_path: &str,
) -> bool {
    graph
        .references
        .get(config_path)
        .is_some_and(|references| !references.is_empty())
        && resolve_config_file(file_system, config_path)
            .value
            .is_some_and(|config| {
                config.files.as_ref().is_some_and(Vec::is_empty)
                    && config.include.as_ref().is_none_or(Vec::is_empty)
            })
}

fn project_config_paths(file_system: &dyn FileSystem, config_path: &str) -> Vec<String> {
    let mut paths = Vec::new();
    let mut seen = BTreeSet::new();
    collect_project_config_paths(file_system, config_path, &mut paths, &mut seen);
    paths
}

fn collect_project_config_paths(
    file_system: &dyn FileSystem,
    config_path: &str,
    paths: &mut Vec<String>,
    seen: &mut BTreeSet<String>,
) {
    let config_path = normalize_path(config_path);
    let identity = canonical_config_path(file_system, &config_path);
    if !seen.insert(identity) {
        return;
    }
    paths.push(config_path.clone());

    let Some(config) = parse_config_file(file_system, &config_path).value else {
        return;
    };
    for extended_path in config.resolved_extends(file_system) {
        if let Some(resolved_path) =
            resolve_extended_config_path(file_system, &config_path, &extended_path)
        {
            collect_project_config_paths(file_system, &resolved_path, paths, seen);
        }
    }
}

fn resolve_extended_config_path(
    file_system: &dyn FileSystem,
    config_path: &str,
    extended_path: &str,
) -> Option<String> {
    if let Some(path) = existing_config_path(file_system, extended_path) {
        return Some(path);
    }
    if is_absolute(extended_path) {
        return None;
    }

    let mut directory = Path::new(config_path).parent();
    while let Some(parent) = directory {
        let parent_path = parent.to_string_lossy();
        let candidate = resolve_path(&parent_path, &["node_modules", extended_path]);
        if let Some(path) = existing_config_path(file_system, &candidate) {
            return Some(path);
        }
        directory = parent.parent();
    }
    None
}

fn existing_config_path(file_system: &dyn FileSystem, path: &str) -> Option<String> {
    let path = normalize_path(path);
    if file_system.file_exists(&path) {
        return Some(path);
    }
    if Path::new(&path).extension().is_none() {
        let json_path = format!("{path}.json");
        if file_system.file_exists(&json_path) {
            return Some(json_path);
        }
    }
    if !file_system.directory_exists(&path) {
        return None;
    }

    let package_path = resolve_path(&path, &["package.json"]);
    if let Some(configured_path) = parse_config_file(file_system, &package_path)
        .value
        .and_then(|package| {
            package
                .raw
                .get("tsconfig")
                .and_then(ts_config::JsonValue::as_str)
                .map(|configured| resolve_path(&path, &[configured]))
        })
        && file_system.file_exists(&configured_path)
    {
        return Some(configured_path);
    }

    let default_path = resolve_path(&path, &["tsconfig.json"]);
    file_system
        .file_exists(&default_path)
        .then_some(default_path)
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
                emit_declaration_file_with_semantics_and_options(
                    &source.parse.arena,
                    source.parse.source_file,
                    &source.file_name,
                    &source.source_text,
                    false,
                    Some(&source.checking.declaration_reachability),
                    Some(&source.checking.import_runtime_meanings),
                    None,
                    Some(&source.checking.types),
                    Some(&source.checking.node_types),
                    Some(&source.checking.import_type_references),
                    Some(&source.checking.named_type_references),
                    program.options().remove_comments,
                    program.options().rewrite_relative_import_extensions,
                    program.options().strip_internal,
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
    config_paths: &[String],
    info: &BuildInfo,
) -> bool {
    let Some(output_time) = file_system.modified_time(output) else {
        return false;
    };
    info.files
        .keys()
        .map(String::as_str)
        .chain(config_paths.iter().map(String::as_str))
        .filter_map(|path| file_system.modified_time(path))
        .all(|input_time| input_time <= output_time)
}

fn canonical_config_path(file_system: &dyn FileSystem, path: &str) -> String {
    canonicalize(
        path,
        "/",
        if file_system.use_case_sensitive_file_names() {
            CaseSensitivity::Sensitive
        } else {
            CaseSensitivity::Insensitive
        },
    )
}

struct GraphLoader<'a> {
    file_system: &'a dyn FileSystem,
    graph: ProjectGraph,
    completed: BTreeSet<String>,
    visiting: BTreeMap<String, usize>,
    display_paths: BTreeMap<String, String>,
    stack: Vec<String>,
}

impl<'a> GraphLoader<'a> {
    fn new(file_system: &'a dyn FileSystem) -> Self {
        Self {
            file_system,
            graph: ProjectGraph::default(),
            completed: BTreeSet::new(),
            visiting: BTreeMap::new(),
            display_paths: BTreeMap::new(),
            stack: Vec::new(),
        }
    }

    fn visit(&mut self, config_path: &str) {
        self.visit_reference(config_path, false);
    }

    fn visit_reference(&mut self, config_path: &str, circular_context: bool) {
        let config_path = normalize_path(config_path);
        let identity = canonical_config_path(self.file_system, &config_path);
        if self.completed.contains(&identity) {
            return;
        }
        if let Some(index) = self.visiting.get(&identity).copied() {
            if !circular_context {
                self.report_cycle(index);
            }
            return;
        }
        if !self.file_system.file_exists(&config_path) {
            self.report_missing(&config_path);
            self.completed.insert(identity);
            return;
        }

        self.display_paths
            .entry(identity.clone())
            .or_insert_with(|| config_path.clone());
        self.visiting.insert(identity.clone(), self.stack.len());
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
            let config_directory = Path::new(&config_path)
                .parent()
                .and_then(Path::to_str)
                .unwrap_or("/");
            let mut references = Vec::new();
            let mut seen_references = BTreeSet::new();
            for reference in config.resolved_references(self.file_system) {
                let reference_path =
                    resolve_config_path(self.file_system, config_directory, &reference.path);
                let reference_identity = canonical_config_path(self.file_system, &reference_path);
                if !seen_references.insert(reference_identity.clone()) {
                    continue;
                }
                let display_path = self
                    .display_paths
                    .get(&reference_identity)
                    .cloned()
                    .unwrap_or(reference_path);
                references.push((display_path, reference.circular.unwrap_or(false)));
            }
            for (reference_path, circular) in &references {
                self.visit_reference(reference_path, circular_context || *circular);
            }
            let references = references
                .into_iter()
                .map(|(reference_path, _)| {
                    let identity = canonical_config_path(self.file_system, &reference_path);
                    self.display_paths
                        .get(&identity)
                        .cloned()
                        .unwrap_or(reference_path)
                })
                .collect();
            self.graph
                .references
                .insert(config_path.clone(), references);
            self.graph.projects.push(config_path.clone());
        }
        self.stack.pop();
        self.visiting.remove(&identity);
        self.completed.insert(identity);
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
    use ts_compiler::{OutputFile, ProgramOptionsOverride};
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::{BuildFileSystem, BuildResult, build_projects, load_project_graph};

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
    fn generated_declarations_are_visible_through_package_symlinks() {
        let file_system = MemoryFileSystem::new(true);
        file_system.add_directory_link("/repo/packages/lib", "/repo/node_modules/lib");
        let mut build_file_system = BuildFileSystem::new(&file_system);
        build_file_system.add_outputs(&[OutputFile {
            file_name: "/repo/packages/lib/dist/index.d.ts".to_owned(),
            text: "export declare const value: number;\n".to_owned(),
        }]);

        let directory = "/repo/node_modules/lib/dist";
        let declaration = "/repo/node_modules/lib/dist/index.d.ts";
        assert!(build_file_system.directory_exists(directory));
        assert!(build_file_system.file_exists(declaration));
        assert_eq!(
            build_file_system.read_file(declaration).unwrap(),
            "export declare const value: number;\n"
        );
        assert_eq!(
            build_file_system.read_directory(directory).unwrap().files,
            ["index.d.ts"]
        );
    }

    #[cfg(unix)]
    #[test]
    fn generated_declarations_follow_existing_os_symlink_ancestors() {
        use std::{
            os::unix::fs::symlink,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir().join(format!(
            "ts-project-links-{}-{}",
            std::process::id(),
            NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed)
        ));
        let package = root.join("packages/lib");
        let node_modules = root.join("node_modules");
        std::fs::create_dir_all(&package).unwrap();
        std::fs::create_dir_all(&node_modules).unwrap();
        symlink(&package, node_modules.join("lib")).unwrap();

        let file_system = ts_vfs::OsFileSystem::default();
        let mut build_file_system = BuildFileSystem::new(&file_system);
        let declaration = package.join("dist/index.d.ts");
        build_file_system.add_outputs(&[OutputFile {
            file_name: declaration.to_string_lossy().into_owned(),
            text: "export declare const value: number;\n".to_owned(),
        }]);
        let linked_directory = node_modules.join("lib/dist");
        let linked_declaration = linked_directory.join("index.d.ts");

        assert!(build_file_system.directory_exists(&linked_directory.to_string_lossy()));
        assert!(build_file_system.file_exists(&linked_declaration.to_string_lossy()));
        assert_eq!(
            build_file_system.realpath(&linked_declaration.to_string_lossy()),
            declaration.to_string_lossy().into_owned()
        );
        assert_eq!(
            build_file_system
                .read_directory(&linked_directory.to_string_lossy())
                .unwrap()
                .files,
            ["index.d.ts"]
        );

        std::fs::remove_dir_all(root).unwrap();
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
    fn allows_explicitly_circular_project_references() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"files":[],"references":[{"path":"./app","circular":true}]}"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/app/tsconfig.json",
            r#"{"files":[],"references":[{"path":".."}]}"#,
        )
        .unwrap();

        let graph = load_project_graph(&fs, "/repo", &["tsconfig.json".into()]);

        assert!(graph.diagnostics.is_empty(), "{:?}", graph.diagnostics);
        assert!(!graph.has_cycle);
        assert_eq!(
            graph.projects,
            ["/repo/app/tsconfig.json", "/repo/tsconfig.json"]
        );
    }

    #[test]
    fn deduplicates_reference_casing_on_case_insensitive_file_systems() {
        let fs = MemoryFileSystem::new(false);
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"files":[],"references":[{"path":"./lib"},{"path":"./LIB"}]}"#,
        )
        .unwrap();
        fs.write_file("/repo/lib/tsconfig.json", r#"{"files":[]}"#)
            .unwrap();

        let graph = load_project_graph(&fs, "/repo", &["tsconfig.json".into()]);

        assert!(graph.diagnostics.is_empty(), "{:?}", graph.diagnostics);
        assert_eq!(
            graph.projects,
            ["/repo/lib/tsconfig.json", "/repo/tsconfig.json"]
        );
    }

    #[test]
    fn uses_first_project_casing_for_transitive_reference_edges() {
        let fs = MemoryFileSystem::new(false);
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"files":[],"references":[{"path":"./app"},{"path":"./lib"}]}"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/app/tsconfig.json",
            r#"{"files":[],"references":[{"path":"../LIB"}]}"#,
        )
        .unwrap();
        fs.write_file("/repo/lib/tsconfig.json", r#"{"files":[]}"#)
            .unwrap();

        let graph = load_project_graph(&fs, "/repo", &["tsconfig.json".into()]);

        assert!(graph.diagnostics.is_empty(), "{:?}", graph.diagnostics);
        assert_eq!(
            graph.references["/repo/tsconfig.json"],
            ["/repo/app/tsconfig.json", "/repo/LIB/tsconfig.json"]
        );
        assert_eq!(
            graph.projects,
            [
                "/repo/LIB/tsconfig.json",
                "/repo/app/tsconfig.json",
                "/repo/tsconfig.json"
            ]
        );
    }

    #[test]
    fn resolves_bare_reference_paths_relative_to_the_parent_config() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"files":[],"references":[{"path":"lib"}]}"#,
        )
        .unwrap();
        fs.write_file("/repo/lib/tsconfig.json", r#"{"files":[]}"#)
            .unwrap();

        let graph = load_project_graph(&fs, "/repo", &["tsconfig.json".into()]);

        assert!(graph.diagnostics.is_empty(), "{:?}", graph.diagnostics);
        assert_eq!(
            graph.projects,
            ["/repo/lib/tsconfig.json", "/repo/tsconfig.json"]
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
    fn solution_configs_do_not_compile_or_write_build_info() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"files":[],"references":[{"path":"./lib"}],"compilerOptions":{"composite":true,"noLib":true}}"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/lib/tsconfig.json",
            r#"{"files":["index.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist"}}"#,
        )
        .unwrap();
        fs.write_file("/repo/lib/index.ts", "export const value = 1;\n")
            .unwrap();

        let result = build_projects(
            &fs,
            "/repo",
            &["tsconfig.json".into()],
            ProgramOptionsOverride::default(),
            true,
        );

        assert_eq!(
            result
                .projects
                .iter()
                .map(|project| project.config_path.as_str())
                .collect::<Vec<_>>(),
            ["/repo/lib/tsconfig.json"]
        );
        write_build_outputs(&fs, result);
        assert!(!fs.file_exists("/repo/tsconfig.tsbuildinfo"));
        assert!(fs.file_exists("/repo/lib/dist/tsconfig.tsbuildinfo"));
    }

    #[test]
    fn nested_build_info_paths_preserve_config_location_within_root_dir() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/packages/app/tsconfig.app.json",
            r#"{"files":["index.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"../../dist","rootDir":".."}}"#,
        )
        .unwrap();
        fs.write_file("/repo/packages/app/index.ts", "export const value = 1;\n")
            .unwrap();

        let result = build_projects(
            &fs,
            "/repo",
            &["packages/app/tsconfig.app.json".into()],
            ProgramOptionsOverride::default(),
            true,
        );
        let build_info = result.projects[0]
            .build_info
            .as_ref()
            .expect("successful composite build emits build information");

        assert_eq!(
            build_info.file_name,
            "/repo/dist/app/tsconfig.app.tsbuildinfo"
        );
    }

    #[test]
    fn extended_config_changes_invalidate_incremental_projects() {
        let fs = MemoryFileSystem::new(true);
        let base_config = r#"{"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist"}}"#;
        fs.write_file("/repo/tsconfig.base.json", base_config)
            .unwrap();
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"extends":"./tsconfig.base.json","files":["index.ts"]}"#,
        )
        .unwrap();
        fs.write_file("/repo/index.ts", "export const value = 1;\n")
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

        fs.write_file("/repo/tsconfig.base.json", base_config)
            .unwrap();
        let result = build_projects(
            &fs,
            "/repo",
            &["tsconfig.json".into()],
            ProgramOptionsOverride::default(),
            true,
        );

        assert_eq!(result.projects.len(), 1);
        assert!(result.skipped.is_empty());
    }

    #[test]
    fn package_config_changes_invalidate_incremental_projects() {
        let fs = MemoryFileSystem::new(true);
        let base_config = r#"{"compilerOptions":{"composite":true,"noLib":true}}"#;
        fs.write_file(
            "/repo/node_modules/preset/package.json",
            r#"{"tsconfig":"config/base.json"}"#,
        )
        .unwrap();
        fs.write_file("/repo/node_modules/preset/config/base.json", base_config)
            .unwrap();
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"extends":"preset","files":["index.ts"],"compilerOptions":{"outDir":"dist"}}"#,
        )
        .unwrap();
        fs.write_file("/repo/index.ts", "export const value = 1;\n")
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

        fs.write_file("/repo/node_modules/preset/config/base.json", base_config)
            .unwrap();
        let result = build_projects(
            &fs,
            "/repo",
            &["tsconfig.json".into()],
            ProgramOptionsOverride::default(),
            true,
        );

        assert_eq!(result.projects.len(), 1);
        assert!(result.skipped.is_empty());
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
        assert_eq!(declaration_change.projects.len(), 2);
        assert!(declaration_change.skipped.is_empty());
    }

    #[test]
    fn stripped_internal_declaration_changes_do_not_invalidate_consumers() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"files":[],"include":[],"references":[{"path":"./app"}]}"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/lib/tsconfig.json",
            r#"{"files":["index.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist","stripInternal":true}}"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/lib/index.ts",
            concat!(
                "/** @internal */\n",
                "export function hidden(): number { return 1; }\n",
                "export function visible(): number { return 1; }\n",
            ),
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
            concat!(
                "/** @internal */\n",
                "export function hidden(): string { return 'internal'; }\n",
                "export function visible(): number { return 1; }\n",
            ),
        )
        .unwrap();
        let result = build_projects(
            &fs,
            "/repo",
            &["tsconfig.json".into()],
            ProgramOptionsOverride::default(),
            true,
        );

        assert_eq!(
            result
                .projects
                .iter()
                .map(|project| project.config_path.as_str())
                .collect::<Vec<_>>(),
            ["/repo/lib/tsconfig.json"]
        );
        assert_eq!(result.skipped, ["/repo/app/tsconfig.json"]);
    }

    #[test]
    fn downstream_projects_resolve_declarations_from_the_current_build() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/tsconfig.json",
            r#"{"files":[],"references":[{"path":"./app"}]}"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/lib/tsconfig.json",
            r#"{"files":["index.ts"],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist"}}"#,
        )
        .unwrap();
        fs.write_file("/repo/lib/index.ts", "export const value = 1;\n")
            .unwrap();
        fs.write_file(
            "/repo/app/tsconfig.json",
            r#"{"files":["index.ts"],"references":[{"path":"../lib"}],"compilerOptions":{"composite":true,"noLib":true,"outDir":"dist"}}"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/app/index.ts",
            "import { value } from '../lib/dist/index'; export const result = value;\n",
        )
        .unwrap();

        let result = build_projects(
            &fs,
            "/repo",
            &["tsconfig.json".into()],
            ProgramOptionsOverride::default(),
            true,
        );
        let application = result
            .projects
            .iter()
            .find(|project| project.config_path == "/repo/app/tsconfig.json")
            .unwrap();

        assert!(
            application.program.diagnostics().is_empty(),
            "{:?}",
            application.program.diagnostics()
        );
        assert!(!fs.file_exists("/repo/lib/dist/index.d.ts"));
    }
}
