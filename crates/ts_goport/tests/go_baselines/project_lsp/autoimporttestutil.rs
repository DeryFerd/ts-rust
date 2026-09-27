//! Port of Go `internal/testutil/autoimporttestutil/fixtures.go`.
//!
//! PORT: Go `t.Cleanup(session.Close)` is not needed: each test runs in a
//! child process (`child_test!`). Go map ranges are in key order here
//! (`BTreeMap`); the file map order does not change the session.

use std::collections::BTreeMap;
use std::rc::Rc;

use ts_goport::frontend::tspath;
use ts_goport::ls::lsconv;
use ts_goport::lsp::lsproto;
use ts_goport::project::Session;

use super::projecttestutil::{self, FileMap, SessionUtils};
use crate::support::vfstest::{self, MapFile};

// Go: fixtures.go:19 FileHandle
// FileHandle represents a file created for an autoimport lifecycle test.
#[derive(Clone, Debug, Default)]
pub struct FileHandle {
    file_name: String,
    content: String,
}

impl FileHandle {
    pub fn file_name(&self) -> &str {
        &self.file_name
    }
    pub fn content(&self) -> &str {
        &self.content
    }
    pub fn uri(&self) -> lsproto::DocumentUri {
        lsconv::file_name_to_document_uri(&self.file_name)
    }
}

// Go: fixtures.go:29 ProjectFileHandle
// ProjectFileHandle adds export metadata for TypeScript source files.
#[derive(Clone, Debug, Default)]
pub struct ProjectFileHandle {
    pub file: FileHandle,
    pub export_identifier: String,
}

impl std::ops::Deref for ProjectFileHandle {
    type Target = FileHandle;
    fn deref(&self) -> &FileHandle {
        &self.file
    }
}

// Go: fixtures.go:35 NodeModulesPackageHandle
// NodeModulesPackageHandle describes a generated package under node_modules.
#[derive(Clone, Debug, Default)]
pub struct NodeModulesPackageHandle {
    pub name: String,
    pub directory: String,
    package_json: FileHandle,
    declaration: FileHandle,
}

impl NodeModulesPackageHandle {
    pub fn package_json_file(&self) -> &FileHandle {
        &self.package_json
    }
    pub fn declaration_file(&self) -> &FileHandle {
        &self.declaration
    }
}

// Go: fixtures.go:46 MonorepoHandle
// MonorepoHandle exposes the generated monorepo layout including root and packages.
#[derive(Clone, Debug, Default)]
pub struct MonorepoHandle {
    root: String,
    root_node_modules: Vec<NodeModulesPackageHandle>,
    root_dependencies: Vec<String>,
    packages: Vec<ProjectHandle>,
    root_tsconfig: FileHandle,
    root_package_json: FileHandle,
}

impl MonorepoHandle {
    pub fn root(&self) -> &str {
        &self.root
    }
    pub fn root_node_modules(&self) -> &[NodeModulesPackageHandle] {
        &self.root_node_modules
    }
    pub fn root_dependencies(&self) -> &[String] {
        &self.root_dependencies
    }
    pub fn packages(&self) -> &[ProjectHandle] {
        &self.packages
    }
    pub fn package(&self, index: usize) -> &ProjectHandle {
        self.packages
            .get(index)
            .unwrap_or_else(|| panic!("package index {index} out of range"))
    }
    pub fn root_tsconfig(&self) -> &FileHandle {
        &self.root_tsconfig
    }
    pub fn root_package_json_file(&self) -> &FileHandle {
        &self.root_package_json
    }
}

// Go: fixtures.go:71 ProjectHandle
// ProjectHandle exposes the generated project layout for a fixture project root.
#[derive(Clone, Debug, Default)]
pub struct ProjectHandle {
    root: String,
    files: Vec<ProjectFileHandle>,
    tsconfig: FileHandle,
    package_json: FileHandle,
    node_modules: Vec<NodeModulesPackageHandle>,
    dependencies: Vec<String>,
}

impl ProjectHandle {
    pub fn root(&self) -> &str {
        &self.root
    }
    pub fn files(&self) -> &[ProjectFileHandle] {
        &self.files
    }
    pub fn file(&self, index: usize) -> &ProjectFileHandle {
        self.files
            .get(index)
            .unwrap_or_else(|| panic!("file index {index} out of range"))
    }
    pub fn tsconfig(&self) -> &FileHandle {
        &self.tsconfig
    }
    pub fn package_json_file(&self) -> &FileHandle {
        &self.package_json
    }
    pub fn node_modules(&self) -> &[NodeModulesPackageHandle] {
        &self.node_modules
    }
    pub fn dependencies(&self) -> &[String] {
        &self.dependencies
    }
    pub fn node_module_by_name(&self, name: &str) -> Option<&NodeModulesPackageHandle> {
        self.node_modules.iter().find(|p| p.name == name)
    }
}

// Go: fixtures.go:103 Fixture
// Fixture encapsulates a fully-initialized auto import lifecycle test session.
pub struct Fixture {
    session: Rc<Session>,
    utils: SessionUtils,
    projects: Vec<ProjectHandle>,
}

impl Fixture {
    pub fn session(&self) -> &Rc<Session> {
        &self.session
    }
    pub fn utils(&self) -> &SessionUtils {
        &self.utils
    }
    pub fn projects(&self) -> &[ProjectHandle] {
        &self.projects
    }
    pub fn project(&self, index: usize) -> &ProjectHandle {
        self.projects
            .get(index)
            .unwrap_or_else(|| panic!("project index {index} out of range"))
    }
    pub fn single_project(&self) -> &ProjectHandle {
        self.project(0)
    }
}

// Go: fixtures.go:122 MonorepoFixture
// MonorepoFixture encapsulates a fully-initialized monorepo lifecycle test session.
pub struct MonorepoFixture {
    session: Rc<Session>,
    utils: SessionUtils,
    monorepo: MonorepoHandle,
    extra: Vec<FileHandle>,
}

impl MonorepoFixture {
    pub fn session(&self) -> &Rc<Session> {
        &self.session
    }
    pub fn utils(&self) -> &SessionUtils {
        &self.utils
    }
    pub fn monorepo(&self) -> &MonorepoHandle {
        &self.monorepo
    }
    pub fn extra_files(&self) -> &[FileHandle] {
        &self.extra
    }
    pub fn extra_file(&self, path: &str) -> &FileHandle {
        let normalized = normalize_absolute_path(path);
        self.extra
            .iter()
            .find(|handle| handle.file_name == normalized)
            .unwrap_or_else(|| panic!("extra file not found: {path}"))
    }
}

// Go: fixtures.go:146 MonorepoPackageTemplate
// MonorepoPackageTemplate captures the reusable settings for a package.json scope:
// the node_modules packages that exist alongside the package.json and the dependency
// names that should be written into that package.json. When DependencyNames is empty,
// all available node_modules packages in scope are used.
#[derive(Clone, Debug, Default)]
pub struct MonorepoPackageTemplate {
    pub name: String,
    pub node_module_names: Vec<String>,
    pub dependency_names: Vec<String>,
}

// Go: fixtures.go:157 MonorepoSetupConfig
// MonorepoSetupConfig describes the monorepo root and packages to create.
#[derive(Clone, Debug, Default)]
pub struct MonorepoSetupConfig {
    pub root: String,
    pub template: MonorepoPackageTemplate,
    pub packages: Vec<MonorepoPackageConfig>,
    pub extra_files: Vec<TextFileSpec>,
    pub symlinks: Vec<SymlinkSpec>,
}

// Go: fixtures.go:165 MonorepoPackageConfig
#[derive(Clone, Debug, Default)]
pub struct MonorepoPackageConfig {
    pub file_count: usize,
    pub template: MonorepoPackageTemplate,
}

// Go: fixtures.go:171 TextFileSpec
// TextFileSpec describes an additional file to place in the fixture.
#[derive(Clone, Debug, Default)]
pub struct TextFileSpec {
    pub path: String,
    pub content: String,
}

// Go: fixtures.go:177 SymlinkSpec
// SymlinkSpec describes a symlink to create in the fixture.
#[derive(Clone, Debug, Default)]
pub struct SymlinkSpec {
    pub link: String,
    pub target: String,
}

// Go: fixtures.go:202 SetupMonorepoLifecycleSession
// SetupMonorepoLifecycleSession builds a monorepo workspace with root-level node_modules
// and multiple packages, each potentially with their own node_modules.
pub fn setup_monorepo_lifecycle_session(config: MonorepoSetupConfig) -> MonorepoFixture {
    let mut builder = FileMapBuilder::default();

    let monorepo_root = normalize_absolute_path(&config.root);
    let monorepo_name = if config.template.name.is_empty() {
        "monorepo".to_string()
    } else {
        config.template.name.clone()
    };

    // Add root tsconfig.json
    let root_tsconfig_path = tspath::combine_paths(&monorepo_root, &["tsconfig.json"]);
    let root_tsconfig_content = "{\n  \"compilerOptions\": {\n    \"module\": \"esnext\",\n    \"target\": \"esnext\",\n    \"strict\": true,\n    \"baseUrl\": \".\",\n    \"allowJs\": true,\n    \"checkJs\": true\n  }\n}\n";
    builder.add_text_file(&root_tsconfig_path, root_tsconfig_content);
    let root_tsconfig = FileHandle {
        file_name: root_tsconfig_path,
        content: root_tsconfig_content.to_string(),
    };

    // Add root node_modules
    let root_node_modules_dir = tspath::combine_paths(&monorepo_root, &["node_modules"]);
    let root_node_modules = builder.add_node_modules_packages_with_names(
        &root_node_modules_dir,
        &config.template.node_module_names,
    );

    // Add root package.json with dependencies (default to all root node_modules if unspecified)
    let root_dependencies =
        select_packages_by_name(&root_node_modules, &config.template.dependency_names);
    let root_package_json =
        builder.add_root_package_json(&monorepo_root, &monorepo_name, &root_dependencies);
    let root_dependency_names = package_names(&root_dependencies);

    // Build each package in packages/
    let packages_dir = tspath::combine_paths(&monorepo_root, &["packages"]);
    for pkg in &config.packages {
        let pkg_dir = tspath::combine_paths(&packages_dir, &[pkg.template.name.as_str()]);
        builder.add_local_project(&pkg_dir, pkg.file_count);

        let mut pkg_node_modules = Vec::new();
        if !pkg.template.node_module_names.is_empty() {
            let pkg_node_modules_dir = tspath::combine_paths(&pkg_dir, &["node_modules"]);
            pkg_node_modules = builder.add_node_modules_packages_with_names(
                &pkg_node_modules_dir,
                &pkg.template.node_module_names,
            );
        }

        let mut available_deps = root_node_modules.clone();
        available_deps.extend(pkg_node_modules);
        let selected_deps =
            select_packages_by_name(&available_deps, &pkg.template.dependency_names);
        if !selected_deps.is_empty() {
            builder.add_package_json_with_dependencies_named(
                &pkg_dir,
                &pkg.template.name,
                &selected_deps,
            );
        }
    }

    // Add arbitrary extra files
    let mut extra_handles = Vec::with_capacity(config.extra_files.len());
    for extra in &config.extra_files {
        builder.add_text_file(&extra.path, &extra.content);
        extra_handles.push(FileHandle {
            file_name: normalize_absolute_path(&extra.path),
            content: extra.content.clone(),
        });
    }

    // Add symlinks
    for symlink in &config.symlinks {
        builder.add_symlink(&symlink.link, &symlink.target);
    }

    // Build project handles after all packages are created
    let mut package_handles = Vec::with_capacity(config.packages.len());
    for pkg in &config.packages {
        let pkg_dir = tspath::combine_paths(&packages_dir, &[pkg.template.name.as_str()]);
        if let Some(record) = builder.projects.get(&pkg_dir) {
            package_handles.push(record.to_handles());
        }
    }

    let (session, session_utils) = projecttestutil::setup(builder.files());

    // Build root node_modules handle by looking at the project record for the workspace root
    // (created as side effect of AddNodeModulesPackages)
    let root_node_modules_handles = builder
        .projects
        .get(&monorepo_root)
        .map(|record| record.node_modules.clone())
        .unwrap_or_default();

    MonorepoFixture {
        session,
        utils: session_utils,
        monorepo: MonorepoHandle {
            root: monorepo_root,
            root_node_modules: root_node_modules_handles,
            root_dependencies: root_dependency_names,
            packages: package_handles,
            root_tsconfig,
            root_package_json,
        },
        extra: extra_handles,
    }
}

// Go: fixtures.go:294 SetupLifecycleSession
// SetupLifecycleSession builds a basic single-project workspace configured with the
// requested number of TypeScript files and a single synthetic node_modules package.
pub fn setup_lifecycle_session(project_root: &str, file_count: usize) -> Fixture {
    let mut builder = FileMapBuilder::default();
    builder.add_local_project(project_root, file_count);
    let node_modules_dir = tspath::combine_paths(project_root, &["node_modules"]);
    let deps = builder.add_node_modules_packages(&node_modules_dir, 1);
    builder.add_package_json_with_dependencies(project_root, &deps);
    let (session, session_utils) = projecttestutil::setup(builder.files());
    Fixture {
        session,
        utils: session_utils,
        projects: builder.project_handles(),
    }
}

// Go: fixtures.go:305 fileMapBuilder
#[derive(Default)]
struct FileMapBuilder {
    files: FileMap,
    next_package_id: i32,
    next_project_id: i32,
    projects: BTreeMap<String, ProjectRecord>,
}

// Go: fixtures.go:312 projectRecord
#[derive(Default)]
struct ProjectRecord {
    root: String,
    source_files: Vec<ProjectFile>,
    tsconfig: FileHandle,
    package_json: Option<FileHandle>,
    node_modules: Vec<NodeModulesPackageHandle>,
    dependencies: Vec<String>,
}

// Go: fixtures.go:321 projectFile
struct ProjectFile {
    file_name: String,
    export_identifier: String,
    content: String,
}

impl FileMapBuilder {
    // Go: fixtures.go:346 ensureProjectRecord
    fn ensure_project_record(&mut self, root: &str) -> &mut ProjectRecord {
        self.projects
            .entry(root.to_string())
            .or_insert_with(|| ProjectRecord {
                root: root.to_string(),
                ..Default::default()
            })
    }

    // Go: fixtures.go:355 projectHandles
    fn project_handles(&self) -> Vec<ProjectHandle> {
        self.projects
            .values()
            .map(ProjectRecord::to_handles)
            .collect()
    }

    // Go: fixtures.go:387 Files
    fn files(&self) -> FileMap {
        self.files.clone()
    }

    // Go: fixtures.go:391 AddTextFile
    fn add_text_file(&mut self, path: &str, contents: &str) {
        self.files
            .insert(normalize_absolute_path(path), MapFile::from(contents));
    }

    // Go: fixtures.go:398 AddSymlink
    // AddSymlink creates a symlink from linkPath to targetPath.
    fn add_symlink(&mut self, link_path: &str, target_path: &str) {
        self.files.insert(
            normalize_absolute_path(link_path),
            vfstest::symlink(&normalize_absolute_path(target_path)),
        );
    }

    // Go: fixtures.go:403 AddNodeModulesPackages
    fn add_node_modules_packages(
        &mut self,
        node_modules_dir: &str,
        count: usize,
    ) -> Vec<NodeModulesPackageHandle> {
        (0..count)
            .map(|_| self.add_node_modules_package(node_modules_dir))
            .collect()
    }

    // Go: fixtures.go:411 AddNodeModulesPackagesWithNames
    fn add_node_modules_packages_with_names(
        &mut self,
        node_modules_dir: &str,
        names: &[String],
    ) -> Vec<NodeModulesPackageHandle> {
        names
            .iter()
            .map(|name| self.add_named_node_modules_package(node_modules_dir, name))
            .collect()
    }

    // Go: fixtures.go:422 AddNodeModulesPackage
    fn add_node_modules_package(&mut self, node_modules_dir: &str) -> NodeModulesPackageHandle {
        self.add_named_node_modules_package(node_modules_dir, "")
    }

    // Go: fixtures.go:426 AddNamedNodeModulesPackage
    fn add_named_node_modules_package(
        &mut self,
        node_modules_dir: &str,
        name: &str,
    ) -> NodeModulesPackageHandle {
        let normalized_dir = normalize_absolute_path(node_modules_dir);
        if tspath::get_base_file_name(&normalized_dir) != "node_modules" {
            panic!("nodeModulesDir must point to a node_modules directory: {node_modules_dir}");
        }
        self.next_package_id += 1;
        let resolved_name = if name.is_empty() {
            format!("pkg{}", self.next_package_id)
        } else {
            name.to_string()
        };
        let export_name = format!("{}_value", sanitize_identifier(&resolved_name));
        let pkg_dir = tspath::combine_paths(&normalized_dir, &[resolved_name.as_str()]);
        let package_json_path = tspath::combine_paths(&pkg_dir, &["package.json"]);
        let package_json_content = format!(r#"{{"name":"{resolved_name}","types":"index.d.ts"}}"#);
        self.files.insert(
            package_json_path.clone(),
            MapFile::from(package_json_content.as_str()),
        );
        let declaration_path = tspath::combine_paths(&pkg_dir, &["index.d.ts"]);
        let declaration_content = format!("export declare const {export_name}: number;\n");
        self.files.insert(
            declaration_path.clone(),
            MapFile::from(declaration_content.as_str()),
        );
        let package_handle = NodeModulesPackageHandle {
            name: resolved_name,
            directory: pkg_dir,
            package_json: FileHandle {
                file_name: package_json_path,
                content: package_json_content,
            },
            declaration: FileHandle {
                file_name: declaration_path,
                content: declaration_content,
            },
        };
        let project_root = tspath::get_directory_path(&normalized_dir);
        let record = self.ensure_project_record(&project_root);
        record.node_modules.push(package_handle.clone());
        package_handle
    }

    // Go: fixtures.go:457 AddLocalProject
    fn add_local_project(&mut self, project_dir: &str, file_count: usize) {
        let dir = normalize_absolute_path(project_dir);
        self.ensure_project_record(&dir);
        self.next_project_id += 1;
        let project_id = self.next_project_id;
        let ts_config_path = tspath::combine_paths(&dir, &["tsconfig.json"]);
        let ts_config_content = "{\n  \"compilerOptions\": {\n    \"module\": \"esnext\",\n    \"target\": \"esnext\",\n    \"strict\": true,\n    \"allowJs\": true,\n    \"checkJs\": true\n  }\n}\n";
        self.files
            .insert(ts_config_path.clone(), MapFile::from(ts_config_content));
        let mut source_files = Vec::new();
        for i in 1..=file_count {
            let path = tspath::combine_paths(&dir, &[format!("file{i}.ts").as_str()]);
            let export_name = format!("localExport{project_id}_{i}");
            let content = format!("export const {export_name} = {i};\n");
            self.files
                .insert(path.clone(), MapFile::from(content.as_str()));
            source_files.push(ProjectFile {
                file_name: path,
                export_identifier: export_name,
                content,
            });
        }
        let record = self.ensure_project_record(&dir);
        record.tsconfig = FileHandle {
            file_name: ts_config_path,
            content: ts_config_content.to_string(),
        };
        record.source_files.extend(source_files);
    }

    // Go: fixtures.go:478 AddPackageJSONWithDependencies
    fn add_package_json_with_dependencies(
        &mut self,
        project_dir: &str,
        deps: &[NodeModulesPackageHandle],
    ) -> FileHandle {
        self.next_project_id += 1;
        let name = format!("local-project-{}", self.next_project_id);
        self.add_package_json_with_dependencies_named(project_dir, &name, deps)
    }

    // Go: fixtures.go:483 AddPackageJSONWithDependenciesNamed
    fn add_package_json_with_dependencies_named(
        &mut self,
        project_dir: &str,
        package_name: &str,
        deps: &[NodeModulesPackageHandle],
    ) -> FileHandle {
        let dir = normalize_absolute_path(project_dir);
        let package_json_path = tspath::combine_paths(&dir, &["package.json"]);
        let dependency_lines: Vec<String> = deps
            .iter()
            .map(|dep| format!("\"{}\": \"*\"", dep.name))
            .collect();
        let name = if package_name.is_empty() {
            self.next_project_id += 1;
            format!("local-project-{}", self.next_project_id)
        } else {
            package_name.to_string()
        };
        let mut builder = format!("{{\n  \"name\": \"{name}\"");
        if dependency_lines.is_empty() {
            builder.push('\n');
        } else {
            builder.push_str(",\n  \"dependencies\": {\n    ");
            builder.push_str(&dependency_lines.join(",\n    "));
            builder.push_str("\n  }\n");
        }
        builder.push_str("}\n");
        self.files
            .insert(package_json_path.clone(), MapFile::from(builder.as_str()));
        let package_handle = FileHandle {
            file_name: package_json_path,
            content: builder,
        };
        let record = self.ensure_project_record(&dir);
        record.package_json = Some(package_handle.clone());
        record.dependencies = package_names(deps);
        package_handle
    }

    // Go: fixtures.go:517 addRootPackageJSON
    // addRootPackageJSON creates a root package.json for a monorepo without creating a project record.
    fn add_root_package_json(
        &mut self,
        root_dir: &str,
        package_name: &str,
        deps: &[NodeModulesPackageHandle],
    ) -> FileHandle {
        let dir = normalize_absolute_path(root_dir);
        let package_json_path = tspath::combine_paths(&dir, &["package.json"]);
        let dependency_lines: Vec<String> = deps
            .iter()
            .map(|dep| format!("\"{}\": \"*\"", dep.name))
            .collect();
        let pkg_name = if package_name.is_empty() {
            "monorepo-root"
        } else {
            package_name
        };
        let mut builder = format!("{{\n  \"name\": \"{pkg_name}\",\n  \"private\": true");
        if dependency_lines.is_empty() {
            builder.push('\n');
        } else {
            builder.push_str(",\n  \"dependencies\": {\n    ");
            builder.push_str(&dependency_lines.join(",\n    "));
            builder.push_str("\n  }\n");
        }
        builder.push_str("}\n");
        self.files
            .insert(package_json_path.clone(), MapFile::from(builder.as_str()));
        FileHandle {
            file_name: package_json_path,
            content: builder,
        }
    }
}

impl ProjectRecord {
    // Go: fixtures.go:365 toHandles
    fn to_handles(&self) -> ProjectHandle {
        let files = self
            .source_files
            .iter()
            .map(|file| ProjectFileHandle {
                file: FileHandle {
                    file_name: file.file_name.clone(),
                    content: file.content.clone(),
                },
                export_identifier: file.export_identifier.clone(),
            })
            .collect();
        ProjectHandle {
            root: self.root.clone(),
            files,
            tsconfig: self.tsconfig.clone(),
            package_json: self.package_json.clone().unwrap_or_default(),
            node_modules: self.node_modules.clone(),
            dependencies: self.dependencies.clone(),
        }
    }
}

// Go: fixtures.go:544 selectPackagesByName
fn select_packages_by_name(
    available: &[NodeModulesPackageHandle],
    names: &[String],
) -> Vec<NodeModulesPackageHandle> {
    if names.is_empty() {
        return available.to_vec();
    }
    names
        .iter()
        .map(|name| {
            available
                .iter()
                .find(|candidate| &candidate.name == name)
                .cloned()
                .unwrap_or_else(|| panic!("dependency not found: {name}"))
        })
        .collect()
}

// Go: fixtures.go:565 packageNames
fn package_names(deps: &[NodeModulesPackageHandle]) -> Vec<String> {
    deps.iter().map(|dep| dep.name.clone()).collect()
}

// Go: fixtures.go:576 sanitizeIdentifier
fn sanitize_identifier(name: &str) -> String {
    let sanitized: String = name
        .chars()
        .filter_map(|r| match r {
            'a'..='z' | 'A'..='Z' | '0'..='9' => Some(r),
            '_' | '-' => Some('_'),
            _ => None,
        })
        .collect();
    if sanitized.is_empty() {
        return "pkg".to_string();
    }
    sanitized
}

// Go: fixtures.go:604 normalizeAbsolutePath
fn normalize_absolute_path(path: &str) -> String {
    let normalized = tspath::normalize_path(path);
    if !tspath::path_is_absolute(&normalized) {
        panic!("paths used in lifecycle tests must be absolute: {path}");
    }
    normalized
}
