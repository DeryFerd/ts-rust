//! Foundational TypeScript module resolution.

use std::{
    collections::{BTreeMap, BTreeSet},
    io,
    sync::{Arc, PoisonError, RwLock},
};

use serde_json::Value;
use ts_path::{FileExtension, is_absolute, is_relative, normalize_path, resolve_path, root_length};
use ts_semver::{Version, VersionRange};
use ts_vfs::FileSystem;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ResolutionMode {
    Classic,
    #[default]
    Node10,
    Node16,
    NodeNext,
    Bundler,
}

/// The runtime module format implied by a source or declaration file.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ModuleFormat {
    CommonJs,
    Esm,
}

/// Package scope and format facts attached to one compiler input file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleFileFacts {
    pub format: Option<ModuleFormat>,
    pub is_declaration_file: bool,
    pub has_fixed_format: bool,
    pub package_json: Option<String>,
    pub package_type: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(clippy::struct_excessive_bools)]
pub struct ResolutionOptions {
    pub mode: ResolutionMode,
    pub allow_arbitrary_extensions: bool,
    pub allow_javascript: bool,
    pub resolve_json: bool,
    pub resolve_package_json_exports: bool,
    pub resolve_package_json_imports: bool,
    pub prefer_types: bool,
    pub custom_conditions: Vec<String>,
    pub module_suffixes: Vec<String>,
    pub base_url: Option<String>,
    pub paths: BTreeMap<String, Vec<String>>,
    pub root_dirs: Vec<String>,
    pub type_roots: Option<Vec<String>>,
    pub types: Option<Vec<String>>,
}

impl Default for ResolutionOptions {
    fn default() -> Self {
        Self {
            mode: ResolutionMode::Node10,
            allow_arbitrary_extensions: false,
            allow_javascript: true,
            resolve_json: false,
            resolve_package_json_exports: true,
            resolve_package_json_imports: true,
            prefer_types: true,
            custom_conditions: Vec::new(),
            module_suffixes: Vec::new(),
            base_url: None,
            paths: BTreeMap::new(),
            root_dirs: Vec::new(),
            type_roots: None,
            types: None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FailedLookupKind {
    File,
    Directory,
    PackageJson,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FailedLookup {
    pub kind: FailedLookupKind,
    pub path: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedModule {
    pub resolved_file_name: String,
    /// The exact candidate passed to the file system's `realpath` call.
    pub original_file_name: String,
    pub extension: Option<FileExtension>,
    pub resolved_using_ts_extension: bool,
    pub is_external_library_import: bool,
    pub package_json: Option<String>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ResolutionResult {
    pub resolved: Option<ResolvedModule>,
    pub failed_lookups: Vec<FailedLookup>,
    /// The import or require condition selected for this resolution attempt.
    /// A synthetic default result has no observed mode.
    pub effective_mode: Option<ModuleFormat>,
    /// Inputs from the worker that produced this result. Cache hits reuse this
    /// evidence without accessing the filesystem. A synthetic result has none.
    pub package_json_inputs: Option<PackageJsonInputs>,
}

/// Bounds retained package JSON events and UTF-8 string bytes per worker.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PackageJsonInputLimits {
    pub max_events: usize,
    pub max_string_bytes: usize,
}

impl Default for PackageJsonInputLimits {
    fn default() -> Self {
        Self {
            max_events: 256,
            max_string_bytes: 256 * 1024,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageJsonInputPurpose {
    DefaultMode,
    PackageResolution,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageJsonInputReadError {
    pub kind: io::ErrorKind,
    pub message: String,
}

/// One existing package metadata access, in worker execution order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PackageJsonInputEvent {
    FileExists {
        path: String,
        exists: bool,
    },
    /// Success retains the exact VFS text passed to package JSON parsing.
    ReadFile {
        path: String,
        purpose: PackageJsonInputPurpose,
        result: Result<String, PackageJsonInputReadError>,
    },
}

/// An ordered prefix of one worker's package metadata accesses, without deduplication.
///
/// Repeated reads remain separate. Once a limit is reached, all later events
/// are counted as omitted. Cache clones share the retained event storage.
/// This excludes `file_module_facts` and automatic type directive discovery.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PackageJsonInputs {
    pub events: Arc<[PackageJsonInputEvent]>,
    pub omitted_events: usize,
}

impl PackageJsonInputs {
    /// Whether all worker package JSON events were retained. This does not
    /// prove full package identity, peer context, or complete graph evidence.
    #[must_use]
    pub const fn is_complete(&self) -> bool {
        self.omitted_events == 0
    }
}

struct PackageJsonInputRecorder {
    limits: PackageJsonInputLimits,
    string_bytes: usize,
    events: Vec<PackageJsonInputEvent>,
    omitted_events: usize,
}

impl PackageJsonInputRecorder {
    fn new(limits: PackageJsonInputLimits) -> Self {
        Self {
            limits,
            string_bytes: 0,
            events: Vec::new(),
            omitted_events: 0,
        }
    }

    fn finish(self) -> PackageJsonInputs {
        PackageJsonInputs {
            events: self.events.into(),
            omitted_events: self.omitted_events,
        }
    }

    fn retain(
        &mut self,
        string_bytes: Option<usize>,
        event: impl FnOnce() -> PackageJsonInputEvent,
    ) {
        let total = string_bytes.and_then(|bytes| self.string_bytes.checked_add(bytes));
        if self.omitted_events != 0
            || self.events.len() >= self.limits.max_events
            || total.is_none_or(|bytes| bytes > self.limits.max_string_bytes)
        {
            self.omitted_events = self.omitted_events.saturating_add(1);
            return;
        }
        self.string_bytes = total.expect("the retained string bytes fit the limit");
        self.events.push(event());
    }

    fn file_exists(&mut self, path: &str, exists: bool) {
        self.retain(Some(path.len()), || PackageJsonInputEvent::FileExists {
            path: path.to_owned(),
            exists,
        });
    }

    fn read_text(&mut self, path: &str, purpose: PackageJsonInputPurpose, contents: &str) {
        self.retain(path.len().checked_add(contents.len()), || {
            PackageJsonInputEvent::ReadFile {
                path: path.to_owned(),
                purpose,
                result: Ok(contents.to_owned()),
            }
        });
    }

    fn read_error(&mut self, path: &str, purpose: PackageJsonInputPurpose, error: &io::Error) {
        let message = error.to_string();
        self.retain(path.len().checked_add(message.len()), || {
            PackageJsonInputEvent::ReadFile {
                path: path.to_owned(),
                purpose,
                result: Err(PackageJsonInputReadError {
                    kind: error.kind(),
                    message,
                }),
            }
        });
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PackageJson {
    pub types: Option<String>,
    pub typings: Option<String>,
    pub main: Option<String>,
    pub package_type: Option<String>,
    pub exports: Option<Value>,
    pub types_versions: Option<Value>,
    pub name: Option<String>,
    pub imports: Option<Value>,
}

type ResolutionCacheKey = (String, String, Option<ModuleFormat>);

pub struct Resolver<'a, F: FileSystem + ?Sized> {
    file_system: &'a F,
    options: ResolutionOptions,
    package_json_input_limits: PackageJsonInputLimits,
    cache: RwLock<BTreeMap<ResolutionCacheKey, ResolutionResult>>,
}

impl<'a, F: FileSystem + ?Sized> Resolver<'a, F> {
    #[must_use]
    pub fn new(file_system: &'a F, options: ResolutionOptions) -> Self {
        Self::new_with_package_json_input_limits(
            file_system,
            options,
            PackageJsonInputLimits::default(),
        )
    }

    /// Sets one input observation limit for each uncached resolver operation.
    /// Limits change retained evidence, not resolution decisions or cache keys.
    #[must_use]
    pub fn new_with_package_json_input_limits(
        file_system: &'a F,
        options: ResolutionOptions,
        limits: PackageJsonInputLimits,
    ) -> Self {
        Self {
            file_system,
            options,
            package_json_input_limits: limits,
            cache: RwLock::new(BTreeMap::new()),
        }
    }

    #[must_use]
    pub fn options(&self) -> ResolutionOptions {
        self.options.clone()
    }

    #[must_use]
    pub fn resolve(&self, specifier: &str, containing_file: &str) -> ResolutionResult {
        self.resolve_worker(specifier, containing_file, None)
    }

    /// Resolves one specifier using its exact import or require syntax mode.
    #[must_use]
    pub fn resolve_with_mode(
        &self,
        specifier: &str,
        containing_file: &str,
        mode: ModuleFormat,
    ) -> ResolutionResult {
        self.resolve_worker(specifier, containing_file, Some(mode))
    }

    /// Reads the nearest package scope and the file extension's Node format.
    #[must_use]
    pub fn file_module_facts(&self, file_name: &str) -> ModuleFileFacts {
        let normalized = normalize_path(file_name);
        let extension = ts_path::extension_from_path(&normalized);
        let package = ancestors(&directory_path(&normalized))
            .into_iter()
            .find_map(|directory| {
                let package_json = join(&directory, "package.json");
                self.file_system
                    .file_exists(&package_json)
                    .then_some(package_json)
            });
        let fixed_format = match extension {
            Some(FileExtension::Mts | FileExtension::Mjs | FileExtension::Dmts) => {
                Some(ModuleFormat::Esm)
            }
            Some(FileExtension::Cts | FileExtension::Cjs | FileExtension::Dcts) => {
                Some(ModuleFormat::CommonJs)
            }
            _ => None,
        };
        let use_package_type = fixed_format.is_none()
            && matches!(
                self.options.mode,
                ResolutionMode::Node16 | ResolutionMode::NodeNext
            )
            || normalized.contains("/node_modules/");
        let package_type =
            package
                .as_deref()
                .filter(|_| use_package_type)
                .and_then(|package_json| {
                    self.file_system
                        .read_file(package_json)
                        .ok()
                        .and_then(|contents| parse_package_json(&contents).ok())
                        .and_then(|package| package.package_type)
                });
        let format = fixed_format.or_else(|| match extension {
            Some(
                FileExtension::Ts
                | FileExtension::Tsx
                | FileExtension::Dts
                | FileExtension::Js
                | FileExtension::Jsx,
            ) => Some(if package_type.as_deref() == Some("module") {
                ModuleFormat::Esm
            } else {
                ModuleFormat::CommonJs
            }),
            _ => None,
        });
        ModuleFileFacts {
            format,
            is_declaration_file: extension.is_some_and(FileExtension::is_declaration),
            has_fixed_format: fixed_format.is_some(),
            package_json: package,
            package_type,
        }
    }

    fn resolve_worker(
        &self,
        specifier: &str,
        containing_file: &str,
        mode: Option<ModuleFormat>,
    ) -> ResolutionResult {
        let key = (specifier.to_owned(), normalize_path(containing_file), mode);
        if let Some(cached) = self
            .cache
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .get(&key)
        {
            return cached.clone();
        }
        let mut state = ResolutionState {
            resolver: self,
            failed_lookups: Vec::new(),
            package_json_inputs: PackageJsonInputRecorder::new(self.package_json_input_limits),
            import_condition: false,
            extension_priority: ExtensionPriority::All,
            specifier_uses_ts_extension: is_typescript_extension(specifier),
            candidate_ending_is_from_config: false,
            active_package_targets: BTreeSet::new(),
        };
        state.import_condition = mode.map_or_else(
            || state.use_import_condition(containing_file),
            |mode| mode == ModuleFormat::Esm,
        );
        let containing_directory = directory_path(containing_file);
        let resolved = if is_relative(specifier) {
            let candidate = resolve_path(&containing_directory, &[specifier]);
            state
                .resolve_relative_candidate(&candidate, false)
                .or_else(|| state.resolve_root_dirs(specifier, &containing_directory))
        } else if is_absolute_uri_specifier(specifier) {
            state.resolve_path_mapping(specifier)
        } else if is_absolute(specifier) {
            state.resolve_paths_or_base_url(specifier).or_else(|| {
                let candidate = resolve_path(&containing_directory, &[specifier]);
                state.resolve_relative_candidate(&candidate, false)
            })
        } else if self.options.mode == ResolutionMode::Classic {
            state.resolve_paths_or_base_url(specifier).or_else(|| {
                ancestors(&containing_directory)
                    .into_iter()
                    .find_map(|directory| {
                        let candidate = resolve_path(&directory, &[specifier]);
                        state.resolve_candidate(&candidate, false)
                    })
            })
        } else {
            state
                .resolve_paths_or_base_url(specifier)
                .or_else(|| state.resolve_package_imports_or_self(specifier, &containing_directory))
                .or_else(|| state.resolve_node_modules(specifier, &containing_directory))
                .or_else(|| state.resolve_from_type_roots(specifier, &containing_directory))
        };
        let result = ResolutionResult {
            resolved,
            failed_lookups: state.failed_lookups,
            effective_mode: Some(if state.import_condition {
                ModuleFormat::Esm
            } else {
                ModuleFormat::CommonJs
            }),
            package_json_inputs: Some(state.package_json_inputs.finish()),
        };
        self.cache
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(key, result.clone());
        result
    }

    /// Resolves a `types` compiler-option entry or automatically discovered
    /// package through type roots and ancestor `node_modules/@types` folders.
    #[must_use]
    pub fn resolve_type_reference(&self, name: &str, containing_file: &str) -> ResolutionResult {
        let mut state = ResolutionState {
            resolver: self,
            failed_lookups: Vec::new(),
            package_json_inputs: PackageJsonInputRecorder::new(self.package_json_input_limits),
            import_condition: false,
            extension_priority: ExtensionPriority::Types,
            specifier_uses_ts_extension: is_typescript_extension(name),
            candidate_ending_is_from_config: false,
            active_package_targets: BTreeSet::new(),
        };
        state.import_condition = state.use_import_condition(containing_file);
        let containing_directory = directory_path(containing_file);
        let resolved = state
            .resolve_type_reference_from_roots(name, &containing_directory)
            .or_else(|| state.resolve_node_modules(name, &containing_directory));
        ResolutionResult {
            resolved,
            failed_lookups: state.failed_lookups,
            effective_mode: Some(if state.import_condition {
                ModuleFormat::Esm
            } else {
                ModuleFormat::CommonJs
            }),
            package_json_inputs: Some(state.package_json_inputs.finish()),
        }
    }

    pub fn clear_cache(&self) {
        self.cache
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .clear();
    }
}

struct ResolutionState<'a, 'fs, F: FileSystem + ?Sized> {
    resolver: &'a Resolver<'fs, F>,
    failed_lookups: Vec<FailedLookup>,
    package_json_inputs: PackageJsonInputRecorder,
    import_condition: bool,
    extension_priority: ExtensionPriority,
    specifier_uses_ts_extension: bool,
    candidate_ending_is_from_config: bool,
    active_package_targets: BTreeSet<(String, String)>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum ExtensionPriority {
    All,
    Types,
    JavaScript,
}

enum PackageMetadataResolution {
    NotApplicable,
    Resolved(ResolvedModule),
    Blocked,
}

enum PackageTargetResolution {
    NotMatched,
    Resolved(ResolvedModule),
    Blocked,
}

struct PackageMapMatch<'a> {
    target: &'a Value,
    capture: String,
    is_pattern: bool,
}

impl<F: FileSystem + ?Sized> ResolutionState<'_, '_, F> {
    fn use_import_condition(&mut self, containing_file: &str) -> bool {
        match self.resolver.options.mode {
            ResolutionMode::Bundler => true,
            ResolutionMode::Node16 | ResolutionMode::NodeNext => {
                match source_extension(containing_file) {
                    Some(".mts" | ".mjs" | ".d.mts") => return true,
                    Some(".cts" | ".cjs" | ".d.cts") => return false,
                    _ => {}
                }
                ancestors(&directory_path(containing_file))
                    .into_iter()
                    .find_map(|directory| {
                        let package_json = join(&directory, "package.json");
                        self.read_package_json_contents(
                            &package_json,
                            PackageJsonInputPurpose::DefaultMode,
                        )
                        .and_then(|contents| parse_package_json(&contents).ok())
                    })
                    .is_some_and(|package| package.package_type.as_deref() == Some("module"))
            }
            ResolutionMode::Classic | ResolutionMode::Node10 => false,
        }
    }

    fn condition_matches(&self, condition: &str) -> bool {
        match condition {
            "default" => true,
            "import" => self.import_condition,
            "require" => !self.import_condition,
            "types" => self.resolver.options.prefer_types,
            "node" => matches!(
                self.resolver.options.mode,
                ResolutionMode::Node16 | ResolutionMode::NodeNext
            ),
            _ => {
                self.resolver
                    .options
                    .custom_conditions
                    .iter()
                    .any(|custom| custom == condition)
                    || (self.resolver.options.prefer_types
                        && condition
                            .strip_prefix("types@")
                            .and_then(|range| VersionRange::parse(range).ok())
                            .zip(Version::parse(env!("CARGO_PKG_VERSION")).ok())
                            .is_some_and(|(range, version)| range.test(&version)))
            }
        }
    }

    fn resolve_paths_or_base_url(&mut self, specifier: &str) -> Option<ResolvedModule> {
        if let Some(resolved) = self.resolve_path_mapping(specifier) {
            return Some(resolved);
        }
        let base = self.resolver.options.base_url.as_deref()?;
        let candidate = resolve_path(base, &[specifier]);
        self.resolve_relative_candidate(&candidate, false)
    }

    fn resolve_path_mapping(&mut self, specifier: &str) -> Option<ResolvedModule> {
        if let Some((capture, substitutions)) =
            best_path_match(&self.resolver.options.paths, specifier)
        {
            let base = self
                .resolver
                .options
                .base_url
                .clone()
                .unwrap_or_else(|| ".".to_owned());
            for substitution in substitutions {
                let mapped = substitution.replace('*', &capture);
                let candidate = resolve_path(&base, &[&mapped]);
                let previous_ending = self.candidate_ending_is_from_config;
                self.candidate_ending_is_from_config = source_extension(&substitution).is_some();
                let resolved = self.resolve_relative_candidate(&candidate, false);
                self.candidate_ending_is_from_config = previous_ending;
                if let Some(resolved) = resolved {
                    return Some(resolved);
                }
            }
        }
        None
    }

    fn resolve_root_dirs(
        &mut self,
        specifier: &str,
        containing_directory: &str,
    ) -> Option<ResolvedModule> {
        let roots = self.resolver.options.root_dirs.clone();
        let normalized_containing = normalize_path(containing_directory);
        let (_, suffix) = roots
            .iter()
            .filter_map(|root| {
                let normalized_root = normalize_path(root);
                path_suffix(&normalized_containing, &normalized_root)
                    .map(|suffix| (normalized_root.len(), suffix.to_owned()))
            })
            .max_by_key(|(length, _)| *length)?;
        for root in roots {
            let candidate_directory = if suffix.is_empty() {
                normalize_path(&root)
            } else {
                resolve_path(&root, &[&suffix])
            };
            let candidate = resolve_path(&candidate_directory, &[specifier]);
            if let Some(resolved) = self.resolve_relative_candidate(&candidate, false) {
                return Some(resolved);
            }
        }
        None
    }

    fn resolve_package_imports_or_self(
        &mut self,
        specifier: &str,
        containing_directory: &str,
    ) -> Option<ResolvedModule> {
        if !matches!(
            self.resolver.options.mode,
            ResolutionMode::Node16 | ResolutionMode::NodeNext | ResolutionMode::Bundler
        ) {
            return None;
        }
        if specifier == "#"
            || (self.resolver.options.mode == ResolutionMode::Node16 && specifier.starts_with("#/"))
            || (specifier.starts_with('#') && !self.resolver.options.resolve_package_json_imports)
            || (!specifier.starts_with('#') && !self.resolver.options.resolve_package_json_exports)
        {
            return None;
        }
        let (package_directory, package_json_path, package) = ancestors(containing_directory)
            .into_iter()
            .find_map(|directory| {
                let package_json = join(&directory, "package.json");
                self.package_json_exists(&package_json)
                    .then_some((directory, package_json))
            })
            .and_then(|(directory, package_json)| {
                self.read_package_json(&package_json)
                    .map(|package| (directory, package_json, package))
            })?;
        let is_imports = specifier.starts_with('#');
        let matched = if is_imports {
            package
                .imports
                .as_ref()
                .and_then(|imports| package_map_match(imports, specifier))
        } else {
            let name = package.name.as_deref()?;
            let rest = specifier
                .strip_prefix(name)
                .filter(|rest| rest.is_empty() || rest.starts_with('/'))?;
            let key = if rest.is_empty() {
                ".".to_owned()
            } else {
                format!(".{rest}")
            };
            package
                .exports
                .as_ref()
                .and_then(|exports| package_export_match(exports, &key))
        }?;
        match self.resolve_package_target(
            matched.target,
            &package_directory,
            &package_json_path,
            &matched.capture,
            matched.is_pattern,
            is_imports,
        ) {
            PackageTargetResolution::Resolved(resolved) => Some(resolved),
            PackageTargetResolution::NotMatched | PackageTargetResolution::Blocked => None,
        }
    }

    fn resolve_type_reference_from_roots(
        &mut self,
        specifier: &str,
        containing_directory: &str,
    ) -> Option<ResolvedModule> {
        for root in effective_type_roots(&self.resolver.options, containing_directory) {
            let root = normalize_path(&root);
            let name = if root.ends_with("/node_modules/@types") {
                mangled_scoped_package_name(specifier)
            } else {
                specifier.to_owned()
            };
            let candidate = resolve_path(&root, &[&name]);
            if let Some(mut resolved) = self.resolve_candidate(&candidate, true) {
                resolved.is_external_library_import = true;
                return Some(resolved);
            }
        }
        None
    }

    fn resolve_from_type_roots(
        &mut self,
        specifier: &str,
        containing_directory: &str,
    ) -> Option<ResolvedModule> {
        for root in effective_type_roots(&self.resolver.options, containing_directory) {
            let candidate = resolve_path(&root, &[specifier]);
            if let Some(mut resolved) = self.resolve_candidate(&candidate, true) {
                resolved.is_external_library_import = true;
                return Some(resolved);
            }
        }
        None
    }

    fn resolve_node_modules(
        &mut self,
        specifier: &str,
        containing_directory: &str,
    ) -> Option<ResolvedModule> {
        let (package_name, rest) = parse_package_name(specifier)?;
        let previous_priority = self.extension_priority;
        let priorities: &[ExtensionPriority] = match previous_priority {
            ExtensionPriority::All
                if self.resolver.options.allow_javascript || self.resolver.options.resolve_json =>
            {
                &[ExtensionPriority::Types, ExtensionPriority::JavaScript]
            }
            ExtensionPriority::All | ExtensionPriority::Types => &[ExtensionPriority::Types],
            ExtensionPriority::JavaScript => &[ExtensionPriority::JavaScript],
        };
        let types_name = types_package_name(specifier);
        for &priority in priorities {
            self.extension_priority = priority;
            for ancestor in ancestors(containing_directory) {
                if ancestor.ends_with("/node_modules") {
                    continue;
                }
                let node_modules = join(&ancestor, "node_modules");
                if let Some(resolved) =
                    self.resolve_node_modules_package(&node_modules, package_name, rest)
                {
                    self.extension_priority = previous_priority;
                    return Some(resolved);
                }
                if priority == ExtensionPriority::Types
                    && let Some(types_name) = types_name.as_deref()
                    && let Some((types_package, types_rest)) = parse_package_name(types_name)
                    && let Some(resolved) =
                        self.resolve_node_modules_package(&node_modules, types_package, types_rest)
                {
                    self.extension_priority = previous_priority;
                    return Some(resolved);
                }
            }
        }
        self.extension_priority = previous_priority;
        None
    }

    fn resolve_node_modules_package(
        &mut self,
        node_modules: &str,
        package_name: &str,
        rest: &str,
    ) -> Option<ResolvedModule> {
        let package_directory = join(node_modules, package_name);
        if !rest.is_empty() {
            let nested_directory = join(&package_directory, rest);
            let nested_package_json = join(&nested_directory, "package.json");
            if self.package_json_exists(&nested_package_json)
                && !self.package_exports_apply(&package_directory)
                && let Some(resolved) = self.resolve_candidate(&nested_directory, true)
            {
                return Some(resolved);
            }
        }
        match self.resolve_package_metadata(&package_directory, rest) {
            PackageMetadataResolution::Resolved(resolved) => return Some(resolved),
            PackageMetadataResolution::Blocked => return None,
            PackageMetadataResolution::NotApplicable => {}
        }
        let candidate = if rest.is_empty() {
            package_directory
        } else {
            join(&package_directory, rest)
        };
        self.resolve_candidate(&candidate, true)
            .map(|mut resolved| {
                resolved.is_external_library_import = true;
                resolved
            })
    }

    fn resolve_package_metadata(
        &mut self,
        package_directory: &str,
        rest: &str,
    ) -> PackageMetadataResolution {
        let package_json_path = join(package_directory, "package.json");
        if !self.package_json_exists(&package_json_path) {
            return PackageMetadataResolution::NotApplicable;
        }
        let Some(package) = self.read_package_json(&package_json_path) else {
            return PackageMetadataResolution::NotApplicable;
        };
        if self.resolver.options.resolve_package_json_exports
            && let Some(exports) = &package.exports
            && !exports.is_null()
            && matches!(
                self.resolver.options.mode,
                ResolutionMode::Node16 | ResolutionMode::NodeNext | ResolutionMode::Bundler
            )
        {
            let key = if rest.is_empty() {
                ".".to_owned()
            } else {
                format!("./{rest}")
            };
            let Some(matched) = package_export_match(exports, &key) else {
                return PackageMetadataResolution::Blocked;
            };
            match self.resolve_package_target(
                matched.target,
                package_directory,
                &package_json_path,
                &matched.capture,
                matched.is_pattern,
                false,
            ) {
                PackageTargetResolution::Resolved(mut resolved) => {
                    resolved.is_external_library_import = true;
                    return PackageMetadataResolution::Resolved(resolved);
                }
                PackageTargetResolution::NotMatched | PackageTargetResolution::Blocked => {
                    return PackageMetadataResolution::Blocked;
                }
            }
        }
        if !rest.is_empty()
            && let Some(types_versions) = &package.types_versions
            && let Some(targets) = types_version_targets(types_versions, rest)
        {
            for target in targets {
                let candidate = resolve_path(package_directory, &[&target]);
                if let Some(mut resolved) =
                    self.resolve_candidate_with_package(&candidate, &package_json_path, true)
                {
                    resolved.is_external_library_import = true;
                    return PackageMetadataResolution::Resolved(resolved);
                }
            }
        }
        PackageMetadataResolution::NotApplicable
    }

    fn package_exports_apply(&mut self, package_directory: &str) -> bool {
        self.resolver.options.resolve_package_json_exports
            && matches!(
                self.resolver.options.mode,
                ResolutionMode::Node16 | ResolutionMode::NodeNext | ResolutionMode::Bundler
            )
            && self
                .read_package_json(&join(package_directory, "package.json"))
                .is_some_and(|package| package.exports.is_some_and(|exports| !exports.is_null()))
    }

    fn resolve_package_target(
        &mut self,
        target: &Value,
        package_directory: &str,
        package_json: &str,
        capture: &str,
        is_pattern: bool,
        is_imports: bool,
    ) -> PackageTargetResolution {
        match target {
            Value::String(target) => {
                if !is_pattern && !capture.is_empty() && !target.ends_with('/') {
                    return PackageTargetResolution::NotMatched;
                }
                let expanded = if is_pattern {
                    target.replace('*', capture)
                } else {
                    format!("{target}{capture}")
                };
                if !target.starts_with("./") {
                    if is_imports
                        && !target.starts_with("../")
                        && !is_absolute(target)
                        && let Some(resolved) =
                            self.resolve_bare_package_target(&expanded, package_directory)
                    {
                        return PackageTargetResolution::Resolved(resolved);
                    }
                    return PackageTargetResolution::NotMatched;
                }
                if invalid_package_path(target.trim_start_matches("./"))
                    || invalid_package_path(capture)
                {
                    return PackageTargetResolution::NotMatched;
                }
                let candidate = resolve_path(package_directory, &[&expanded]);
                let external = package_directory.contains("/node_modules/");
                self.resolve_package_map_file(&candidate, package_json, external)
                    .map_or(PackageTargetResolution::NotMatched, |mut resolved| {
                        resolved.is_external_library_import = external;
                        resolved.resolved_using_ts_extension = is_pattern
                            && target.ends_with('*')
                            && is_typescript_extension(&candidate);
                        PackageTargetResolution::Resolved(resolved)
                    })
            }
            Value::Array(targets) => {
                for candidate in targets {
                    let result = self.resolve_package_target(
                        candidate,
                        package_directory,
                        package_json,
                        capture,
                        is_pattern,
                        is_imports,
                    );
                    if !matches!(result, PackageTargetResolution::NotMatched) {
                        return result;
                    }
                }
                PackageTargetResolution::NotMatched
            }
            Value::Object(conditions) => {
                for (condition, candidate) in conditions {
                    if !self.condition_matches(condition) {
                        continue;
                    }
                    let result = self.resolve_package_target(
                        candidate,
                        package_directory,
                        package_json,
                        capture,
                        is_pattern,
                        is_imports,
                    );
                    if !matches!(result, PackageTargetResolution::NotMatched) {
                        return result;
                    }
                }
                PackageTargetResolution::NotMatched
            }
            Value::Null => PackageTargetResolution::Blocked,
            Value::Bool(_) | Value::Number(_) => PackageTargetResolution::NotMatched,
        }
    }

    fn resolve_bare_package_target(
        &mut self,
        specifier: &str,
        package_directory: &str,
    ) -> Option<ResolvedModule> {
        let key = (normalize_path(package_directory), specifier.to_owned());
        if !self.active_package_targets.insert(key.clone()) {
            return None;
        }
        let resolved = if is_absolute_uri_specifier(specifier) {
            self.resolve_path_mapping(specifier)
        } else {
            self.resolve_paths_or_base_url(specifier)
                .or_else(|| self.resolve_package_imports_or_self(specifier, package_directory))
                .or_else(|| self.resolve_node_modules(specifier, package_directory))
                .or_else(|| self.resolve_from_type_roots(specifier, package_directory))
        };
        self.active_package_targets.remove(&key);
        resolved
    }

    fn resolve_candidate_with_package(
        &mut self,
        candidate: &str,
        package_json: &str,
        external: bool,
    ) -> Option<ResolvedModule> {
        if let Some(resolved) = self.resolve_file(candidate, external, Some(package_json)) {
            return Some(resolved);
        }
        if self.resolver.file_system.directory_exists(candidate) {
            return self.resolve_index(candidate, external, Some(package_json));
        }
        None
    }

    fn resolve_package_map_file(
        &mut self,
        candidate: &str,
        package_json: &str,
        external: bool,
    ) -> Option<ResolvedModule> {
        if !path_has_extension(candidate) {
            return None;
        }
        if is_typescript_extension(candidate) {
            return self.try_file(candidate, external, Some(package_json));
        }
        self.resolve_file(candidate, external, Some(package_json))
    }

    fn resolve_relative_candidate(
        &mut self,
        candidate: &str,
        external: bool,
    ) -> Option<ResolvedModule> {
        if self.import_condition
            && matches!(
                self.resolver.options.mode,
                ResolutionMode::Node16 | ResolutionMode::NodeNext
            )
        {
            if !path_has_extension(candidate) {
                return None;
            }
            return self.resolve_file(candidate, external, None);
        }
        self.resolve_candidate(candidate, external)
    }

    fn resolve_candidate(&mut self, candidate: &str, external: bool) -> Option<ResolvedModule> {
        if !candidate.ends_with('/')
            && let Some(resolved) = self.resolve_file(candidate, external, None)
        {
            return Some(resolved);
        }
        if !self.resolver.file_system.directory_exists(candidate) {
            self.failed(FailedLookupKind::Directory, candidate);
            return None;
        }
        self.resolve_directory(candidate, external)
    }

    fn resolve_directory(&mut self, directory: &str, external: bool) -> Option<ResolvedModule> {
        let package_json_path = join(directory, "package.json");
        let package = self.read_package_json(&package_json_path);
        if let Some(package) = package {
            if self.resolver.options.prefer_types
                && let Some(types_versions) = &package.types_versions
            {
                let types_entry = package
                    .typings
                    .as_deref()
                    .or(package.types.as_deref())
                    .unwrap_or("index");
                if let Some(targets) = types_version_targets(types_versions, types_entry) {
                    for target in targets {
                        let candidate = resolve_path(directory, &[&target]);
                        if let Some(mut resolved) = self.resolve_candidate_with_package(
                            &candidate,
                            &package_json_path,
                            external,
                        ) {
                            resolved.package_json = Some(package_json_path.clone());
                            return Some(resolved);
                        }
                    }
                }
            }
            let fields = if self.resolver.options.prefer_types {
                [
                    package.typings.as_deref(),
                    package.types.as_deref(),
                    package.main.as_deref(),
                ]
            } else {
                [
                    package.main.as_deref(),
                    package.typings.as_deref(),
                    package.types.as_deref(),
                ]
            };
            for field in fields.into_iter().flatten() {
                let target = resolve_path(directory, &[field]);
                if let Some(mut resolved) =
                    self.resolve_file(&target, external, Some(&package_json_path))
                {
                    resolved.package_json = Some(package_json_path.clone());
                    return Some(resolved);
                }
                if self.resolver.file_system.directory_exists(&target)
                    && let Some(mut resolved) =
                        self.resolve_index(&target, external, Some(&package_json_path))
                {
                    resolved.package_json = Some(package_json_path.clone());
                    return Some(resolved);
                }
            }
        }
        self.resolve_index(directory, external, None)
    }

    fn resolve_index(
        &mut self,
        directory: &str,
        external: bool,
        package_json: Option<&str>,
    ) -> Option<ResolvedModule> {
        self.resolve_file(&join(directory, "index"), external, package_json)
    }

    fn resolve_file(
        &mut self,
        candidate: &str,
        external: bool,
        package_json: Option<&str>,
    ) -> Option<ResolvedModule> {
        for path in self.file_candidates(candidate) {
            if let Some(resolved) = self.try_file(&path, external, package_json) {
                return Some(resolved);
            }
        }
        None
    }

    fn try_file(
        &mut self,
        path: &str,
        external: bool,
        package_json: Option<&str>,
    ) -> Option<ResolvedModule> {
        for candidate in self.module_suffix_candidates(path) {
            if self.resolver.file_system.file_exists(&candidate) {
                let is_external_library_import = external || candidate.contains("/node_modules/");
                let resolved_file_name = self.resolver.file_system.realpath(&candidate);
                return Some(ResolvedModule {
                    extension: ts_path::extension_from_path(&resolved_file_name),
                    resolved_file_name,
                    original_file_name: candidate,
                    resolved_using_ts_extension: self.specifier_uses_ts_extension
                        && !self.candidate_ending_is_from_config,
                    is_external_library_import,
                    package_json: package_json.map(str::to_owned),
                });
            }
            self.failed(FailedLookupKind::File, &candidate);
        }
        None
    }

    fn module_suffix_candidates(&self, path: &str) -> Vec<String> {
        if self.resolver.options.module_suffixes.is_empty() {
            return vec![path.to_owned()];
        }
        let extension = source_extension(path).unwrap_or("");
        let stem = &path[..path.len() - extension.len()];
        self.resolver
            .options
            .module_suffixes
            .iter()
            .map(|suffix| format!("{stem}{suffix}{extension}"))
            .collect()
    }

    fn file_candidates(&self, candidate: &str) -> Vec<String> {
        let normalized = normalize_path(candidate);
        let extension = source_extension(&normalized);
        if extension.is_none()
            && self.resolver.options.allow_arbitrary_extensions
            && let Some(segment) = normalized.rsplit('/').next()
            && let Some(dot) = segment.rfind('.')
        {
            let extension = &segment[dot..];
            let stem = &normalized[..normalized.len() - extension.len()];
            return vec![format!("{stem}.d{extension}.ts")];
        }
        let stem = extension.map_or_else(
            || normalized.as_str(),
            |extension| &normalized[..normalized.len() - extension.len()],
        );
        let endings: &[&str] = match extension {
            Some(".mjs" | ".mts" | ".d.mts") => &[".mts", ".d.mts", ".mjs"],
            Some(".cjs" | ".cts" | ".d.cts") => &[".cts", ".d.cts", ".cjs"],
            Some(".tsx" | ".jsx") => &[".tsx", ".ts", ".d.ts", ".jsx", ".js"],
            Some(".ts" | ".d.ts" | ".js") | None => {
                if self.resolver.options.allow_javascript {
                    &[".ts", ".tsx", ".d.ts", ".js", ".jsx"]
                } else {
                    &[".ts", ".tsx", ".d.ts"]
                }
            }
            Some(".json") if self.resolver.options.resolve_json => &[".d.json.ts", ".json"],
            Some(".json") => &[".d.json.ts"],
            Some(extension) if self.resolver.options.allow_arbitrary_extensions => {
                return vec![format!("{stem}.d{extension}.ts")];
            }
            Some(_) => &[".d.ts"],
        };
        endings
            .iter()
            .map(|ending| format!("{stem}{ending}"))
            .filter(|path| {
                let extension = source_extension(path);
                let is_javascript = matches!(extension, Some(".js" | ".jsx" | ".mjs" | ".cjs"));
                if is_javascript && !self.resolver.options.allow_javascript {
                    return false;
                }
                match self.extension_priority {
                    ExtensionPriority::All => true,
                    ExtensionPriority::Types => !is_javascript && extension != Some(".json"),
                    ExtensionPriority::JavaScript => is_javascript || extension == Some(".json"),
                }
            })
            .collect()
    }

    fn read_package_json(&mut self, path: &str) -> Option<PackageJson> {
        if !self.package_json_exists(path) {
            self.failed(FailedLookupKind::PackageJson, path);
            return None;
        }
        let contents =
            self.read_package_json_contents(path, PackageJsonInputPurpose::PackageResolution)?;
        parse_package_json(&contents).ok()
    }

    fn package_json_exists(&mut self, path: &str) -> bool {
        let exists = self.resolver.file_system.file_exists(path);
        self.package_json_inputs.file_exists(path, exists);
        exists
    }

    fn read_package_json_contents(
        &mut self,
        path: &str,
        purpose: PackageJsonInputPurpose,
    ) -> Option<String> {
        match self.resolver.file_system.read_file(path) {
            Ok(contents) => {
                self.package_json_inputs.read_text(path, purpose, &contents);
                Some(contents)
            }
            Err(error) => {
                self.package_json_inputs.read_error(path, purpose, &error);
                None
            }
        }
    }

    fn failed(&mut self, kind: FailedLookupKind, path: &str) {
        self.failed_lookups.push(FailedLookup {
            kind,
            path: normalize_path(path),
        });
    }
}

/// Parses the package fields used by foundational Node resolution.
///
/// # Errors
///
/// Returns `serde_json::Error` when `contents` is not valid JSON.
pub fn parse_package_json(contents: &str) -> serde_json::Result<PackageJson> {
    let value: Value = serde_json::from_str(contents)?;
    Ok(PackageJson {
        types: string_field(&value, "types"),
        typings: string_field(&value, "typings"),
        main: string_field(&value, "main"),
        package_type: string_field(&value, "type"),
        exports: value.get("exports").cloned(),
        types_versions: value.get("typesVersions").cloned(),
        name: string_field(&value, "name"),
        imports: value.get("imports").cloned(),
    })
}

/// Whether a bare specifier is an absolute URL or another URI-style scheme.
#[must_use]
pub fn is_absolute_uri_specifier(specifier: &str) -> bool {
    ts_path::is_url(specifier)
        || (!is_relative(specifier) && !is_absolute(specifier) && specifier.contains(':'))
}

fn best_path_match(
    paths: &BTreeMap<String, Vec<String>>,
    specifier: &str,
) -> Option<(String, Vec<String>)> {
    if let Some(substitutions) = paths.get(specifier) {
        return Some((String::new(), substitutions.clone()));
    }
    let mut best: Option<(usize, &str, &[String])> = None;
    for (pattern, substitutions) in paths {
        let Some(star) = pattern.find('*') else {
            continue;
        };
        if pattern[star + 1..].contains('*') {
            continue;
        }
        let Some(capture) = match_pattern(pattern, specifier) else {
            continue;
        };
        if best
            .as_ref()
            .is_none_or(|(prefix_length, _, _)| star > *prefix_length)
        {
            best = Some((star, capture, substitutions.as_slice()));
        }
    }
    best.map(|(_, capture, substitutions)| (capture.to_owned(), substitutions.to_vec()))
}

fn match_pattern<'a>(pattern: &str, value: &'a str) -> Option<&'a str> {
    let Some(star) = pattern.find('*') else {
        return (pattern == value).then_some("");
    };
    let (prefix, suffix_with_star) = pattern.split_at(star);
    let suffix = &suffix_with_star[1..];
    value
        .strip_prefix(prefix)?
        .strip_suffix(suffix)
        .filter(|_| value.len() >= prefix.len() + suffix.len())
}

fn path_suffix<'a>(path: &'a str, root: &str) -> Option<&'a str> {
    let suffix = path.strip_prefix(root)?;
    if suffix.is_empty() {
        Some("")
    } else {
        suffix.strip_prefix('/')
    }
}

fn package_export_match<'a>(exports: &'a Value, key: &str) -> Option<PackageMapMatch<'a>> {
    if let Some(object) = exports.as_object() {
        let has_subpaths = object.keys().any(|name| name.starts_with('.'));
        if has_subpaths {
            if object.keys().any(|name| !name.starts_with('.')) {
                return None;
            }
            return package_map_match(exports, key);
        }
    }
    (key == ".").then(|| PackageMapMatch {
        target: exports,
        capture: String::new(),
        is_pattern: false,
    })
}

fn package_map_match<'a>(map: &'a Value, key: &str) -> Option<PackageMapMatch<'a>> {
    let object = map.as_object()?;
    if !key.ends_with('/')
        && !key.contains('*')
        && let Some(target) = object.get(key)
    {
        return Some(PackageMapMatch {
            target,
            capture: String::new(),
            is_pattern: false,
        });
    }
    object
        .iter()
        .filter_map(|(pattern, target)| {
            let star = pattern.find('*');
            let capture = if let Some(index) = star {
                if pattern[index + 1..].contains('*') {
                    return None;
                }
                match_pattern(pattern, key)?
            } else if pattern.ends_with('/') {
                key.strip_prefix(pattern)?
            } else {
                return None;
            };
            let prefix_length = star.map_or(pattern.len(), |index| index + 1);
            Some((
                (prefix_length, star.is_some(), pattern.len()),
                PackageMapMatch {
                    target,
                    capture: capture.to_owned(),
                    is_pattern: star.is_some(),
                },
            ))
        })
        .max_by_key(|(specificity, _)| *specificity)
        .map(|(_, matched)| matched)
}

fn invalid_package_path(path: &str) -> bool {
    path.split('/')
        .any(|segment| matches!(segment, "." | ".." | "node_modules"))
}

fn mangled_scoped_package_name(specifier: &str) -> String {
    specifier
        .strip_prefix('@')
        .and_then(|name| name.split_once('/'))
        .map_or_else(
            || specifier.to_owned(),
            |(scope, package)| format!("{scope}__{package}"),
        )
}

fn types_package_name(specifier: &str) -> Option<String> {
    if specifier.starts_with("@types/") || specifier.starts_with('#') {
        return None;
    }
    let (package, rest) = parse_package_name(specifier)?;
    let package = mangled_scoped_package_name(package);
    Some(if rest.is_empty() {
        format!("@types/{package}")
    } else {
        format!("@types/{package}/{rest}")
    })
}

/// Returns explicit type roots or ancestor `node_modules/@types` directories.
#[must_use]
pub fn effective_type_roots(options: &ResolutionOptions, current_directory: &str) -> Vec<String> {
    options.type_roots.clone().unwrap_or_else(|| {
        ancestors(current_directory)
            .into_iter()
            .map(|directory| join(&join(&directory, "node_modules"), "@types"))
            .collect()
    })
}

/// Lists automatic type directive package names in stable order.
#[must_use]
pub fn automatic_type_directive_names(
    file_system: &dyn FileSystem,
    options: &ResolutionOptions,
    current_directory: &str,
) -> Vec<String> {
    if let Some(types) = &options.types
        && !types.iter().any(|name| name == "*")
    {
        return types.clone();
    }
    let mut installed = Vec::new();
    let mut seen = BTreeSet::new();
    for root in effective_type_roots(options, current_directory) {
        if let Ok(entries) = file_system.read_directory(&root) {
            for name in entries.directories {
                let package_json = join(&join(&root, &name), "package.json");
                let is_not_needed = file_system
                    .read_file(&package_json)
                    .ok()
                    .and_then(|contents| serde_json::from_str::<Value>(&contents).ok())
                    .is_some_and(|package| package.get("typings").is_some_and(Value::is_null));
                if !name.starts_with('.') && !is_not_needed && seen.insert(name.clone()) {
                    installed.push(name);
                }
            }
        }
    }
    let names = options.types.as_ref().map_or_else(
        || installed.clone(),
        |types| {
            types
                .iter()
                .flat_map(|name| {
                    if name == "*" {
                        installed.clone()
                    } else {
                        vec![name.clone()]
                    }
                })
                .collect()
        },
    );
    let mut seen = BTreeSet::new();
    names
        .into_iter()
        .filter(|name| seen.insert(name.clone()))
        .collect()
}

fn types_version_targets(types_versions: &Value, rest: &str) -> Option<Vec<String>> {
    let versions = types_versions.as_object()?;
    let compiler_version = Version::parse(env!("CARGO_PKG_VERSION")).ok()?;
    let mapping = versions.iter().find_map(|(range, mapping)| {
        VersionRange::parse(range)
            .ok()
            .filter(|range| range.test(&compiler_version))
            .and_then(|_| mapping.as_object())
    })?;
    let (capture, targets) = if let Some(targets) = mapping.get(rest) {
        ("", targets.as_array()?)
    } else {
        let mut best: Option<(usize, &str, &Value)> = None;
        for (pattern, targets) in mapping {
            let Some(star) = pattern.find('*') else {
                continue;
            };
            if pattern[star + 1..].contains('*') {
                continue;
            }
            let Some(capture) = match_pattern(pattern, rest) else {
                continue;
            };
            if best
                .as_ref()
                .is_none_or(|(prefix_length, _, _)| star > *prefix_length)
            {
                best = Some((star, capture, targets));
            }
        }
        let (_, capture, targets) = best?;
        (capture, targets.as_array()?)
    };
    Some(
        targets
            .iter()
            .filter_map(Value::as_str)
            .map(|target| target.replace('*', capture))
            .collect(),
    )
}

fn string_field(value: &Value, field: &str) -> Option<String> {
    value.get(field)?.as_str().map(str::to_owned)
}

fn source_extension(path: &str) -> Option<&'static str> {
    [
        ".d.mts", ".d.cts", ".d.ts", ".mjs", ".mts", ".cjs", ".cts", ".tsx", ".jsx", ".json",
        ".ts", ".js",
    ]
    .into_iter()
    .find(|extension| path.ends_with(extension))
}

fn path_has_extension(path: &str) -> bool {
    path.rsplit('/')
        .next()
        .is_some_and(|name| name.contains('.'))
}

fn is_typescript_extension(path: &str) -> bool {
    matches!(
        source_extension(path),
        Some(".ts" | ".tsx" | ".mts" | ".cts" | ".d.ts" | ".d.mts" | ".d.cts")
    )
}

fn parse_package_name(specifier: &str) -> Option<(&str, &str)> {
    if specifier.starts_with('#') {
        return None;
    }
    if let Some(scoped) = specifier.strip_prefix('@') {
        let first_slash = scoped.find('/')? + 1;
        let after_scope = &specifier[first_slash + 1..];
        let package_end = after_scope
            .find('/')
            .map_or(specifier.len(), |index| first_slash + 1 + index);
        let package_name = &specifier[..package_end];
        let rest = specifier.get(package_end + 1..).unwrap_or("");
        Some((package_name, rest))
    } else {
        let package_end = specifier.find('/').unwrap_or(specifier.len());
        let package_name = &specifier[..package_end];
        if package_name.is_empty() {
            return None;
        }
        let rest = specifier.get(package_end + 1..).unwrap_or("");
        Some((package_name, rest))
    }
}

fn directory_path(path: &str) -> String {
    let normalized = normalize_path(path);
    let root = root_length(&normalized);
    let trimmed = normalized.trim_end_matches('/');
    let last_slash = trimmed.rfind('/').unwrap_or(root.saturating_sub(1));
    if last_slash < root {
        normalized[..root].to_owned()
    } else {
        normalized[..last_slash].to_owned()
    }
}

fn join(left: &str, right: &str) -> String {
    resolve_path(left, &[right])
}

fn ancestors(path: &str) -> Vec<String> {
    let mut result = Vec::new();
    let normalized = normalize_path(path);
    let root = root_length(&normalized);
    let mut current = if normalized.len() == root {
        normalized
    } else {
        normalized.trim_end_matches('/').to_owned()
    };
    loop {
        result.push(current.clone());
        let parent = directory_path(&current);
        if parent == current || parent.len() < root_length(&current) {
            break;
        }
        current = parent;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use ts_vfs::MemoryFileSystem;

    fn fs(files: &[(&str, &str)]) -> MemoryFileSystem {
        let fs = MemoryFileSystem::new(true);
        for (path, contents) in files {
            fs.write_file(path, contents).unwrap();
        }
        fs
    }

    #[test]
    fn derives_node_formats_from_fixed_extensions_and_nearest_package_scope() {
        let fs = fs(&[
            ("/repo/package.json", r#"{"type":"module"}"#),
            ("/repo/nested/package.json", r#"{"type":"commonjs"}"#),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );

        let esm_declaration = resolver.file_module_facts("/repo/types/index.d.mts");
        assert_eq!(esm_declaration.format, Some(ModuleFormat::Esm));
        assert!(esm_declaration.is_declaration_file);
        assert!(esm_declaration.has_fixed_format);
        assert_eq!(
            esm_declaration.package_json.as_deref(),
            Some("/repo/package.json")
        );

        let commonjs_declaration = resolver.file_module_facts("/repo/types/index.d.cts");
        assert_eq!(commonjs_declaration.format, Some(ModuleFormat::CommonJs));
        assert!(commonjs_declaration.is_declaration_file);
        assert!(commonjs_declaration.has_fixed_format);

        let package_module = resolver.file_module_facts("/repo/src/index.ts");
        assert_eq!(package_module.format, Some(ModuleFormat::Esm));
        assert!(!package_module.is_declaration_file);
        assert!(!package_module.has_fixed_format);
        assert_eq!(package_module.package_type.as_deref(), Some("module"));

        let nested_commonjs = resolver.file_module_facts("/repo/nested/index.d.ts");
        assert_eq!(nested_commonjs.format, Some(ModuleFormat::CommonJs));
        assert!(nested_commonjs.is_declaration_file);
        assert_eq!(nested_commonjs.package_type.as_deref(), Some("commonjs"));

        assert_eq!(resolver.file_module_facts("/repo/data.json").format, None);
    }

    #[test]
    fn mode_aware_resolution_caches_import_and_require_targets_separately() {
        let fs = fs(&[
            ("/app/package.json", r#"{"type":"module"}"#),
            (
                "/app/node_modules/pkg/package.json",
                r#"{"exports":{".":{"import":"./esm.d.mts","require":"./commonjs.d.cts"}}}"#,
            ),
            ("/app/node_modules/pkg/esm.d.mts", ""),
            ("/app/node_modules/pkg/commonjs.d.cts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );

        let expected_esm = "/app/node_modules/pkg/esm.d.mts";
        let expected_commonjs = "/app/node_modules/pkg/commonjs.d.cts";
        assert_eq!(
            resolver
                .resolve("pkg", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            expected_esm
        );
        assert_eq!(
            resolver
                .resolve_with_mode("pkg", "/app/main.ts", ModuleFormat::CommonJs)
                .resolved
                .unwrap()
                .resolved_file_name,
            expected_commonjs
        );
        assert_eq!(
            resolver
                .resolve_with_mode("pkg", "/app/main.ts", ModuleFormat::Esm)
                .resolved
                .unwrap()
                .resolved_file_name,
            expected_esm
        );
        assert_eq!(
            resolver
                .resolve_with_mode("pkg", "/app/main.ts", ModuleFormat::CommonJs)
                .resolved
                .unwrap()
                .resolved_file_name,
            expected_commonjs
        );
    }

    #[test]
    fn package_type_applies_to_node_resolution_or_installed_dependencies() {
        let fs = fs(&[
            ("/repo/package.json", r#"{"type":"module"}"#),
            (
                "/repo/node_modules/pkg/package.json",
                r#"{"type":"module"}"#,
            ),
        ]);
        let bundler = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                ..ResolutionOptions::default()
            },
        );

        let local = bundler.file_module_facts("/repo/source.ts");
        assert_eq!(local.format, Some(ModuleFormat::CommonJs));
        assert!(local.package_type.is_none());

        let dependency = bundler.file_module_facts("/repo/node_modules/pkg/index.d.ts");
        assert_eq!(dependency.format, Some(ModuleFormat::Esm));
        assert_eq!(dependency.package_type.as_deref(), Some("module"));
    }

    #[test]
    fn resolves_relative_files_with_typescript_substitution() {
        let fs = fs(&[("/src/lib.ts", "")]);
        let result =
            Resolver::new(&fs, ResolutionOptions::default()).resolve("./lib.js", "/src/main.ts");
        let resolved = result.resolved.unwrap();
        assert_eq!(resolved.resolved_file_name, "/src/lib.ts");
        assert_eq!(resolved.extension, Some(FileExtension::Ts));
        assert!(!resolved.is_external_library_import);
        assert!(!resolved.resolved_using_ts_extension);
    }

    #[test]
    fn node_esm_requires_explicit_relative_file_extensions() {
        let fs = fs(&[
            ("/repo/package.json", r#"{"type":"module"}"#),
            ("/repo/entry.ts", ""),
            ("/repo/directory/index.ts", ""),
        ]);
        let node = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );

        assert!(node.resolve("./entry", "/repo/main.ts").resolved.is_none());
        assert!(
            node.resolve("./directory", "/repo/main.ts")
                .resolved
                .is_none()
        );
        assert_eq!(
            node.resolve("./entry.js", "/repo/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/entry.ts"
        );
        assert_eq!(
            node.resolve_with_mode("./entry", "/repo/main.ts", ModuleFormat::CommonJs)
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/entry.ts"
        );

        let bundler = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                ..ResolutionOptions::default()
            },
        );
        assert_eq!(
            bundler
                .resolve("./entry", "/repo/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/entry.ts"
        );
    }

    #[test]
    fn absolute_uri_specifiers_skip_filesystem_resolution_without_a_path_mapping() {
        let filesystem = fs(&[
            ("/project/node_modules/foo/index.d.ts", ""),
            ("/project/node_modules/node:fs/index.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &filesystem,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                ..ResolutionOptions::default()
            },
        );

        for specifier in [
            "https://deno.land/std@0.208.0/path/mod.ts",
            "node:fs",
            "data:text/javascript,export%20default%201",
        ] {
            let result = resolver.resolve(specifier, "/project/index.ts");
            assert!(
                result.resolved.is_none(),
                "unexpected resolution: {specifier}"
            );
            assert!(
                result.failed_lookups.is_empty(),
                "URI specifiers must not probe files: {specifier}"
            );
        }

        assert!(is_absolute_uri_specifier("https://example.test/mod.ts"));
        assert!(is_absolute_uri_specifier("node:fs"));
        assert!(!is_absolute_uri_specifier("./folder:value.js"));
        assert!(!is_absolute_uri_specifier("C:/project/file.ts"));
    }

    #[test]
    fn explicit_paths_can_override_absolute_uri_specifiers() {
        let filesystem = fs(&[("/project/local.d.ts", "")]);
        let resolver = Resolver::new(
            &filesystem,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                base_url: Some("/project".into()),
                paths: BTreeMap::from([(
                    "https://example.test/types".into(),
                    vec!["./local.d.ts".into()],
                )]),
                ..ResolutionOptions::default()
            },
        );

        assert_eq!(
            resolver
                .resolve("https://example.test/types", "/project/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/project/local.d.ts"
        );
    }

    #[test]
    fn records_typescript_extensions_written_in_relative_specifiers() {
        let fs = fs(&[("/src/lib.ts", ""), ("/src/types.d.ts", "")]);
        let resolver = Resolver::new(&fs, ResolutionOptions::default());

        assert!(
            resolver
                .resolve("./lib.ts", "/src/main.ts")
                .resolved
                .unwrap()
                .resolved_using_ts_extension
        );
        assert!(
            resolver
                .resolve("./types.d.ts", "/src/main.ts")
                .resolved
                .unwrap()
                .resolved_using_ts_extension
        );
        assert!(
            !resolver
                .resolve("./lib.js", "/src/main.ts")
                .resolved
                .unwrap()
                .resolved_using_ts_extension
        );
    }

    #[test]
    fn resolves_scoped_packages_from_the_filesystem_root() {
        let fs = fs(&[(
            "/node_modules/@fullcalendar/react/index.d.ts",
            "export default class FullCalendar {}",
        )]);
        let result = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                ..ResolutionOptions::default()
            },
        )
        .resolve("@fullcalendar/react", "/index.tsx");
        assert_eq!(
            result.resolved.unwrap().resolved_file_name,
            "/node_modules/@fullcalendar/react/index.d.ts"
        );
    }

    #[test]
    fn uses_package_typings_then_main_and_index() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"typings":"types/entry.d.ts","main":"dist/main.js"}"#,
            ),
            ("/app/node_modules/pkg/types/entry.d.ts", ""),
            (
                "/app/node_modules/typepkg/package.json",
                r#"{"types":"types.d.ts","main":"runtime.js"}"#,
            ),
            ("/app/node_modules/typepkg/types.d.ts", ""),
            (
                "/app/node_modules/mainpkg/package.json",
                r#"{"main":"dist/main.js"}"#,
            ),
            ("/app/node_modules/mainpkg/dist/main.ts", ""),
            ("/app/node_modules/fallback/index.ts", ""),
        ]);
        let resolver = Resolver::new(&fs, ResolutionOptions::default());
        let package = resolver
            .resolve("pkg", "/app/src/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            package.resolved_file_name,
            "/app/node_modules/pkg/types/entry.d.ts"
        );
        assert!(package.is_external_library_import);
        let types = resolver
            .resolve("typepkg", "/app/src/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            types.resolved_file_name,
            "/app/node_modules/typepkg/types.d.ts"
        );
        let main = resolver
            .resolve("mainpkg", "/app/src/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            main.resolved_file_name,
            "/app/node_modules/mainpkg/dist/main.ts"
        );
        let fallback = resolver
            .resolve("fallback", "/app/src/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            fallback.resolved_file_name,
            "/app/node_modules/fallback/index.ts"
        );
    }

    #[test]
    fn walks_node_modules_ancestors_and_resolves_subpaths() {
        let fs = fs(&[("/repo/node_modules/@scope/pkg/subpath.ts", "")]);
        let result = Resolver::new(&fs, ResolutionOptions::default())
            .resolve("@scope/pkg/subpath", "/repo/packages/app/src/main.ts");
        assert_eq!(
            result.resolved.unwrap().resolved_file_name,
            "/repo/node_modules/@scope/pkg/subpath.ts"
        );
    }

    #[test]
    fn records_failed_file_directory_and_package_lookups() {
        let fs = MemoryFileSystem::new(true);
        let result =
            Resolver::new(&fs, ResolutionOptions::default()).resolve("./missing", "/src/main.ts");
        assert!(result.resolved.is_none());
        assert!(result.failed_lookups.iter().any(|lookup| {
            lookup.kind == FailedLookupKind::File && lookup.path == "/src/missing.ts"
        }));
        assert!(result.failed_lookups.iter().any(|lookup| {
            lookup.kind == FailedLookupKind::Directory && lookup.path == "/src/missing"
        }));
    }

    #[test]
    fn honors_javascript_and_json_options() {
        let fs = fs(&[("/src/value.js", ""), ("/src/data.json", "{}")]);
        let no_js = ResolutionOptions {
            allow_javascript: false,
            ..ResolutionOptions::default()
        };
        assert!(
            Resolver::new(&fs, no_js)
                .resolve("./value", "/src/main.ts")
                .resolved
                .is_none()
        );
        let json = ResolutionOptions {
            resolve_json: true,
            ..ResolutionOptions::default()
        };
        assert_eq!(
            Resolver::new(&fs, json)
                .resolve("./data.json", "/src/main.ts")
                .resolved
                .unwrap()
                .extension,
            Some(FileExtension::Json)
        );
    }

    #[test]
    fn resolves_arbitrary_extensions_to_declaration_companions() {
        let fs = fs(&[("/src/data.d.html.ts", "")]);
        let options = ResolutionOptions {
            allow_arbitrary_extensions: true,
            ..ResolutionOptions::default()
        };
        assert_eq!(
            Resolver::new(&fs, options)
                .resolve("./data.html", "/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/src/data.d.html.ts"
        );
    }

    #[test]
    fn resolves_base_url_paths_with_wildcards_and_fallbacks() {
        let fs = fs(&[
            ("/repo/src/lib/exact.ts", ""),
            ("/repo/generated/models/user.ts", ""),
            ("/repo/src/plain.ts", ""),
        ]);
        let options = ResolutionOptions {
            base_url: Some("/repo".into()),
            paths: BTreeMap::from([
                (
                    "@lib/exact".into(),
                    vec!["missing.ts".into(), "src/lib/exact".into()],
                ),
                ("@models/*".into(), vec!["generated/models/*".into()]),
            ]),
            ..ResolutionOptions::default()
        };
        let resolver = Resolver::new(&fs, options);
        assert_eq!(
            resolver
                .resolve("@lib/exact", "/repo/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/src/lib/exact.ts"
        );
        assert_eq!(
            resolver
                .resolve("@models/user", "/repo/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/generated/models/user.ts"
        );
        assert_eq!(
            resolver
                .resolve("src/plain", "/repo/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/src/plain.ts"
        );
    }

    #[test]
    fn paths_prefer_exact_matches_then_the_longest_wildcard_prefix() {
        let fs = fs(&[
            ("/repo/exact.d.ts", ""),
            ("/repo/empty-capture.d.ts", ""),
            ("/repo/broad/deep/tool.d.ts", ""),
            ("/repo/deep/tool.development.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                base_url: Some("/repo".into()),
                paths: BTreeMap::from([
                    ("foo/*bar.js".into(), vec!["empty-capture".into()]),
                    ("foo/bar.js".into(), vec!["exact".into()]),
                    ("pkg/*.development.js".into(), vec!["broad/*".into()]),
                    ("pkg/deep/*".into(), vec!["deep/*".into()]),
                ]),
                ..ResolutionOptions::default()
            },
        );

        assert_eq!(
            resolver
                .resolve("foo/bar.js", "/repo/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/exact.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("pkg/deep/tool.development.js", "/repo/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/deep/tool.development.d.ts"
        );
    }

    #[test]
    fn trailing_directory_paths_prefer_nested_package_types_over_at_types() {
        let fs = fs(&[
            (
                "/repo/node_modules/preact/compat/package.json",
                r#"{"name":"preact-compat","types":"./index.d.ts"}"#,
            ),
            ("/repo/node_modules/preact/compat/index.d.ts", ""),
            ("/repo/node_modules/@types/react/index.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                base_url: Some("/repo".into()),
                paths: BTreeMap::from([(
                    "react".into(),
                    vec!["./node_modules/preact/compat/".into()],
                )]),
                ..ResolutionOptions::default()
            },
        );

        assert_eq!(
            resolver
                .resolve("react", "/repo/app.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/node_modules/preact/compat/index.d.ts"
        );
    }

    #[test]
    fn paths_into_node_modules_remain_external_before_symlink_resolution() {
        let filesystem = fs(&[
            ("/repo/node_modules/direct/index.d.ts", ""),
            ("/workspace/linked/index.d.ts", ""),
            ("/repo/src/local.d.ts", ""),
        ]);
        filesystem.add_directory_link("/workspace/linked", "/repo/node_modules/linked");
        let resolver = Resolver::new(
            &filesystem,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                base_url: Some("/repo".into()),
                paths: BTreeMap::from([
                    (
                        "direct".into(),
                        vec!["./node_modules/direct/index.d.ts".into()],
                    ),
                    (
                        "linked".into(),
                        vec!["./node_modules/linked/index.d.ts".into()],
                    ),
                    ("local".into(), vec!["./src/local.d.ts".into()]),
                ]),
                ..ResolutionOptions::default()
            },
        );

        let direct = resolver
            .resolve("direct", "/repo/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            direct.resolved_file_name,
            "/repo/node_modules/direct/index.d.ts"
        );
        assert!(direct.is_external_library_import);

        let linked = resolver
            .resolve("linked", "/repo/main.ts")
            .resolved
            .unwrap();
        assert_eq!(linked.resolved_file_name, "/workspace/linked/index.d.ts");
        assert!(linked.is_external_library_import);

        let local = resolver.resolve("local", "/repo/main.ts").resolved.unwrap();
        assert_eq!(local.resolved_file_name, "/repo/src/local.d.ts");
        assert!(!local.is_external_library_import);
    }

    #[test]
    fn configured_path_extensions_do_not_count_as_imported_typescript_extensions() {
        let fs = fs(&[("/repo/some-path/index.d.ts", "")]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                base_url: Some("/repo".into()),
                paths: BTreeMap::from([("some-path".into(), vec!["./some-path/index.ts".into()])]),
                ..ResolutionOptions::default()
            },
        );
        let target = resolver
            .resolve("some-path", "/repo/named-import.ts")
            .resolved
            .unwrap();

        assert_eq!(target.resolved_file_name, "/repo/some-path/index.d.ts");
        assert!(!target.resolved_using_ts_extension);
    }

    #[test]
    fn resolves_rooted_specifiers_through_paths_with_real_root_fallback() {
        let fs = fs(&[("/repo/src/foo.ts", ""), ("/bar.ts", "")]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                base_url: Some("/repo".into()),
                paths: BTreeMap::from([("/*".into(), vec!["./src/*".into()])]),
                ..ResolutionOptions::default()
            },
        );
        assert_eq!(
            resolver
                .resolve("/foo", "/repo/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/src/foo.ts"
        );
        assert_eq!(
            resolver
                .resolve("/bar", "/repo/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/bar.ts"
        );
    }

    #[test]
    fn resolves_relative_modules_across_root_dirs() {
        let fs = fs(&[("/generated/views/template.ts", "")]);
        let options = ResolutionOptions {
            root_dirs: vec!["/src".into(), "/generated".into()],
            ..ResolutionOptions::default()
        };
        let result = Resolver::new(&fs, options).resolve("./template", "/src/views/page.ts");
        assert_eq!(
            result.resolved.unwrap().resolved_file_name,
            "/generated/views/template.ts"
        );
    }

    #[test]
    fn resolves_package_exports_and_types_conditions() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"exports":{".":{"types":"./types/index.d.ts","default":"./dist/index.js"},"./features/*":{"types":"./types/features/*.d.ts","default":"./dist/features/*.js"}}}"#,
            ),
            ("/app/node_modules/pkg/types/index.d.ts", ""),
            ("/app/node_modules/pkg/types/features/tool.d.ts", ""),
            ("/app/node_modules/pkg/private.ts", ""),
        ]);
        let options = ResolutionOptions {
            mode: ResolutionMode::NodeNext,
            ..ResolutionOptions::default()
        };
        let resolver = Resolver::new(&fs, options);
        assert_eq!(
            resolver
                .resolve("pkg", "/app/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/types/index.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("pkg/features/tool", "/app/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/types/features/tool.d.ts"
        );
        assert!(
            resolver
                .resolve("pkg/private", "/app/src/main.ts")
                .resolved
                .is_none()
        );
    }

    #[test]
    fn package_exports_use_exact_declarations_and_require_explicit_targets() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"exports":{".":"./types/index.d.ts","./implicit":"./types/implicit","./directory":"./types/folder"}}"#,
            ),
            ("/app/node_modules/pkg/types/index.ts", ""),
            ("/app/node_modules/pkg/types/index.d.ts", ""),
            ("/app/node_modules/pkg/types/implicit.d.ts", ""),
            ("/app/node_modules/pkg/types/folder/index.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                ..ResolutionOptions::default()
            },
        );

        assert_eq!(
            resolver
                .resolve("pkg", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/types/index.d.ts"
        );
        assert!(
            resolver
                .resolve("pkg/implicit", "/app/main.ts")
                .resolved
                .is_none()
        );
        assert!(
            resolver
                .resolve("pkg/directory", "/app/main.ts")
                .resolved
                .is_none()
        );
    }

    #[test]
    fn package_conditions_follow_json_order_and_skip_unresolved_targets() {
        let fs = fs(&[
            (
                "/app/node_modules/ordered/package.json",
                r#"{"exports":{".":{"default":"./default.d.ts","types":"./types.d.ts"}}}"#,
            ),
            ("/app/node_modules/ordered/default.d.ts", ""),
            ("/app/node_modules/ordered/types.d.ts", ""),
            (
                "/app/node_modules/fallback/package.json",
                r#"{"exports":{".":{"types":"./missing.d.ts","default":"./runtime.js"}}}"#,
            ),
            ("/app/node_modules/fallback/runtime.d.ts", ""),
            (
                "/app/node_modules/array/package.json",
                r#"{"exports":{".":{"types":["./missing.d.ts","./actual.d.ts"]}}}"#,
            ),
            ("/app/node_modules/array/actual.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                ..ResolutionOptions::default()
            },
        );

        assert_eq!(
            resolver
                .resolve("ordered", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/ordered/default.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("fallback", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/fallback/runtime.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("array", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/array/actual.d.ts"
        );
    }

    #[test]
    fn node_conditions_follow_source_format_and_package_type() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"exports":{".":{"import":"./esm.d.mts","require":"./commonjs.d.cts"}}}"#,
            ),
            ("/app/node_modules/pkg/esm.d.mts", ""),
            ("/app/node_modules/pkg/commonjs.d.cts", ""),
            ("/app/esm/package.json", r#"{"type":"module"}"#),
            ("/app/commonjs/package.json", r#"{"type":"commonjs"}"#),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );

        for containing_file in ["/app/esm/main.ts", "/app/main.mts"] {
            assert_eq!(
                resolver
                    .resolve("pkg", containing_file)
                    .resolved
                    .unwrap()
                    .resolved_file_name,
                "/app/node_modules/pkg/esm.d.mts"
            );
        }
        for containing_file in ["/app/commonjs/main.ts", "/app/main.cts"] {
            assert_eq!(
                resolver
                    .resolve("pkg", containing_file)
                    .resolved
                    .unwrap()
                    .resolved_file_name,
                "/app/node_modules/pkg/commonjs.d.cts"
            );
        }
    }

    #[test]
    fn node_condition_is_excluded_from_bundler_resolution() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"exports":{".":{"node":"./node.d.ts","default":"./browser.d.ts"}}}"#,
            ),
            ("/app/node_modules/pkg/node.d.ts", ""),
            ("/app/node_modules/pkg/browser.d.ts", ""),
        ]);

        for (mode, expected) in [
            (ResolutionMode::Node16, "/app/node_modules/pkg/node.d.ts"),
            (
                ResolutionMode::Bundler,
                "/app/node_modules/pkg/browser.d.ts",
            ),
        ] {
            assert_eq!(
                Resolver::new(
                    &fs,
                    ResolutionOptions {
                        mode,
                        ..ResolutionOptions::default()
                    },
                )
                .resolve("pkg", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
                expected
            );
        }
    }

    #[test]
    fn custom_package_conditions_follow_package_json_order() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"exports":{".":{"development":"./development.d.ts","browser":"./browser.d.ts","default":"./default.d.ts"}}}"#,
            ),
            ("/app/node_modules/pkg/development.d.ts", ""),
            ("/app/node_modules/pkg/browser.d.ts", ""),
            ("/app/node_modules/pkg/default.d.ts", ""),
        ]);

        let configured = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                custom_conditions: vec!["browser".into(), "development".into()],
                ..ResolutionOptions::default()
            },
        );
        assert_eq!(
            configured
                .resolve("pkg", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/development.d.ts"
        );

        let defaults = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                ..ResolutionOptions::default()
            },
        );
        assert_eq!(
            defaults
                .resolve("pkg", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/default.d.ts"
        );
    }

    #[test]
    fn package_exports_accept_matching_versioned_types_conditions() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"exports":{".":{"types@<7":"./old.d.ts","types@>=7":"./current.d.ts","types":"./fallback.d.ts"}}}"#,
            ),
            ("/app/node_modules/pkg/old.d.ts", ""),
            ("/app/node_modules/pkg/current.d.ts", ""),
            ("/app/node_modules/pkg/fallback.d.ts", ""),
        ]);
        let resolved = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        )
        .resolve("pkg", "/app/main.ts")
        .resolved
        .unwrap();

        assert_eq!(
            resolved.resolved_file_name,
            "/app/node_modules/pkg/current.d.ts"
        );
    }

    #[test]
    fn package_patterns_prioritize_the_longest_prefix() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"exports":{"./features/*.development.js":"./broad/*.d.ts","./features/deep/*":"./deep/*.d.ts","./legacy/":"./legacy-types/"}}"#,
            ),
            ("/app/node_modules/pkg/broad/deep/tool.d.ts", ""),
            ("/app/node_modules/pkg/deep/tool.development.js.d.ts", ""),
            ("/app/node_modules/pkg/legacy-types/item.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                ..ResolutionOptions::default()
            },
        );

        assert_eq!(
            resolver
                .resolve("pkg/features/deep/tool.development.js", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/deep/tool.development.js.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("pkg/legacy/item.js", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/legacy-types/item.d.ts"
        );
    }

    #[test]
    fn null_root_exports_use_legacy_fields_but_null_conditions_block_fallback() {
        let fs = fs(&[
            (
                "/app/node_modules/legacy/package.json",
                r#"{"types":"./legacy.d.ts","exports":null}"#,
            ),
            ("/app/node_modules/legacy/legacy.d.ts", ""),
            (
                "/app/node_modules/blocked/package.json",
                r#"{"exports":{".":{"types":null,"default":"./default.d.ts"}}}"#,
            ),
            ("/app/node_modules/blocked/default.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );

        assert_eq!(
            resolver
                .resolve("legacy", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/legacy/legacy.d.ts"
        );
        assert!(
            resolver
                .resolve("blocked", "/app/main.ts")
                .resolved
                .is_none()
        );
    }

    #[test]
    fn package_maps_reject_paths_that_leave_the_package() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"exports":{".":"../outside.d.ts","./unsafe/*":"./types/*"}}"#,
            ),
            ("/app/node_modules/outside.d.ts", ""),
            ("/app/node_modules/pkg/private.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                ..ResolutionOptions::default()
            },
        );

        assert!(resolver.resolve("pkg", "/app/main.ts").resolved.is_none());
        assert!(
            resolver
                .resolve("pkg/unsafe/../private", "/app/main.ts")
                .resolved
                .is_none()
        );
    }

    #[test]
    fn disabled_package_exports_use_legacy_package_resolution() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"types":"./legacy/index.d.ts","exports":{".":"./public/index.d.ts"}}"#,
            ),
            ("/app/node_modules/pkg/legacy/index.d.ts", ""),
            ("/app/node_modules/pkg/public/index.d.ts", ""),
            ("/app/node_modules/pkg/private.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                resolve_package_json_exports: false,
                ..ResolutionOptions::default()
            },
        );

        assert_eq!(
            resolver
                .resolve("pkg", "/app/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/legacy/index.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("pkg/private", "/app/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/private.ts"
        );
    }

    #[test]
    fn resolves_package_types_versions_subpaths() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"typesVersions":{"<7":{"feature/*":["old/feature/*"]},">=7":{"feature/*":["types/feature/*"],"*":["types/*"]}}}"#,
            ),
            ("/app/node_modules/pkg/old/feature/tool.d.ts", ""),
            ("/app/node_modules/pkg/types/feature/tool.d.ts", ""),
        ]);
        let resolved = Resolver::new(&fs, ResolutionOptions::default())
            .resolve("pkg/feature/tool", "/app/src/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            resolved.resolved_file_name,
            "/app/node_modules/pkg/types/feature/tool.d.ts"
        );
        assert_eq!(
            resolved.package_json.as_deref(),
            Some("/app/node_modules/pkg/package.json")
        );
    }

    #[test]
    fn nested_package_types_take_priority_over_root_types_versions() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"typesVersions":{">=7":{"sub":["./root.d.ts"]}}}"#,
            ),
            ("/app/node_modules/pkg/root.d.ts", ""),
            (
                "/app/node_modules/pkg/sub/package.json",
                r#"{"types":"./nested.d.ts"}"#,
            ),
            ("/app/node_modules/pkg/sub/nested.d.ts", ""),
            (
                "/app/node_modules/protected/package.json",
                r#"{"exports":{"./sub":"./public.d.ts"}}"#,
            ),
            ("/app/node_modules/protected/public.d.ts", ""),
            (
                "/app/node_modules/protected/sub/package.json",
                r#"{"types":"./private.d.ts"}"#,
            ),
            ("/app/node_modules/protected/sub/private.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                ..ResolutionOptions::default()
            },
        );

        assert_eq!(
            resolver
                .resolve("pkg/sub", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/sub/nested.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("protected/sub", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/protected/public.d.ts"
        );
    }

    #[test]
    fn missing_types_versions_targets_fall_back_to_direct_package_files() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"typesVersions":{">=7":{"feature/*":["./missing/*"]}}}"#,
            ),
            ("/app/node_modules/pkg/feature/tool.d.ts", ""),
        ]);

        assert_eq!(
            Resolver::new(&fs, ResolutionOptions::default())
                .resolve("pkg/feature/tool", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/feature/tool.d.ts"
        );
    }

    #[test]
    fn types_versions_prefer_exact_keys_then_the_longest_wildcard_prefix() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"typesVersions":{">=7":{"feature/*-suffix":["./broad/*"],"feature/deep/*":["./deep/*"],"feature/deep/exact-suffix":["./exact.d.ts"]}}}"#,
            ),
            ("/app/node_modules/pkg/broad/deep/item.d.ts", ""),
            ("/app/node_modules/pkg/deep/item-suffix.d.ts", ""),
            ("/app/node_modules/pkg/exact.d.ts", ""),
        ]);
        let resolver = Resolver::new(&fs, ResolutionOptions::default());

        assert_eq!(
            resolver
                .resolve("pkg/feature/deep/item-suffix", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/deep/item-suffix.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("pkg/feature/deep/exact-suffix", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/exact.d.ts"
        );
    }

    #[test]
    fn resolves_package_types_versions_root_entry() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"types":"index","typesVersions":{">=7":{"*":["types/*"]}}}"#,
            ),
            ("/app/node_modules/pkg/index.d.ts", ""),
            ("/app/node_modules/pkg/types/index.d.ts", ""),
        ]);
        let resolver = Resolver::new(&fs, ResolutionOptions::default());
        let resolution = resolver
            .resolve("pkg", "/app/src/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            resolution.resolved_file_name,
            "/app/node_modules/pkg/types/index.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("../", "/app/node_modules/pkg/types/index.d.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/types/index.d.ts"
        );
    }

    #[test]
    fn node16_resolves_package_imports_and_patterns() {
        let fs = fs(&[
            (
                "/repo/package.json",
                r##"{"imports":{"#core":{"types":"./types/core.d.ts"},"#features/*":"./types/features/*.d.ts"}}"##,
            ),
            ("/repo/types/core.d.ts", ""),
            ("/repo/types/features/tool.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Node16,
                ..ResolutionOptions::default()
            },
        );
        assert_eq!(
            resolver
                .resolve("#core", "/repo/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/types/core.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("#features/tool", "/repo/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/types/features/tool.d.ts"
        );
    }

    #[test]
    fn package_imports_support_external_packages_and_local_provenance() {
        let fs = fs(&[
            (
                "/repo/package.json",
                r##"{"imports":{"#local":"./src/local.d.ts","#dep":"dependency/entry"}}"##,
            ),
            ("/repo/src/local.d.ts", ""),
            ("/repo/node_modules/dependency/entry.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );

        let local = resolver
            .resolve("#local", "/repo/main.ts")
            .resolved
            .unwrap();
        assert_eq!(local.resolved_file_name, "/repo/src/local.d.ts");
        assert!(!local.is_external_library_import);

        let dependency = resolver.resolve("#dep", "/repo/main.ts").resolved.unwrap();
        assert_eq!(
            dependency.resolved_file_name,
            "/repo/node_modules/dependency/entry.d.ts"
        );
        assert!(dependency.is_external_library_import);
    }

    #[test]
    fn package_imports_can_resolve_the_current_package_through_self_exports() {
        let filesystem = fs(&[
            (
                "/repo/package.json",
                r##"{"name":"package","type":"module","exports":"./index.cjs","imports":{"#type":"package"}}"##,
            ),
            ("/repo/index.cts", "export const value = 1;"),
        ]);
        let resolver = Resolver::new(
            &filesystem,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );

        let target = resolver
            .resolve_with_mode("#type", "/repo/index.ts", ModuleFormat::Esm)
            .resolved
            .unwrap();
        assert_eq!(target.resolved_file_name, "/repo/index.cts");
        assert_eq!(target.package_json.as_deref(), Some("/repo/package.json"));
        assert!(!target.is_external_library_import);
    }

    #[test]
    fn package_imports_apply_paths_to_bare_package_targets() {
        let filesystem = fs(&[
            (
                "/repo/package.json",
                r##"{"imports":{"#dependency":"workspace-alias"}}"##,
            ),
            ("/repo/src/dependency.ts", "export const value = 1;"),
        ]);
        let resolver = Resolver::new(
            &filesystem,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                base_url: Some("/repo".into()),
                paths: BTreeMap::from([(
                    "workspace-alias".into(),
                    vec!["./src/dependency.ts".into()],
                )]),
                ..ResolutionOptions::default()
            },
        );

        let dependency = resolver
            .resolve("#dependency", "/repo/main.ts")
            .resolved
            .unwrap();
        assert_eq!(dependency.resolved_file_name, "/repo/src/dependency.ts");
        assert!(!dependency.is_external_library_import);
    }

    #[test]
    fn cyclic_package_import_maps_fail_without_recursive_resolution() {
        let filesystem = fs(&[(
            "/repo/package.json",
            r##"{"name":"package","exports":"package","imports":{"#self":"package","#first":"#second","#second":"#first"}}"##,
        )]);
        let resolver = Resolver::new(
            &filesystem,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );

        assert!(
            resolver
                .resolve("#self", "/repo/index.ts")
                .resolved
                .is_none()
        );
        assert!(
            resolver
                .resolve("#first", "/repo/index.ts")
                .resolved
                .is_none()
        );
        assert!(
            resolver
                .resolve("#second", "/repo/index.ts")
                .resolved
                .is_none()
        );
    }

    #[test]
    fn linked_nodenext_packages_resolve_declarations_and_local_subpath_imports() {
        let filesystem = fs(&[
            (
                "/packages/b/package.json",
                r#"{"name":"package-b","type":"module","exports":{".":"./index.js"}}"#,
            ),
            ("/packages/b/index.js", "export {};"),
            ("/packages/b/index.d.ts", "export interface B { b: 'b' }"),
            (
                "/packages/a/package.json",
                r##"{"name":"package-a","type":"module","imports":{"#re_export":"./src/re_export.ts"},"exports":{".":"./dist/index.js"}}"##,
            ),
            (
                "/packages/a/src/re_export.ts",
                "import type { B } from 'package-b';",
            ),
        ]);
        filesystem.add_directory_link("/packages/b", "/packages/a/node_modules/package-b");
        let resolver = Resolver::new(
            &filesystem,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );

        let package = resolver
            .resolve_with_mode(
                "package-b",
                "/packages/a/src/re_export.ts",
                ModuleFormat::Esm,
            )
            .resolved
            .unwrap();
        assert_eq!(package.resolved_file_name, "/packages/b/index.d.ts");
        assert!(package.is_external_library_import);
        assert_eq!(
            package.package_json.as_deref(),
            Some("/packages/a/node_modules/package-b/package.json")
        );

        let subpath = resolver
            .resolve_with_mode("#re_export", "/packages/a/src/index.ts", ModuleFormat::Esm)
            .resolved
            .unwrap();
        assert_eq!(subpath.resolved_file_name, "/packages/a/src/re_export.ts");
        assert!(!subpath.is_external_library_import);
    }

    #[test]
    fn package_imports_use_only_the_nearest_package_scope() {
        let fs = fs(&[
            (
                "/repo/package.json",
                r##"{"imports":{"#shared":"./shared.d.ts"}}"##,
            ),
            ("/repo/shared.d.ts", ""),
            ("/repo/nested/package.json", r#"{"name":"nested"}"#),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                ..ResolutionOptions::default()
            },
        );

        assert!(
            resolver
                .resolve("#shared", "/repo/nested/main.ts")
                .resolved
                .is_none()
        );
    }

    #[test]
    fn nodenext_accepts_rooted_import_patterns_but_node16_rejects_them() {
        let fs = fs(&[
            ("/repo/package.json", r##"{"imports":{"#/*":"./src/*"}}"##),
            ("/repo/src/feature.ts", ""),
        ]);

        let nodenext = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );
        assert_eq!(
            nodenext
                .resolve("#/feature.js", "/repo/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/src/feature.ts"
        );

        let node16 = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Node16,
                ..ResolutionOptions::default()
            },
        );
        assert!(
            node16
                .resolve("#/feature.js", "/repo/main.ts")
                .resolved
                .is_none()
        );
    }

    #[test]
    fn wildcard_package_imports_record_typescript_extensions_from_captures() {
        let fs = fs(&[
            (
                "/repo/package.json",
                r##"{"type":"module","imports":{"#/*.omg":"./src/*","#generated/*":"./src/*.ts"}}"##,
            ),
            ("/repo/src/foo.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );

        let captured = resolver
            .resolve("#/foo.ts.omg", "/repo/src/index.ts")
            .resolved
            .unwrap();
        assert_eq!(captured.resolved_file_name, "/repo/src/foo.ts");
        assert!(captured.resolved_using_ts_extension);

        let generated = resolver
            .resolve("#generated/foo", "/repo/src/index.ts")
            .resolved
            .unwrap();
        assert_eq!(generated.resolved_file_name, "/repo/src/foo.ts");
        assert!(!generated.resolved_using_ts_extension);
    }

    #[test]
    fn disabled_package_imports_do_not_resolve_internal_specifiers() {
        let fs = fs(&[
            (
                "/repo/package.json",
                r##"{"imports":{"#core":"./types/core.d.ts"}}"##,
            ),
            ("/repo/types/core.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                resolve_package_json_imports: false,
                ..ResolutionOptions::default()
            },
        );

        assert!(
            resolver
                .resolve("#core", "/repo/src/main.ts")
                .resolved
                .is_none()
        );
    }

    #[test]
    fn nodenext_resolves_package_self_name_exports() {
        let fs = fs(&[
            (
                "/repo/package.json",
                r#"{"name":"workspace-pkg","exports":{".":{"types":"./types/index.d.ts"},"./feature":"./types/feature.d.ts"}}"#,
            ),
            ("/repo/types/index.d.ts", ""),
            ("/repo/types/feature.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );
        assert_eq!(
            resolver
                .resolve("workspace-pkg/feature", "/repo/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/types/feature.d.ts"
        );
    }

    #[test]
    fn bundler_falls_back_to_at_types_and_custom_type_roots() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"main":"index.js"}"#,
            ),
            ("/app/node_modules/pkg/index.js", ""),
            ("/app/node_modules/@types/pkg/index.d.ts", ""),
            ("/custom/types/ambient/index.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                allow_javascript: false,
                type_roots: Some(vec!["/custom/types".into()]),
                ..ResolutionOptions::default()
            },
        );
        assert_eq!(
            resolver
                .resolve("pkg", "/app/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/@types/pkg/index.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("ambient", "/app/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/custom/types/ambient/index.d.ts"
        );
    }

    #[test]
    fn declaration_packages_take_priority_over_closer_javascript_packages() {
        let fs = fs(&[
            ("/repo/app/node_modules/pkg/index.js", ""),
            ("/repo/node_modules/@types/pkg/index.d.ts", ""),
        ]);
        let resolved = Resolver::new(&fs, ResolutionOptions::default())
            .resolve("pkg", "/repo/app/src/main.ts")
            .resolved
            .unwrap();

        assert_eq!(
            resolved.resolved_file_name,
            "/repo/node_modules/@types/pkg/index.d.ts"
        );
    }

    #[test]
    fn type_references_follow_package_exports_and_bundler_import_conditions() {
        let fs = fs(&[
            (
                "/node_modules/pkg/package.json",
                r#"{"name":"pkg","exports":{".":{"import":{"types":"./esm.d.mts"},"default":{"types":"./commonjs.d.ts"}}}}"#,
            ),
            ("/node_modules/pkg/esm.d.mts", ""),
            ("/node_modules/pkg/commonjs.d.ts", ""),
        ]);
        let resolved = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                types: Some(vec!["pkg".into()]),
                ..ResolutionOptions::default()
            },
        )
        .resolve_type_reference("pkg", "/__inferred type names__.ts")
        .resolved
        .unwrap();

        assert_eq!(resolved.resolved_file_name, "/node_modules/pkg/esm.d.mts");
    }

    #[test]
    fn scoped_type_references_use_scoped_names_under_custom_type_roots() {
        let fs = fs(&[("/custom/@scope/pkg/index.d.ts", "")]);
        let resolved = Resolver::new(
            &fs,
            ResolutionOptions {
                type_roots: Some(vec!["/custom".into()]),
                ..ResolutionOptions::default()
            },
        )
        .resolve_type_reference("@scope/pkg", "/app/main.ts")
        .resolved
        .unwrap();

        assert_eq!(resolved.resolved_file_name, "/custom/@scope/pkg/index.d.ts");
    }

    #[test]
    fn javascript_mode_does_not_load_explicit_mjs_or_cjs_when_disabled() {
        let fs = fs(&[("/src/value.mjs", ""), ("/src/other.cjs", "")]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                allow_javascript: false,
                ..ResolutionOptions::default()
            },
        );

        assert!(
            resolver
                .resolve("./value.mjs", "/src/main.ts")
                .resolved
                .is_none()
        );
        assert!(
            resolver
                .resolve("./other.cjs", "/src/main.ts")
                .resolved
                .is_none()
        );
    }

    #[test]
    fn module_suffixes_select_matching_files_in_configured_order() {
        let fs = fs(&[
            ("/app/feature.ts", ""),
            ("/app/feature.native.ts", ""),
            ("/app/feature.ios.ts", ""),
            ("/app/ordinary.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                module_suffixes: vec![".android".into(), ".native".into(), String::new()],
                ..ResolutionOptions::default()
            },
        );

        assert_eq!(
            resolver
                .resolve("./feature.js", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/feature.native.ts"
        );
        assert_eq!(
            resolver
                .resolve("./ordinary", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/ordinary.ts"
        );

        let required_suffix = Resolver::new(
            &fs,
            ResolutionOptions {
                module_suffixes: vec![".android".into()],
                ..ResolutionOptions::default()
            },
        );
        assert!(
            required_suffix
                .resolve("./ordinary", "/app/main.ts")
                .resolved
                .is_none()
        );
    }

    #[test]
    fn module_suffixes_apply_to_package_declarations_and_export_targets() {
        let fs = fs(&[
            ("/app/node_modules/legacy/index.d.ts", ""),
            ("/app/node_modules/legacy/index.ios.d.ts", ""),
            (
                "/app/node_modules/modern/package.json",
                r#"{"exports":{".":"./entry.js"}}"#,
            ),
            ("/app/node_modules/modern/entry.d.ts", ""),
            ("/app/node_modules/modern/entry.ios.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                module_suffixes: vec![".ios".into()],
                ..ResolutionOptions::default()
            },
        );

        assert_eq!(
            resolver
                .resolve("legacy", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/legacy/index.ios.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("modern", "/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/modern/entry.ios.d.ts"
        );
    }

    #[test]
    fn discovers_automatic_types_and_caches_resolution_results() {
        let fs = fs(&[
            ("/repo/node_modules/@types/node/index.d.ts", ""),
            ("/repo/node_modules/@types/jest/index.d.ts", ""),
            (
                "/repo/node_modules/@types/obsolete/package.json",
                r#"{"typings":null}"#,
            ),
        ]);
        let options = ResolutionOptions::default();
        assert_eq!(
            automatic_type_directive_names(&fs, &options, "/repo/src"),
            ["jest", "node"]
        );
        let selected = ResolutionOptions {
            types: Some(vec!["custom".into(), "*".into(), "node".into()]),
            ..ResolutionOptions::default()
        };
        assert_eq!(
            automatic_type_directive_names(&fs, &selected, "/repo/src"),
            ["custom", "jest", "node"]
        );
        let resolver = Resolver::new(&fs, options);
        assert!(
            resolver
                .resolve("./later", "/repo/src/main.ts")
                .resolved
                .is_none()
        );
        fs.write_file("/repo/src/later.ts", "").unwrap();
        assert!(
            resolver
                .resolve("./later", "/repo/src/main.ts")
                .resolved
                .is_none()
        );
        resolver.clear_cache();
        assert_eq!(
            resolver
                .resolve("./later", "/repo/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/src/later.ts"
        );
    }
}
