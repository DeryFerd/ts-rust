//! Go `internal/project/configfileregistry.go`.
//!
//! PORT: one thread (project/dirty/interfaces.rs). Go `*ConfigFileRegistry`
//! is `Rc<ConfigFileRegistry>` (never changed after it is shared). Go
//! `*configFileEntry` and `*configFileNames` are `Rc<RefCell<..>>`: the
//! registry builder changes them through `dirty` entries. Go
//! `map[tspath.Path]struct{}` is `FxHashSet<tspath::Path>` and a nil map is
//! the empty set (Go only reads nil maps and makes one before a write).

use crate::project::prelude::*;

// Go: project/configfileregistry.go:13 ConfigFileRegistry
#[derive(Clone, Default)]
pub struct ConfigFileRegistry {
    // configs is a map of config file paths to their entries.
    pub configs: FxHashMap<tspath::Path, Rc<RefCell<ConfigFileEntry>>>,
    // configFileNames is a map of open file paths to information
    // about their ancestor config file names. It is only used as
    // a cache during
    pub config_file_names: FxHashMap<tspath::Path, Rc<RefCell<ConfigFileNames>>>,
    // customConfigFileName is the custom config file name preference that was
    // used when building this registry's configFileNames cache.
    pub custom_config_file_name: String,
}

// Go: project/configfileregistry.go:25 configFileEntry
pub struct ConfigFileEntry {
    pub file_name: String,
    pub pending_reload: PendingReload,
    pub command_line: Option<Rc<tsoptions::ParsedCommandLine>>,
    // retainingProjects is the set of projects that have called acquireConfig
    // without releasing it. A config file entry may be acquired by a project
    // either because it is the config for that project or because it is the
    // config for a referenced project.
    pub retaining_projects: FxHashSet<tspath::Path>,
    // retainingOpenFiles is the set of open files that caused this config to
    // load during project collection building. This config file may or may not
    // end up being the config for the default project for these files, but
    // determining the default project loaded this config as a candidate, so
    // subsequent calls to `projectCollectionBuilder.findDefaultConfiguredProject`
    // will use this config as part of the search, so it must be retained.
    pub retaining_open_files: FxHashSet<tspath::Path>,
    // retainingConfigs is the set of config files that extend this one. This
    // provides a cheap reverse mapping for a project config's
    // `commandLine.ExtendedSourceFiles()` that can be used to notify the
    // extending projects when this config changes. An extended config file may
    // or may not also be used directly by a project, so it's possible that
    // when this is set, no other fields will be used.
    pub retaining_configs: FxHashSet<tspath::Path>,
    // rootFilesWatch is a watch for the root files of this config file.
    pub root_files_watch: Option<Rc<WatchedFiles<PatternsAndIgnored>>>,
}

// Go: project/configfileregistry.go:52 newConfigFileEntry
pub fn new_config_file_entry(
    has_relative_pattern_capability: bool,
    file_name: &str,
) -> Rc<RefCell<ConfigFileEntry>> {
    // Go: core.Identity
    let identity: Rc<dyn Fn(&PatternsAndIgnored) -> PatternsAndIgnored> =
        Rc::new(|p: &PatternsAndIgnored| p.clone());
    Rc::new(RefCell::new(ConfigFileEntry {
        file_name: file_name.to_string(),
        pending_reload: PendingReload::FULL,
        command_line: None,
        retaining_projects: FxHashSet::default(),
        retaining_open_files: FxHashSet::default(),
        retaining_configs: FxHashSet::default(),
        root_files_watch: Some(new_watched_files(
            &format!("root files for {file_name}"),
            lsproto::WatchKind(
                lsproto::WatchKind::CREATE.0
                    | lsproto::WatchKind::CHANGE.0
                    | lsproto::WatchKind::DELETE.0,
            ),
            has_relative_pattern_capability,
            identity,
        )),
    }))
}

// Go: project/configfileregistry.go:65 newExtendedConfigFileEntry
pub fn new_extended_config_file_entry(
    file_name: &str,
    extending_config_path: tspath::Path,
) -> Rc<RefCell<ConfigFileEntry>> {
    let mut retaining_configs = FxHashSet::default();
    retaining_configs.insert(extending_config_path);
    Rc::new(RefCell::new(ConfigFileEntry {
        file_name: file_name.to_string(),
        pending_reload: PendingReload::FULL,
        command_line: None,
        retaining_projects: FxHashSet::default(),
        retaining_open_files: FxHashSet::default(),
        retaining_configs,
        root_files_watch: None,
    }))
}

impl ConfigFileEntry {
    // Go: project/configfileregistry.go:73 configFileEntry.Clone
    // PORT: Go `Clone()` is `clone_` (dirty decision 3).
    pub fn clone_(&self) -> Rc<RefCell<ConfigFileEntry>> {
        Rc::new(RefCell::new(ConfigFileEntry {
            file_name: self.file_name.clone(),
            pending_reload: self.pending_reload,
            command_line: self.command_line.clone(),
            // !!! eagerly cloning these maps makes everything more convenient,
            // but it could be avoided if needed.
            retaining_projects: self.retaining_projects.clone(),
            retaining_open_files: self.retaining_open_files.clone(),
            retaining_configs: self.retaining_configs.clone(),
            root_files_watch: self.root_files_watch.clone(),
        }))
    }
}

// Go: project/configfileregistry.go:73 configFileEntry.Clone (dirty.Cloneable)
impl dirty::Cloneable for Rc<RefCell<ConfigFileEntry>> {
    fn clone_(&self) -> Self {
        self.borrow().clone_()
    }
}

impl ConfigFileRegistry {
    // Go: project/configfileregistry.go:87 ConfigFileRegistry.GetConfig
    pub fn get_config(&self, path: &tspath::Path) -> Option<Rc<tsoptions::ParsedCommandLine>> {
        if let Some(entry) = self.configs.get(path) {
            return entry.borrow().command_line.clone();
        }
        None
    }

    // Go: project/configfileregistry.go:130 ConfigFileRegistry.isTracked
    pub fn is_tracked(&self, path: &tspath::Path) -> bool {
        self.configs.contains_key(path)
    }

    // Go: project/configfileregistry.go:94 ConfigFileRegistry.GetConfigFileName
    pub fn get_config_file_name(&self, path: &tspath::Path) -> String {
        if let Some(entry) = self.config_file_names.get(path) {
            return entry.borrow().nearest_config_file_name.clone();
        }
        String::new()
    }

    // Go: project/configfileregistry.go:101 ConfigFileRegistry.GetAncestorConfigFileName
    pub fn get_ancestor_config_file_name(
        &self,
        path: &tspath::Path,
        higher_than_config: &str,
    ) -> String {
        if let Some(entry) = self.config_file_names.get(path) {
            return entry
                .borrow()
                .ancestors
                .get(higher_than_config)
                .cloned()
                .unwrap_or_default();
        }
        String::new()
    }

    // Go: project/configfileregistry.go:109 ConfigFileRegistry.clone
    // clone creates a shallow copy of the configFileRegistry.
    // PORT: named `clone_` like the Go `Clone` methods, so it is not taken
    // for `std::clone::Clone::clone`.
    pub fn clone_(&self) -> ConfigFileRegistry {
        ConfigFileRegistry {
            configs: self.configs.clone(),
            config_file_names: self.config_file_names.clone(),
            custom_config_file_name: self.custom_config_file_name.clone(),
        }
    }

    // Go: project/configfileregistry.go:126 ConfigFileRegistry.ForEachTestConfigEntry
    // For testing
    // PORT: Go checks for a nil receiver, so `c` is an `Option`.
    pub fn for_each_test_config_entry(
        c: Option<&ConfigFileRegistry>,
        cb: &mut dyn FnMut(&tspath::Path, &TestConfigEntry),
    ) {
        if let Some(c) = c {
            for (path, entry) in &c.configs {
                let entry = entry.borrow();
                cb(
                    path,
                    &TestConfigEntry {
                        file_name: entry.file_name.clone(),
                        retaining_projects: entry.retaining_projects.iter().cloned().collect(),
                        retaining_open_files: entry.retaining_open_files.iter().cloned().collect(),
                        retaining_configs: entry.retaining_configs.iter().cloned().collect(),
                    },
                );
            }
        }
    }

    // Go: project/configfileregistry.go:140 ConfigFileRegistry.GetTestConfigEntry
    // For testing
    // PORT: Go checks for a nil receiver, so `c` is an `Option`.
    pub fn get_test_config_entry(
        c: Option<&ConfigFileRegistry>,
        path: &tspath::Path,
    ) -> Option<TestConfigEntry> {
        if let Some(c) = c {
            if let Some(entry) = c.configs.get(path) {
                let entry = entry.borrow();
                return Some(TestConfigEntry {
                    file_name: entry.file_name.clone(),
                    retaining_projects: entry.retaining_projects.iter().cloned().collect(),
                    retaining_open_files: entry.retaining_open_files.iter().cloned().collect(),
                    retaining_configs: entry.retaining_configs.iter().cloned().collect(),
                });
            }
        }
        None
    }

    // Go: project/configfileregistry.go:160 ConfigFileRegistry.ForEachTestConfigFileNamesEntry
    // For testing
    // PORT: Go checks for a nil receiver, so `c` is an `Option`.
    pub fn for_each_test_config_file_names_entry(
        c: Option<&ConfigFileRegistry>,
        cb: &mut dyn FnMut(&tspath::Path, &TestConfigFileNamesEntry),
    ) {
        if let Some(c) = c {
            for (path, entry) in &c.config_file_names {
                let entry = entry.borrow();
                cb(
                    path,
                    &TestConfigFileNamesEntry {
                        nearest_config_file_name: entry.nearest_config_file_name.clone(),
                        ancestors: entry.ancestors.clone(),
                    },
                );
            }
        }
    }

    // Go: project/configfileregistry.go:172 ConfigFileRegistry.GetTestConfigFileNamesEntry
    // For testing
    // PORT: Go checks for a nil receiver, so `c` is an `Option`.
    pub fn get_test_config_file_names_entry(
        c: Option<&ConfigFileRegistry>,
        path: &tspath::Path,
    ) -> Option<TestConfigFileNamesEntry> {
        if let Some(c) = c {
            if let Some(entry) = c.config_file_names.get(path) {
                let entry = entry.borrow();
                return Some(TestConfigFileNamesEntry {
                    nearest_config_file_name: entry.nearest_config_file_name.clone(),
                    ancestors: entry.ancestors.clone(),
                });
            }
        }
        None
    }
}

// Go: project/configfileregistry.go:118 TestConfigEntry
// For testing
// PORT: Go `iter.Seq[tspath.Path]` over a live map is the collected keys.
#[derive(Clone, Debug, Default)]
pub struct TestConfigEntry {
    pub file_name: String,
    pub retaining_projects: Vec<tspath::Path>,
    pub retaining_open_files: Vec<tspath::Path>,
    pub retaining_configs: Vec<tspath::Path>,
}

// Go: project/configfileregistry.go:154 TestConfigFileNamesEntry
// PORT: Go shares the entry's `ancestors` map; the port copies it.
#[derive(Clone, Debug, Default)]
pub struct TestConfigFileNamesEntry {
    pub nearest_config_file_name: String,
    pub ancestors: FxHashMap<String, String>,
}

// Go: project/configfileregistry.go:184 configFileNames
#[derive(Clone, Debug, Default)]
pub struct ConfigFileNames {
    // nearestConfigFileName is the file name of the nearest ancestor config file.
    pub nearest_config_file_name: String,
    // ancestors is a map from one ancestor config file path to the next.
    // For example, if `/a`, `/a/b`, and `/a/b/c` all contain config files,
    // the fully loaded map will look like:
    //		{
    //			"/a/b/c/tsconfig.json": "/a/b/tsconfig.json",
    //			"/a/b/tsconfig.json": "/a/tsconfig.json"
    //		}
    // PORT: a nil map is the empty map.
    pub ancestors: FxHashMap<String, String>,
}

impl ConfigFileNames {
    // Go: project/configfileregistry.go:197 configFileNames.Clone
    // PORT: Go `Clone()` is `clone_` (dirty decision 3).
    pub fn clone_(&self) -> Rc<RefCell<ConfigFileNames>> {
        Rc::new(RefCell::new(ConfigFileNames {
            nearest_config_file_name: self.nearest_config_file_name.clone(),
            ancestors: self.ancestors.clone(),
        }))
    }
}

// Go: project/configfileregistry.go:197 configFileNames.Clone (dirty.Cloneable)
impl dirty::Cloneable for Rc<RefCell<ConfigFileNames>> {
    fn clone_(&self) -> Self {
        self.borrow().clone_()
    }
}
