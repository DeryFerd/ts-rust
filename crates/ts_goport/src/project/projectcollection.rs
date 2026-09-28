//! Go `internal/project/projectcollection.go`.
//!
//! PORT: one thread (project/dirty/interfaces.rs). Go `*Project` is
//! `Rc<RefCell<Project>>` (nil is `None`); Go `*ConfigFileRegistry` is
//! `Rc<ConfigFileRegistry>`. Go `collections.Set` is `FxHashSet`. Go
//! `map[K]struct{}` is `FxHashSet<K>`. A Go map that the builder shares
//! with the collection is copied here (the collection never writes it).

use crate::project::prelude::*;

use crate::frontend::{core_bfs, core_ls_ext};
use std::cell::OnceCell;

// Go: project/projectcollection.go:15 ProjectCollection
pub struct ProjectCollection {
    pub to_path: Rc<dyn Fn(&str) -> tspath::Path>,
    // PORT: nil in the collection that NewSnapshot makes.
    pub config_file_registry: Option<Rc<ConfigFileRegistry>>,
    // fileDefaultProjects is a map of file paths to the config file path (the key
    // into `configuredProjects`) of the default project for that file. If the file
    // belongs to the inferred project, the value is `inferredProjectName`. This map
    // contains quick lookups for only the associations discovered during the latest
    // snapshot update.
    pub file_default_projects: FxHashMap<tspath::Path, tspath::Path>,
    // configuredProjects is the set of loaded projects associated with a tsconfig
    // file, keyed by the config file path.
    pub configured_projects: FxHashMap<tspath::Path, Rc<RefCell<Project>>>,
    // openFiles is the set of open file paths associated with the snapshot that owns
    // this project collection.
    pub open_files: FxHashSet<tspath::Path>,
    // inferredProject is a fallback project that is used when no configured
    // project can be found for an open file.
    pub inferred_project: Option<Rc<RefCell<Project>>>,
    // apiState tracks the projects and files that API clients have explicitly
    // opened so they are kept loaded across snapshots.
    pub api_state: APIState,

    // PORT: Go `openConfiguredProjectsOnce sync.Once` and
    // `openConfiguredProjects *collections.Set[tspath.Path]` are one `OnceCell`.
    pub open_configured_projects: OnceCell<Rc<FxHashSet<tspath::Path>>>,
}

// Go: project/projectcollection.go:44 APIState
// APIState tracks the projects and files that API clients have explicitly opened.
// Opens and closes are ref-counted so multiple API clients don't clobber each
// other, and it is carried across snapshots so API-opened resources stay loaded.
// PORT: Go maps iterate in random order; `IndexMap` keeps insertion order.
// Go `clone` (projectcollection.go:55) and `equals` (projectcollection.go:62)
// are the derived `Clone` and `PartialEq`; `IndexMap` equality ignores order,
// like `maps.Equal`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct APIState {
    // openProjects is the ref-counted set of projects to keep open for API
    // clients, keyed by config file path. The value is the number of outstanding
    // API opens.
    pub open_projects: IndexMap<tspath::Path, i32>,
    // openFiles is the ref-counted set of files to keep open for API clients,
    // keyed by file path. Files with no configured project are loaded into the
    // inferred project.
    pub open_files: IndexMap<tspath::Path, APIOpenedFile>,
}

// Go: project/projectcollection.go:67 apiOpenedFile
// apiOpenedFile tracks a file kept open by API clients along with its ref count.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct APIOpenedFile {
    pub file_name: String,
    pub ref_count: i32,
}

/// Go `tspath.Path(inferredProjectName)`.
fn inferred_project_path() -> tspath::Path {
    tspath::Path(INFERRED_PROJECT_NAME.to_string())
}

impl ProjectCollection {
    // Go: project/projectcollection.go:40 ConfigFileRegistry
    pub fn config_file_registry(&self) -> Option<Rc<ConfigFileRegistry>> {
        self.config_file_registry.clone()
    }

    // Go: project/projectcollection.go:42 ConfiguredProject
    pub fn configured_project(&self, path: &tspath::Path) -> Option<Rc<RefCell<Project>>> {
        self.configured_projects.get(path).cloned()
    }

    // Go: project/projectcollection.go:46 GetProjectByPath
    pub fn get_project_by_path(&self, project_path: &tspath::Path) -> Option<Rc<RefCell<Project>>> {
        if let Some(project) = self.configured_projects.get(project_path) {
            return Some(project.clone());
        }

        if project_path.as_str() == INFERRED_PROJECT_NAME {
            return self.inferred_project.clone();
        }

        None
    }

    // Go: project/projectcollection.go:59 ConfiguredProjects
    // ConfiguredProjects returns all configured projects in a stable order.
    pub fn configured_projects(&self) -> Vec<Rc<RefCell<Project>>> {
        let mut projects = Vec::with_capacity(self.configured_projects.len());
        self.fill_configured_projects(&mut projects);
        projects
    }

    // Go: project/projectcollection.go:65 fillConfiguredProjects
    pub fn fill_configured_projects(&self, projects: &mut Vec<Rc<RefCell<Project>>>) {
        for p in self.configured_projects.values() {
            projects.push(p.clone());
        }
        gostd::slices::sort_func(projects, |a, b| {
            // Go: cmp.Compare(a.Name(), b.Name())
            a.borrow().name().cmp(&b.borrow().name()) as i32
        });
    }

    // Go: project/projectcollection.go:76 ProjectsByPath
    // ProjectsByPath returns an ordered map of configured projects keyed by their config file path,
    // plus the inferred project, if it exists, with the key `inferredProjectName`.
    // PORT: Go `*collections.OrderedMap` is an owned `IndexMap`.
    pub fn projects_by_path(&self) -> IndexMap<tspath::Path, Rc<RefCell<Project>>> {
        let mut projects: IndexMap<tspath::Path, Rc<RefCell<Project>>> = IndexMap::with_capacity(
            self.configured_projects.len()
                + if self.inferred_project.is_some() {
                    1
                } else {
                    0
                },
        );
        for project in self.configured_projects() {
            let config_file_path = project.borrow().config_file_path.clone();
            projects.insert(config_file_path, project);
        }
        if let Some(inferred_project) = &self.inferred_project {
            projects.insert(inferred_project_path(), inferred_project.clone());
        }
        projects
    }

    // Go: project/projectcollection.go:90 Projects
    // Projects returns all projects, including the inferred project if it exists, in a stable order.
    pub fn projects(&self) -> Vec<Rc<RefCell<Project>>> {
        let Some(inferred_project) = &self.inferred_project else {
            return self.configured_projects();
        };
        let mut projects = Vec::with_capacity(self.configured_projects.len() + 1);
        self.fill_configured_projects(&mut projects);
        projects.push(inferred_project.clone());
        projects
    }

    // Go: project/projectcollection.go:100 InferredProject
    pub fn inferred_project(&self) -> Option<Rc<RefCell<Project>>> {
        self.inferred_project.clone()
    }

    // Go: project/projectcollection.go:104 GetProjectsContainingFile
    // PORT: Go `ls.Project` values are `Rc<dyn ls::Project>`; the project
    // handle `Rc<RefCell<Project>>` coerces (project.rs implements
    // `ls::Project` for `RefCell<Project>`). A Go nil slice is empty.
    pub fn get_projects_containing_file(&self, path: &tspath::Path) -> Vec<Rc<dyn ls::Project>> {
        let mut projects: Vec<Rc<dyn ls::Project>> = Vec::new();
        for project in self.configured_projects() {
            if project.borrow().contains_file(path) {
                projects.push(project as Rc<dyn ls::Project>);
            }
        }
        if let Some(inferred_project) = &self.inferred_project {
            if inferred_project.borrow().contains_file(path) {
                projects.push(inferred_project.clone() as Rc<dyn ls::Project>);
            }
        }
        projects
    }

    // Go: project/projectcollection.go:118 GetOpenConfiguredProjects
    // GetOpenConfiguredProjects returns configured projects containing at least one open file.
    pub fn get_open_configured_projects(&self) -> Rc<FxHashSet<tspath::Path>> {
        self.open_configured_projects
            .get_or_init(|| {
                let mut open_projects: FxHashSet<tspath::Path> =
                    FxHashSet::with_capacity_and_hasher(
                        self.configured_projects.len(),
                        Default::default(),
                    );
                // PORT: Go map order is random; FxHashSet order here. The
                // result is a set, so the order does not show.
                for path in &self.open_files {
                    if let Some(project_path) = self.file_default_projects.get(path) {
                        if project_path.as_str() != INFERRED_PROJECT_NAME
                            && self.configured_projects.contains_key(project_path)
                        {
                            open_projects.insert(project_path.clone());
                            continue;
                        }
                    }

                    for project in self.configured_projects.values() {
                        let project = project.borrow();
                        if project.contains_file(path) {
                            open_projects.insert(project.config_file_path.clone());
                        }
                    }
                }
                Rc::new(open_projects)
            })
            .clone()
    }

    // Go: project/projectcollection.go:149 GetDefaultProject
    // !!! result could be cached
    pub fn get_default_project(&self, path: &tspath::Path) -> Option<Rc<RefCell<Project>>> {
        if let Some(result) = self.file_default_projects.get(path) {
            if result.as_str() == INFERRED_PROJECT_NAME {
                return self.inferred_project.clone();
            }
            return self.configured_projects.get(result).cloned();
        }

        let mut containing_projects: Vec<Rc<RefCell<Project>>> = Vec::new();
        let mut first_configured_project: Option<Rc<RefCell<Project>>> = None;
        let mut first_non_source_of_project_reference_redirect: Option<Rc<RefCell<Project>>> = None;
        let mut multiple_direct_inclusions = false;
        for p in self.configured_projects() {
            if p.borrow().contains_file(path) {
                containing_projects.push(p.clone());
                if !multiple_direct_inclusions && !p.borrow().is_source_from_project_reference(path)
                {
                    if first_non_source_of_project_reference_redirect.is_none() {
                        first_non_source_of_project_reference_redirect = Some(p.clone());
                    } else {
                        multiple_direct_inclusions = true;
                    }
                }
                if first_configured_project.is_none() {
                    first_configured_project = Some(p.clone());
                }
            }
        }
        if containing_projects.len() == 1 {
            return Some(containing_projects[0].clone());
        }
        if containing_projects.is_empty() {
            if let Some(inferred_project) = &self.inferred_project {
                if inferred_project.borrow().contains_file(path) {
                    return Some(inferred_project.clone());
                }
            }
            return None;
        }
        if !multiple_direct_inclusions {
            if first_non_source_of_project_reference_redirect.is_some() {
                // Multiple projects include the file, but only one is a direct inclusion.
                return first_non_source_of_project_reference_redirect;
            }
            // Multiple projects include the file, and none are direct inclusions.
            return first_configured_project;
        }
        // Multiple projects include the file directly.
        if let Some(default_project) = self.find_default_configured_project(path) {
            return Some(default_project);
        }
        first_configured_project
    }

    // Go: project/projectcollection.go:202 findDefaultConfiguredProject
    pub fn find_default_configured_project(
        &self,
        path: &tspath::Path,
    ) -> Option<Rc<RefCell<Project>>> {
        let config_file_name = self
            .config_file_registry
            .as_ref()
            .expect("invalid memory address or nil pointer dereference")
            .get_config_file_name(path);
        if !config_file_name.is_empty() {
            return self.find_default_configured_project_worker(
                path,
                &config_file_name,
                None,
                None,
            );
        }
        None
    }

    // Go: project/projectcollection.go:209 findDefaultConfiguredProjectWorker
    // PORT: Go `*collections.SyncSet[*Project]` is a `RefCell<FxHashSet>` of
    // project addresses (`Rc::as_ptr as usize`, Go pointer keys).
    pub fn find_default_configured_project_worker(
        &self,
        path: &tspath::Path,
        config_file_name: &str,
        visited: Option<&RefCell<FxHashSet<usize>>>,
        fallback: Option<Rc<RefCell<Project>>>,
    ) -> Option<Rc<RefCell<Project>>> {
        let mut fallback = fallback;
        let config_file_path = (self.to_path)(config_file_name);
        let project = self.configured_projects.get(&config_file_path).cloned()?;
        let new_visited: RefCell<FxHashSet<usize>>;
        let visited = match visited {
            Some(visited) => visited,
            None => {
                new_visited = RefCell::new(FxHashSet::default());
                &new_visited
            }
        };

        // Look in the config's project and its references recursively.
        let search = core_bfs::breadth_first_search_parallel_ex(
            project,
            &mut |project: &Rc<RefCell<Project>>| -> Vec<Rc<RefCell<Project>>> {
                let project = project.borrow();
                let Some(command_line) = &project.command_line else {
                    return Vec::new();
                };
                // A referenced project may not be loaded if `disableReferencedProjectLoad` is true.
                core_ls_ext::map_non_nil(
                    command_line.resolved_project_reference_paths(),
                    |config_file_name: &String| {
                        self.configured_projects
                            .get(&(self.to_path)(config_file_name))
                            .cloned()
                    },
                )
            },
            &mut |project: &Rc<RefCell<Project>>| -> (bool, bool) {
                let project = project.borrow();
                if project.contains_file(path) {
                    return (true, !project.is_source_from_project_reference(path));
                }
                (false, false)
            },
            core_bfs::BreadthFirstSearchOptions {
                visited: Some(visited),
                preprocess_level: None,
            },
            // Go: core.Identity (the key is the Go pointer).
            &mut |project: &Rc<RefCell<Project>>| Rc::as_ptr(project) as usize,
        );

        if search.stopped {
            // If we found a project that directly contains the file, return it.
            return Some(search.path[0].clone());
        }
        if !search.path.is_empty() && fallback.is_none() {
            // If we found a project that contains the file, but it is a source from
            // a project reference, record it as a fallback.
            fallback = Some(search.path[0].clone());
        }

        // Look for tsconfig.json files higher up the directory tree and do the same. This handles
        // the common case where a higher-level "solution" tsconfig.json contains all projects in a
        // workspace.
        let config_file_registry = self
            .config_file_registry
            .as_ref()
            .expect("invalid memory address or nil pointer dereference");
        if let Some(config) = config_file_registry.get_config(path) {
            if config
                .compiler_options()
                .disable_solution_searching
                .is_true()
            {
                return fallback;
            }
        }
        let ancestor_config_name =
            config_file_registry.get_ancestor_config_file_name(path, config_file_name);
        if !ancestor_config_name.is_empty() {
            return self.find_default_configured_project_worker(
                path,
                &ancestor_config_name,
                Some(visited),
                fallback,
            );
        }
        fallback
    }

    // Go: project/projectcollection.go:298 clone
    // clone creates a shallow copy of the project collection.
    // PORT: Go shares the maps; the port copies them (neither side writes
    // them after the copy). `openConfiguredProjectsOnce` starts fresh, as in
    // Go. Call it as `ProjectCollection::clone(&c)`: `Rc::clone` wins on an
    // `Rc<ProjectCollection>` receiver.
    pub fn clone(&self) -> ProjectCollection {
        ProjectCollection {
            to_path: self.to_path.clone(),
            config_file_registry: self.config_file_registry.clone(),
            configured_projects: self.configured_projects.clone(),
            open_files: self.open_files.clone(),
            inferred_project: self.inferred_project.clone(),
            file_default_projects: self.file_default_projects.clone(),
            api_state: self.api_state.clone(),
            open_configured_projects: OnceCell::new(),
        }
    }
}

// Go: project/projectcollection.go:140 openFilePaths
// PORT: Go `map[tspath.Path]*Overlay` is the `IndexMap` of overlayfs.rs.
pub fn open_file_paths(overlays: &IndexMap<tspath::Path, Rc<Overlay>>) -> FxHashSet<tspath::Path> {
    let mut open_files: FxHashSet<tspath::Path> =
        FxHashSet::with_capacity_and_hasher(overlays.len(), Default::default());
    for path in overlays.keys() {
        open_files.insert(path.clone());
    }
    open_files
}

// Go: project/projectcollection.go:284 findDefaultConfiguredProjectFromProgramInclusion
// findDefaultConfiguredProjectFromProgramInclusion finds the default configured project for a file
// based on the file's inclusion in existing projects. The projects should be sorted, as ties will
// be broken by slice order. `getProject` should return a project with an up-to-date program.
// Along with the resulting project path, a boolean is returned indicating whether there were multiple
// direct inclusions of the file in different projects, indicating that the caller may want to perform
// additional logic to determine the best project.
// PORT: `get_project` returns `None` for Go nil; Go then dereferences it.
pub fn find_default_configured_project_from_program_inclusion(
    _file_name: &str,
    path: &tspath::Path,
    project_paths: &[tspath::Path],
    get_project: &mut dyn FnMut(&tspath::Path) -> Option<Rc<RefCell<Project>>>,
) -> (tspath::Path, bool) {
    let mut containing_projects: Vec<tspath::Path> = Vec::new();
    let mut first_configured_project = tspath::Path::default();
    let mut first_non_source_of_project_reference_redirect = tspath::Path::default();
    let mut multiple_direct_inclusions = false;

    for project_path in project_paths {
        let p =
            get_project(project_path).expect("invalid memory address or nil pointer dereference");
        let p = p.borrow();
        if p.contains_file(path) {
            containing_projects.push(project_path.clone());
            if !multiple_direct_inclusions && !p.is_source_from_project_reference(path) {
                if first_non_source_of_project_reference_redirect.is_empty() {
                    first_non_source_of_project_reference_redirect = project_path.clone();
                } else {
                    multiple_direct_inclusions = true;
                }
            }
            if first_configured_project.is_empty() {
                first_configured_project = project_path.clone();
            }
        }
    }

    if containing_projects.len() == 1 {
        return (containing_projects[0].clone(), false);
    }
    if !multiple_direct_inclusions {
        if !first_non_source_of_project_reference_redirect.is_empty() {
            // Multiple projects include the file, but only one is a direct inclusion.
            return (first_non_source_of_project_reference_redirect, false);
        }
        // Multiple projects include the file, and none are direct inclusions.
        return (first_configured_project, false);
    }
    // Multiple projects include the file directly.
    (first_configured_project, true)
}
