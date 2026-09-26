//! Go `internal/project/autoimport.go`.
//!
//! PORT: one thread (project/dirty/interfaces.rs). Go
//! `collections.SyncMap` is a `RefCell<FxHashMap>`; `filesMu` is dropped.
//! Go `FileHandle` is `Option<Rc<dyn FileHandle>>` (nil is `None`). In this
//! package's prelude, `autoimport` is Go package `ls/autoimport`.

use crate::project::prelude::*;

use crate::frontend::module;
use crate::frontend::parser;
use crate::frontend::vfs::Fs as _;

// Go: project/autoimport.go:15 autoImportBuilderFS
// PORT: the untracked map stores Go nil handles too (Go `LoadOrStore` of a
// nil `fh` caches the miss), so its values are `Option`.
pub struct AutoImportBuilderFS {
    pub snapshot_fs_builder: Rc<SnapshotFSBuilder>,
    pub untracked_files: RefCell<FxHashMap<tspath::Path, Option<Rc<dyn FileHandle>>>>,
}

// Go: project/autoimport.go:20 `var _ FileSource = (*autoImportBuilderFS)(nil)`
impl FileSource for AutoImportBuilderFS {
    // Go: project/autoimport.go:23 FS
    // FS implements FileSource.
    fn fs(&self) -> Rc<dyn vfs::Fs> {
        self.snapshot_fs_builder.fs.clone()
    }

    // Go: project/autoimport.go:28 GetFile
    // GetFile implements FileSource.
    fn get_file(&self, file_name: &str) -> Option<Rc<dyn FileHandle>> {
        let path = (self.snapshot_fs_builder.to_path)(file_name);
        self.get_file_by_path(file_name, &path)
    }

    // Go: project/autoimport.go:34 GetFileByPath
    // GetFileByPath implements FileSource.
    fn get_file_by_path(&self, file_name: &str, path: &tspath::Path) -> Option<Rc<dyn FileHandle>> {
        // We want to avoid long-term caching of files referenced only by auto-imports, so we
        // override GetFileByPath to avoid collecting more files into the snapshotFSBuilder's
        // diskFiles. (Note the reason we can't just use the finalized SnapshotFS is that changed
        // files not read during other parts of the snapshot clone will be marked as dirty, but
        // not yet refreshed from disk.)
        if let Some(overlay) = self.snapshot_fs_builder.overlays.get(path) {
            return Some(overlay.clone() as Rc<dyn FileHandle>);
        }
        if let (Some(disk_file), true) = self.snapshot_fs_builder.disk_files.load(path) {
            return self.snapshot_fs_builder.reload_entry_if_needed(&disk_file);
        }
        if let Some(fh) = self.untracked_files.borrow().get(path) {
            return fh.clone();
        }
        let mut fh: Option<Rc<dyn FileHandle>> = None;
        let (content, ok) = self.snapshot_fs_builder.fs.read_file(file_name);
        if ok {
            fh = Some(new_disk_file(file_name, content) as Rc<dyn FileHandle>);
        }
        // Go: fh, _ = a.untrackedFiles.LoadOrStore(path, fh)
        let fh = self
            .untracked_files
            .borrow_mut()
            .entry(path.clone())
            .or_insert(fh)
            .clone();
        fh
    }

    // Go: project/autoimport.go:63 FileExists
    // FileExists implements FileSource.
    fn file_exists(&self, file_name: &str, path: &tspath::Path) -> bool {
        self.snapshot_fs_builder.file_exists(file_name, path)
    }

    // Go: project/autoimport.go:58 GetAccessibleEntries
    // PORT: after FileExists because the Rust trait lists it last.
    fn get_accessible_entries(&self, path: &str) -> vfs::Entries {
        self.snapshot_fs_builder.get_accessible_entries(path)
    }
}

// Go: project/autoimport.go:67 autoImportRegistryCloneHost
// PORT: `filesMu` is dropped; `files` is written after sharing, so it is a
// `RefCell`.
pub struct AutoImportRegistryCloneHost {
    pub project_collection: Rc<ProjectCollection>,
    pub parse_cache: Rc<ParseCache>,
    pub fs: Rc<SourceFS>,
    pub current_directory: String,

    pub files: RefCell<Vec<ParseCacheKey>>,
}

// Go: project/autoimport.go:79 newAutoImportRegistryCloneHost
pub fn new_auto_import_registry_clone_host(
    project_collection: Rc<ProjectCollection>,
    parse_cache: Rc<ParseCache>,
    snapshot_fs_builder: Rc<SnapshotFSBuilder>,
    current_directory: &str,
    to_path: Rc<dyn Fn(&str) -> tspath::Path>,
) -> Rc<AutoImportRegistryCloneHost> {
    Rc::new(AutoImportRegistryCloneHost {
        project_collection,
        parse_cache,
        fs: new_source_fs(
            false,
            Rc::new(AutoImportBuilderFS {
                snapshot_fs_builder,
                untracked_files: RefCell::new(FxHashMap::default()),
            }),
            to_path,
        ),
        current_directory: current_directory.to_string(),
        files: RefCell::new(Vec::new()),
    })
}

// PORT: Go `autoimport.RegistryCloneHost` embeds `module.ResolutionHost`;
// its `FS` and `GetCurrentDirectory` are this supertrait.
impl module::ResolutionHost for AutoImportRegistryCloneHost {
    // Go: project/autoimport.go:95 FS
    // FS implements autoimport.RegistryCloneHost.
    fn fs(&self) -> &dyn vfs::Fs {
        &*self.fs
    }

    // Go: project/autoimport.go:100 GetCurrentDirectory
    // GetCurrentDirectory implements autoimport.RegistryCloneHost.
    fn get_current_directory(&self) -> &str {
        &self.current_directory
    }
}

// Go: project/autoimport.go:77 `var _ autoimport.RegistryCloneHost = (*autoImportRegistryCloneHost)(nil)`
impl autoimport::RegistryCloneHost for AutoImportRegistryCloneHost {
    // Go: project/autoimport.go:105 GetDefaultProject
    // GetDefaultProject implements autoimport.RegistryCloneHost.
    fn get_default_project(
        &self,
        path: &tspath::Path,
    ) -> (tspath::Path, Option<&'static compiler::NewProgram>) {
        let Some(project) = self.project_collection.get_default_project(path) else {
            return (tspath::Path::default(), None);
        };
        let project = project.borrow();
        // PORT: Go `project.GetProgram()` is the field read.
        (project.config_file_path.clone(), project.program)
    }

    // Go: project/autoimport.go:145 GetProgramForProject
    // GetProgramForProject implements autoimport.RegistryCloneHost.
    fn get_program_for_project(
        &self,
        project_path: &tspath::Path,
    ) -> Option<&'static compiler::NewProgram> {
        let project = self.project_collection.get_project_by_path(project_path)?;
        // PORT: Go `project.GetProgram()` is the field read.
        let program = project.borrow().program;
        program
    }

    // Go: project/autoimport.go:114 GetPackageJson
    // GetPackageJson implements autoimport.RegistryCloneHost.
    fn get_package_json(&self, file_name: &str) -> Option<Rc<packagejson::InfoCacheEntry>> {
        // !!! ref-counted shared cache
        let fh = self.fs.get_file(file_name);
        let package_directory = tspath::get_directory_path(file_name);
        let Some(fh) = fh else {
            return Some(Rc::new(packagejson::InfoCacheEntry {
                directory_exists: self.fs.directory_exists(&package_directory),
                package_directory,
                contents: None,
            }));
        };
        let fields = match packagejson::parse(fh.content().as_bytes()) {
            Ok(fields) => fields,
            Err(_) => {
                return Some(Rc::new(packagejson::InfoCacheEntry {
                    directory_exists: true,
                    package_directory: tspath::get_directory_path(file_name),
                    contents: Some(Rc::new(packagejson::PackageJson {
                        parseable: false,
                        ..Default::default()
                    })),
                }));
            }
        };
        Some(Rc::new(packagejson::InfoCacheEntry {
            directory_exists: true,
            package_directory: tspath::get_directory_path(file_name),
            contents: Some(Rc::new(packagejson::PackageJson {
                fields,
                parseable: true,
                ..Default::default()
            })),
        }))
    }

    // Go: project/autoimport.go:154 GetSourceFile
    // GetSourceFile implements autoimport.RegistryCloneHost.
    // PORT: Go `*ast.SourceFile` is the file root `Node` (`file.root`).
    fn get_source_file(&self, file_name: &str, path: &tspath::Path) -> Node {
        let Some(fh) = self.fs.get_file(file_name) else {
            return Node::NIL;
        };
        let opts = parser::SourceFileParseOptions {
            file_name: file_name.to_string(),
            path: path.clone(),
            ..Default::default()
        };
        let key = new_parse_cache_key(&opts, fh.hash(), fh.kind());
        let result = self.parse_cache.acquire(key.clone(), fh);

        // Go: a.filesMu.Lock() / Unlock() (PORT: no lock).
        self.files.borrow_mut().push(key);

        result.file.root
    }

    // Go: project/autoimport.go:174 Dispose
    // Dispose implements autoimport.RegistryCloneHost.
    fn dispose(&self) {
        // Go: a.filesMu.Lock(); defer a.filesMu.Unlock() (PORT: no lock).
        for key in self.files.borrow().iter() {
            self.parse_cache.deref(key);
        }
    }
}
