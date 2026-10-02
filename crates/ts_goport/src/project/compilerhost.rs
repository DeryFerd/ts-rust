//! Go `internal/project/compilerhost.go`.
//!
//! PORT: Go `compilerHost` is the struct `CompilerHost`; the Go interface
//! `compiler.CompilerHost` is always written `compiler::CompilerHost`
//! (map-project.md section 4). The host is shared (`Rc<CompilerHost>` in
//! the project and `Rc<dyn compiler::CompilerHost>` in the program), and
//! `freeze` writes it after sharing, so the fields that `freeze` clears are
//! `RefCell`s. `freeze` drops the `builder` and `project` references, which
//! breaks the `Project -> host -> builder -> Project` cycle.

use crate::project::prelude::*;

use crate::contentmapper;
use crate::frontend::module::{AheadCall, ModuleResolutionCacheKey};
use crate::frontend::parser;
use std::cell::Cell;
use std::sync::Arc;
use xxhash_rust::xxh3::xxh3_128;

// Go: project/compilerhost.go:16 compilerHost
pub struct CompilerHost {
    pub config_file_path: tspath::Path,
    pub current_directory: String,
    pub session_options: Rc<SessionOptions>,

    pub source_fs: Rc<SourceFS>,
    pub config_file_registry: RefCell<Option<Rc<ConfigFileRegistry>>>,

    pub project: RefCell<Option<Rc<RefCell<Project>>>>,
    pub builder: RefCell<Option<Rc<ProjectCollectionBuilder>>>,
    pub logger: RefCell<Option<Rc<logging::LogTree>>>,
    // tsgo#4712. PORT: Go nil interface is `None`. `content_mapper_once`
    // is Go `contentMapperOnce` (`sync.Once`).
    pub content_mapper_project: RefCell<Option<Rc<dyn contentmapper::Project>>>,
    pub content_mapper_once: Cell<bool>,

    /// True when the project had no program when this host was made (its
    /// first load). `compiler::CompilerHost::prefetch_parses` returns it.
    // PORT: not in Go (see `compiler::CompilerHost::prefetch_parses`).
    pub first_load: bool,

    /// The module resolution keys of the last program load with this host,
    /// or else of the project's host before it: the keys that the next load
    /// resolves ahead (`compiler::CompilerHost::resolve_ahead`).
    // PORT: not in Go (perf).
    pub resolution_keys: Rc<RefCell<Option<Arc<[ModuleResolutionCacheKey]>>>>,
}

// Go: project/compilerhost.go:29 newCompilerHost
// PORT: reads `project.configFilePath`, so the caller must not hold a
// mutable borrow of `project` during this call. The host keeps its own
// `Rc`s of `project` and `builder` until `freeze`.
pub fn new_compiler_host(
    current_directory: &str,
    project: &Rc<RefCell<Project>>,
    builder: &Rc<ProjectCollectionBuilder>,
    logger: Option<Rc<logging::LogTree>>,
) -> Rc<CompilerHost> {
    let (config_file_path, first_load, resolution_keys) = {
        let project = project.borrow();
        (
            project.config_file_path.clone(),
            project.program.is_none(),
            project
                .host
                .as_ref()
                .and_then(|host| host.resolution_keys.borrow().clone()),
        )
    };
    let source_fs = new_source_fs(true, builder.fs.clone(), builder.to_path.clone());
    Rc::new(CompilerHost {
        config_file_path,
        current_directory: current_directory.to_string(),
        session_options: builder.session_options.clone(),

        source_fs,
        config_file_registry: RefCell::new(None),

        project: RefCell::new(Some(project.clone())),
        builder: RefCell::new(Some(builder.clone())),
        logger: RefCell::new(logger),
        content_mapper_project: RefCell::new(None),
        content_mapper_once: Cell::new(false),

        first_load,
        resolution_keys: Rc::new(RefCell::new(resolution_keys)),
    })
}

impl CompilerHost {
    // Go: project/compilerhost.go:50 compilerHost.freeze
    // freeze clears references to mutable state to make the compilerHost safe for use
    // after the snapshot has been finalized. See the usage in snapshot.go for more details.
    pub fn freeze(
        &self,
        snapshot_fs: Rc<SnapshotFS>,
        config_file_registry: Rc<ConfigFileRegistry>,
    ) {
        if self.builder.borrow().is_none() {
            crate::core::go_panic("freeze can only be called once".to_string());
        }
        *self.source_fs.source.borrow_mut() = snapshot_fs;
        self.source_fs.disable_tracking();
        *self.config_file_registry.borrow_mut() = Some(config_file_registry);
        // PORT: the old values are dropped after the borrows end, because
        // dropping the builder can drop other hosts and projects.
        let builder = self.builder.borrow_mut().take();
        let project = self.project.borrow_mut().take();
        let logger = self.logger.borrow_mut().take();
        drop(builder);
        drop(project);
        drop(logger);
    }

    // Go: project/compilerhost.go:62 compilerHost.ensureAlive
    pub fn ensure_alive(&self) {
        if self.builder.borrow().is_none() || self.project.borrow().is_none() {
            crate::core::go_panic(
                "method must not be called after snapshot initialization".to_string(),
            );
        }
    }
}

// Go: project/compilerhost.go:14 `var _ compiler.CompilerHost = (*compilerHost)(nil)`
impl compiler::CompilerHost for CompilerHost {
    // Go: project/compilerhost.go:69 compilerHost.DefaultLibraryPath
    // DefaultLibraryPath implements compiler.CompilerHost.
    fn default_library_path(&self) -> String {
        self.session_options.default_library_path.clone()
    }

    // Go: project/compilerhost.go:74 compilerHost.FS
    // FS implements compiler.CompilerHost.
    fn fs(&self) -> Rc<dyn vfs::Fs> {
        self.source_fs.clone()
    }

    // Go: project/compilerhost.go:79 compilerHost.GetCurrentDirectory
    // GetCurrentDirectory implements compiler.CompilerHost.
    fn get_current_directory(&self) -> String {
        self.current_directory.clone()
    }

    // Go: project/compilerhost.go:84 compilerHost.GetResolvedProjectReference
    // GetResolvedProjectReference implements compiler.CompilerHost.
    fn get_resolved_project_reference(
        &self,
        file_name: &str,
        path: &tspath::Path,
    ) -> Option<Rc<tsoptions::ParsedCommandLine>> {
        let builder = self.builder.borrow().clone();
        match builder {
            None => self
                .config_file_registry
                .borrow()
                .as_ref()
                .unwrap_or_else(|| crate::core::go_nil_dereference())
                .get_config(path),
            Some(builder) => {
                // acquireConfigForProject will bypass sourceFS, so track the file here.
                self.source_fs.track(file_name);
                let project = self
                    .project
                    .borrow()
                    .clone()
                    .unwrap_or_else(|| crate::core::go_nil_dereference());
                let logger = self.logger.borrow().clone();
                builder
                    .config_file_registry_builder
                    .acquire_config_for_project(file_name, path, &project, logger)
            }
        }
    }

    // Go: project/compilerhost.go:96 compilerHost.GetSourceFile
    // GetSourceFile implements compiler.CompilerHost. Files are cached in parseCache
    // and acquired immediately for the in-progress program.
    // PORT: the parse cache holds `HashedSourceFile` (the file and Go's
    // `file.Hash`); the program gets the file.
    fn get_source_file(
        &self,
        opts: &parser::SourceFileParseOptions,
    ) -> Option<Rc<parser::ParsedSourceFile>> {
        self.ensure_alive();
        if let Some(fh) = self.source_fs.get_file_by_path(&opts.file_name, &opts.path) {
            let key = new_parse_cache_key(opts, fh.hash(), fh.kind());
            let builder = self
                .builder
                .borrow()
                .clone()
                .unwrap_or_else(|| crate::core::go_nil_dereference());
            return Some(builder.parse_cache.acquire(key, fh).file);
        }
        None
    }

    // Go: project/compilerhost.go:112 compilerHost.GetContentMappedSourceFiles (tsgo#4712)
    // GetContentMappedSourceFile implements compiler.CompilerHost.
    // PORT: a file that cannot be read is `Ok` with no canonical file (Go
    // returns the zero value and a nil error). Go `file.Hash = key.Hash` is
    // `set_source_file_hash` (project/parsecache.rs).
    fn get_content_mapped_source_files(
        &self,
        parse_options: &parser::SourceFileParseOptions,
        mapper: &Rc<contentmapper::Mapper>,
    ) -> Result<contentmapper::SourceFiles, GoError> {
        self.ensure_alive();
        let Some(fh) = self
            .source_fs
            .get_file_by_path(&parse_options.file_name, &parse_options.path)
        else {
            return Ok(contentmapper::SourceFiles::default());
        };
        let builder = self
            .builder
            .borrow()
            .clone()
            .unwrap_or_else(|| crate::core::go_nil_dereference());
        // ts#64163: the locale comes from the builder context.
        let diagnostic_locale = locale::from_context(&builder.ctx);
        // ts#64221
        let Some(project) = compiler::CompilerHost::content_mapper_project(self) else {
            return Err(contentmapper::ERR_PROJECT_UNAVAILABLE.clone());
        };
        let identity = match project.identity(mapper) {
            Ok(identity) => identity,
            Err(err) => {
                return Err(contentmapper::new_transform_error(
                    contentmapper::TransformErrorKind::PROJECT,
                    Some(err),
                )
                .to_go_error());
            }
        };
        let transform_identity = xxh3_128(identity.as_bytes());
        let key = content_mapped_parse_cache_key(
            parse_options,
            fh.hash(),
            transform_identity,
            &diagnostic_locale,
        );
        let files = builder
            .content_mapped_parse_cache
            .acquire_or_error(key.clone(), || {
                let files = contentmapper::transform_and_parse(
                    parse_options,
                    &fh.content(),
                    mapper,
                    &*project,
                )?;
                // Go: binder.BindSourceFile on the canonical file and on each
                // supplemental file (ts#63952). PORT: not ported; the Rust
                // binder binds each program version in one arena
                // (`program::bind_all`), see `new_parse_cache`.
                if let Some(canonical) = &files.canonical {
                    set_source_file_hash(canonical, key.hash);
                }
                for supplemental in &files.supplemental {
                    set_source_file_hash(supplemental, key.hash);
                }
                Ok(files)
            })?;
        let fs = compiler::CompilerHost::fs(self);
        if let Err(err) =
            contentmapper::check_supplemental_file_name_collisions(&files, &|name: &str| {
                vfs::Fs::file_exists(&*fs, name)
            })
        {
            deref_content_mapped_file(&builder.content_mapped_parse_cache, &key);
            return Err(err);
        }
        Ok(files)
    }

    // Go: project/compilerhost.go:153 compilerHost.ContentMapperProject (tsgo#4712, ts#64221)
    // PORT: the body of Go `ensureContentMapperProject` moved here in ts#64221
    // (Go `contentMapperOnce.Do`).
    fn content_mapper_project(&self) -> Option<Rc<dyn contentmapper::Project>> {
        if !self.content_mapper_once.replace(true) {
            let content_mapper_host = self
                .builder
                .borrow()
                .as_ref()
                .and_then(|builder| builder.content_mapper_host.clone());
            if let Some(content_mapper_host) = content_mapper_host {
                let project = self
                    .project
                    .borrow()
                    .clone()
                    .unwrap_or_else(|| crate::core::go_nil_dereference());
                let command_line = project.borrow().get_command_line_with_typings_files();
                // Go `ContentMappers` is nil-safe: a nil command line has
                // none, so it returns before the other getters.
                if let Some(command_line) =
                    command_line.filter(|command_line| !command_line.content_mappers().is_empty())
                {
                    let content_mapper_project =
                        content_mapper_host.project(contentmapper::ProjectSpec {
                            config_file_name: command_line.config_name().to_string(),
                            mappers: command_line.content_mappers().to_vec(),
                            compiler_options: Some(command_line.compiler_options().clone()),
                        });
                    *self.content_mapper_project.borrow_mut() = content_mapper_project;
                }
            }
        }
        self.content_mapper_project.borrow().clone()
    }

    // Go: project/compilerhost.go:106 compilerHost.Trace
    // Trace implements compiler.CompilerHost.
    fn trace(&self, msg: &'static crate::diagnostics::Message, args: Vec<String>) {
        let logger = self.logger.borrow().clone();
        logger.log(&crate::diagnostics_loc::message_localize(
            msg,
            &locale::DEFAULT,
            &args,
        ));
    }

    // PORT: not in Go (see `compiler::CompilerHost::prefetch_parses`). A
    // rebuild gets almost every file from the parse cache, which uses a
    // worker parse only on a miss. Parse workers would parse the whole
    // program again for nothing, and those parses stay in the workers' AST
    // arenas (about 30 MiB for each Query core rebuild). The first load of
    // a project still parses ahead.
    fn prefetch_parses(&self) -> bool {
        self.first_load
    }

    // PORT: not in Go (see `compiler::CompilerHost::release`). Go frees the
    // host when the last program that uses it is freed. The port keeps the
    // program shell (multiprog M2), so the host drops its data here: the
    // snapshot file system (disk file map copy, overlays, cachedvfs
    // results), the seen files and missing directories, and the config
    // registry. A later file read panics, like a use after `freeze` does
    // for the builder.
    fn release(&self) {
        self.source_fs.release();
        let config_file_registry = self.config_file_registry.borrow_mut().take();
        drop(config_file_registry);
        let resolution_keys = self.resolution_keys.borrow_mut().take();
        drop(resolution_keys);
    }

    // PORT: not in Go (perf, see `compiler::CompilerHost::resolve_ahead`).
    // Only while the host tracks the files that its program load sees
    // (before `freeze`), on a case-sensitive file system whose layers are
    // the open files over the OS file system: the workers then see what
    // the loader sees, except the snapshot's cached files, which the check
    // compares (`accept_ahead_answer`). A case-insensitive file system
    // could spell a read file name another way than the loader would.
    fn resolve_ahead(&self) -> Option<compiler::resolve_ahead::ResolveAheadHost> {
        if !self.source_fs.tracking.get() {
            return None;
        }
        let builder = self.builder.borrow().clone()?;
        let files = builder.fs.clone();
        // The loader reads `files` through `source_fs`.
        if !std::ptr::addr_eq(
            Rc::as_ptr(&*self.source_fs.source.borrow()),
            Rc::as_ptr(&files),
        ) {
            return None;
        }
        let use_case_sensitive_file_names =
            vfs::Fs::use_case_sensitive_file_names(&*self.source_fs);
        if !use_case_sensitive_file_names {
            return None;
        }
        // The workers make the paths as `source_fs` does.
        let current_directory = self.session_options.current_directory.clone();
        let probe = "a/B.ts";
        if (self.source_fs.to_path)(probe)
            != tspath::to_path(probe, &current_directory, use_case_sensitive_file_names)
        {
            return None;
        }
        let (open_files, open_directories) = files.open_files_over_os()?;
        let reads = RefCell::new(FxHashMap::default());
        let accept = {
            let source_fs = self.source_fs.clone();
            let files = files.clone();
            Rc::new(
                move |_key: &ModuleResolutionCacheKey,
                      _value: &ResolvedModule,
                      calls: &[AheadCall]| {
                    accept_ahead_answer(&source_fs, &files, &reads, calls)
                },
            )
        };
        let keys = self.resolution_keys.clone();
        let scratch = cfg!(debug_assertions).then(|| {
            let to_path = self.source_fs.to_path.clone();
            Rc::new(move || {
                let fs = new_source_fs(true, files.clone(), to_path.clone());
                let tracked = fs.clone();
                compiler::resolve_ahead::ScratchFs {
                    fs,
                    tracked: Box::new(move || {
                        let seen = tracked
                            .seen_files
                            .borrow()
                            .as_ref()
                            .map(|seen| seen.borrow().clone());
                        let missing = tracked
                            .missing_directories
                            .as_ref()
                            .map(|missing| missing.borrow().clone());
                        (seen.unwrap_or_default(), missing.unwrap_or_default())
                    }),
                    to_path: to_path.clone(),
                }
            }) as Rc<dyn Fn() -> compiler::resolve_ahead::ScratchFs>
        });
        Some(compiler::resolve_ahead::ResolveAheadHost {
            previous_keys: self.resolution_keys.borrow().clone(),
            view: compiler::resolve_ahead::WorkerView {
                current_directory,
                use_case_sensitive_file_names,
                open_files,
                open_directories,
            },
            accept,
            keep_keys: Box::new(move |new_keys| *keys.borrow_mut() = Some(new_keys)),
            scratch,
        })
    }
}

/// Checks the file system calls of a resolve-ahead answer on this host's
/// file system, as the loader's own resolution of the key would make them
/// at this point of the load, and replays their side effects
/// (`compiler::CompilerHost::resolve_ahead`). False: a call would give
/// another answer here, and the loader resolves the key itself.
///
/// - `file_exists`: the snapshot's cached file of the path decides, if it
///   has one (`SnapshotFSBuilder::cached_file_state`). A cached file that
///   needs a reload fails the check: the loader's lookup would read it.
///   Else the layered file system decides, which the worker read the same
///   way (open files over the OS).
/// - a read is the loader's own read (`SourceFS::get_file`: it tracks the
///   file, caches it and notes a `node_modules` realpath alias), made at
///   the moment the loader would make it, since every call before it gave
///   the same answer. Its text must have the worker's hash. `reads` keeps
///   the reads of this load, so a later answer that reads the file again
///   only compares the hash.
/// - then each `file_exists` path becomes a seen file and each missing
///   directory a missing directory, as the loader's calls would note them.
fn accept_ahead_answer(
    source_fs: &SourceFS,
    files: &SnapshotFSBuilder,
    reads: &RefCell<FxHashMap<String, Option<u128>>>,
    calls: &[AheadCall],
) -> bool {
    for call in calls {
        match call {
            AheadCall::FileExists { path, exists } => {
                let same = match files.cached_file_state(path) {
                    CachedFileState::Absent => true,
                    CachedFileState::Live => *exists,
                    CachedFileState::NoValue => !*exists,
                    CachedFileState::NeedsReload => false,
                };
                if !same {
                    return false;
                }
            }
            AheadCall::MissingDirectory { .. } => {}
            AheadCall::Read { file_name, hash } => {
                let known = reads.borrow().get(file_name).copied();
                let read = known.unwrap_or_else(|| {
                    let read = source_fs.get_file(file_name).map(|file| file.hash());
                    reads.borrow_mut().insert(file_name.clone(), read);
                    read
                });
                if read != *hash {
                    return false;
                }
            }
        }
    }
    for call in calls {
        match call {
            AheadCall::FileExists { path, .. } => source_fs.track_path(path),
            AheadCall::MissingDirectory { path } => source_fs.note_missing_directory(path),
            AheadCall::Read { .. } => {}
        }
    }
    true
}
