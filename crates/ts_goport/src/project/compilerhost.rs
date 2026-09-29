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
use crate::frontend::parser;
use std::cell::Cell;
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
    let (config_file_path, first_load) = {
        let project = project.borrow();
        (project.config_file_path.clone(), project.program.is_none())
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
            panic!("freeze can only be called once");
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
            panic!("method must not be called after snapshot initialization");
        }
    }

    // Go: project/compilerhost.go:153 compilerHost.ensureContentMapperProject (tsgo#4712)
    pub fn ensure_content_mapper_project(&self) {
        if self.content_mapper_once.replace(true) {
            return;
        }
        let content_mapper_host = self
            .builder
            .borrow()
            .as_ref()
            .expect("invalid memory address or nil pointer dereference: compilerHost.builder")
            .content_mapper_host
            .clone();
        let Some(content_mapper_host) = content_mapper_host else {
            return;
        };
        let project = self
            .project
            .borrow()
            .clone()
            .expect("invalid memory address or nil pointer dereference: compilerHost.project");
        let command_line = project.borrow().get_command_line_with_typings_files().expect(
            "invalid memory address or nil pointer dereference: project.getCommandLineWithTypingsFiles",
        );
        let content_mapper_project = content_mapper_host.project(contentmapper::ProjectSpec {
            config_file_name: command_line.config_name().to_string(),
            mappers: command_line.content_mappers().to_vec(),
            compiler_options: Some(command_line.compiler_options().clone()),
        });
        *self.content_mapper_project.borrow_mut() = content_mapper_project;
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
                .expect("invalid memory address or nil pointer dereference: compilerHost.configFileRegistry")
                .get_config(path),
            Some(builder) => {
                // acquireConfigForProject will bypass sourceFS, so track the file here.
                self.source_fs.track(file_name);
                let project = self
                    .project
                    .borrow()
                    .clone()
                    .expect("invalid memory address or nil pointer dereference: compilerHost.project");
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
            let builder =
                self.builder.borrow().clone().expect(
                    "invalid memory address or nil pointer dereference: compilerHost.builder",
                );
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
            .expect("invalid memory address or nil pointer dereference: compilerHost.builder");
        let mut diagnostic_locale = locale::DEFAULT;
        if let Some(client) = &builder.client {
            diagnostic_locale = client.get_locale();
        }
        self.ensure_content_mapper_project();
        let Some(project) = self.content_mapper_project.borrow().clone() else {
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

    // Go: project/compilerhost.go:167 compilerHost.ContentMapperProject (tsgo#4712)
    fn content_mapper_project(&self) -> Option<Rc<dyn contentmapper::Project>> {
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
    }
}
