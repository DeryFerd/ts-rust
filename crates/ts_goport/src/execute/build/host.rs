//! Go: execute/build/host.go, execute/build/compilerHost.go, and the
//! `ExtendedConfigCache` of execute/tsc/extendedconfigcache.go.
//!
//! PORT: Go `host` keeps a pointer to its `*Orchestrator` and reads
//! `opts.Sys`, `opts.Command` and `toPath` through it. Here the host keeps
//! those values itself, so it needs no reference back to the orchestrator.
//! The orchestrator owns the host as `Rc<BuildHost>` and passes clones
//! where Go passes `o.host`.
//!
//! PORT: Go `time.Time` is `Option<SystemTime>` (`None` = zero) and
//! `time.Duration` is `Duration`, as in build_task.rs.

use crate::contentmapper::{self, Mapper, Project, SourceFiles};
use crate::execute::build::command_line::ParsedBuildCommandLine;
use crate::execute::build::config_prefetch::ConfigPrefetch;
use crate::execute::build::orchestrator::MTimePrefetch;
use crate::execute::build::parse_cache::ParseCache;
use crate::execute::incremental::incremental;
use crate::execute::tsc::compile::System;
use crate::frontend::prelude::*;
use crate::gostd::GoError;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::{Duration, SystemTime};

// Go: tsc/extendedconfigcache.go:15 ExtendedConfigCache
// PORT: the Go type is `tsc.ExtendedConfigCache`; the Rust name adds `Tsc`
// because the `tsoptions.ExtendedConfigCache` interface already has the
// plain name. The per-entry mutex is dropped (one thread, see
// parse_cache.rs). The map borrow is not held while the config parses, so
// a nested `extends` can use the cache.
#[derive(Default)]
pub struct TscExtendedConfigCache {
    m: RefCell<FxHashMap<Path, Rc<ExtendedConfigCacheEntry>>>,
}

impl ExtendedConfigCache for TscExtendedConfigCache {
    // Go: tsc/extendedconfigcache.go:27 (*ExtendedConfigCache).GetExtendedConfig
    fn get_extended_config(
        &self,
        file_name: &str,
        path: &Path,
        resolution_stack: &[Path],
        host: &dyn ParseConfigHost,
    ) -> Rc<ExtendedConfigCacheEntry> {
        if let Some(entry) = self.m.borrow().get(path) {
            return entry.clone();
        }
        let entry = Rc::new(parse_extended_config(
            file_name,
            path.clone(),
            resolution_stack,
            host,
            Some(self),
        ));
        self.m
            .borrow_mut()
            .entry(path.clone())
            .or_insert(entry)
            .clone()
    }
}

impl TscExtendedConfigCache {
    // PORT: Go assigns a new cache (`o.host.extendedConfigCache =
    // tsc.ExtendedConfigCache{}`, orchestrator.go:276). The programs of a
    // build keep the host `Rc`, so the cache is emptied in place.
    pub fn reset(&self) {
        self.m.borrow_mut().clear();
    }
}

// PORT: Go keys the source file cache by `ast.SourceFileParseOptions`, a
// comparable struct. The Rust struct has no `Hash`, so this key hashes the
// same fields.
#[derive(Clone, PartialEq, Eq)]
pub struct SourceFileCacheKey(pub SourceFileParseOptions);

impl Hash for SourceFileCacheKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.file_name.hash(state);
        self.0.path.hash(state);
        self.0.external_module_indicator_options.jsx.hash(state);
        self.0.external_module_indicator_options.force.hash(state);
    }
}

// Go: build/host.go:18 host
pub struct BuildHost {
    // PORT: in place of Go `orchestrator *Orchestrator` (see top).
    sys: Rc<dyn System>,
    command: Rc<ParsedBuildCommandLine>,
    compare_paths_options: ComparePathsOptions,

    host: Rc<dyn CompilerHost>,
    // PORT: the `*cachedvfs.FS` of `host`, kept for `resetCaches`. Go
    // reaches it as `o.host.host.FS().(*cachedvfs.FS)` (orchestrator.go:272).
    pub cached_fs: Rc<CachedFs>,

    // Caches that last only for build cycle and then cleared out
    pub extended_config_cache: TscExtendedConfigCache,
    pub source_files: ParseCache<SourceFileCacheKey, Rc<ParsedSourceFile>>,
    pub config_times: RefCell<FxHashMap<Path, Duration>>,

    // caches that stay as long as they are needed
    pub resolved_references: ParseCache<Path, Rc<ParsedCommandLine>>,
    // PORT: not in Go (perf). The threads that parse the configs of the
    // graph ahead of `get_resolved_project_reference` (config_prefetch.rs).
    pub config_prefetch: RefCell<Option<ConfigPrefetch>>,
    // PORT: Go `*collections.SyncMap`. The task `writeFile` stores into it
    // from the checker threads.
    pub m_times: Arc<Mutex<FxHashMap<Path, Option<SystemTime>>>>,
    // PORT: not in Go (perf). The mtimes that the build info threads read
    // for the up-to-date checks of this build cycle (orchestrator.rs
    // `BuildInfoPrefetch`). `load_or_store_m_time` takes one where it would
    // read the file system.
    pub m_time_prefetch: RefCell<Option<MTimePrefetch>>,
}

impl BuildHost {
    // PORT: Go builds the host inline in `NewOrchestrator`
    // (orchestrator.go:764): `compiler.NewCachedFSCompilerHost(cwd, sys.FS(),
    // sys.DefaultLibraryPath(), nil, nil, nil)` and an empty mTimes map.
    // `NewCachedFSCompilerHost` is written out (compiler/host.go:44) to keep
    // the cached file system.
    pub fn new(
        sys: Rc<dyn System>,
        command: Rc<ParsedBuildCommandLine>,
        compare_paths_options: ComparePathsOptions,
    ) -> BuildHost {
        let cached_fs = cachedvfs_from(sys.fs());
        let host = new_compiler_host(
            &sys.get_current_directory(),
            cached_fs.clone(),
            &sys.default_library_path(),
            None,
            None,
            None,
        );
        BuildHost {
            sys,
            command,
            compare_paths_options,
            host,
            cached_fs,
            extended_config_cache: TscExtendedConfigCache::default(),
            source_files: ParseCache::default(),
            config_times: RefCell::new(FxHashMap::default()),
            resolved_references: ParseCache::default(),
            config_prefetch: RefCell::new(None),
            m_times: Arc::default(),
            m_time_prefetch: RefCell::new(None),
        }
    }

    // Go: build/host.go:72, the raw command line options of
    // `GetResolvedProjectReference`: wrapped in a "compilerOptions" key to
    // match the tsconfig.json structure.
    pub fn command_line_raw(&self) -> Option<IndexMap<String, CompilerOptionsValue>> {
        match &self.command.raw {
            CompilerOptionsValue::Map(raw) => {
                let mut wrapped = IndexMap::default();
                wrapped.insert(
                    "compilerOptions".to_string(),
                    CompilerOptionsValue::Map(raw.clone()),
                );
                Some(wrapped)
            }
            _ => None,
        }
    }

    // Go: orchestrator.go:91 (*Orchestrator).toPath, as the host reaches it.
    pub fn to_path(&self, file_name: &str) -> Path {
        to_path(
            file_name,
            &self.compare_paths_options.current_directory,
            self.compare_paths_options.use_case_sensitive_file_names,
        )
    }

    // Go: build/host.go:94 (*host).GetMTime
    pub fn get_m_time(&self, file: &str) -> Option<SystemTime> {
        self.load_or_store_m_time(file, None, true)
    }

    // Go: build/host.go:98 (*host).SetMTime
    pub fn set_m_time(&self, file: &str, m_time: Option<SystemTime>) -> Result<(), FsError> {
        CompilerHost::fs(self).chtimes(file, None, m_time)
    }

    // Go: build/host.go:102 (*host).loadOrStoreMTime
    pub fn load_or_store_m_time(
        &self,
        file: &str,
        old_cache: Option<&FxHashMap<Path, Option<SystemTime>>>,
        store: bool,
    ) -> Option<SystemTime> {
        let path = self.to_path(file);
        // PORT: Go `Load`, then `LoadOrStore` below. The lock is not held
        // while `get_m_time` reads the file system.
        let existing = self
            .m_times
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(&path)
            .copied();
        if let Some(existing) = existing {
            return existing;
        }
        let mut found = false;
        let mut m_time = None;
        if let Some(old_cache) = old_cache {
            if let Some(old) = old_cache.get(&path) {
                m_time = *old;
                found = true;
            }
        }
        if !found {
            // PORT: perf. An mtime that a build info thread read.
            let prefetched = self.m_time_prefetch.borrow().as_ref().and_then(|m_times| {
                m_times
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .remove(&path)
            });
            m_time = match prefetched {
                Some(m_time) => m_time,
                None => incremental::get_m_time(&*self.host, file),
            };
        }
        if store {
            m_time = *self
                .m_times
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .entry(path)
                .or_insert(m_time);
        }
        m_time
    }

    // Go: build/host.go:121 (*host).storeMTime
    pub fn store_m_time(&self, file: &str, m_time: Option<SystemTime>) {
        let path = self.to_path(file);
        self.m_times
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(path, m_time);
    }

    // Go: build/host.go:126 (*host).storeMTimeFromOldCache
    pub fn store_m_time_from_old_cache(
        &self,
        file: &str,
        old_cache: &FxHashMap<Path, Option<SystemTime>>,
    ) {
        let path = self.to_path(file);
        if let Some(m_time) = old_cache.get(&path) {
            self.m_times
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .insert(path, *m_time);
        }
    }

    // Go: build/host.go:87 (*host).ReadBuildInfo
    // PORT: Go reads the build info cache of the config's task
    // (`loadOrStoreBuildInfo`). Its only caller is `ReadBuildInfoProgram` in
    // `compileAndEmit`, with the config of the task that compiles, so
    // `BuildTask::compile_and_emit_start` reads its own cache (`TaskBuildInfo`)
    // and the host does not implement `incremental.BuildInfoReader`.
}

impl CompilerHost for BuildHost {
    // Go: build/host.go:38 (*host).FS
    fn fs(&self) -> Rc<dyn Fs> {
        self.host.fs()
    }

    // Go: build/host.go:42 (*host).DefaultLibraryPath
    fn default_library_path(&self) -> String {
        self.host.default_library_path()
    }

    // Go: build/host.go:46 (*host).GetCurrentDirectory
    fn get_current_directory(&self) -> String {
        self.host.get_current_directory()
    }

    // Go: build/host.go:50 (*host).Trace
    fn trace(&self, _msg: &'static Message, _args: Vec<String>) {
        panic!(
            "build.Orchestrator.host does not support tracing; use a different host for tracing"
        );
    }

    // Go: build/host.go:54 (*host).GetSourceFile
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<Rc<ParsedSourceFile>> {
        if is_declaration_file_name(&opts.file_name)
            || file_extension_is(&opts.file_name, EXTENSION_JSON)
        {
            // Cache dts and json files as they will be reused
            // PORT: a parse that the cache keeps can be left out of one
            // program (a deduplicated package, or a file that only such a
            // package imports) and be a program file of a later one. Go
            // keeps the whole `*ast.SourceFile`. The note makes the publish
            // of the first program give the store its complete Go file, so
            // the later program can use it.
            return self.source_files.load_or_store(
                SourceFileCacheKey(opts.clone()),
                |key| {
                    let file = self.host.get_source_file(&key.0);
                    if let Some(file) = &file {
                        crate::program::note_parsed_source_file(file);
                    }
                    file
                },
                false, /* allowZero */
            );
        }
        self.host.get_source_file(opts)
    }

    // Go: build/host.go:62 (*host).GetContentMappedSourceFiles (tsgo#4712)
    fn get_content_mapped_source_files(
        &self,
        _parse_options: &SourceFileParseOptions,
        _mapper: &Rc<Mapper>,
    ) -> Result<SourceFiles, GoError> {
        Err(contentmapper::ERR_PROJECT_UNAVAILABLE.clone())
    }

    // Go: build/host.go:66 (*host).ContentMapperProject (tsgo#4712)
    fn content_mapper_project(&self) -> Option<Rc<dyn Project>> {
        panic!(
            "build.Orchestrator.host does not support content mapper project; use an individual project's compiler host instead"
        );
    }

    // PORT: not in Go (see `CompilerHost::cached_source_file_names`). The
    // `.d.ts` and `.json` files that `get_source_file` keeps.
    fn cached_source_file_names(&self) -> FxHashSet<String> {
        let mut names = FxHashSet::default();
        self.source_files.for_each_stored(|key| {
            names.insert(key.0.file_name.clone());
        });
        names
    }

    // Go: build/host.go:70 (*host).GetResolvedProjectReference
    fn get_resolved_project_reference(
        &self,
        file_name: &str,
        path: &Path,
    ) -> Option<Rc<ParsedCommandLine>> {
        self.resolved_references.load_or_store(
            path.clone(),
            |path| {
                let config_start = self.sys.now();
                // Wrap command line options in "compilerOptions" key to match tsconfig.json structure
                let command_line_raw = self.command_line_raw();
                let (command_line, _) = get_parsed_command_line_of_config_file_path(
                    file_name,
                    path.clone(),
                    Some(&self.command.compiler_options),
                    command_line_raw.as_ref(),
                    self,
                    Some(&self.extended_config_cache),
                );
                let config_time = self
                    .sys
                    .now()
                    .duration_since(config_start)
                    .unwrap_or_default();
                self.config_times
                    .borrow_mut()
                    .insert(path.clone(), config_time);
                command_line.map(Rc::new)
            },
            true, /* allowZero */
        )
    }
}

// PORT: Go passes the `*host` as a `tsoptions.ParseConfigHost` (it has
// `FS()` and `GetCurrentDirectory()`). Rust needs the explicit impl.
impl ParseConfigHost for BuildHost {
    fn fs(&self) -> Rc<dyn Fs> {
        self.host.fs()
    }

    fn get_current_directory(&self) -> String {
        self.host.get_current_directory()
    }

    // PORT: not in Go (perf). The file names that a config thread matched
    // (config_prefetch.rs), else Go `getFileNamesFromConfigSpecs`.
    fn get_file_names_from_config_specs(
        &self,
        config_file_name: &str,
        config_file_specs: &ConfigFileSpecs,
        base_path: &str,
        options: Option<&CompilerOptions>,
        extra_extensions: &[String],
    ) -> (Vec<String>, i32) {
        let fs = ParseConfigHost::fs(self);
        match &*self.config_prefetch.borrow() {
            Some(prefetch) => prefetch.get_file_names_from_config_specs(
                config_file_name,
                config_file_specs,
                base_path,
                options,
                extra_extensions,
                &*fs,
            ),
            None => get_file_names_from_config_specs(
                config_file_specs,
                base_path,
                options,
                &*fs,
                extra_extensions,
            ),
        }
    }
}

// Go: build/host.go:35 `_ incremental.Host = (*host)(nil)`
impl incremental::Host for BuildHost {
    fn fs(&self) -> Rc<dyn Fs> {
        CompilerHost::fs(self)
    }

    fn get_m_time(&self, file_name: &str) -> Option<SystemTime> {
        BuildHost::get_m_time(self, file_name)
    }

    fn set_m_time(&self, file_name: &str, m_time: Option<SystemTime>) -> Result<(), FsError> {
        BuildHost::set_m_time(self, file_name, m_time)
    }
}

// Go: build/compilerHost.go:13 compilerHost
// PORT: the host that the build task gives `compiler.NewProgram`: the
// build host with the task's trace writer. Go nil `contentMapperProject`
// is `None`.
pub struct BuildCompilerHost {
    pub host: Rc<BuildHost>,
    pub trace: TraceFn,
    pub content_mapper_project: Option<Rc<dyn Project>>,
}

impl CompilerHost for BuildCompilerHost {
    // Go: build/compilerHost.go:21 (*compilerHost).FS
    fn fs(&self) -> Rc<dyn Fs> {
        CompilerHost::fs(&*self.host)
    }

    // Go: build/compilerHost.go:25 (*compilerHost).DefaultLibraryPath
    fn default_library_path(&self) -> String {
        self.host.default_library_path()
    }

    // Go: build/compilerHost.go:29 (*compilerHost).GetCurrentDirectory
    fn get_current_directory(&self) -> String {
        CompilerHost::get_current_directory(&*self.host)
    }

    // Go: build/compilerHost.go:33 (*compilerHost).Trace
    fn trace(&self, msg: &'static Message, args: Vec<String>) {
        (self.trace)(msg, args);
    }

    // Go: build/compilerHost.go:37 (*compilerHost).GetSourceFile
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<Rc<ParsedSourceFile>> {
        self.host.get_source_file(opts)
    }

    // Go: build/compilerHost.go:41 (*compilerHost).GetContentMappedSourceFiles (tsgo#4712)
    // PORT: Go returns `(files, err)`; a file that cannot be read is `Ok`
    // with no canonical file, as in the compiler host.
    fn get_content_mapped_source_files(
        &self,
        parse_options: &SourceFileParseOptions,
        mapper: &Rc<Mapper>,
    ) -> Result<SourceFiles, GoError> {
        let Some(project) = self.content_mapper_project() else {
            return Err(contentmapper::ERR_PROJECT_UNAVAILABLE.clone());
        };
        let fs = CompilerHost::fs(self);
        let (content, ok) = fs.read_file(&parse_options.file_name);
        if !ok {
            return Ok(SourceFiles::default());
        }
        let files = contentmapper::transform_and_parse(parse_options, &content, mapper, &*project)?;
        contentmapper::check_supplemental_file_name_collisions(&files, &|name: &str| {
            fs.file_exists(name)
        })?;
        Ok(files)
    }

    // Go: build/compilerHost.go:56 (*compilerHost).ContentMapperProject (tsgo#4712)
    fn content_mapper_project(&self) -> Option<Rc<dyn Project>> {
        self.content_mapper_project.clone()
    }

    // Go: build/compilerHost.go:60 (*compilerHost).GetResolvedProjectReference
    fn get_resolved_project_reference(
        &self,
        file_name: &str,
        path: &Path,
    ) -> Option<Rc<ParsedCommandLine>> {
        self.host.get_resolved_project_reference(file_name, path)
    }

    // PORT: not in Go (see `CompilerHost::cached_source_file_names`).
    fn cached_source_file_names(&self) -> FxHashSet<String> {
        self.host.cached_source_file_names()
    }
}
