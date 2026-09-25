//! Go: execute/build/host.go, execute/build/compilerHost.go, and the
//! `ExtendedConfigCache` of execute/tsc/extendedconfigcache.go.
//!
//! PORT: Go `host` keeps a pointer to its `*Orchestrator` and reads
//! `opts.Sys`, `opts.Command` and `toPath` through it. Here the host keeps
//! those values itself, so the orchestrator process and the build worker
//! process can both make one (plan D1). The orchestrator owns the host as
//! `Rc<BuildHost>` and passes clones where Go passes `o.host`.
//!
//! PORT: Go `time.Time` is `Option<SystemTime>` (`None` = zero) and
//! `time.Duration` is `Duration`, as in build_task.rs.

use crate::execute::build::command_line::ParsedBuildCommandLine;
use crate::execute::build::parse_cache::ParseCache;
use crate::execute::incremental::build_info::BuildInfo;
use crate::execute::incremental::incremental::{self as incremental, BuildInfoReader};
use crate::execute::tsc::compile::System;
use crate::frontend::prelude::*;
use std::hash::{Hash, Hasher};
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

// Go: build/host.go:17 host
pub struct BuildHost {
    // PORT: in place of Go `orchestrator *Orchestrator` (see top).
    sys: Rc<dyn System>,
    command: Rc<ParsedBuildCommandLine>,
    compare_paths_options: ComparePathsOptions,

    host: Rc<dyn CompilerHost>,

    // Caches that last only for build cycle and then cleared out
    pub extended_config_cache: TscExtendedConfigCache,
    pub source_files: ParseCache<SourceFileCacheKey, Rc<ParsedSourceFile>>,
    pub config_times: RefCell<FxHashMap<Path, Duration>>,

    // caches that stay as long as they are needed
    pub resolved_references: ParseCache<Path, Rc<ParsedCommandLine>>,
    pub m_times: RefCell<FxHashMap<Path, Option<SystemTime>>>,
}

impl BuildHost {
    // PORT: Go builds the host inline in `NewOrchestrator`
    // (orchestrator.go:618): `compiler.NewCachedFSCompilerHost(cwd, sys.FS(),
    // sys.DefaultLibraryPath(), nil, nil)` and an empty mTimes map.
    pub fn new(
        sys: Rc<dyn System>,
        command: Rc<ParsedBuildCommandLine>,
        compare_paths_options: ComparePathsOptions,
    ) -> BuildHost {
        let host = new_cached_fs_compiler_host(
            &sys.get_current_directory(),
            sys.fs(),
            &sys.default_library_path(),
            None,
            None,
        );
        BuildHost {
            sys,
            command,
            compare_paths_options,
            host,
            extended_config_cache: TscExtendedConfigCache::default(),
            source_files: ParseCache::default(),
            config_times: RefCell::new(FxHashMap::default()),
            resolved_references: ParseCache::default(),
            m_times: RefCell::new(FxHashMap::default()),
        }
    }

    // Go: orchestrator.go:87 (*Orchestrator).toPath, as the host reaches it.
    pub fn to_path(&self, file_name: &str) -> Path {
        to_path(
            file_name,
            &self.compare_paths_options.current_directory,
            self.compare_paths_options.use_case_sensitive_file_names,
        )
    }

    // Go: build/host.go:83 (*host).GetMTime
    pub fn get_m_time(&self, file: &str) -> Option<SystemTime> {
        self.load_or_store_m_time(file, None, true)
    }

    // Go: build/host.go:87 (*host).SetMTime
    pub fn set_m_time(&self, file: &str, m_time: Option<SystemTime>) -> Result<(), FsError> {
        CompilerHost::fs(self).chtimes(file, None, m_time)
    }

    // Go: build/host.go:91 (*host).loadOrStoreMTime
    pub fn load_or_store_m_time(
        &self,
        file: &str,
        old_cache: Option<&FxHashMap<Path, Option<SystemTime>>>,
        store: bool,
    ) -> Option<SystemTime> {
        let path = self.to_path(file);
        if let Some(existing) = self.m_times.borrow().get(&path) {
            return *existing;
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
            m_time = incremental::get_m_time(&*self.host, file);
        }
        if store {
            m_time = *self.m_times.borrow_mut().entry(path).or_insert(m_time);
        }
        m_time
    }

    // Go: build/host.go:111 (*host).storeMTime
    pub fn store_m_time(&self, file: &str, m_time: Option<SystemTime>) {
        let path = self.to_path(file);
        self.m_times.borrow_mut().insert(path, m_time);
    }

    // Go: build/host.go:116 (*host).storeMTimeFromOldCache
    pub fn store_m_time_from_old_cache(
        &self,
        file: &str,
        old_cache: &FxHashMap<Path, Option<SystemTime>>,
    ) {
        let path = self.to_path(file);
        if let Some(m_time) = old_cache.get(&path) {
            self.m_times.borrow_mut().insert(path, *m_time);
        }
    }

    // Go: build/host.go:77 (*host).ReadBuildInfo
    // PORT: Go reads through the task's `loadOrStoreBuildInfo` cache. Only
    // `incremental.ReadBuildInfoProgram` calls this, and it runs in the
    // build worker, which has no tasks (plan D1). The task cache was filled
    // from the same file by the orchestrator, so the worker reads the file
    // (`incremental.NewBuildInfoReader(h.host)`), which gives the same value.
    pub fn read_build_info(&self, config: &ParsedCommandLine) -> Option<BuildInfo> {
        incremental::new_build_info_reader(self.host.clone()).read_build_info(config)
    }
}

impl CompilerHost for BuildHost {
    // Go: build/host.go:36 (*host).FS
    fn fs(&self) -> Rc<dyn Fs> {
        self.host.fs()
    }

    // Go: build/host.go:40 (*host).DefaultLibraryPath
    fn default_library_path(&self) -> String {
        self.host.default_library_path()
    }

    // Go: build/host.go:44 (*host).GetCurrentDirectory
    fn get_current_directory(&self) -> String {
        self.host.get_current_directory()
    }

    // Go: build/host.go:48 (*host).Trace
    fn trace(&self, _msg: &'static Message, _args: Vec<String>) {
        panic!(
            "build.Orchestrator.host does not support tracing, use a different host for tracing"
        );
    }

    // Go: build/host.go:52 (*host).GetSourceFile
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<Rc<ParsedSourceFile>> {
        if is_declaration_file_name(&opts.file_name)
            || file_extension_is(&opts.file_name, EXTENSION_JSON)
        {
            // Cache dts and json files as they will be reused
            return self.source_files.load_or_store(
                SourceFileCacheKey(opts.clone()),
                |key| self.host.get_source_file(&key.0),
                false, /* allowZero */
            );
        }
        self.host.get_source_file(opts)
    }

    // Go: build/host.go:60 (*host).GetResolvedProjectReference
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
                let command_line_raw = match &self.command.raw {
                    CompilerOptionsValue::Map(raw) => {
                        let mut wrapped = IndexMap::default();
                        wrapped.insert(
                            "compilerOptions".to_string(),
                            CompilerOptionsValue::Map(raw.clone()),
                        );
                        Some(wrapped)
                    }
                    _ => None,
                };
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
}

// Go: build/host.go:30 `_ incremental.BuildInfoReader = (*host)(nil)`
impl BuildInfoReader for BuildHost {
    fn read_build_info(&self, config: &ParsedCommandLine) -> Option<BuildInfo> {
        BuildHost::read_build_info(self, config)
    }
}

// Go: build/host.go:31 `_ incremental.Host = (*host)(nil)`
impl incremental::Host for BuildHost {
    fn get_m_time(&self, file_name: &str) -> Option<SystemTime> {
        BuildHost::get_m_time(self, file_name)
    }

    fn set_m_time(&self, file_name: &str, m_time: Option<SystemTime>) -> Result<(), FsError> {
        BuildHost::set_m_time(self, file_name, m_time)
    }
}

// Go: build/compilerHost.go:12 compilerHost
// PORT: the host that the build task gives `compiler.NewProgram`: the
// build host with the task's trace writer.
pub struct BuildCompilerHost {
    pub host: Rc<BuildHost>,
    pub trace: TraceFn,
}

impl CompilerHost for BuildCompilerHost {
    // Go: build/compilerHost.go:19 (*compilerHost).FS
    fn fs(&self) -> Rc<dyn Fs> {
        CompilerHost::fs(&*self.host)
    }

    // Go: build/compilerHost.go:23 (*compilerHost).DefaultLibraryPath
    fn default_library_path(&self) -> String {
        self.host.default_library_path()
    }

    // Go: build/compilerHost.go:27 (*compilerHost).GetCurrentDirectory
    fn get_current_directory(&self) -> String {
        CompilerHost::get_current_directory(&*self.host)
    }

    // Go: build/compilerHost.go:31 (*compilerHost).Trace
    fn trace(&self, msg: &'static Message, args: Vec<String>) {
        (self.trace)(msg, args);
    }

    // Go: build/compilerHost.go:35 (*compilerHost).GetSourceFile
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<Rc<ParsedSourceFile>> {
        self.host.get_source_file(opts)
    }

    // Go: build/compilerHost.go:39 (*compilerHost).GetResolvedProjectReference
    fn get_resolved_project_reference(
        &self,
        file_name: &str,
        path: &Path,
    ) -> Option<Rc<ParsedCommandLine>> {
        self.host.get_resolved_project_reference(file_name, path)
    }
}
