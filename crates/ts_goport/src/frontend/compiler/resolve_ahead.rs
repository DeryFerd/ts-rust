//! Resolve ahead: worker threads resolve again, in the same order, the
//! module names that the previous program load of a language server project
//! resolved, while the loader of the new load runs (lspp95 plan, step 1).
//!
//! The loader stays serial. It takes a worker answer only when the answer
//! passes its host's check (`ResolveAheadHost::accept`): every file system
//! call of the worker's resolution gives the same answer on the loader's
//! file system, and the check replays the side effects of the calls (seen
//! files, missing directories, file reads) at the moment the loader's own
//! resolution would make them. Else the loader resolves the key itself. So
//! the program, its file order and the watched files are the same as with
//! no workers.
// PORT: not in Go (perf). Go resolves in each parse task, on all threads;
// the port's loader resolves on one thread (contract 10).

use crate::frontend::prelude::*;
use std::cell::Cell;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use xxhash_rust::xxh3::xxh3_128;

/// Whether program loads resolve ahead (`GOPORT_RESOLVE_AHEAD`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// `0`: no workers. The loader resolves every key itself.
    Off,
    /// The default: the workers resolve while the loader runs.
    On,
    /// `force`: the workers resolve every key before the loader starts, so
    /// the loader finds an answer for each key of the previous load (tests).
    Force,
}

thread_local! {
    /// `set_mode` on this thread.
    static MODE: Cell<Option<Mode>> = const { Cell::new(None) };
    /// The counts of the last resolve-ahead load on this thread.
    static LAST_STATS: Cell<Option<LoadStats>> = const { Cell::new(None) };
}

/// Sets the mode of the program loads on this thread, in place of
/// `GOPORT_RESOLVE_AHEAD` (`None`: the variable again). For tests.
pub fn set_mode(mode: Option<Mode>) {
    MODE.with(|m| m.set(mode));
}

/// The mode of a program load on this thread.
#[must_use]
pub fn mode() -> Mode {
    static ENV: std::sync::OnceLock<Mode> = std::sync::OnceLock::new();
    MODE.with(Cell::get).unwrap_or_else(|| {
        *ENV.get_or_init(|| match std::env::var("GOPORT_RESOLVE_AHEAD").as_deref() {
            Ok("0") => Mode::Off,
            Ok("force") => Mode::Force,
            _ => Mode::On,
        })
    })
}

/// The counts of one resolve-ahead load.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LoadStats {
    /// Keys of the previous load that the workers had.
    pub keys: usize,
    /// Keys that this load resolved or took.
    pub new_keys: usize,
    pub loader: AheadStats,
}

/// The counts of the last resolve-ahead load on this thread. For tests.
#[must_use]
pub fn last_stats() -> Option<LoadStats> {
    LAST_STATS.with(Cell::get)
}

/// The workers' view of a host's file system: the OS file system with the
/// open files of the host over it, as the language server's overlay file
/// system shows it (project/overlayfs.rs).
pub struct WorkerView {
    /// `current_directory` and `use_case_sensitive_file_names` make the
    /// paths, as the host's `to_path`.
    pub current_directory: String,
    pub use_case_sensitive_file_names: bool,
    /// The paths of the open files.
    pub open_files: FxHashSet<Path>,
    /// The paths of the directories that have open files in them.
    pub open_directories: FxHashSet<Path>,
}

/// A compiler host's part in resolve ahead
/// (`CompilerHost::resolve_ahead`).
pub struct ResolveAheadHost {
    /// The keys of the host's previous program load, in its order. `None`:
    /// no workers; the load only records its keys.
    pub previous_keys: Option<Arc<[ModuleResolutionCacheKey]>>,
    pub view: WorkerView,
    /// Checks the calls of a worker answer on the host's file system and
    /// replays their side effects (`AheadLink::accept`).
    pub accept: Rc<dyn Fn(&ModuleResolutionCacheKey, &ResolvedModule, &[AheadCall]) -> bool>,
    /// Keeps the keys of this load for the next load.
    pub keep_keys: Box<dyn FnOnce(Arc<[ModuleResolutionCacheKey]>)>,
    /// Debug builds: makes a new tracking view of the host's file system,
    /// to check that the calls of each taken answer list every side effect
    /// of its resolution (`debug_check_answer`).
    pub scratch: Option<Rc<dyn Fn() -> ScratchFs>>,
}

/// A view of a host's file system that tracks its seen files and missing
/// directories in new sets (`ResolveAheadHost::scratch`).
pub struct ScratchFs {
    pub fs: Rc<dyn Fs>,
    /// The seen files and missing directories of `fs` so far.
    pub tracked: Box<dyn Fn() -> (FxHashSet<Path>, FxHashSet<Path>)>,
    /// The host's `to_path`.
    pub to_path: Rc<dyn Fn(&str) -> Path>,
}

/// What a worker resolver needs: the loader resolver's options.
struct ResolverConfig {
    options: CompilerOptions,
    typings_location: String,
    project_name: String,
    extra_extensions: Vec<String>,
    /// The current directory of the loader resolver's host.
    current_directory: String,
}

impl ResolverConfig {
    /// A resolver with the loader resolver's options on `fs`.
    fn new_resolver(&self, fs: Rc<dyn Fs>) -> DefaultResolver {
        new_resolver(ResolverOptions {
            host: Some(Rc::new(AheadResolutionHost {
                fs,
                current_directory: self.current_directory.clone(),
            })),
            compiler_options: Some(Rc::new(self.options.clone())),
            typings_location: self.typings_location.clone(),
            project_name: self.project_name.clone(),
            extra_extensions: self.extra_extensions.clone(),
            package_json_cache: None,
        })
    }
}

/// Resolve ahead in one program load (`process_all_program_files`).
pub struct ResolveAhead {
    pool: Option<Pool>,
    keep_keys: Box<dyn FnOnce(Arc<[ModuleResolutionCacheKey]>)>,
    previous_keys: usize,
}

impl ResolveAhead {
    /// Starts resolve ahead for the load of `resolver`, the loader's
    /// resolver, with `host`. The caller checked the conditions of the load
    /// (`process_all_program_files`).
    pub fn start(host: ResolveAheadHost, resolver: &DefaultResolver) -> Self {
        let config = Arc::new(ResolverConfig {
            options: resolver.compiler_options.as_ref().clone(),
            typings_location: resolver.typings_location.clone(),
            project_name: resolver.project_name.clone(),
            extra_extensions: resolver.extra_extensions.clone(),
            current_directory: resolver.host.get_current_directory().to_string(),
        });
        let threads = worker_count();
        let previous_keys = host.previous_keys.as_ref().map_or(0, |keys| keys.len());
        let pool = host
            .previous_keys
            .filter(|keys| !keys.is_empty() && threads > 0)
            .map(|keys| Pool::start(keys, host.view, config.clone(), threads));
        let accept = match host.scratch.filter(|_| cfg!(debug_assertions)) {
            None => host.accept,
            Some(scratch) => {
                let accept = host.accept;
                Rc::new(
                    move |key: &ModuleResolutionCacheKey,
                          value: &ResolvedModule,
                          calls: &[AheadCall]| {
                        let accepted = accept(key, value, calls);
                        if accepted {
                            debug_check_answer(&config, &scratch(), key, value, calls);
                        }
                        accepted
                    },
                )
                    as Rc<dyn Fn(&ModuleResolutionCacheKey, &ResolvedModule, &[AheadCall]) -> bool>
            }
        };
        *resolver.caches.ahead.borrow_mut() = Some(AheadLink {
            answers: pool.as_ref().map(|pool| pool.shared.answers.clone()),
            accept,
            keys: RefCell::new(Vec::new()),
            stats: Cell::new(AheadStats::default()),
        });
        if mode() == Mode::Force
            && let Some(pool) = &pool
        {
            pool.wait();
        }
        ResolveAhead {
            pool,
            keep_keys: host.keep_keys,
            previous_keys,
        }
    }

    /// Ends resolve ahead after the load of `resolver`: stops the workers,
    /// unlinks `resolver` from their answers and gives the keys of the
    /// load to the host. The answers and the workers' caches are freed
    /// later (`drop_later`).
    pub fn finish(self, resolver: &DefaultResolver) {
        let ResolveAhead {
            pool,
            keep_keys,
            previous_keys,
        } = self;
        if let Some(pool) = &pool {
            pool.stop();
        }
        let Some(link) = resolver.caches.ahead.borrow_mut().take() else {
            return;
        };
        let keys: Arc<[ModuleResolutionCacheKey]> = link.keys.into_inner().into();
        let stats = LoadStats {
            keys: previous_keys,
            new_keys: keys.len(),
            loader: link.stats.get(),
        };
        LAST_STATS.with(|last| last.set(Some(stats)));
        print_stats(&stats);
        keep_keys(keys);
        if let Some(pool) = pool {
            crate::gostd::local::drop_later(Box::new(pool));
        }
    }
}

/// Prints the counts of a load when `GOPORT_RESOLVE_AHEAD_STATS` is set:
/// to stderr for `1`, else appended to the file that it names.
fn print_stats(stats: &LoadStats) {
    use std::io::Write;
    static TO: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    let Some(to) = TO.get_or_init(|| std::env::var("GOPORT_RESOLVE_AHEAD_STATS").ok()) else {
        return;
    };
    let line = format!("resolve-ahead: {stats:?}");
    if to == "1" {
        eprintln!("{line}");
    } else if let Ok(mut file) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(to)
    {
        let _ = writeln!(file, "{line}");
    }
}

/// The number of workers: the parse threads of a program that is not
/// large, less the loading thread (`GOPORT_RESOLVE_AHEAD_THREADS` sets it).
fn worker_count() -> usize {
    std::env::var("GOPORT_RESOLVE_AHEAD_THREADS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or_else(|| {
            crate::program::ThreadBudget::current()
                .parse_threads(false)
                .saturating_sub(1)
        })
}

/// The workers of one load. Dropping it stops them.
struct Pool {
    shared: Arc<PoolShared>,
    threads: RefCell<Vec<std::thread::JoinHandle<()>>>,
}

/// What the workers of one load share.
struct PoolShared {
    keys: Arc<[ModuleResolutionCacheKey]>,
    /// The index of the next key to resolve.
    next: AtomicUsize,
    closed: AtomicBool,
    answers: Arc<SharedResolutionCache>,
    view: WorkerView,
    /// The OS lookups of the workers, as the host's per-snapshot cache
    /// keeps the loader's.
    stats: StatCache,
    config: Arc<ResolverConfig>,
}

impl Pool {
    fn start(
        keys: Arc<[ModuleResolutionCacheKey]>,
        view: WorkerView,
        config: Arc<ResolverConfig>,
        threads: usize,
    ) -> Self {
        let shared = Arc::new(PoolShared {
            keys,
            next: AtomicUsize::new(0),
            closed: AtomicBool::new(false),
            answers: Arc::new(SharedResolutionCache::default()),
            view,
            stats: StatCache::default(),
            config,
        });
        let mut handles = Vec::with_capacity(threads);
        for _ in 0..threads {
            let shared = shared.clone();
            // A worker that cannot start only makes fewer answers.
            let spawned = std::thread::Builder::new()
                .name("goport-resolve".to_string())
                .stack_size(crate::gostd::stack::max_stack_size())
                .spawn(move || run_worker(&shared));
            handles.extend(spawned.ok());
        }
        Pool {
            shared,
            threads: RefCell::new(handles),
        }
    }

    /// Waits until the workers resolved every key.
    fn wait(&self) {
        for thread in self.threads.borrow_mut().drain(..) {
            let _ = thread.join();
        }
    }

    /// Stops the workers after their current key and waits for them.
    fn stop(&self) {
        self.shared.closed.store(true, Ordering::Relaxed);
        self.wait();
    }
}

impl Drop for Pool {
    fn drop(&mut self) {
        self.stop();
    }
}

/// A worker: resolves the next key until none is left or the pool stops.
/// A resolution that panics (a Go panic) panics on the loader too when it
/// resolves the same key; the worker only stops.
fn run_worker(shared: &Arc<PoolShared>) {
    let view = &shared.view;
    begin_ahead_thread(&view.current_directory, view.use_case_sensitive_file_names);
    let fs: Rc<dyn Fs> = Rc::new(AheadFs {
        os: wrap_fs(osvfs_fs()),
        shared: shared.clone(),
    });
    let mut resolver = shared.config.new_resolver(fs);
    resolver.caches.shared = Some(SharedResolutionLink {
        cache: shared.answers.clone(),
        publish: true,
    });
    let _ = crate::core::go_recover(|| {
        while !shared.closed.load(Ordering::Relaxed) {
            let index = shared.next.fetch_add(1, Ordering::Relaxed);
            let Some(key) = shared.keys.get(index) else {
                break;
            };
            // A redirected key needs the project reference; the loader
            // resolves it.
            if !key.redirect_config_name.is_empty() {
                continue;
            }
            let _ = resolver.resolve_module_name_from_directory(
                &key.module_name,
                &key.containing_directory,
                key.resolution_mode,
            );
        }
    });
    end_ahead_thread();
}

/// Go `module.ResolutionHost` of a worker resolver.
struct AheadResolutionHost {
    fs: Rc<dyn Fs>,
    current_directory: String,
}

impl ResolutionHost for AheadResolutionHost {
    fn fs(&self) -> &dyn Fs {
        &*self.fs
    }

    fn get_current_directory(&self) -> &str {
        &self.current_directory
    }
}

/// A worker's file system: the OS file system of its thread with the open
/// files of the host over it (project/overlayfs.rs `OverlayFS`), and the
/// workers' stat cache. It logs each call (`note_ahead_call`). A call that
/// the loader cannot check makes the answer unshareable.
struct AheadFs {
    os: Rc<dyn Fs>,
    shared: Arc<PoolShared>,
}

impl AheadFs {
    fn path(&self, name: &str) -> Path {
        let view = &self.shared.view;
        to_path(
            name,
            &view.current_directory,
            view.use_case_sensitive_file_names,
        )
    }
}

impl Fs for AheadFs {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.os.use_case_sensitive_file_names()
    }

    // Go: project/overlayfs.go:276 overlayFS.FileExists
    fn file_exists(&self, path: &str) -> bool {
        let canonical = self.path(path);
        let view = &self.shared.view;
        let exists = view.open_files.contains(&canonical)
            || !view.open_directories.contains(&canonical)
                && self
                    .shared
                    .stats
                    .file_exists(path, || self.os.file_exists(path));
        note_ahead_call(AheadCall::FileExists {
            path: canonical,
            exists,
        });
        exists
    }

    // Go: project/overlayfs.go:285 overlayFS.ReadFile
    fn read_file(&self, path: &str) -> (String, bool) {
        let canonical = self.path(path);
        let view = &self.shared.view;
        if view.open_files.contains(&canonical) {
            // The workers do not have the text of an open file.
            note_ahead_unshareable(Some(path));
            return (String::new(), false);
        }
        let (text, ok) = if view.open_directories.contains(&canonical) {
            (String::new(), false)
        } else {
            self.os.read_file(path)
        };
        note_ahead_read(path, ok.then(|| xxh3_128(text.as_bytes())));
        (text, ok)
    }

    fn write_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        note_ahead_unshareable(None);
        self.os.write_file(path, data)
    }

    fn append_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        note_ahead_unshareable(None);
        self.os.append_file(path, data)
    }

    fn remove(&self, path: &str) -> Result<(), FsError> {
        note_ahead_unshareable(None);
        self.os.remove(path)
    }

    fn chtimes(
        &self,
        path: &str,
        a_time: Option<std::time::SystemTime>,
        m_time: Option<std::time::SystemTime>,
    ) -> Result<(), FsError> {
        note_ahead_unshareable(None);
        self.os.chtimes(path, a_time, m_time)
    }

    // Go: project/overlayfs.go:302 overlayFS.DirectoryExists
    fn directory_exists(&self, path: &str) -> bool {
        let canonical = self.path(path);
        let view = &self.shared.view;
        let exists = view.open_directories.contains(&canonical)
            || !view.open_files.contains(&canonical)
                && self
                    .shared
                    .stats
                    .directory_exists(path, || self.os.directory_exists(path));
        if !exists {
            note_ahead_call(AheadCall::MissingDirectory { path: canonical });
        }
        exists
    }

    // The loader's directory entries merge cached and open files
    // (project/snapshotfs.rs `GetAccessibleEntries`).
    fn get_accessible_entries(&self, path: &str) -> Entries {
        note_ahead_unshareable(None);
        self.os.get_accessible_entries(path)
    }

    fn stat(&self, path: &str) -> Option<FileInfo> {
        note_ahead_unshareable(None);
        self.os.stat(path)
    }

    // Go: project/overlayfs.go:361 overlayFS.Realpath
    fn realpath(&self, path: &str) -> String {
        self.shared.stats.realpath(path, || self.os.realpath(path))
    }
}

/// Debug builds: checks a taken answer for `key` against a resolution of
/// the key by a new resolver on a new tracking view of the host's file
/// system. The answer must be the same, and the calls must list exactly the
/// files that the view saw and the directories that it found missing. A
/// new resolver reads every package.json itself, so this also checks that
/// each answer lists the calls of the package.json cache entries it read.
fn debug_check_answer(
    config: &ResolverConfig,
    scratch: &ScratchFs,
    key: &ModuleResolutionCacheKey,
    value: &ResolvedModule,
    calls: &[AheadCall],
) {
    let resolver = config.new_resolver(scratch.fs.clone());
    let (own, _, _) = resolver.resolve_module_name_from_directory(
        &key.module_name,
        &key.containing_directory,
        key.resolution_mode,
    );
    assert_eq!(
        describe(&own),
        describe(value),
        "resolve ahead: the answer for {key:?} differs"
    );
    let mut seen = FxHashSet::default();
    let mut missing = FxHashSet::default();
    for call in calls {
        match call {
            AheadCall::FileExists { path, .. } => {
                seen.insert(path.clone());
            }
            AheadCall::MissingDirectory { path } => {
                missing.insert(path.clone());
            }
            AheadCall::Read { file_name, .. } => {
                seen.insert((scratch.to_path)(file_name));
            }
        }
    }
    let (own_seen, own_missing) = (scratch.tracked)();
    assert!(
        own_seen == seen && own_missing == missing,
        "resolve ahead: the calls for {key:?} differ: seen {:?}, logged {:?}; missing {:?}, logged {:?}",
        sorted(&own_seen),
        sorted(&seen),
        sorted(&own_missing),
        sorted(&missing),
    );
}

fn sorted(paths: &FxHashSet<Path>) -> Vec<&str> {
    let mut paths: Vec<&str> = paths.iter().map(Path::as_str).collect();
    paths.sort_unstable();
    paths
}

/// The fields of a resolved module, for `debug_check_answer`.
fn describe(module: &ResolvedModule) -> String {
    format!(
        "{} {} {} {} {} {:?} {} {} {:?}",
        module.resolved_file_name,
        module.original_path,
        module.extension,
        module.resolved_using_ts_extension,
        module.resolved_using_extra_extensions,
        module.package_id,
        module.is_external_library_import,
        module.alternate_result,
        module.resolution_diagnostics,
    )
}
