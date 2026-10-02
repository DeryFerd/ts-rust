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
use std::sync::{Condvar, Mutex};
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
    pub previous_keys: Option<Arc<KeyList>>,
    pub view: WorkerView,
    /// Checks the calls of a worker answer on the host's file system and
    /// replays their side effects (`AheadLink::accept`).
    pub accept: AheadAccept,
    /// Keeps the keys of this load for the next load.
    pub keep_keys: Box<dyn FnOnce(Arc<KeyList>)>,
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
    /// A resolver with the loader resolver's options on `fs`, with
    /// `package_json_cache` or a new one.
    fn new_resolver(
        &self,
        fs: Rc<dyn Fs>,
        package_json_cache: Option<Rc<InfoCache>>,
    ) -> DefaultResolver {
        new_resolver(ResolverOptions {
            host: Some(Rc::new(AheadResolutionHost {
                fs,
                current_directory: self.current_directory.clone(),
            })),
            compiler_options: Some(Rc::new(self.options.clone())),
            typings_location: self.typings_location.clone(),
            project_name: self.project_name.clone(),
            extra_extensions: self.extra_extensions.clone(),
            package_json_cache,
        })
    }
}

/// Resolve ahead in one program load (`process_all_program_files`).
pub struct ResolveAhead {
    /// The workers' job of this load, until `finish`.
    job: Option<Arc<Job>>,
    keep_keys: Option<Box<dyn FnOnce(Arc<KeyList>)>>,
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
        let previous_keys = host.previous_keys.as_ref().map_or(0, |keys| keys.len());
        let keys = host
            .previous_keys
            .as_deref()
            .map(KeyList::with_capacity_of)
            .unwrap_or_default();
        let job = host
            .previous_keys
            .filter(|keys| !keys.is_empty())
            .and_then(|keys| {
                let workers = Workers::get()?;
                let fresh = workers.fresh.swap(false, Ordering::Relaxed);
                workers.post(Job {
                    queue: Arc::new(AheadQueue::new(keys)),
                    fresh_package_jsons: fresh,
                    known_files: if fresh {
                        Arc::default()
                    } else {
                        workers.known_files()
                    },
                    closed: AtomicBool::new(false),
                    left: AtomicUsize::new(0),
                    answers: Arc::new(SharedResolutionCache::default()),
                    view: host.view,
                    stats: WorkerStats::default(),
                    config: config.clone(),
                })
            });
        let accept = match host.scratch.filter(|_| cfg!(debug_assertions)) {
            None => host.accept,
            Some(scratch) => {
                let accept = host.accept;
                Rc::new(
                    move |key: ModuleKeyParts<'_>, value: &ResolvedModule, calls: &[AheadCall]| {
                        let accepted = accept(key, value, calls);
                        if accepted {
                            debug_check_answer(&config, &scratch(), key, value, calls);
                        }
                        accepted
                    },
                ) as AheadAccept
            }
        };
        *resolver.caches.ahead.borrow_mut() = Some(AheadLink {
            answers: job.as_ref().map(|job| job.answers.clone()),
            accept,
            keys: RefCell::new(keys),
            queue: job.as_ref().map(|job| job.queue.clone()),
            cursor: Cell::new(0),
            stats: Cell::new(AheadStats::default()),
        });
        if mode() == Mode::Force
            && let Some((job, workers)) = job.as_ref().zip(Workers::get())
        {
            workers.wait_left(job);
        }
        ResolveAhead {
            job,
            keep_keys: Some(host.keep_keys),
            previous_keys,
        }
    }

    /// Ends resolve ahead after the load of `resolver`: stops the workers,
    /// unlinks `resolver` from their answers and gives the keys of the
    /// load to the host. The workers free the answers and their caches.
    pub fn finish(mut self, resolver: &DefaultResolver) {
        let link = resolver.caches.ahead.borrow_mut().take();
        let Some(mut link) = link else {
            self.end_job(None, true);
            return;
        };
        // The workers free the answers and the queue with the job.
        let rejected = link.stats.get().rejected > 0;
        self.end_job(
            Some(Box::new((link.answers.take(), link.queue.take()))),
            rejected,
        );
        let Some(keep_keys) = self.keep_keys.take() else {
            return;
        };
        let keys = Arc::new(link.keys.into_inner());
        let stats = LoadStats {
            keys: self.previous_keys,
            new_keys: keys.len(),
            loader: link.stats.get(),
        };
        // A rejected answer can come from a kept package.json parse or a
        // known file that changed: the workers of the next load start with
        // neither.
        if stats.loader.rejected > 0
            && let Some(workers) = Workers::get()
        {
            workers.fresh.store(true, Ordering::Relaxed);
        }
        LAST_STATS.with(|last| last.set(Some(stats)));
        print_stats(&stats);
        keep_keys(keys);
    }

    /// Stops the workers of this load and gives its job and `shared`, the
    /// loader's links to it, to them to free. Unless the loader `rejected`
    /// an answer, the workers keep the files that the job's answers found
    /// for the next job (`Workers::known_files`).
    fn end_job(&mut self, shared: Option<Box<dyn Send>>, rejected: bool) {
        let Some(job) = self.job.take() else {
            return;
        };
        if let Some(workers) = Workers::get() {
            workers.end(&job);
            workers.free(EndedJob {
                job,
                shared,
                keep_known_files: !rejected,
            });
        }
    }
}

impl Drop for ResolveAhead {
    /// A load that ends with a panic stops its workers too.
    fn drop(&mut self) {
        self.end_job(None, true);
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

/// The workers of the process, once a load started them
/// (`Workers::get`).
static WORKERS: std::sync::OnceLock<Option<&'static Workers>> = std::sync::OnceLock::new();

/// Drops `value` on a resolve-ahead worker when a load started the workers
/// (they wait between loads), else here. The language server's loads take
/// most answers from the workers; the workers then also free a released
/// program's resolutions (`module::Caches::release`), so the dispatch
/// thread does not before its next request.
// PORT: not in Go (Go's garbage collector frees in the background).
pub fn drop_on_worker(value: Box<dyn Send>) {
    match WORKERS.get().copied().flatten() {
        Some(workers) => {
            lock_state(workers).drops.push(value);
            workers.wake.notify_one();
        }
        None => drop(value),
    }
}

/// The resolve-ahead workers of the process. They start at the first load
/// that resolves ahead and stay: between loads they wait on `wake` and
/// use no CPU. One load at a time has them (`post`). After a load they free
/// its data (`free`), which they allocated, so the dispatch thread does not
/// free it before its next request.
struct Workers {
    state: Mutex<WorkerState>,
    /// Wakes the workers for a new job or for data to free.
    wake: Condvar,
    /// Wakes a loader that waits for the workers to leave its job
    /// (`wait_left`).
    left: Condvar,
    /// The workers that started.
    count: AtomicUsize,
    /// The next job drops what the workers keep: the package.json parses
    /// (`KeptPackageJsons`) and the known files.
    fresh: AtomicBool,
    /// The files that the answers of earlier jobs found, since the last
    /// rejected answer (`EndedJob::free`): a worker answers `file_exists`
    /// for them with no OS call, and the loader checks those answers
    /// (`AheadCall::FileExists`).
    known_files: Mutex<Arc<FxHashSet<Path>>>,
}

#[derive(Default)]
struct WorkerState {
    /// The job of the load that has the workers now.
    job: Option<Arc<Job>>,
    /// Counts the posted jobs, so that a worker runs each job once.
    generation: u64,
    /// The jobs of ended loads, for the workers to free.
    ended: Vec<EndedJob>,
    /// Other values for the workers to free (`drop_on_worker`).
    drops: Vec<Box<dyn Send>>,
}

/// What a worker does next.
enum Task {
    Run(Arc<Job>),
    Free(EndedJob),
    Drop(Box<dyn Send>),
}

/// The job of an ended load and the loader's links to it, which a worker
/// frees (`Workers::free`).
struct EndedJob {
    job: Arc<Job>,
    shared: Option<Box<dyn Send>>,
    /// Keep the job's known files and the files that its answers found
    /// (`Workers::known_files`).
    keep_known_files: bool,
}

impl EndedJob {
    /// Frees the job on this worker, after it keeps the files that the
    /// job's answers found: the known files of the next job.
    fn free(self, workers: &Workers) {
        let EndedJob {
            job,
            shared,
            keep_known_files,
        } = self;
        drop(shared);
        // The files of the job's known set and the files that its answers
        // found. A file that the answers did not use stays known: the loader
        // checks each known answer, and a rejection starts a new set
        // (`Workers::fresh`). Most loads find no new file, and the set is
        // then kept as it is.
        if keep_known_files {
            let mut more: Option<FxHashSet<Path>> = None;
            job.answers.for_each_module(|answer| {
                AheadCall::each(answer.ahead.as_deref().unwrap_or_default(), &mut |call| {
                    if let AheadCall::FileExists {
                        path, exists: true, ..
                    } = call
                        && !job.known_files.contains(path)
                        && !job.view.open_files.contains(path)
                        && !more.as_ref().is_some_and(|more| more.contains(path))
                    {
                        more.get_or_insert_with(|| (*job.known_files).clone())
                            .insert(path.clone());
                    }
                });
            });
            let known = more.map_or_else(|| job.known_files.clone(), Arc::new);
            *workers
                .known_files
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner) = known;
        }
        drop(job);
    }
}

fn lock_state(workers: &Workers) -> std::sync::MutexGuard<'_, WorkerState> {
    workers
        .state
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

impl Workers {
    /// The workers, started at the first call. `None` when none could
    /// start or the count is 0.
    fn get() -> Option<&'static Workers> {
        *WORKERS.get_or_init(|| {
            let count = worker_count();
            if count == 0 {
                return None;
            }
            let workers: &'static Workers = Box::leak(Box::new(Workers {
                state: Mutex::default(),
                wake: Condvar::new(),
                left: Condvar::new(),
                count: AtomicUsize::new(0),
                fresh: AtomicBool::new(false),
                known_files: Mutex::default(),
            }));
            for _ in 0..count {
                // A worker that cannot start only makes fewer answers.
                let started = std::thread::Builder::new()
                    .name("goport-resolve".to_string())
                    .stack_size(crate::gostd::stack::max_stack_size())
                    .spawn(move || run_worker(workers));
                if started.is_ok() {
                    workers.count.fetch_add(1, Ordering::Relaxed);
                }
            }
            (workers.count.load(Ordering::Relaxed) > 0).then_some(workers)
        })
    }

    /// Gives `job` to the workers. `None` when another load has them now
    /// (a load on another thread): this load then resolves every key
    /// itself.
    fn post(&self, job: Job) -> Option<Arc<Job>> {
        let mut state = lock_state(self);
        if state.job.is_some() {
            return None;
        }
        let job = Arc::new(job);
        state.job = Some(job.clone());
        state.generation += 1;
        drop(state);
        self.wake.notify_all();
        Some(job)
    }

    /// Stops `job`: each worker ends it after its current key.
    fn end(&self, job: &Arc<Job>) {
        job.closed.store(true, Ordering::Relaxed);
        let mut state = lock_state(self);
        if state
            .job
            .as_ref()
            .is_some_and(|posted| Arc::ptr_eq(posted, job))
        {
            state.job = None;
        }
    }

    /// Gives `ended` to a worker to free.
    fn free(&self, ended: EndedJob) {
        lock_state(self).ended.push(ended);
        self.wake.notify_one();
    }

    /// The files that the answers of the last ended job found.
    fn known_files(&self) -> Arc<FxHashSet<Path>> {
        self.known_files
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone()
    }

    /// Waits until every worker has left `job` (`Mode::Force`).
    fn wait_left(&self, job: &Job) {
        let count = self.count.load(Ordering::Relaxed);
        let mut state = lock_state(self);
        while job.left.load(Ordering::Acquire) < count {
            state = self
                .left
                .wait(state)
                .unwrap_or_else(std::sync::PoisonError::into_inner);
        }
    }
}

/// A worker: runs each posted job once and frees the data of ended loads.
/// A new job goes before the data to free.
fn run_worker(workers: &'static Workers) {
    let mut ran = 0;
    loop {
        let task = {
            let mut state = lock_state(workers);
            loop {
                if state.generation != ran
                    && let Some(job) = &state.job
                {
                    ran = state.generation;
                    break Task::Run(job.clone());
                }
                if let Some(ended) = state.ended.pop() {
                    break Task::Free(ended);
                }
                if let Some(value) = state.drops.pop() {
                    break Task::Drop(value);
                }
                state = workers
                    .wake
                    .wait(state)
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
            }
        };
        match task {
            Task::Free(ended) => ended.free(workers),
            Task::Drop(value) => drop(value),
            Task::Run(job) => {
                run_job(&job);
                job.left.fetch_add(1, Ordering::Release);
                drop(job);
                let _state = lock_state(workers);
                workers.left.notify_all();
            }
        }
    }
}

/// The workers' part of one load.
struct Job {
    /// The keys of the previous load, in its order.
    queue: Arc<AheadQueue>,
    /// The workers drop the package.json parses that they keep.
    fresh_package_jsons: bool,
    /// The files that earlier jobs found (`Workers::known_files`).
    known_files: Arc<FxHashSet<Path>>,
    closed: AtomicBool,
    /// The workers that left this job.
    left: AtomicUsize,
    answers: Arc<SharedResolutionCache>,
    view: WorkerView,
    /// The OS lookups of the workers, as the host's per-snapshot cache
    /// keeps the loader's.
    stats: WorkerStats,
    config: Arc<ResolverConfig>,
}

/// A worker's part of `job`: resolves the next key until none is left or
/// the job ends. A resolution that panics (a Go panic) panics on the loader
/// too when it resolves the same key; the worker ends that key with no
/// answer and leaves the job. The worker's resolver and its caches are
/// freed here, on the worker.
fn run_job(job: &Arc<Job>) {
    let view = &job.view;
    let (package_jsons, reads, kept) = KeptPackageJsons::take(job);
    let fs = Rc::new(AheadFs {
        os: wrap_fs(osvfs_fs()),
        job: job.clone(),
    });
    let directory_exists = {
        let fs = fs.clone();
        Rc::new(move |path: &str| fs.directory_exists_unlogged(path)) as Rc<dyn Fn(&str) -> bool>
    };
    begin_ahead_thread(
        &view.current_directory,
        view.use_case_sensitive_file_names,
        reads,
        kept,
        directory_exists,
    );
    let fs: Rc<dyn Fs> = fs;
    let mut resolver = job.config.new_resolver(fs, Some(package_jsons.clone()));
    resolver.caches.shared = Some(SharedResolutionLink {
        cache: job.answers.clone(),
        publish: true,
    });
    let current = Cell::new(None);
    let _ = crate::core::go_recover(|| {
        while !job.closed.load(Ordering::Relaxed) {
            let Some((index, (containing_directory, module_name, mode))) = job.queue.take_next()
            else {
                break;
            };
            current.set(Some(index));
            let _ = resolver.resolve_module_name_from_directory(
                module_name,
                containing_directory,
                mode,
            );
            job.queue.done(index);
            current.set(None);
        }
    });
    if let Some(index) = current.get() {
        job.queue.done(index);
    }
    let reads = end_ahead_thread();
    drop(resolver);
    KEPT.with(|kept| {
        *kept.borrow_mut() = Some(KeptPackageJsons {
            current_directory: view.current_directory.clone(),
            use_case_sensitive_file_names: view.use_case_sensitive_file_names,
            cache: package_jsons,
            reads,
        });
    });
}

thread_local! {
    /// A worker's package.json cache from its last job.
    static KEPT: RefCell<Option<KeptPackageJsons>> = const { RefCell::new(None) };
}

/// A worker's package.json cache, kept from job to job, so a worker does
/// not parse the same package.json files at every load. The loader checks
/// each logged read by the hash of its text on the snapshot file system,
/// so it never takes an answer from a parse whose file changed: it
/// rejects the answer, and the next job starts with no kept parse
/// (`Workers::fresh`). Only parses of files that the worker
/// read are kept: a directory or package.json that was missing can be
/// there now, and the loader does not check that.
// PORT: not in Go (perf).
struct KeptPackageJsons {
    current_directory: String,
    use_case_sensitive_file_names: bool,
    cache: Rc<InfoCache>,
    /// The hash of each file that the worker read, by name
    /// (`begin_ahead_thread`).
    reads: FxHashMap<String, Option<u128>>,
}

impl KeptPackageJsons {
    /// The package.json cache, read hashes and kept file names for `job`
    /// on this worker: the kept entries of files that the worker read, or
    /// none.
    fn take(
        job: &Job,
    ) -> (
        Rc<InfoCache>,
        FxHashMap<String, Option<u128>>,
        FxHashSet<String>,
    ) {
        let view = &job.view;
        let cache = Rc::new(new_info_cache(
            &view.current_directory,
            view.use_case_sensitive_file_names,
        ));
        let mut reads = FxHashMap::default();
        let mut kept_files = FxHashSet::default();
        let kept = KEPT.with(|kept| kept.borrow_mut().take()).filter(|kept| {
            !job.fresh_package_jsons
                && kept.current_directory == view.current_directory
                && kept.use_case_sensitive_file_names == view.use_case_sensitive_file_names
        });
        if let Some(mut kept) = kept {
            kept.cache.range(|_, entry| {
                if entry.directory_exists && entry.contents.is_some() {
                    let file_name = combine_paths(&entry.package_directory, &["package.json"]);
                    if let Some((file_name, Some(hash))) = kept.reads.remove_entry(&file_name) {
                        cache.set(&file_name, entry.clone());
                        kept_files.insert(file_name.clone());
                        reads.insert(file_name, Some(hash));
                    }
                }
                true
            });
        }
        (cache, reads, kept_files)
    }
}

/// The OS lookups of a job's workers (`Job::stats`), as `StatCache`
/// (files_parser.rs) keeps them, in shards by path, so the workers seldom
/// wait for each other's lock.
#[derive(Default)]
struct WorkerStats {
    file_exists: [Mutex<FxHashMap<String, bool>>; STAT_SHARDS],
    directory_exists: [Mutex<FxHashMap<String, bool>>; STAT_SHARDS],
    realpath: [Mutex<FxHashMap<String, String>>; STAT_SHARDS],
}

const STAT_SHARDS: usize = 16;

impl WorkerStats {
    fn file_exists(&self, path: &str, load: impl FnOnce() -> bool) -> bool {
        cached(&self.file_exists, path, load)
    }

    fn directory_exists(&self, path: &str, load: impl FnOnce() -> bool) -> bool {
        cached(&self.directory_exists, path, load)
    }

    fn realpath(&self, path: &str, load: impl FnOnce() -> String) -> String {
        cached(&self.realpath, path, load)
    }
}

/// The cached value of `path` in its shard, or `load()` stored as it. The
/// lock is not held while `load` runs; the first stored value wins.
fn cached<V: Clone>(
    shards: &[Mutex<FxHashMap<String, V>>; STAT_SHARDS],
    path: &str,
    load: impl FnOnce() -> V,
) -> V {
    use std::hash::BuildHasher;
    let hash = rustc_hash::FxBuildHasher.hash_one(path);
    let shard = &shards[(hash >> 32) as usize % STAT_SHARDS];
    let lock = || {
        shard
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    };
    if let Some(value) = lock().get(path) {
        return value.clone();
    }
    let value = load();
    lock().entry(path.to_string()).or_insert(value).clone()
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
    job: Arc<Job>,
}

impl AheadFs {
    /// `directory_exists` with no log: whether a kept package.json cache
    /// entry's directory is still there (`begin_ahead_thread`).
    fn directory_exists_unlogged(&self, path: &str) -> bool {
        self.directory_lookup(path).0
    }

    /// Whether directory `path` exists, as `overlayFS.DirectoryExists`
    /// answers it, and its path.
    fn directory_lookup(&self, path: &str) -> (bool, Path) {
        let canonical = self.path(path);
        let view = &self.job.view;
        let exists = view.open_directories.contains(&canonical)
            || !view.open_files.contains(&canonical)
                && self
                    .job
                    .stats
                    .directory_exists(path, || self.os.directory_exists(path));
        (exists, canonical)
    }

    fn path(&self, name: &str) -> Path {
        let view = &self.job.view;
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
    // PORT: a file that earlier jobs found is known to exist with no OS
    // call; the loader checks that answer (`AheadCall::FileExists`).
    fn file_exists(&self, path: &str) -> bool {
        let canonical = self.path(path);
        let view = &self.job.view;
        let (exists, known) = if view.open_files.contains(&canonical) {
            (true, false)
        } else if view.open_directories.contains(&canonical) {
            (false, false)
        } else if self.job.known_files.contains(&canonical) {
            (true, true)
        } else {
            let exists = self
                .job
                .stats
                .file_exists(path, || self.os.file_exists(path));
            (exists, false)
        };
        note_ahead_call(AheadCall::FileExists {
            path: canonical,
            exists,
            known,
        });
        exists
    }

    // Go: project/overlayfs.go:285 overlayFS.ReadFile
    fn read_file(&self, path: &str) -> (String, bool) {
        let canonical = self.path(path);
        let view = &self.job.view;
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
        let (exists, canonical) = self.directory_lookup(path);
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
        self.job.stats.realpath(path, || self.os.realpath(path))
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
    key: ModuleKeyParts<'_>,
    value: &ResolvedModule,
    calls: &[AheadCall],
) {
    let (containing_directory, module_name, mode, _) = key;
    let resolver = config.new_resolver(scratch.fs.clone(), None);
    let (own, _, _) =
        resolver.resolve_module_name_from_directory(module_name, containing_directory, mode);
    assert_eq!(
        describe(&own),
        describe(value),
        "resolve ahead: the answer for {key:?} differs"
    );
    let mut seen = FxHashSet::default();
    let mut missing = FxHashSet::default();
    AheadCall::each(calls, &mut |call| match call {
        AheadCall::FileExists { path, .. } => {
            seen.insert(path.clone());
        }
        AheadCall::MissingDirectory { path } => {
            missing.insert(path.clone());
        }
        AheadCall::Read { file_name, .. } => {
            seen.insert((scratch.to_path)(file_name));
        }
        AheadCall::PackageJson(_) => {}
    });
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
