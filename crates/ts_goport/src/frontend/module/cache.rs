//! Port of module/cache.go.

use crate::frontend::prelude::*;
use std::cell::Cell;
use std::sync::Arc;

// Go: module/cache.go:9 ModeAwareCache
pub type ModeAwareCache<T> = FxHashMap<ModeAwareCacheKey, T>;

// Go: module/cache.go:11 moduleResolutionCacheKey
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ModuleResolutionCacheKey {
    pub containing_directory: String,
    pub module_name: String,
    pub resolution_mode: ResolutionMode,
    pub redirect_config_name: String,
}

/// The fields of a `ModuleResolutionCacheKey`: containing directory,
/// module name, resolution mode and redirect config name.
pub type ModuleKeyParts<'a> = (&'a str, &'a str, ResolutionMode, &'a str);

/// A module resolution cache key as its parts, so a lookup needs no new
/// key (`ModuleResolutionCache::get`).
// PORT: not in Go (perf). A Go key is a struct of string headers, which
// costs no allocation; a Rust key owns its strings.
pub trait ModuleKey {
    fn parts(&self) -> ModuleKeyParts<'_>;
}

impl ModuleKey for ModuleResolutionCacheKey {
    fn parts(&self) -> ModuleKeyParts<'_> {
        (
            &self.containing_directory,
            &self.module_name,
            self.resolution_mode,
            &self.redirect_config_name,
        )
    }
}

impl ModuleKey for ModuleKeyParts<'_> {
    fn parts(&self) -> ModuleKeyParts<'_> {
        *self
    }
}

impl<'a> std::borrow::Borrow<dyn ModuleKey + 'a> for ModuleResolutionCacheKey {
    fn borrow(&self) -> &(dyn ModuleKey + 'a) {
        self
    }
}

// The same hash as a derived one (the fields in order), so the map order
// does not change.
impl std::hash::Hash for ModuleResolutionCacheKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.parts().hash(state);
    }
}

impl std::hash::Hash for dyn ModuleKey + '_ {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.parts().hash(state);
    }
}

impl PartialEq for dyn ModuleKey + '_ {
    fn eq(&self, other: &Self) -> bool {
        self.parts() == other.parts()
    }
}

impl Eq for dyn ModuleKey + '_ {}

impl ModuleResolutionCacheKey {
    /// The key of `parts`.
    #[must_use]
    pub fn from_parts(parts: ModuleKeyParts<'_>) -> Self {
        let (containing_directory, module_name, resolution_mode, redirect_config_name) = parts;
        ModuleResolutionCacheKey {
            containing_directory: containing_directory.to_string(),
            module_name: module_name.to_string(),
            resolution_mode,
            redirect_config_name: redirect_config_name.to_string(),
        }
    }
}

// Go: module/cache.go:18 moduleResolutionCache
// PORT: Go `collections.SyncMap` is a plain map behind a `RefCell`, so the
// `DefaultResolver` methods can take `&self`. Cached Go pointers are `Arc`: parse
// workers share them (`SharedResolutionCache`), and checker threads read
// the program's resolutions with no copy (`GoSharedState`).
#[derive(Default)]
pub struct ModuleResolutionCache {
    pub cache: RefCell<FxHashMap<ModuleResolutionCacheKey, Arc<ResolvedModule>>>,
}

impl ModuleResolutionCache {
    // Go: module/cache.go:22 moduleResolutionCache.Get
    #[must_use]
    pub fn get(&self, key: &dyn ModuleKey) -> Option<Arc<ResolvedModule>> {
        self.cache.borrow().get(key).cloned()
    }

    // Go: module/cache.go:26 moduleResolutionCache.Set
    // PORT: Go `LoadOrStore`: the first stored value wins.
    pub fn set(&self, key: ModuleResolutionCacheKey, value: Arc<ResolvedModule>) {
        self.cache.borrow_mut().entry(key).or_insert(value);
    }
}

// Go: module/cache.go:30 typeRefDirectiveResolutionCacheKey
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct TypeRefDirectiveResolutionCacheKey {
    pub containing_directory: String,
    pub type_reference_name: String,
    pub resolution_mode: ResolutionMode,
    pub redirect_config_name: String,
    pub from_inferred_types_containing_file: bool,
}

// Go: module/cache.go:38 typeRefDirectiveResolutionCache
// PORT: see `ModuleResolutionCache`.
#[derive(Default)]
pub struct TypeRefDirectiveResolutionCache {
    pub cache:
        RefCell<FxHashMap<TypeRefDirectiveResolutionCacheKey, Rc<ResolvedTypeReferenceDirective>>>,
}

impl TypeRefDirectiveResolutionCache {
    // Go: module/cache.go:42 typeRefDirectiveResolutionCache.Get
    #[must_use]
    pub fn get(
        &self,
        key: &TypeRefDirectiveResolutionCacheKey,
    ) -> Option<Rc<ResolvedTypeReferenceDirective>> {
        self.cache.borrow().get(key).cloned()
    }

    // Go: module/cache.go:46 typeRefDirectiveResolutionCache.Set
    // PORT: Go `Store`: the last stored value wins.
    pub fn set(
        &self,
        key: TypeRefDirectiveResolutionCacheKey,
        value: Rc<ResolvedTypeReferenceDirective>,
    ) {
        self.cache.borrow_mut().insert(key, value);
    }
}

// Go: module/cache.go:50 parsedPatternsCache
// PORT: Go keys the `SyncMap` by the `*OrderedMap` of `paths`, and the key
// keeps that map alive. The Rust `paths` map is a field of the
// `CompilerOptions`, so the key is the address of that field (0 for a nil
// map), and the entry holds the options `Rc` that owns it.
#[derive(Default)]
pub struct ParsedPatternsCache {
    cache: RefCell<FxHashMap<usize, (Rc<CompilerOptions>, Rc<ParsedPatterns>)>>,
}

impl ParsedPatternsCache {
    // Go: module/cache.go:54 parsedPatternsCache.Get
    // PORT: Go takes `compilerOptions.Paths`; this takes the options that
    // own it (see the type).
    pub fn get(&self, compiler_options: &Rc<CompilerOptions>) -> Rc<ParsedPatterns> {
        let path_mappings = compiler_options.paths.as_ref();
        let key = path_mappings.map_or(0, |path_mappings| {
            std::ptr::from_ref(path_mappings) as usize
        });
        if let Some((_, patterns)) = self.cache.borrow().get(&key) {
            return patterns.clone();
        }
        let patterns = Rc::new(try_parse_patterns(path_mappings));
        self.cache
            .borrow_mut()
            .entry(key)
            .or_insert_with(|| (compiler_options.clone(), patterns))
            .1
            .clone()
    }

    /// Drops the entries (`Caches::release`).
    // PORT: not in Go.
    fn clear(&self) {
        let entries = std::mem::take(&mut *self.cache.borrow_mut());
        drop(entries);
    }
}

// Go: module/cache.go:62 caches
// PORT: Go `*packagejson.InfoCache` is shared between resolvers
// (`ResolverOptions.PackageJsonCache`), so it is `Rc<InfoCache>`. `InfoCache`
// has interior mutability, like the Go `SyncMap`.
pub struct Caches {
    pub package_json_info_cache: Rc<InfoCache>,

    pub module_resolution_cache: ModuleResolutionCache,
    pub type_ref_directive_resolution_cache: TypeRefDirectiveResolutionCache,

    // Cached representations for `core.CompilerOptions.paths`, keyed by the
    // path mappings themselves. This does not handle other path patterns such
    // as `typesVersions`.
    pub parsed_patterns_for_paths: ParsedPatternsCache,

    /// The resolution caches that this resolver shares with the other
    /// resolvers of one program load (see `SharedResolutionCache`). `None`
    /// for a resolver that shares nothing.
    pub shared: Option<SharedResolutionLink>,

    /// A parse worker's resolver: the package.json lookups of the
    /// resolution that it runs now, published with its answer.
    pub package_json_log: RefCell<Vec<PackageJsonLookup>>,

    /// The loader's resolver: the package.json lookups of the worker
    /// answers that it took from `shared`. A read of all the package.json
    /// cache entries lists them too
    /// (`DefaultResolver::package_json_cache_entries`).
    pub worker_package_jsons: RefCell<Vec<Arc<[PackageJsonLookup]>>>,

    /// The loader's resolver in `tsc -b`: the file system lookups of the
    /// worker answers that it took from `shared` (`SharedResolution::lookups`).
    /// The load adds them to the build host's cache at its end
    /// (`DefaultResolver::take_worker_lookups`, `BuildStatCache::end_load`).
    pub worker_lookups: RefCell<Vec<Arc<[StatLookup]>>>,

    /// The loader's resolver during a resolve-ahead program load
    /// (compiler/resolve_ahead.rs). The load removes it at its end.
    pub ahead: RefCell<Option<AheadLink>>,
}

/// The loader's resolver in a resolve-ahead program load
/// (compiler/resolve_ahead.rs): the answers of the workers, the check before
/// the loader takes one, and the keys of the load.
// PORT: not in Go (perf).
pub struct AheadLink {
    /// The answers of the resolve-ahead workers of this load. `None` when
    /// no worker runs; the load then only records its keys.
    pub answers: Option<Arc<SharedResolutionCache>>,
    /// Checks the calls of a worker answer for a key on the loader's file
    /// system and replays their side effects. False: a call gives another
    /// answer there, and the loader resolves the key itself.
    pub accept: AheadAccept,
    /// The keys that the loader resolved or took in this load, in its
    /// order: the keys for the workers of the next load.
    pub keys: RefCell<KeyList>,
    /// The workers' queue of the previous load's keys. `None` when no
    /// worker runs.
    pub queue: Option<Arc<AheadQueue>>,
    /// The index in the queue after the last key of the loader that was
    /// found there (`AheadQueue::find`).
    pub cursor: Cell<usize>,
    pub stats: Cell<AheadStats>,
}

/// The keys of the previous load, which the resolve-ahead workers resolve
/// in order, and who resolves each one: the loader takes a key that no
/// worker has started, so no key is resolved twice, and it waits for a key
/// that a worker resolves now.
// PORT: not in Go (perf).
pub struct AheadQueue {
    pub keys: Arc<KeyList>,
    /// The index of the next key for a worker.
    pub next: std::sync::atomic::AtomicUsize,
    /// Per key: `KEY_FREE`, `KEY_WORKER`, `KEY_DONE` or `KEY_LOADER`.
    states: Box<[std::sync::atomic::AtomicU8]>,
}

const KEY_FREE: u8 = 0;
/// A worker resolves the key now.
const KEY_WORKER: u8 = 1;
/// A worker ended the key: its answer is published, unless the
/// resolution could not be shared or panicked.
const KEY_DONE: u8 = 2;
/// The loader resolves the key itself.
const KEY_LOADER: u8 = 3;

/// How many keys after the cursor `AheadQueue::find` looks at. The loader
/// meets the keys of the previous load in its order, less removed keys
/// and with new ones between them.
const FIND_AHEAD: usize = 4;

impl AheadQueue {
    #[must_use]
    pub fn new(keys: Arc<KeyList>) -> Self {
        let states = (0..keys.len())
            .map(|_| std::sync::atomic::AtomicU8::new(KEY_FREE))
            .collect();
        AheadQueue {
            keys,
            next: std::sync::atomic::AtomicUsize::new(0),
            states,
        }
    }

    /// A worker takes the next key that the loader did not take: its index
    /// and parts. `None` when no key is left.
    pub fn take_next(&self) -> Option<(usize, (&str, &str, ResolutionMode))> {
        use std::sync::atomic::Ordering;
        loop {
            let index = self.next.fetch_add(1, Ordering::Relaxed);
            let key = self.keys.get(index)?;
            if self.states[index]
                .compare_exchange(KEY_FREE, KEY_WORKER, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
            {
                return Some((index, key));
            }
        }
    }

    /// A worker ended key `index` (after it published the answer).
    pub fn done(&self, index: usize) {
        self.states[index].store(KEY_DONE, std::sync::atomic::Ordering::Release);
    }

    /// The index of the loader's key `key`, from `cursor` on, and moves
    /// the cursor after it.
    fn find(&self, cursor: &Cell<usize>, key: (&str, &str, ResolutionMode)) -> Option<usize> {
        let start = cursor.get();
        let index = (start..self.keys.len().min(start + FIND_AHEAD))
            .find(|&index| self.keys.get(index) == Some(key))?;
        cursor.set(index + 1);
        Some(index)
    }

    /// For the loader's key `index` that has no answer: true when a worker
    /// resolved it (it waits while a worker resolves it now), so the answer
    /// may be published now. False: the loader resolves it itself, and no
    /// worker starts it.
    fn wait_or_take(&self, index: usize) -> bool {
        use std::sync::atomic::Ordering;
        let state = &self.states[index];
        match state.compare_exchange(KEY_FREE, KEY_LOADER, Ordering::AcqRel, Ordering::Acquire) {
            Ok(_) | Err(KEY_LOADER) => false,
            Err(_) => {
                // A resolution takes some microseconds; the worker runs on
                // another core.
                let mut spins = 0u32;
                while state.load(Ordering::Acquire) == KEY_WORKER {
                    spins += 1;
                    if spins % 256 == 0 {
                        std::thread::yield_now();
                    } else {
                        std::hint::spin_loop();
                    }
                }
                true
            }
        }
    }
}

/// The check of a worker answer (`AheadLink::accept`): the key, the answer
/// and the file system calls of its resolution.
pub type AheadAccept = Rc<dyn Fn(ModuleKeyParts<'_>, &ResolvedModule, &[AheadCall]) -> bool>;

/// The module resolution keys of one program load that have no redirect,
/// in the load's order (`AheadLink::keys`). The keys share one text, so
/// the loader records a key with no allocation of its own, and the list
/// frees in two.
// PORT: not in Go (perf).
#[derive(Default)]
pub struct KeyList {
    text: String,
    /// Per key: the end of its containing directory and of its module name
    /// in `text`, and its resolution mode. A key starts where the one
    /// before it ends.
    ends: Vec<(usize, usize, ResolutionMode)>,
}

impl KeyList {
    /// An empty list with room for the keys of `like`.
    #[must_use]
    pub fn with_capacity_of(like: &KeyList) -> Self {
        KeyList {
            text: String::with_capacity(like.text.len()),
            ends: Vec::with_capacity(like.ends.len()),
        }
    }

    pub fn push(&mut self, containing_directory: &str, module_name: &str, mode: ResolutionMode) {
        self.text.push_str(containing_directory);
        let directory_end = self.text.len();
        self.text.push_str(module_name);
        self.ends.push((directory_end, self.text.len(), mode));
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.ends.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.ends.is_empty()
    }

    /// The containing directory, module name and mode of key `index`.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<(&str, &str, ResolutionMode)> {
        let &(directory_end, end, mode) = self.ends.get(index)?;
        let start = index.checked_sub(1).map_or(0, |before| self.ends[before].1);
        Some((
            &self.text[start..directory_end],
            &self.text[directory_end..end],
            mode,
        ))
    }
}

/// What the loader did with the keys of a resolve-ahead load that its own
/// cache did not have.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AheadStats {
    /// Worker answers that passed the check.
    pub taken: usize,
    /// Worker answers that failed the check.
    pub rejected: usize,
    /// Keys with no worker answer (not resolved yet, new or not shareable).
    pub missing: usize,
    /// Keys whose worker answer the loader waited for.
    pub waited: usize,
}

impl Caches {
    // PORT: Go zero `caches` with only `packageJsonInfoCache` set
    // (`NewResolver` with a shared `PackageJsonCache`).
    #[must_use]
    pub fn with_package_json_info_cache(package_json_info_cache: Rc<InfoCache>) -> Caches {
        Caches {
            package_json_info_cache,
            module_resolution_cache: ModuleResolutionCache::default(),
            type_ref_directive_resolution_cache: TypeRefDirectiveResolutionCache::default(),
            parsed_patterns_for_paths: ParsedPatternsCache::default(),
            shared: None,
            package_json_log: RefCell::new(Vec::new()),
            worker_package_jsons: RefCell::new(Vec::new()),
            worker_lookups: RefCell::new(Vec::new()),
            ahead: RefCell::new(None),
        }
    }

    /// Drops the cached resolutions and package.json entries when no
    /// program uses this resolver any more
    /// (`NewProgram::release_resolver_caches`). A package.json cache that
    /// another resolver shares stays.
    // PORT: not in Go. Go's GC frees the resolver with its last program.
    pub fn release(&self) {
        let modules = std::mem::take(&mut *self.module_resolution_cache.cache.borrow_mut());
        let type_ref_directives =
            std::mem::take(&mut *self.type_ref_directive_resolution_cache.cache.borrow_mut());
        self.parsed_patterns_for_paths.clear();
        let worker_package_jsons = std::mem::take(&mut *self.worker_package_jsons.borrow_mut());
        let worker_lookups = std::mem::take(&mut *self.worker_lookups.borrow_mut());
        drop((
            modules,
            type_ref_directives,
            worker_package_jsons,
            worker_lookups,
        ));
        if Rc::strong_count(&self.package_json_info_cache) == 1 {
            self.package_json_info_cache.clear();
        }
    }
}

// Go: module/cache.go:18 moduleResolutionCache and :40
// typeRefDirectiveResolutionCache, the `SyncMap`s themselves.
// PORT: Go shares one resolver, and so these maps, between all parse tasks
// of a program. The Rust loader resolves on one thread with `Rc` values
// (`Caches`), and each parse worker has its own resolver. This is the part
// they share: the loader's resolver reads what the workers resolved ahead
// of it. A resolution is a function of its key (the key has the redirect
// config) and of the file system, so any resolver stores the same answer
// that the loader would find; first answer wins, as in Go. Only a program
// that resolves on the plain OS file system, with no project references
// and no traced resolution, shares one (`process_all_program_files`).
//
// Go also shares one package.json cache, which the build info lists
// (`Program::package_json_cache_entries`). So each answer carries the
// package.json lookups that made it (`SharedResolution`), and the loader
// adds them to its own package.json cache.
#[derive(Default)]
pub struct SharedResolutionCache {
    modules: std::sync::Mutex<
        FxHashMap<ModuleResolutionCacheKey, SharedResolution<Arc<ResolvedModule>>>,
    >,
    type_ref_directives: std::sync::Mutex<
        FxHashMap<
            TypeRefDirectiveResolutionCacheKey,
            SharedResolution<Arc<ResolvedTypeReferenceDirective>>,
        >,
    >,
}

/// A parse worker's answer in the `SharedResolutionCache`.
#[derive(Clone)]
pub struct SharedResolution<T> {
    pub value: T,
    /// The package.json lookups of the resolution (`package_json_log`).
    pub package_jsons: Arc<[PackageJsonLookup]>,
    /// The file system lookups of the resolution that the `tsc -b` host's
    /// cache did not have (`note_worker_lookup`). `None` when the worker
    /// does not log them (no `tsc -b` host).
    pub lookups: Option<Arc<[StatLookup]>>,
    /// The file system calls of a resolve-ahead worker's resolution, with
    /// their answers (`AheadCall`). `None` from other parse workers. The
    /// loader takes a resolve-ahead answer only with them.
    pub ahead: Option<Arc<[AheadCall]>>,
}

/// One file system call of a resolve-ahead worker's resolution
/// (compiler/resolve_ahead.rs), with its answer. Before the loader takes
/// the answer, it checks each call on its own file system and replays the
/// side effects of the call (`AheadLink::accept`).
// PORT: not in Go (perf). Go resolves in each parse task on the host's
// file system, which tracks the calls itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AheadCall {
    /// `file_exists` of a name whose path is `path`.
    FileExists { path: Path, exists: bool },
    /// A `directory_exists` that gave false.
    MissingDirectory { path: Path },
    /// `read_file`: the xxh3 hash of the text, `None` when the file could
    /// not be read.
    Read {
        file_name: String,
        hash: Option<u128>,
    },
}

/// How the resolve-ahead call log of a resolution ended
/// (`Caches::take_ahead_log`).
pub enum AheadLogEnd {
    /// This thread does not log (it is no resolve-ahead worker).
    NotLogged,
    /// The resolution made a call that the loader cannot check (a read of
    /// an open file, a directory listing, a stat). Its answer is not
    /// published.
    Unshareable,
    Logged(Arc<[AheadCall]>),
}

/// The state of a resolve-ahead worker thread.
struct AheadThread {
    current_directory: String,
    use_case_sensitive_file_names: bool,
    /// The calls of the resolution that runs now. `None` between
    /// resolutions.
    calls: Option<Vec<AheadCall>>,
    /// False when the resolution made a call that the loader cannot check.
    shareable: bool,
    /// The hash of each file that this thread read, by name. The
    /// package.json cache of the worker's resolver keeps the parses of
    /// these texts, and a later resolution that reads the cache logs the
    /// read again (`Caches::log_package_json`).
    reads: FxHashMap<String, Option<u128>>,
}

thread_local! {
    /// Set on a resolve-ahead worker thread (`begin_ahead_thread`).
    static AHEAD: RefCell<Option<AheadThread>> = const { RefCell::new(None) };
}

/// Makes this thread a resolve-ahead worker: its resolutions log their file
/// system calls (`note_ahead_call`). `current_directory` and
/// `use_case_sensitive_file_names` make the paths, as the host's `to_path`.
pub fn begin_ahead_thread(current_directory: &str, use_case_sensitive_file_names: bool) {
    AHEAD.with(|ahead| {
        *ahead.borrow_mut() = Some(AheadThread {
            current_directory: current_directory.to_string(),
            use_case_sensitive_file_names,
            calls: None,
            shareable: true,
            reads: FxHashMap::default(),
        });
    });
}

/// Ends `begin_ahead_thread`.
pub fn end_ahead_thread() {
    let state = AHEAD.with(|ahead| ahead.borrow_mut().take());
    drop(state);
}

/// Logs `call` in the resolution that runs on this thread, if it logs.
pub fn note_ahead_call(call: AheadCall) {
    AHEAD.with(|ahead| {
        if let Some(calls) = ahead
            .borrow_mut()
            .as_mut()
            .and_then(|state| state.calls.as_mut())
        {
            calls.push(call);
        }
    });
}

/// Logs a read of `file_name` (`hash` of its text, `None` when it could not
/// be read) in the resolution that runs on this thread, and keeps the hash
/// for later reads of the same parse.
pub fn note_ahead_read(file_name: &str, hash: Option<u128>) {
    AHEAD.with(|ahead| {
        if let Some(state) = ahead.borrow_mut().as_mut() {
            state.reads.insert(file_name.to_string(), hash);
            if let Some(calls) = state.calls.as_mut() {
                calls.push(AheadCall::Read {
                    file_name: file_name.to_string(),
                    hash,
                });
            }
        }
    });
}

/// Logs the file system calls of Go `getPackageJsonInfo` for `entry` in
/// the resolve-ahead resolution that runs on this thread. A resolution that
/// finds the entry in the worker's package.json cache makes no call, but
/// the loader's own resolution makes them when its cache does not have the
/// entry. So each resolution that reads the entry lists them, as
/// `Caches::log_package_json` does for the `tsc -b` lookups. A call that
/// the worker made for this entry is then listed twice, which the loader's
/// check and replay allow.
fn log_ahead_package_json(entry: &InfoCacheEntry) {
    AHEAD.with(|ahead| {
        let mut ahead = ahead.borrow_mut();
        let Some(AheadThread {
            current_directory,
            use_case_sensitive_file_names,
            calls: Some(calls),
            shareable,
            reads,
        }) = ahead.as_mut()
        else {
            return;
        };
        let to_path = |name: &str| to_path(name, current_directory, *use_case_sensitive_file_names);
        if !entry.directory_exists {
            calls.push(AheadCall::MissingDirectory {
                path: to_path(&entry.package_directory),
            });
            return;
        }
        let file_name = combine_paths(&entry.package_directory, &["package.json"]);
        calls.push(AheadCall::FileExists {
            path: to_path(&file_name),
            exists: entry.exists(),
        });
        if entry.exists() {
            match reads.get(&file_name) {
                Some(&hash) => calls.push(AheadCall::Read { file_name, hash }),
                // The worker did not read it from a file that the loader can
                // check.
                None => *shareable = false,
            }
        }
    });
}

/// Marks the resolution that runs on this thread as not shareable: it made
/// a call that the loader cannot check. With `file_name`, it read that
/// file from a source that the loader cannot check (an open file), so a
/// later resolution that uses its parse is not shareable either.
pub fn note_ahead_unshareable(file_name: Option<&str>) {
    AHEAD.with(|ahead| {
        if let Some(state) = ahead.borrow_mut().as_mut() {
            state.shareable = false;
            if let Some(file_name) = file_name {
                state.reads.remove(file_name);
            }
        }
    });
}

/// A lookup that Go `cachedvfs` caches (all but `Stat`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatKind {
    FileExists,
    DirectoryExists,
    Realpath,
    Entries,
}

/// One cached lookup of a parse worker's resolution, without its value.
/// The value is in the worker cache of the program load
/// (`BuildStatCache`).
#[derive(Clone, Debug)]
pub struct StatLookup {
    pub kind: StatKind,
    pub path: String,
}

thread_local! {
    /// True on a parse worker thread whose file system reads the `tsc -b`
    /// host's cache (`set_worker_lookup_log`).
    static WORKER_LOOKUP_LOG: Cell<bool> = const { Cell::new(false) };
    /// The lookups of the parse worker resolution that runs on this thread
    /// now (`Caches::start_package_json_log` to `take_package_json_log`).
    static WORKER_LOOKUPS: RefCell<Option<Vec<StatLookup>>> = const { RefCell::new(None) };
}

/// Makes the resolutions of this parse worker thread log their file system
/// lookups (`note_worker_lookup`) or not.
// PORT: not in Go. Go parse tasks share the host's cachedvfs, so the
// lookups of each resolution are in it. A `tsc -b` parse worker keeps its
// lookups out of the host's cache, and the loader adds the lookups of the
// answers it takes (`BuildStatCache`).
pub fn set_worker_lookup_log(on: bool) {
    WORKER_LOOKUP_LOG.with(|log| log.set(on));
}

/// Records a lookup of the parse worker resolution that runs on this
/// thread, if one runs and this thread logs lookups.
pub fn note_worker_lookup(kind: StatKind, path: &str) {
    WORKER_LOOKUPS.with(|log| {
        if let Some(log) = log.borrow_mut().as_mut() {
            log.push(StatLookup {
                kind,
                path: path.to_string(),
            });
        }
    });
}

/// One Go `getPackageJsonInfo` call of a parse worker's resolution: the
/// package.json cache entry that it read or stored, without the contents.
#[derive(Clone, Debug)]
pub struct PackageJsonLookup {
    pub package_directory: String,
    pub directory_exists: bool,
    /// The package.json file exists (`InfoCacheEntry::exists`).
    pub exists: bool,
}

/// One entry of `DefaultResolver::package_json_cache_entries`: the parts
/// of a package.json cache entry (Go `*packagejson.InfoCacheEntry`) that the
/// build info reads.
// PORT: Go yields the cache entries. The entries of the parse workers'
// lookups (`Caches::worker_package_jsons`) have no contents here, so the
// callback gets these parts of each entry instead.
#[derive(Clone, Copy, Debug)]
pub struct PackageJsonCacheEntry<'e> {
    /// Go `GetDirectory()`.
    pub package_directory: &'e str,
    pub directory_exists: bool,
    /// Go `Exists()`: the package.json file was read.
    pub exists: bool,
}

/// A resolver's link to a `SharedResolutionCache`.
#[derive(Clone)]
pub struct SharedResolutionLink {
    pub cache: Arc<SharedResolutionCache>,
    /// True for a parse worker's resolver: it stores each answer it makes.
    /// The loader's resolver only reads, so its serial path does no extra
    /// copies.
    pub publish: bool,
}

fn lock_shared<T>(mutex: &std::sync::Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

impl SharedResolutionCache {
    /// Go `moduleResolutionCache.Get`.
    #[must_use]
    pub fn get_module(&self, key: &dyn ModuleKey) -> Option<SharedResolution<Arc<ResolvedModule>>> {
        lock_shared(&self.modules).get(key).cloned()
    }

    /// Go `moduleResolutionCache.Set` (`LoadOrStore`: the first value wins).
    pub fn set_module(
        &self,
        key: ModuleResolutionCacheKey,
        value: SharedResolution<Arc<ResolvedModule>>,
    ) {
        lock_shared(&self.modules).entry(key).or_insert(value);
    }

    /// Go `typeRefDirectiveResolutionCache.Get`.
    #[must_use]
    pub fn get_type_ref_directive(
        &self,
        key: &TypeRefDirectiveResolutionCacheKey,
    ) -> Option<SharedResolution<Arc<ResolvedTypeReferenceDirective>>> {
        lock_shared(&self.type_ref_directives).get(key).cloned()
    }

    /// Go `typeRefDirectiveResolutionCache.Set` (`Store`: the last value
    /// wins).
    pub fn set_type_ref_directive(
        &self,
        key: TypeRefDirectiveResolutionCacheKey,
        value: SharedResolution<Arc<ResolvedTypeReferenceDirective>>,
    ) {
        lock_shared(&self.type_ref_directives).insert(key, value);
    }
}

impl Caches {
    /// True for a parse worker's resolver, which publishes its answers.
    #[must_use]
    pub fn publishes(&self) -> bool {
        self.shared.as_ref().is_some_and(|shared| shared.publish)
    }

    /// Records a package.json lookup of a parse worker's resolution
    /// (`publishes`). `entry` is the package.json cache entry that the
    /// lookup read or stored.
    ///
    /// The file system lookups of Go `getPackageJsonInfo` for the entry go
    /// into the resolution's lookup log too: an earlier resolution of the
    /// worker made them, but Go makes them in whichever resolution of the
    /// load reads the entry first, so each one that reads it lists them.
    pub fn log_package_json(&self, entry: &InfoCacheEntry) {
        if self.publishes() {
            self.package_json_log.borrow_mut().push(PackageJsonLookup {
                package_directory: entry.package_directory.clone(),
                directory_exists: entry.directory_exists,
                exists: entry.exists(),
            });
            if WORKER_LOOKUPS.with(|log| log.borrow().is_some()) {
                note_worker_lookup(StatKind::DirectoryExists, &entry.package_directory);
                if entry.directory_exists {
                    note_worker_lookup(
                        StatKind::FileExists,
                        &combine_paths(&entry.package_directory, &["package.json"]),
                    );
                }
            }
            log_ahead_package_json(entry);
        }
    }

    /// Starts the package.json log of a parse worker's resolution. The
    /// lookups before it (such as `source_file_meta_data`) are not part of
    /// a resolution; the loader makes them itself. It starts the file
    /// system lookup log too, on a thread that logs them
    /// (`set_worker_lookup_log`).
    pub fn start_package_json_log(&self) {
        if self.publishes() {
            self.package_json_log.borrow_mut().clear();
            if WORKER_LOOKUP_LOG.with(Cell::get) {
                WORKER_LOOKUPS.with(|log| *log.borrow_mut() = Some(Vec::new()));
            }
            AHEAD.with(|ahead| {
                if let Some(state) = ahead.borrow_mut().as_mut() {
                    state.calls = Some(Vec::new());
                    state.shareable = true;
                }
            });
        }
    }

    /// Takes the resolve-ahead call log of the resolution that just ended
    /// (`start_package_json_log` to here), and stops it.
    pub fn take_ahead_log(&self) -> AheadLogEnd {
        AHEAD.with(|ahead| {
            let mut ahead = ahead.borrow_mut();
            let Some(state) = ahead.as_mut() else {
                return AheadLogEnd::NotLogged;
            };
            match state.calls.take() {
                None => AheadLogEnd::NotLogged,
                Some(calls) if state.shareable => AheadLogEnd::Logged(calls.into()),
                Some(_) => AheadLogEnd::Unshareable,
            }
        })
    }

    /// The loader's resolver in a resolve-ahead load: records `key` for
    /// the next load (`AheadLink::keys`), and gives the worker answer for
    /// `key` when there is one and it passes the check
    /// (`AheadLink::accept`). `None`: the loader resolves the key itself.
    pub fn take_resolved_ahead(&self, key: ModuleKeyParts<'_>) -> Option<Arc<ResolvedModule>> {
        let ahead = self.ahead.borrow();
        let ahead = ahead.as_ref()?;
        let (containing_directory, module_name, mode, redirect_config_name) = key;
        // A key with a redirect needs its project reference; only the
        // loader resolves it.
        if redirect_config_name.is_empty() {
            ahead
                .keys
                .borrow_mut()
                .push(containing_directory, module_name, mode);
        }
        let answers = ahead.answers.as_ref()?;
        let mut stats = ahead.stats.get();
        let mut found = answers.get_module(&key);
        if redirect_config_name.is_empty()
            && let Some(queue) = &ahead.queue
            && let Some(index) =
                queue.find(&ahead.cursor, (containing_directory, module_name, mode))
            && found.is_none()
            && queue.wait_or_take(index)
        {
            stats.waited += 1;
            found = answers.get_module(&key);
        }
        let accepted = match found
            .as_ref()
            .and_then(|found| Some((found, found.ahead.as_ref()?)))
        {
            None => {
                stats.missing += 1;
                false
            }
            Some((found, calls)) => {
                let accepted = (ahead.accept)(key, &found.value, calls);
                if accepted {
                    stats.taken += 1;
                } else {
                    stats.rejected += 1;
                }
                accepted
            }
        };
        ahead.stats.set(stats);
        let found = found.filter(|_| accepted)?;
        self.note_worker_package_jsons(&found.package_jsons);
        Some(found.value)
    }

    /// Takes the package.json lookups of the resolution that just ended.
    pub fn take_package_json_log(&self) -> Arc<[PackageJsonLookup]> {
        std::mem::take(&mut *self.package_json_log.borrow_mut()).into()
    }

    /// Takes the file system lookups of the resolution that just ended
    /// (`note_worker_lookup`), and stops the log.
    pub fn take_worker_lookup_log(&self) -> Option<Arc<[StatLookup]>> {
        WORKER_LOOKUPS
            .with(|log| log.borrow_mut().take())
            .map(Into::into)
    }

    /// Keeps the package.json lookups of a worker answer that the loader's
    /// resolver took (`worker_package_jsons`).
    pub fn note_worker_package_jsons(&self, package_jsons: &Arc<[PackageJsonLookup]>) {
        if !package_jsons.is_empty() {
            self.worker_package_jsons
                .borrow_mut()
                .push(package_jsons.clone());
        }
    }

    /// Keeps the file system lookups of a worker answer that the loader's
    /// resolver took (`worker_lookups`).
    pub fn note_worker_lookups(&self, lookups: &Option<Arc<[StatLookup]>>) {
        if let Some(lookups) = lookups.as_ref().filter(|lookups| !lookups.is_empty()) {
            self.worker_lookups.borrow_mut().push(lookups.clone());
        }
    }
}

// Go: module/cache.go:74 newCaches
#[must_use]
pub fn new_caches(
    current_directory: &str,
    use_case_sensitive_file_names: bool,
    _options: &CompilerOptions,
) -> Caches {
    Caches::with_package_json_info_cache(Rc::new(new_info_cache(
        current_directory,
        use_case_sensitive_file_names,
    )))
}

// Go: module/cache.go:84 getRedirectConfigName
#[must_use]
pub fn get_redirect_config_name(redirect: Option<&dyn ModuleResolvedProjectReference>) -> String {
    match redirect {
        None => String::new(),
        Some(redirect) => redirect.config_name().to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::vfs::osvfs_fs;

    struct TestHost {
        fs: Rc<dyn Fs>,
        current_directory: String,
    }

    impl ResolutionHost for TestHost {
        fn fs(&self) -> &dyn Fs {
            &*self.fs
        }

        fn get_current_directory(&self) -> &str {
            &self.current_directory
        }
    }

    /// A bundler resolver on the OS file system of this thread, linked to
    /// `shared` when given.
    fn test_resolver(dir: &str, shared: Option<SharedResolutionLink>) -> DefaultResolver {
        let host: Rc<dyn ResolutionHost> = Rc::new(TestHost {
            fs: osvfs_fs(),
            current_directory: dir.to_string(),
        });
        let options = Rc::new(CompilerOptions {
            module: ModuleKind::ES_NEXT,
            module_resolution: ModuleResolutionKind::BUNDLER,
            ..Default::default()
        });
        let mut resolver = new_resolver(ResolverOptions {
            host: Some(host),
            compiler_options: Some(options),
            ..Default::default()
        });
        resolver.caches.shared = shared;
        resolver
    }

    /// The imports of `src/deep/index.ts`. `@types/node` is a type
    /// reference directive.
    const NAMES: &[&str] = &[
        "pkg-a",
        "pkg-a/sub",
        "@scope/pkg-b",
        "missing-pkg",
        "@scope/missing",
        "./local",
        "@types/node",
    ];

    fn resolve(resolver: &DefaultResolver, dir: &str, names: &[&str]) {
        let containing_file = format!("{dir}/src/deep/index.ts");
        for name in names {
            if let Some(type_reference) = name.strip_prefix("@types/") {
                let _ = resolver.resolve_type_reference_directive(
                    type_reference,
                    &containing_file,
                    ModuleKind::ES_NEXT,
                    None,
                );
            } else {
                let _ =
                    resolver.resolve_module_name(name, &containing_file, ModuleKind::ES_NEXT, None);
            }
        }
    }

    /// The package.json cache entries that the build info reads, sorted.
    fn package_json_entries(resolver: &DefaultResolver) -> Vec<(String, String, bool, bool)> {
        let mut entries = Vec::new();
        resolver.package_json_cache_entries(|key, entry| {
            entries.push((
                key.0.clone(),
                entry.package_directory.to_string(),
                entry.directory_exists,
                entry.exists,
            ));
            true
        });
        entries.sort();
        entries
    }

    /// The loader's resolver takes every answer from parse workers on
    /// other threads, and its package.json cache then holds the same
    /// entries as a resolver that resolved all names itself (the one Go
    /// cache of all parse tasks).
    #[test]
    fn loader_takes_worker_package_json_lookups() {
        let root = std::env::temp_dir().join(format!(
            "ts_goport_shared_package_jsons_{}",
            std::process::id()
        ));
        let files = [
            ("src/deep/local.ts", "export {};"),
            (
                "node_modules/pkg-a/package.json",
                r#"{ "name": "pkg-a", "version": "1.0.0", "types": "index.d.ts" }"#,
            ),
            ("node_modules/pkg-a/index.d.ts", "export {};"),
            ("node_modules/pkg-a/sub/index.d.ts", "export {};"),
            (
                "node_modules/@scope/pkg-b/package.json",
                r#"{ "name": "@scope/pkg-b", "version": "2.0.0", "types": "lib/b.d.ts" }"#,
            ),
            ("node_modules/@scope/pkg-b/lib/b.d.ts", "export {};"),
            (
                "node_modules/@types/node/package.json",
                r#"{ "name": "@types/node", "version": "20.0.0" }"#,
            ),
            ("node_modules/@types/node/index.d.ts", "export {};"),
        ];
        for (path, text) in files {
            let path = root.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        }
        let dir = root.to_string_lossy().replace('\\', "/");

        let alone = test_resolver(&dir, None);
        resolve(&alone, &dir, NAMES);
        let expected = package_json_entries(&alone);
        assert!(expected.iter().any(|entry| entry.3), "{expected:?}");
        assert!(
            expected
                .iter()
                .any(|entry| !entry.3 && entry.0.contains("/node_modules/")),
            "{expected:?}"
        );

        let shared = Arc::new(SharedResolutionCache::default());
        std::thread::scope(|scope| {
            for names in NAMES.chunks(3) {
                let link = SharedResolutionLink {
                    cache: shared.clone(),
                    publish: true,
                };
                let dir = dir.as_str();
                scope.spawn(move || resolve(&test_resolver(dir, Some(link)), dir, names));
            }
        });
        let loader = test_resolver(
            &dir,
            Some(SharedResolutionLink {
                cache: shared,
                publish: false,
            }),
        );
        resolve(&loader, &dir, NAMES);
        // Every answer came from a worker, so the loader made no lookup.
        let mut own = 0;
        loader.caches.package_json_info_cache.range(|_, _| {
            own += 1;
            true
        });
        assert_eq!(own, 0);
        let entries = package_json_entries(&loader);
        std::fs::remove_dir_all(&root).unwrap();
        assert_eq!(entries, expected);
    }
}
