//! Port of module/cache.go.

use crate::frontend::prelude::*;
use std::cell::Cell;
use std::sync::Arc;

// Go: module/cache.go:9 ModeAwareCache
pub type ModeAwareCache<T> = FxHashMap<ModeAwareCacheKey, T>;

// Go: module/cache.go:11 moduleResolutionCacheKey
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ModuleResolutionCacheKey {
    pub containing_directory: String,
    pub module_name: String,
    pub resolution_mode: ResolutionMode,
    pub redirect_config_name: String,
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
    pub fn get(&self, key: &ModuleResolutionCacheKey) -> Option<Arc<ResolvedModule>> {
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
    pub fn get_module(
        &self,
        key: &ModuleResolutionCacheKey,
    ) -> Option<SharedResolution<Arc<ResolvedModule>>> {
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
        }
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
