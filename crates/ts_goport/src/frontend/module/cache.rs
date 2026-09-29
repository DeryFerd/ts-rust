//! Port of module/cache.go.

use crate::frontend::prelude::*;
use std::sync::Arc;

// Go: module/cache.go:11 ModeAwareCache
pub type ModeAwareCache<T> = FxHashMap<ModeAwareCacheKey, T>;

// Go: module/cache.go:13 moduleResolutionCacheKey
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ModuleResolutionCacheKey {
    pub containing_directory: String,
    pub module_name: String,
    pub resolution_mode: ResolutionMode,
    pub redirect_config_name: String,
}

// Go: module/cache.go:20 moduleResolutionCache
// PORT: Go `collections.SyncMap` is a plain map behind a `RefCell`, so the
// `Resolver` methods can take `&self`. Cached Go pointers are `Arc`: parse
// workers share them (`SharedResolutionCache`), and checker threads read
// the program's resolutions with no copy (`GoSharedState`).
#[derive(Default)]
pub struct ModuleResolutionCache {
    pub cache: RefCell<FxHashMap<ModuleResolutionCacheKey, Arc<ResolvedModule>>>,
}

impl ModuleResolutionCache {
    // Go: module/cache.go:24 moduleResolutionCache.Get
    #[must_use]
    pub fn get(&self, key: &ModuleResolutionCacheKey) -> Option<Arc<ResolvedModule>> {
        self.cache.borrow().get(key).cloned()
    }

    // Go: module/cache.go:28 moduleResolutionCache.Set
    // PORT: Go `LoadOrStore`: the first stored value wins.
    pub fn set(&self, key: ModuleResolutionCacheKey, value: Arc<ResolvedModule>) {
        self.cache.borrow_mut().entry(key).or_insert(value);
    }
}

// Go: module/cache.go:32 typeRefDirectiveResolutionCacheKey
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct TypeRefDirectiveResolutionCacheKey {
    pub containing_directory: String,
    pub type_reference_name: String,
    pub resolution_mode: ResolutionMode,
    pub redirect_config_name: String,
    pub from_inferred_types_containing_file: bool,
}

// Go: module/cache.go:40 typeRefDirectiveResolutionCache
// PORT: see `ModuleResolutionCache`.
#[derive(Default)]
pub struct TypeRefDirectiveResolutionCache {
    pub cache:
        RefCell<FxHashMap<TypeRefDirectiveResolutionCacheKey, Rc<ResolvedTypeReferenceDirective>>>,
}

impl TypeRefDirectiveResolutionCache {
    // Go: module/cache.go:44 typeRefDirectiveResolutionCache.Get
    #[must_use]
    pub fn get(
        &self,
        key: &TypeRefDirectiveResolutionCacheKey,
    ) -> Option<Rc<ResolvedTypeReferenceDirective>> {
        self.cache.borrow().get(key).cloned()
    }

    // Go: module/cache.go:48 typeRefDirectiveResolutionCache.Set
    // PORT: Go `Store`: the last stored value wins.
    pub fn set(
        &self,
        key: TypeRefDirectiveResolutionCacheKey,
        value: Rc<ResolvedTypeReferenceDirective>,
    ) {
        self.cache.borrow_mut().insert(key, value);
    }
}

// Go: module/cache.go:52 caches
// PORT: Go `*packagejson.InfoCache` is shared between resolvers
// (`ResolverOptions.PackageJsonCache`), so it is `Rc<InfoCache>`. `InfoCache`
// has interior mutability, like the Go `SyncMap`. Go `sync.Once` plus the
// pointer field is a `RefCell<Option<..>>`, filled on first use.
pub struct Caches {
    pub package_json_info_cache: Rc<InfoCache>,

    pub module_resolution_cache: ModuleResolutionCache,
    pub type_ref_directive_resolution_cache: TypeRefDirectiveResolutionCache,

    // Cached representation for `core.CompilerOptions.paths`.
    // Doesn't handle other path patterns like in `typesVersions`.
    pub parsed_patterns_for_paths: RefCell<Option<Rc<ParsedPatterns>>>,

    /// The resolution caches that this resolver shares with the other
    /// resolvers of one program load (see `SharedResolutionCache`). `None`
    /// for a resolver that shares nothing.
    pub shared: Option<SharedResolutionLink>,

    /// A parse worker's resolver: the package.json lookups of the
    /// resolution that it runs now, published with its answer.
    pub package_json_log: RefCell<Vec<PackageJsonLookup>>,

    /// The loader's resolver: the package.json lookups of the worker
    /// answers that it took from `shared`. They go into
    /// `package_json_info_cache` before a read of all its entries
    /// (`Resolver::package_json_cache_entries`).
    pub worker_package_jsons: RefCell<Vec<Arc<[PackageJsonLookup]>>>,
}

impl Caches {
    // PORT: Go zero `caches` with only `packageJsonInfoCache` set
    // (`NewResolverWithOptions` with a shared cache).
    #[must_use]
    pub fn with_package_json_info_cache(package_json_info_cache: Rc<InfoCache>) -> Caches {
        Caches {
            package_json_info_cache,
            module_resolution_cache: ModuleResolutionCache::default(),
            type_ref_directive_resolution_cache: TypeRefDirectiveResolutionCache::default(),
            parsed_patterns_for_paths: RefCell::new(None),
            shared: None,
            package_json_log: RefCell::new(Vec::new()),
            worker_package_jsons: RefCell::new(Vec::new()),
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
        let patterns = self.parsed_patterns_for_paths.borrow_mut().take();
        let worker_package_jsons = std::mem::take(&mut *self.worker_package_jsons.borrow_mut());
        drop((modules, type_ref_directives, patterns, worker_package_jsons));
        if Rc::strong_count(&self.package_json_info_cache) == 1 {
            self.package_json_info_cache.clear();
        }
    }
}

// Go: module/cache.go:20 moduleResolutionCache and :40
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
    pub fn log_package_json(&self, entry: &InfoCacheEntry) {
        if self.publishes() {
            self.package_json_log.borrow_mut().push(PackageJsonLookup {
                package_directory: entry.package_directory.clone(),
                directory_exists: entry.directory_exists,
                exists: entry.exists(),
            });
        }
    }

    /// Starts the package.json log of a parse worker's resolution. The
    /// lookups before it (such as `source_file_meta_data`) are not part of
    /// a resolution; the loader makes them itself.
    pub fn start_package_json_log(&self) {
        if self.publishes() {
            self.package_json_log.borrow_mut().clear();
        }
    }

    /// Takes the package.json lookups of the resolution that just ended.
    pub fn take_package_json_log(&self) -> Arc<[PackageJsonLookup]> {
        std::mem::take(&mut *self.package_json_log.borrow_mut()).into()
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
}

// Go: module/cache.go:64 newCaches
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

// Go: module/cache.go:74 getRedirectConfigName
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
    fn test_resolver(dir: &str, shared: Option<SharedResolutionLink>) -> Resolver {
        let host: Rc<dyn ResolutionHost> = Rc::new(TestHost {
            fs: osvfs_fs(),
            current_directory: dir.to_string(),
        });
        let options = Rc::new(CompilerOptions {
            module: ModuleKind::ES_NEXT,
            module_resolution: ModuleResolutionKind::BUNDLER,
            ..Default::default()
        });
        let mut resolver = new_resolver(host, options, "", "");
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

    fn resolve(resolver: &Resolver, dir: &str, names: &[&str]) {
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
    fn package_json_entries(resolver: &Resolver) -> Vec<(String, String, bool, bool)> {
        let mut entries = Vec::new();
        resolver.package_json_cache_entries(|key, entry| {
            entries.push((
                key.0.clone(),
                entry.package_directory.clone(),
                entry.directory_exists,
                entry.exists(),
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
