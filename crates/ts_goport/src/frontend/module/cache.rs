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
// `Resolver` methods can take `&self`. Cached Go pointers are `Rc`.
#[derive(Default)]
pub struct ModuleResolutionCache {
    pub cache: RefCell<FxHashMap<ModuleResolutionCacheKey, Rc<ResolvedModule>>>,
}

impl ModuleResolutionCache {
    // Go: module/cache.go:24 moduleResolutionCache.Get
    #[must_use]
    pub fn get(&self, key: &ModuleResolutionCacheKey) -> Option<Rc<ResolvedModule>> {
        self.cache.borrow().get(key).cloned()
    }

    // Go: module/cache.go:28 moduleResolutionCache.Set
    // PORT: Go `LoadOrStore`: the first stored value wins.
    pub fn set(&self, key: ModuleResolutionCacheKey, value: Rc<ResolvedModule>) {
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
#[derive(Default)]
pub struct SharedResolutionCache {
    modules: std::sync::Mutex<FxHashMap<ModuleResolutionCacheKey, Arc<ResolvedModule>>>,
    type_ref_directives: std::sync::Mutex<
        FxHashMap<TypeRefDirectiveResolutionCacheKey, Arc<ResolvedTypeReferenceDirective>>,
    >,
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
    pub fn get_module(&self, key: &ModuleResolutionCacheKey) -> Option<Arc<ResolvedModule>> {
        lock_shared(&self.modules).get(key).cloned()
    }

    /// Go `moduleResolutionCache.Set` (`LoadOrStore`: the first value wins).
    pub fn set_module(&self, key: ModuleResolutionCacheKey, value: Arc<ResolvedModule>) {
        lock_shared(&self.modules).entry(key).or_insert(value);
    }

    /// Go `typeRefDirectiveResolutionCache.Get`.
    #[must_use]
    pub fn get_type_ref_directive(
        &self,
        key: &TypeRefDirectiveResolutionCacheKey,
    ) -> Option<Arc<ResolvedTypeReferenceDirective>> {
        lock_shared(&self.type_ref_directives).get(key).cloned()
    }

    /// Go `typeRefDirectiveResolutionCache.Set` (`Store`: the last value
    /// wins).
    pub fn set_type_ref_directive(
        &self,
        key: TypeRefDirectiveResolutionCacheKey,
        value: Arc<ResolvedTypeReferenceDirective>,
    ) {
        lock_shared(&self.type_ref_directives).insert(key, value);
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
