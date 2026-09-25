//! Port of module/cache.go.

use crate::frontend::prelude::*;

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
    pub cache: RefCell<FxHashMap<TypeRefDirectiveResolutionCacheKey, Rc<ResolvedTypeReferenceDirective>>>,
}

impl TypeRefDirectiveResolutionCache {
    // Go: module/cache.go:44 typeRefDirectiveResolutionCache.Get
    #[must_use]
    pub fn get(&self, key: &TypeRefDirectiveResolutionCacheKey) -> Option<Rc<ResolvedTypeReferenceDirective>> {
        self.cache.borrow().get(key).cloned()
    }

    // Go: module/cache.go:48 typeRefDirectiveResolutionCache.Set
    // PORT: Go `Store`: the last stored value wins.
    pub fn set(&self, key: TypeRefDirectiveResolutionCacheKey, value: Rc<ResolvedTypeReferenceDirective>) {
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
        }
    }
}

// Go: module/cache.go:64 newCaches
#[must_use]
pub fn new_caches(current_directory: &str, use_case_sensitive_file_names: bool, _options: &CompilerOptions) -> Caches {
    Caches::with_package_json_info_cache(Rc::new(new_info_cache(current_directory, use_case_sensitive_file_names)))
}

// Go: module/cache.go:74 getRedirectConfigName
#[must_use]
pub fn get_redirect_config_name(redirect: Option<&dyn ModuleResolvedProjectReference>) -> String {
    match redirect {
        None => String::new(),
        Some(redirect) => redirect.config_name().to_string(),
    }
}
