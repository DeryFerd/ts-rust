//! The Go `*compiler.Program` methods that implement
//! `ModuleSpecifierGenerationHost` (compiler/program.go), and the parts of
//! the module resolver that they call.

use crate::prelude::*;

use ts_vfs::FileSystem;

use super::deps::{self, OutputPathsHost};
use super::packagejson::{self, InfoCacheEntry, PackageJson};
use super::symlinks::KnownSymlinks;
use super::tspath;
use super::types::ModuleSpecifierGenerationHost;

/// The loaded program as a `ModuleSpecifierGenerationHost`. The program
/// state is global in this crate, so the host has no fields.
#[derive(Clone, Copy, Debug, Default)]
pub struct ProgramHost;

thread_local! {
    // Go: module/resolver.go packageJsonInfoCache. Keyed by package.json path.
    static PACKAGE_JSON_INFO_CACHE: RefCell<FxHashMap<String, Rc<InfoCacheEntry>>> =
        RefCell::new(FxHashMap::default());
    // Go: compiler/program.go knownSymlinks (a lazily computed value).
    static KNOWN_SYMLINKS: RefCell<Option<Rc<KnownSymlinks>>> = const { RefCell::new(None) };
}

// Go: module/resolver.go:1757 getPackageJsonInfo
// PORT: Go returns `existing.WithPackageDirectory(packageDirectory)`. The
// cache key is `<packageDirectory>/package.json`, so the directory already
// matches and the cached entry is returned as is. Tracing is not ported.
fn get_package_json_info_for_directory(package_directory: &str) -> Option<Rc<InfoCacheEntry>> {
    let package_json_path = tspath::combine_paths(package_directory, &["package.json"]);

    if let Some(existing) =
        PACKAGE_JSON_INFO_CACHE.with(|c| c.borrow().get(&package_json_path).cloned())
    {
        if existing.contents.is_some() {
            return Some(existing);
        }
        return None;
    }

    let fs = ts_vfs::OsFileSystem::default();
    let directory_exists = fs.directory_exists(package_directory);
    if directory_exists && fs.file_exists(&package_json_path) {
        // Ignore error
        let contents = fs.read_file(&package_json_path).unwrap_or_default();
        let parsed = packagejson::parse(&contents);
        let parseable = parsed.is_ok();
        let result = Rc::new(InfoCacheEntry {
            package_directory: package_directory.to_string(),
            directory_exists: true,
            contents: Some(PackageJson::new(parsed.unwrap_or_default(), parseable)),
        });
        // Go: packageJsonInfoCache.Set keeps the first stored value.
        let result = PACKAGE_JSON_INFO_CACHE.with(|c| {
            c.borrow_mut()
                .entry(package_json_path)
                .or_insert(result)
                .clone()
        });
        return Some(result);
    }
    PACKAGE_JSON_INFO_CACHE.with(|c| {
        c.borrow_mut().entry(package_json_path).or_insert_with(|| {
            Rc::new(InfoCacheEntry {
                package_directory: package_directory.to_string(),
                directory_exists,
                contents: None,
            })
        });
    });
    None
}

// Go: module/resolver.go:493 getPackageScopeForPath
// PORT: the typings location is always empty in this crate.
fn get_package_scope_for_path(directory: &str) -> Option<Rc<InfoCacheEntry>> {
    tspath::for_each_ancestor_directory_stopping_at_global_cache("", directory, |directory| {
        if let Some(result) = get_package_json_info_for_directory(directory) {
            return (Some(result), true);
        }
        (None, false)
    })
}

// Go: module/resolver.go ResolvePackageDirectory
// PORT: the Go resolver runs a full node_modules package lookup. This walks
// the ancestor `node_modules` directories of the containing file, tries
// `<dep>` and then `@types/<dep>`, and uses the real path of the first
// directory that exists. It returns `(original_path, resolved)`. Like Go,
// `original_path` is empty when the real path is the same.
fn resolve_package_directory(
    package_name: &str,
    containing_file: &str,
) -> Option<(String, String)> {
    let fs = ts_vfs::OsFileSystem::default();
    let containing_directory = tspath::get_directory_path(containing_file);
    tspath::for_each_ancestor_directory_stopping_at_global_cache(
        "",
        &containing_directory,
        |directory| {
            if tspath::get_base_file_name(directory) == "node_modules" {
                return (None, false);
            }
            let node_modules = tspath::combine_paths(directory, &["node_modules"]);
            let mut candidates = vec![tspath::combine_paths(&node_modules, &[package_name])];
            if !package_name.starts_with("@types/") {
                candidates.push(tspath::combine_paths(
                    &node_modules,
                    &["@types", &deps::mangle_scoped_package_name(package_name)],
                ));
            }
            for candidate in candidates {
                if fs.directory_exists(&candidate) {
                    let candidate = tspath::normalize_path(&candidate);
                    let real = tspath::normalize_path(&fs.realpath(&candidate));
                    let original = if real == candidate {
                        String::new()
                    } else {
                        candidate
                    };
                    return (Some((original, real)), true);
                }
            }
            (None, false)
        },
    )
}

impl OutputPathsHost for ProgramHost {
    fn common_source_directory(&self) -> String {
        crate::program::common_source_directory().to_string()
    }

    fn get_current_directory(&self) -> String {
        crate::program::get_current_directory().to_string()
    }

    fn use_case_sensitive_file_names(&self) -> bool {
        crate::program::use_case_sensitive_file_names()
    }
}

impl ModuleSpecifierGenerationHost for ProgramHost {
    // Go: compiler/program.go:2017 GetSymlinkCache
    fn get_symlink_cache(&self) -> Option<Rc<KnownSymlinks>> {
        if let Some(cached) = KNOWN_SYMLINKS.with(|c| c.borrow().clone()) {
            return Some(cached);
        }
        let cwd = crate::program::get_current_directory();
        let case = crate::program::use_case_sensitive_file_names();
        let mut known_symlinks = KnownSymlinks::new(cwd, case);

        // Resolved modules store realpath information when they're resolved inside node_modules
        // PORT: type reference directive resolutions are not kept by the
        // program in this crate.
        for resolutions in crate::program::get_resolved_modules().values() {
            for resolution in resolutions.values() {
                known_symlinks
                    .process_resolution(&resolution.original_path, &resolution.resolved_file_name);
            }
        }

        // Check other dependencies for symlinks
        let mut seen_package_jsons: FxHashSet<tspath::Path> = FxHashSet::default();
        for file in crate::program::source_files() {
            let meta = crate::program::get_source_file_meta_data(&source_file_info(file).path);
            if meta.package_json_directory.is_empty()
                || !crate::program::source_file_may_be_emitted(file, false)
                || !seen_package_jsons.insert(tspath::to_path(
                    &meta.package_json_directory,
                    cwd,
                    case,
                ))
            {
                continue;
            }
            let package_json_name =
                tspath::combine_paths(&meta.package_json_directory, &["package.json"]);
            let Some(contents) = self
                .get_package_json_info(&package_json_name)
                .and_then(|info| {
                    info.get_contents()
                        .map(|c| c.fields.get_runtime_dependency_names())
                })
            else {
                continue;
            };

            for dep in contents {
                // Skip work in common case: we already saved a symlink for this package directory
                // in the node_modules adjacent to this package.json
                let possible_directory_path = tspath::to_path(
                    &tspath::combine_paths(&meta.package_json_directory, &["node_modules", &dep]),
                    cwd,
                    case,
                );
                if known_symlinks.has_directory(&possible_directory_path) {
                    continue;
                }
                if !dep.starts_with("@types") {
                    let types_name = format!("@types/{}", deps::mangle_scoped_package_name(&dep));
                    let possible_types_directory_path = tspath::to_path(
                        &tspath::combine_paths(
                            &meta.package_json_directory,
                            &["node_modules", &types_name],
                        ),
                        cwd,
                        case,
                    );
                    if known_symlinks.has_directory(&possible_types_directory_path) {
                        continue;
                    }
                }

                if let Some((original_path, resolved)) =
                    resolve_package_directory(&dep, &package_json_name)
                {
                    known_symlinks.process_resolution(
                        &tspath::combine_paths(&original_path, &["package.json"]),
                        &tspath::combine_paths(&resolved, &["package.json"]),
                    );
                }
            }
        }
        let known_symlinks = Rc::new(known_symlinks);
        KNOWN_SYMLINKS.with(|c| *c.borrow_mut() = Some(known_symlinks.clone()));
        Some(known_symlinks)
    }

    fn common_source_directory(&self) -> String {
        crate::program::common_source_directory().to_string()
    }

    // Go: compiler/program.go:132 GetGlobalTypingsCacheLocation
    // PORT: the program options never set a typings location here.
    fn get_global_typings_cache_location(&self) -> String {
        String::new()
    }

    fn use_case_sensitive_file_names(&self) -> bool {
        crate::program::use_case_sensitive_file_names()
    }

    fn get_current_directory(&self) -> String {
        crate::program::get_current_directory().to_string()
    }

    // Go: compiler/program.go:173 GetProjectReferenceFromSource
    fn get_project_reference_from_source(
        &self,
        path: &tspath::Path,
    ) -> Option<&'static SourceOutputAndProjectReference> {
        crate::program::get_project_reference_from_source(path)
    }

    // Go: compiler/program.go:157 GetRedirectTargets
    // PORT: the program in this crate does not build `redirectTargetsMap`
    // (it does not deduplicate packages by name@version), so no file has
    // redirect targets.
    fn get_redirect_targets(&self, path: &tspath::Path) -> Vec<String> {
        let _ = path;
        Vec::new()
    }

    // Go: compiler/program.go:165 GetSourceOfProjectReferenceIfOutputIncluded
    // PORT: project references are not loaded, so
    // `outputFileToProjectReferenceSource` is always empty.
    fn get_source_of_project_reference_if_output_included(&self, file: Node) -> String {
        source_file_info(file).file_name.clone()
    }

    fn file_exists(&self, path: &str) -> bool {
        crate::program::file_exists(path)
    }

    // Go: compiler/program.go:137 GetNearestAncestorDirectoryWithPackageJson
    fn get_nearest_ancestor_directory_with_package_json(&self, dirname: &str) -> String {
        match get_package_scope_for_path(dirname) {
            Some(scoped) if scoped.exists() => scoped.package_directory.clone(),
            _ => String::new(),
        }
    }

    // Go: compiler/program.go:146 GetPackageJsonInfo
    fn get_package_json_info(&self, pkg_json_path: &str) -> Option<Rc<InfoCacheEntry>> {
        let directory = tspath::get_directory_path(pkg_json_path);
        match get_package_scope_for_path(&directory) {
            Some(scoped) if scoped.exists() && scoped.package_directory == directory => {
                Some(scoped)
            }
            _ => None,
        }
    }

    fn get_default_resolution_mode_for_file(&self, file: Node) -> ResolutionMode {
        crate::program::get_default_resolution_mode_for_file(file)
    }

    fn get_resolved_module_from_module_specifier(
        &self,
        file: Node,
        module_specifier: Node,
    ) -> Option<ResolvedModule> {
        crate::program::get_resolved_module_from_module_specifier(file, module_specifier)
    }

    fn get_mode_for_usage_location(&self, file: Node, module_specifier: Node) -> ResolutionMode {
        crate::program::get_mode_for_usage_location(file, module_specifier)
    }

    fn as_output_paths_host(&self) -> &dyn OutputPathsHost {
        self
    }
}
