//! The Go `*compiler.Program` methods that implement
//! `ModuleSpecifierGenerationHost` (compiler/program.go), and the parts of
//! the module resolver that they call.

use crate::prelude::*;

use crate::frontend::vfs::osvfs_fs;

use super::deps::{self, OutputPathsHost};
use super::packagejson::{self, InfoCacheEntry, PackageJson};
use super::symlinks::KnownSymlinks;
use super::tspath;
use super::types::ModuleSpecifierGenerationHost;
use std::sync::Arc;

/// The current program (`prog()`) as a `ModuleSpecifierGenerationHost`.
/// The program state is reached through the current program, so the host has
/// no fields.
#[derive(Clone, Copy, Debug, Default)]
pub struct ProgramHost;

/// The caches that Go keeps on one program and its module resolver.
#[derive(Default)]
struct ProgramCaches {
    /// Go: module/resolver.go packageJsonInfoCache. Keyed by package.json path.
    package_json_info: FxHashMap<String, Rc<InfoCacheEntry>>,
    /// Go: compiler/program.go knownSymlinks (a lazily computed value).
    known_symlinks: Option<Rc<KnownSymlinks>>,
    /// Go: compiler/program.go opts.TypingsLocation, which is also the
    /// `typingsLocation` of the program's resolver. See `typings_location`.
    typings_location: Option<Rc<str>>,
}

/// The most programs whose caches a thread keeps. A checker worker serves
/// one program. A thread that serves several (the language server's) keeps
/// the most recently used ones; a program found again after it was dropped
/// fills its caches again, with the same values.
const CACHED_PROGRAMS: usize = 8;

thread_local! {
    /// The caches of the programs that used this thread, by `GoProgram::id`
    /// (0 without a program), most recently used first.
    static CACHES: RefCell<Vec<(u32, ProgramCaches)>> = const { RefCell::new(Vec::new()) };
}

/// Runs `f` on this thread's caches of the current program. `f` must not
/// reach the caches again.
fn with_program_caches<R>(f: impl FnOnce(&mut ProgramCaches) -> R) -> R {
    let program = try_prog().map_or(0, |program| program.id);
    CACHES.with(|caches| {
        let mut caches = caches.borrow_mut();
        match caches.iter().position(|(id, _)| *id == program) {
            Some(0) => {}
            Some(position) => {
                let entry = caches.remove(position);
                caches.insert(0, entry);
            }
            None => {
                caches.truncate(CACHED_PROGRAMS - 1);
                caches.insert(0, (program, ProgramCaches::default()));
            }
        }
        f(&mut caches[0].1)
    })
}

/// The typings location of the current program (Go `p.opts.TypingsLocation`).
// PORT: the frontend program holds it, and only the thread that loaded the
// program can read the frontend program (`program::go_frontend_program`).
// Only a language server program with type acquisition has a typings
// location (Go project/project.go:391). The language server loads its
// programs on the dispatch thread, and its language service and checkers
// run there, so the location is read there. The probe for that thread is
// `ls_program::parsed_source_file`: it finds only the programs that
// `ls_program` made on this thread. Other threads get "": a compile checker
// worker, a one-program process, and a language server search thread
// (`ls/search_thread.rs`). Go gives "" for the first two. On a search
// thread of a program with type acquisition, Go gives the location.
fn typings_location() -> Rc<str> {
    if let Some(location) = with_program_caches(|c| c.typings_location.clone()) {
        return location;
    }
    let made_on_this_thread = try_prog()
        .and_then(|program| program.source_files().next())
        .is_some_and(|file| crate::program::ls_program::parsed_source_file(file.root).is_some());
    let location: Rc<str> = if made_on_this_thread {
        crate::program::go_frontend_program()
            .map(|program| program.get_global_typings_cache_location())
            .unwrap_or_default()
            .into()
    } else {
        Rc::from("")
    };
    with_program_caches(|c| c.typings_location = Some(location.clone()));
    location
}

// Go: module/resolver.go:1757 getPackageJsonInfo
// PORT: Go returns `existing.WithPackageDirectory(packageDirectory)`. The
// cache key is `<packageDirectory>/package.json`, so the directory already
// matches and the cached entry is returned as is. Tracing is not ported.
fn get_package_json_info_for_directory(package_directory: &str) -> Option<Rc<InfoCacheEntry>> {
    let package_json_path = tspath::combine_paths(package_directory, &["package.json"]);

    if let Some(existing) =
        with_program_caches(|c| c.package_json_info.get(&package_json_path).cloned())
    {
        if existing.contents.is_some() {
            return Some(existing);
        }
        return None;
    }

    // PORT: the OS file system in the port form (see
    // `scanner_util::GO_STRING_MARKER`); Go parses the file's bytes.
    let fs = osvfs_fs();
    let directory_exists = fs.directory_exists(package_directory);
    if directory_exists && fs.file_exists(&package_json_path) {
        // Ignore error
        let (contents, _) = fs.read_file(&package_json_path);
        let parsed = packagejson::parse(&crate::scanner_util::go_string_bytes(&contents));
        let parseable = parsed.is_ok();
        let result = Rc::new(InfoCacheEntry {
            package_directory: package_directory.to_string(),
            directory_exists: true,
            contents: Some(PackageJson::new(parsed.unwrap_or_default(), parseable)),
        });
        // Go: packageJsonInfoCache.Set keeps the first stored value.
        let result = with_program_caches(|c| {
            c.package_json_info
                .entry(package_json_path)
                .or_insert(result)
                .clone()
        });
        return Some(result);
    }
    with_program_caches(|c| {
        c.package_json_info
            .entry(package_json_path)
            .or_insert_with(|| {
                Rc::new(InfoCacheEntry {
                    package_directory: package_directory.to_string(),
                    directory_exists,
                    contents: None,
                })
            });
    });
    None
}

// Go: module/resolver.go:497 getPackageScopeForPath
fn get_package_scope_for_path(directory: &str) -> Option<Rc<InfoCacheEntry>> {
    tspath::for_each_ancestor_directory_stopping_at_global_cache(
        &typings_location(),
        directory,
        |directory| {
            if let Some(result) = get_package_json_info_for_directory(directory) {
                return (Some(result), true);
            }
            (None, false)
        },
    )
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
    let fs = osvfs_fs();
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
        if let Some(cached) = with_program_caches(|c| c.known_symlinks.clone()) {
            return Some(cached);
        }
        if let Some(go) = crate::program::get_go_symlink_cache() {
            let known_symlinks = Rc::new((*go).clone());
            with_program_caches(|c| c.known_symlinks = Some(known_symlinks.clone()));
            return Some(known_symlinks);
        }
        // PORT: the rest is the legacy loader only. It approximates Go with
        // the data that loader keeps.
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
        with_program_caches(|c| c.known_symlinks = Some(known_symlinks.clone()));
        Some(known_symlinks)
    }

    fn common_source_directory(&self) -> String {
        crate::program::common_source_directory().to_string()
    }

    // Go: compiler/program.go:132 GetGlobalTypingsCacheLocation
    fn get_global_typings_cache_location(&self) -> String {
        typings_location().to_string()
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
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        crate::program::get_project_reference_from_source(path)
    }

    // Go: compiler/program.go:157 GetRedirectTargets
    fn get_redirect_targets(&self, path: &tspath::Path) -> Vec<String> {
        crate::program::get_redirect_targets(path)
    }

    // Go: compiler/program.go:165 GetSourceOfProjectReferenceIfOutputIncluded
    fn get_source_of_project_reference_if_output_included(&self, file: Node) -> String {
        crate::program::get_source_of_project_reference_if_output_included(file)
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
