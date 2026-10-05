//! The Go `*compiler.Program` methods that implement
//! `ModuleSpecifierGenerationHost` (compiler/program.go), and the parts of
//! the module resolver that they call.

use crate::prelude::*;

use crate::frontend::vfs::osvfs_fs;

use super::deps::OutputPathsHost;
use super::packagejson::{self, InfoCacheEntry, PackageJson};
use super::symlinks::KnownSymlinks;
use super::tspath;
use super::types::ModuleSpecifierGenerationHost;
use std::sync::{Arc, PoisonError, RwLock};

/// The current program (`prog()`) as a `ModuleSpecifierGenerationHost`.
/// The program state is reached through the current program, so the host has
/// no fields.
#[derive(Clone, Copy, Debug, Default)]
pub struct ProgramHost;

/// The file system answers that module specifier generation reads, shared
/// by every thread of one program version: Go `compilerHost.fs` (a
/// `cachedvfs.FS`, compiler/host.go:52) and the package.json entries of the
/// program's resolver (module/resolver.go `packageJsonInfoCache`). Go
/// shares both between its checker goroutines.
// PORT: the frontend host and resolver caches are not thread-safe, so only
// the loading thread can read them. The program version's tables hold this
// cache (`program::with_host_fs_cache`) and free it with the program.
#[derive(Default)]
pub(crate) struct HostFsCache {
    /// Go cachedvfs.go `fileExistsCache`, for `file_exists` off the
    /// loading thread (`program::file_exists`).
    file_exists: RwLock<FxHashMap<String, bool>>,
    /// Go module/resolver.go `packageJsonInfoCache`: the entries of the
    /// module specifier lookups (`get_package_json_info_for_directory`), by
    /// the `Path` of the package.json (Go `InfoCache.Get`).
    package_json_info: RwLock<FxHashMap<tspath::Path, Arc<InfoCacheEntry>>>,
}

impl HostFsCache {
    // Go: vfs/cachedvfs/cachedvfs.go:64 FileExists
    /// The cached answer for `path`, or the answer of `probe`, which is then
    /// cached.
    pub(crate) fn file_exists(&self, path: &str, probe: impl FnOnce() -> bool) -> bool {
        if let Some(&ret) = read(&self.file_exists).get(path) {
            return ret;
        }
        let ret = probe();
        write(&self.file_exists).insert(path.to_string(), ret);
        ret
    }

    // Go: packagejson/cache.go:182 Get
    fn get_package_json_info(&self, key: &tspath::Path) -> Option<Arc<InfoCacheEntry>> {
        read(&self.package_json_info).get(key).cloned()
    }

    // Go: packagejson/cache.go:190 Set (the first stored value stays)
    fn set_package_json_info(
        &self,
        key: tspath::Path,
        entry: InfoCacheEntry,
    ) -> Arc<InfoCacheEntry> {
        write(&self.package_json_info)
            .entry(key)
            .or_insert_with(|| Arc::new(entry))
            .clone()
    }

    /// Calls `f` with the key, package directory, `DirectoryExists` and
    /// `Exists()` of each package.json entry, in no order (Go
    /// `InfoCache.Range`, packagejson/cache.go:196). `f` returns false to
    /// stop.
    pub(crate) fn package_json_entries(
        &self,
        mut f: impl FnMut(&tspath::Path, &str, bool, bool) -> bool,
    ) {
        for (key, entry) in read(&self.package_json_info).iter() {
            if !f(
                key,
                &entry.package_directory,
                entry.directory_exists,
                entry.exists(),
            ) {
                return;
            }
        }
    }
}

fn read<T>(lock: &RwLock<T>) -> std::sync::RwLockReadGuard<'_, T> {
    lock.read().unwrap_or_else(PoisonError::into_inner)
}

fn write<T>(lock: &RwLock<T>) -> std::sync::RwLockWriteGuard<'_, T> {
    lock.write().unwrap_or_else(PoisonError::into_inner)
}

/// The caches that Go keeps on one program.
#[derive(Default)]
struct ProgramCaches {
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

// Go: module/resolver.go:1755 getPackageJsonInfo
// PORT: tracing is not ported. The entries are in the program's
// `HostFsCache`, not in the frontend resolver's cache; the build info reads
// both (`incremental::checker_access::package_json_cache_entries`). The key
// is the `Path` of `<packageDirectory>/package.json`, so another spelling of
// a directory (another case on a case-insensitive file system, or a trailing
// separator) finds the entry of the first spelling, and
// `with_package_directory` gives it this spelling, as in Go.
fn get_package_json_info_for_directory(package_directory: &str) -> Option<Arc<InfoCacheEntry>> {
    let package_json_path = tspath::combine_paths(package_directory, &["package.json"]);
    let key = tspath::to_path(
        &package_json_path,
        crate::program::get_current_directory(),
        crate::program::use_case_sensitive_file_names(),
    );

    if let Some(existing) =
        crate::program::with_host_fs_cache(|cache| cache.get_package_json_info(&key))
    {
        if existing.contents.is_some() {
            return Some(existing.with_package_directory(package_directory));
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
        let result = InfoCacheEntry {
            package_directory: package_directory.to_string(),
            directory_exists: true,
            contents: Some(Arc::new(PackageJson::new(
                parsed.unwrap_or_default(),
                parseable,
            ))),
        };
        let result =
            crate::program::with_host_fs_cache(|cache| cache.set_package_json_info(key, result));
        return Some(result.with_package_directory(package_directory));
    }
    crate::program::with_host_fs_cache(|cache| {
        cache.set_package_json_info(
            key,
            InfoCacheEntry {
                package_directory: package_directory.to_string(),
                directory_exists,
                contents: None,
            },
        )
    });
    None
}

// Go: module/resolver.go:485 getPackageScopeForPath
fn get_package_scope_for_path(directory: &str) -> Option<Arc<InfoCacheEntry>> {
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

    // tsgo#4712: Go `Program.ContentMapperExtensions` (program.go:508).
    fn content_mapper_extensions(&self) -> Vec<String> {
        crate::program::content_mapper_extensions()
    }
}

impl ModuleSpecifierGenerationHost for ProgramHost {
    // Go: compiler/program.go:2300 GetSymlinkCache
    fn get_symlink_cache(&self) -> Option<Rc<KnownSymlinks>> {
        if let Some(cached) = with_program_caches(|c| c.known_symlinks.clone()) {
            return Some(cached);
        }
        let go = crate::program::get_go_symlink_cache()?;
        let known_symlinks = Rc::new((*go).clone());
        with_program_caches(|c| c.known_symlinks = Some(known_symlinks.clone()));
        Some(known_symlinks)
    }

    fn common_source_directory(&self) -> String {
        crate::program::common_source_directory().to_string()
    }

    // Go: compiler/program.go:528 ContentMapperExtensions (tsgo#4712)
    fn content_mapper_extensions(&self) -> Vec<String> {
        crate::program::content_mapper_extensions()
    }

    // Go: compiler/program.go:143 GetGlobalTypingsCacheLocation
    fn get_global_typings_cache_location(&self) -> String {
        typings_location().to_string()
    }

    fn use_case_sensitive_file_names(&self) -> bool {
        crate::program::use_case_sensitive_file_names()
    }

    fn get_current_directory(&self) -> String {
        crate::program::get_current_directory().to_string()
    }

    // Go: compiler/program.go:189 GetProjectReferenceFromSource
    fn get_project_reference_from_source(
        &self,
        path: &tspath::Path,
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        crate::program::get_project_reference_from_source(path)
    }

    // Go: compiler/program.go:173 GetRedirectTargets
    fn get_redirect_targets(&self, path: &tspath::Path) -> Vec<String> {
        crate::program::get_redirect_targets(path)
    }

    // Go: compiler/program.go:181 GetSourceOfProjectReferenceIfOutputIncluded
    fn get_source_of_project_reference_if_output_included(&self, file: Node) -> String {
        crate::program::get_source_of_project_reference_if_output_included(file)
    }

    fn file_exists(&self, path: &str) -> bool {
        crate::program::file_exists(path)
    }

    // Go: compiler/program.go:148 GetNearestAncestorDirectoryWithPackageJson
    fn get_nearest_ancestor_directory_with_package_json(&self, dirname: &str) -> String {
        match get_package_scope_for_path(dirname) {
            Some(scoped) if scoped.exists() => scoped.package_directory.clone(),
            _ => String::new(),
        }
    }

    // Go: compiler/program.go:157 GetPackageJsonInfo
    fn get_package_json_info(&self, pkg_json_path: &str) -> Option<Arc<InfoCacheEntry>> {
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

#[cfg(test)]
mod tests {
    use super::*;

    // specstat1 skeptic: Go getPackageJsonInfo gives the cached entry the
    // caller's directory (packagejson/cache.go:158 WithPackageDirectory).
    // Two spellings of one directory have one cache key: here a trailing
    // separator, on a case-insensitive file system also another case. The
    // port gave the first spelling's entry as is, so GetPackageJsonInfo
    // (which wants the entry's directory to equal its own) found no
    // package.json, and GetNearestAncestorDirectoryWithPackageJson gave the
    // first spelling.
    #[test]
    fn a_package_json_lookup_keeps_the_spelling_of_its_directory() {
        let dir = std::env::temp_dir().join(format!(
            "goport-package-directory-spelling-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        for (path, text) in [
            (
                "tsconfig.json",
                r#"{"compilerOptions":{"types":[]},"files":["index.ts"]}"#,
            ),
            ("index.ts", "export const x = 1;\n"),
            ("node_modules/pkg/package.json", r#"{"name":"pkg"}"#),
        ] {
            let path = dir.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        }
        let dir = dir.to_string_lossy().replace('\\', "/");
        let program = crate::program::try_load_version(&format!("{dir}/tsconfig.json"), |_| {})
            .unwrap_or_else(|e| panic!("cannot load {dir}: {e}"));
        let _scope = crate::core::enter_program(Some(program));
        let pkg = format!("{dir}/node_modules/pkg");
        let thread_pkg = pkg.clone();
        let (with_separator, info, without_separator) = std::thread::spawn(move || {
            crate::core::set_thread_program(Some(program));
            let pkg = thread_pkg;
            (
                ProgramHost.get_nearest_ancestor_directory_with_package_json(&format!("{pkg}/")),
                ProgramHost
                    .get_package_json_info(&format!("{pkg}/package.json"))
                    .map(|entry| entry.package_directory.clone()),
                ProgramHost.get_nearest_ancestor_directory_with_package_json(&pkg),
            )
        })
        .join()
        .unwrap();
        drop(_scope);
        crate::program::release_program(program);
        let _ = std::fs::remove_dir_all(&dir);
        assert_eq!(with_separator, format!("{pkg}/"));
        assert_eq!(info, Some(pkg.clone()));
        assert_eq!(without_separator, pkg);
    }
}
