//! U4a: the Go `*compiler.Program` methods that the incremental program
//! calls and `program.rs` does not expose yet.
//!
//! - `GetTypeCheckerForFileExclusive` (compiler/program.go:487). Go returns
//!   the checker and a release function. The port lends the file's checker
//!   to a callback on the checker's own thread
//!   (`program::with_type_checker_for_file`). Jobs for one checker run one at
//!   a time, which is what "exclusive" gives Go.
//! - Methods that read the Go frontend program (`GetParseFileRedirect`,
//!   `GetResolvedTypeReferenceDirectives`, `GetDefaultLibFile`,
//!   `CommandLine`, `Host`, `PackageJsonCacheEntries`). The frontend program
//!   is not thread-safe, so these work on the loading thread only, like
//!   `program.rs`.

use crate::frontend::prelude::*;

// Go: compiler/program.go:616 GetTypeCheckerForFileExclusive
// PORT: `f` runs with the checker of `file` on that checker's thread. Copy
// what `f` needs into it, and return plain data (handles, strings).
pub fn get_type_checker_for_file_exclusive<R: Send + 'static>(
    file: Node,
    f: impl FnOnce(&mut Checker) -> R + Send + 'static,
) -> R {
    with_type_checker_for_file(file, f)
}

/// The Go frontend program (Go `*compiler.Program`). Panics off the loading
/// thread.
fn frontend_program() -> Rc<NewProgram> {
    go_frontend_program().expect("the incremental program needs the Go frontend program")
}

// Go: compiler/program.go:211 GetParseFileRedirect
#[must_use]
pub fn get_parse_file_redirect(file_name: &str) -> String {
    frontend_program().get_parse_file_redirect(file_name)
}

// Go: compiler/program.go:2184 GetResolvedTypeReferenceDirectives (the
// resolutions of one file, in the map order)
// PORT: Go returns the program's map. The frontend program is not
// `'static`, so this returns the values of the file's entry. The map key is
// a `Path`; `Borrow<str>` looks it up without a copy of the path.
#[must_use]
pub fn get_resolved_type_reference_directives_in_file(
    path: &str,
) -> Vec<Rc<ResolvedTypeReferenceDirective>> {
    frontend_program()
        .get_resolved_type_reference_directives()
        .get(path)
        .map(|in_file| in_file.values().cloned().collect())
        .unwrap_or_default()
}

// Go: compiler/program.go:1792 GetDefaultLibFile
#[must_use]
pub fn get_default_lib_file(path: &Path) -> Option<Rc<LibFile>> {
    frontend_program().lib_files.get(path).cloned()
}

// Go: compiler/program.go CommandLine
#[must_use]
pub fn command_line() -> Rc<ParsedCommandLine> {
    frontend_program().command_line().clone()
}

// Go: compiler/program.go Host
#[must_use]
pub fn host() -> Rc<dyn CompilerHost> {
    frontend_program().host().clone()
}

// Go: compiler/program.go:167 PackageJsonCacheEntries
// PORT: Go's resolver cache also holds the package.json lookups of module
// specifier generation (program.go:147 GetNearestAncestorDirectoryWithPackageJson
// and :157 GetPackageJsonInfo), which checker threads make for declaration
// diagnostics and declaration emit. The port keeps those in the program's
// thread-safe `HostFsCache` (`modulespecifiers::host`). So they follow the
// resolver's entries here: each one whose key the resolver does not have.
// The order of the entries is not defined, as in Go.
pub fn package_json_cache_entries(mut f: impl FnMut(&Path, PackageJsonCacheEntry<'_>) -> bool) {
    let mut seen: FxHashSet<Path> = FxHashSet::default();
    let mut go_on = true;
    frontend_program().package_json_cache_entries(|key, entry| {
        seen.insert(key.clone());
        go_on = f(key, entry);
        go_on
    });
    if !go_on {
        return;
    }
    crate::program::with_host_fs_cache(|cache| {
        cache.package_json_entries(|key, package_directory, directory_exists, exists| {
            seen.contains(key)
                || f(
                    key,
                    PackageJsonCacheEntry {
                        package_directory,
                        directory_exists,
                        exists,
                    },
                )
        });
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modulespecifiers::{ModuleSpecifierGenerationHost, ProgramHost};

    /// Writes `files` (path, text) to a new dir under the system temp dir
    /// and returns the dir with `/` separators. `name` names the dir.
    fn write_project(name: &str, files: &[(&str, &str)]) -> String {
        let dir = std::env::temp_dir().join(format!("{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        for (path, text) in files {
            let path = dir.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        }
        dir.to_string_lossy().replace('\\', "/")
    }

    // specstat1 (realworld3 gap 3): the package.json lookups that module
    // specifier generation makes on a checker thread are entries of the
    // program's package.json cache, as in Go, where they go to the
    // resolver's cache (compiler/program.go:147). So the build info lists
    // them (incremental/program.go:454 ensurePackageJsonsForState). Here
    // no program file is in `pkg/dist`, so only the module specifier lookup
    // asks for `pkg/dist/package.json`.
    #[test]
    fn package_json_entries_have_module_specifier_lookups() {
        let dir = write_project(
            "goport-specifier-package-jsons",
            &[
                (
                    "tsconfig.json",
                    r#"{"compilerOptions":{"types":[]},"files":["index.ts"]}"#,
                ),
                ("index.ts", "export const x = 1;\n"),
                ("node_modules/pkg/package.json", r#"{"name":"pkg"}"#),
                ("node_modules/pkg/dist/index.d.ts", "export {};\n"),
            ],
        );
        let program = crate::program::try_load_version(&format!("{dir}/tsconfig.json"), |_| {})
            .unwrap_or_else(|e| panic!("cannot load {dir}: {e}"));
        let _scope = crate::core::enter_program(Some(program));
        let dist = format!("{dir}/node_modules/pkg/dist");
        let nearest = std::thread::spawn(move || {
            crate::core::set_thread_program(Some(program));
            ProgramHost.get_nearest_ancestor_directory_with_package_json(&dist)
        })
        .join()
        .unwrap();
        let mut entries = Vec::new();
        package_json_cache_entries(|key, entry| {
            entries.push((key.0.clone(), entry.directory_exists, entry.exists));
            true
        });
        drop(_scope);
        crate::program::release_program(program);
        let _ = std::fs::remove_dir_all(&dir);
        assert_eq!(nearest, format!("{dir}/node_modules/pkg"));
        for expected in [
            (
                format!("{dir}/node_modules/pkg/dist/package.json"),
                true,
                false,
            ),
            (format!("{dir}/node_modules/pkg/package.json"), true, true),
        ] {
            assert!(
                entries.contains(&expected),
                "{expected:?} is not in the package.json entries {entries:?}"
            );
        }
    }
}
