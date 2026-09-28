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

// Go: compiler/program.go:487 GetTypeCheckerForFileExclusive
// PORT: `f` runs with the checker of `file` on that checker's thread. Copy
// what `f` needs into it, and return plain data (handles, strings).
pub fn get_type_checker_for_file_exclusive<R: Send + 'static>(
    file: Node,
    f: impl FnOnce(&mut Checker) -> R + Send + 'static,
) -> R {
    with_type_checker_for_file(file, f)
}

/// The Go frontend program (Go `*compiler.Program`). Panics on the legacy
/// path, which has no Go frontend program, and off the loading thread.
fn frontend_program() -> &'static NewProgram {
    go_frontend_program().expect("the incremental program needs the Go frontend program")
}

// Go: compiler/program.go:195 GetParseFileRedirect
#[must_use]
pub fn get_parse_file_redirect(file_name: &str) -> String {
    frontend_program().get_parse_file_redirect(file_name)
}

// Go: compiler/program.go:1901 GetResolvedTypeReferenceDirectives
#[must_use]
pub fn get_resolved_type_reference_directives()
-> &'static FxHashMap<Path, ModeAwareCache<Rc<ResolvedTypeReferenceDirective>>> {
    frontend_program().get_resolved_type_reference_directives()
}

// Go: compiler/program.go:1555 GetDefaultLibFile
#[must_use]
pub fn get_default_lib_file(path: &Path) -> Option<&'static LibFile> {
    frontend_program()
        .lib_files
        .get(path)
        .map(|lib_file| &**lib_file)
}

// Go: compiler/program.go CommandLine
#[must_use]
pub fn command_line() -> &'static ParsedCommandLine {
    frontend_program().command_line()
}

// Go: compiler/program.go Host
#[must_use]
pub fn host() -> &'static Rc<dyn CompilerHost> {
    frontend_program().host()
}

// Go: compiler/program.go:156 PackageJsonCacheEntries
pub fn package_json_cache_entries(f: impl FnMut(&Path, &Rc<InfoCacheEntry>) -> bool) {
    frontend_program().package_json_cache_entries(f);
}
