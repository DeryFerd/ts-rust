//! Rust port of the Go tests of `internal/project` (with `ata`,
//! `background`, `dirty`, `logging`), `internal/lsp` and
//! `internal/ls/autoimport`, and their helpers `projecttestutil`,
//! `lsptestutil` and `autoimporttestutil`.
//!
//! PORT: each Go leaf subtest (`t.Run`) is one `#[test]`, so a port bug
//! can be marked `#[ignore = "bug: S4-..."]` on the one subtest that shows
//! it. `t.Parallel()` is dropped. The expected values are the Go test
//! literals.
//!
//! A test that builds a program runs in a child process of its own
//! (`child_test!`, `support::child::run_test_in_child`): parse workers and
//! module specifier code read `osvfs_fs()`, and the OS override that
//! points it at the test map file system is for the whole process
//! (`projecttestutil::install_fs_override`).
//!
//! Test names are `project_lsp::<go file>::<go subtest path>`.

/// A `#[test]` that runs its body in a child process with the map file
/// system override (see the module comment). The libtest name comes from
/// `module_path!()` without the crate name.
macro_rules! child_test {
    ($(#[$meta:meta])* fn $name:ident() $body:block) => {
        $(#[$meta])*
        #[test]
        fn $name() {
            let path = concat!(module_path!(), "::", stringify!($name));
            let test = path.split_once("::").map_or(path, |(_, rest)| rest);
            crate::support::child::run_test_in_child(test, || {
                crate::project_lsp::projecttestutil::install_fs_override();
                $body
            });
        }
    };
}

pub(crate) mod projecttestutil;
pub(crate) mod util;

mod ata_discovertypings_test;
mod ata_installnpmpackages_test;
mod ata_test;
mod ata_validatepackagename_test;
mod background_queue_test;
mod bulkcache_test;
mod configfilechanges_test;
mod customconfigfilename_test;
mod dirty_syncmap_test;
mod extendedconfigcache_test;
mod logging_logtree_test;
mod lsp_dynamic_queue_test;
mod lsp_stack_sanitizer_test;
mod overlayfs_test;
mod project_test;
mod projectcollectionbuilder_test;
mod projectcollectiondefaultproject_test;
mod projectlifetime_test;
mod projectreferencesprogram_test;
mod refcountcache_test;
mod session_test;
mod snapshot_test;
mod untitled_test;
mod watch_test;
mod watchtimeout_test;
