//! Go: `internal/execute/watchmanager/watchmanager_test.go` (added by
//! tsgo#4658).

use ts_goport::execute::watchmanager::new_dir_watch_set;
use ts_goport::frontend::tspath::ComparePathsOptions;

// Go: watchmanager_test.go:11 caseSensitiveOpts
fn case_sensitive_opts() -> ComparePathsOptions {
    ComparePathsOptions {
        use_case_sensitive_file_names: true,
        current_directory: "/repo".to_string(),
    }
}

// Go: watchmanager_test.go:12 caseInsensitiveOpts
fn case_insensitive_opts() -> ComparePathsOptions {
    ComparePathsOptions {
        use_case_sensitive_file_names: false,
        current_directory: "/repo".to_string(),
    }
}

// Go: watchmanager_test.go:18 TestDirWatchSetCoverage
/// TestDirWatchSetCoverage checks the core coverage rules: a recursive watch
/// covers itself and all descendants, while a non-recursive watch covers only
/// itself. Ancestors and unrelated paths are never covered.
#[test]
fn test_dir_watch_set_coverage() {
    let mut set = new_dir_watch_set(case_sensitive_opts());
    set.set("/repo/src", true); // recursive
    set.set("/repo/config", false); // non-recursive
    set.set("/repo/node_modules/a", false); // non-recursive

    let tests: [(&str, bool); 9] = [
        ("/repo/src", true),             // exact recursive
        ("/repo/src/nested", true),      // descendant of recursive
        ("/repo/src/nested/deep", true), // deep descendant of recursive
        ("/repo/config", true),          // exact non-recursive
        ("/repo/config/nested", false),  // descendant of non-recursive: NOT covered
        ("/repo/node_modules/a", true),  // exact non-recursive
        ("/repo/node_modules/b", false), // sibling, absent
        ("/repo", false),                // ancestor of watched dirs: NOT covered
        ("/other", false),               // unrelated
    ];
    for (dir, want) in tests {
        assert_eq!(set.covered(dir), want, "Covered({dir:?})");
    }
}

// Go: watchmanager_test.go:47 TestDirWatchSetCaseSensitive
/// TestDirWatchSetCaseSensitive verifies that on a case-sensitive filesystem a
/// differently-cased directory is a distinct, uncovered directory.
#[test]
fn test_dir_watch_set_case_sensitive() {
    let mut set = new_dir_watch_set(case_sensitive_opts());
    set.set("/repo/node_modules/a", false);
    set.set("/repo/Src", true);

    assert!(set.covered("/repo/node_modules/a"));
    assert!(
        !set.covered("/repo/node_modules/A"),
        "case-sensitive FS must not cover differently-cased dir"
    );
    assert!(
        set.covered("/repo/Src/nested"),
        "recursive descendant with matching case is covered"
    );
    assert!(
        !set.covered("/repo/src/nested"),
        "case-sensitive FS must not cover differently-cased descendant"
    );
}

// Go: watchmanager_test.go:62 TestDirWatchSetCaseInsensitive
/// TestDirWatchSetCaseInsensitive verifies that on a case-insensitive filesystem
/// coverage ignores casing for both exact matches and recursive containment.
#[test]
fn test_dir_watch_set_case_insensitive() {
    let mut set = new_dir_watch_set(case_insensitive_opts());
    set.set("/repo/node_modules/a", false);
    set.set("/repo/Src", true);

    assert!(
        set.covered("/repo/node_modules/A"),
        "exact match should be case-insensitive"
    );
    assert!(
        set.covered("/REPO/NODE_MODULES/a"),
        "exact match should be case-insensitive across components"
    );
    assert!(
        set.covered("/repo/src/nested/deep"),
        "recursive containment should be case-insensitive"
    );
}

// Go: watchmanager_test.go:77 TestDirWatchSetCanonicalDedup
/// TestDirWatchSetCanonicalDedup verifies that on a case-insensitive filesystem
/// directories that differ only by casing collapse to a single canonical entry,
/// while a case-sensitive filesystem keeps them distinct.
#[test]
fn test_dir_watch_set_canonical_dedup() {
    let mut insensitive = new_dir_watch_set(case_insensitive_opts());
    insensitive.set("/repo/Node_Modules/PkgName", false);
    insensitive.set("/repo/node_modules/pkgname", false); // same dir, different casing

    let dirs = insensitive.dirs();
    assert_eq!(
        dirs.len(),
        1,
        "differently-cased dirs must collapse to one entry"
    );
    let original = dirs.contains_key("/repo/Node_Modules/PkgName");
    assert!(
        original,
        "Dirs must retain the original spelling used for registration"
    );

    let mut sensitive = new_dir_watch_set(case_sensitive_opts());
    sensitive.set("/repo/Node_Modules/PkgName", false);
    sensitive.set("/repo/node_modules/pkgname", false); // distinct dirs when case-sensitive
    assert_eq!(
        sensitive.dirs().len(),
        2,
        "case-sensitive FS keeps differently-cased dirs distinct"
    );
}

// Go: watchmanager_test.go:97 TestDirWatchSetUpgradeToRecursive
/// TestDirWatchSetUpgradeToRecursive verifies that upgrading a directory from
/// non-recursive to recursive begins covering its descendants.
#[test]
fn test_dir_watch_set_upgrade_to_recursive() {
    let mut set = new_dir_watch_set(case_sensitive_opts());
    set.set("/repo/src", false);
    assert!(set.covered("/repo/src"));
    assert!(
        !set.covered("/repo/src/nested"),
        "descendant not covered while non-recursive"
    );

    set.set("/repo/src", true);
    assert!(
        set.covered("/repo/src/nested"),
        "descendant covered after upgrade to recursive"
    );
    assert!(set.dirs().get("/repo/src").copied().unwrap_or(false));
}

// Go: watchmanager_test.go:112 TestDirWatchSetNeverDowngrades
/// TestDirWatchSetNeverDowngrades verifies a recursive watch is not downgraded by
/// a subsequent non-recursive Set of the same directory.
#[test]
fn test_dir_watch_set_never_downgrades() {
    let mut set = new_dir_watch_set(case_sensitive_opts());
    set.set("/repo/src", true);
    set.set("/repo/src", false);

    assert!(set.dirs().get("/repo/src").copied().unwrap_or(false));
    assert!(
        set.covered("/repo/src/nested"),
        "recursive coverage retained after non-recursive Set"
    );
}

// Go: watchmanager_test.go:125 TestDirWatchSetDirs
/// TestDirWatchSetDirs verifies the emitted map reflects every added directory
/// with the expected recursive flags.
#[test]
fn test_dir_watch_set_dirs() {
    let mut set = new_dir_watch_set(case_sensitive_opts());
    set.set("/repo/a", false);
    set.set("/repo/b", true);
    set.set("/repo/a", false); // duplicate non-recursive add is idempotent

    let dirs = set.dirs();
    assert_eq!(dirs.len(), 2);
    assert!(!dirs.get("/repo/a").copied().unwrap_or(false));
    assert!(dirs.get("/repo/b").copied().unwrap_or(false));
}
