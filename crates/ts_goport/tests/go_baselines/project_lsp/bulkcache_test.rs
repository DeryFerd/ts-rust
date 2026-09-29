//! Port of Go `internal/project/bulkcache_test.go` (`TestBulkCacheInvalidation`).

use std::rc::Rc;

use ts_goport::flags::ScriptTarget;
use ts_goport::lsp::lsproto;
use ts_goport::options::Tristate;
use ts_goport::project::Kind;

use super::projecttestutil::{self, FileMap, files};
use super::util::*;

const INDEX: &str = r#"import { helper } from "./helper"; console.log(helper);"#;
const INDEX_URI: &str = "file:///project/src/index.ts";

// Go: bulkcache_test.go:24 baseFiles
fn base_files() -> FileMap {
    files(&[
        (
            "/project/tsconfig.json",
            r#"{
			"compilerOptions": {
				"strict": true,
				"target": "es2015",
				"types": ["node"]
			},
			"include": ["src/**/*"]
		}"#,
        ),
        ("/project/src/index.ts", INDEX),
        ("/project/src/helper.ts", r#"export const helper = "test";"#),
        (
            "/project/src/utils/lib.ts",
            r#"export function util() { return "util"; }"#,
        ),
        (
            "/project/node_modules/@types/node/index.d.ts",
            r#"import "./fs"; import "./console";"#,
        ),
        ("/project/node_modules/@types/node/fs.d.ts", ""),
        ("/project/node_modules/@types/node/console.d.ts", ""),
    ])
}

const ESNEXT_TSCONFIG: &str = r#"{
			"compilerOptions": {
				"strict": true,
				"target": "esnext",
				"types": ["node"]
			},
			"include": ["src/**/*"]
		}"#;

// Go: bulkcache_test.go:44 TestBulkCacheInvalidation/large number of node_modules changes invalidates only node_modules cache (test)
fn node_modules_changes(
    file_events: Vec<lsproto::FileEvent>,
    expect_node_modules_invalidation: bool,
) {
    let (session, utils) = projecttestutil::setup(base_files());

    // Open a file to create the project
    open(&session, INDEX_URI, INDEX);

    // Get initial snapshot and verify config
    let p = program(&session, INDEX_URI);
    assert_eq!(p.options().target, ScriptTarget::ES2015);

    let config_before = session.snapshot().config_file_registry.clone();

    // Update tsconfig.json on disk to test that configs don't get reloaded
    utils
        .fs()
        .write_file("/project/tsconfig.json", ESNEXT_TSCONFIG)
        .unwrap();
    // Update fs.d.ts in node_modules
    utils
        .fs()
        .write_file("/project/node_modules/@types/node/fs.d.ts", "new text")
        .unwrap();

    // Process the excessive node_modules changes
    session.did_change_watched_files(&bg(), &file_events);

    // Get language service again to trigger snapshot update
    let p = program(&session, INDEX_URI);

    let snapshot_after = session.snapshot();
    let config_after = snapshot_after.config_file_registry.clone();

    // Config should NOT have been reloaded (target should remain ES2015, not esnext)
    assert_eq!(
        p.options().target,
        ScriptTarget::ES2015,
        "Config should not have been reloaded for node_modules-only changes"
    );

    // Config registry should be the same instance (no configs reloaded)
    assert!(
        Rc::ptr_eq(&config_before, &config_after),
        "Config registry should not have changed for node_modules-only changes"
    );

    let fs_dts_text = snapshot_after
        .get_file("/project/node_modules/@types/node/fs.d.ts")
        .expect("fs.d.ts")
        .content();
    if expect_node_modules_invalidation {
        assert_eq!(fs_dts_text, "new text");
    } else {
        assert_eq!(fs_dts_text, "");
    }
}

child_test! {
    // Go: bulkcache_test.go:96 TestBulkCacheInvalidation/large number of node_modules changes invalidates only node_modules cache/with file existing in cache
    fn node_modules_changes_with_file_existing_in_cache() {
        let mut file_events = generate_file_events(
            1001,
            "file:///project/node_modules/generated/file%d.js",
            CREATED,
        );
        // Include two files in the program to trigger a full program creation.
        // Exclude fs.d.ts to show that its content still gets invalidated.
        file_events.push(lsproto::FileEvent {
            uri: uri("file:///project/node_modules/@types/node/index.d.ts"),
            type_: CHANGED,
        });
        file_events.push(lsproto::FileEvent {
            uri: uri("file:///project/node_modules/@types/node/console.d.ts"),
            type_: CHANGED,
        });

        node_modules_changes(file_events, true);
    }
}

child_test! {
    // Go: bulkcache_test.go:112 TestBulkCacheInvalidation/large number of node_modules changes invalidates only node_modules cache/without file existing in cache
    fn node_modules_changes_without_file_existing_in_cache() {
        let file_events = generate_file_events(
            1001,
            "file:///project/node_modules/generated/file%d.js",
            CREATED,
        );
        node_modules_changes(file_events, false);
    }
}

// Go: bulkcache_test.go:121 TestBulkCacheInvalidation/large number of changes outside node_modules (test)
fn outside_node_modules_changes(file_events: Vec<lsproto::FileEvent>, expect_config_reload: bool) {
    let (session, utils) = projecttestutil::setup(base_files());

    // Open a file to create the project
    open(&session, INDEX_URI, INDEX);

    // Get initial state
    let p = program(&session, INDEX_URI);
    assert_eq!(p.options().target, ScriptTarget::ES2015);

    // Update tsconfig.json on disk
    utils
        .fs()
        .write_file("/project/tsconfig.json", ESNEXT_TSCONFIG)
        .unwrap();
    // Add root file
    utils
        .fs()
        .write_file("/project/src/rootFile.ts", r#"console.log("root file")"#)
        .unwrap();

    session.did_change_watched_files(&bg(), &file_events);
    let p = program(&session, INDEX_URI);

    if expect_config_reload {
        assert_eq!(
            p.options().target,
            ScriptTarget::ES_NEXT,
            "Config should have been reloaded for changes outside node_modules"
        );
        assert!(
            has_file(&p, "/project/src/rootFile.ts"),
            "New root file should be present"
        );
    } else {
        assert_eq!(
            p.options().target,
            ScriptTarget::ES2015,
            "Config should not have been reloaded for changes outside node_modules"
        );
        assert!(
            !has_file(&p, "/project/src/rootFile.ts"),
            "New root file should not be present"
        );
    }
}

child_test! {
    // Go: bulkcache_test.go:159 TestBulkCacheInvalidation/large number of changes outside node_modules/with event matching include glob
    fn outside_node_modules_with_event_matching_include_glob() {
        let mut file_events = generate_file_events(1001, "file:///project/generated/file%d.ts", CREATED);
        file_events.push(lsproto::FileEvent {
            uri: uri("file:///project/src/rootFile.ts"),
            type_: CREATED,
        });
        outside_node_modules_changes(file_events, true);
    }
}

child_test! {
    // Go: bulkcache_test.go:169 TestBulkCacheInvalidation/large number of changes outside node_modules/without event matching include glob
    fn outside_node_modules_without_event_matching_include_glob() {
        let file_events = generate_file_events(1001, "file:///project/generated/file%d.ts", CREATED);
        outside_node_modules_changes(file_events, false);
    }
}

child_test! {
    // Go: bulkcache_test.go:176 TestBulkCacheInvalidation/large number of changes outside node_modules causes project reevaluation
    fn large_number_of_changes_outside_node_modules_causes_project_reevaluation() {
        let (session, utils) = projecttestutil::setup(base_files());
        let lib_uri = "file:///project/src/utils/lib.ts";

        // Open a file that will initially use the root tsconfig
        open(&session, lib_uri, r#"export function util() { return "util"; }"#);

        // Initially, the file should use the root project (strict mode)
        assert_eq!(
            default_project_name(&session, lib_uri),
            "/project/tsconfig.json",
            "Should initially use root tsconfig"
        );

        // Get language service to verify initial strict mode
        let p = program(&session, lib_uri);
        assert_eq!(
            p.options().strict,
            Tristate::True,
            "Should initially use strict mode from root config"
        );

        // Now create the nested tsconfig (this would normally be detected, but we'll simulate a missed event)
        utils
            .fs()
            .write_file(
                "/project/src/utils/tsconfig.json",
                r#"{
			"compilerOptions": {
				"strict": false,
				"target": "esnext"
			}
		}"#,
            )
            .unwrap();

        // Create excessive changes to trigger bulk invalidation
        let file_events = generate_file_events(1001, "file:///project/src/generated/file%d.ts", CREATED);

        // Process the excessive changes - this should trigger project reevaluation
        session.did_change_watched_files(&bg(), &file_events);

        // Get language service - this should now find the nested config and switch projects
        let p = program(&session, lib_uri);

        // The file should now use the nested tsconfig
        assert_eq!(
            default_project_name(&session, lib_uri),
            "/project/src/utils/tsconfig.json",
            "Should now use nested tsconfig after bulk invalidation"
        );
        assert_eq!(
            p.options().strict,
            Tristate::False,
            "Should now use non-strict mode from nested config"
        );
        assert_eq!(
            p.options().target,
            ScriptTarget::ES_NEXT,
            "Should use esnext target from nested config"
        );
    }
}

// Go: bulkcache_test.go:223 TestBulkCacheInvalidation/config file names cache (test)
fn config_file_names_cache(file_events: Vec<lsproto::FileEvent>, expect_config_discovery: bool) {
    let (session, utils) = projecttestutil::setup(files(&[(
        "/project/src/index.ts",
        r#"console.log("test");"#,
    )]));

    // Open file without tsconfig - should create inferred project
    open(
        &session,
        "file:///project/src/index.ts",
        r#"console.log("test");"#,
    );

    assert!(
        has_inferred_project(&session),
        "Should have inferred project"
    );
    assert_eq!(
        default_project_kind(&session, "file:///project/src/index.ts"),
        Kind::INFERRED
    );

    // Create a tsconfig that would affect this file (simulating a missed creation event)
    utils
        .fs()
        .write_file(
            "/project/tsconfig.json",
            r#"{
		"compilerOptions": {
			"strict": true
		},
		"include": ["src/**/*"]
	}"#,
        )
        .unwrap();

    // Process the changes
    session.did_change_watched_files(&bg(), &file_events);

    // Get language service to trigger config discovery
    let _ = language_service(&session, "file:///project/src/index.ts");

    let snapshot = session.snapshot();
    let new_project = snapshot
        .get_default_project(&uri("file:///project/src/index.ts"))
        .expect("default project");

    // Check expected behavior
    if expect_config_discovery {
        // Should now use configured project instead of inferred
        assert_eq!(
            new_project.borrow().kind,
            Kind::CONFIGURED,
            "Should now use configured project after cache invalidation"
        );
        assert_eq!(
            new_project.borrow().name(),
            "/project/tsconfig.json",
            "Should use the newly discovered tsconfig"
        );
    } else {
        // Should still use inferred project (config file names cache not cleared)
        let inferred = snapshot
            .project_collection
            .inferred_project()
            .expect("inferred project");
        assert!(
            Rc::ptr_eq(&new_project, &inferred),
            "Should still use inferred project after node_modules-only changes"
        );
    }
}

child_test! {
    // Go: bulkcache_test.go:266 TestBulkCacheInvalidation/config file names cache/excessive changes only in node_modules does not affect config file names cache
    fn config_file_names_cache_excessive_changes_only_in_node_modules_does_not_affect_config_file_names_cache() {
        let file_events = generate_file_events(
            1001,
            "file:///project/node_modules/generated/file%d.js",
            CREATED,
        );
        config_file_names_cache(file_events, false);
    }
}

child_test! {
    // Go: bulkcache_test.go:272 TestBulkCacheInvalidation/config file names cache/excessive changes outside node_modules clears config file names cache
    fn config_file_names_cache_excessive_changes_outside_node_modules_clears_config_file_names_cache() {
        let mut file_events = generate_file_events(1001, "file:///project/src/generated/file%d.ts", CREATED);
        // Presence of any tsconfig.json file event triggers rediscovery for config for all open files
        file_events.push(lsproto::FileEvent {
            uri: uri("file:///project/src/generated/tsconfig.json"),
            type_: CREATED,
        });
        config_file_names_cache(file_events, true);
    }
}

child_test! {
    // Go: bulkcache_test.go:285 TestBulkCacheInvalidation/excessive changes in dist folder do not invalidate
    fn excessive_changes_in_dist_folder_do_not_invalidate() {
        let (session, utils) = projecttestutil::setup(files(&[(
            "/project/src/index.ts",
            r#"console.log("test");"#,
        )]));

        // Open file without tsconfig - should create inferred project
        open(&session, "file:///project/src/index.ts", r#"console.log("test");"#);

        assert_eq!(default_project_kind(&session, "file:///project/src/index.ts"), Kind::INFERRED);

        // Create a tsconfig that would affect this file (simulating a missed creation event)
        // This should NOT be discovered after dist-folder changes
        utils
            .fs()
            .write_file(
                "/project/tsconfig.json",
                r#"{
			"compilerOptions": {
				"strict": true
			},
			"include": ["src/**/*"]
		}"#,
            )
            .unwrap();

        // Create excessive changes in dist folder only
        let file_events = generate_file_events(1001, "file:///project/dist/generated/file%d.js", CREATED);
        session.did_change_watched_files(&bg(), &file_events);

        // File should still use inferred project (config file names cache NOT cleared for dist changes)
        let _ = language_service(&session, "file:///project/src/index.ts");

        assert_eq!(
            default_project_kind(&session, "file:///project/src/index.ts"),
            Kind::INFERRED,
            "dist-folder changes should not cause config discovery"
        );
    }
}
