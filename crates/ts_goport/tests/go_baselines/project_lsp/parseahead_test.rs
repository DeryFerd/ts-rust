//! Parse ahead (src/frontend/compiler/files_parser.rs). Not a Go test: the
//! parse workers of the port's program loads parse queued files ahead of
//! the loader. A project that a snapshot clone makes again gets its files
//! from the parse cache, so its load starts no worker parse
//! (`CompilerHost::cached_source_file_refs`): the loader would not take
//! them, and their nodes would stay in the workers' AST arenas
//! (projsearch1b, hono's tsconfig.spec.json).
//!
//! The workers read the OS file system, so each test writes a project to a
//! temp directory and runs with no OS override (not `child_test!`).

use ts_goport::frontend::compiler::{PrefetchCounts, prefetch_counts};

use super::resolveahead_test::{file_uri, os_session, write};
use super::util::{edit, open};

/// A test in a child process with no OS override and two parse workers.
macro_rules! os_child_test {
    ($(#[$meta:meta])* fn $name:ident() $body:block) => {
        $(#[$meta])*
        #[test]
        fn $name() {
            let path = concat!(module_path!(), "::", stringify!($name));
            let test = path.split_once("::").map_or(path, |(_, rest)| rest);
            crate::support::child::run_test_in_child_with_env(
                test,
                &[("GOPORT_PARSE_THREADS", "2")],
                || $body,
            );
        }
    };
}

const MAIN: &str = "export const foo = 1;\n";
const HELPER: &str = "export const bar = 2;\n";
const TEST: &str = "import { foo } from './main';\nimport { bar } from './helper';\nfoo + bar;\n";

/// A solution with a build and a spec project over one `src`, as in hono.
/// The spec project has another jsx option, so its parse cache keys differ
/// from the build project's.
const FILES: &[(&str, &str)] = &[
    (
        "tsconfig.json",
        r#"{ "files": [], "references": [{ "path": "./tsconfig.build.json" }, { "path": "./tsconfig.spec.json" }] }"#,
    ),
    (
        "tsconfig.build.json",
        r#"{ "compilerOptions": { "noLib": true, "types": [] }, "include": ["src/**/*.ts"], "exclude": ["src/**/*.test.ts"] }"#,
    ),
    (
        "tsconfig.spec.json",
        r#"{ "compilerOptions": { "noLib": true, "types": [], "jsx": "react-jsx" }, "include": ["src/**/*.ts"] }"#,
    ),
    ("src/main.ts", MAIN),
    ("src/helper.ts", HELPER),
    ("src/main.test.ts", TEST),
];

/// The change of the counts from `before` to now.
fn since(before: PrefetchCounts) -> PrefetchCounts {
    let now = prefetch_counts();
    PrefetchCounts {
        pool_loads: now.pool_loads - before.pool_loads,
        cached_loads: now.cached_loads - before.cached_loads,
        reads: now.reads - before.reads,
        untaken: now.untaken - before.untaken,
        untaken_bytes: now.untaken_bytes - before.untaken_bytes,
    }
}

os_child_test! {
    fn made_again_project_parses_nothing_ahead() {
        let root = std::env::temp_dir().join(format!(
            "ts_goport_parse_ahead_{}_made_again",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&root);
        for (name, text) in FILES {
            write(&root.to_string_lossy(), name, text);
        }
        let root = std::fs::canonicalize(&root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        let session = os_session(&root);
        let main = file_uri(&root, "src/main.ts");
        let helper = file_uri(&root, "src/helper.ts");
        let test = file_uri(&root, "src/main.test.ts");
        let start = prefetch_counts();

        // The search makes and loads both projects of the level. The spec
        // project's files are not in the cache with its jsx option, so its
        // first load parses ahead too, and takes the parses. Then the clone
        // deletes it (main.ts is in the build project), and its files stay
        // in the cache, as in Go.
        let before = prefetch_counts();
        open(&session, &main, MAIN);
        let first = since(before);
        assert_eq!(
            (first.pool_loads, first.cached_loads),
            (2, 0),
            "build and spec parse ahead: {first:?}"
        );

        // The search makes the spec project again. The cache has every file
        // of it with its options, so its load starts no worker.
        let before = prefetch_counts();
        open(&session, &helper, HELPER);
        let second = since(before);
        assert_eq!(
            (second.pool_loads, second.cached_loads, second.reads),
            (0, 1, 0),
            "the spec project made again parses nothing ahead: {second:?}"
        );

        // An open file whose text is not the cached text is not a cached
        // file, so the spec load parses ahead again.
        edit(&session, &helper, 2, (0, 0), (0, 0), "// edited\n");
        let before = prefetch_counts();
        open(&session, &test, TEST);
        let third = since(before);
        assert_eq!(
            (third.pool_loads, third.cached_loads),
            (1, 0),
            "an edited open file is parsed ahead: {third:?}"
        );

        let all = since(start);
        assert_eq!(
            (all.untaken, all.untaken_bytes),
            (0, 0),
            "every worker parse was taken: {all:?}"
        );
        drop(session);
        std::fs::remove_dir_all(&root).unwrap();
    }
}
