//! Port of Go `internal/project/ata/discovertypings_test.go` (`TestDiscoverTypings`).
//! No program is built, so the tests run in the test process.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};
use ts_goport::frontend::core_ext::TypeAcquisition;
use ts_goport::frontend::semver;
use ts_goport::options::{CompilerOptions, Tristate};
use ts_goport::project::ata::{self, CachedTyping, TypingsInfo};
use ts_goport::project::logging;

use super::projecttestutil::{TEST_TYPINGS_LOCATION, types_registry_config};
use crate::support::vfstest;

const APP: &str = "/home/src/projects/project/app.js";
const ROOT: &str = "/home/src/projects/project";

type Registry = FxHashMap<String, Option<FxHashMap<String, String>>>;
type Cache = RefCell<IndexMap<String, Rc<CachedTyping>>>;

/// Go `&ata.TypingsInfo{CompilerOptions: &core.CompilerOptions{}, TypeAcquisition: &core.TypeAcquisition{Enable: core.TSTrue}, UnresolvedImports: ...}`.
fn typings_info(unresolved_imports: &[&str]) -> TypingsInfo {
    TypingsInfo {
        type_acquisition: Some(Rc::new(TypeAcquisition {
            enable: Tristate::True,
            ..Default::default()
        })),
        compiler_options: Some(Rc::new(CompilerOptions::default())),
        unresolved_imports: if unresolved_imports.is_empty() {
            None
        } else {
            Some(Rc::new(
                unresolved_imports
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<FxHashSet<_>>(),
            ))
        },
    }
}

/// Go `ata.DiscoverTypings(fs, logger, info, fileNames, projectRootPath, cache, registry)`.
fn discover(
    files: &[(&str, &str)],
    info: &TypingsInfo,
    file_names: &[&str],
    cache: &Cache,
    registry: &Registry,
) -> (Vec<String>, Vec<String>, Vec<String>) {
    let logger = logging::new_log_tree("DiscoverTypings").expect("log tree");
    let fs = vfstest::from_map(
        files.iter().copied(),
        false, /*useCaseSensitiveFileNames*/
    );
    let file_names: Vec<String> = file_names.iter().map(|s| s.to_string()).collect();
    ata::discover_typings(&*fs, &*logger, info, &file_names, ROOT, cache, registry)
}

fn set(items: &[String]) -> BTreeSet<String> {
    items.iter().cloned().collect()
}

fn set_of(items: &[&str]) -> BTreeSet<String> {
    items.iter().map(|s| s.to_string()).collect()
}

fn watch_dirs() -> Vec<String> {
    vec![
        "/home/src/projects/project/bower_components".to_string(),
        "/home/src/projects/project/node_modules".to_string(),
    ]
}

/// Go `projecttestutil.TypesRegistryConfig()` as a registry entry.
fn registry_config() -> FxHashMap<String, String> {
    types_registry_config()
        .into_iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect()
}

fn cache_entry(cache: &Cache, name: &str, location: &str, version: &str) {
    cache.borrow_mut().insert(
        name.to_string(),
        Rc::new(CachedTyping {
            typings_location: location.to_string(),
            version: semver::must_parse_version(version),
        }),
    );
}

// Go: discovertypings_test.go:19 TestDiscoverTypings/should use mappings from safe list
#[test]
fn should_use_mappings_from_safe_list() {
    let (cached_typing_paths, new_typing_names, files_to_watch) = discover(
        &[
            (APP, ""),
            ("/home/src/projects/project/jquery.js", ""),
            ("/home/src/projects/project/chroma.min.js", ""),
        ],
        &typings_info(&[]),
        &[
            APP,
            "/home/src/projects/project/jquery.js",
            "/home/src/projects/project/chroma.min.js",
        ],
        &Cache::default(),
        &Registry::default(),
    );
    assert!(cached_typing_paths.is_empty());
    assert_eq!(set(&new_typing_names), set_of(&["jquery", "chroma-js"]));
    assert_eq!(files_to_watch, watch_dirs());
}

// Go: discovertypings_test.go:51 TestDiscoverTypings/should return node for core modules
#[test]
fn should_return_node_for_core_modules() {
    let (cached_typing_paths, new_typing_names, files_to_watch) = discover(
        &[(APP, "")],
        &typings_info(&["assert", "somename"]),
        &[APP],
        &Cache::default(),
        &Registry::default(),
    );
    assert!(cached_typing_paths.is_empty());
    assert_eq!(set(&new_typing_names), set_of(&["node", "somename"]));
    assert_eq!(files_to_watch, watch_dirs());
}

// Go: discovertypings_test.go:83 TestDiscoverTypings/should use cached locations
#[test]
fn should_use_cached_locations() {
    let cache = Cache::default();
    cache_entry(
        &cache,
        "node",
        "/home/src/projects/project/node.d.ts",
        "1.3.0",
    );
    let mut registry = Registry::default();
    registry.insert("node".to_string(), Some(registry_config()));
    let (cached_typing_paths, new_typing_names, files_to_watch) = discover(
        &[(APP, ""), ("/home/src/projects/project/node.d.ts", "")],
        &typings_info(&["fs", "bar"]),
        &[APP],
        &cache,
        &registry,
    );
    assert_eq!(
        cached_typing_paths,
        ["/home/src/projects/project/node.d.ts"]
    );
    assert_eq!(set(&new_typing_names), set_of(&["bar"]));
    assert_eq!(files_to_watch, watch_dirs());
}

// Go: discovertypings_test.go:125 TestDiscoverTypings/should gracefully handle packages that have been removed from the types-registry
#[test]
fn should_gracefully_handle_packages_that_have_been_removed_from_the_types_registry() {
    let cache = Cache::default();
    cache_entry(
        &cache,
        "node",
        "/home/src/projects/project/node.d.ts",
        "1.3.0",
    );
    let (cached_typing_paths, new_typing_names, files_to_watch) = discover(
        &[(APP, ""), ("/home/src/projects/project/node.d.ts", "")],
        &typings_info(&["fs", "bar"]),
        &[APP],
        &cache,
        &Registry::default(),
    );
    assert!(cached_typing_paths.is_empty());
    assert_eq!(set(&new_typing_names), set_of(&["node", "bar"]));
    assert_eq!(files_to_watch, watch_dirs());
}

// Go: discovertypings_test.go:164 TestDiscoverTypings/should search only 2 levels deep
#[test]
fn should_search_only_2_levels_deep() {
    let (cached_typing_paths, new_typing_names, files_to_watch) = discover(
        &[
            (APP, ""),
            (
                "/home/src/projects/project/node_modules/a/package.json",
                r#"{ "name": "a" }"#,
            ),
            (
                "/home/src/projects/project/node_modules/a/b/package.json",
                r#"{ "name": "b" }"#,
            ),
        ],
        &typings_info(&[]),
        &[APP],
        &Cache::default(),
        &Registry::default(),
    );
    assert!(cached_typing_paths.is_empty());
    assert_eq!(set(&new_typing_names), set_of(&["a"]));
    assert_eq!(files_to_watch, watch_dirs());
}

// Go: discovertypings_test.go:195 TestDiscoverTypings/should support scoped packages
#[test]
fn should_support_scoped_packages() {
    let (cached_typing_paths, new_typing_names, files_to_watch) = discover(
        &[
            (APP, ""),
            (
                "/home/src/projects/project/node_modules/@a/b/package.json",
                r#"{ "name": "@a/b" }"#,
            ),
        ],
        &typings_info(&[]),
        &[APP],
        &Cache::default(),
        &Registry::default(),
    );
    assert!(cached_typing_paths.is_empty());
    assert_eq!(set(&new_typing_names), set_of(&["@a/b"]));
    assert_eq!(files_to_watch, watch_dirs());
}

// Go: discovertypings_test.go:225 TestDiscoverTypings/should install expired typings
#[test]
fn should_install_expired_typings() {
    let cache = Cache::default();
    cache_entry(
        &cache,
        "node",
        &format!("{TEST_TYPINGS_LOCATION}/node_modules/@types/node/index.d.ts"),
        "1.3.0",
    );
    cache_entry(
        &cache,
        "commander",
        &format!("{TEST_TYPINGS_LOCATION}/node_modules/@types/commander/index.d.ts"),
        "1.0.0",
    );
    let mut registry = Registry::default();
    registry.insert("node".to_string(), Some(registry_config()));
    registry.insert("commander".to_string(), Some(registry_config()));
    let (cached_typing_paths, new_typing_names, files_to_watch) = discover(
        &[(APP, "")],
        &typings_info(&["http", "commander"]),
        &[APP],
        &cache,
        &registry,
    );
    assert_eq!(
        cached_typing_paths,
        ["/home/src/Library/Caches/typescript/node_modules/@types/node/index.d.ts"]
    );
    assert_eq!(set(&new_typing_names), set_of(&["commander"]));
    assert_eq!(files_to_watch, watch_dirs());
}

// Go: discovertypings_test.go:272 TestDiscoverTypings/should install expired typings with prerelease version of tsserver
#[test]
fn should_install_expired_typings_with_prerelease_version_of_tsserver() {
    let cache = Cache::default();
    cache_entry(
        &cache,
        "node",
        &format!("{TEST_TYPINGS_LOCATION}/node_modules/@types/node/index.d.ts"),
        "1.0.0",
    );
    let mut config = registry_config();
    config.remove(&format!("ts{}", ts_goport::core::version_major_minor()));
    let mut registry = Registry::default();
    registry.insert("node".to_string(), Some(config));

    let (cached_typing_paths, new_typing_names, files_to_watch) = discover(
        &[(APP, "")],
        &typings_info(&["http"]),
        &[APP],
        &cache,
        &registry,
    );
    assert!(cached_typing_paths.is_empty());
    assert_eq!(set(&new_typing_names), set_of(&["node"]));
    assert_eq!(files_to_watch, watch_dirs());
}

// Go: discovertypings_test.go:314 TestDiscoverTypings/prerelease typings are properly handled
#[test]
fn prerelease_typings_are_properly_handled() {
    let cache = Cache::default();
    cache_entry(
        &cache,
        "node",
        &format!("{TEST_TYPINGS_LOCATION}/node_modules/@types/node/index.d.ts"),
        "1.3.0-next.0",
    );
    cache_entry(
        &cache,
        "commander",
        &format!("{TEST_TYPINGS_LOCATION}/node_modules/@types/commander/index.d.ts"),
        "1.3.0-next.0",
    );
    let mut config = registry_config();
    config.insert(
        format!("ts{}", ts_goport::core::version_major_minor()),
        "1.3.0-next.1".to_string(),
    );
    let mut registry = Registry::default();
    registry.insert("node".to_string(), Some(config));
    registry.insert("commander".to_string(), Some(registry_config()));
    let (cached_typing_paths, new_typing_names, files_to_watch) = discover(
        &[(APP, "")],
        &typings_info(&["http", "commander"]),
        &[APP],
        &cache,
        &registry,
    );
    assert!(cached_typing_paths.is_empty());
    assert_eq!(set(&new_typing_names), set_of(&["node", "commander"]));
    assert_eq!(files_to_watch, watch_dirs());
}
