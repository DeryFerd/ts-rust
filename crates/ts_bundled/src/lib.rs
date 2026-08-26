//! TypeScript default-library declarations bundled from the pinned upstream.

include!(concat!(env!("OUT_DIR"), "/libraries.rs"));

use std::collections::HashSet;
use ts_options::ScriptTarget;

// Matches tsoptions.Libs in pinned internal/tsoptions/enummaps.go, including aliases.
const LIBRARY_LOAD_ORDER: &[&str] = &[
    "es5",
    "es6",
    "es2015",
    "es7",
    "es2016",
    "es2017",
    "es2018",
    "es2019",
    "es2020",
    "es2021",
    "es2022",
    "es2023",
    "es2024",
    "es2025",
    "esnext",
    "dom",
    "dom.iterable",
    "dom.asynciterable",
    "webworker",
    "webworker.importscripts",
    "webworker.iterable",
    "webworker.asynciterable",
    "scripthost",
    "es2015.core",
    "es2015.collection",
    "es2015.generator",
    "es2015.iterable",
    "es2015.promise",
    "es2015.proxy",
    "es2015.reflect",
    "es2015.symbol",
    "es2015.symbol.wellknown",
    "es2016.array.include",
    "es2016.intl",
    "es2017.arraybuffer",
    "es2017.date",
    "es2017.object",
    "es2017.sharedmemory",
    "es2017.string",
    "es2017.intl",
    "es2017.typedarrays",
    "es2018.asyncgenerator",
    "es2018.asynciterable",
    "es2018.intl",
    "es2018.promise",
    "es2018.regexp",
    "es2019.array",
    "es2019.object",
    "es2019.string",
    "es2019.symbol",
    "es2019.intl",
    "es2020.bigint",
    "es2020.date",
    "es2020.promise",
    "es2020.sharedmemory",
    "es2020.string",
    "es2020.symbol.wellknown",
    "es2020.intl",
    "es2020.number",
    "es2021.promise",
    "es2021.string",
    "es2021.weakref",
    "es2021.intl",
    "es2022.array",
    "es2022.error",
    "es2022.intl",
    "es2022.object",
    "es2022.string",
    "es2022.regexp",
    "es2023.array",
    "es2023.collection",
    "es2023.intl",
    "es2024.arraybuffer",
    "es2024.collection",
    "es2024.object",
    "es2024.promise",
    "es2024.regexp",
    "es2024.sharedmemory",
    "es2024.string",
    "es2025.collection",
    "es2025.float16",
    "es2025.intl",
    "es2025.iterator",
    "es2025.promise",
    "es2025.regexp",
    "esnext.asynciterable",
    "esnext.symbol",
    "esnext.bigint",
    "esnext.weakref",
    "esnext.object",
    "esnext.regexp",
    "esnext.string",
    "esnext.float16",
    "esnext.iterator",
    "esnext.promise",
    "esnext.array",
    "esnext.collection",
    "esnext.date",
    "esnext.decorators",
    "esnext.disposable",
    "esnext.error",
    "esnext.intl",
    "esnext.sharedmemory",
    "esnext.temporal",
    "esnext.typedarrays",
    "decorators",
    "decorators.legacy",
];

/// Returns the upstream default library entry point for an emit target.
#[must_use]
pub const fn default_library_name(target: ScriptTarget) -> &'static str {
    match target {
        ScriptTarget::EsNext => "lib.esnext.full.d.ts",
        ScriptTarget::Es2025 => "lib.es2025.full.d.ts",
        ScriptTarget::Es2024 => "lib.es2024.full.d.ts",
        ScriptTarget::Es2023 => "lib.es2023.full.d.ts",
        ScriptTarget::Es2022 => "lib.es2022.full.d.ts",
        ScriptTarget::Es2021 => "lib.es2021.full.d.ts",
        ScriptTarget::Es2020 => "lib.es2020.full.d.ts",
        ScriptTarget::Es2019 => "lib.es2019.full.d.ts",
        ScriptTarget::Es2018 => "lib.es2018.full.d.ts",
        ScriptTarget::Es2017 => "lib.es2017.full.d.ts",
        ScriptTarget::Es2016 => "lib.es2016.full.d.ts",
        ScriptTarget::Es2015 => "lib.es6.d.ts",
        ScriptTarget::Es3 | ScriptTarget::Es5 => "lib.d.ts",
    }
}

#[must_use]
pub fn library(name: &str) -> Option<&'static str> {
    LIBRARIES
        .binary_search_by_key(&name, |(library_name, _)| library_name)
        .ok()
        .map(|index| LIBRARIES[index].1)
}

#[must_use]
pub fn library_names() -> impl ExactSizeIterator<Item = &'static str> {
    LIBRARIES.iter().map(|(name, _)| *name)
}

/// Returns the pinned Program load priority for a bundled library basename.
///
/// Original default roots come first. Unlisted files share the last priority.
#[must_use]
pub fn library_priority(file_name: &str) -> usize {
    if matches!(file_name, "lib.d.ts" | "lib.es6.d.ts") {
        return 0;
    }
    file_name
        .strip_prefix("lib.")
        .and_then(|name| name.strip_suffix(".d.ts"))
        .and_then(|name| {
            LIBRARY_LOAD_ORDER
                .iter()
                .position(|candidate| *candidate == name)
        })
        .map_or(LIBRARY_LOAD_ORDER.len() + 2, |index| index + 1)
}

/// Resolves triple-slash `reference lib` dependencies in dependency-first
/// order, ending with `root`.
#[must_use]
pub fn library_closure(root: &str) -> Vec<&'static str> {
    let mut result = Vec::new();
    let mut seen = HashSet::new();
    visit_library(root, &mut seen, &mut result);
    result
}

fn visit_library(name: &str, seen: &mut HashSet<String>, result: &mut Vec<&'static str>) {
    if !seen.insert(name.to_owned()) {
        return;
    }
    let Some((stored_name, source)) = LIBRARIES.iter().find(|(stored, _)| *stored == name) else {
        return;
    };
    for reference in referenced_libraries(source) {
        let dependency = format!("lib.{reference}.d.ts");
        visit_library(&dependency, seen, result);
    }
    result.push(stored_name);
}

fn referenced_libraries(source: &str) -> impl Iterator<Item = &str> {
    source.lines().filter_map(|line| {
        let marker = "/// <reference lib=\"";
        let rest = line.trim().strip_prefix(marker)?;
        rest.split_once('"').map(|(name, _)| name)
    })
}

#[cfg(test)]
mod tests {
    use ts_options::ScriptTarget;

    use super::{
        LIBRARY_LOAD_ORDER, default_library_name, library, library_closure, library_names,
        library_priority,
    };

    #[test]
    fn embeds_the_complete_pinned_library_set() {
        assert_eq!(library_names().len(), 108);
        assert!(
            library("lib.d.ts")
                .unwrap()
                .contains("reference lib=\"es5\"")
        );
        assert!(
            library("lib.es5.d.ts")
                .unwrap()
                .contains("interface Array<T>")
        );
        assert!(
            library("lib.dom.d.ts")
                .unwrap()
                .contains("interface Document")
        );
        assert!(library("missing.d.ts").is_none());
    }

    #[test]
    fn resolves_default_library_references_dependency_first() {
        let closure = library_closure("lib.d.ts");
        assert!(closure.contains(&"lib.es5.d.ts"));
        assert!(closure.contains(&"lib.dom.d.ts"));
        assert_eq!(closure.last(), Some(&"lib.d.ts"));
        let mut deduplicated = closure.clone();
        deduplicated.sort_unstable();
        deduplicated.dedup();
        assert_eq!(deduplicated.len(), closure.len());
    }

    #[test]
    fn library_priorities_match_pinned_roots_hosts_features_and_fallback() {
        assert_eq!(library_priority("lib.d.ts"), 0);
        assert_eq!(library_priority("lib.es6.d.ts"), 0);
        assert_eq!(library_priority("lib.es5.d.ts"), 1);
        assert_eq!(library_priority("lib.es2015.d.ts"), 3);
        let mut libraries = [
            "lib.decorators.d.ts",
            "lib.es2015.symbol.wellknown.d.ts",
            "lib.es2015.iterable.d.ts",
            "lib.scripthost.d.ts",
            "lib.es2015.generator.d.ts",
            "lib.dom.d.ts",
            "lib.es5.d.ts",
        ];
        libraries.sort_by_key(|name| library_priority(name));
        assert_eq!(
            libraries,
            [
                "lib.es5.d.ts",
                "lib.dom.d.ts",
                "lib.scripthost.d.ts",
                "lib.es2015.generator.d.ts",
                "lib.es2015.iterable.d.ts",
                "lib.es2015.symbol.wellknown.d.ts",
                "lib.decorators.d.ts",
            ]
        );
        for name in ["lib.es2025.full.d.ts", "custom.d.ts", "lib.missing.d.ts"] {
            assert_eq!(library_priority(name), LIBRARY_LOAD_ORDER.len() + 2);
        }
    }

    #[test]
    fn selects_the_upstream_default_library_for_each_target_generation() {
        assert_eq!(default_library_name(ScriptTarget::Es5), "lib.d.ts");
        assert_eq!(default_library_name(ScriptTarget::Es2015), "lib.es6.d.ts");
        assert_eq!(
            default_library_name(ScriptTarget::Es2025),
            "lib.es2025.full.d.ts"
        );
        assert_eq!(
            default_library_name(ScriptTarget::EsNext),
            "lib.esnext.full.d.ts"
        );
    }
}
