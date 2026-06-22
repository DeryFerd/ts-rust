//! TypeScript default-library declarations bundled from the pinned upstream.

include!(concat!(env!("OUT_DIR"), "/libraries.rs"));

use std::collections::HashSet;
use ts_options::ScriptTarget;

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

    use super::{default_library_name, library, library_closure, library_names};

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
