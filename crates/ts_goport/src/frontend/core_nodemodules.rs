//! Port of Go `core/nodemodules.go`.

use crate::frontend::prelude::*;
use std::sync::LazyLock;

// Go: core/nodemodules.go:9 UnprefixedNodeCoreModules
// require('module').builtinModules.filter(x => !x.match(/^(?:_|node:)/))
// PORT: Go package var `map[string]bool`. `IndexMap` keeps the Go list order.
// A missing key reads as `false` in Go: use `.get(k).copied().unwrap_or(false)`
// or `contains_key` (every value is `true`).
pub static UNPREFIXED_NODE_CORE_MODULES: LazyLock<IndexMap<&'static str, bool>> =
    LazyLock::new(|| {
        IndexMap::from_iter([
            ("assert", true),
            ("assert/strict", true),
            ("async_hooks", true),
            ("buffer", true),
            ("child_process", true),
            ("cluster", true),
            ("console", true),
            ("constants", true),
            ("crypto", true),
            ("dgram", true),
            ("diagnostics_channel", true),
            ("dns", true),
            ("dns/promises", true),
            ("domain", true),
            ("events", true),
            ("fs", true),
            ("fs/promises", true),
            ("http", true),
            ("http2", true),
            ("https", true),
            ("inspector", true),
            ("inspector/promises", true),
            ("module", true),
            ("net", true),
            ("os", true),
            ("path", true),
            ("path/posix", true),
            ("path/win32", true),
            ("perf_hooks", true),
            ("process", true),
            ("punycode", true),
            ("querystring", true),
            ("readline", true),
            ("readline/promises", true),
            ("repl", true),
            ("stream", true),
            ("stream/consumers", true),
            ("stream/promises", true),
            ("stream/web", true),
            ("string_decoder", true),
            ("sys", true),
            ("timers", true),
            ("timers/promises", true),
            ("tls", true),
            ("trace_events", true),
            ("tty", true),
            ("url", true),
            ("util", true),
            ("util/types", true),
            ("v8", true),
            ("vm", true),
            ("wasi", true),
            ("worker_threads", true),
            ("zlib", true),
        ])
    });

// Go: core/nodemodules.go:67 ExclusivelyPrefixedNodeCoreModules
// require('module').builtinModules.filter(x => x.startsWith('node:'))
// PORT: see `UNPREFIXED_NODE_CORE_MODULES`.
pub static EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES: LazyLock<IndexMap<&'static str, bool>> =
    LazyLock::new(|| {
        IndexMap::from_iter([
            ("node:quic", true),
            ("node:sea", true),
            ("node:sqlite", true),
            ("node:test", true),
            ("node:test/reporters", true),
        ])
    });

// Go: core/nodemodules.go:75 NodeCoreModules
// PORT: Go `sync.OnceValue(func() map[string]bool)` is a function over a
// `LazyLock`. Go ranges over a map (random order); this inserts in the Go
// list order. The result is only used for lookups.
pub fn node_core_modules() -> &'static IndexMap<String, bool> {
    static NODE_CORE_MODULES: LazyLock<IndexMap<String, bool>> = LazyLock::new(|| {
        let mut node_core_modules: IndexMap<String, bool> = IndexMap::with_capacity(
            UNPREFIXED_NODE_CORE_MODULES.len() * 2 + EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES.len(),
        );
        for unprefixed in UNPREFIXED_NODE_CORE_MODULES.keys() {
            node_core_modules.insert((*unprefixed).to_string(), true);
            node_core_modules.insert(format!("node:{unprefixed}"), true);
        }
        // Go: maps.Copy(nodeCoreModules, ExclusivelyPrefixedNodeCoreModules)
        for (k, v) in EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES.iter() {
            node_core_modules.insert((*k).to_string(), *v);
        }
        node_core_modules
    });
    &NODE_CORE_MODULES
}

// Go: core/nodemodules.go:85 NonRelativeModuleNameForTypingCache
pub fn non_relative_module_name_for_typing_cache(module_name: &str) -> String {
    if node_core_modules()
        .get(module_name)
        .copied()
        .unwrap_or(false)
    {
        return "node".to_string();
    }
    module_name.to_string()
}
