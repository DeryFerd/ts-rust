//! Port of typescript-go `internal/parser/references.go`: the imports,
//! module augmentations and ambient module names of a parsed file.
//!
//! PORT: Go writes these to `*ast.SourceFile`. Here they go to the matching
//! `ParsedSourceFile` fields (plan contract 6).

use crate::frontend::prelude::*;

// Go: core/nodemodules.go:9 UnprefixedNodeCoreModules
// PORT: Go `map[string]bool`; a fixed array searched with `contains`.
// core/nodemodules.go is not in this unit, so the set is private here.
const UNPREFIXED_NODE_CORE_MODULES: [&str; 54] = [
    "assert",
    "assert/strict",
    "async_hooks",
    "buffer",
    "child_process",
    "cluster",
    "console",
    "constants",
    "crypto",
    "dgram",
    "diagnostics_channel",
    "dns",
    "dns/promises",
    "domain",
    "events",
    "fs",
    "fs/promises",
    "http",
    "http2",
    "https",
    "inspector",
    "inspector/promises",
    "module",
    "net",
    "os",
    "path",
    "path/posix",
    "path/win32",
    "perf_hooks",
    "process",
    "punycode",
    "querystring",
    "readline",
    "readline/promises",
    "repl",
    "stream",
    "stream/consumers",
    "stream/promises",
    "stream/web",
    "string_decoder",
    "sys",
    "timers",
    "timers/promises",
    "tls",
    "trace_events",
    "tty",
    "url",
    "util",
    "util/types",
    "v8",
    "vm",
    "wasi",
    "worker_threads",
    "zlib",
];

// Go: core/nodemodules.go:67 ExclusivelyPrefixedNodeCoreModules
// PORT: see UNPREFIXED_NODE_CORE_MODULES.
const EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES: [&str; 5] = [
    "node:quic",
    "node:sea",
    "node:sqlite",
    "node:test",
    "node:test/reporters",
];

// Go: parser/references.go:11 collectExternalModuleReferences
pub fn collect_external_module_references(file: &mut ParsedSourceFile) {
    let root = file.root;
    for node in root.statements().iter() {
        collect_module_references(file, node, false /*inAmbientModule*/);
    }

    if root
        .flags()
        .intersects(NodeFlags::POSSIBLY_CONTAINS_DYNAMIC_IMPORT)
        || is_in_js_file(root)
    {
        for_each_dynamic_import_or_require_call(
            root,
            true, /*includeTypeSpaceImports*/
            true, /*requireStringLiteralLikeArgument*/
            &mut |_node, module_specifier| {
                // Go: ast.SetImportsOfSourceFile(file, append(file.Imports(), moduleSpecifier))
                file.imports.push(module_specifier);
                false
            },
        );
    }
}

// Go: parser/references.go:24 collectModuleReferences
fn collect_module_references(file: &mut ParsedSourceFile, node: Node, in_ambient_module: bool) {
    if is_any_import_or_re_export(node) {
        let module_name_expr = get_external_module_name(node);
        // TypeScript 1.0 spec (April 2014): 12.1.6
        // An ExternalImportDeclaration in an AmbientExternalModuleDeclaration may reference other external modules
        // only through top - level external module names. Relative external module names are not permitted.
        if module_name_expr.is_some() && is_string_literal(module_name_expr) {
            let module_name = module_name_expr.text();
            if !module_name.is_empty()
                && (!in_ambient_module || !is_external_module_name_relative(module_name))
            {
                // Go: ast.SetImportsOfSourceFile(file, append(file.Imports(), moduleNameExpr))
                file.imports.push(module_name_expr);
                // !!! removed `&& p.currentNodeModulesDepth == 0`
                if file.uses_uri_style_node_core_modules != Tristate::True
                    && !file.is_declaration_file
                {
                    if module_name.starts_with("node:")
                        && !EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES.contains(&module_name)
                    {
                        // Presence of `node:` prefix takes precedence over unprefixed node core modules
                        file.uses_uri_style_node_core_modules = Tristate::True;
                    } else if file.uses_uri_style_node_core_modules == Tristate::Unknown
                        && UNPREFIXED_NODE_CORE_MODULES.contains(&module_name)
                    {
                        // Avoid `unprefixedNodeCoreModules.has` for every import
                        file.uses_uri_style_node_core_modules = Tristate::False;
                    }
                }
            }
        }
        return;
    }
    if is_module_declaration(node)
        && is_ambient_module(node)
        && (in_ambient_module
            || has_syntactic_modifier(node, ModifierFlags::AMBIENT)
            || file.is_declaration_file)
    {
        let name_text = node.name().text();
        // Ambient module declarations can be interpreted as augmentations for some existing external modules.
        // This will happen in two cases:
        // - if current file is external module then module augmentation is a ambient module declaration defined in the top level scope
        // - if current file is not external module then module augmentation is an ambient module declaration with non-relative module name
        //   immediately nested in top level ambient module declaration .
        // PORT: Go `ast.IsExternalModule(file)` is `file.ExternalModuleIndicator != nil`.
        // It reads the `ParsedSourceFile` field, because the file is not installed yet.
        if file.external_module_indicator.is_some()
            || (in_ambient_module && !is_external_module_name_relative(name_text))
        {
            file.module_augmentations.push(node.name());
        } else if !in_ambient_module {
            file.ambient_module_names.push(name_text.to_string());
            // An AmbientExternalModuleDeclaration declares an external module.
            // This type of declaration is permitted only in the global module.
            // The StringLiteral must specify a top - level external module name.
            // Relative external module names are not permitted
            // NOTE: body of ambient module is always a module block, if it exists
            let body = node.body();
            if body.is_some() {
                for statement in body.statements().iter() {
                    collect_module_references(file, statement, true /*inAmbientModule*/);
                }
            }
        }
    }
}
