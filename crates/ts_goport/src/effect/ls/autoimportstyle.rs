//! Port of Effect-TS/tsgo `internal/autoimportstyle` (`stylepolicy.go`) at
//! effect-tsgo 0.51.1 (`47cb1ed7`), and of the transformer factory that
//! `etslshooks/init.go:51-82` registers (patch 027).
//!
//! The plugin options `namespaceImportPackages`, `barrelImportPackages`,
//! `importAliases` and `topLevelNamedReexports` rewrite the auto-import
//! fixes of a package:
//! - namespace packages: `import * as X from "<spec>"` plus `X.` at the use;
//! - barrel packages: `import { X } from "<barrel>"` plus `X.` at the use.
//!
//! `ls/autoimport/view.rs` `new_view` calls [`new_view_fix_transformer`]
//! (Go `NewView` calls the registered factory), and
//! `ls/autoimport/fix.rs` `get_fixes` runs the transformer at each return
//! (patch 018, `applyStylePolicy`).
//!
//! PORT: Go `FixTransformer` is a closure over a `*stylePolicy`. The port
//! uses the struct [`FixTransformer`]. Go nil fixes and nil results are
//! `None`; an unchanged fix is the same `Rc`, as Go returns the same
//! pointer.

use crate::effect::etscore::{ResolvedEffectPluginOptions, TopLevelNamedReexportsMode};
use crate::effect::pluginoptions::resolve_effect_plugin_options_for_source_file;
use crate::effect::rulerunner::enabled_options;
use crate::ls::autoimport::{Export, ExportSyntax, Fix, ModuleID};
use crate::ls::prelude::*;

/// Go `func(export *autoimport.Export) (string, modulespecifiers.ResultKind)`:
/// the direct module specifier of a namespace reexport's target module.
pub type ResolveTarget = Box<dyn Fn(&Export) -> (String, modulespecifiers::ResultKind)>;

// Go: internal/autoimportstyle/stylepolicy.go:14 stylePolicy
// stylePolicy applies auto-import style rewrites based on configured preferences.
#[derive(Default)]
struct StylePolicy {
    namespace_packages: FxHashSet<String>,
    barrel_packages: FxHashSet<String>,
    aliases: FxHashMap<String, String>,
    follow_reexports: bool,
    resolve_target: Option<ResolveTarget>,
}

/// Go `autoimport.FixTransformer` as effect-tsgo makes it: rewrites the
/// fixes of one export by the style policy.
pub struct FixTransformer {
    sp: StylePolicy,
}

// Go: internal/autoimportstyle/stylepolicy.go:24 NewFixTransformer
// NewFixTransformer creates a FixTransformer from the given resolved Effect options.
// Returns nil if the preferences are empty (no packages configured).
// PORT: Go nil `resolved` is `None`.
pub fn new_fix_transformer(
    resolved: Option<&ResolvedEffectPluginOptions>,
    resolve_target: Option<ResolveTarget>,
) -> Option<FixTransformer> {
    let mut sp = new_style_policy(resolved);
    sp.resolve_target = resolve_target;
    if sp.is_empty() {
        return None;
    }
    Some(FixTransformer { sp })
}

impl FixTransformer {
    // Go: internal/autoimportstyle/stylepolicy.go:33 (the returned closure)
    /// The fixes of `export` after the style policy. An empty result drops
    /// every fix of the export (Go returns nil).
    pub fn transform(&self, export: &Export, fixes: Vec<Rc<Fix>>) -> Vec<Rc<Fix>> {
        let mut rewritten: Vec<Rc<Fix>> = Vec::with_capacity(fixes.len());
        let mut has_use_namespace: FxHashSet<String> = FxHashSet::default();
        for fix in &fixes {
            if let Some(adjusted) = self.sp.apply(export, fix) {
                if adjusted.kind == lsproto::AutoImportFixKind::USE_NAMESPACE {
                    has_use_namespace.insert(namespace_fix_key(&adjusted));
                }
                rewritten.push(adjusted);
            }
        }
        if !has_use_namespace.is_empty() {
            rewritten.retain(|fix| {
                !(fix.kind == lsproto::AutoImportFixKind::ADD_NEW
                    && fix.import_kind == lsproto::ImportKind::NAMESPACE
                    && has_use_namespace.contains(&namespace_fix_key(fix)))
            });
        }
        rewritten
    }
}

// Go: internal/autoimportstyle/stylepolicy.go:62 namespaceFixKey
fn namespace_fix_key(fix: &Fix) -> String {
    format!("{}\x00{}", fix.module_specifier, fix.namespace_prefix)
}

// Go: internal/autoimportstyle/stylepolicy.go:71 newStylePolicy
// newStylePolicy creates a stylePolicy from the given resolved options.
// Package names are lowercased for case-insensitive matching.
fn new_style_policy(resolved: Option<&ResolvedEffectPluginOptions>) -> StylePolicy {
    let Some(resolved) = resolved else {
        return StylePolicy::default();
    };
    StylePolicy {
        namespace_packages: resolved
            .namespace_import_packages
            .iter()
            .map(|pkg| pkg.to_lowercase())
            .collect(),
        barrel_packages: resolved
            .barrel_import_packages
            .iter()
            .map(|pkg| pkg.to_lowercase())
            .collect(),
        aliases: resolved
            .import_aliases
            .iter()
            .map(|(pkg, alias)| (pkg.to_lowercase(), alias.clone()))
            .collect(),
        follow_reexports: resolved.top_level_named_reexports == TopLevelNamedReexportsMode::Follow,
        resolve_target: None,
    }
}

impl StylePolicy {
    // Go: internal/autoimportstyle/stylepolicy.go:94 isEmpty
    // isEmpty returns true if no style preferences are configured.
    // PORT: Go also takes a nil receiver; the port has no nil policy.
    fn is_empty(&self) -> bool {
        self.namespace_packages.is_empty() && self.barrel_packages.is_empty()
    }

    // Go: internal/autoimportstyle/stylepolicy.go:101 Apply
    // Apply transforms a fix based on the export's package and the configured style.
    // Returns nil if the fix should be suppressed (e.g., ignored top-level reexport).
    // Returns the fix unchanged if no style policy applies.
    // PORT: Go also takes a nil export (the fix comes back) and a nil fix
    // (nil comes back); the port has neither.
    fn apply(&self, export: &Export, fix: &Rc<Fix>) -> Option<Rc<Fix>> {
        if self.is_empty() {
            return Some(Rc::clone(fix));
        }

        // Only rewrite new imports or additions to existing imports.
        if fix.kind != lsproto::AutoImportFixKind::ADD_NEW
            && fix.kind != lsproto::AutoImportFixKind::ADD_TO_EXISTING
        {
            return Some(Rc::clone(fix));
        }

        let pkg_name = export.package_name.to_lowercase();
        if pkg_name.is_empty() {
            return Some(Rc::clone(fix));
        }
        if pkg_name == "effect"
            && (self.namespace_packages.contains(&pkg_name)
                || self.barrel_packages.contains(&pkg_name))
            && (fix.module_specifier.starts_with("effect/internal/")
                || fix.module_specifier.contains("/internal/"))
        {
            return None;
        }

        // Check namespace-import packages
        if self.namespace_packages.contains(&pkg_name) {
            return self.apply_namespace_rewrite(export, fix);
        }

        // Check barrel-import packages
        if self.barrel_packages.contains(&pkg_name) {
            return self.apply_barrel_rewrite(export, fix);
        }

        Some(Rc::clone(fix))
    }

    // Go: internal/autoimportstyle/stylepolicy.go:135 applyNamespaceRewrite
    // applyNamespaceRewrite rewrites a named-import fix to a namespace-import fix.
    fn apply_namespace_rewrite(&self, export: &Export, fix: &Rc<Fix>) -> Option<Rc<Fix>> {
        // Only rewrite named imports
        if fix.import_kind != lsproto::ImportKind::NAMED {
            return Some(Rc::clone(fix));
        }
        // Rewrites require usage qualification (e.g. `succeed` -> `Effect.succeed`).
        // If no usage site is available, keep the original named-import fix.
        if fix.usage_position.is_none() {
            return Some(Rc::clone(fix));
        }
        if is_namespace_reexport(export) {
            let Some(resolve_target) = &self.resolve_target else {
                return Some(Rc::clone(fix));
            };
            let (module_specifier, module_specifier_kind) = resolve_target(export);
            if module_specifier.is_empty() {
                return Some(Rc::clone(fix));
            }
            return Some(Rc::new(Fix {
                auto_import_fix: lsproto::AutoImportFix {
                    kind: lsproto::AutoImportFixKind::ADD_NEW,
                    import_kind: lsproto::ImportKind::NAMESPACE,
                    module_specifier,
                    name: export.name(),
                    use_require: fix.use_require,
                    add_as_type_only: fix.add_as_type_only,
                    usage_position: fix.usage_position,
                    ..Default::default()
                },
                module_specifier_kind,
                module_file_name: module_id_file_name(&export.target.module_id),
                ..Default::default()
            }));
        }

        // Check if this is a top-level named reexport
        let is_reexport = !export.target.module_id.as_string().is_empty()
            && export.target.module_id != export.module_id;
        if is_reexport && !self.follow_reexports {
            // When topLevelNamedReexports is "ignore", skip rewriting top-level reexports
            return Some(Rc::clone(fix));
        }
        if is_reexport && self.follow_reexports {
            // When topLevelNamedReexports is "follow", suppress reexport fixes
            // so the direct submodule namespace import wins instead
            return None;
        }

        let namespace_name = infer_namespace_name(&fix.module_specifier);
        if namespace_name.is_empty() {
            return Some(Rc::clone(fix));
        }

        // Apply alias if configured
        let pkg_name = export.package_name.to_lowercase();
        let alias = self.resolve_alias(&pkg_name, namespace_name);

        Some(Rc::new(Fix {
            auto_import_fix: lsproto::AutoImportFix {
                kind: lsproto::AutoImportFixKind::ADD_NEW,
                import_kind: lsproto::ImportKind::NAMESPACE,
                module_specifier: fix.module_specifier.clone(),
                name: fix.name.clone(),
                use_require: fix.use_require,
                add_as_type_only: fix.add_as_type_only,
                usage_position: fix.usage_position,
                namespace_prefix: alias,
                ..Default::default()
            },
            module_specifier_kind: fix.module_specifier_kind,
            is_re_export: fix.is_re_export,
            module_file_name: fix.module_file_name.clone(),
            ..Default::default()
        }))
    }

    // Go: internal/autoimportstyle/stylepolicy.go:216 applyBarrelRewrite
    // applyBarrelRewrite rewrites a fix to a named import from the barrel package.
    fn apply_barrel_rewrite(&self, export: &Export, fix: &Rc<Fix>) -> Option<Rc<Fix>> {
        if export.package_name == "effect" {
            let barrel = effect_nested_barrel(&fix.module_specifier);
            if !barrel.is_empty() {
                return self.apply_barrel_rewrite_from(export, fix, &barrel);
            }
        }
        self.apply_barrel_rewrite_from(export, fix, &export.package_name)
    }

    // Go: internal/autoimportstyle/stylepolicy.go:239 applyBarrelRewriteFrom
    fn apply_barrel_rewrite_from(
        &self,
        export: &Export,
        fix: &Rc<Fix>,
        barrel_specifier: &str,
    ) -> Option<Rc<Fix>> {
        // Barrel rewrites require usage qualification (e.g. `request` -> `HttpClient.request`).
        // If no usage site is available, keep the original named-import fix.
        if fix.usage_position.is_none() {
            return Some(Rc::clone(fix));
        }

        if barrel_specifier.is_empty() {
            return Some(Rc::clone(fix));
        }

        // Infer the namespace name from the module specifier (e.g., "effect/Effect" -> "Effect")
        let namespace_name = infer_namespace_name(&fix.module_specifier);
        if namespace_name.is_empty() {
            return Some(Rc::clone(fix));
        }

        // Apply alias if configured
        let pkg_name = export.package_name.to_lowercase();
        let alias = self.resolve_alias(&pkg_name, namespace_name);

        Some(Rc::new(Fix {
            auto_import_fix: lsproto::AutoImportFix {
                kind: lsproto::AutoImportFixKind::ADD_NEW,
                import_kind: lsproto::ImportKind::NAMED,
                module_specifier: barrel_specifier.to_string(),
                name: fix.name.clone(),
                use_require: fix.use_require,
                add_as_type_only: fix.add_as_type_only,
                usage_position: fix.usage_position,
                namespace_prefix: alias,
                ..Default::default()
            },
            module_specifier_kind: fix.module_specifier_kind,
            is_re_export: fix.is_re_export,
            module_file_name: fix.module_file_name.clone(),
            ..Default::default()
        }))
    }

    // Go: internal/autoimportstyle/stylepolicy.go:280 resolveAlias
    // resolveAlias returns the configured alias for the given namespace name under
    // the given package, or the namespace name itself if no alias is configured.
    fn resolve_alias(&self, pkg_name_lower: &str, namespace_name: &str) -> String {
        match self.aliases.get(pkg_name_lower) {
            Some(alias) => alias.clone(),
            None => namespace_name.to_string(),
        }
    }
}

// Go: internal/autoimportstyle/stylepolicy.go:207 isNamespaceReexport
fn is_namespace_reexport(export: &Export) -> bool {
    export.syntax == ExportSyntax::MODIFIER
        && export.flags.intersects(SymbolFlags::MODULE)
        && !export.target.module_id.as_string().is_empty()
        && export.target.module_id != export.module_id
}

// Go: shim/ls/autoimport/integration.go ModuleIDFileName (effect-tsgo 0.51.1)
// The file path of a file module, "" for an ambient module.
// PORT: Go `tspath.RootedFilePath` is `String` here, as `Fix::module_file_name`.
fn module_id_file_name(id: &ModuleID) -> String {
    id.as_path_key()
        .map(|path| path.0.clone())
        .unwrap_or_default()
}

// Go: internal/autoimportstyle/stylepolicy.go:227 effectNestedBarrel
// effectNestedBarrel maps a nested Effect module to its public barrel.
// Effect v4 exports both the group barrel and its public nested modules.
fn effect_nested_barrel(specifier: &str) -> String {
    let Some(rest) = specifier.strip_prefix("effect/") else {
        return String::new();
    };
    let Some((group, _)) = rest.split_once('/') else {
        return String::new();
    };
    if group.is_empty() || group == "internal" {
        return String::new();
    }
    format!("effect/{group}")
}

// Go: internal/autoimportstyle/stylepolicy.go:291 packageNameFromSpecifier
// packageNameFromSpecifier extracts the npm package name from a bare module specifier.
// For scoped packages like "@scope/pkg/sub", returns "@scope/pkg".
// For non-scoped packages like "pkg/sub", returns "pkg".
// For relative paths, returns "".
// PORT: as in Go, only the tests call it.
#[cfg_attr(not(test), allow(dead_code))]
fn package_name_from_specifier(specifier: &str) -> &str {
    if specifier.is_empty() || specifier.starts_with('.') || specifier.starts_with('/') {
        return "";
    }
    if specifier.starts_with('@') {
        // Scoped package: @scope/name or @scope/name/sub
        let Some(slash_idx) = specifier.find('/') else {
            return specifier;
        };
        let Some(second_slash) = specifier[slash_idx + 1..].find('/') else {
            return specifier;
        };
        return &specifier[..slash_idx + 1 + second_slash];
    }
    // Non-scoped: name or name/sub
    match specifier.split_once('/') {
        Some((name, _)) => name,
        None => specifier,
    }
}

// Go: internal/autoimportstyle/stylepolicy.go:317 inferNamespaceName
// inferNamespaceName derives a namespace name from the last segment of a module specifier path.
// For example, "effect/Effect" → "Effect", "effect" → "effect", "@scope/pkg/Foo" → "Foo".
fn infer_namespace_name(module_specifier: &str) -> &str {
    match module_specifier.rfind('/') {
        Some(last_slash) => &module_specifier[last_slash + 1..],
        None => module_specifier,
    }
}

// Go: etslshooks/init.go:51 (the factory that init registers with
// autoimport.RegisterAutoImportFixTransformer)
/// The fix transformer of an auto-import view, or None when the program has
/// no Effect plugin or the plugin sets no namespace or barrel package.
/// `ls/autoimport/view.rs` `new_view` calls it (Effect-TS/tsgo patch 027).
// PORT: Go registers the factory and `NewView` calls it when it is set. The
// port calls it directly (no registry), as for the other hooks. The plugin
// check is `enabled_options`, so a standalone API process without
// `TSGO_EFFECT_API=1` has no transformer.
pub fn new_view_fix_transformer(
    preferences: &modulespecifiers::UserPreferences,
    program: &Rc<compiler::NewProgram>,
    importing_file: Node,
) -> Option<FixTransformer> {
    let effect_config = enabled_options(program.options())?;
    let resolved_options = resolve_effect_plugin_options_for_source_file(
        effect_config,
        source_file_file_name(importing_file),
        &program.options().config_file_path,
        program.use_case_sensitive_file_names(),
    );
    let program = Rc::clone(program);
    let preferences = preferences.clone();
    new_fix_transformer(
        Some(&resolved_options),
        Some(Box::new(move |export: &Export| {
            let mut target_file_name = module_id_file_name(&export.target.module_id);
            if let Some(target_file) = program.get_source_file(&target_file_name) {
                target_file_name = target_file.file_name().to_string();
            }
            let (specifiers, kind) = modulespecifiers::get_module_specifiers_for_file_with_info(
                &importing_file,
                &target_file_name,
                program.options(),
                &modulespecifiers::ProgramHost,
                &preferences,
                modulespecifiers::ModuleSpecifierOptions::default(),
                true,
            );
            for specifier in specifiers {
                if !specifier.contains("/node_modules/") {
                    return (specifier, kind);
                }
            }
            (String::new(), modulespecifiers::ResultKind::None)
        })),
    )
}

// Go: internal/autoimportstyle/stylepolicy_test.go
#[cfg(test)]
mod tests {
    use super::*;
    use crate::ls::autoimport::{ExportID, ambient_module_id};

    // Go: shim/ls/autoimport/integration.go NewAmbientModuleID (effect-tsgo 0.51.1)
    fn new_ambient_module_id(specifier: &str) -> ModuleID {
        if specifier.is_empty() {
            return ModuleID::default();
        }
        ambient_module_id(specifier)
    }

    fn options(
        namespace: &[&str],
        barrel: &[&str],
        aliases: &[(&str, &str)],
        top_level_named_reexports: TopLevelNamedReexportsMode,
    ) -> ResolvedEffectPluginOptions {
        ResolvedEffectPluginOptions {
            namespace_import_packages: namespace.iter().map(|s| s.to_string()).collect(),
            barrel_import_packages: barrel.iter().map(|s| s.to_string()).collect(),
            import_aliases: aliases
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect(),
            top_level_named_reexports,
            ..Default::default()
        }
    }

    fn namespace_policy() -> StylePolicy {
        new_style_policy(Some(&options(
            &["effect"],
            &[],
            &[],
            TopLevelNamedReexportsMode::Unset,
        )))
    }

    // Go: stylepolicy_test.go:54 makeExport
    fn make_export(package_name: &str, module_id: &str, target_module_id: &str) -> Export {
        Export {
            export_id: ExportID {
                module_id: new_ambient_module_id(module_id),
                export_name: "succeed".to_string(),
            },
            package_name: package_name.to_string(),
            target: ExportID {
                module_id: new_ambient_module_id(target_module_id),
                ..Default::default()
            },
            ..Default::default()
        }
    }

    // Go: stylepolicy_test.go:66 makeAddNewFix
    fn make_add_new_fix(
        import_kind: lsproto::ImportKind,
        module_specifier: &str,
        name: &str,
    ) -> Fix {
        Fix {
            auto_import_fix: lsproto::AutoImportFix {
                kind: lsproto::AutoImportFixKind::ADD_NEW,
                import_kind,
                module_specifier: module_specifier.to_string(),
                name: name.to_string(),
                usage_position: Some(lsproto::Position {
                    line: 1,
                    character: 1,
                }),
                ..Default::default()
            },
            ..Default::default()
        }
    }

    fn named_fix(module_specifier: &str, name: &str) -> Rc<Fix> {
        Rc::new(make_add_new_fix(
            lsproto::ImportKind::NAMED,
            module_specifier,
            name,
        ))
    }

    // Go: TestNewStylePolicy
    #[test]
    fn new_style_policy_lowercases_keys() {
        let sp = new_style_policy(Some(&options(
            &["effect", "Effect"],
            &["@effect/platform"],
            &[("effect", "Fx")],
            TopLevelNamedReexportsMode::Unset,
        )));
        assert!(sp.namespace_packages.contains("effect"));
        assert!(!sp.namespace_packages.contains("Effect"));
        assert!(sp.barrel_packages.contains("@effect/platform"));
        assert_eq!(sp.aliases.get("effect").map(String::as_str), Some("Fx"));
    }

    // Go: TestStylePolicyIsEmpty
    // PORT: the Go nil policy case has no Rust form (`new_style_policy(None)`
    // is the nearest).
    #[test]
    fn style_policy_is_empty() {
        assert!(new_style_policy(None).is_empty());
        assert!(new_style_policy(Some(&ResolvedEffectPluginOptions::default())).is_empty());
        assert!(!namespace_policy().is_empty());
    }

    // Go: TestApplyNamespaceRewrite
    #[test]
    fn apply_namespace_rewrite() {
        let sp = namespace_policy();
        let export = make_export("effect", "effect/Effect", "");
        let result = sp
            .apply(&export, &named_fix("effect/Effect", "succeed"))
            .expect("a fix");
        assert_eq!(result.import_kind, lsproto::ImportKind::NAMESPACE);
        assert_eq!(result.name, "succeed");
        assert_eq!(result.namespace_prefix, "Effect");
        assert_eq!(result.module_specifier, "effect/Effect");
    }

    // Go: TestApplySuppressesEffectInternalImport
    #[test]
    fn apply_suppresses_effect_internal_import() {
        let sp = namespace_policy();
        let export = make_export("effect", "effect/internal/schema/parser", "");
        let fix = named_fix("effect/internal/schema/parser", "succeed");
        assert!(sp.apply(&export, &fix).is_none());
    }

    // Go: TestApplyNamespaceRewriteFromAddToExisting
    #[test]
    fn apply_namespace_rewrite_from_add_to_existing() {
        let sp = namespace_policy();
        let export = make_export("effect", "effect/testing/TestClock", "");
        let mut fix = make_add_new_fix(
            lsproto::ImportKind::NAMED,
            "effect/testing/TestClock",
            "testClockWith",
        );
        fix.kind = lsproto::AutoImportFixKind::ADD_TO_EXISTING;
        let result = sp.apply(&export, &Rc::new(fix)).expect("a fix");
        assert_eq!(result.kind, lsproto::AutoImportFixKind::ADD_NEW);
        assert_eq!(result.import_kind, lsproto::ImportKind::NAMESPACE);
        assert_eq!(result.module_specifier, "effect/testing/TestClock");
        assert_eq!(result.namespace_prefix, "TestClock");
    }

    // Go: TestApplyNamespaceRewriteWithAlias
    #[test]
    fn apply_namespace_rewrite_with_alias() {
        let sp = new_style_policy(Some(&options(
            &["effect"],
            &[],
            &[("effect", "Fx")],
            TopLevelNamedReexportsMode::Unset,
        )));
        let export = make_export("effect", "effect/Effect", "");
        let result = sp
            .apply(&export, &named_fix("effect/Effect", "succeed"))
            .expect("a fix");
        assert_eq!(result.import_kind, lsproto::ImportKind::NAMESPACE);
        assert_eq!(result.name, "succeed");
        assert_eq!(result.namespace_prefix, "Fx");
    }

    // Go: TestApplyNamespaceReexport
    #[test]
    fn apply_namespace_reexport() {
        let mut sp = namespace_policy();
        sp.resolve_target = Some(Box::new(|export: &Export| {
            assert_eq!(export.target.module_id.as_string(), "effect/Effect");
            (
                "effect/Effect".to_string(),
                modulespecifiers::ResultKind::NodeModules,
            )
        }));
        let mut export = make_export("effect", "effect", "effect/Effect");
        export.export_id.export_name = "Effect".to_string();
        export.syntax = ExportSyntax::MODIFIER;
        export.flags = SymbolFlags::VALUE_MODULE;
        let result = sp
            .apply(&export, &named_fix("effect", "Effect"))
            .expect("a fix");
        assert_eq!(result.import_kind, lsproto::ImportKind::NAMESPACE);
        assert_eq!(result.module_specifier, "effect/Effect");
        assert_eq!(result.name, "Effect");
        assert_eq!(result.namespace_prefix, "");
        assert_eq!(
            result.module_specifier_kind,
            modulespecifiers::ResultKind::NodeModules
        );
        assert!(!result.is_re_export);
    }

    // Go: TestApplyBarrelRewrite
    #[test]
    fn apply_barrel_rewrite() {
        let sp = new_style_policy(Some(&options(
            &[],
            &["@effect/platform"],
            &[],
            TopLevelNamedReexportsMode::Unset,
        )));
        let export = make_export("@effect/platform", "@effect/platform/HttpClient", "");
        let result = sp
            .apply(
                &export,
                &named_fix("@effect/platform/HttpClient", "request"),
            )
            .expect("a fix");
        assert_eq!(result.import_kind, lsproto::ImportKind::NAMED);
        assert_eq!(result.module_specifier, "@effect/platform");
        assert_eq!(result.name, "request");
        assert_eq!(result.namespace_prefix, "HttpClient");
    }

    // Go: TestApplyBarrelRewriteWithAlias
    #[test]
    fn apply_barrel_rewrite_with_alias() {
        let sp = new_style_policy(Some(&options(
            &[],
            &["@effect/platform"],
            &[("@effect/platform", "Platform")],
            TopLevelNamedReexportsMode::Unset,
        )));
        let export = make_export("@effect/platform", "@effect/platform/HttpClient", "");
        let result = sp
            .apply(
                &export,
                &named_fix("@effect/platform/HttpClient", "request"),
            )
            .expect("a fix");
        assert_eq!(result.name, "request");
        assert_eq!(result.namespace_prefix, "Platform");
    }

    // Go: TestApplyNamespaceRewriteWithoutUsagePositionFallsBack
    #[test]
    fn apply_namespace_rewrite_without_usage_position_falls_back() {
        let sp = namespace_policy();
        let export = make_export("effect", "effect/Effect", "");
        let mut fix = make_add_new_fix(lsproto::ImportKind::NAMED, "effect/Effect", "succeed");
        fix.usage_position = None;
        let fix = Rc::new(fix);
        let result = sp.apply(&export, &fix).expect("a fix");
        assert!(Rc::ptr_eq(&result, &fix));
    }

    // Go: TestApplyBarrelRewriteWithoutUsagePositionFallsBack
    #[test]
    fn apply_barrel_rewrite_without_usage_position_falls_back() {
        let sp = new_style_policy(Some(&options(
            &[],
            &["@effect/platform"],
            &[],
            TopLevelNamedReexportsMode::Unset,
        )));
        let export = make_export("@effect/platform", "@effect/platform/HttpClient", "");
        let mut fix = make_add_new_fix(
            lsproto::ImportKind::NAMED,
            "@effect/platform/HttpClient",
            "request",
        );
        fix.usage_position = None;
        let fix = Rc::new(fix);
        let result = sp.apply(&export, &fix).expect("a fix");
        assert!(Rc::ptr_eq(&result, &fix));
    }

    // Go: TestApplyTopLevelReexportIgnore
    #[test]
    fn apply_top_level_reexport_ignore() {
        let sp = new_style_policy(Some(&options(
            &["effect"],
            &[],
            &[],
            TopLevelNamedReexportsMode::Ignore,
        )));
        // Export is a reexport (target module differs from module)
        let mut export = make_export("effect", "effect", "effect/Effect");
        export.syntax = ExportSyntax::NAMED;
        let result = sp
            .apply(&export, &named_fix("effect", "succeed"))
            .expect("a fix");
        // When ignoring reexports, the fix should be returned unchanged
        assert_eq!(result.import_kind, lsproto::ImportKind::NAMED);
        assert_eq!(result.name, "succeed");
    }

    // Go: TestApplyTopLevelReexportFollow
    #[test]
    fn apply_top_level_reexport_follow() {
        let sp = new_style_policy(Some(&options(
            &["effect"],
            &[],
            &[],
            TopLevelNamedReexportsMode::Follow,
        )));
        // Export is a reexport (target module differs from module)
        let mut export = make_export("effect", "effect", "effect/Effect");
        export.syntax = ExportSyntax::NAMED;
        // When following reexports, the reexport fix should be suppressed (nil)
        // so the direct submodule namespace import wins instead
        assert!(sp.apply(&export, &named_fix("effect", "succeed")).is_none());
    }

    // Go: TestApplyNoMatchPassthrough
    #[test]
    fn apply_no_match_passthrough() {
        let sp = namespace_policy();
        let export = make_export("lodash", "lodash", "");
        let fix = named_fix("lodash", "map");
        let result = sp.apply(&export, &fix).expect("a fix");
        assert!(Rc::ptr_eq(&result, &fix));
    }

    // Go: TestApplyNonAddNewPassthrough
    #[test]
    fn apply_non_add_new_passthrough() {
        let sp = namespace_policy();
        let export = make_export("effect", "effect/Effect", "");
        let fix = Rc::new(Fix {
            auto_import_fix: lsproto::AutoImportFix {
                kind: lsproto::AutoImportFixKind::ADD_TO_EXISTING,
                import_kind: lsproto::ImportKind::NAMED,
                module_specifier: "effect/Effect".to_string(),
                name: "succeed".to_string(),
                ..Default::default()
            },
            ..Default::default()
        });
        let result = sp.apply(&export, &fix).expect("a fix");
        assert!(Rc::ptr_eq(&result, &fix));
    }

    // Go: TestApplyCaseInsensitiveMatching
    #[test]
    fn apply_case_insensitive_matching() {
        let sp = new_style_policy(Some(&options(
            &["Effect"],
            &[],
            &[],
            TopLevelNamedReexportsMode::Unset,
        )));
        // Package name is lowercase but config was uppercase
        let export = make_export("effect", "effect/Effect", "");
        let result = sp
            .apply(&export, &named_fix("effect/Effect", "succeed"))
            .expect("a fix");
        assert_eq!(result.import_kind, lsproto::ImportKind::NAMESPACE);
    }

    // Go: TestApplyNilInputs
    // PORT: not ported. `apply` takes no nil export and no nil fix.

    // Go: TestPackageNameFromSpecifier
    #[test]
    fn package_name_from_specifier_cases() {
        for (input, expected) in [
            ("effect", "effect"),
            ("effect/Effect", "effect"),
            ("@scope/pkg", "@scope/pkg"),
            ("@scope/pkg/sub", "@scope/pkg"),
            ("@scope/pkg/sub/deep", "@scope/pkg"),
            ("./local", ""),
            ("/absolute", ""),
            ("", ""),
            ("@scope", "@scope"),
        ] {
            assert_eq!(package_name_from_specifier(input), expected, "{input:?}");
        }
    }

    // Go: TestInferNamespaceName
    #[test]
    fn infer_namespace_name_cases() {
        for (input, expected) in [
            ("effect/Effect", "Effect"),
            ("effect", "effect"),
            ("@scope/pkg/Foo", "Foo"),
            ("@effect/platform/HttpClient", "HttpClient"),
            ("", ""),
            ("foo/", ""),
        ] {
            assert_eq!(infer_namespace_name(input), expected, "{input:?}");
        }
    }

    // PORT: no Go test. `effectNestedBarrel` cases from the barrel fourslash
    // test (`effect/cli/Prompt`, `effect/workflow/DurableDeferred`).
    #[test]
    fn effect_nested_barrel_cases() {
        for (input, expected) in [
            ("effect/cli/Prompt", "effect/cli"),
            ("effect/workflow/DurableDeferred", "effect/workflow"),
            ("effect/Effect", ""),
            ("effect", ""),
            ("effect/internal/core", ""),
            ("@effect/platform/HttpClient", ""),
        ] {
            assert_eq!(effect_nested_barrel(input), expected, "{input:?}");
        }
    }

    // Go: TestNewFixTransformerNilForEmptyPrefs
    #[test]
    fn new_fix_transformer_none_for_empty_prefs() {
        assert!(new_fix_transformer(Some(&ResolvedEffectPluginOptions::default()), None).is_none());
    }

    // Go: TestNewFixTransformerAppliesPolicy
    #[test]
    fn new_fix_transformer_applies_policy() {
        let options = options(&["effect"], &[], &[], TopLevelNamedReexportsMode::Unset);
        let transformer = new_fix_transformer(Some(&options), None).expect("a transformer");
        let export = make_export("effect", "effect/Effect", "");
        let result = transformer.transform(&export, vec![named_fix("effect/Effect", "succeed")]);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].import_kind, lsproto::ImportKind::NAMESPACE);
    }

    // Go: TestNewFixTransformerPrefersExistingNamespaceUse
    #[test]
    fn new_fix_transformer_prefers_existing_namespace_use() {
        let options = options(&["effect"], &[], &[], TopLevelNamedReexportsMode::Unset);
        let transformer = new_fix_transformer(Some(&options), None).expect("a transformer");
        let export = make_export("effect", "effect/testing/TestClock", "");
        let use_namespace = Rc::new(Fix {
            auto_import_fix: lsproto::AutoImportFix {
                kind: lsproto::AutoImportFixKind::USE_NAMESPACE,
                import_kind: lsproto::ImportKind::NAMESPACE,
                module_specifier: "effect/testing/TestClock".to_string(),
                name: "testClockWith".to_string(),
                namespace_prefix: "TestClock".to_string(),
                ..Default::default()
            },
            ..Default::default()
        });
        let mut add_to_existing = make_add_new_fix(
            lsproto::ImportKind::NAMED,
            "effect/testing/TestClock",
            "testClockWith",
        );
        add_to_existing.kind = lsproto::AutoImportFixKind::ADD_TO_EXISTING;
        let result = transformer.transform(&export, vec![use_namespace, Rc::new(add_to_existing)]);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].kind, lsproto::AutoImportFixKind::USE_NAMESPACE);
    }
}
