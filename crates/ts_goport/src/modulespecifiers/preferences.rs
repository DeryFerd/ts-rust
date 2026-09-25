//! Port of modulespecifiers/preferences.go.

use crate::prelude::*;

use super::tspath;
use super::types::*;

// Go: modulespecifiers/preferences.go:14 shouldAllowImportingTsExtension
// Program errors validate that `noEmit` or `emitDeclarationOnly` is also set,
// so this function doesn't check them to avoid propagating errors.
pub(crate) fn should_allow_importing_ts_extension(compiler_options: &CompilerOptions, from_file_name: &str) -> bool {
    compiler_options.get_allow_importing_ts_extensions()
        || !from_file_name.is_empty() && tspath::is_declaration_file_name(from_file_name)
}

// Go: modulespecifiers/preferences.go:18 usesExtensionsOnImports
fn uses_extensions_on_imports(file: &dyn SourceFileForSpecifierGeneration) -> bool {
    for r in file.imports() {
        let text = r.text();
        if tspath::path_is_relative(text)
            && !tspath::file_extension_is_one_of(text, tspath::EXTENSIONS_NOT_SUPPORTING_EXTENSIONLESS_RESOLUTION)
        {
            return tspath::has_ts_file_extension(text) || tspath::has_js_file_extension(text);
        }
    }
    false
}

// Go: modulespecifiers/preferences.go:28 inferPreference
fn infer_preference(
    resolution_mode: ResolutionMode,
    source_file: Option<&dyn SourceFileForSpecifierGeneration>,
    module_resolution_is_node_next: bool,
) -> ModuleSpecifierEnding {
    let mut uses_js_extensions = false;
    let mut specifiers: Vec<Node> = Vec::new();
    if let Some(sf) = source_file.filter(|sf| !sf.imports().is_empty()) {
        specifiers = sf.imports();
    } else if source_file.is_some_and(|sf| sf.is_js()) {
        // !!! TODO: JS support
        // specifiers = core.Map(getRequiresAtTopOfFile(sourceFile), func(d *ast.Node) *ast.Node { return d.arguments[0] })
    }

    for specifier in specifiers {
        let path = specifier.text();
        if tspath::path_is_relative(path) {
            // !!! TODO: proper resolutionMode support
            if module_resolution_is_node_next && resolution_mode == RESOLUTION_MODE_COMMON_JS
            /* && getModeForUsageLocation(sourceFile!, specifier, compilerOptions) === ModuleKind.ESNext */
            {
                // We're trying to decide a preference for a CommonJS module specifier, but looking at an ESM import.
                continue;
            }
            if tspath::file_extension_is_one_of(path, tspath::EXTENSIONS_NOT_SUPPORTING_EXTENSIONLESS_RESOLUTION) {
                // These extensions are not optional, so do not indicate a preference.
                continue;
            }
            if tspath::has_ts_file_extension(path) {
                return ModuleSpecifierEnding::TsExtension;
            }
            if tspath::has_js_file_extension(path) {
                uses_js_extensions = true;
            }
        }
    }

    if uses_js_extensions {
        return ModuleSpecifierEnding::JsExtension;
    }
    ModuleSpecifierEnding::Minimal
}

// Go: modulespecifiers/preferences.go:66 getModuleSpecifierEndingPreference
fn get_module_specifier_ending_preference(
    pref: ImportModuleSpecifierEndingPreference,
    resolution_mode: ResolutionMode,
    compiler_options: &CompilerOptions,
    source_file: Option<&dyn SourceFileForSpecifierGeneration>,
) -> ModuleSpecifierEnding {
    let module_resolution = compiler_options.get_module_resolution_kind();
    let module_resolution_is_node_next =
        ModuleResolutionKind::NODE16 <= module_resolution && module_resolution <= ModuleResolutionKind::NODE_NEXT;

    if pref == ImportModuleSpecifierEndingPreference::Js
        || resolution_mode == RESOLUTION_MODE_ESM && module_resolution_is_node_next
    {
        // Extensions are explicitly requested or required. Now choose between .js and .ts.
        if !should_allow_importing_ts_extension(compiler_options, "") {
            return ModuleSpecifierEnding::JsExtension;
        }
        // `allowImportingTsExtensions` is a strong signal, so use .ts unless the file
        // already uses .js extensions and no .ts extensions.
        if infer_preference(resolution_mode, source_file, module_resolution_is_node_next)
            != ModuleSpecifierEnding::JsExtension
        {
            return ModuleSpecifierEnding::TsExtension;
        }
        return ModuleSpecifierEnding::JsExtension;
    }

    if pref == ImportModuleSpecifierEndingPreference::Minimal {
        return ModuleSpecifierEnding::Minimal;
    }

    if pref == ImportModuleSpecifierEndingPreference::Index {
        return ModuleSpecifierEnding::Index;
    }

    // No preference was specified.
    // Look at imports and/or requires to guess whether .js, .ts, or extensionless imports are preferred.
    // N.B. that `Index` detection is not supported since it would require file system probing to do
    // accurately, and more importantly, literally nobody wants `Index` and its existence is a mystery.
    if !should_allow_importing_ts_extension(compiler_options, "") {
        // If .ts imports are not valid, we only need to see one .js import to go with that.
        if source_file.is_some_and(uses_extensions_on_imports) {
            return ModuleSpecifierEnding::JsExtension;
        }
        return ModuleSpecifierEnding::Minimal;
    }

    infer_preference(resolution_mode, source_file, module_resolution_is_node_next)
}

// Go: modulespecifiers/preferences.go:115 getPreferredEnding
fn get_preferred_ending(
    prefs: &UserPreferences,
    host: &dyn ModuleSpecifierGenerationHost,
    compiler_options: &CompilerOptions,
    importing_source_file: &dyn SourceFileForSpecifierGeneration,
    old_import_specifier: &str,
    mut resolution_mode: ResolutionMode,
) -> ModuleSpecifierEnding {
    if !old_import_specifier.is_empty() {
        if tspath::has_js_file_extension(old_import_specifier) {
            return ModuleSpecifierEnding::JsExtension;
        }
        if old_import_specifier.ends_with("/index") {
            return ModuleSpecifierEnding::Index;
        }
    }
    if resolution_mode == RESOLUTION_MODE_NONE {
        resolution_mode = host.get_default_resolution_mode_for_file(importing_source_file.node());
    }
    get_module_specifier_ending_preference(
        prefs.import_module_specifier_ending,
        resolution_mode,
        compiler_options,
        Some(importing_source_file),
    )
}

// Go: modulespecifiers/preferences.go:141 ModuleSpecifierPreferences
// PORT: Go stores a closure over the arguments of getModuleSpecifierPreferences.
// The Rust closure borrows them for `'a`.
pub struct ModuleSpecifierPreferences<'a> {
    pub relative_preference: RelativePreferenceKind,
    pub get_allowed_endings_in_preferred_order: Box<dyn Fn(ResolutionMode) -> Vec<ModuleSpecifierEnding> + 'a>,
    pub exclude_regexes: Vec<String>,
}

// Go: modulespecifiers/preferences.go:147 GetAllowedEndingsInPreferredOrder
pub fn get_allowed_endings_in_preferred_order(
    prefs: &UserPreferences,
    host: &dyn ModuleSpecifierGenerationHost,
    compiler_options: &CompilerOptions,
    importing_source_file: &dyn SourceFileForSpecifierGeneration,
    old_import_specifier: &str,
    syntax_implied_node_format: ResolutionMode,
) -> Vec<ModuleSpecifierEnding> {
    use ModuleSpecifierEnding::*;
    let mut preferred_ending = get_preferred_ending(
        prefs,
        host,
        compiler_options,
        importing_source_file,
        old_import_specifier,
        RESOLUTION_MODE_NONE,
    );
    let resolution_mode = host.get_default_resolution_mode_for_file(importing_source_file.node());
    if resolution_mode != syntax_implied_node_format {
        preferred_ending = get_preferred_ending(
            prefs,
            host,
            compiler_options,
            importing_source_file,
            old_import_specifier,
            syntax_implied_node_format,
        );
    }
    let module_resolution = compiler_options.get_module_resolution_kind();
    let module_resolution_is_node_next =
        ModuleResolutionKind::NODE16 <= module_resolution && module_resolution <= ModuleResolutionKind::NODE_NEXT;
    let allow_importing_ts_extension =
        should_allow_importing_ts_extension(compiler_options, &importing_source_file.file_name());
    if syntax_implied_node_format == RESOLUTION_MODE_ESM && module_resolution_is_node_next {
        if allow_importing_ts_extension {
            return vec![TsExtension, JsExtension];
        }
        return vec![JsExtension];
    }
    match preferred_ending {
        JsExtension => {
            if allow_importing_ts_extension {
                return vec![JsExtension, TsExtension, Minimal, Index];
            }
            vec![JsExtension, Minimal, Index]
        }
        TsExtension => vec![TsExtension, Minimal, JsExtension, Index],
        Index => {
            if allow_importing_ts_extension {
                return vec![Index, Minimal, TsExtension, JsExtension];
            }
            vec![Index, Minimal, JsExtension]
        }
        Minimal => {
            if allow_importing_ts_extension {
                return vec![Minimal, Index, TsExtension, JsExtension];
            }
            vec![Minimal, Index, JsExtension]
        }
    }
}

// Go: modulespecifiers/preferences.go:207 getModuleSpecifierPreferences
pub(crate) fn get_module_specifier_preferences<'a>(
    prefs: &'a UserPreferences,
    host: &'a dyn ModuleSpecifierGenerationHost,
    compiler_options: &'a CompilerOptions,
    importing_source_file: &'a dyn SourceFileForSpecifierGeneration,
    old_import_specifier: &'a str,
) -> ModuleSpecifierPreferences<'a> {
    let excludes = prefs.auto_import_specifier_exclude_regexes.clone();
    let mut relative_preference = RelativePreferenceKind::Shortest;
    if !old_import_specifier.is_empty() {
        if tspath::is_external_module_name_relative(old_import_specifier) {
            relative_preference = RelativePreferenceKind::Relative;
        } else {
            relative_preference = RelativePreferenceKind::NonRelative;
        }
    } else {
        match prefs.import_module_specifier_preference {
            ImportModuleSpecifierPreference::Relative => relative_preference = RelativePreferenceKind::Relative,
            ImportModuleSpecifierPreference::NonRelative => relative_preference = RelativePreferenceKind::NonRelative,
            ImportModuleSpecifierPreference::ProjectRelative => {
                relative_preference = RelativePreferenceKind::ExternalNonRelative
            }
            // all others are shortest
            _ => {}
        }
    }

    let get_allowed_endings_in_preferred_order = move |syntax_implied_node_format: ResolutionMode| {
        get_allowed_endings_in_preferred_order(
            prefs,
            host,
            compiler_options,
            importing_source_file,
            old_import_specifier,
            syntax_implied_node_format,
        )
    };

    ModuleSpecifierPreferences {
        exclude_regexes: excludes,
        relative_preference,
        get_allowed_endings_in_preferred_order: Box::new(get_allowed_endings_in_preferred_order),
    }
}
