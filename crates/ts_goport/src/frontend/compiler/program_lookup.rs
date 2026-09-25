//! Port of compiler/program.go lines 1788 to 2190: file lookup, include
//! explanations, resolution lookups, package name collection, the symlink
//! cache and the `plainJSErrors` set.

use crate::prelude::*;
use std::fmt::Write as _;
use std::sync::OnceLock;

// Go: program.go:73 packageNamesInfo
// PORT: U21 dropped the `packageNames` field and this type. It is here
// because only `collectPackageNames` uses it. Go `*collections.Set[string]`
// is an `FxHashSet<String>`.
#[derive(Clone, Debug, Default)]
pub struct PackageNamesInfo {
    pub resolved: FxHashSet<String>,
    pub unresolved: FxHashSet<String>,
    pub deep_import_packages: FxHashSet<String>,
}

/// Go callback `func(resolution T, moduleName string, mode core.ResolutionMode, filePath tspath.Path)`.
pub type ResolutionCallback<'f, T> = dyn FnMut(&T, &str, ResolutionMode, &Path) + 'f;

impl NewProgram {
    // Go: program.go:1788 (*Program).toPath
    pub fn to_path(&self, filename: &str) -> Path {
        to_path(filename, &self.get_current_directory(), self.use_case_sensitive_file_names())
    }

    // Go: program.go:1792 (*Program).GetSourceFile
    pub fn get_source_file(&self, filename: &str) -> Option<Rc<ParsedSourceFile>> {
        let path = self.to_path(filename);
        self.get_source_file_by_path(&path)
    }

    // Go: program.go:1797 (*Program).GetSourceFileForResolvedModule
    pub fn get_source_file_for_resolved_module(&self, file_name: &str) -> Option<Rc<ParsedSourceFile>> {
        let file = self.get_source_file(file_name);
        if file.is_none() {
            let filename = self.get_parse_file_redirect(file_name);
            if !filename.is_empty() {
                return self.get_source_file(&filename);
            }
        }
        file
    }

    // Go: program.go:1808 (*Program).FilesByPath
    pub fn files_by_path(&self) -> &FxHashMap<Path, Rc<ParsedSourceFile>> {
        &self.processed_files.files_by_path
    }

    // Go: program.go:1812 (*Program).GetSourceFileByPath
    pub fn get_source_file_by_path(&self, path: &Path) -> Option<Rc<ParsedSourceFile>> {
        self.processed_files.files_by_path.get(path).cloned()
    }

    // Go: program.go:1816 (*Program).HasSameFileNames
    // PORT: Go `maps.EqualFunc` treats a nil map as empty; a `None`
    // `redirect_files_by_path` is an empty map here.
    pub fn has_same_file_names(&self, other: &NewProgram) -> bool {
        fn equal_maps<V>(a: &FxHashMap<Path, V>, b: &FxHashMap<Path, V>, eq: impl Fn(&V, &V) -> bool) -> bool {
            a.len() == b.len() && a.iter().all(|(k, v1)| b.get(k).is_some_and(|v2| eq(v1, v2)))
        }
        let empty = FxHashMap::default();
        equal_maps(&self.processed_files.files_by_path, &other.processed_files.files_by_path, |a, b| {
            // checks for casing differences on case-insensitive file systems
            a.file_name() == b.file_name()
        }) && equal_maps(
            self.processed_files.redirect_files_by_path.as_ref().unwrap_or(&empty),
            other.processed_files.redirect_files_by_path.as_ref().unwrap_or(&empty),
            |a, b| a.file_name() == b.file_name(),
        )
    }

    // Go: program.go:1825 (*Program).GetSourceFiles
    pub fn get_source_files(&self) -> &[Rc<ParsedSourceFile>] {
        &self.processed_files.files
    }

    // Go: program.go:1830 (*Program).GetIncludeReasons
    // Testing only
    pub fn get_include_reasons(&self) -> &FxHashMap<Path, Vec<Rc<FileIncludeReason>>> {
        &self.processed_files.include_processor.file_include_reasons
    }

    // Go: program.go:1835 (*Program).IsMissingPath
    // Testing only
    pub fn is_missing_path(&self, path: &Path) -> bool {
        self.processed_files.missing_files.iter().any(|missing_path| self.to_path(missing_path) == *path)
    }

    // Go: program.go:1841 (*Program).ExplainFiles
    // PORT: Go writes to an `io.Writer`; this appends to a `String`. The
    // locale parameter is dropped (the port has only English messages).
    // Go `fmt.Fprintln(w, "  ", x)` puts one more space between the operands.
    // PORT: the Go `explainFile` closure increments `filesExplained`; here
    // the callers do it, so the loop condition can read the counter.
    pub fn explain_files(&self, w: &mut String) {
        let to_relative_file_name = |file_name: &str| {
            get_relative_path_from_directory(&self.get_current_directory(), file_name, &self.compare_paths_options)
        };
        let explain_file = |w: &mut String, file: &dyn HasFileName| {
            let _ = writeln!(w, "{}", to_relative_file_name(&file.file_name()));
            if let Some(reasons) = self.processed_files.include_processor.file_include_reasons.get(&file.path()) {
                for reason in reasons {
                    let _ = writeln!(w, "   {}", reason.to_diagnostic(self, true).localize());
                }
            }
            for diag in self.processed_files.include_processor.explain_redirect_and_implied_format(
                self,
                &file.path(),
                to_relative_file_name,
            ) {
                let _ = writeln!(w, "   {}", diag.localize());
            }
        };
        let mut files_explained: i32 = 0;

        let mut redirect_files: Vec<&RedirectsFile> =
            self.processed_files.redirect_files_by_path.iter().flat_map(|m| m.values()).collect();
        redirect_files.sort_by_key(|r| r.index);

        let files = self.get_source_files();
        let mut source_file_index = 0;
        let mut explain_source_files = |w: &mut String, files_explained: &mut i32, end_index: i32| {
            while *files_explained < end_index {
                explain_file(w, &*files[source_file_index]);
                *files_explained += 1;
                source_file_index += 1;
            }
        };

        for redirect_file in &redirect_files {
            // Explain all sourceFiles till we reach this redirectFile index
            explain_source_files(w, &mut files_explained, redirect_file.index);
            explain_file(w, *redirect_file);
            files_explained += 1;
        }

        // Explain any remaining sourceFiles
        explain_source_files(w, &mut files_explained, (files.len() + redirect_files.len()) as i32);
    }

    // Go: program.go:1880 (*Program).GetLibFileFromReference
    pub fn get_lib_file_from_reference(&self, ref_: &FileReference) -> Option<Rc<ParsedSourceFile>> {
        let (path, ok) = get_lib_file_name(&ref_.file_name);
        if !ok {
            return None;
        }
        self.processed_files.files_by_path.get(&Path(path)).cloned()
    }

    // Go: program.go:1891 (*Program).GetResolvedTypeReferenceDirectiveFromTypeReferenceDirective
    pub fn get_resolved_type_reference_directive_from_type_reference_directive(
        &self,
        type_ref: &FileReference,
        source_file: &ParsedSourceFile,
    ) -> Option<Rc<ResolvedTypeReferenceDirective>> {
        let resolutions = self.processed_files.type_resolutions_in_file.get(source_file.path())?;
        let key = ModeAwareCacheKey {
            name: type_ref.file_name.clone(),
            mode: self.get_mode_for_type_reference_directive_in_file(type_ref, source_file),
        };
        resolutions.get(&key).cloned()
    }

    // Go: program.go:1900 (*Program).GetResolvedTypeReferenceDirectives
    pub fn get_resolved_type_reference_directives(
        &self,
    ) -> &FxHashMap<Path, ModeAwareCache<Rc<ResolvedTypeReferenceDirective>>> {
        &self.processed_files.type_resolutions_in_file
    }

    // Go: program.go:1904 (*Program).getModeForTypeReferenceDirectiveInFile
    pub fn get_mode_for_type_reference_directive_in_file(
        &self,
        ref_: &FileReference,
        source_file: &ParsedSourceFile,
    ) -> ResolutionMode {
        if ref_.resolution_mode != RESOLUTION_MODE_NONE {
            return ref_.resolution_mode;
        }
        self.get_default_resolution_mode_for_file(source_file)
    }

    // Go: program.go:1911 (*Program).IsSourceFileFromExternalLibrary
    pub fn is_source_file_from_external_library(&self, file: &ParsedSourceFile) -> bool {
        self.processed_files.source_files_found_searching_node_modules.contains(file.path())
    }

    // Go: program.go:1915 (*Program).GetJSXRuntimeImportSpecifier
    // PORT: a Go nil map is `None`.
    pub fn get_jsx_runtime_import_specifier(&self, path: &Path) -> (String, Node) {
        if let Some(result) = self.processed_files.jsx_runtime_import_specifiers.as_ref().and_then(|m| m.get(path)) {
            return (result.module_reference.clone(), result.specifier);
        }
        (String::new(), Node::NIL)
    }

    // Go: program.go:1922 (*Program).GetImportHelpersImportSpecifier
    // PORT: a Go nil map is `None`; a missing entry is `Node::NIL`.
    pub fn get_import_helpers_import_specifier(&self, path: &Path) -> Node {
        self.processed_files
            .import_helpers_import_specifiers
            .as_ref()
            .and_then(|m| m.get(path).copied())
            .unwrap_or(Node::NIL)
    }

    // Go: program.go:1926 (*Program).SourceFileMayBeEmitted
    // PORT: Go `sourceFileMayBeEmitted` is in emitter.go. The emitter is out
    // of scope for the frontend port.
    pub fn source_file_may_be_emitted(&self, _source_file: &ParsedSourceFile, _force_dts_emit: bool) -> bool {
        unported!("sourceFileMayBeEmitted")
    }

    // Go: program.go:1930 (*Program).ResolvedPackageNames
    pub fn resolved_package_names(&self) -> &FxHashSet<String> {
        &self.collect_package_names().resolved
    }

    // Go: program.go:1934 (*Program).UnresolvedPackageNames
    pub fn unresolved_package_names(&self) -> &FxHashSet<String> {
        &self.collect_package_names().unresolved
    }

    // Go: program.go:1938 (*Program).DeepImportPackageNames
    pub fn deep_import_package_names(&self) -> &FxHashSet<String> {
        &self.collect_package_names().deep_import_packages
    }

    // Go: program.go:1942 (*Program).collectPackageNames
    // PORT: `package_names` is Go `packageNames lazyValue[*packageNamesInfo]`.
    fn collect_package_names(&self) -> &PackageNamesInfo {
        self.package_names.get_value(|| {
            let mut package_names = PackageNamesInfo::default();
            let resolver = self.processed_files.resolver.as_ref().expect("program has a resolver");
            for file in &self.processed_files.files {
                if self.is_source_file_default_library(file.path())
                    || self.is_source_file_from_external_library(file)
                    || file.file_name().contains("/node_modules/")
                {
                    // Checking for /node_modules/ is a little imprecise, but ATA treats locally installed typings
                    // as root files, which would not pass IsSourceFileFromExternalLibrary.
                    continue;
                }
                for &imp in &file.imports {
                    if is_external_module_name_relative(imp.text()) {
                        continue;
                    }
                    if let Some(resolved_modules) = self.processed_files.resolved_modules.get(file.path()) {
                        let key = ModeAwareCacheKey {
                            name: imp.text().to_string(),
                            mode: self.get_mode_for_usage_location(file, imp),
                        };
                        if let Some(resolved_module) = resolved_modules.get(&key)
                            && resolved_module.is_resolved()
                        {
                            if !resolved_module.is_external_library_import {
                                continue;
                            }
                            // Priority order for getting package name:
                            // 1. PackageId.Name (requires both name and version in package.json)
                            let mut name = resolved_module.package_id.name.clone();
                            if name.is_empty() {
                                // 2. GetPackageScopeForPath - get name from package.json in the package directory
                                if let Some(package_scope) =
                                    resolver.get_package_scope_for_path(&resolved_module.resolved_file_name)
                                    && package_scope.exists()
                                {
                                    let (scope_name, ok) = package_scope.contents.name.get_value();
                                    if ok {
                                        name = scope_name;
                                    }
                                }
                            }
                            if name.is_empty() {
                                // 3. GetPackageNameFromDirectory - extract from node_modules path
                                name = get_package_name_from_directory(&resolved_module.resolved_file_name);
                            }
                            // 4. If all fail, don't add empty string
                            if !name.is_empty() {
                                package_names.resolved.insert(name.clone());
                                // Detect deep imports: subpath imports in packages without exports.
                                // These are imports like "lodash/fp" where the package has no exports
                                // map, so auto-import can only find them via recursive directory search.
                                let (_, rest) = parse_package_name(imp.text());
                                if !rest.is_empty()
                                    && let Some(scope) =
                                        resolver.get_package_scope_for_path(&resolved_module.resolved_file_name)
                                    && scope.exists()
                                    && !scope.contents.exports.is_present()
                                {
                                    package_names
                                        .deep_import_packages
                                        .insert(get_package_name_from_types_package_name(&name));
                                }
                            }
                            continue;
                        }
                    }
                    package_names.unresolved.insert(imp.text().to_string());
                }
            }
            Rc::new(package_names)
        })
    }

    // Go: program.go:2002 (*Program).IsLibFile
    pub fn is_lib_file(&self, source_file: &ParsedSourceFile) -> bool {
        self.processed_files.lib_files.contains_key(source_file.path())
    }

    // Go: program.go:2007 (*Program).HasTSFile
    // PORT: Go `hasTSFileOnce` plus `hasTSFile` is `has_ts_file: OnceCell<bool>`.
    pub fn has_ts_file(&self) -> bool {
        *self.has_ts_file.get_or_init(|| {
            self.processed_files.files.iter().any(|file| has_implementation_ts_file_extension(file.file_name()))
        })
    }

    // Go: program.go:2019 (*Program).GetSymlinkCache
    // PORT: `known_symlinks` is Go `knownSymlinks lazyValue[*symlinks.KnownSymlinks]`.
    pub fn get_symlink_cache(&self) -> Rc<KnownSymlinks> {
        self.known_symlinks
            .get_value(|| {
                let mut known_symlinks =
                    new_known_symlink(&self.get_current_directory(), self.use_case_sensitive_file_names());

                // Resolved modules store realpath information when they're resolved inside node_modules
                if !self.processed_files.resolved_modules.is_empty()
                    || !self.processed_files.type_resolutions_in_file.is_empty()
                {
                    known_symlinks.set_symlinks_from_resolutions(
                        &|callback: &mut ResolutionCallback<'_, Rc<ResolvedModule>>, file: Option<&ParsedSourceFile>| {
                            self.for_each_resolved_module(callback, file);
                        },
                        &|callback: &mut ResolutionCallback<'_, Rc<ResolvedTypeReferenceDirective>>,
                          file: Option<&ParsedSourceFile>| {
                            self.for_each_resolved_type_reference_directive(callback, file);
                        },
                    );
                }

                // Check other dependencies for symlinks
                let resolver = self.processed_files.resolver.as_ref().expect("program has a resolver");
                let mut seen_package_jsons: FxHashSet<Path> = FxHashSet::default();
                for (file_path, meta) in &self.processed_files.source_file_meta_datas {
                    if meta.package_json_directory.is_empty() {
                        continue;
                    }
                    // PORT: Go passes a possibly nil file to `SourceFileMayBeEmitted`.
                    let source_file = self.get_source_file_by_path(file_path);
                    if !source_file.is_some_and(|f| self.source_file_may_be_emitted(&f, false))
                        || !seen_package_jsons.insert(self.to_path(&meta.package_json_directory))
                    {
                        continue;
                    }
                    let package_json_name = combine_paths(&meta.package_json_directory, &["package.json"]);
                    let info = self.get_package_json_info(&package_json_name);
                    let Some(contents) = info.as_ref().and_then(|info| info.get_contents()) else {
                        continue;
                    };

                    for dep in contents.get_runtime_dependency_names() {
                        // Skip work in common case: we already saved a symlink for this package directory
                        // in the node_modules adjacent to this package.json
                        let possible_directory_path =
                            self.to_path(&combine_paths(&meta.package_json_directory, &["node_modules", &dep]));
                        if known_symlinks.has_directory(&possible_directory_path) {
                            continue;
                        }
                        if !dep.starts_with("@types") {
                            let possible_types_directory_path = self.to_path(&combine_paths(
                                &meta.package_json_directory,
                                &["node_modules", &get_types_package_name(&dep)],
                            ));
                            if known_symlinks.has_directory(&possible_types_directory_path) {
                                continue;
                            }
                        }

                        if let Some(package_resolution) =
                            resolver.resolve_package_directory(&dep, &package_json_name, RESOLUTION_MODE_COMMON_JS, None)
                            && package_resolution.is_resolved()
                        {
                            known_symlinks.process_resolution(
                                &combine_paths(&package_resolution.original_path, &["package.json"]),
                                &combine_paths(&package_resolution.resolved_file_name, &["package.json"]),
                            );
                        }
                    }
                }
                Rc::new(known_symlinks)
            })
            .clone()
    }

    // Go: program.go:2072 (*Program).ResolveModuleName
    pub fn resolve_module_name(
        &self,
        module_name: &str,
        containing_file: &str,
        resolution_mode: ResolutionMode,
    ) -> Rc<ResolvedModule> {
        let resolver = self.processed_files.resolver.as_ref().expect("program has a resolver");
        let (resolved, _) = resolver.resolve_module_name(module_name, containing_file, resolution_mode, None);
        resolved
    }

    // Go: program.go:2077 (*Program).ForEachResolvedModule
    pub fn for_each_resolved_module(
        &self,
        callback: &mut ResolutionCallback<'_, Rc<ResolvedModule>>,
        file: Option<&ParsedSourceFile>,
    ) {
        for_each_resolution(&self.processed_files.resolved_modules, callback, file);
    }

    // Go: program.go:2081 (*Program).ForEachResolvedTypeReferenceDirective
    pub fn for_each_resolved_type_reference_directive(
        &self,
        callback: &mut ResolutionCallback<'_, Rc<ResolvedTypeReferenceDirective>>,
        file: Option<&ParsedSourceFile>,
    ) {
        for_each_resolution(&self.processed_files.type_resolutions_in_file, callback, file);
    }
}

// Go: program.go:2085 forEachResolution
pub fn for_each_resolution<T>(
    resolution_cache: &FxHashMap<Path, ModeAwareCache<T>>,
    callback: &mut ResolutionCallback<'_, T>,
    file: Option<&ParsedSourceFile>,
) {
    if let Some(file) = file {
        if let Some(resolutions) = resolution_cache.get(file.path()) {
            for (key, resolution) in resolutions {
                callback(resolution, &key.name, key.mode, file.path());
            }
        }
    } else {
        for (file_path, resolutions) in resolution_cache {
            for (key, resolution) in resolutions {
                callback(resolution, &key.name, key.mode, file_path);
            }
        }
    }
}

// Go: program.go:2095 plainJSErrors
// PORT: Go package-level set; built once on first use.
pub fn plain_js_errors() -> &'static FxHashSet<i32> {
    static PLAIN_JS_ERRORS: OnceLock<FxHashSet<i32>> = OnceLock::new();
    PLAIN_JS_ERRORS.get_or_init(|| {
        [
            // binder errors
            diag::Cannot_redeclare_block_scoped_variable_0.code() as i32,
            diag::A_module_cannot_have_multiple_default_exports.code() as i32,
            diag::Another_export_default_is_here.code() as i32,
            diag::The_first_export_default_is_here.code() as i32,
            diag::Identifier_expected_0_is_a_reserved_word_at_the_top_level_of_a_module.code() as i32,
            diag::Identifier_expected_0_is_a_reserved_word_in_strict_mode_Modules_are_automatically_in_strict_mode.code() as i32,
            diag::Identifier_expected_0_is_a_reserved_word_that_cannot_be_used_here.code() as i32,
            diag::X_constructor_is_a_reserved_word.code() as i32,
            diag::X_delete_cannot_be_called_on_an_identifier_in_strict_mode.code() as i32,
            diag::Code_contained_in_a_class_is_evaluated_in_JavaScript_s_strict_mode_which_does_not_allow_this_use_of_0_For_more_information_see_https_Colon_Slash_Slashdeveloper_mozilla_org_Slashen_US_Slashdocs_SlashWeb_SlashJavaScript_SlashReference_SlashStrict_mode.code() as i32,
            diag::Invalid_use_of_0_Modules_are_automatically_in_strict_mode.code() as i32,
            diag::Invalid_use_of_0_in_strict_mode.code() as i32,
            diag::A_label_is_not_allowed_here.code() as i32,
            diag::X_with_statements_are_not_allowed_in_strict_mode.code() as i32,
            // grammar errors
            diag::A_break_statement_can_only_be_used_within_an_enclosing_iteration_or_switch_statement.code() as i32,
            diag::A_break_statement_can_only_jump_to_a_label_of_an_enclosing_statement.code() as i32,
            diag::A_class_declaration_without_the_default_modifier_must_have_a_name.code() as i32,
            diag::A_class_member_cannot_have_the_0_keyword.code() as i32,
            diag::A_comma_expression_is_not_allowed_in_a_computed_property_name.code() as i32,
            diag::A_continue_statement_can_only_be_used_within_an_enclosing_iteration_statement.code() as i32,
            diag::A_continue_statement_can_only_jump_to_a_label_of_an_enclosing_iteration_statement.code() as i32,
            diag::A_default_clause_cannot_appear_more_than_once_in_a_switch_statement.code() as i32,
            diag::A_default_export_must_be_at_the_top_level_of_a_file_or_module_declaration.code() as i32,
            diag::A_definite_assignment_assertion_is_not_permitted_in_this_context.code() as i32,
            diag::A_destructuring_declaration_must_have_an_initializer.code() as i32,
            diag::A_get_accessor_cannot_have_parameters.code() as i32,
            diag::A_rest_element_cannot_contain_a_binding_pattern.code() as i32,
            diag::A_rest_element_cannot_have_a_property_name.code() as i32,
            diag::A_rest_element_cannot_have_an_initializer.code() as i32,
            diag::A_rest_element_must_be_last_in_a_destructuring_pattern.code() as i32,
            diag::A_rest_parameter_cannot_have_an_initializer.code() as i32,
            diag::A_rest_parameter_must_be_last_in_a_parameter_list.code() as i32,
            diag::A_rest_parameter_or_binding_pattern_may_not_have_a_trailing_comma.code() as i32,
            diag::A_return_statement_cannot_be_used_inside_a_class_static_block.code() as i32,
            diag::A_set_accessor_cannot_have_rest_parameter.code() as i32,
            diag::A_set_accessor_must_have_exactly_one_parameter.code() as i32,
            diag::An_export_declaration_can_only_be_used_at_the_top_level_of_a_module.code() as i32,
            diag::An_export_declaration_cannot_have_modifiers.code() as i32,
            diag::An_import_declaration_can_only_be_used_at_the_top_level_of_a_module.code() as i32,
            diag::An_import_declaration_cannot_have_modifiers.code() as i32,
            diag::An_object_member_cannot_be_declared_optional.code() as i32,
            diag::Argument_of_dynamic_import_cannot_be_spread_element.code() as i32,
            diag::Cannot_assign_to_private_method_0_Private_methods_are_not_writable.code() as i32,
            diag::Cannot_redeclare_identifier_0_in_catch_clause.code() as i32,
            diag::Catch_clause_variable_cannot_have_an_initializer.code() as i32,
            diag::Class_decorators_can_t_be_used_with_static_private_identifier_Consider_removing_the_experimental_decorator.code() as i32,
            diag::Classes_can_only_extend_a_single_class.code() as i32,
            diag::Classes_may_not_have_a_field_named_constructor.code() as i32,
            diag::Did_you_mean_to_use_a_Colon_An_can_only_follow_a_property_name_when_the_containing_object_literal_is_part_of_a_destructuring_pattern.code() as i32,
            diag::Duplicate_label_0.code() as i32,
            diag::Dynamic_imports_can_only_accept_a_module_specifier_and_an_optional_set_of_attributes_as_arguments.code() as i32,
            diag::X_for_await_loops_cannot_be_used_inside_a_class_static_block.code() as i32,
            diag::JSX_attributes_must_only_be_assigned_a_non_empty_expression.code() as i32,
            diag::JSX_elements_cannot_have_multiple_attributes_with_the_same_name.code() as i32,
            diag::JSX_expressions_may_not_use_the_comma_operator_Did_you_mean_to_write_an_array.code() as i32,
            diag::JSX_property_access_expressions_cannot_include_JSX_namespace_names.code() as i32,
            diag::Jump_target_cannot_cross_function_boundary.code() as i32,
            diag::Line_terminator_not_permitted_before_arrow.code() as i32,
            diag::Modifiers_cannot_appear_here.code() as i32,
            diag::Only_a_single_variable_declaration_is_allowed_in_a_for_in_statement.code() as i32,
            diag::Only_a_single_variable_declaration_is_allowed_in_a_for_of_statement.code() as i32,
            diag::Private_identifiers_are_not_allowed_outside_class_bodies.code() as i32,
            diag::Private_identifiers_are_only_allowed_in_class_bodies_and_may_only_be_used_as_part_of_a_class_member_declaration_property_access_or_on_the_left_hand_side_of_an_in_expression.code() as i32,
            diag::Property_0_is_not_accessible_outside_class_1_because_it_has_a_private_identifier.code() as i32,
            diag::Tagged_template_expressions_are_not_permitted_in_an_optional_chain.code() as i32,
            diag::The_left_hand_side_of_a_for_of_statement_may_not_be_async.code() as i32,
            diag::The_variable_declaration_of_a_for_in_statement_cannot_have_an_initializer.code() as i32,
            diag::The_variable_declaration_of_a_for_of_statement_cannot_have_an_initializer.code() as i32,
            diag::Trailing_comma_not_allowed.code() as i32,
            diag::Variable_declaration_list_cannot_be_empty.code() as i32,
            diag::X_0_and_1_operations_cannot_be_mixed_without_parentheses.code() as i32,
            diag::X_0_expected.code() as i32,
            diag::X_0_is_not_a_valid_meta_property_for_keyword_1_Did_you_mean_2.code() as i32,
            diag::X_0_list_cannot_be_empty.code() as i32,
            diag::X_0_modifier_already_seen.code() as i32,
            diag::X_0_modifier_cannot_appear_on_a_constructor_declaration.code() as i32,
            diag::X_0_modifier_cannot_appear_on_a_module_or_namespace_element.code() as i32,
            diag::X_0_modifier_cannot_appear_on_a_parameter.code() as i32,
            diag::X_0_modifier_cannot_appear_on_class_elements_of_this_kind.code() as i32,
            diag::X_0_modifier_cannot_be_used_here.code() as i32,
            diag::X_0_modifier_must_precede_1_modifier.code() as i32,
            diag::X_0_declarations_can_only_be_declared_inside_a_block.code() as i32,
            diag::X_0_declarations_must_be_initialized.code() as i32,
            diag::X_extends_clause_already_seen.code() as i32,
            diag::X_let_is_not_allowed_to_be_used_as_a_name_in_let_or_const_declarations.code() as i32,
            diag::Class_constructor_may_not_be_a_generator.code() as i32,
            diag::Class_constructor_may_not_be_an_accessor.code() as i32,
            diag::X_await_expressions_are_only_allowed_within_async_functions_and_at_the_top_levels_of_modules.code() as i32,
            diag::X_await_using_statements_are_only_allowed_within_async_functions_and_at_the_top_levels_of_modules.code() as i32,
            diag::Private_field_0_must_be_declared_in_an_enclosing_class.code() as i32,
            // Type errors
            diag::This_condition_will_always_return_0_since_JavaScript_compares_objects_by_reference_not_value.code() as i32,
        ]
        .into_iter()
        .collect()
    })
}
