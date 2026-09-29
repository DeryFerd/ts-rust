//! Port of Go `ls/file_rename.go`.
//!
//! PORT: Go `*compiler.Program` is `&'static compiler::NewProgram`. Go
//! `*change.Tracker` is `&mut change::Tracker`. Go passes an
//! `*ast.SourceFile` where a program method takes an `ast.HasFileName`; here
//! that is `autoimport::source_file_has_file_name(file)`.

use crate::ls::prelude::*;

// Go: ls/file_rename.go:20 pathUpdater
// PORT: a Go func type. `createPathUpdater` returns it boxed; other functions
// take it as `&PathUpdater`.
pub type PathUpdater<'a> = dyn Fn(&str) -> (String, bool) + 'a;

// Go: ls/file_rename.go:22 toImport
#[derive(Clone, Debug, Default)]
pub struct ToImport {
    pub new_file_name: String,
    pub updated: bool,
}

// Go: ls/file_rename.go:27 movedFile
#[derive(Clone, Debug, Default)]
pub struct MovedFile {
    pub source_file: Node,
    pub new_file_name: String,
}

impl LanguageService {
    // Go: ls/file_rename.go:27 GetEditsForFileRename
    pub fn get_edits_for_file_rename(
        &self,
        ctx: &Context,
        old_uri: &lsproto::DocumentUri,
        new_uri: &lsproto::DocumentUri,
    ) -> Vec<lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile> {
        let program = self.get_program();
        let old_path = old_uri.file_name();
        let new_path = new_uri.file_name();

        let old_to_new = self.create_path_updater(&old_path, &new_path);

        let mut change_tracker = change::new_tracker(
            ctx,
            program.options(),
            self.format_options(),
            self.converters.clone(),
        );
        self.update_tsconfig_files(
            program,
            &mut change_tracker,
            &*old_to_new,
            &old_path,
            &new_path,
        );
        self.update_imports_for_file_rename(program, &mut change_tracker, &*old_to_new);

        let mut document_changes: Vec<
            lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile,
        > = Vec::new();

        // When renaming e.g. `foo.d.css.ts` -> `bar.d.css.ts`, also rename `foo.css` -> `bar.css` if it exists.
        if tspath::is_declaration_file_name(&old_path)
            && tspath::is_declaration_file_name(&new_path)
        {
            let dts_ext = tspath::get_declaration_file_extension(&old_path);
            let original_extensions =
                tspath::get_possible_original_input_extension_for_extension(&dts_ext);
            for ext in &original_extensions {
                let old_original_path = tspath::change_full_extension(&old_path, ext);
                if self.host.file_exists(&old_original_path) {
                    let new_dts_ext = tspath::get_declaration_file_extension(&old_path);
                    let new_original_extensions =
                        tspath::get_possible_original_input_extension_for_extension(&new_dts_ext);
                    if new_original_extensions.contains(ext) {
                        let new_original_path = tspath::change_full_extension(&new_path, ext);
                        document_changes.push(
                            lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile {
                                rename_file: Some(lsproto::RenameFile {
                                    old_uri: lsconv::file_name_to_document_uri(&old_original_path),
                                    new_uri: lsconv::file_name_to_document_uri(&new_original_path),
                                    ..Default::default()
                                }),
                                ..Default::default()
                            },
                        );
                    }
                }
            }
        }

        // PORT: Go ranges over the `GetChanges` map (random order). The
        // tracker returns an IndexMap in the order files were first changed.
        let (changes, _) = change_tracker.get_changes();
        for (file_name, edits) in changes {
            let uri = lsconv::file_name_to_document_uri(&file_name);
            let mut lsp_edits: Vec<lsproto::TextEditOrAnnotatedTextEditOrSnippetTextEdit> =
                Vec::with_capacity(edits.len());
            for edit in edits {
                lsp_edits.push(lsproto::TextEditOrAnnotatedTextEditOrSnippetTextEdit {
                    text_edit: Some(edit),
                    ..Default::default()
                });
            }
            document_changes.push(
                lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile {
                    text_document_edit: Some(lsproto::TextDocumentEdit {
                        text_document: lsproto::OptionalVersionedTextDocumentIdentifier {
                            uri,
                            ..Default::default()
                        },
                        edits: lsp_edits,
                    }),
                    ..Default::default()
                },
            );
        }

        document_changes
    }

    // Go: ls/file_rename.go:89 createPathUpdater
    // PORT: the Go closure calls `l.UseCaseSensitiveFileNames()` on each call;
    // the boxed closure borrows `self` for that.
    pub fn create_path_updater<'a>(
        &'a self,
        old_path: &str,
        new_path: &str,
    ) -> Box<PathUpdater<'a>> {
        let compare_options = tspath::ComparePathsOptions {
            use_case_sensitive_file_names: self.use_case_sensitive_file_names(),
            ..Default::default()
        };
        let trimmed_old_path = tspath::remove_trailing_directory_separator(old_path).to_string();
        let old_path = old_path.to_string();
        let new_path = new_path.to_string();
        Box::new(move |path: &str| -> (String, bool) {
            if tspath::compare_paths(path, &old_path, &compare_options) == 0 {
                return (new_path.clone(), true);
            }
            // Trim the directory prefix ourselves (rather than using
            // tspath.StartsWithDirectory followed by a separate slice on
            // len(oldPath)) so the containment check and the suffix we return can
            // never disagree, and so we don't slice path by a byte count derived
            // from a canonicalized/differently-cased string: case-folding can
            // change a path's UTF-8 byte length without changing its rune count
            // (e.g. the Kelvin sign '\u212A' folds to the single-byte 'k'), which
            // could otherwise put len(oldPath) out of range of path.
            // (tsgo#4900)
            if let Some(suffix) = tspath::trim_file_path_prefix(
                path,
                &trimmed_old_path,
                self.use_case_sensitive_file_names(),
            ) && (suffix.starts_with('/') || suffix.starts_with('\\'))
            {
                return (format!("{new_path}{suffix}"), true);
            }
            (String::new(), false)
        })
    }

    // Go: ls/file_rename.go:94 updateTsconfigFiles
    pub fn update_tsconfig_files(
        &self,
        program: &'static compiler::NewProgram,
        change_tracker: &mut change::Tracker,
        old_to_new: &PathUpdater<'_>,
        old_path: &str,
        new_path: &str,
    ) {
        // PORT: Go `program.CommandLine()` can be nil; here it is always set.
        let command_line = program.command_line();
        let Some(config_file_info) = command_line.config_file.as_ref() else {
            return;
        };

        let config_file = config_file_info.source_file;
        if config_file.is_nil() {
            return;
        }
        let config_dir = tspath::get_directory_path(source_file_file_name(config_file));
        let json_object_literal = get_ts_config_object_literal_expression(config_file);
        if json_object_literal.is_nil() {
            return;
        }

        for_each_object_property(
            json_object_literal,
            &mut |property: Node, property_name: &str| match property_name {
                "files" | "include" | "exclude" => {
                    let found_exact_match = update_paths_property(
                        config_file,
                        &config_dir,
                        property,
                        change_tracker,
                        old_to_new,
                        &self.converters,
                        self.use_case_sensitive_file_names(),
                    );
                    if found_exact_match
                        || property_name != "include"
                        || !is_array_literal_expression(property.initializer())
                    {
                        return;
                    }
                    let (old_spec, is_default) = command_line.get_matched_include_spec(old_path);
                    if !old_spec.is_empty() && !is_default {
                        let (new_spec, _) = command_line.get_matched_include_spec(new_path);
                        if new_spec.is_empty() {
                            let elements = property.initializer().elements();
                            if !elements.is_empty() {
                                let last_element = elements.get(elements.len() - 1);
                                let new_node = change_tracker.node_factory().new_string_literal(
                                    relative_path_from_directory(
                                        &config_dir,
                                        new_path,
                                        self.use_case_sensitive_file_names(),
                                    ),
                                    TokenFlags::NONE,
                                );
                                change_tracker.insert_node_after(
                                    config_file,
                                    last_element,
                                    new_node,
                                );
                            }
                        }
                    }
                }
                "compilerOptions" => {
                    if !is_object_literal_expression(property.initializer()) {
                        return;
                    }
                    for_each_object_property(
                        property.initializer(),
                        &mut |property: Node, property_name: &str| {
                            let option =
                                tsoptions::COMMAND_LINE_COMPILER_OPTIONS_MAP.get(property_name);
                            if let Some(option) = option {
                                let element_option = option.elements();
                                if option.is_file_path
                                    || (option.kind == tsoptions::CommandLineOptionKind::LIST
                                        && element_option
                                            .is_some_and(|element| element.is_file_path))
                                {
                                    update_paths_property(
                                        config_file,
                                        &config_dir,
                                        property,
                                        change_tracker,
                                        old_to_new,
                                        &self.converters,
                                        self.use_case_sensitive_file_names(),
                                    );
                                    return;
                                }
                            }

                            if property_name != "paths"
                                || !is_object_literal_expression(property.initializer())
                            {
                                return;
                            }
                            for_each_object_property(
                                property.initializer(),
                                &mut |paths_property: Node, _: &str| {
                                    if !is_array_literal_expression(paths_property.initializer()) {
                                        return;
                                    }
                                    for element in paths_property.initializer().elements().iter() {
                                        try_update_config_string(
                                            config_file,
                                            &config_dir,
                                            element,
                                            change_tracker,
                                            old_to_new,
                                            &self.converters,
                                            self.use_case_sensitive_file_names(),
                                        );
                                    }
                                },
                            );
                        },
                    );
                }
                _ => {}
            },
        );
    }
}

// Go: ls/file_rename.go:159 updatePathsProperty
pub fn update_paths_property(
    config_file: Node,
    config_dir: &str,
    property: Node,
    change_tracker: &mut change::Tracker,
    old_to_new: &PathUpdater<'_>,
    converters: &lsconv::Converters,
    use_case_sensitive_file_names: bool,
) -> bool {
    let mut elements: Vec<Node> = vec![property.initializer()];
    if is_array_literal_expression(property.initializer()) {
        elements = property.initializer().elements().to_vec();
    }

    let mut found_exact_match = false;
    for element in elements {
        found_exact_match = try_update_config_string(
            config_file,
            config_dir,
            element,
            change_tracker,
            old_to_new,
            converters,
            use_case_sensitive_file_names,
        ) || found_exact_match;
    }
    found_exact_match
}

// Go: ls/file_rename.go:172 tryUpdateConfigString
pub fn try_update_config_string(
    config_file: Node,
    config_dir: &str,
    element: Node,
    change_tracker: &mut change::Tracker,
    old_to_new: &PathUpdater<'_>,
    converters: &lsconv::Converters,
    use_case_sensitive_file_names: bool,
) -> bool {
    if !is_string_literal(element) {
        return false;
    }

    let element_file_name =
        tspath::normalize_path(&tspath::combine_paths(config_dir, &[element.text()]));
    let (updated, ok) = old_to_new(&element_file_name);
    if !ok {
        return false;
    }

    let text_range = TextRange::new(
        get_token_pos_of_node(element, config_file, false) + 1,
        element.end() - 1,
    );
    let (lsp_range, fidelity) = converters.to_lsp_range(&config_file, text_range);
    crate::go_assert!(fidelity.is_exact(), "config files are not content-mapped");
    change_tracker.replace_range_with_text(
        config_file,
        lsp_range,
        &relative_path_from_directory(config_dir, &updated, use_case_sensitive_file_names),
    );
    true
}

impl LanguageService {
    // Go: ls/file_rename.go:190 updateRelativePath
    pub fn update_relative_path(
        &self,
        old_to_new: &PathUpdater<'_>,
        old_import_from_path: &str,
        new_import_from_path: &str,
        relative_specifier: &str,
    ) -> String {
        let old_absolute = tspath::normalize_path(&tspath::combine_paths(
            &tspath::get_directory_path(old_import_from_path),
            &[relative_specifier],
        ));
        let (mut new_absolute, ok) = old_to_new(&old_absolute);
        if !ok {
            new_absolute = old_absolute;
        }
        relative_import_path_from_directory(
            &tspath::get_directory_path(new_import_from_path),
            &new_absolute,
            self.use_case_sensitive_file_names(),
        )
    }

    // Go: ls/file_rename.go:199 updateImportsForFileRename
    pub fn update_imports_for_file_rename(
        &self,
        program: &'static compiler::NewProgram,
        change_tracker: &mut change::Tracker,
        old_to_new: &PathUpdater<'_>,
    ) {
        let all_files: Vec<Node> = program
            .get_source_files()
            .iter()
            .map(|source_file| source_file.root)
            .collect();
        // Go: `defer done()`; `_done` releases the lease at the end of the scope.
        let (checker_rc, _done) =
            ls_program::get_type_checker(program, &crate::gostd::context::background());
        let checker = &mut *checker_rc.borrow_mut();
        let module_specifier_preferences = self.user_preferences().module_specifier_preferences();

        let mut moved_files: Vec<MovedFile> = Vec::new();
        for &source_file in &all_files {
            let (new_file_name, ok) = old_to_new(source_file_original_file_name(source_file));
            if ok {
                moved_files.push(MovedFile {
                    source_file,
                    new_file_name,
                });
            }
        }

        for source_file in all_files {
            let old_file_name = source_file_original_file_name(source_file);
            let (new_from_old, file_moved) = old_to_new(old_file_name);
            let mut new_import_from_path = old_file_name.to_string();
            if file_moved {
                new_import_from_path = new_from_old;
            }

            for ref_ in &source_file_info(source_file).referenced_files {
                if !tspath::is_external_module_name_relative(&ref_.file_name) {
                    continue;
                }
                let updated = self.update_relative_path(
                    old_to_new,
                    old_file_name,
                    &new_import_from_path,
                    &ref_.file_name,
                );
                if updated != ref_.file_name {
                    change_tracker.replace_text_range_with_text(source_file, ref_.range, &updated);
                }
            }

            for import_string_literal in source_file_imports(source_file).iter() {
                let updated = self.get_updated_import_specifier(
                    program,
                    checker,
                    source_file,
                    import_string_literal,
                    old_to_new,
                    &moved_files,
                    &new_import_from_path,
                    file_moved,
                    &module_specifier_preferences,
                );
                if !updated.is_empty() && updated != import_string_literal.text() {
                    change_tracker.replace_text_range_with_text(
                        source_file,
                        create_string_text_range(source_file, import_string_literal),
                        &updated,
                    );
                }
            }
        }
    }

    // Go: ls/file_rename.go:233 getUpdatedImportSpecifier
    // We assume the source file did not move to a different program.
    // PORT: Go passes the program as the `ModuleSpecifierGenerationHost`;
    // here that is `modulespecifiers::ProgramHost` (the installed program).
    pub fn get_updated_import_specifier(
        &self,
        program: &'static compiler::NewProgram,
        checker: &mut Checker,
        source_file: Node, // old importing source file
        import_literal: Node,
        old_to_new: &PathUpdater<'_>,
        moved_files: &[MovedFile],
        new_import_from_path: &str,
        importing_source_file_moved: bool,
        user_preferences: &modulespecifiers::UserPreferences,
    ) -> String {
        let imported_module_symbol = checker.get_symbol_at_location_exported(import_literal);
        if is_ambient_module_symbol(&checker.symbols, imported_module_symbol) {
            return String::new();
        }

        let target = get_source_file_to_import(program, source_file, import_literal, old_to_new);

        let Some(target) = target else {
            // First fall back: try every file affected by the rename to see if any of them would match the import specifier, and if so, obtain the updated specifier for that file.
            let updated = get_updated_import_specifier_from_moved_source_files(
                program,
                source_file,
                import_literal,
                moved_files,
                new_import_from_path,
                user_preferences,
            );
            if !updated.is_empty() && updated != import_literal.text() {
                return updated;
            }
            // Fall back to a regular path update for unresolved module.
            if tspath::is_external_module_name_relative(import_literal.text()) {
                return self.update_relative_path(
                    old_to_new,
                    source_file_file_name(source_file),
                    new_import_from_path,
                    import_literal.text(),
                );
            }
            return String::new();
        };

        // Optimization: neither the importing or imported file changed.
        if !target.updated
            && !(importing_source_file_moved
                && tspath::is_external_module_name_relative(import_literal.text()))
        {
            return String::new();
        }

        modulespecifiers::update_module_specifier(
            program.options(),
            &modulespecifiers::ProgramHost,
            source_file,
            new_import_from_path,
            import_literal.text(),
            &target.new_file_name,
            user_preferences,
            modulespecifiers::ModuleSpecifierOptions {
                override_import_mode: program.get_mode_for_usage_location(
                    &autoimport::source_file_has_file_name(source_file),
                    import_literal,
                ),
            },
        )
    }
}

// Go: ls/file_rename.go:282 getSourceFileToImport
// PORT: Go returns `*toImport`; nil is `None`.
pub fn get_source_file_to_import(
    program: &'static compiler::NewProgram,
    source_file: Node,
    import_literal: Node,
    old_to_new: &PathUpdater<'_>,
) -> Option<ToImport> {
    if let Some(resolved) = program.get_resolved_module_from_module_specifier(
        &autoimport::source_file_has_file_name(source_file),
        import_literal,
    ) {
        if !resolved.resolved_file_name.is_empty() {
            let old_file_name = resolved.resolved_file_name.clone();
            let (new_file_name, ok) = old_to_new(&old_file_name);
            if ok {
                return Some(ToImport {
                    new_file_name,
                    updated: true,
                });
            }
            return Some(ToImport {
                new_file_name: old_file_name,
                updated: false,
            });
        }
    }

    None
}

// Go: ls/file_rename.go:301 getUpdatedImportSpecifierFromMovedSourceFiles
// As a fall back for unresolved modules, we'll check every file affected by the rename to see if any of them would match
// the import specifier, and if so, we'll obtain the updated specifier for that file.
// PORT: Go passes the program as the `ModuleSpecifierGenerationHost`; here
// that is `modulespecifiers::ProgramHost` (the installed program).
pub fn get_updated_import_specifier_from_moved_source_files(
    program: &'static compiler::NewProgram,
    source_file: Node,
    import_literal: Node,
    moved_files: &[MovedFile],
    importing_source_file_name: &str,
    user_preferences: &modulespecifiers::UserPreferences,
) -> String {
    let resolution_mode = program.get_mode_for_usage_location(
        &autoimport::source_file_has_file_name(source_file),
        import_literal,
    );
    for candidate in moved_files {
        let old_specifier = modulespecifiers::update_module_specifier(
            program.options(),
            &modulespecifiers::ProgramHost,
            source_file,
            importing_source_file_name,
            import_literal.text(),
            source_file_file_name(candidate.source_file),
            user_preferences,
            modulespecifiers::ModuleSpecifierOptions {
                override_import_mode: resolution_mode,
            },
        );
        if old_specifier != import_literal.text() {
            continue;
        }

        return modulespecifiers::update_module_specifier(
            program.options(),
            &modulespecifiers::ProgramHost,
            source_file,
            importing_source_file_name,
            import_literal.text(),
            &candidate.new_file_name,
            user_preferences,
            modulespecifiers::ModuleSpecifierOptions {
                override_import_mode: resolution_mode,
            },
        );
    }
    String::new()
}

// Go: ls/file_rename.go:341 createStringTextRange
pub fn create_string_text_range(source_file: Node, node: Node) -> TextRange {
    TextRange::new(
        get_token_pos_of_node(node, source_file, false) + 1,
        node.end() - 1,
    )
}

// Go: ls/file_rename.go:345 getTsConfigObjectLiteralExpression
// PORT: Go returns `*ast.ObjectLiteralExpression`; nil is `Node::NIL`.
pub fn get_ts_config_object_literal_expression(ts_config_source_file: Node) -> Node {
    if ts_config_source_file.is_some()
        && ts_config_source_file.statement_list().is_some()
        && !ts_config_source_file.statements().is_empty()
    {
        let expression = ts_config_source_file.statements().get(0).expression();
        if is_object_literal_expression(expression) {
            return expression;
        }
    }
    Node::NIL
}

// Go: ls/file_rename.go:355 forEachObjectProperty
// PORT: Go `cb func(property *ast.PropertyAssignment, propertyName string)`.
pub fn for_each_object_property(object_literal: Node, cb: &mut dyn FnMut(Node, &str)) {
    if object_literal.is_nil() {
        return;
    }
    for property in object_literal.properties().iter() {
        if !is_property_assignment(property) {
            continue;
        }
        let (name, ok) = try_get_text_of_property_name(property.name());
        if ok {
            cb(property, &name);
        }
    }
}

// Go: ls/file_rename.go:369 relativePathFromDirectory
pub fn relative_path_from_directory(
    from_directory: &str,
    to: &str,
    use_case_sensitive_file_names: bool,
) -> String {
    tspath::get_relative_path_from_directory(
        from_directory,
        to,
        &tspath::ComparePathsOptions {
            use_case_sensitive_file_names,
            ..Default::default()
        },
    )
}

// Go: ls/file_rename.go:373 relativeImportPathFromDirectory
pub fn relative_import_path_from_directory(
    from_directory: &str,
    to: &str,
    use_case_sensitive_file_names: bool,
) -> String {
    tspath::ensure_path_is_non_module_name(&relative_path_from_directory(
        from_directory,
        to,
        use_case_sensitive_file_names,
    ))
}

// Go: ls/file_rename.go:377 isAmbientModuleSymbol
// PORT: Go reads `symbol.Declarations` without a checker; the symbol arena
// is the first parameter, as for ast helpers that take a symbol.
pub fn is_ambient_module_symbol(symbols: &SymbolArena, symbol: SymbolId) -> bool {
    if symbol.is_nil() {
        return false;
    }
    symbols
        .sym(symbol)
        .declarations
        .iter()
        .any(|&declaration| is_module_with_string_literal_name(declaration))
}
