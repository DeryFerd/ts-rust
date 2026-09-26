use crate::ls::prelude::*;

// Port of Go `ls/completions.go` lines 1709-3498: completion entry building,
// keyword lists and the context helpers.
//
// PORT (whole file):
// - Go text scanning (`utf8.DecodeRuneInString`, `utf8.DecodeLastRuneInString`,
//   `unicode.IsSpace`, `unicode.IsDigit`) runs on byte offsets with the
//   scanner's rune decoders. A Go `rune` is an `i32`.
// - Go `*ast.Symbol` reads without a checker take the symbol arena as the
//   first parameter (`symbols: &SymbolArena`), as the ast helpers do.
// - Go `*checker.Type` is `TypeId`; its methods read the checker arena
//   (`type_checker.ty(t)`).
// - Go `*symbolOriginInfo` parameters are `Option<&SymbolOriginInfo>`.
// - Go `collections.Set[string]` results are `FxHashSet<String>`.

use crate::astnav;
use crate::frontend::json_ext;
use crate::frontend::scanner::scanner_p1::{
    RUNE_ERROR, utf8_decode_last_rune_in_string, utf8_decode_rune_in_string,
};
use crate::frontend::stringutil_ls;
use crate::gostd::{Context, GoError};
use crate::ls::lsutil;
use crate::lsp::lsproto;

// Go: ls/completions.go:1709 keywordCompletionData
pub fn keyword_completion_data(
    keyword_filters: KeywordCompletionFilters,
    filter_out_ts_only_keywords: bool,
    is_new_identifier_location: bool,
) -> CompletionDataKeyword {
    CompletionDataKeyword {
        keyword_completions: get_keyword_completions(keyword_filters, filter_out_ts_only_keywords),
        is_new_identifier_location,
    }
}

// Go: ls/completions.go:1720 getDefaultCommitCharacters
pub fn get_default_commit_characters(is_new_identifier_location: bool) -> Vec<String> {
    if is_new_identifier_location {
        return Vec::new();
    }
    ALL_COMMIT_CHARACTERS
        .iter()
        .map(|s| (*s).to_string())
        .collect()
}

impl LanguageService {
    // Go: ls/completions.go:1727 completionInfoFromData
    // PORT: Go mutates `data.symbols` through the pointer, so `data` is
    // `&mut`.
    pub fn completion_info_from_data(
        &self,
        ctx: &Context,
        type_checker: &mut Checker,
        file: Node,
        compiler_options: &CompilerOptions,
        data: &mut CompletionDataData,
        position: i32,
        optional_replacement_span: Option<lsproto::Range>,
        include_symbols: bool,
    ) -> Result<Option<CompletionList>, GoError> {
        let keyword_filters = data.keyword_filters;
        let is_new_identifier_location = data.is_new_identifier_location;
        let context_token = data.context_token;
        let mut literals = data.literals.clone();
        let preferences = self.user_preferences();

        // Verify if the file is JSX language variant
        if source_file_info(file).language_variant == LanguageVariant::JSX {
            let list = self.get_jsx_closing_tag_completion(ctx, data.location, file, position);
            if list.is_some() {
                return Ok(list);
            }
        }

        // When the completion is for the expression of a case clause (e.g. `case |`),
        // filter literals & enum symbols whose values are already present in existing case clauses.
        let case_clause = find_ancestor(context_token, is_case_clause);
        if case_clause.is_some()
            && (context_token.kind() == SyntaxKind::CaseKeyword
                || is_node_descendant_of(context_token, case_clause.expression()))
        {
            let clauses = case_clause.parent().clauses().nodes().to_vec();
            let tracker = new_case_clause_tracker(type_checker, &clauses);
            literals = literals
                .into_iter()
                .filter(|literal| !tracker.has_value(literal))
                .collect();
            data.symbols = data
                .symbols
                .iter()
                .copied()
                .filter(|&symbol| {
                    let value_declaration = type_checker.sym(symbol).value_declaration;
                    if value_declaration.is_some() && is_enum_member(value_declaration) {
                        let value = type_checker.get_constant_value(value_declaration);
                        if let Some(value) = value {
                            if tracker.has_value(&value) {
                                return false;
                            }
                        }
                    }
                    true
                })
                .collect();
        }

        let is_checked = is_checked_file(file, compiler_options);
        if is_checked
            && !is_new_identifier_location
            && data.symbols.is_empty()
            && keyword_filters == KeywordCompletionFilters::NONE
        {
            return Ok(None);
        }

        let (mut unique_names, mut sorted_entries) = self.get_completion_entries_from_symbols(
            ctx,
            type_checker,
            data,
            Node::NIL, /*replacementToken*/
            position,
            file,
            compiler_options,
            include_symbols,
        );

        if data.keyword_filters != KeywordCompletionFilters::NONE {
            let keyword_completions = get_keyword_completions(
                data.keyword_filters,
                !data.inside_js_doc_tag_type_expression && is_source_file_js(file),
            );
            for keyword_entry in keyword_completions {
                let label = keyword_entry.completion_item.label.clone();
                if data.is_type_only_location && is_type_keyword(string_to_token(&label))
                    || !data.is_type_only_location
                        && is_contextual_keyword_in_auto_importable_expression_space(&label)
                    || !unique_names.contains(&label)
                {
                    unique_names.insert(label);
                    sorted_entries.push(keyword_entry);
                }
            }
        }

        for keyword_entry in get_contextual_keywords(file, context_token, position) {
            if !unique_names.contains(&keyword_entry.label) {
                unique_names.insert(keyword_entry.label.clone());
                sorted_entries.push(CompletionItem {
                    completion_item: keyword_entry,
                    symbol: SymbolId::NIL,
                });
            }
        }

        for literal in &literals {
            let literal_entry = create_completion_item_for_literal(file, &preferences, literal);
            unique_names.insert(literal_entry.label.clone());
            sorted_entries.push(CompletionItem {
                completion_item: literal_entry,
                symbol: SymbolId::NIL,
            });
        }

        if !is_checked {
            sorted_entries = self.get_js_completion_entries(
                ctx,
                file,
                position,
                &mut unique_names,
                sorted_entries,
            );
        }

        if context_token.is_some()
            && !data.is_right_of_open_tag
            && !data.is_right_of_dot_or_question_dot
        {
            let case_block = find_ancestor_kind(context_token, SyntaxKind::CaseBlock);
            if case_block.is_some() {
                let cases_item = self.get_exhaustive_case_snippets(
                    ctx,
                    case_block,
                    file,
                    position,
                    compiler_options,
                    self.program,
                    type_checker,
                )?;
                if let Some(cases_item) = cases_item {
                    sorted_entries.push(CompletionItem {
                        completion_item: cases_item,
                        symbol: SymbolId::NIL,
                    });
                }
            }
        }

        // PORT: Go passes `&data.defaultCommitCharacters`, a non-nil pointer
        // to the field. The field is set at completions.go:1678 and is never
        // nil here; a nil slice would marshal as `[]` (json v2), the same as
        // the empty Vec.
        let default_commit_characters = data.default_commit_characters.clone().unwrap_or_default();
        let item_defaults = self.set_item_defaults(
            ctx,
            position,
            file,
            &mut sorted_entries,
            Some(&default_commit_characters),
            optional_replacement_span,
        );

        Ok(Some(CompletionList {
            is_incomplete: data.has_unresolved_auto_imports,
            item_defaults,
            apply_kind: None,
            items: sorted_entries,
        }))
    }

    // Go: ls/completions.go:1859 getCompletionEntriesFromSymbols
    pub fn get_completion_entries_from_symbols(
        &self,
        ctx: &Context,
        type_checker: &mut Checker,
        data: &CompletionDataData,
        replacement_token: Node,
        position: i32,
        file: Node,
        compiler_options: &CompilerOptions,
        include_symbols: bool,
    ) -> (FxHashSet<String>, Vec<CompletionItem>) {
        let closest_symbol_declaration =
            get_closest_symbol_declaration(data.context_token, data.location);
        let use_semicolons = lsutil::probably_uses_semicolons(file);
        let is_member_completion = is_member_completion_kind(data.completion_kind);
        let mut sorted_entries: Vec<CompletionItem> =
            Vec::with_capacity(data.symbols.len() + data.auto_imports.len());
        // Tracks unique names.
        // Value is set to false for global variables or completions from external module exports, because we can have multiple of those;
        // true otherwise. Based on the order we add things we will always see locals first, then globals, then module exports.
        // So adding a completion for a local will prevent us from adding completions for external module exports sharing the same name.
        // PORT: Go map; only membership and the final key set are read.
        let mut uniques: UniqueNamesMap = FxHashMap::default();
        for (index, &symbol) in data.symbols.iter().enumerate() {
            let origin = data.symbol_to_origin_info_map.get(&(index as i32));
            let (name, needs_convert_property_access) =
                get_completion_entry_display_name_for_symbol(
                    &type_checker.symbols,
                    symbol,
                    origin,
                    data.completion_kind,
                    data.is_jsx_identifier_expected,
                );
            if name.is_empty()
                || uniques.get(&name).copied().unwrap_or(false)
                    && (origin.is_none() || !origin_is_object_literal_method(origin))
                || data.completion_kind == CompletionKind::GLOBAL
                    && !should_include_symbol(
                        symbol,
                        data,
                        closest_symbol_declaration,
                        file,
                        type_checker,
                        compiler_options,
                    )
            {
                continue;
            }

            // When in a value location in a JS file, ignore symbols that definitely seem to be type-only.
            if !data.is_type_only_location
                && is_source_file_js(file)
                && symbol_appears_to_be_type_only(symbol, type_checker)
            {
                continue;
            }

            let mut original_sort_text: SortText = data
                .symbol_to_sort_text_map
                .get(&get_symbol_id(&type_checker.symbols, symbol))
                .cloned()
                .unwrap_or_default();
            if original_sort_text.is_empty() {
                original_sort_text = SORT_TEXT_LOCATION_PRIORITY.to_string();
            }

            let sort_text: SortText = if is_deprecated(symbol, type_checker) {
                deprecate_sort_text(&original_sort_text)
            } else {
                original_sort_text
            };
            let entry = self.create_completion_item(
                ctx,
                type_checker,
                symbol,
                &sort_text,
                replacement_token,
                data,
                position,
                file,
                &name,
                needs_convert_property_access,
                origin,
                use_semicolons,
                compiler_options,
                is_member_completion,
            );
            let Some(entry) = entry else {
                continue;
            };

            // True for locals; false for globals, module exports from other files, `this.` completions.
            let should_shadow_later_symbols = (origin.is_none()
                || origin_is_type_only_alias(origin))
                && !(type_checker.sym(symbol).parent.is_nil()
                    && !type_checker
                        .sym(symbol)
                        .declarations
                        .iter()
                        .any(|&d| get_source_file_of_node(d) == file));
            uniques.insert(name, should_shadow_later_symbols);
            let sym = if include_symbols {
                symbol
            } else {
                SymbolId::NIL
            };
            sorted_entries.push(CompletionItem {
                completion_item: entry,
                symbol: sym,
            });
        }

        for auto_import in &data.auto_imports {
            // !!! check for type-only in JS
            // !!! deprecation

            if data.import_statement_completion.is_some() {
                // !!!
                continue;
            }

            // Non-contextual keywords (e.g., `function`, `class`, `const`) cannot be used as identifiers,
            // so auto-imports with these names should not shadow keyword completions.
            let token = string_to_token(&auto_import.fix.name);
            if token != SyntaxKind::Unknown && crate::ast::is_non_contextual_keyword(token) {
                continue;
            }

            if !auto_import.export.is_unresolved_alias() {
                if data.is_type_only_location {
                    if !auto_import.export.flags.intersects(SymbolFlags::TYPE)
                        && !auto_import.export.flags.intersects(SymbolFlags::MODULE)
                    {
                        continue;
                    }
                } else if !auto_import.export.flags.intersects(SymbolFlags::VALUE) {
                    continue;
                }
            }

            let entry = self.create_lsp_completion_item(
                ctx,
                &auto_import.fix.name,
                "",
                "",
                SORT_TEXT_AUTO_IMPORT_SUGGESTIONS,
                auto_import.export.script_element_kind,
                auto_import.export.script_element_kind_modifiers,
                None,
                None,
                Some(lsproto::CompletionItemLabelDetails {
                    description: Some(auto_import.fix.module_specifier.clone()),
                    ..Default::default()
                }),
                file,
                position,
                false, /*isMemberCompletion*/
                false, /*isSnippet*/
                true,  /*hasAction*/
                false, /*preselect*/
                &auto_import.fix.module_specifier,
                Some(auto_import.fix.auto_import_fix.clone()),
                None, /*detail*/
            );

            let is_shadowed = uniques.get(&auto_import.fix.name).copied().unwrap_or(false);
            if !is_shadowed {
                uniques.insert(auto_import.fix.name.clone(), false);
                sorted_entries.push(CompletionItem {
                    completion_item: entry,
                    symbol: SymbolId::NIL,
                });
            }
        }

        let mut unique_set: FxHashSet<String> =
            FxHashSet::with_capacity_and_hasher(uniques.len(), Default::default());
        for name in uniques.keys() {
            unique_set.insert(name.clone());
        }
        (unique_set, sorted_entries)
    }
}

// Go: ls/completions.go:2003 completionNameForLiteral
pub fn completion_name_for_literal(
    file: Node,
    preferences: &lsutil::UserPreferences,
    literal: &LiteralValue,
) -> String {
    match literal {
        LiteralValue::String(literal) => quote(file, preferences, literal),
        LiteralValue::Number(literal) => {
            // Go: `core.StringifyJson(literal, "", "")`; the error is ignored
            // (an error gives "").
            json_ext::marshal_indent(&literal.0, "" /*prefix*/, "" /*suffix*/).unwrap_or_default()
        }
        LiteralValue::PseudoBigInt(literal) => format!("{literal}n"),
        LiteralValue::Bool(_) => panic!("Unhandled literal value: {literal:?}"),
    }
}

// Go: ls/completions.go:2020 createCompletionItemForLiteral
pub fn create_completion_item_for_literal(
    file: Node,
    preferences: &lsutil::UserPreferences,
    literal: &LiteralValue,
) -> lsproto::CompletionItem {
    lsproto::CompletionItem {
        label: completion_name_for_literal(file, preferences, literal),
        kind: Some(lsproto::CompletionItemKind::CONSTANT),
        sort_text: Some(SORT_TEXT_LOCATION_PRIORITY.to_string()),
        commit_characters: Some(Vec::new()),
        ..Default::default()
    }
}

impl LanguageService {
    // Go: ls/completions.go:2033 createCompletionItem
    // PORT: Go returns a nil `*lsproto.CompletionItem` when there is no dot
    // to convert; that is `None`. Go reassigns the `sortText` and `name`
    // parameters, so they are copied into locals.
    pub fn create_completion_item(
        &self,
        ctx: &Context,
        type_checker: &mut Checker,
        symbol: SymbolId,
        sort_text: &str,
        replacement_token: Node,
        data: &CompletionDataData,
        position: i32,
        file: Node,
        name: &str,
        needs_convert_property_access: bool,
        origin: Option<&SymbolOriginInfo>,
        use_semicolons: bool,
        compiler_options: &CompilerOptions,
        is_member_completion: bool,
    ) -> Option<lsproto::CompletionItem> {
        let mut sort_text: SortText = sort_text.to_string();
        let mut name: String = name.to_string();
        let context_token = data.context_token;
        let mut insert_text = String::new();
        let filter_text = String::new();
        let mut replacement_span =
            self.get_replacement_range_for_context_token(file, replacement_token, position);
        let mut is_snippet = false;
        let mut has_action = false;
        let mut source = get_source_from_origin(origin);
        let mut label_details: Option<lsproto::CompletionItemLabelDetails> = None;
        let preferences = self.user_preferences();
        let insert_question_dot = origin_is_nullable_member(origin);
        let use_braces = origin_is_symbol_member(origin) || needs_convert_property_access;
        if origin_is_this_type_node(origin) {
            if needs_convert_property_access {
                insert_text = format!(
                    "this{}[{}]",
                    if insert_question_dot { "?." } else { "" },
                    quote_property_name(file, &preferences, &name),
                );
            } else {
                insert_text = format!(
                    "this{}{}",
                    if insert_question_dot { "?." } else { "." },
                    name,
                );
            }
        } else if data.property_access_to_convert.is_some() && (use_braces || insert_question_dot) {
            // We should only have needsConvertPropertyAccess if there's a property access to convert. But see microsoft/TypeScript#21790.
            // Somehow there was a global with a non-identifier name. Hopefully someone will complain about getting a "foo bar" global completion and provide a repro.
            if use_braces {
                if needs_convert_property_access {
                    insert_text = format!("[{}]", quote_property_name(file, &preferences, &name));
                } else {
                    insert_text = format!("[{name}]");
                }
            } else {
                insert_text = name.clone();
            }

            if insert_question_dot
                || data
                    .property_access_to_convert
                    .question_dot_token()
                    .is_some()
            {
                insert_text = format!("?.{insert_text}");
            }

            let mut dot = astnav::find_child_of_kind(
                data.property_access_to_convert,
                SyntaxKind::DotToken,
                file,
            );
            if dot.is_nil() {
                dot = astnav::find_child_of_kind(
                    data.property_access_to_convert,
                    SyntaxKind::QuestionDotToken,
                    file,
                );
            }

            if dot.is_nil() {
                return None;
            }

            // If the text after the '.' starts with this name, write over it. Else, add new text.
            let end = if name.starts_with(data.property_access_to_convert.name().text()) {
                data.property_access_to_convert.end()
            } else {
                dot.end()
            };
            replacement_span = Some(self.create_lsp_range_from_bounds(
                astnav::get_start_of_node(dot, file, false /*includeJSDoc*/),
                end,
                file,
            ));
        }

        if data.jsx_initializer.is_initializer {
            if insert_text.is_empty() {
                insert_text = name.clone();
            }
            insert_text = format!("{{{insert_text}}}");
            if data.jsx_initializer.initializer.is_some() {
                replacement_span =
                    Some(self.create_lsp_range_from_node(data.jsx_initializer.initializer, file));
            }
        }

        if origin_is_promise(origin) && data.property_access_to_convert.is_some() {
            if insert_text.is_empty() {
                insert_text = name.clone();
            }
            let preceding_token =
                astnav::find_preceding_token(file, data.property_access_to_convert.pos());
            let mut await_text = String::new();
            if preceding_token.is_some()
                && lsutil::position_is_asi_candidate(
                    preceding_token.end(),
                    preceding_token.parent(),
                    file,
                )
            {
                await_text = ";".to_string();
            }

            await_text += &format!(
                "(await {})",
                get_text_of_node(data.property_access_to_convert.expression())
            );
            if needs_convert_property_access {
                insert_text = await_text + &insert_text;
            } else {
                let dot_str = if insert_question_dot { "?." } else { "." };
                insert_text = await_text + dot_str + &insert_text;
            }
            let is_in_await_expression =
                is_await_expression(data.property_access_to_convert.parent());
            let wrap_node = if is_in_await_expression {
                data.property_access_to_convert.parent()
            } else {
                data.property_access_to_convert.expression()
            };
            replacement_span = Some(self.create_lsp_range_from_bounds(
                astnav::get_start_of_node(wrap_node, file, false /*includeJSDoc*/),
                data.property_access_to_convert.end(),
                file,
            ));
        }

        if origin_is_type_only_alias(origin) {
            has_action = true;
        }

        // Provide object member completions when missing commas, and insert missing commas.
        // For example:
        //
        //    interface I {
        //        a: string;
        //        b: number
        //     }
        //
        //     const cc: I = { a: "red" | }
        //
        // Completion should add a comma after "red" and provide completions for b
        if data.completion_kind == CompletionKind::OBJECT_PROPERTY_DECLARATION
            && context_token.is_some()
            && !node_has_kind(
                astnav::find_preceding_token_ex(
                    file,
                    context_token.pos(),
                    context_token,
                    false, /*excludeJSDoc*/
                ),
                SyntaxKind::CommaToken,
            )
        {
            if is_method_declaration(context_token.parent().parent())
                || is_get_accessor_declaration(context_token.parent().parent())
                || is_set_accessor_declaration(context_token.parent().parent())
                || is_spread_assignment(context_token.parent())
                || lsutil::get_last_token(
                    find_ancestor(context_token.parent(), is_property_assignment),
                    file,
                ) == context_token
                || is_shorthand_property_assignment(context_token.parent())
                    && get_line_of_position(file, context_token.end())
                        != get_line_of_position(file, position)
            {
                source = COMPLETION_SOURCE_OBJECT_LITERAL_MEMBER_WITH_COMMA.to_string();
                has_action = true;
            }
        }

        if preferences
            .include_completions_with_class_member_snippets
            .is_true()
            && data.completion_kind == CompletionKind::MEMBER_LIKE
            && is_class_like_member_completion(symbol, data.location, file)
        {
            // !!! class member completions
        }

        if origin_is_object_literal_method(origin) {
            let origin = origin.unwrap();
            insert_text = origin.as_object_literal_method().insert_text.clone();
            is_snippet = origin.as_object_literal_method().is_snippet;
            label_details = origin.as_object_literal_method().label_details.clone(); // !!! check if this can conflict with case above where we set label details
            if !client_supports_item_label_details(ctx) {
                // PORT: Go dereferences `labelDetails.Detail`; a nil pointer
                // panics there, as the unwraps do here.
                name = name
                    + origin
                        .as_object_literal_method()
                        .label_details
                        .as_ref()
                        .unwrap()
                        .detail
                        .as_ref()
                        .unwrap();
                label_details = None;
            }
            source = COMPLETION_SOURCE_OBJECT_LITERAL_METHOD_SNIPPET.to_string();
            sort_text = sort_below(&sort_text);
        }

        if data.is_jsx_identifier_expected
            && !data.is_right_of_open_tag
            && client_supports_item_snippet(ctx)
            && preferences.jsx_attribute_completion_style
                != lsutil::JsxAttributeCompletionStyle::NONE
            && !(data.location.parent().is_some()
                && is_jsx_attribute(data.location.parent())
                && data.location.parent().initializer().is_some())
        {
            let mut use_braces = preferences.jsx_attribute_completion_style
                == lsutil::JsxAttributeCompletionStyle::BRACES;
            let t = type_checker.get_type_of_symbol_at_location(symbol, data.location);

            // If is boolean like or undefined, don't return a snippet, we want to return just the completion.
            if preferences.jsx_attribute_completion_style
                == lsutil::JsxAttributeCompletionStyle::AUTO
                && !type_checker.ty(t).is_boolean_like()
                && !(type_checker.ty(t).is_union()
                    && type_checker
                        .ty(t)
                        .types()
                        .iter()
                        .any(|&t| type_checker.ty(t).is_boolean_like()))
            {
                if type_checker.ty(t).is_string_like()
                    || type_checker.ty(t).is_union() && {
                        let types = type_checker.ty(t).types().to_vec();
                        types.iter().all(|&t| {
                            type_checker
                                .ty(t)
                                .flags
                                .intersects(TypeFlags::STRING_LIKE | TypeFlags::UNDEFINED)
                                || is_string_and_empty_anonymous_object_intersection(
                                    type_checker,
                                    t,
                                )
                        })
                    }
                {
                    // If type is string-like or undefined, use quotes.
                    insert_text = format!(
                        "{}={}",
                        escape_snippet_text(&name),
                        quote(file, &preferences, "$1")
                    );
                    is_snippet = true;
                } else {
                    // Use braces for everything else.
                    use_braces = true;
                }
            }

            if use_braces {
                insert_text = escape_snippet_text(&name) + "={$1}";
                is_snippet = true;
            }
        }

        let parent_named_import_or_export =
            find_ancestor(data.location, is_named_imports_or_exports);
        if parent_named_import_or_export.is_some() {
            if !is_identifier_text(&name, LanguageVariant::STANDARD) {
                insert_text = quote_property_name(file, &preferences, &name);

                if parent_named_import_or_export.kind() == SyntaxKind::NamedImports {
                    // Check if it is `import { ^here as name } from '...'``.
                    // We have to access the scanner here to check if it is `{ ^here as name }`` or `{ ^here, as, name }`.
                    let mut scanner = crate::frontend::scanner::new_scanner();
                    scanner.set_text(source_file_text(file));
                    scanner.reset_pos(position);
                    if !(scanner.scan() == SyntaxKind::AsKeyword
                        && scanner.scan() == SyntaxKind::Identifier)
                    {
                        insert_text +=
                            &format!(" as {}", generate_identifier_for_arbitrary_string(&name));
                    }
                }
            } else if parent_named_import_or_export.kind() == SyntaxKind::NamedImports {
                let possible_token = string_to_token(&name);
                if possible_token != SyntaxKind::Unknown
                    && (possible_token == SyntaxKind::AwaitKeyword
                        || lsutil::is_non_contextual_keyword(possible_token))
                {
                    insert_text = format!("{name} as {name}_");
                }
            }
        }

        // Commit characters

        let element_kind = lsutil::get_symbol_kind(Some(&mut *type_checker), symbol, data.location);
        let mut commit_characters: Option<Vec<String>> = None;
        if client_supports_item_commit_characters(ctx) {
            if element_kind == lsutil::ScriptElementKind::WARNING
                || element_kind == lsutil::ScriptElementKind::STRING
            {
                commit_characters = Some(Vec::new());
            } else if !client_supports_default_commit_characters(ctx) {
                // PORT: Go `new(data.defaultCommitCharacters)` is a non-nil
                // pointer; a nil slice marshals as `[]` (json v2).
                commit_characters =
                    Some(data.default_commit_characters.clone().unwrap_or_default());
            }
            // Otherwise use the completion list default.
        }

        let preselect =
            is_recommended_completion_match(symbol, data.recommended_completion, type_checker);
        let kind_modifiers = lsutil::get_symbol_modifiers(Some(&mut *type_checker), symbol);

        Some(self.create_lsp_completion_item(
            ctx,
            &name,
            &insert_text,
            &filter_text,
            &sort_text,
            element_kind,
            kind_modifiers,
            replacement_span,
            commit_characters,
            label_details,
            file,
            position,
            is_member_completion,
            is_snippet,
            has_action,
            preselect,
            &source,
            None, /*autoImportFix*/
            None, /*detail*/
        ))
    }
}

// Go: ls/completions.go:2296 isRecommendedCompletionMatch
pub fn is_recommended_completion_match(
    local_symbol: SymbolId,
    recommended_completion: SymbolId,
    type_checker: &mut Checker,
) -> bool {
    local_symbol == recommended_completion
        || type_checker
            .sym(local_symbol)
            .flags
            .intersects(SymbolFlags::EXPORT_VALUE)
            && type_checker.get_export_symbol_of_symbol(local_symbol) == recommended_completion
}

// Go: ls/completions.go:2302 wordSeparators
// Ported from vscode.
// PORT: Go `collections.Set[rune]`; a rune is an `i32`.
pub static WORD_SEPARATORS: [i32; 29] = [
    '`' as i32,
    '~' as i32,
    '!' as i32,
    '@' as i32,
    '%' as i32,
    '^' as i32,
    '&' as i32,
    '*' as i32,
    '(' as i32,
    ')' as i32,
    '-' as i32,
    '=' as i32,
    '+' as i32,
    '[' as i32,
    '{' as i32,
    ']' as i32,
    '}' as i32,
    '\\' as i32,
    '|' as i32,
    ';' as i32,
    ':' as i32,
    '\'' as i32,
    '"' as i32,
    ',' as i32,
    '.' as i32,
    '<' as i32,
    '>' as i32,
    '/' as i32,
    '?' as i32,
];

// Go: ls/completions.go:2309 getWordLengthAndStart
// Finds the length and first rune of the word that ends at the given position.
// e.g. for "abc def.ghi|jkl", the word length is 3 and the word start is 'g'.
// PORT: Go cuts `text := sourceFile.Text()[:position]`. The decoders read the
// whole text and stop at `position`, so no `&str` is cut inside a character.
pub fn get_word_length_and_start(source_file: Node, position: i32) -> (i32, i32) {
    // !!! Port other case of vscode's `DEFAULT_WORD_REGEXP` that covers words that start like numbers, e.g. -123.456abcd.
    let text = source_file_text(source_file);
    let text_len = position as usize;
    let mut total_size: i32 = 0;
    let mut first_rune: i32 = 0;
    let (mut r, mut size) = utf8_decode_last_rune_in_string(text, text_len);
    while size != 0 {
        if WORD_SEPARATORS.contains(&r) || unicode_is_space(r) {
            break;
        }
        total_size += size;
        first_rune = r;
        (r, size) = utf8_decode_last_rune_in_string(text, text_len - total_size as usize);
    }
    // If word starts with `@`, disregard this first character.
    if first_rune == '@' as i32 {
        total_size -= 1;
        (first_rune, _) = decode_rune_in_range(text, text_len - total_size as usize, text_len);
    }
    (total_size, first_rune)
}

// Go: ls/completions.go:2332 trimElementAccess
// `["ab c"]` -> `ab c`
// `['ab c']` -> `ab c`
// `[123]` -> `123`
pub fn trim_element_access(text: &str) -> String {
    let mut text = text.strip_prefix('[').unwrap_or(text);
    text = text.strip_suffix(']').unwrap_or(text);
    if text.starts_with('\'') && text.ends_with('\'') {
        let trimmed = text.strip_suffix('\'').unwrap_or(text);
        text = trimmed.strip_prefix('\'').unwrap_or(trimmed);
    }
    if text.starts_with('"') && text.ends_with('"') {
        let trimmed = text.strip_suffix('"').unwrap_or(text);
        text = trimmed.strip_prefix('"').unwrap_or(trimmed);
    }
    text.to_string()
}

// Go: ls/completions.go:2345 getFilterText
// Ported from vscode ts extension: `getFilterText`.
pub fn get_filter_text(
    file: Node,
    position: i32,
    insert_text: &str,
    label: &str,
    word_start: i32,
    dot_accessor: &str,
) -> String {
    // Private field completion, e.g. label `#bar`.
    if let Some(after) = label.strip_prefix('#') {
        if !insert_text.is_empty() {
            if let Some(after) = insert_text.strip_prefix("this.#") {
                if word_start == '#' as i32 {
                    // `method() { this.#| }`
                    // `method() { #| }`
                    return String::new();
                } else {
                    // `method() { this.| }`
                    // `method() { | }`
                    return after.to_string();
                }
            }
        } else if word_start == '#' as i32 {
            // `method() { this.#| }`
            return String::new();
        } else {
            // `method() { this.| }`
            // `method() { | }`
            return after.to_string();
        }
    }

    // For `this.` completions, generally don't set the filter text since we don't want them to be overly deprioritized. microsoft/vscode#74164
    if insert_text.starts_with("this.") {
        return String::new();
    }

    // Handle the case:
    // ```
    // const xyz = { 'ab c': 1 };
    // xyz.ab|
    // ```
    // In which case we want to insert a bracket accessor but should use `.abc` as the filter text instead of
    // the bracketed insert text.
    if insert_text.starts_with('[') {
        return dot_accessor.to_string() + &trim_element_access(insert_text);
    }

    if insert_text.starts_with("?.") {
        // Handle this case like the case above:
        // ```
        // const xyz = { 'ab c': 1 } | undefined;
        // xyz.ab|
        // ```
        // filterText should be `.ab c` instead of `?.['ab c']`.
        if insert_text.starts_with("?.[") {
            return dot_accessor.to_string() + &trim_element_access(&insert_text[2..]);
        } else {
            // ```
            // const xyz = { abc: 1 } | undefined;
            // xyz.ab|
            // ```
            // filterText should be `.abc` instead of `?.abc.
            return dot_accessor.to_string() + &insert_text[2..];
        }
    }

    // In all other cases, fall back to using the insertText.
    insert_text.to_string()
}

// Go: ls/completions.go:2419 getDotAccessor
// Ported from vscode's `provideCompletionItems`.
pub fn get_dot_accessor(file: Node, position: i32) -> String {
    let full_text = source_file_text(file);
    let text = &full_text.as_bytes()[..position as usize];
    let mut total_size: i32 = 0;
    if text.ends_with(b"?.") {
        total_size += 2;
        return full_text[(position - total_size) as usize..position as usize].to_string();
    }
    if text.ends_with(b".") {
        total_size += 1;
        return full_text[(position - total_size) as usize..position as usize].to_string();
    }
    String::new()
}

// Go: ls/completions.go:2433 strPtrIsEmpty
pub fn str_ptr_is_empty(ptr: Option<String>) -> bool {
    match ptr {
        None => true,
        Some(ptr) => ptr.is_empty(),
    }
}

// Go: ls/completions.go:2440 strPtrTo
pub fn str_ptr_to(v: &str) -> Option<String> {
    if v.is_empty() {
        return None;
    }
    Some(v.to_string())
}

// Go: ls/completions.go:2447 boolToPtr
pub fn bool_to_ptr(v: bool) -> Option<bool> {
    if v {
        return Some(true);
    }
    None
}

// Go: ls/completions.go:2454 getLineOfPosition
pub fn get_line_of_position(file: Node, pos: i32) -> i32 {
    get_ecma_line_of_position(file, pos)
}

// Go: ls/completions.go:2459 getLineEndOfPosition
pub fn get_line_end_of_position(file: Node, pos: i32) -> i32 {
    let line = get_line_of_position(file, pos);
    let line_starts = get_ecma_line_starts(file);
    let last_char_pos: i32 = if (line + 1) as usize >= line_starts.len() {
        file.end()
    } else {
        line_starts[(line + 1) as usize] - 1
    };
    let full_text = source_file_text(file).as_bytes();
    if last_char_pos > 0
        && (last_char_pos as usize) < full_text.len()
        && full_text[last_char_pos as usize] == b'\n'
        && full_text[last_char_pos as usize - 1] == b'\r'
    {
        return last_char_pos - 1;
    }
    last_char_pos
}

// Go: ls/completions.go:2475 isClassLikeMemberCompletion
pub fn is_class_like_member_completion(symbol: SymbolId, location: Node, file: Node) -> bool {
    // !!! class member completions
    false
}

// Go: ls/completions.go:2480 symbolAppearsToBeTypeOnly
pub fn symbol_appears_to_be_type_only(symbol: SymbolId, type_checker: &mut Checker) -> bool {
    let target = type_checker.skip_alias(symbol);
    let flags = type_checker
        .sym(target)
        .combined_local_and_export_symbol_flags(&type_checker.symbols);
    let declarations = &type_checker.sym(symbol).declarations;
    !flags.intersects(SymbolFlags::VALUE)
        && (declarations.is_empty()
            || !is_in_js_file(declarations[0])
            || flags.intersects(SymbolFlags::TYPE))
}

// Go: ls/completions.go:2486 shouldIncludeSymbol
pub fn should_include_symbol(
    symbol: SymbolId,
    data: &CompletionDataData,
    closest_symbol_declaration: Node,
    file: Node,
    type_checker: &mut Checker,
    compiler_options: &CompilerOptions,
) -> bool {
    let mut all_flags = type_checker.sym(symbol).flags;
    let location = data.location;
    // export = /**/ here we want to get all meanings, so any symbol is ok
    if location.parent().is_some() && is_export_assignment(location.parent()) {
        return true;
    }

    // Filter out variables from their own initializers
    // `const a = /* no 'a' here */`
    let value_declaration = type_checker.sym(symbol).value_declaration;
    if closest_symbol_declaration.is_some()
        && is_variable_declaration(closest_symbol_declaration)
        && value_declaration == closest_symbol_declaration
    {
        return false;
    }

    // Filter out current and latter parameters from defaults
    // `function f(a = /* no 'a' and 'b' here */, b) { }` or
    // `function f<T = /* no 'T' and 'T2' here */>(a: T, b: T2) { }`
    let mut symbol_declaration = Node::NIL;
    if value_declaration.is_some() {
        symbol_declaration = value_declaration;
    } else if !type_checker.sym(symbol).declarations.is_empty() {
        symbol_declaration = type_checker.sym(symbol).declarations[0];
    }

    if closest_symbol_declaration.is_some() && symbol_declaration.is_some() {
        if is_parameter_declaration(closest_symbol_declaration)
            && is_parameter_declaration(symbol_declaration)
        {
            let parameters = closest_symbol_declaration.parent().parameter_list();
            if symbol_declaration.pos() >= closest_symbol_declaration.pos()
                && symbol_declaration.pos() < parameters.end()
            {
                return false;
            }
        } else if is_type_parameter_declaration(closest_symbol_declaration)
            && is_type_parameter_declaration(symbol_declaration)
        {
            if closest_symbol_declaration == symbol_declaration
                && data.context_token.is_some()
                && data.context_token.kind() == SyntaxKind::ExtendsKeyword
            {
                // filter out the directly self-recursive type parameters
                // `type A<K extends /* no 'K' here*/> = K`
                return false;
            }
            if is_in_type_parameter_default(data.context_token)
                && !is_infer_type_node(closest_symbol_declaration.parent())
            {
                let type_parameters = closest_symbol_declaration.parent().type_parameter_list();
                if !type_parameters.is_nil()
                    && symbol_declaration.pos() >= closest_symbol_declaration.pos()
                    && symbol_declaration.pos() < type_parameters.end()
                {
                    return false;
                }
            }
        }
    }

    // External modules can have global export declarations that will be
    // available as global keywords in all scopes. But if the external module
    // already has an explicit export and user only wants to use explicit
    // module imports then the global keywords will be filtered out so auto
    // import suggestions will win in the completion.
    let symbol_origin = type_checker.skip_alias(symbol);
    // We only want to filter out the global keywords.
    // Auto Imports are not available for scripts so this conditional is always false.
    let symbol_parent = type_checker.sym(symbol).parent;
    if source_file_info(file).external_module_indicator.is_some()
        && compiler_options.allow_umd_global_access != Tristate::True
        && symbol != symbol_origin
        && data
            .symbol_to_sort_text_map
            .get(&get_symbol_id(&type_checker.symbols, symbol))
            .map_or("", |s| s.as_str())
            == SORT_TEXT_GLOBALS_OR_KEYWORDS
        && symbol_parent.is_some()
        && type_checker.is_external_module_symbol(symbol_parent)
    {
        return false;
    }

    all_flags = all_flags
        | type_checker
            .sym(symbol_origin)
            .combined_local_and_export_symbol_flags(&type_checker.symbols);
    if type_checker
        .sym(symbol)
        .flags
        .intersects(SymbolFlags::ALIAS)
    {
        all_flags = all_flags | type_checker.get_symbol_flags_exported(symbol);
    }

    // import m = /**/ <-- It can only access namespace (if typing import = x. this would get member symbols and not namespace)
    if is_in_right_side_of_internal_import_equals_declaration(data.location) {
        return all_flags.intersects(SymbolFlags::NAMESPACE);
    }

    if data.is_type_only_location {
        // It's a type, but you can reach it by namespace.type as well.
        return symbol_can_be_referenced_at_type_location(symbol, type_checker, None);
    }

    // expressions are value space (which includes the value namespaces)
    all_flags.intersects(SymbolFlags::VALUE)
}

// Go: ls/completions.go:2578 getCompletionEntryDisplayNameForSymbol
// PORT: `checker.IsKnownSymbol(symbol)` is `isLateBoundName(symbol.Name)`;
// it reads the arena directly (the port has it as a `Checker` method).
pub fn get_completion_entry_display_name_for_symbol(
    symbols: &SymbolArena,
    symbol: SymbolId,
    origin: Option<&SymbolOriginInfo>,
    completion_kind: CompletionKind,
    is_jsx_identifier_expected: bool,
) -> (String, bool) {
    if origin_is_ignore(origin) {
        return (String::new(), false);
    }

    let name: String = if origin_includes_symbol_name(origin) {
        origin.unwrap().symbol_name()
    } else {
        symbol_name(symbols, symbol)
    };
    let flags = symbols.sym(symbol).flags;
    if name.is_empty()
        // If the symbol is external module, don't show it in the completion list
        // (i.e declare module "http" { const x; } | // <= request completion here, "http" should not be there)
        || flags.intersects(SymbolFlags::MODULE) && starts_with_quote(&name)
        // If the symbol is the internal name of an ES symbol, it is not a valid entry. Internal names for ES symbols start with "__@"
        || crate::checker::is_late_bound_name(&symbols.sym(symbol).name)
    {
        return (String::new(), false);
    }

    let variant = if is_jsx_identifier_expected {
        LanguageVariant::JSX
    } else {
        LanguageVariant::STANDARD
    };
    // name is a valid identifier or private identifier text
    let value_declaration = symbols.sym(symbol).value_declaration;
    if is_identifier_text(&name, variant)
        || value_declaration.is_some()
            && is_private_identifier_class_element_declaration(value_declaration)
    {
        return (name, false);
    }
    if flags.intersects(SymbolFlags::ALIAS) {
        // Allow non-identifier import/export aliases since we can insert them as string literals
        return (name, true);
    }

    match completion_kind {
        CompletionKind::MEMBER_LIKE => {
            if origin_is_computed_property_name(origin) {
                return (origin.unwrap().symbol_name(), false);
            }
            (String::new(), false)
        }
        CompletionKind::OBJECT_PROPERTY_DECLARATION => {
            // TODO: microsoft/TypeScript#18169
            // Go: `core.StringifyJson(name, "", "")`; the error is ignored.
            let escaped_name = json_ext::marshal_indent(name.as_str(), "", "").unwrap_or_default();
            (escaped_name, false)
        }
        CompletionKind::PROPERTY_ACCESS | CompletionKind::GLOBAL => {
            // For a 'this.' completion it will be in a global context, but may have a non-identifier name.
            // Don't add a completion for a name starting with a space. See https://github.com/Microsoft/TypeScript/pull/20547
            let (ch, _) = utf8_decode_rune_in_string(&name, 0);
            if ch == ' ' as i32 {
                return (String::new(), false);
            }
            (name, true)
        }
        CompletionKind::NONE | CompletionKind::STRING => (name, false),
        _ => panic!("Unexpected completion kind: {}", completion_kind.0),
    }
}

// !!! refactor symbolOriginInfo so that we can tell the difference between flags and the kind of data it has
// Go: ls/completions.go:2640 originIsIgnore
pub fn origin_is_ignore(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|origin| origin.kind.intersects(SymbolOriginInfoKind::IGNORE))
}

// Go: ls/completions.go:2644 originIncludesSymbolName
pub fn origin_includes_symbol_name(origin: Option<&SymbolOriginInfo>) -> bool {
    origin_is_computed_property_name(origin)
}

// Go: ls/completions.go:2648 originIsComputedPropertyName
pub fn origin_is_computed_property_name(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|origin| {
        origin
            .kind
            .intersects(SymbolOriginInfoKind::COMPUTED_PROPERTY_NAME)
    })
}

// Go: ls/completions.go:2652 originIsObjectLiteralMethod
pub fn origin_is_object_literal_method(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|origin| {
        origin
            .kind
            .intersects(SymbolOriginInfoKind::OBJECT_LITERAL_METHOD)
    })
}

// Go: ls/completions.go:2656 originIsThisTypeNode
pub fn origin_is_this_type_node(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|origin| origin.kind.intersects(SymbolOriginInfoKind::THIS_TYPE))
}

// Go: ls/completions.go:2660 originIsTypeOnlyAlias
pub fn origin_is_type_only_alias(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|origin| {
        origin
            .kind
            .intersects(SymbolOriginInfoKind::TYPE_ONLY_ALIAS)
    })
}

// Go: ls/completions.go:2664 originIsSymbolMember
pub fn origin_is_symbol_member(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|origin| origin.kind.intersects(SymbolOriginInfoKind::SYMBOL_MEMBER))
}

// Go: ls/completions.go:2668 originIsNullableMember
pub fn origin_is_nullable_member(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|origin| origin.kind.intersects(SymbolOriginInfoKind::NULLABLE))
}

// Go: ls/completions.go:2672 originIsPromise
pub fn origin_is_promise(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|origin| origin.kind.intersects(SymbolOriginInfoKind::PROMISE))
}

// Go: ls/completions.go:2676 getSourceFromOrigin
pub fn get_source_from_origin(origin: Option<&SymbolOriginInfo>) -> String {
    if origin_is_this_type_node(origin) {
        return COMPLETION_SOURCE_THIS_PROPERTY.to_string();
    }

    if origin_is_type_only_alias(origin) {
        return COMPLETION_SOURCE_TYPE_ONLY_ALIAS.to_string();
    }

    String::new()
}

// Go: ls/completions.go:2691 getRelevantTokens
// In a scenarion such as `const x = 1 * |`, the context and previous tokens are both `*`.
// In `const x = 1 * o|`, the context token is *, and the previous token is `o`.
// `contextToken` and `previousToken` can both be nil if we are at the beginning of the file.
// PORT: returns `(contextToken, previousToken)`.
pub fn get_relevant_tokens(position: i32, file: Node) -> (Node, Node) {
    let previous_token = astnav::find_preceding_token(file, position);
    if previous_token.is_some()
        && position <= previous_token.end()
        && (is_member_name(previous_token) || is_keyword_kind(previous_token.kind()))
    {
        let context_token = astnav::find_preceding_token(file, previous_token.pos());
        return (context_token, previous_token);
    }
    (previous_token, previous_token)
}

// Go: ls/completions.go:2701 CompletionsTriggerCharacter
// "." | '"' | "'" | "`" | "/" | "@" | "<" | "#" | " "
pub type CompletionsTriggerCharacter = String;

// Go: ls/completions.go:2703 isValidTrigger
// PORT: the `CompletionsTriggerCharacter` (Go string) parameter is `&str`.
pub fn is_valid_trigger(
    file: Node,
    trigger_character: &str,
    context_token: Node,
    position: i32,
) -> bool {
    match trigger_character {
        "." | "@" => true,
        "\"" | "'" | "`" => {
            // Only automatically bring up completions if this is an opening quote.
            context_token.is_some()
                && is_string_literal_or_template(context_token)
                && position
                    == astnav::get_start_of_node(context_token, file, false /*includeJSDoc*/) + 1
        }
        "#" => {
            context_token.is_some()
                && is_private_identifier(context_token)
                && get_containing_class(context_token).is_some()
        }
        "<" => {
            // Opening JSX tag
            context_token.is_some()
                && context_token.kind() == SyntaxKind::LessThanToken
                && (!is_binary_expression(context_token.parent())
                    || binary_expression_may_be_open_tag(context_token.parent()))
        }
        "/" => {
            if context_token.is_nil() {
                return false;
            }
            if is_string_literal_like(context_token) {
                return try_get_import_from_module_specifier(context_token).is_some();
            }
            context_token.kind() == SyntaxKind::LessThanSlashToken
                && is_jsx_closing_element(context_token.parent())
        }
        " " => {
            context_token.is_some()
                && context_token.kind() == SyntaxKind::ImportKeyword
                && context_token.parent().kind() == SyntaxKind::SourceFile
        }
        _ => panic!("Unknown trigger character: {trigger_character}"),
    }
}

// Go: ls/completions.go:2736 isStringLiteralOrTemplate
pub fn is_string_literal_or_template(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::StringLiteral
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::TemplateExpression
            | SyntaxKind::TaggedTemplateExpression
    )
}

// Go: ls/completions.go:2745 binaryExpressionMayBeOpenTag
pub fn binary_expression_may_be_open_tag(binary_expression: Node) -> bool {
    node_is_missing(binary_expression.left())
}

// Go: ls/completions.go:2749 isCheckedFile
pub fn is_checked_file(file: Node, compiler_options: &CompilerOptions) -> bool {
    !is_source_file_js(file) || is_check_js_enabled_for_file(file, compiler_options)
}

// Go: ls/completions.go:2753 isContextTokenValueLocation
pub fn is_context_token_value_location(context_token: Node) -> bool {
    context_token.is_some()
        && ((context_token.kind() == SyntaxKind::TypeOfKeyword
            && (context_token.parent().kind() == SyntaxKind::TypeQuery
                || is_type_of_expression(context_token.parent())))
            || (context_token.kind() == SyntaxKind::AssertsKeyword
                && context_token.parent().kind() == SyntaxKind::TypePredicate))
}

// Go: ls/completions.go:2759 isPossiblyTypeArgumentPosition
pub fn is_possibly_type_argument_position(
    token: Node,
    source_file: Node,
    type_checker: &mut Checker,
) -> bool {
    let info = get_possible_type_arguments_info(token, source_file);
    match info {
        None => false,
        Some(info) => {
            is_part_of_type_node(info.called)
                || !get_possible_generic_signatures(
                    info.called,
                    info.n_type_arguments,
                    type_checker,
                )
                .is_empty()
                || is_possibly_type_argument_position(info.called, source_file, type_checker)
        }
    }
}

// Go: ls/completions.go:2766 isContextTokenTypeLocation
pub fn is_context_token_type_location(context_token: Node) -> bool {
    if context_token.is_some() {
        let parent_kind = context_token.parent().kind();
        match context_token.kind() {
            SyntaxKind::ColonToken => {
                return parent_kind == SyntaxKind::PropertyDeclaration
                    || parent_kind == SyntaxKind::PropertySignature
                    || parent_kind == SyntaxKind::Parameter
                    || parent_kind == SyntaxKind::VariableDeclaration
                    || is_function_like_kind(parent_kind);
            }
            SyntaxKind::EqualsToken => {
                return parent_kind == SyntaxKind::TypeAliasDeclaration
                    || parent_kind == SyntaxKind::TypeParameter;
            }
            SyntaxKind::AsKeyword => {
                return parent_kind == SyntaxKind::AsExpression;
            }
            SyntaxKind::LessThanToken => {
                return parent_kind == SyntaxKind::TypeReference
                    || parent_kind == SyntaxKind::TypeAssertionExpression;
            }
            SyntaxKind::ExtendsKeyword => {
                return parent_kind == SyntaxKind::TypeParameter;
            }
            SyntaxKind::SatisfiesKeyword => {
                return parent_kind == SyntaxKind::SatisfiesExpression;
            }
            _ => {}
        }
    }
    false
}

/// Go `collections.Set[ast.SymbolId]` passed by value
/// (`symbolCanBeReferencedAtTypeLocation`, completions.go:2792).
// PORT: Go copies the `Set` struct on each call. A copy shares the map once
// the map exists; `Add` on a nil map makes a new map in that copy only.
// `None` is the nil map; a clone of `Some` shares the one map. Callers that
// pass Go's `collections.Set[ast.SymbolId]{}` pass `None`.
pub type SymbolIdSetValue = Option<Rc<RefCell<FxHashSet<u64>>>>;

// Go: collections/set.go:57 (*Set).AddIfAbsent, on a by-value `Set` copy.
fn symbol_id_set_add_if_absent(set: &mut SymbolIdSetValue, key: u64) -> bool {
    // Go: Has
    if let Some(m) = set.as_ref() {
        if RefCell::borrow(m).contains(&key) {
            return false;
        }
    }
    // Go: Add (makes the map in this copy when it is nil)
    RefCell::borrow_mut(set.get_or_insert_with(Default::default)).insert(key);
    true
}

// Go: ls/completions.go:2792 symbolCanBeReferencedAtTypeLocation
// True if symbol is a type or a module containing at least one type.
pub fn symbol_can_be_referenced_at_type_location(
    symbol: SymbolId,
    type_checker: &mut Checker,
    seen_modules: SymbolIdSetValue,
) -> bool {
    // Since an alias can be merged with a local declaration, we need to test both the alias and its target.
    // This code used to just test the result of `skipAlias`, but that would ignore any locally introduced meanings.
    non_alias_can_be_referenced_at_type_location(symbol, type_checker, seen_modules.clone()) || {
        let export_symbol = type_checker.sym(symbol).export_symbol;
        let target = type_checker.skip_alias(if export_symbol.is_some() {
            export_symbol
        } else {
            symbol
        });
        non_alias_can_be_referenced_at_type_location(target, type_checker, seen_modules)
    }
}

// Go: ls/completions.go:2803 nonAliasCanBeReferencedAtTypeLocation
pub fn non_alias_can_be_referenced_at_type_location(
    symbol: SymbolId,
    type_checker: &mut Checker,
    mut seen_modules: SymbolIdSetValue,
) -> bool {
    let flags = type_checker.sym(symbol).flags;
    flags.intersects(SymbolFlags::TYPE)
        || type_checker.is_unknown_symbol(symbol)
        || flags.intersects(SymbolFlags::MODULE)
            && symbol_id_set_add_if_absent(
                &mut seen_modules,
                get_symbol_id(&type_checker.symbols, symbol),
            )
            && type_checker
                .get_exports_of_module_exported(symbol)
                .into_iter()
                .any(|e| {
                    symbol_can_be_referenced_at_type_location(e, type_checker, seen_modules.clone())
                })
}

// Go: core/core.go:669 CheckEachDefined
fn check_each_defined(s: Vec<SymbolId>, msg: &str) -> Vec<SymbolId> {
    for value in &s {
        if value.is_nil() {
            panic!("{}", msg);
        }
    }
    s
}

// Go: ls/completions.go:2814 getPropertiesForCompletion
// Gets all properties on a type, but if that type is a union of several types,
// excludes array-like types or callable/constructable types.
pub fn get_properties_for_completion(t: TypeId, type_checker: &mut Checker) -> Vec<SymbolId> {
    if type_checker.ty(t).is_union() {
        let types = type_checker.ty(t).types().to_vec();
        check_each_defined(
            type_checker.get_all_possible_properties_of_types(&types),
            "getAllPossiblePropertiesOfTypes() should all be defined.",
        )
    } else {
        check_each_defined(
            type_checker.get_apparent_properties(t),
            "getApparentProperties() should all be defined.",
        )
    }
}

// Go: ls/completions.go:2823 getLeftMostName
// Given 'a.b.c', returns 'a'.
pub fn get_left_most_name(e: Node) -> Node {
    if is_identifier(e) {
        e
    } else if is_property_access_expression(e) {
        get_left_most_name(e.expression())
    } else {
        Node::NIL
    }
}

// Go: ls/completions.go:2833 getFirstSymbolInChain
pub fn get_first_symbol_in_chain(
    symbol: SymbolId,
    enclosing_declaration: Node,
    type_checker: &mut Checker,
) -> SymbolId {
    let chain = type_checker.get_accessible_symbol_chain_exported(
        symbol,
        enclosing_declaration,
        SymbolFlags::ALL, /*meaning*/
        false,            /*useOnlyExternalAliasing*/
    );
    if !chain.is_empty() {
        return chain[0];
    }
    let parent = type_checker.sym(symbol).parent;
    if parent.is_some() {
        if is_module_symbol(&type_checker.symbols, parent) {
            return symbol;
        }
        return get_first_symbol_in_chain(parent, enclosing_declaration, type_checker);
    }
    SymbolId::NIL
}

// Go: ls/completions.go:2852 isModuleSymbol
pub fn is_module_symbol(symbols: &SymbolArena, symbol: SymbolId) -> bool {
    symbols
        .sym(symbol)
        .declarations
        .iter()
        .any(|decl| decl.kind() == SyntaxKind::SourceFile)
}

// Go: ls/completions.go:2856 getNullableSymbolOriginInfoKind
pub fn get_nullable_symbol_origin_info_kind(
    kind: SymbolOriginInfoKind,
    insert_question_dot: bool,
) -> SymbolOriginInfoKind {
    let mut kind = kind;
    if insert_question_dot {
        kind |= SymbolOriginInfoKind::NULLABLE;
    }
    kind
}

// Go: ls/completions.go:2863 isStaticProperty
pub fn is_static_property(symbols: &SymbolArena, symbol: SymbolId) -> bool {
    let value_declaration = symbols.sym(symbol).value_declaration;
    value_declaration.is_some()
        && value_declaration
            .modifier_flags()
            .intersects(ModifierFlags::STATIC)
        && is_class_like(value_declaration.parent())
}

// Go: ls/completions.go:2871 getContextualTypeForConditionalExpression
// getContextualTypeForConditionalExpression handles completion within a conditional expression
// (ternary operator) by using the parent expression to find the contextual type.
pub fn get_contextual_type_for_conditional_expression(
    conditional_expr: Node,
    position: i32,
    file: Node,
    type_checker: &mut Checker,
) -> TypeId {
    let arg_info =
        get_argument_info_for_completions(conditional_expr, position, file, type_checker);
    if let Some(arg_info) = arg_info {
        return type_checker.get_contextual_type_for_argument_at_index_exported(
            arg_info.invocation,
            arg_info.argument_index,
        );
    }
    // Fall through to regular contextual type logic if not in an argument
    let contextual_type = type_checker
        .get_contextual_type_exported(conditional_expr, ContextFlags::IGNORE_NODE_INFERENCES);
    if contextual_type.is_some() {
        return contextual_type;
    }
    type_checker.get_contextual_type_exported(conditional_expr, ContextFlags::NONE)
}

// Go: ls/completions.go:2884 getContextualType
pub fn get_contextual_type(
    previous_token: Node,
    position: i32,
    file: Node,
    type_checker: &mut Checker,
) -> TypeId {
    let parent = previous_token.parent();
    match previous_token.kind() {
        SyntaxKind::Identifier => {
            return get_contextual_type_from_parent(
                previous_token,
                type_checker,
                ContextFlags::NONE,
            );
        }
        SyntaxKind::EqualsToken => {
            return match parent.kind() {
                SyntaxKind::VariableDeclaration => type_checker
                    .get_contextual_type_exported(parent.initializer(), ContextFlags::NONE),
                SyntaxKind::BinaryExpression => type_checker.get_type_at_location(parent.left()),
                SyntaxKind::JsxAttribute => {
                    type_checker.get_contextual_type_for_jsx_attribute_exported(parent)
                }
                _ => TypeId::NIL,
            };
        }
        SyntaxKind::NewKeyword => {
            return type_checker.get_contextual_type_exported(parent, ContextFlags::NONE);
        }
        SyntaxKind::CaseKeyword => {
            let case_clause = if is_case_clause(parent) {
                parent
            } else {
                Node::NIL
            };
            if case_clause.is_some() {
                return get_switched_type(case_clause, type_checker);
            }
            return TypeId::NIL;
        }
        SyntaxKind::OpenBraceToken => {
            if is_jsx_expression(parent)
                && !is_jsx_element(parent.parent())
                && !is_jsx_fragment(parent.parent())
            {
                return type_checker
                    .get_contextual_type_for_jsx_attribute_exported(parent.parent());
            }
            return TypeId::NIL;
        }
        SyntaxKind::OpenBracketToken => {
            // When completing after `[` in an array literal (e.g., `[/*here*/]`),
            // we should provide contextual type for the first element
            if is_array_literal_expression(parent) {
                let contextual_array_type =
                    type_checker.get_contextual_type_exported(parent, ContextFlags::NONE);
                if contextual_array_type.is_some() {
                    // Get the type for the first element (index 0)
                    return type_checker.get_contextual_type_for_array_literal_at_position(
                        contextual_array_type,
                        parent,
                        position,
                    );
                }
            }
            return TypeId::NIL;
        }
        SyntaxKind::CloseBracketToken => {
            // When completing after `]` (e.g., `[x]/*here*/`), we should not provide a contextual type
            // for the closing bracket token itself. Without this case, CloseBracketToken would fall through
            // to the default case, and if the parent is an array literal, GetContextualType would try to
            // find the token's index in the array elements (returning -1), leading to an out-of-bounds panic
            // in getContextualTypeForElementExpression.
            return TypeId::NIL;
        }
        SyntaxKind::QuestionToken => {
            // When completing after `?` in a ternary conditional (e.g., `foo(a ? /*here*/)`),
            // we need to look at the parent conditional expression to find the contextual type.
            if is_conditional_expression(parent) {
                return get_contextual_type_for_conditional_expression(
                    parent,
                    position,
                    file,
                    type_checker,
                );
            }
            return TypeId::NIL;
        }
        SyntaxKind::ColonToken => {
            // When completing after `:` in a ternary conditional (e.g., `foo(a ? b : /*here*/)`),
            // we need to look at the parent conditional expression to find the contextual type.
            // Only handle this if parent is ConditionalExpression, otherwise fall through to default
            // (colons are used in other contexts like object literals, type annotations, etc.)
            if is_conditional_expression(parent) {
                return get_contextual_type_for_conditional_expression(
                    parent,
                    position,
                    file,
                    type_checker,
                );
            }
        }
        SyntaxKind::CommaToken => {
            // When completing after `,` in an array literal (e.g., `[x, /*here*/]`),
            // we should provide contextual type for the element after the comma.
            if is_array_literal_expression(parent) {
                let contextual_array_type =
                    type_checker.get_contextual_type_exported(parent, ContextFlags::NONE);
                if contextual_array_type.is_some() {
                    return type_checker.get_contextual_type_for_array_literal_at_position(
                        contextual_array_type,
                        parent,
                        position,
                    );
                }
                return TypeId::NIL;
            }
        }
        _ => {}
    }
    // Default case: see if we're in an argument position.
    let arg_info = get_argument_info_for_completions(previous_token, position, file, type_checker);
    if let Some(arg_info) = arg_info {
        type_checker.get_contextual_type_for_argument_at_index_exported(
            arg_info.invocation,
            arg_info.argument_index,
        )
    } else if is_equality_operator_kind(previous_token.kind())
        && is_binary_expression(parent)
        && is_equality_operator_kind(parent.operator_token().kind())
    {
        // completion at `x ===/**/`
        type_checker.get_type_at_location(parent.left())
    } else {
        let contextual_type = type_checker
            .get_contextual_type_exported(previous_token, ContextFlags::IGNORE_NODE_INFERENCES);
        if contextual_type.is_some() {
            return contextual_type;
        }
        type_checker.get_contextual_type_exported(previous_token, ContextFlags::NONE)
    }
}

// Go: ls/completions.go:2973 getSwitchedType
pub fn get_switched_type(case_clause: Node, type_checker: &mut Checker) -> TypeId {
    type_checker.get_type_at_location(case_clause.parent().parent().expression())
}

// Go: ls/completions.go:2977 isEqualityOperatorKind
pub fn is_equality_operator_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::EqualsEqualsEqualsToken
            | SyntaxKind::EqualsEqualsToken
            | SyntaxKind::ExclamationEqualsEqualsToken
            | SyntaxKind::ExclamationEqualsToken
    )
}

// Go: ls/completions.go:2988 isLiteral
// We disregard boolean literals for completion purposes.
// PORT: Go reads the `*checker.Type`; the port reads the checker arena.
pub fn is_literal(type_checker: &Checker, t: TypeId) -> bool {
    let t = type_checker.ty(t);
    t.is_string_literal() || t.is_number_literal() || t.is_big_int_literal()
}

// Go: ls/completions.go:2992 getRecommendedCompletion
pub fn get_recommended_completion(
    previous_token: Node,
    contextual_type: TypeId,
    type_checker: &mut Checker,
) -> SymbolId {
    let types: Vec<TypeId> = if type_checker.ty(contextual_type).is_union() {
        type_checker.ty(contextual_type).types().to_vec()
    } else {
        vec![contextual_type]
    };
    // For a union, return the first one with a recommended completion.
    // Go: core.FirstNonNil
    for t in types {
        let symbol = type_checker.ty(t).symbol();
        // Don't make a recommended completion for an abstract class.
        let result = if symbol.is_some()
            && type_checker
                .sym(symbol)
                .flags
                .intersects(SymbolFlags::ENUM_MEMBER | SymbolFlags::ENUM | SymbolFlags::CLASS)
            && !is_abstract_constructor_symbol(&type_checker.symbols, symbol)
        {
            get_first_symbol_in_chain(symbol, previous_token, type_checker)
        } else {
            SymbolId::NIL
        };
        if result.is_some() {
            return result;
        }
    }
    SymbolId::NIL
}

// Go: ls/completions.go:3015 isAbstractConstructorSymbol
pub fn is_abstract_constructor_symbol(symbols: &SymbolArena, symbol: SymbolId) -> bool {
    if symbols.sym(symbol).flags.intersects(SymbolFlags::CLASS) {
        let declaration = get_class_like_declaration_of_symbol(symbols, symbol);
        return declaration.is_some()
            && has_syntactic_modifier(declaration, ModifierFlags::ABSTRACT);
    }
    false
}

// Go: ls/completions.go:3023 startsWithQuote
pub fn starts_with_quote(s: &str) -> bool {
    let (r, _) = utf8_decode_rune_in_string(s, 0);
    r == '"' as i32 || r == '\'' as i32
}

// Go: ls/completions.go:3028 getClosestSymbolDeclaration
pub fn get_closest_symbol_declaration(context_token: Node, location: Node) -> Node {
    if context_token.is_nil() {
        return Node::NIL;
    }

    let mut closest_declaration =
        find_ancestor_or_quit(context_token, |node: Node| -> FindAncestorResult {
            if is_function_block(node) || is_arrow_function_body(node) || is_binding_pattern(node) {
                return FindAncestorResult::FIND_ANCESTOR_QUIT;
            }

            if (is_parameter_declaration(node) || is_type_parameter_declaration(node))
                && !is_index_signature_declaration(node.parent())
            {
                return FindAncestorResult::FIND_ANCESTOR_TRUE;
            }
            FindAncestorResult::FIND_ANCESTOR_FALSE
        });

    if closest_declaration.is_nil() {
        closest_declaration = find_ancestor_or_quit(location, |node: Node| -> FindAncestorResult {
            if is_function_block(node) || is_arrow_function_body(node) || is_binding_pattern(node) {
                return FindAncestorResult::FIND_ANCESTOR_QUIT;
            }

            if is_variable_declaration(node) {
                return FindAncestorResult::FIND_ANCESTOR_TRUE;
            }
            FindAncestorResult::FIND_ANCESTOR_FALSE
        });
    }
    closest_declaration
}

// Go: ls/completions.go:3060 isArrowFunctionBody
pub fn is_arrow_function_body(node: Node) -> bool {
    node.parent().is_some()
        && is_arrow_function(node.parent())
        && (node.parent().body() == node ||
            // const a = () => /**/;
            node.kind() == SyntaxKind::EqualsGreaterThanToken)
}

// Go: ls/completions.go:3067 isInTypeParameterDefault
pub fn is_in_type_parameter_default(context_token: Node) -> bool {
    if context_token.is_nil() {
        return false;
    }

    let mut node = context_token;
    let mut parent = context_token.parent();
    while parent.is_some() {
        if is_type_parameter_declaration(parent) {
            return parent.default_type() == node || node.kind() == SyntaxKind::EqualsToken;
        }
        node = parent;
        parent = parent.parent();
    }

    false
}

// Go: ls/completions.go:3085 isDeprecated
pub fn is_deprecated(symbol: SymbolId, type_checker: &mut Checker) -> bool {
    let target = type_checker.skip_alias(symbol);
    let declarations: Vec<Node> = type_checker.sym(target).declarations.to_vec();
    !declarations.is_empty()
        && declarations
            .iter()
            .all(|&decl| type_checker.is_deprecated_declaration(decl))
}

impl LanguageService {
    // Go: ls/completions.go:3090 getReplacementRangeForContextToken
    pub fn get_replacement_range_for_context_token(
        &self,
        file: Node,
        context_token: Node,
        position: i32,
    ) -> Option<lsproto::Range> {
        if context_token.is_nil() {
            return None;
        }

        // !!! ensure range is single line
        match context_token.kind() {
            SyntaxKind::StringLiteral | SyntaxKind::NoSubstitutionTemplateLiteral => {
                self.create_range_from_string_literal_like_content(file, context_token, position)
            }
            _ => Some(self.create_lsp_range_from_node(context_token, file)),
        }
    }

    // Go: ls/completions.go:3104 createRangeFromStringLiteralLikeContent
    pub fn create_range_from_string_literal_like_content(
        &self,
        file: Node,
        node: Node,
        position: i32,
    ) -> Option<lsproto::Range> {
        let mut replacement_end = node.end() - 1;
        let node_start = astnav::get_start_of_node(node, file, false /*includeJSDoc*/);
        if is_unterminated_literal(node) {
            // we return no replacement range only if unterminated string is empty
            if node_start == replacement_end {
                return None;
            }
            replacement_end = position.min(node.end());
        }
        Some(self.create_lsp_range_from_bounds(node_start + 1, replacement_end, file))
    }
}

// Go: ls/completions.go:3117 quotePropertyName
pub fn quote_property_name(
    file: Node,
    preferences: &lsutil::UserPreferences,
    name: &str,
) -> String {
    let (r, _) = utf8_decode_rune_in_string(name, 0);
    if unicode_is_digit(r) {
        return name.to_string();
    }
    quote(file, preferences, name)
}

// Go: ls/completions.go:3128 isStringAndEmptyAnonymousObjectIntersection
// Checks whether type is `string & {}`, which is semantically equivalent to string but
// is not reduced by the checker as a special case used for supporting string literal completions
// for string type.
pub fn is_string_and_empty_anonymous_object_intersection(
    type_checker: &mut Checker,
    t: TypeId,
) -> bool {
    if !type_checker.ty(t).is_intersection() {
        return false;
    }

    let types = type_checker.ty(t).types().to_vec();
    types.len() == 2
        && (are_intersected_types_avoiding_string_reduction(type_checker, types[0], types[1])
            || are_intersected_types_avoiding_string_reduction(type_checker, types[1], types[0]))
}

// Go: ls/completions.go:3138 areIntersectedTypesAvoidingStringReduction
pub fn are_intersected_types_avoiding_string_reduction(
    type_checker: &mut Checker,
    t1: TypeId,
    t2: TypeId,
) -> bool {
    type_checker.ty(t1).is_string() && type_checker.is_empty_anonymous_object_type(t2)
}

// Go: ls/completions.go:3142 escapeSnippetText
pub fn escape_snippet_text(text: &str) -> String {
    text.replace('$', "\\$")
}

// Go: ls/completions.go:3146 isNamedImportsOrExports
pub fn is_named_imports_or_exports(node: Node) -> bool {
    is_named_imports(node) || is_named_exports(node)
}

// Go: ls/completions.go:3150 generateIdentifierForArbitraryString
pub fn generate_identifier_for_arbitrary_string(text: &str) -> String {
    let mut needs_underscore = false;
    let mut identifier = String::new();

    // Convert "(example, text)" into "_example_text_"
    let mut pos: usize = 0;
    while pos < text.len() {
        let (ch, size) = utf8_decode_rune_in_string(text, pos);
        let c = rune_to_char(ch);
        let valid_char = if pos == 0 {
            is_identifier_start(c)
        } else {
            is_identifier_part(c)
        };
        if size > 0 && valid_char {
            if needs_underscore {
                identifier.push('_');
            }
            identifier.push(c);
            needs_underscore = false;
        } else {
            needs_underscore = true;
        }
        pos += size as usize;
    }

    if needs_underscore {
        identifier.push('_');
    }

    // Default to "_" if the provided text was empty
    if identifier.is_empty() {
        return "_".to_string();
    }

    identifier
}

// Go: ls/completions.go:3190 getCompletionsSymbolKind
// Copied from vscode TS extension.
pub fn get_completions_symbol_kind(kind: lsutil::ScriptElementKind) -> lsproto::CompletionItemKind {
    use lsutil::ScriptElementKind as K;
    match kind {
        K::PRIMITIVE_TYPE | K::KEYWORD => lsproto::CompletionItemKind::KEYWORD,
        K::CONST_ELEMENT
        | K::LET_ELEMENT
        | K::VARIABLE_ELEMENT
        | K::LOCAL_VARIABLE_ELEMENT
        | K::ALIAS
        | K::PARAMETER_ELEMENT => lsproto::CompletionItemKind::VARIABLE,

        K::MEMBER_VARIABLE_ELEMENT
        | K::MEMBER_GET_ACCESSOR_ELEMENT
        | K::MEMBER_SET_ACCESSOR_ELEMENT => lsproto::CompletionItemKind::FIELD,

        K::FUNCTION_ELEMENT | K::LOCAL_FUNCTION_ELEMENT => lsproto::CompletionItemKind::FUNCTION,

        K::MEMBER_FUNCTION_ELEMENT
        | K::CONSTRUCT_SIGNATURE_ELEMENT
        | K::CALL_SIGNATURE_ELEMENT
        | K::INDEX_SIGNATURE_ELEMENT => lsproto::CompletionItemKind::METHOD,

        K::ENUM_ELEMENT => lsproto::CompletionItemKind::ENUM,

        K::ENUM_MEMBER_ELEMENT => lsproto::CompletionItemKind::ENUM_MEMBER,

        K::MODULE_ELEMENT | K::EXTERNAL_MODULE_NAME => lsproto::CompletionItemKind::MODULE,

        K::CLASS_ELEMENT | K::TYPE_ELEMENT => lsproto::CompletionItemKind::CLASS,

        K::INTERFACE_ELEMENT => lsproto::CompletionItemKind::INTERFACE,

        K::WARNING => lsproto::CompletionItemKind::TEXT,

        K::SCRIPT_ELEMENT => lsproto::CompletionItemKind::FILE,

        K::DIRECTORY => lsproto::CompletionItemKind::FOLDER,

        K::STRING => lsproto::CompletionItemKind::CONSTANT,

        _ => lsproto::CompletionItemKind::PROPERTY,
    }
}

// Go: ls/completions.go:3245 CompareCompletionEntries
// Editors will use the `sortText` and then fall back to `name` for sorting, but leave ties in response order.
// So, it's important that we sort those ties in the order we want them displayed if it matters. We don't
// strictly need to sort by name or SortText here since clients are going to do it anyway, but we have to
// do the work of comparing them so we can sort those ties appropriately.
// PORT: Go dereferences `SortText`; a nil pointer panics there, as the
// unwraps do here.
pub fn compare_completion_entries(a: &lsproto::CompletionItem, b: &lsproto::CompletionItem) -> i32 {
    let compare_strings = stringutil_ls::compare_strings_case_insensitive_then_sensitive;
    let mut result = compare_strings(
        a.sort_text.as_deref().unwrap(),
        b.sort_text.as_deref().unwrap(),
    );
    if result == stringutil_ls::COMPARISON_EQUAL {
        result = compare_strings(&a.label, &b.label);
    }
    result
}

thread_local! {
    // Go: ls/completions.go:3255 keywordCompletionsCache
    // PORT: Go `collections.SyncMap[KeywordCompletionFilters, ...]`; the key
    // is the filter value. One map per thread (every request runs on the
    // dispatch thread).
    static KEYWORD_COMPLETIONS_CACHE: RefCell<FxHashMap<i32, Vec<lsproto::CompletionItem>>> =
        RefCell::new(FxHashMap::default());

    // Go: ls/completions.go:3256 allKeywordCompletions (sync.OnceValue)
    static ALL_KEYWORD_COMPLETIONS: Vec<lsproto::CompletionItem> = {
        let first = SyntaxKind::FIRST_KEYWORD as u16;
        let last = SyntaxKind::LAST_KEYWORD as u16;
        let mut result = Vec::with_capacity((last - first + 1) as usize);
        for i in first..=last {
            let kind = SyntaxKind::try_from(i).expect("keyword kind");
            result.push(lsproto::CompletionItem {
                label: token_to_string(kind).to_string(),
                kind: Some(lsproto::CompletionItemKind::KEYWORD),
                sort_text: Some(SORT_TEXT_GLOBALS_OR_KEYWORDS.to_string()),
                ..Default::default()
            });
        }
        result
    };
}

// Go: ls/completions.go:3256 allKeywordCompletions
// PORT: Go returns the shared slice; the port returns a copy. Callers copy
// every item before they change it (`cloneItems`).
pub fn all_keyword_completions() -> Vec<lsproto::CompletionItem> {
    ALL_KEYWORD_COMPLETIONS.with(|items| items.clone())
}

// Go: ls/completions.go:3269 cloneItems
// PORT: Go returns nil for a nil input; a `Vec` has no nil, so both are empty.
pub fn clone_items(items: &[lsproto::CompletionItem]) -> Vec<CompletionItem> {
    let mut entries = Vec::with_capacity(items.len());
    for item in items {
        let item_clone = item.clone();
        entries.push(CompletionItem {
            completion_item: item_clone,
            symbol: SymbolId::NIL,
        });
    }
    entries
}

// Go: ls/completions.go:3281 getKeywordCompletions
pub fn get_keyword_completions(
    keyword_filter: KeywordCompletionFilters,
    filter_out_ts_only_keywords: bool,
) -> Vec<CompletionItem> {
    if !filter_out_ts_only_keywords {
        return clone_items(&get_typescript_keyword_completions(keyword_filter));
    }

    let index = keyword_filter.0 + KeywordCompletionFilters::LAST.0 + 1;
    let cached = KEYWORD_COMPLETIONS_CACHE.with(|cache| cache.borrow().get(&index).cloned());
    if let Some(cached) = cached {
        return clone_items(&cached);
    }
    let result: Vec<lsproto::CompletionItem> = get_typescript_keyword_completions(keyword_filter)
        .into_iter()
        .filter(|ci| !is_type_script_only_keyword(string_to_token(&ci.label)))
        .collect();
    KEYWORD_COMPLETIONS_CACHE.with(|cache| {
        cache.borrow_mut().insert(index, result.clone());
    });
    clone_items(&result)
}

// Go: ls/completions.go:3300 getTypescriptKeywordCompletions
pub fn get_typescript_keyword_completions(
    keyword_filter: KeywordCompletionFilters,
) -> Vec<lsproto::CompletionItem> {
    let cached =
        KEYWORD_COMPLETIONS_CACHE.with(|cache| cache.borrow().get(&keyword_filter.0).cloned());
    if let Some(cached) = cached {
        return cached;
    }
    let result: Vec<lsproto::CompletionItem> = all_keyword_completions()
        .into_iter()
        .filter(|entry| {
            let kind = string_to_token(&entry.label);
            match keyword_filter {
                KeywordCompletionFilters::NONE => false,
                KeywordCompletionFilters::ALL => {
                    is_function_like_body_keyword(kind)
                        || kind == SyntaxKind::DeclareKeyword
                        || kind == SyntaxKind::ModuleKeyword
                        || kind == SyntaxKind::TypeKeyword
                        || kind == SyntaxKind::NamespaceKeyword
                        || kind == SyntaxKind::AbstractKeyword
                        || is_type_keyword(kind) && kind != SyntaxKind::UndefinedKeyword
                }
                KeywordCompletionFilters::FUNCTION_LIKE_BODY_KEYWORDS => {
                    is_function_like_body_keyword(kind)
                }
                KeywordCompletionFilters::CLASS_ELEMENT_KEYWORDS => {
                    is_class_member_completion_keyword(kind)
                }
                KeywordCompletionFilters::INTERFACE_ELEMENT_KEYWORDS => {
                    is_interface_or_type_literal_completion_keyword(kind)
                }
                KeywordCompletionFilters::CONSTRUCTOR_PARAMETER_KEYWORDS => {
                    is_parameter_property_modifier(kind)
                }
                KeywordCompletionFilters::TYPE_ASSERTION_KEYWORDS => {
                    is_type_keyword(kind) || kind == SyntaxKind::ConstKeyword
                }
                KeywordCompletionFilters::TYPE_KEYWORDS => is_type_keyword(kind),
                KeywordCompletionFilters::TYPE_KEYWORD => kind == SyntaxKind::TypeKeyword,
                _ => panic!("Unknown keyword filter: {}", keyword_filter.0),
            }
        })
        .collect();

    KEYWORD_COMPLETIONS_CACHE.with(|cache| {
        cache.borrow_mut().insert(keyword_filter.0, result.clone());
    });
    result
}

// Go: ls/completions.go:3340 isTypeScriptOnlyKeyword
pub fn is_type_script_only_keyword(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::AbstractKeyword
            | SyntaxKind::AnyKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::DeclareKeyword
            | SyntaxKind::EnumKeyword
            | SyntaxKind::GlobalKeyword
            | SyntaxKind::ImplementsKeyword
            | SyntaxKind::InferKeyword
            | SyntaxKind::InterfaceKeyword
            | SyntaxKind::IsKeyword
            | SyntaxKind::KeyOfKeyword
            | SyntaxKind::ModuleKeyword
            | SyntaxKind::NamespaceKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::OverrideKeyword
            | SyntaxKind::PrivateKeyword
            | SyntaxKind::ProtectedKeyword
            | SyntaxKind::PublicKeyword
            | SyntaxKind::ReadonlyKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::TypeKeyword
            | SyntaxKind::UniqueKeyword
            | SyntaxKind::UnknownKeyword
    )
}

// Go: ls/completions.go:3375 isFunctionLikeBodyKeyword
pub fn is_function_like_body_keyword(kind: SyntaxKind) -> bool {
    kind == SyntaxKind::AsyncKeyword
        || kind == SyntaxKind::AwaitKeyword
        || kind == SyntaxKind::UsingKeyword
        || kind == SyntaxKind::AsKeyword
        || kind == SyntaxKind::SatisfiesKeyword
        || kind == SyntaxKind::TypeKeyword
        || !is_contextual_keyword(kind) && !is_class_member_completion_keyword(kind)
}

// Go: ls/completions.go:3385 isClassMemberCompletionKeyword
pub fn is_class_member_completion_keyword(kind: SyntaxKind) -> bool {
    match kind {
        SyntaxKind::AbstractKeyword
        | SyntaxKind::AccessorKeyword
        | SyntaxKind::ConstructorKeyword
        | SyntaxKind::GetKeyword
        | SyntaxKind::SetKeyword
        | SyntaxKind::AsyncKeyword
        | SyntaxKind::DeclareKeyword
        | SyntaxKind::OverrideKeyword => true,
        _ => is_class_member_modifier(kind),
    }
}

// Go: ls/completions.go:3395 isInterfaceOrTypeLiteralCompletionKeyword
pub fn is_interface_or_type_literal_completion_keyword(kind: SyntaxKind) -> bool {
    kind == SyntaxKind::ReadonlyKeyword
}

// Go: ls/completions.go:3399 isContextualKeywordInAutoImportableExpressionSpace
pub fn is_contextual_keyword_in_auto_importable_expression_space(keyword: &str) -> bool {
    keyword == "abstract"
        || keyword == "async"
        || keyword == "await"
        || keyword == "declare"
        || keyword == "module"
        || keyword == "namespace"
        || keyword == "type"
        || keyword == "satisfies"
        || keyword == "as"
}

// Go: ls/completions.go:3411 getContextualKeywords
pub fn get_contextual_keywords(
    file: Node,
    context_token: Node,
    position: i32,
) -> Vec<lsproto::CompletionItem> {
    let mut entries: Vec<lsproto::CompletionItem> = Vec::new();
    // An `AssertClause` can come after an import declaration:
    //  import * from "foo" |
    //  import "foo" |
    // or after a re-export declaration that has a module specifier:
    //  export { foo } from "foo" |
    // Source: https://tc39.es/proposal-import-assertions/
    if context_token.is_some() {
        let parent = context_token.parent();
        let token_line = get_ecma_line_of_position(file, context_token.end());
        let current_line = get_ecma_line_of_position(file, position);
        if (is_import_declaration(parent)
            || is_export_declaration(parent) && parent.module_specifier().is_some())
            && context_token == parent.module_specifier()
            && token_line == current_line
        {
            entries.push(lsproto::CompletionItem {
                label: token_to_string(SyntaxKind::AssertKeyword).to_string(),
                kind: Some(lsproto::CompletionItemKind::KEYWORD),
                sort_text: Some(SORT_TEXT_GLOBALS_OR_KEYWORDS.to_string()),
                ..Default::default()
            });
        }
    }
    entries
}

impl LanguageService {
    // Go: ls/completions.go:3437 getJSCompletionEntries
    // PORT: Go ranges over the name table map in random order; the port
    // uses the map's own order. Clients sort by sort text and label.
    pub fn get_js_completion_entries(
        &self,
        ctx: &Context,
        file: Node,
        position: i32,
        unique_names: &mut FxHashSet<String>,
        sorted_entries: Vec<CompletionItem>,
    ) -> Vec<CompletionItem> {
        let mut sorted_entries = sorted_entries;
        let name_table = source_file_get_name_table(file);
        for (name, &pos) in name_table {
            // Skip identifiers produced only from the current location
            if pos == position {
                continue;
            }
            if !unique_names.contains(name) && is_identifier_text(name, LanguageVariant::STANDARD) {
                unique_names.insert(name.clone());
                sorted_entries.push(CompletionItem {
                    completion_item: lsproto::CompletionItem {
                        label: name.clone(),
                        kind: Some(lsproto::CompletionItemKind::TEXT),
                        sort_text: Some(SORT_TEXT_JAVASCRIPT_IDENTIFIERS.to_string()),
                        commit_characters: Some(Vec::new()),
                        ..Default::default()
                    },
                    symbol: SymbolId::NIL,
                });
            }
        }
        sorted_entries
    }

    // Go: ls/completions.go:3465 getOptionalReplacementSpan
    pub fn get_optional_replacement_span(
        &self,
        location: Node,
        file: Node,
    ) -> Option<lsproto::Range> {
        // StringLiteralLike locations are handled separately in stringCompletions.ts
        if location.is_some()
            && (location.kind() == SyntaxKind::Identifier
                || location.kind() == SyntaxKind::PrivateIdentifier)
        {
            let start = astnav::get_start_of_node(location, file, false /*includeJSDoc*/);
            return Some(self.create_lsp_range_from_bounds(start, location.end(), file));
        }
        None
    }
}

// Go: ls/completions.go:3474 isMemberCompletionKind
pub fn is_member_completion_kind(kind: CompletionKind) -> bool {
    kind == CompletionKind::OBJECT_PROPERTY_DECLARATION
        || kind == CompletionKind::MEMBER_LIKE
        || kind == CompletionKind::PROPERTY_ACCESS
}

// Go: ls/completions.go:3480 tryGetFunctionLikeBodyCompletionContainer
pub fn try_get_function_like_body_completion_container(context_token: Node) -> Node {
    if context_token.is_nil() {
        return Node::NIL;
    }

    let mut prev = Node::NIL;
    find_ancestor_or_quit(context_token, |node: Node| -> FindAncestorResult {
        if is_class_like(node) {
            return FindAncestorResult::FIND_ANCESTOR_QUIT;
        }
        if is_function_like_declaration(node) && prev == node.body() {
            return FindAncestorResult::FIND_ANCESTOR_TRUE;
        }
        prev = node;
        FindAncestorResult::FIND_ANCESTOR_FALSE
    })
}

// ---------------------------------------------------------------------------
// Go `unicode` and `unicode/utf8` helpers used above (file-local).
// ---------------------------------------------------------------------------

/// Go `utf8.DecodeRuneInString(text[pos:end])` over a byte range of `text`.
// PORT: Go cuts the string at `end` first. A `&str` cannot be cut inside a
// character, so the decoder reads `text` and treats the bytes from `end` on
// as missing: an empty range is `(RuneError, 0)` and a rune cut at `end` is
// `(RuneError, 1)`, as in Go.
fn decode_rune_in_range(text: &str, pos: usize, end: usize) -> (i32, i32) {
    if pos >= end {
        return (RUNE_ERROR, 0);
    }
    let (r, size) = utf8_decode_rune_in_string(text, pos);
    if pos + size as usize > end {
        return (RUNE_ERROR, 1);
    }
    (r, size)
}

/// A decoded Go rune as a `char` (`utf8.RuneError` is U+FFFD).
fn rune_to_char(r: i32) -> char {
    char::from_u32(r as u32).unwrap_or(char::REPLACEMENT_CHARACTER)
}

/// Go `unicode.IsSpace`.
// PORT: Go `unicode.IsSpace` is the Unicode White_Space property, the same
// set as Rust `char::is_whitespace` (U+0085 and U+00A0 are in both; U+180E is
// in neither).
fn unicode_is_space(r: i32) -> bool {
    char::from_u32(r as u32).is_some_and(char::is_whitespace)
}

// Go: unicode/tables.go _Nd (Unicode 15.0.0, the pinned Go 1.26 toolchain).
const UNICODE_ND_RANGES: [(u32, u32); 64] = [
    (0x0030, 0x0039),
    (0x0660, 0x0669),
    (0x06f0, 0x06f9),
    (0x07c0, 0x07c9),
    (0x0966, 0x096f),
    (0x09e6, 0x09ef),
    (0x0a66, 0x0a6f),
    (0x0ae6, 0x0aef),
    (0x0b66, 0x0b6f),
    (0x0be6, 0x0bef),
    (0x0c66, 0x0c6f),
    (0x0ce6, 0x0cef),
    (0x0d66, 0x0d6f),
    (0x0de6, 0x0def),
    (0x0e50, 0x0e59),
    (0x0ed0, 0x0ed9),
    (0x0f20, 0x0f29),
    (0x1040, 0x1049),
    (0x1090, 0x1099),
    (0x17e0, 0x17e9),
    (0x1810, 0x1819),
    (0x1946, 0x194f),
    (0x19d0, 0x19d9),
    (0x1a80, 0x1a89),
    (0x1a90, 0x1a99),
    (0x1b50, 0x1b59),
    (0x1bb0, 0x1bb9),
    (0x1c40, 0x1c49),
    (0x1c50, 0x1c59),
    (0xa620, 0xa629),
    (0xa8d0, 0xa8d9),
    (0xa900, 0xa909),
    (0xa9d0, 0xa9d9),
    (0xa9f0, 0xa9f9),
    (0xaa50, 0xaa59),
    (0xabf0, 0xabf9),
    (0xff10, 0xff19),
    (0x104a0, 0x104a9),
    (0x10d30, 0x10d39),
    (0x11066, 0x1106f),
    (0x110f0, 0x110f9),
    (0x11136, 0x1113f),
    (0x111d0, 0x111d9),
    (0x112f0, 0x112f9),
    (0x11450, 0x11459),
    (0x114d0, 0x114d9),
    (0x11650, 0x11659),
    (0x116c0, 0x116c9),
    (0x11730, 0x11739),
    (0x118e0, 0x118e9),
    (0x11950, 0x11959),
    (0x11c50, 0x11c59),
    (0x11d50, 0x11d59),
    (0x11da0, 0x11da9),
    (0x11f50, 0x11f59),
    (0x16a60, 0x16a69),
    (0x16ac0, 0x16ac9),
    (0x16b50, 0x16b59),
    (0x1d7ce, 0x1d7ff),
    (0x1e140, 0x1e149),
    (0x1e2f0, 0x1e2f9),
    (0x1e4f0, 0x1e4f9),
    (0x1e950, 0x1e959),
    (0x1fbf0, 0x1fbf9),
];

/// Go `unicode.IsDigit`: general category Nd.
// PORT: Rust `char::is_numeric` is Nd, Nl and No; the Go Nd table above
// gives Go's exact test.
fn unicode_is_digit(r: i32) -> bool {
    // Go: `if r <= MaxLatin1`
    if r <= 0xFF {
        return ('0' as i32) <= r && r <= ('9' as i32);
    }
    let r = r as u32;
    UNICODE_ND_RANGES.iter().any(|&(lo, hi)| lo <= r && r <= hi)
}
