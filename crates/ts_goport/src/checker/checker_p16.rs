//! Port of typescript-go `internal/checker/checker.go` lines 13929-14828.
//!
//! PORT: Go `c.error(...)` returns the `*ast.Diagnostic` it already added, and
//! some Go callers mutate it afterwards (`AddRelatedInfo`). Our `Diagnostic`
//! is owned, so those callers build the diagnostic with
//! `new_diagnostic_for_node`, finish it, then call `add_diagnostic`. That is
//! exactly what Go `c.error` does, with the same final state. Functions that
//! return the Go `*ast.Diagnostic` return a clone of the added diagnostic.

use crate::prelude::*;
use ts_diagnostics::Message;

impl Checker {
    // Go: checker/checker.go:13929 errorSkippedOnNoEmit
    // PORT: `SetSkippedOnNoEmit` is set before the diagnostic is added (the
    // diagnostic is owned); Go sets it on the added pointer. Same final state.
    pub fn error_skipped_on_no_emit(
        &mut self,
        location: Node,
        message: &'static Message,
        args: Vec<String>,
    ) -> Diagnostic {
        let mut diagnostic = new_diagnostic_for_node(location, message, args);
        diagnostic.set_skipped_on_no_emit();
        self.add_diagnostic(diagnostic.clone());
        diagnostic
    }

    // Go: checker/checker.go:13935 errorOrSuggestion
    pub fn error_or_suggestion(
        &mut self,
        is_error: bool,
        location: Node,
        message: &'static Message,
        args: Vec<String>,
    ) {
        self.add_error_or_suggestion(is_error, new_diagnostic_for_node(location, message, args));
    }

    // Go: checker/checker.go:13939 errorAndMaybeSuggestAwait
    // PORT: the related info is attached before the diagnostic is added (see
    // the file comment).
    pub fn error_and_maybe_suggest_await(
        &mut self,
        location: Node,
        maybe_missing_await: bool,
        message: &'static Message,
        args: Vec<String>,
    ) -> Diagnostic {
        let mut diagnostic = new_diagnostic_for_node(location, message, args);
        if maybe_missing_await {
            diagnostic.add_related_info(Some(create_diagnostic_for_node(
                location,
                diag::Did_you_forget_to_use_await,
                args![],
            )));
        }
        self.add_diagnostic(diagnostic.clone());
        diagnostic
    }

    // Go: checker/checker.go:13947 addErrorOrSuggestion
    pub fn add_error_or_suggestion(&mut self, is_error: bool, diagnostic: Diagnostic) {
        if is_error {
            self.add_diagnostic(diagnostic);
        } else {
            let mut suggestion = diagnostic.clone();
            suggestion.set_category(ts_diagnostics::Category::Suggestion);
            self.add_suggestion_diagnostic(suggestion);
        }
    }

    // Go: checker/checker.go:13957 IsDeprecatedDeclaration
    // PERF: U4 (CH7). A node of a store without the flag is not deprecated
    // (`frozen_store_lacks_deprecated_tag`), so the cached combined flags
    // are not read. That cache is a one-entry memo of a pure function, so
    // skipping its update changes no result.
    pub fn is_deprecated_declaration(&mut self, declaration: Node) -> bool {
        if frozen_store_lacks_deprecated_tag(declaration) {
            debug_assert!(
                !get_combined_node_flags(declaration)
                    .intersects(NodeFlags::POSSIBLY_CONTAINS_DEPRECATED_TAG)
            );
            return false;
        }
        let flags = self.get_combined_node_flags_cached(declaration);
        is_deprecated_declaration_with_cached_flags(declaration, flags)
    }

    // Go: checker/checker.go:13961 addDeprecatedSuggestion
    pub fn add_deprecated_suggestion(
        &mut self,
        location: Node,
        declarations: &[Node],
        deprecated_entity: &str,
    ) -> Diagnostic {
        let diagnostic =
            new_diagnostic_for_node(location, diag::X_0_is_deprecated, args![deprecated_entity]);
        self.add_deprecated_suggestion_worker(declarations, diagnostic)
    }

    // Go: checker/checker.go:13966 addDeprecatedSuggestionWorker
    // PORT: takes the diagnostic by value and returns a clone of the added one.
    pub fn add_deprecated_suggestion_worker(
        &mut self,
        declarations: &[Node],
        mut diagnostic: Diagnostic,
    ) -> Diagnostic {
        for &declaration in declarations {
            let deprecated_tag = get_js_doc_deprecated_tag(declaration);
            if deprecated_tag.is_some() {
                diagnostic.add_related_info(Some(new_diagnostic_for_node(
                    deprecated_tag,
                    diag::The_declaration_was_marked_as_deprecated_here,
                    args![],
                )));
                break;
            }
        }
        self.add_suggestion_diagnostic(diagnostic.clone());
        diagnostic
    }

    // Go: checker/checker.go:13978 isDeprecatedSymbol
    pub fn is_deprecated_symbol(&mut self, symbol: SymbolId) -> bool {
        let parent_symbol = self.get_parent_of_symbol(symbol);
        let declarations = self.sym(symbol).declarations.clone();
        if parent_symbol.is_some() && declarations.len() > 1 {
            if self
                .sym(parent_symbol)
                .flags
                .intersects(SymbolFlags::INTERFACE)
            {
                for &d in &declarations {
                    if self.is_deprecated_declaration(d) {
                        return true;
                    }
                }
                return false;
            } else {
                for &d in &declarations {
                    if !self.is_deprecated_declaration(d) {
                        return false;
                    }
                }
                return true;
            }
        }
        let value_declaration = self.sym(symbol).value_declaration;
        if value_declaration.is_some() && self.is_deprecated_declaration(value_declaration) {
            return true;
        }
        if declarations.is_empty() {
            return false;
        }
        for &d in &declarations {
            if !self.is_deprecated_declaration(d) {
                return false;
            }
        }
        true
    }

    // Go: checker/checker.go:13990 hasParseDiagnostics
    pub fn has_parse_diagnostics(&self, source_file: Node) -> bool {
        !source_file_info(source_file).diagnostics.is_empty()
    }

    // Go: checker/checker.go:13994 newSymbol
    pub fn new_symbol(&mut self, flags: SymbolFlags, name: impl Into<Name>) -> SymbolId {
        self.symbol_count += 1;
        self.symbols
            .new_symbol(flags | SymbolFlags::TRANSIENT, name)
    }

    // Go: checker/checker.go:14002 newSymbolEx
    pub fn new_symbol_ex(
        &mut self,
        flags: SymbolFlags,
        name: impl Into<Name>,
        check_flags: CheckFlags,
    ) -> SymbolId {
        let result = self.new_symbol(flags, name);
        self.sym_mut(result).check_flags = check_flags;
        result
    }

    // Go: checker/checker.go:14008 newParameter
    pub fn new_parameter(&mut self, name: &str, t: TypeId) -> SymbolId {
        let symbol = self.new_symbol(SymbolFlags::FUNCTION_SCOPED_VARIABLE, name);
        self.value_symbol_links.get(symbol).resolved_type = t;
        symbol
    }

    // Go: checker/checker.go:14014 newProperty
    pub fn new_property(&mut self, name: &str, t: TypeId) -> SymbolId {
        let symbol = self.new_symbol(SymbolFlags::PROPERTY, name);
        self.value_symbol_links.get(symbol).resolved_type = t;
        symbol
    }

    // Go: checker/checker.go:14020 combineSymbolTables
    pub fn combine_symbol_tables(
        &mut self,
        first: SymbolTable,
        second: SymbolTable,
    ) -> SymbolTable {
        if self.symbols.len(first) == 0 {
            return second;
        }
        if self.symbols.len(second) == 0 {
            return first;
        }
        let combined = self.symbols.new_table();
        self.merge_symbol_table(combined, first, false, SymbolId::NIL);
        self.merge_symbol_table(combined, second, false, SymbolId::NIL);
        combined
    }

    // Go: checker/checker.go:14033 mergeSymbolTable
    // PORT: Go ranges over the map in random order; this iterates a snapshot
    // of `source` in insertion order.
    pub fn merge_symbol_table(
        &mut self,
        target: SymbolTable,
        source: SymbolTable,
        unidirectional: bool,
        merged_parent: SymbolId,
    ) {
        for (id, source_symbol) in self.symbols.entries(source) {
            let target_symbol = self.symbols.get(target, &id);
            let merged = if target_symbol.is_some() {
                self.merge_symbol(target_symbol, source_symbol, unidirectional)
            } else {
                self.get_merged_symbol(source_symbol)
            };
            if merged_parent.is_some() && target_symbol.is_some() {
                // If a merge was performed on the target symbol, set its parent to the merged parent that initiated the merge
                // of its exports. Otherwise, `merged` came only from `sourceSymbol` and can keep its parent:
                //
                // // a.ts
                // export interface A { x: number; }
                //
                // // b.ts
                // declare module "./a" {
                //   interface A { y: number; }
                //   interface B {}
                // }
                //
                // When merging the module augmentation into a.ts, the symbol for `A` will itself be merged, so its parent
                // should be the merged module symbol. But the symbol for `B` has only one declaration, so its parent should
                // be the module augmentation symbol, which contains its only declaration.
                if self.sym(merged).flags.intersects(SymbolFlags::TRANSIENT) {
                    self.sym_mut(merged).parent = merged_parent;
                }
            }
            self.symbols.set(target, id, merged);
        }
    }

    // Go: checker/checker.go:14070 mergeSymbol
    /**
     * Note: if target is transient, then it is mutable, and mergeSymbol with both mutate and return it.
     * If target is not transient, mergeSymbol will produce a transient clone, mutate that and return it.
     */
    pub fn merge_symbol(
        &mut self,
        mut target: SymbolId,
        source: SymbolId,
        unidirectional: bool,
    ) -> SymbolId {
        let source_flags = self.sym(source).flags;
        let target_flags = self.sym(target).flags;
        if !target_flags.intersects(get_excluded_symbol_flags(source_flags))
            || (source_flags | target_flags).intersects(SymbolFlags::ASSIGNMENT)
        {
            if source == target {
                // This can happen when an export assigned namespace exports something also erroneously exported at the top level
                // See `declarationFileNoCrashOnExtraExportModifier` for an example
                return target;
            }
            if !target_flags.intersects(SymbolFlags::TRANSIENT) {
                let resolved_target = self.resolve_symbol(target);
                if resolved_target == self.unknown_symbol {
                    return source;
                }
                let resolved_flags = self.sym(resolved_target).flags;
                if !resolved_flags.intersects(get_excluded_symbol_flags(source_flags))
                    || (source_flags | resolved_flags).intersects(SymbolFlags::ASSIGNMENT)
                {
                    target = self.clone_symbol(resolved_target);
                } else {
                    self.report_merge_symbol_error(target, source);
                    return source;
                }
            }
            // Javascript static-property-assignment declarations always merge, even though they are also values
            let target_flags = self.sym(target).flags;
            if source_flags.intersects(SymbolFlags::VALUE_MODULE)
                && target_flags.intersects(SymbolFlags::VALUE_MODULE)
                && target_flags.intersects(SymbolFlags::CONST_ENUM_ONLY_MODULE)
                && !source_flags.intersects(SymbolFlags::CONST_ENUM_ONLY_MODULE)
            {
                // reset flag when merging instantiated module into value module that has only const enums
                self.sym_mut(target).flags =
                    target_flags.without(SymbolFlags::CONST_ENUM_ONLY_MODULE);
            }
            let mut merged_flags = source_flags;
            if !self
                .sym(target)
                .flags
                .intersects(SymbolFlags::CONST_ENUM_ONLY_MODULE)
            {
                merged_flags = merged_flags.without(SymbolFlags::CONST_ENUM_ONLY_MODULE);
            }
            self.sym_mut(target).flags |= merged_flags;
            let source_value_declaration = self.sym(source).value_declaration;
            if source_value_declaration.is_some() {
                set_value_declaration(&mut self.symbols, target, source_value_declaration);
            }
            let source_declarations = self.sym(source).declarations.clone();
            let target_declarations = &mut self.sym_mut(target).declarations;
            for &d in source_declarations.iter() {
                target_declarations.push(d);
            }
            let source_members = self.sym(source).members;
            if source_members.is_some() {
                let mut members = self.sym(target).members;
                let table = get_symbol_table(&mut self.symbols, &mut members);
                self.sym_mut(target).members = members;
                self.merge_symbol_table(table, source_members, unidirectional, SymbolId::NIL);
            }
            let source_exports = self.sym(source).exports;
            if source_exports.is_some() {
                let mut exports = self.sym(target).exports;
                let table = get_symbol_table(&mut self.symbols, &mut exports);
                self.sym_mut(target).exports = exports;
                self.merge_symbol_table(table, source_exports, unidirectional, target);
            }
            if !unidirectional {
                self.record_merged_symbol(target, source);
            }
        } else if target_flags.intersects(SymbolFlags::NAMESPACE_MODULE) {
            // Do not report an error when merging `var globalThis` with the built-in `globalThis`,
            // as we will already report a "Declaration name conflicts..." error, and this error
            // won't make much sense.
            if target != self.global_this_symbol {
                let first_declaration = self.get_first_declaration(source);
                let symbol_string = self.symbol_to_string(target);
                self.error(
                    get_name_of_declaration(first_declaration),
                    diag::Cannot_augment_module_0_with_value_exports_because_it_resolves_to_a_non_module_entity,
                    args![symbol_string],
                );
            }
        } else {
            self.report_merge_symbol_error(target, source);
        }
        target
    }

    // Go: checker/checker.go:14121 reportMergeSymbolError
    pub fn report_merge_symbol_error(&mut self, target: SymbolId, source: SymbolId) {
        let target_flags = self.sym(target).flags;
        let source_flags = self.sym(source).flags;
        let is_either_enum = target_flags.intersects(SymbolFlags::ENUM)
            || source_flags.intersects(SymbolFlags::ENUM);
        let is_either_block_scoped = target_flags.intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE)
            || source_flags.intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE);
        let message: &'static Message = if is_either_enum {
            diag::Enum_declarations_can_only_merge_with_namespace_or_other_enum_declarations
        } else if is_either_block_scoped {
            diag::Cannot_redeclare_block_scoped_variable_0
        } else {
            diag::Duplicate_identifier_0
        };
        // PORT: Go `ast.GetSourceFileOfNode(nil)` returns nil.
        let source_first = self.get_first_declaration(source);
        let target_first = self.get_first_declaration(target);
        let source_symbol_file = if source_first.is_some() {
            get_source_file_of_node(source_first)
        } else {
            Node::NIL
        };
        let target_symbol_file = if target_first.is_some() {
            get_source_file_of_node(target_first)
        } else {
            Node::NIL
        };
        let is_source_plain_js =
            is_plain_js_file(source_symbol_file, self.compiler_options.check_js);
        let is_target_plain_js =
            is_plain_js_file(target_symbol_file, self.compiler_options.check_js);
        let symbol_name = self.symbol_to_string(source);
        if !is_source_plain_js {
            self.add_duplicate_declaration_errors_for_symbols(
                source,
                message,
                &symbol_name,
                target,
            );
        }
        if !is_target_plain_js {
            self.add_duplicate_declaration_errors_for_symbols(
                target,
                message,
                &symbol_name,
                source,
            );
        }
    }

    // Go: checker/checker.go:14146 addDuplicateDeclarationErrorsForSymbols
    pub fn add_duplicate_declaration_errors_for_symbols(
        &mut self,
        target: SymbolId,
        message: &'static Message,
        symbol_name: &str,
        source: SymbolId,
    ) {
        let target_declarations = self.sym(target).declarations.clone();
        let source_declarations = self.sym(source).declarations.clone();
        for &node in target_declarations.iter() {
            self.add_duplicate_declaration_error(node, message, symbol_name, &source_declarations);
        }
    }

    // Go: checker/checker.go:14152 addDuplicateDeclarationError
    // PORT: Go mutates the diagnostic returned by `lookupOrIssueError`, which
    // is either the stored diagnostic found by `Lookup` or the newly added one.
    // Diagnostics are owned here, so an existing diagnostic is mutated in place
    // inside `c.diagnostics`, and a new one is completed before it is added.
    // The loop body only reads the diagnostic and the AST, so the final state
    // matches Go.
    pub fn add_duplicate_declaration_error(
        &mut self,
        node: Node,
        message: &'static Message,
        symbol_name: &str,
        related_nodes: &[Node],
    ) {
        let mut error_node = get_adjusted_node_for_error(node);
        if error_node.is_nil() {
            error_node = node;
        }
        // Inlined `c.lookupOrIssueError(errorNode, message, symbolName)`.
        let diagnostic = new_diagnostic_for_node(error_node, message, args![symbol_name]);
        if let Some(existing) = lookup_stored_diagnostic(&mut self.diagnostics, &diagnostic) {
            add_duplicate_declaration_related_info(
                existing,
                error_node,
                symbol_name,
                related_nodes,
            );
            return;
        }
        let mut err = diagnostic;
        add_duplicate_declaration_related_info(&mut err, error_node, symbol_name, related_nodes);
        self.add_diagnostic(err);
    }
}

// PORT: loop body of Go `addDuplicateDeclarationError`, split out so it can
// run on either the stored or the new diagnostic.
fn add_duplicate_declaration_related_info(
    err: &mut Diagnostic,
    error_node: Node,
    symbol_name: &str,
    related_nodes: &[Node],
) {
    for &related_node in related_nodes {
        let adjusted_node = get_adjusted_node_for_error(related_node);
        if adjusted_node == error_node {
            continue;
        }
        let leading_message = create_diagnostic_for_node(
            adjusted_node,
            diag::X_0_was_also_declared_here,
            args![symbol_name],
        );
        let follow_on_message =
            create_diagnostic_for_node(adjusted_node, diag::X_and_here, args![]);
        if err.related_information().len() >= 5
            || err.related_information().iter().any(|d| {
                compare_diagnostics(d, &follow_on_message) == 0
                    || compare_diagnostics(d, &leading_message) == 0
            })
        {
            continue;
        }
        if err.related_information().is_empty() {
            err.add_related_info(Some(leading_message));
        } else {
            err.add_related_info(Some(follow_on_message));
        }
    }
}

// PORT: Go `DiagnosticsCollection.Lookup` returns the stored pointer, which
// Go callers may mutate. `DiagnosticsCollection::lookup` returns a clone, so
// this finds the stored entry after `lookup` has sorted the list.
fn lookup_stored_diagnostic<'a>(
    collection: &'a mut DiagnosticsCollection,
    diagnostic: &Diagnostic,
) -> Option<&'a mut Diagnostic> {
    collection.lookup(diagnostic)?;
    let list: &mut Vec<Diagnostic> = if diagnostic.file().is_some() {
        collection
            .file_diagnostics
            .get_mut(source_file_file_name(diagnostic.file()))?
    } else {
        &mut collection.non_file_diagnostics
    };
    let i = list.partition_point(|d| compare_diagnostics(d, diagnostic) < 0);
    list.get_mut(i)
}

// Go: checker/checker.go:14178 createDiagnosticForNode
pub fn create_diagnostic_for_node(
    node: Node,
    message: &'static Message,
    args: Vec<String>,
) -> Diagnostic {
    new_diagnostic_for_node(node, message, args)
}

// Go: checker/checker.go:14182 getAdjustedNodeForError
pub fn get_adjusted_node_for_error(node: Node) -> Node {
    let name = get_name_of_declaration(node);
    if name.is_some() {
        return name;
    }
    node
}

impl Checker {
    // Go: checker/checker.go:14190 lookupOrIssueError
    // PORT: returns a clone of the stored or added diagnostic. Callers that
    // mutate the result must mutate the stored entry (see
    // `add_duplicate_declaration_error`).
    pub fn lookup_or_issue_error(
        &mut self,
        location: Node,
        message: &'static Message,
        args: Vec<String>,
    ) -> Diagnostic {
        let diagnostic = new_diagnostic_for_node(location, message, args);
        let existing = self.diagnostics.lookup(&diagnostic);
        if let Some(existing) = existing {
            return existing;
        }
        self.add_diagnostic(diagnostic.clone());
        diagnostic
    }

    // Go: checker/checker.go:14200 getFirstDeclaration
    // PORT: package-level Go function that reads symbol data, so a method.
    pub fn get_first_declaration(&self, symbol: SymbolId) -> Node {
        let declarations = &self.sym(symbol).declarations;
        if !declarations.is_empty() {
            return declarations[0];
        }
        Node::NIL
    }
}

// Go: checker/checker.go:14207 getExcludedSymbolFlags
pub fn get_excluded_symbol_flags(flags: SymbolFlags) -> SymbolFlags {
    let mut result = SymbolFlags::NONE;
    if flags.intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE) {
        result |= SymbolFlags::BLOCK_SCOPED_VARIABLE_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::FUNCTION_SCOPED_VARIABLE) {
        result |= SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::PROPERTY) {
        result |= SymbolFlags::PROPERTY_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::ENUM_MEMBER) {
        result |= SymbolFlags::ENUM_MEMBER_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::FUNCTION) {
        result |= SymbolFlags::FUNCTION_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::CLASS) {
        result |= SymbolFlags::CLASS_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::INTERFACE) {
        result |= SymbolFlags::INTERFACE_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::REGULAR_ENUM) {
        result |= SymbolFlags::REGULAR_ENUM_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::CONST_ENUM) {
        result |= SymbolFlags::CONST_ENUM_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::VALUE_MODULE) {
        result |= SymbolFlags::VALUE_MODULE_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::METHOD) {
        result |= SymbolFlags::METHOD_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::GET_ACCESSOR) {
        result |= SymbolFlags::GET_ACCESSOR_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::SET_ACCESSOR) {
        result |= SymbolFlags::SET_ACCESSOR_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::TYPE_PARAMETER) {
        result |= SymbolFlags::TYPE_PARAMETER_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::TYPE_ALIAS) {
        result |= SymbolFlags::TYPE_ALIAS_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::ALIAS) {
        result |= SymbolFlags::ALIAS_EXCLUDES;
    }
    if flags.intersects(SymbolFlags::REPLACEABLE_BY_METHOD) {
        result = result.without(SymbolFlags::METHOD);
    }
    result
}

// PORT: Go `maps.Clone(table)` on an `ast.SymbolTable`. A nil map clones to
// nil; otherwise a new table with the same entries.
fn maps_clone_symbol_table(symbols: &mut SymbolArena, table: SymbolTable) -> SymbolTable {
    symbols.clone_table(table)
}

impl Checker {
    // Go: checker/checker.go:14263 cloneSymbol
    pub fn clone_symbol(&mut self, symbol: SymbolId) -> SymbolId {
        let flags = self.sym(symbol).flags;
        let name = self.sym(symbol).name.clone();
        let result = self.new_symbol(flags, &name);
        // Force reallocation if anything is ever appended to declarations
        // PORT: a `Vec` clone never shares storage, which is what the Go
        // capacity-limited slice ensures.
        let declarations = self.sym(symbol).declarations.clone();
        let parent = self.sym(symbol).parent;
        let value_declaration = self.sym(symbol).value_declaration;
        let members = self.sym(symbol).members;
        let exports = self.sym(symbol).exports;
        self.sym_mut(result).declarations = declarations;
        self.sym_mut(result).parent = parent;
        self.sym_mut(result).value_declaration = value_declaration;
        let cloned_members = maps_clone_symbol_table(&mut self.symbols, members);
        self.sym_mut(result).members = cloned_members;
        let cloned_exports = maps_clone_symbol_table(&mut self.symbols, exports);
        self.sym_mut(result).exports = cloned_exports;
        self.record_merged_symbol(result, symbol);
        result
    }

    // Go: checker/checker.go:14275 getMergedSymbol
    pub fn get_merged_symbol(&self, symbol: SymbolId) -> SymbolId {
        if symbol.is_some() {
            if let Some(&merged) = self.merged_symbols.get(&symbol) {
                if merged.is_some() {
                    return merged;
                }
            }
        }
        symbol
    }

    // Go: checker/checker.go:14285 getParentOfSymbol
    pub fn get_parent_of_symbol(&mut self, symbol: SymbolId) -> SymbolId {
        let parent = self.sym(symbol).parent;
        if parent.is_some() {
            let late = self.get_late_bound_symbol(parent);
            return self.get_merged_symbol(late);
        }
        SymbolId::NIL
    }

    // Go: checker/checker.go:14292 recordMergedSymbol
    pub fn record_merged_symbol(&mut self, target: SymbolId, source: SymbolId) {
        self.merged_symbols.insert(source, target);
    }

    // Go: checker/checker.go:14296 getSymbolIfSameReference
    pub fn get_symbol_if_same_reference(&mut self, s1: SymbolId, s2: SymbolId) -> SymbolId {
        let m1 = self.get_merged_symbol(s1);
        let r1 = self.resolve_symbol(m1);
        let left = self.get_merged_symbol(r1);
        let m2 = self.get_merged_symbol(s2);
        let r2 = self.resolve_symbol(m2);
        let right = self.get_merged_symbol(r2);
        if left == right {
            return s1;
        }
        SymbolId::NIL
    }

    // Go: checker/checker.go:14303 getExportSymbolOfValueSymbolIfExported
    pub fn get_export_symbol_of_value_symbol_if_exported(&self, mut symbol: SymbolId) -> SymbolId {
        if symbol.is_some()
            && self.sym(symbol).flags.intersects(SymbolFlags::EXPORT_VALUE)
            && self.sym(symbol).export_symbol.is_some()
        {
            symbol = self.sym(symbol).export_symbol;
        }
        self.get_merged_symbol(symbol)
    }

    // Go: checker/checker.go:14310 getSymbolOfDeclaration
    pub fn get_symbol_of_declaration(&mut self, node: Node) -> SymbolId {
        let symbol = node.symbol();
        if symbol.is_some() {
            let late = self.get_late_bound_symbol(symbol);
            return self.get_merged_symbol(late);
        }
        SymbolId::NIL
    }

    // Go: checker/checker.go:14320 getSymbolOfNode
    // Get the merged symbol for a node. If you know the node is a `Declaration`, it is more type safe to
    // use use `getSymbolOfDeclaration` instead.
    // PORT: Go reads `node.DeclarationData().Symbol`; `node.symbol()` is the
    // binder symbol stored for declaration nodes (nil for other nodes), the
    // same value Go `node.Symbol()` reads from `DeclarationData`.
    pub fn get_symbol_of_node(&mut self, node: Node) -> SymbolId {
        let symbol = node.symbol();
        if symbol.is_some() {
            let late = self.get_late_bound_symbol(symbol);
            return self.get_merged_symbol(late);
        }
        SymbolId::NIL
    }

    // Go: checker/checker.go:14328 getLateBoundSymbol
    pub fn get_late_bound_symbol(&mut self, symbol: SymbolId) -> SymbolId {
        if !self.sym(symbol).flags.intersects(SymbolFlags::CLASS_MEMBER)
            || self.sym(symbol).name != INTERNAL_SYMBOL_NAME_COMPUTED
        {
            return symbol;
        }
        if self.late_bound_links.get(symbol).late_symbol.is_nil() {
            let declarations = self.sym(symbol).declarations.clone();
            let mut has_late_bindable = false;
            for &d in &declarations {
                if self.has_late_bindable_name(d) {
                    has_late_bindable = true;
                    break;
                }
            }
            if has_late_bindable {
                // force late binding of members/exports. This will set the late-bound symbol
                let parent = self.get_merged_symbol(self.sym(symbol).parent);
                if declarations.iter().any(|&d| has_static_modifier(d)) {
                    self.get_exports_of_symbol(parent);
                } else {
                    self.get_members_of_symbol(parent);
                }
            }
        }
        let links = self.late_bound_links.get(symbol);
        if links.late_symbol.is_nil() {
            links.late_symbol = symbol;
        }
        links.late_symbol
    }

    // Go: checker/checker.go:14348 resolveSymbol
    pub fn resolve_symbol(&mut self, symbol: SymbolId) -> SymbolId {
        self.resolve_symbol_ex(symbol, false /*dontResolveAlias*/)
    }

    // Go: checker/checker.go:14352 resolveSymbolEx
    pub fn resolve_symbol_ex(&mut self, symbol: SymbolId, dont_resolve_alias: bool) -> SymbolId {
        if !dont_resolve_alias
            && is_non_local_alias(
                &self.symbols,
                symbol,
                SymbolFlags::VALUE | SymbolFlags::TYPE | SymbolFlags::NAMESPACE,
            )
        {
            return self.resolve_alias(symbol);
        }
        symbol
    }

    // Go: checker/checker.go:14359 getTargetOfImportEqualsDeclaration
    pub fn get_target_of_import_equals_declaration(&mut self, node: Node) -> SymbolId {
        // Node is ImportEqualsDeclaration | VariableDeclaration
        if is_variable_declaration(node)
            || node.module_reference().kind() == SyntaxKind::ExternalModuleReference
        {
            let mut module_reference = get_external_module_require_argument(node);
            if module_reference.is_nil() {
                module_reference = get_external_module_import_equals_declaration_expression(node);
            }
            let immediate = self.resolve_external_module_name(
                node,
                module_reference,
                false, /*ignoreErrors*/
            );
            let resolved =
                self.resolve_external_module_symbol(immediate, true /*dontResolveAlias*/);
            if resolved.is_some()
                && ModuleKind::NODE20 <= self.module_kind
                && self.module_kind <= ModuleKind::NODE_NEXT
            {
                let module_exports = self.get_export_of_module(
                    resolved,
                    INTERNAL_SYMBOL_NAME_MODULE_EXPORTS,
                    node,
                    true, /*dontResolveAlias*/
                );
                if module_exports.is_some() {
                    return module_exports;
                }
            }
            self.mark_symbol_of_alias_declaration_if_type_only(node, Node::NIL);
            return resolved;
        }
        let resolved =
            self.get_symbol_of_part_of_right_hand_side_of_import_equals(node.module_reference());
        self.check_and_report_error_for_resolving_import_alias_to_type_only_symbol(node, resolved);
        resolved
    }

    // Go: checker/checker.go:14382 resolveExternalModuleTypeByLiteral
    pub fn resolve_external_module_type_by_literal(&mut self, name: Node) -> TypeId {
        let module_sym = self.resolve_external_module_name(name, name, false /*ignoreErrors*/);
        if module_sym.is_some() {
            let resolved_module_symbol =
                self.resolve_external_module_symbol(module_sym, false /*dontResolveAlias*/);
            if resolved_module_symbol.is_some() {
                return self.get_type_of_symbol(resolved_module_symbol);
            }
        }
        self.any_type
    }

    // Go: checker/checker.go:14394 getSymbolOfPartOfRightHandSideOfImportEquals
    // This function is only for imports with entity names
    pub fn get_symbol_of_part_of_right_hand_side_of_import_equals(
        &mut self,
        mut entity_name: Node,
    ) -> SymbolId {
        // There are three things we might try to look for. In the following examples,
        // the search term is enclosed in |...|:
        //
        //     import a = |b|; // Namespace
        //     import a = |b.c|; // Value, type, namespace
        //     import a = |b.c|.d; // Namespace
        if entity_name.kind() == SyntaxKind::Identifier
            && is_right_side_of_qualified_name_or_property_access(entity_name)
        {
            entity_name = entity_name.parent(); // QualifiedName
        }
        // Check for case 1 and 3 in the above example
        if entity_name.kind() == SyntaxKind::Identifier
            || entity_name.parent().kind() == SyntaxKind::QualifiedName
        {
            return self.resolve_entity_name(
                entity_name,
                SymbolFlags::NAMESPACE,
                false,     /*ignoreErrors*/
                true,      /*dontResolveAlias*/
                Node::NIL, /*location*/
            );
        }
        // Case 2 in above example
        // entityName.kind could be a QualifiedName or a Missing identifier
        debug_assert!(entity_name.parent().kind() == SyntaxKind::ImportEqualsDeclaration);
        self.resolve_entity_name(
            entity_name,
            SymbolFlags::VALUE | SymbolFlags::TYPE | SymbolFlags::NAMESPACE,
            false,     /*ignoreErrors*/
            true,      /*dontResolveAlias*/
            Node::NIL, /*location*/
        )
    }

    // Go: checker/checker.go:14414 checkAndReportErrorForResolvingImportAliasToTypeOnlySymbol
    pub fn check_and_report_error_for_resolving_import_alias_to_type_only_symbol(
        &mut self,
        node: Node,
        resolved: SymbolId,
    ) {
        let module_reference = node.module_reference();
        let mut name = module_reference;
        loop {
            let type_only_declaration = self.get_type_only_declaration_of_entity_name(name);
            if type_only_declaration.is_some() {
                let is_export = node_kind_is(
                    type_only_declaration,
                    &[SyntaxKind::ExportSpecifier, SyntaxKind::ExportDeclaration],
                );
                let message: &'static Message = if is_export {
                    diag::An_import_alias_cannot_reference_a_declaration_that_was_exported_using_export_type
                } else {
                    diag::An_import_alias_cannot_reference_a_declaration_that_was_imported_using_import_type
                };
                let related_message: &'static Message = if is_export {
                    diag::X_0_was_exported_here
                } else {
                    diag::X_0_was_imported_here
                };
                // TODO: how to get name for export *?
                let mut name_text = "*".to_string();
                if !is_export_declaration(type_only_declaration) {
                    name_text = type_only_declaration.name().text().to_string();
                }
                // PORT: Go adds related info to the diagnostic returned by
                // `c.error`. Build, annotate, then add (see the file comment).
                let mut diagnostic = new_diagnostic_for_node(module_reference, message, args![]);
                diagnostic.add_related_info(Some(create_diagnostic_for_node(
                    type_only_declaration,
                    related_message,
                    args![name_text],
                )));
                self.add_diagnostic(diagnostic);
                break;
            }
            if is_identifier(name) {
                break;
            }
            name = name.left();
        }
    }

    // Go: checker/checker.go:14441 getTypeOnlyDeclarationOfEntityName
    pub fn get_type_only_declaration_of_entity_name(&mut self, name: Node) -> Node {
        let symbol = self.resolve_entity_name(
            name,
            SymbolFlags::VALUE | SymbolFlags::TYPE | SymbolFlags::NAMESPACE,
            true,      /*ignoreErrors*/
            true,      /*dontResolveAlias*/
            Node::NIL, /*location*/
        );
        if symbol.is_some() {
            return self.get_type_only_alias_declaration(symbol);
        }
        Node::NIL
    }

    // Go: checker/checker.go:14448 getTargetOfImportClause
    pub fn get_target_of_import_clause(&mut self, node: Node) -> SymbolId {
        let module_symbol = self.resolve_external_module_name(
            node,
            get_module_specifier_from_node(node.parent()),
            false, /*ignoreErrors*/
        );
        if module_symbol.is_some() {
            return self.get_target_of_module_default(
                module_symbol,
                node,
                true, /*dontResolveAlias*/
            );
        }
        SymbolId::NIL
    }

    // Go: checker/checker.go:14456 getTargetOfModuleDefault
    pub fn get_target_of_module_default(
        &mut self,
        module_symbol: SymbolId,
        node: Node,
        dont_resolve_alias: bool,
    ) -> SymbolId {
        let file = self
            .sym(module_symbol)
            .declarations
            .iter()
            .copied()
            .find(|&d| is_source_file(d))
            .unwrap_or(Node::NIL);
        let specifier = self.get_module_specifier_for_import_or_export(node);
        let mut export_default_symbol: SymbolId;
        let mut export_module_dot_exports_symbol = SymbolId::NIL;
        if self.is_shorthand_ambient_module_symbol(module_symbol) {
            // !!! exportDefaultSymbol = moduleSymbol
            // Does nothing?
        } else if file.is_some()
            && specifier.is_some()
            && ModuleKind::NODE20 <= self.module_kind
            && self.module_kind <= ModuleKind::NODE_NEXT
            && self.get_emit_syntax_for_module_specifier_expression(specifier)
                == ModuleKind::COMMON_JS
            && get_implied_node_format_for_emit(file) == ModuleKind::ES_NEXT
        {
            export_module_dot_exports_symbol = self.resolve_export_by_name(
                module_symbol,
                INTERNAL_SYMBOL_NAME_MODULE_EXPORTS,
                node,
                dont_resolve_alias,
            );
        }
        if export_module_dot_exports_symbol.is_some() {
            // We have a transpiled default import where the `require` resolves to an ES module with a `module.exports` named
            // export. With `esModuleInterop` (always enabled), this will work:
            //
            // const dep_1 = __importDefault(require("./dep.mjs")); // wraps like { default: require("./dep.mjs") }
            // dep_1.default; // require("./dep.mjs") -> the `module.exports` export value
            self.mark_symbol_of_alias_declaration_if_type_only(node, Node::NIL);
            return export_module_dot_exports_symbol;
        } else {
            export_default_symbol = self.resolve_export_by_name(
                module_symbol,
                INTERNAL_SYMBOL_NAME_DEFAULT,
                node,
                dont_resolve_alias,
            );
        }
        if specifier.is_nil() {
            return export_default_symbol;
        }
        let has_default_only = self.is_only_importable_as_default(specifier, module_symbol);
        let has_synthetic_default =
            self.can_have_synthetic_default(file, module_symbol, dont_resolve_alias, specifier);
        if export_default_symbol.is_nil() && !has_synthetic_default && !has_default_only {
            if is_import_clause(node) {
                self.report_non_default_export(module_symbol, node);
            } else {
                let name = if is_import_or_export_specifier(node) {
                    node.property_name_or_name()
                } else {
                    node.name()
                };
                self.error_no_module_member_symbol(module_symbol, module_symbol, node, name);
            }
        } else if has_synthetic_default || has_default_only {
            // per emit behavior, a synthetic default overrides a "real" .default member if `__esModule` is not present
            let mut resolved =
                self.resolve_external_module_symbol(module_symbol, dont_resolve_alias);
            if resolved.is_nil() {
                resolved = self.resolve_symbol_ex(module_symbol, dont_resolve_alias);
            }
            self.mark_symbol_of_alias_declaration_if_type_only(node, Node::NIL);
            return resolved;
        }
        self.mark_symbol_of_alias_declaration_if_type_only(node, Node::NIL);
        export_default_symbol
    }

    // Go: checker/checker.go:14511 reportNonDefaultExport
    pub fn report_non_default_export(&mut self, module_symbol: SymbolId, node: Node) {
        let exports = self.sym(module_symbol).exports;
        let node_symbol = node.symbol();
        let node_symbol_name = self.sym(node_symbol).name.clone();
        if exports.is_some() && self.symbols.get(exports, &node_symbol_name).is_some() {
            let module_string = self.symbol_to_string(module_symbol);
            let node_symbol_string = self.symbol_to_string(node_symbol);
            self.error(
                node,
                diag::Module_0_has_no_default_export_Did_you_mean_to_use_import_1_from_0_instead,
                args![module_string, node_symbol_string],
            );
        } else {
            // PORT: Go adds related info to the diagnostic returned by
            // `c.error`. Build, annotate, then add (see the file comment).
            let module_string = self.symbol_to_string(module_symbol);
            let mut diagnostic = new_diagnostic_for_node(
                node.name(),
                diag::Module_0_has_no_default_export,
                args![module_string],
            );
            let mut export_star = SymbolId::NIL;
            if exports.is_some() {
                export_star = self.symbols.get(exports, INTERNAL_SYMBOL_NAME_EXPORT_STAR);
            }
            if export_star.is_some() {
                let declarations = self.sym(export_star).declarations.clone();
                let mut default_export = Node::NIL;
                for &decl in declarations.iter() {
                    let found = if !(is_export_declaration(decl)
                        && decl.module_specifier().is_some())
                    {
                        false
                    } else {
                        let resolved_external_module_name = self.resolve_external_module_name(
                            decl,
                            decl.module_specifier(),
                            false, /*ignoreErrors*/
                        );
                        resolved_external_module_name.is_some() && {
                            let resolved_exports = self.sym(resolved_external_module_name).exports;
                            self.symbols
                                .get(resolved_exports, INTERNAL_SYMBOL_NAME_DEFAULT)
                                .is_some()
                        }
                    };
                    if found {
                        default_export = decl;
                        break;
                    }
                }
                if default_export.is_some() {
                    diagnostic.add_related_info(Some(create_diagnostic_for_node(
                        default_export,
                        diag::X_export_Asterisk_does_not_re_export_a_default,
                        args![],
                    )));
                }
            }
            self.add_diagnostic(diagnostic);
        }
    }

    // Go: checker/checker.go:14535 resolveExportByName
    pub fn resolve_export_by_name(
        &mut self,
        module_symbol: SymbolId,
        name: &str,
        source_node: Node,
        dont_resolve_alias: bool,
    ) -> SymbolId {
        let exports = self.sym(module_symbol).exports;
        let export_value = self
            .symbols
            .get(exports, INTERNAL_SYMBOL_NAME_EXPORT_EQUALS);
        let export_symbol = if export_value.is_some() {
            let t = self.get_type_of_symbol(export_value);
            self.get_property_of_type_ex(
                t, name, true,  /*skipObjectFunctionPropertyAugment*/
                false, /*includeTypeOnlyMembers*/
            )
        } else {
            self.symbols.get(exports, name)
        };
        let resolved = self.resolve_symbol_ex(export_symbol, dont_resolve_alias);
        self.mark_symbol_of_alias_declaration_if_type_only(source_node, Node::NIL);
        resolved
    }

    // Go: checker/checker.go:14548 getTargetOfNamespaceImport
    pub fn get_target_of_namespace_import(&mut self, node: Node) -> SymbolId {
        let module_specifier = self.get_module_specifier_for_import_or_export(node);
        let immediate =
            self.resolve_external_module_name(node, module_specifier, false /*ignoreErrors*/);
        let resolved = self.resolve_es_module_symbol(immediate, node, module_specifier);
        self.mark_symbol_of_alias_declaration_if_type_only(node, Node::NIL);
        resolved
    }

    // Go: checker/checker.go:14556 getTargetOfNamespaceExport
    pub fn get_target_of_namespace_export(&mut self, node: Node) -> SymbolId {
        let module_specifier = self.get_module_specifier_for_import_or_export(node);
        if module_specifier.is_some() {
            let immediate = self.resolve_external_module_name(
                node,
                module_specifier,
                false, /*ignoreErrors*/
            );
            let resolved = self.resolve_es_module_symbol(immediate, node, module_specifier);
            self.mark_symbol_of_alias_declaration_if_type_only(node, Node::NIL);
            return resolved;
        }
        SymbolId::NIL
    }

    // Go: checker/checker.go:14567 getTargetOfImportSpecifier
    pub fn get_target_of_import_specifier(&mut self, node: Node) -> SymbolId {
        let name = node.property_name_or_name();
        if is_import_specifier(node) && module_export_name_is_default(name) {
            let specifier = self.get_module_specifier_for_import_or_export(node);
            if specifier.is_some() {
                let module_symbol =
                    self.resolve_external_module_name(node, specifier, false /*ignoreErrors*/);
                if module_symbol.is_some() {
                    return self.get_target_of_module_default(
                        module_symbol,
                        node,
                        true, /*dontResolveAlias*/
                    );
                }
            }
        }
        let mut root = node.parent().parent().parent(); // ImportDeclaration
        if is_binding_element(node) {
            root = get_root_declaration(node);
        }
        let resolved = self.get_external_module_member(root, node, true /*dontResolveAlias*/);
        self.mark_symbol_of_alias_declaration_if_type_only(node, Node::NIL);
        resolved
    }

    // Go: checker/checker.go:14587 getExternalModuleMember
    pub fn get_external_module_member(
        &mut self,
        node: Node,
        specifier: Node,
        dont_resolve_alias: bool,
    ) -> SymbolId {
        // node is ImportDeclaration | ExportDeclaration | VariableDeclaration
        // specifier is ImportSpecifier | ExportSpecifier | BindingElement | PropertyAccessExpression
        let mut module_specifier = get_external_module_require_argument(node);
        if module_specifier.is_nil() {
            module_specifier = get_external_module_name(node);
        }
        let module_symbol =
            self.resolve_external_module_name(node, module_specifier, false /*ignoreErrors*/);
        let name = if !is_property_access_expression(specifier) {
            specifier.property_name_or_name()
        } else {
            specifier.name()
        };
        if !is_identifier(name) && !is_string_literal(name) {
            return SymbolId::NIL;
        }
        let name_text = name.text();
        let target_symbol =
            self.resolve_es_module_symbol(module_symbol, specifier, module_specifier);
        if target_symbol.is_some() {
            // Note: The empty string is a valid module export name:
            //
            //   import { "" as foo } from "./foo";
            //   export { foo as "" };
            //
            if !name_text.is_empty() || name.kind() == SyntaxKind::StringLiteral {
                if self.is_shorthand_ambient_module_symbol(module_symbol) {
                    return module_symbol;
                }
                // PORT: Go `moduleSymbol.Exports[...]` with a nil `moduleSymbol`
                // is guarded by `moduleSymbol != nil`.
                let has_export_equals = module_symbol.is_some() && {
                    let exports = self.sym(module_symbol).exports;
                    self.symbols
                        .get(exports, INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
                        .is_some()
                };
                let mut symbol_from_variable;
                // First check if module was specified with "export=". If so, get the member from the resolved type
                if has_export_equals {
                    let t = self.get_type_of_symbol(target_symbol);
                    symbol_from_variable = self.get_property_of_type_ex(
                        t, name_text, true,  /*skipObjectFunctionPropertyAugment*/
                        false, /*includeTypeOnlyMembers*/
                    );
                } else {
                    symbol_from_variable = self.get_property_of_variable(target_symbol, name_text);
                }
                // if symbolFromVariable is export - get its final target
                symbol_from_variable =
                    self.resolve_symbol_ex(symbol_from_variable, dont_resolve_alias);
                let mut export_container = target_symbol;
                let has_export_equals = module_symbol.is_some() && {
                    let exports = self.sym(module_symbol).exports;
                    self.symbols
                        .get(exports, INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
                        .is_some()
                };
                if has_export_equals {
                    // For `export =` modules, supplemental type/namespace exports live on the original module symbol.
                    export_container = module_symbol;
                }
                let mut symbol_from_module = self.get_export_of_module(
                    export_container,
                    name_text,
                    specifier,
                    dont_resolve_alias,
                );
                if symbol_from_module.is_nil() && name_text == INTERNAL_SYMBOL_NAME_DEFAULT {
                    let file = self
                        .sym(module_symbol)
                        .declarations
                        .iter()
                        .copied()
                        .find(|&d| is_source_file(d))
                        .unwrap_or(Node::NIL);
                    if self.is_only_importable_as_default(module_specifier, module_symbol)
                        || self.can_have_synthetic_default(
                            file,
                            module_symbol,
                            dont_resolve_alias,
                            module_specifier,
                        )
                    {
                        symbol_from_module =
                            self.resolve_external_module_symbol(module_symbol, dont_resolve_alias);
                        if symbol_from_module.is_nil() {
                            symbol_from_module =
                                self.resolve_symbol_ex(module_symbol, dont_resolve_alias);
                        }
                    }
                }
                let mut symbol = symbol_from_variable;
                if symbol_from_module.is_some() {
                    symbol = symbol_from_module;
                    if symbol_from_variable.is_some() {
                        symbol = self.combine_value_and_type_symbols(
                            symbol_from_variable,
                            symbol_from_module,
                        );
                    }
                }
                if is_import_or_export_specifier(specifier)
                    && self.is_only_importable_as_default(module_specifier, module_symbol)
                    && name_text != INTERNAL_SYMBOL_NAME_DEFAULT
                {
                    let module_kind_string = self.module_kind.string();
                    self.error(
                        name,
                        diag::Named_imports_from_a_JSON_file_into_an_ECMAScript_module_are_not_allowed_when_module_is_set_to_0,
                        args![module_kind_string],
                    );
                } else if symbol.is_nil() {
                    self.error_no_module_member_symbol(module_symbol, target_symbol, node, name);
                }
                return symbol;
            }
        }
        SymbolId::NIL
    }

    // Go: checker/checker.go:14658 getPropertyOfVariable
    pub fn get_property_of_variable(&mut self, symbol: SymbolId, name: &str) -> SymbolId {
        if self.sym(symbol).flags.intersects(SymbolFlags::VARIABLE) {
            let type_annotation = self.sym(symbol).value_declaration.type_();
            if type_annotation.is_some() {
                let t = self.get_type_from_type_node(type_annotation);
                let prop = self.get_property_of_type(t, name);
                return self.resolve_symbol(prop);
            }
        }
        SymbolId::NIL
    }

    // Go: checker/checker.go:14686 combineValueAndTypeSymbols
    // This function creates a synthetic symbol that combines the value side of one symbol with the
    // type/namespace side of another symbol. Consider this example:
    //
    //	declare module graphics {
    //	    interface Point {
    //	        x: number;
    //	        y: number;
    //	    }
    //	}
    //	declare var graphics: {
    //	    Point: new (x: number, y: number) => graphics.Point;
    //	}
    //	declare module "graphics" {
    //	    export = graphics;
    //	}
    //
    // An 'import { Point } from "graphics"' needs to create a symbol that combines the value side 'Point'
    // property with the type/namespace side interface 'Point'.
    pub fn combine_value_and_type_symbols(
        &mut self,
        value_symbol: SymbolId,
        type_symbol: SymbolId,
    ) -> SymbolId {
        if value_symbol == self.unknown_symbol && type_symbol == self.unknown_symbol {
            return self.unknown_symbol;
        }
        if self.sym(type_symbol).flags.intersects(SymbolFlags::VALUE) {
            return type_symbol;
        }
        if self
            .sym(value_symbol)
            .flags
            .intersects(SymbolFlags::TYPE | SymbolFlags::NAMESPACE)
        {
            return value_symbol;
        }
        let flags = self.sym(value_symbol).flags | self.sym(type_symbol).flags;
        let name = self.sym(value_symbol).name.clone();
        let result = self.new_symbol(flags, &name);
        debug_assert!(
            !self.sym(value_symbol).declarations.is_empty()
                || !self.sym(type_symbol).declarations.is_empty()
        );
        // Go: slices.Compact(slices.Concat(...)) removes consecutive duplicates.
        let mut declarations: Vec<Node> = self.sym(value_symbol).declarations.to_vec();
        declarations.extend(self.sym(type_symbol).declarations.iter().copied());
        declarations.dedup();
        let mut parent = self.sym(value_symbol).parent;
        if parent.is_nil() {
            parent = self.sym(type_symbol).parent;
        }
        let value_declaration = self.sym(value_symbol).value_declaration;
        let type_members = self.sym(type_symbol).members;
        let value_exports = self.sym(value_symbol).exports;
        self.sym_mut(result).declarations = declarations.into();
        self.sym_mut(result).parent = parent;
        self.sym_mut(result).value_declaration = value_declaration;
        let members = maps_clone_symbol_table(&mut self.symbols, type_members);
        self.sym_mut(result).members = members;
        let exports = maps_clone_symbol_table(&mut self.symbols, value_exports);
        self.sym_mut(result).exports = exports;
        result
    }

    // Go: checker/checker.go:14709 getExportOfModule
    pub fn get_export_of_module(
        &mut self,
        symbol: SymbolId,
        name_text: &str,
        specifier: Node,
        dont_resolve_alias: bool,
    ) -> SymbolId {
        if self.sym(symbol).flags.intersects(SymbolFlags::MODULE) {
            let exports = self.get_exports_of_symbol(symbol);
            let export_symbol = self.symbols.get(exports, name_text);
            let resolved = self.resolve_symbol_ex(export_symbol, dont_resolve_alias);
            let export_star_declaration = self
                .module_symbol_links
                .get(symbol)
                .type_only_export_star_map
                .get(name_text)
                .copied()
                .unwrap_or(Node::NIL);
            self.mark_symbol_of_alias_declaration_if_type_only(specifier, export_star_declaration);
            return resolved;
        }
        SymbolId::NIL
    }

    // Go: checker/checker.go:14720 isOnlyImportableAsDefault
    pub fn is_only_importable_as_default(
        &mut self,
        usage: Node,
        mut resolved_module: SymbolId,
    ) -> bool {
        // In Node.js, JSON modules don't get named exports
        if ModuleKind::NODE16 <= self.module_kind && self.module_kind <= ModuleKind::NODE_NEXT {
            let usage_mode = self.get_emit_syntax_for_module_specifier_expression(usage);
            if usage_mode == ModuleKind::ES_NEXT {
                if resolved_module.is_nil() {
                    resolved_module =
                        self.resolve_external_module_name(usage, usage, true /*ignoreErrors*/);
                }
                let mut target_file = Node::NIL;
                if resolved_module.is_some() {
                    target_file = get_source_file_of_module(&self.symbols, resolved_module);
                }
                return target_file.is_some()
                    && (is_json_source_file(target_file)
                        || tspath_get_declaration_file_extension(source_file_file_name(
                            target_file,
                        )) == ".d.json.ts");
            }
        }
        false
    }

    // Go: checker/checker.go:14738 canHaveSyntheticDefault
    pub fn can_have_synthetic_default(
        &mut self,
        file: Node,
        module_symbol: SymbolId,
        dont_resolve_alias: bool,
        usage: Node,
    ) -> bool {
        let mut usage_mode: ResolutionMode = ModuleKind::NONE;
        if file.is_some() {
            usage_mode = self.get_emit_syntax_for_module_specifier_expression(usage);
        }
        if file.is_some() && usage_mode != ModuleKind::NONE {
            let target_mode = get_implied_node_format_for_emit(file);
            if usage_mode == ModuleKind::ES_NEXT
                && target_mode == ModuleKind::COMMON_JS
                && ModuleKind::NODE16 <= self.module_kind
                && self.module_kind <= ModuleKind::NODE_NEXT
            {
                // In Node.js, CommonJS modules always have a synthetic default when imported into ESM
                return true;
            }
            if usage_mode == ModuleKind::ES_NEXT && target_mode == ModuleKind::ES_NEXT {
                // No matter what the `module` setting is, if we're confident that both files
                // are ESM, there cannot be a synthetic default.
                return false;
            }
            // For other files (not node16/nodenext with impliedNodeFormat), check if we can determine
            // the module format from project references
            if target_mode == ModuleKind::NONE && source_file_info(file).is_declaration_file {
                // Try to get the project reference - try both source file mapping and output file mapping
                // since declaration files can be mapped either way depending on how they're resolved
                // PORT: Go `c.program.GetRedirectForResolution(file)` and
                // `c.program.GetProjectReferenceFromOutputDts(file.Path())` are
                // Program methods, ported as free functions returning `Option`.
                if get_redirect_for_resolution(file).is_some()
                    || get_project_reference_from_output_dts(&source_file_info(file).path).is_some()
                {
                    // This is a declaration file from a project reference, so we can determine
                    // its module format from the referenced project's options
                    let target_module_kind = get_emit_module_format_of_file(file);
                    if usage_mode == ModuleKind::ES_NEXT
                        && ModuleKind::ES2015 <= target_module_kind
                        && target_module_kind <= ModuleKind::ES_NEXT
                    {
                        return false;
                    }
                }
            }
        }
        // Declaration files (and ambient modules)
        if file.is_nil() || source_file_info(file).is_declaration_file {
            // Definitely cannot have a synthetic default if they have a syntactic default member specified
            // PORT: Go passes `(moduleSymbol, Default, nil /*sourceNode*/, true /*dontResolveAlias*/)`
            // (its inline comments are misplaced); ported literally.
            let default_export_symbol = self.resolve_export_by_name(
                module_symbol,
                INTERNAL_SYMBOL_NAME_DEFAULT,
                Node::NIL,
                true,
            ); // Dont resolve alias because we want the immediately exported symbol's declaration
            if default_export_symbol.is_some()
                && self
                    .sym(default_export_symbol)
                    .declarations
                    .iter()
                    .any(|&d| is_syntactic_default(d))
            {
                return false;
            }
            // It _might_ still be incorrect to assume there is no __esModule marker on the import at runtime, even if there is no `default` member
            // So we check a bit more,
            if self
                .resolve_export_by_name(
                    module_symbol,
                    "__esModule",
                    Node::NIL, /*sourceNode*/
                    dont_resolve_alias,
                )
                .is_some()
            {
                // If there is an `__esModule` specified in the declaration (meaning someone explicitly added it or wrote it in their code),
                // it definitely is a module and does not have a synthetic default
                return false;
            }
            // There are _many_ declaration files not written with esmodules in mind that still get compiled into a format with __esModule set
            // Meaning there may be no default at runtime - however to be on the permissive side, we allow access to a synthetic default member
            // as there is no marker to indicate if the accompanying JS has `__esModule` or not, or is even native esm
            return true;
        }
        // TypeScript files never have a synthetic default (as they are always emitted with an __esModule marker) _unless_ they contain an export= statement
        if !is_in_js_file(file) {
            return self.has_export_assignment_symbol(module_symbol);
        }

        // JS files have a synthetic default if they do not contain ES2015+ module syntax (export = is not valid in js) _and_ do not have an __esModule marker
        let external_module_indicator = source_file_info(file).external_module_indicator;
        (external_module_indicator.is_nil() || external_module_indicator == file)
            && self
                .resolve_export_by_name(
                    module_symbol,
                    "__esModule",
                    Node::NIL, /*sourceNode*/
                    dont_resolve_alias,
                )
                .is_nil()
    }

    // Go: checker/checker.go:14797 getEmitSyntaxForModuleSpecifierExpression
    pub fn get_emit_syntax_for_module_specifier_expression(
        &mut self,
        usage: Node,
    ) -> ResolutionMode {
        if is_string_literal_like(usage) {
            return get_emit_syntax_for_usage_location(get_source_file_of_node(usage), usage);
        }
        ModuleKind::NONE
    }

    // Go: checker/checker.go:14804 errorNoModuleMemberSymbol
    pub fn error_no_module_member_symbol(
        &mut self,
        module_symbol: SymbolId,
        target_symbol: SymbolId,
        node: Node,
        name: Node,
    ) {
        if self.compiler_options.no_check.is_true() {
            return;
        }
        let module_name = self.get_fully_qualified_name(module_symbol, node);
        let declaration_name = declaration_name_to_string(name);
        let mut suggestion = SymbolId::NIL;
        if is_identifier(name) {
            suggestion = self.get_suggested_symbol_for_nonexistent_module(name, target_symbol);
        }
        if suggestion.is_some() {
            let suggestion_name = self.symbol_to_string(suggestion);
            // PORT: Go adds related info to the diagnostic returned by
            // `c.error`. Build, annotate, then add (see the file comment).
            let mut diagnostic = new_diagnostic_for_node(
                name,
                diag::X_0_has_no_exported_member_named_1_Did_you_mean_2,
                args![module_name, declaration_name, suggestion_name],
            );
            let value_declaration = self.sym(suggestion).value_declaration;
            if value_declaration.is_some() {
                diagnostic.add_related_info(Some(create_diagnostic_for_node(
                    value_declaration,
                    diag::X_0_is_declared_here,
                    args![suggestion_name],
                )));
            }
            self.add_diagnostic(diagnostic);
        } else {
            let exports = self.sym(module_symbol).exports;
            if self
                .symbols
                .get(exports, INTERNAL_SYMBOL_NAME_DEFAULT)
                .is_some()
            {
                self.error(
                    name,
                    diag::Module_0_has_no_exported_member_1_Did_you_mean_to_use_import_1_from_0_instead,
                    args![module_name, declaration_name],
                );
            } else {
                self.report_non_exported_member(
                    name,
                    &declaration_name,
                    module_symbol,
                    &module_name,
                );
            }
        }
    }
}

// PORT: Go `tspath.GetDeclarationFileExtension`. The tspath package is not
// ported as a shared module (options.rs keeps a private copy), so this file
// keeps its own private copy with the same logic.
// Go: tspath/extension.go:111 GetDeclarationFileExtension
fn tspath_get_declaration_file_extension(file_name: &str) -> String {
    let base = tspath_get_base_file_name(file_name);
    // Go: tspath.SupportedDeclarationExtensions
    for ext in [".d.ts", ".d.cts", ".d.mts"] {
        if base.ends_with(ext) {
            return ext.to_string();
        }
    }
    if base.ends_with(".ts") {
        if let Some(index) = base.find(".d.") {
            return base[index..].to_string();
        }
    }
    String::new()
}

// PORT: Go `tspath.GetBaseFileName` for the absolute, normalized file names
// the program stores: the text after the last `/`, ignoring a trailing `/`.
fn tspath_get_base_file_name(path: &str) -> &str {
    let trimmed = path.strip_suffix('/').unwrap_or(path);
    match trimmed.rfind('/') {
        Some(i) => &trimmed[i + 1..],
        None => trimmed,
    }
}
