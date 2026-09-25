//! Port of `transformers/declarations/tracker.go`.

use std::cell::Cell;

use super::diagnostics::{
    create_diagnostic_for_node, create_get_isolated_declaration_errors, GetIsolatedDeclarationError,
    GetSymbolAccessibilityDiagnostic,
};
use super::DeclarationEmitHost;
use crate::checker::nodebuilder_types::SymbolTracker;
use crate::checker::Checker;
use crate::prelude::*;
use crate::printer::{EmitResolver, SymbolAccessibility, SymbolAccessibilityResult};

// Go: transformers/declarations/tracker.go:12 SymbolTrackerImpl
// PORT: the checker `SymbolTracker` trait takes `&self`, so the fields that Go
// changes in place are `Cell`/`RefCell`. The name shadows the checker's own
// `SymbolTrackerImpl` from the prelude glob; this module means this one.
pub struct SymbolTrackerImpl {
    resolver: Rc<dyn EmitResolver>,
    pub(crate) state: Rc<RefCell<SymbolTrackerSharedState>>,
    #[allow(dead_code)] // Go stores the host but no tracker method reads it.
    host: Rc<dyn DeclarationEmitHost>,
    fallback_stack: RefCell<Vec<Node>>,

    // For detecting class expression self-references during member serialization.
    // When set, TrackSymbol will record usage without reporting accessibility errors.
    pub(crate) watched_class_symbol: Cell<SymbolId>,
    pub(crate) class_symbol_tracked: Cell<bool>,

    get_isolated_declaration_error: GetIsolatedDeclarationError,
}

impl SymbolTrackerImpl {
    // Go: transformers/declarations/tracker.go:27 SymbolTrackerImpl.PopErrorFallbackNode
    // PORT: the trait method needs a checker. The transformer pushes and pops
    // outside of any checker call, so the body is here and the trait forwards.
    pub fn pop_error_fallback_node(&self) {
        self.fallback_stack.borrow_mut().pop().expect("slice bounds out of range");
    }

    // Go: transformers/declarations/tracker.go:32 SymbolTrackerImpl.PushErrorFallbackNode
    pub fn push_error_fallback_node(&self, node: Node) {
        self.fallback_stack.borrow_mut().push(node);
    }

    fn add_diagnostic(&self, diag: Diagnostic) {
        self.state.borrow_mut().add_diagnostic(diag);
    }

    // Go: transformers/declarations/tracker.go:129 SymbolTrackerImpl.errorFallbackNode
    fn error_fallback_node(&self) -> Node {
        self.fallback_stack.borrow().last().copied().unwrap_or(Node::NIL)
    }

    // Go: transformers/declarations/tracker.go:136 SymbolTrackerImpl.errorLocation
    fn error_location(&self) -> Node {
        let mut location = self.state.borrow().error_name_node;
        if location.is_nil() {
            location = self.error_fallback_node();
        }
        location
    }

    // Go: transformers/declarations/tracker.go:144 SymbolTrackerImpl.errorDeclarationNameWithFallback
    fn error_declaration_name_with_fallback(&self) -> String {
        let error_name_node = self.state.borrow().error_name_node;
        if error_name_node.is_some() {
            return declaration_name_to_string(error_name_node);
        }
        let fallback = self.error_fallback_node();
        if fallback.is_some() && get_name_of_declaration(fallback).is_some() {
            return declaration_name_to_string(get_name_of_declaration(fallback));
        }
        if fallback.is_some() && is_export_assignment(fallback) {
            if fallback.is_export_equals() {
                return "export=".to_string();
            }
            return "default".to_string();
        }
        "(Missing)".to_string() // same fallback declarationNameToString uses when node is zero-width (ie, nameless)
    }

    // Go: transformers/declarations/tracker.go:176 SymbolTrackerImpl.handleSymbolAccessibilityError
    fn handle_symbol_accessibility_error(&self, symbol_accessibility_result: SymbolAccessibilityResult) -> bool {
        if symbol_accessibility_result.accessibility == SymbolAccessibility::ACCESSIBLE {
            // Add aliases back onto the possible imports list if they're not there so we can try them again with updated visibility info
            if !symbol_accessibility_result.aliases_to_make_visible.is_empty() {
                let mut state = self.state.borrow_mut();
                for &r#ref in &symbol_accessibility_result.aliases_to_make_visible {
                    if !state.late_marked_statements.contains(&r#ref) {
                        state.late_marked_statements.push(r#ref);
                    }
                }
            }
            // TODO: Do all these accessibility checks inside/after the first pass in the checker when declarations are enabled, if possible

            // The checker should issue errors on unresolvable names, skip the declaration emit error for using a private/unreachable name for those
        } else if symbol_accessibility_result.accessibility != SymbolAccessibility::NOT_RESOLVED {
            // Report error
            // PORT: clone the func value out so the state is not borrowed while it runs.
            let get_diagnostic = self
                .state
                .borrow()
                .get_symbol_accessibility_diagnostic
                .clone()
                .expect("nil getSymbolAccessibilityDiagnostic");
            if let Some(info) = get_diagnostic(&symbol_accessibility_result) {
                let mut diag_node = symbol_accessibility_result.error_node;
                if diag_node.is_nil() {
                    diag_node = info.error_node;
                }
                if info.type_name.is_some() {
                    self.add_diagnostic(create_diagnostic_for_node(
                        diag_node,
                        info.diagnostic_message,
                        args![
                            get_text_of_node(info.type_name),
                            symbol_accessibility_result.error_symbol_name,
                            symbol_accessibility_result.error_module_name
                        ],
                    ));
                } else {
                    self.add_diagnostic(create_diagnostic_for_node(
                        diag_node,
                        info.diagnostic_message,
                        args![symbol_accessibility_result.error_symbol_name, symbol_accessibility_result.error_module_name],
                    ));
                }
                return true;
            }
        }
        false
    }
}

impl SymbolTracker for SymbolTrackerImpl {
    // Go: transformers/declarations/tracker.go:27 SymbolTrackerImpl.PopErrorFallbackNode
    fn pop_error_fallback_node(&self, _c: &mut Checker) {
        SymbolTrackerImpl::pop_error_fallback_node(self);
    }

    // Go: transformers/declarations/tracker.go:32 SymbolTrackerImpl.PushErrorFallbackNode
    fn push_error_fallback_node(&self, _c: &mut Checker, node: Node) {
        SymbolTrackerImpl::push_error_fallback_node(self, node);
    }

    // Go: transformers/declarations/tracker.go:37 SymbolTrackerImpl.ReportCyclicStructureError
    fn report_cyclic_structure_error(&self, _c: &mut Checker) {
        let location = self.error_location();
        if location.is_some() {
            self.add_diagnostic(create_diagnostic_for_node(
                location,
                diag::The_inferred_type_of_0_references_a_type_with_a_cyclic_structure_which_cannot_be_trivially_serialized_A_type_annotation_is_necessary,
                args![self.error_declaration_name_with_fallback()],
            ));
        }
    }

    // Go: transformers/declarations/tracker.go:45 SymbolTrackerImpl.ReportInaccessibleThisError
    fn report_inaccessible_this_error(&self, _c: &mut Checker) {
        let location = self.error_location();
        if location.is_some() {
            self.add_diagnostic(create_diagnostic_for_node(
                location,
                diag::The_inferred_type_of_0_references_an_inaccessible_1_type_A_type_annotation_is_necessary,
                args![self.error_declaration_name_with_fallback(), "this"],
            ));
        }
    }

    // Go: transformers/declarations/tracker.go:53 SymbolTrackerImpl.ReportInaccessibleUniqueSymbolError
    fn report_inaccessible_unique_symbol_error(&self, _c: &mut Checker) {
        let location = self.error_location();
        if location.is_some() {
            self.add_diagnostic(create_diagnostic_for_node(
                location,
                diag::The_inferred_type_of_0_references_an_inaccessible_1_type_A_type_annotation_is_necessary,
                args![self.error_declaration_name_with_fallback(), "unique symbol"],
            ));
        }
    }

    // Go: transformers/declarations/tracker.go:61 SymbolTrackerImpl.ReportInferenceFallback
    fn report_inference_fallback(&self, c: &mut Checker, node: Node) {
        let (isolated_declarations, current_source_file) = {
            let state = self.state.borrow();
            (state.isolated_declarations, state.current_source_file)
        };
        if !isolated_declarations {
            return;
        }
        if get_source_file_of_node(node) != current_source_file {
            return; // Nested error on a declaration in another file - ignore, will be reemitted if file is in the output file set
        }
        if self.resolver.is_expando_function_declaration_unsafe(node) {
            // within a node builder call that should already lock the checker, use the unsafe call
            // PORT: Go `p.ValueDeclaration` on checker symbols; read through the checker in hand.
            SymbolTrackerSharedState::report_expando_function_errors(&self.state, node, &|p| c.sym(p).value_declaration);
        }
        self.add_diagnostic((self.get_isolated_declaration_error)(node));
    }

    // Go: transformers/declarations/tracker.go:75 SymbolTrackerImpl.ReportLikelyUnsafeImportRequiredError
    fn report_likely_unsafe_import_required_error(&self, _c: &mut Checker, specifier: &str, symbol_name: &str) {
        let location = self.error_location();
        if location.is_some() {
            if !symbol_name.is_empty() {
                self.add_diagnostic(create_diagnostic_for_node(
                    location,
                    diag::The_inferred_type_of_0_cannot_be_named_without_a_reference_to_2_from_1_This_is_likely_not_portable_A_type_annotation_is_necessary,
                    args![self.error_declaration_name_with_fallback(), specifier, symbol_name],
                ));
            } else {
                self.add_diagnostic(create_diagnostic_for_node(
                    location,
                    diag::The_inferred_type_of_0_cannot_be_named_without_a_reference_to_1_This_is_likely_not_portable_A_type_annotation_is_necessary,
                    args![self.error_declaration_name_with_fallback(), specifier],
                ));
            }
        }
    }

    // Go: transformers/declarations/tracker.go:87 SymbolTrackerImpl.ReportNonSerializableProperty
    fn report_non_serializable_property(&self, _c: &mut Checker, property_name: &str) {
        let location = self.error_location();
        if location.is_some() {
            self.add_diagnostic(create_diagnostic_for_node(
                location,
                diag::The_type_of_this_node_cannot_be_serialized_because_its_property_0_cannot_be_serialized,
                args![property_name],
            ));
        }
    }

    // Go: transformers/declarations/tracker.go:95 SymbolTrackerImpl.ReportNonlocalAugmentation
    fn report_nonlocal_augmentation(
        &self,
        c: &mut Checker,
        containing_file: Node,
        parent_symbol: SymbolId,
        augmenting_symbol: SymbolId,
    ) {
        let primary_declaration = c
            .sym(parent_symbol)
            .declarations
            .iter()
            .copied()
            .find(|&d| get_source_file_of_node(d) == containing_file)
            .unwrap_or(Node::NIL);
        let augmenting_declarations: Vec<Node> = c
            .sym(augmenting_symbol)
            .declarations
            .iter()
            .copied()
            .filter(|&d| get_source_file_of_node(d) != containing_file)
            .collect();
        if primary_declaration.is_some() && !augmenting_declarations.is_empty() {
            for augmentations in augmenting_declarations {
                let mut diag = create_diagnostic_for_node(
                    augmentations,
                    diag::Declaration_augments_declaration_in_another_file_This_cannot_be_serialized,
                    args![],
                );
                let related = create_diagnostic_for_node(
                    primary_declaration,
                    diag::This_is_the_declaration_being_augmented_Consider_moving_the_augmenting_declaration_into_the_same_file,
                    args![],
                );
                diag.add_related_info(Some(related));
                self.add_diagnostic(diag);
            }
        }
    }

    // Go: transformers/declarations/tracker.go:109 SymbolTrackerImpl.ReportPrivateInBaseOfClassExpression
    fn report_private_in_base_of_class_expression(&self, _c: &mut Checker, property_name: &str) {
        let location = self.error_location();
        if location.is_some() {
            let mut diag = create_diagnostic_for_node(
                location,
                diag::Property_0_of_exported_anonymous_class_type_may_not_be_private_or_protected,
                args![property_name],
            );
            if is_variable_declaration(location.parent()) {
                let related = create_diagnostic_for_node(
                    location,
                    diag::Add_a_type_annotation_to_the_variable_0,
                    args![self.error_declaration_name_with_fallback()],
                );
                diag.add_related_info(Some(related));
            }
            self.add_diagnostic(diag);
        }
    }

    // Go: transformers/declarations/tracker.go:122 SymbolTrackerImpl.ReportTruncationError
    fn report_truncation_error(&self, _c: &mut Checker) {
        let location = self.error_location();
        if location.is_some() {
            self.add_diagnostic(create_diagnostic_for_node(
                location,
                diag::The_inferred_type_of_this_node_exceeds_the_maximum_length_the_compiler_will_serialize_An_explicit_type_annotation_is_needed,
                args![],
            ));
        }
    }

    // Go: transformers/declarations/tracker.go:161 SymbolTrackerImpl.TrackSymbol
    fn track_symbol(&self, c: &mut Checker, symbol: SymbolId, enclosing_declaration: Node, meaning: SymbolFlags) -> bool {
        if c.sym(symbol).flags.intersects(SymbolFlags::TYPE_PARAMETER) {
            return false;
        }
        // When watching for a class expression symbol, record its usage without
        // reporting accessibility errors — the caller will handle visibility by
        // wrapping the class in a namespace.
        let watched = self.watched_class_symbol.get();
        if watched != SymbolId::NIL && symbol == watched {
            self.class_symbol_tracked.set(true);
            return false;
        }
        // PORT: Go calls `s.resolver.IsSymbolAccessible`, which forwards to the
        // checker without a lock. The checker is already borrowed here, so call it directly.
        let result = c.is_symbol_accessible(symbol, enclosing_declaration, meaning, true /*shouldComputeAliasToMarkVisible*/);
        self.handle_symbol_accessibility_error(result)
    }
}

// Go: transformers/declarations/tracker.go:211 SymbolTrackerSharedState
pub struct SymbolTrackerSharedState {
    pub(crate) late_marked_statements: Vec<Node>,
    pub(crate) diagnostics: Vec<Diagnostic>,
    /// `None` is Go nil.
    pub(crate) get_symbol_accessibility_diagnostic: Option<GetSymbolAccessibilityDiagnostic>,
    pub(crate) error_name_node: Node,
    pub(crate) isolated_declarations: bool,
    pub(crate) strip_internal: bool,
    pub(crate) current_source_file: Node,
    pub(crate) resolver: Rc<dyn EmitResolver>,
    // PORT: Go field `reportExpandoFunctionErrors func(node)` is set by
    // NewDeclarationTransformer. It only reads this state and the resolver, so
    // it is the associated fn `report_expando_function_errors` below.
}

impl SymbolTrackerSharedState {
    // Go: transformers/declarations/tracker.go:223 SymbolTrackerSharedState.addDiagnostic
    pub(crate) fn add_diagnostic(&mut self, diag: Diagnostic) {
        self.diagnostics.push(diag);
    }

    // Go: transformers/declarations/transform.go:116 NewDeclarationTransformer.func1 (reportExpandoFunctionErrors)
    // PORT: `value_declaration` reads `p.ValueDeclaration`. The symbols come
    // from the checker arena, so the caller supplies the lookup. The resolver
    // is cloned out so the state is not borrowed during the resolver call.
    pub(crate) fn report_expando_function_errors(
        state: &Rc<RefCell<SymbolTrackerSharedState>>,
        node: Node,
        value_declaration: &dyn Fn(SymbolId) -> Node,
    ) {
        let (isolated_declarations, resolver) = {
            let s = state.borrow();
            (s.isolated_declarations, s.resolver.clone())
        };
        if !isolated_declarations {
            return;
        }
        let props = resolver.get_properties_of_container_function(node);
        for p in props {
            let p_value_declaration = value_declaration(p);
            if is_expando_property_declaration(p_value_declaration) {
                let mut error_target = p_value_declaration;
                if is_binary_expression(error_target) {
                    error_target = error_target.left();
                }
                state.borrow_mut().add_diagnostic(create_diagnostic_for_node(
                    error_target,
                    diag::Assigning_properties_to_functions_without_declaring_them_is_not_supported_with_isolatedDeclarations_Add_an_explicit_declaration_for_the_properties_assigned_to_this_function,
                    args![],
                ));
            }
        }
    }
}

// Go: transformers/declarations/tracker.go:227 NewSymbolTracker
pub fn new_symbol_tracker(
    host: Rc<dyn DeclarationEmitHost>,
    resolver: Rc<dyn EmitResolver>,
    state: Rc<RefCell<SymbolTrackerSharedState>>,
) -> SymbolTrackerImpl {
    SymbolTrackerImpl {
        host,
        get_isolated_declaration_error: create_get_isolated_declaration_errors(resolver.clone()),
        resolver,
        state,
        fallback_stack: RefCell::new(Vec::new()),
        watched_class_symbol: Cell::new(SymbolId::NIL),
        class_symbol_tracked: Cell::new(false),
    }
}
