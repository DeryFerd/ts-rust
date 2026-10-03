//! Port of Go `transformers/destructuring.go`.
//!
//! PORT: Go passes `tx *Transformer` for its emit context, factory and root
//! visitor. Here the caller passes the emit context and its root visitor
//! (`&mut NodeVisitor<'a, C>`, usually from `TransformerVisit::with_visitor`).
//! Go `f.tx.Visitor().VisitNode(n)` is `v.visit_node(n)`. A Go
//! `CreateAssignmentCallback` closes over its transformer; here it gets the
//! visitor, so it reaches the transformer through `v.ctx`.

use crate::prelude::*;

use super::utilities::{is_simple_copiable_expression, is_simple_inlineable_expression};
use crate::ast::visitor::NodeVisitor;

// Go: transformers/destructuring.go:12 FlattenLevel
// FlattenLevel controls how deeply binding/assignment patterns are decomposed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FlattenLevel {
    /// Fully decompose all patterns into individual assignments/bindings
    All,
    /// Only decompose patterns containing object rest elements
    ObjectRest,
}

// Go: transformers/destructuring.go:22 CreateAssignmentCallback
/// CreateAssignmentCallback is a callback used to create custom assignment expressions during destructuring flattening.
/// When provided, the target will always be an Identifier, and the callback can wrap the assignment with additional logic
/// (e.g., export expressions in CJS modules or namespace member assignments).
// PORT: Go `location *core.TextRange` is `Option<TextRange>`.
pub type CreateAssignmentCallback<'f, 'a, C> =
    &'f mut dyn FnMut(&mut NodeVisitor<'a, C>, Node, Node, Option<TextRange>) -> Node;

// Go: transformers/destructuring.go:27 FlattenDestructuringAssignment
/// FlattenDestructuringAssignment flattens a destructuring assignment expression into a sequence of
/// individual property/element access assignments. Supports custom assignment callbacks for module
/// export or namespace member expressions.
pub fn flatten_destructuring_assignment<'a, C>(
    emit_context: &EmitContext,
    v: &mut NodeVisitor<'a, C>,
    node: Node, // VariableDeclaration | DestructuringAssignment
    needs_value: bool,
    level: FlattenLevel,
    create_assignment_callback: Option<CreateAssignmentCallback<'_, 'a, C>>,
) -> Node {
    let mut f = new_flattener(emit_context, level, Mode::Assignment);
    f.create_assignment_callback = create_assignment_callback;
    f.hoist_temp_variables = true;
    f.flatten_destructuring_assignment(v, node, needs_value)
}

// Go: transformers/destructuring.go:46 pendingDecl
// pendingDecl tracks a pending variable declaration during binding flattening.
struct PendingDecl {
    pending_expressions: Vec<Node>,
    name: Node,
    value: Node,
    location: TextRange,
    original: Node,
}

// Go: transformers/destructuring.go:57 FlattenDestructuringBinding
/// FlattenDestructuringBinding flattens a binding pattern in a variable declaration or parameter
/// into individual variable declarations. Returns a single VariableDeclaration, a SyntaxList of
/// declarations, or nil.
pub fn flatten_destructuring_binding<'a, C>(
    emit_context: &EmitContext,
    v: &mut NodeVisitor<'a, C>,
    node: Node, // VariableDeclaration | ParameterDeclaration | BindingElement
    rval: Node,
    level: FlattenLevel,
    hoist_temp_variables: bool,
    skip_initializer: bool,
) -> Node {
    let mut f = new_flattener(emit_context, level, Mode::Binding);
    f.hoist_temp_variables = hoist_temp_variables;
    f.flatten_destructuring_binding(v, node, rval, skip_initializer)
}

/// Go sets four mode callbacks on the flattener. They always come in one of
/// two sets, so the set is this enum.
// PORT: Go `emitBindingOrAssignment`, `createArrayBindingOrAssignmentPattern`,
// `createObjectBindingOrAssignmentPattern` and
// `createArrayBindingOrAssignmentElement` func fields dispatch on `mode`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Assignment,
    Binding,
}

// Go: transformers/destructuring.go:77 flattener
// flattener encapsulates the state and logic for flattening destructuring patterns.
// It is equivalent to TypeScript's FlattenContext in destructuring.ts.
struct Flattener<'e, 'f, 'a, C> {
    emit_context: &'e EmitContext,
    level: FlattenLevel,

    create_assignment_callback: Option<CreateAssignmentCallback<'f, 'a, C>>,

    // State
    expressions: Vec<Node>,
    declarations: Vec<PendingDecl>,
    has_transformed_prior_element: bool,
    hoist_temp_variables: bool,

    mode: Mode,
}

// Go: transformers/destructuring.go:96 newFlattener
fn new_flattener<'e, 'f, 'a, C>(
    emit_context: &'e EmitContext,
    level: FlattenLevel,
    mode: Mode,
) -> Flattener<'e, 'f, 'a, C> {
    Flattener {
        emit_context,
        level,
        create_assignment_callback: None,
        expressions: Vec::new(),
        declarations: Vec::new(),
        has_transformed_prior_element: false,
        hoist_temp_variables: false,
        mode,
    }
}

impl<'a, C> Flattener<'_, '_, 'a, C> {
    fn factory(&self) -> &crate::printer::factory::NodeFactory {
        self.emit_context.factory()
    }

    /// Go `f.emitBindingOrAssignment(f, ...)`.
    fn emit_binding_or_assignment(
        &mut self,
        v: &mut NodeVisitor<'a, C>,
        target: Node,
        value: Node,
        location: TextRange,
        original: Node,
    ) {
        match self.mode {
            Mode::Assignment => self.emit_assignment(v, target, value, location, original),
            Mode::Binding => self.emit_binding(target, value, location, original),
        }
    }

    /// Go `f.createArrayBindingOrAssignmentPattern(f, elements)`.
    fn create_array_binding_or_assignment_pattern(&self, elements: &[Node]) -> Node {
        match self.mode {
            Mode::Assignment => self.create_array_assignment_pattern(elements),
            Mode::Binding => self.create_array_binding_pattern(elements),
        }
    }

    /// Go `f.createObjectBindingOrAssignmentPattern(f, elements)`.
    fn create_object_binding_or_assignment_pattern(&self, elements: &[Node]) -> Node {
        match self.mode {
            Mode::Assignment => self.create_object_assignment_pattern(elements),
            Mode::Binding => self.create_object_binding_pattern(elements),
        }
    }

    /// Go `f.createArrayBindingOrAssignmentElement(f, expr)`.
    fn create_array_binding_or_assignment_element(&self, expr: Node) -> Node {
        match self.mode {
            Mode::Assignment => self.create_array_assignment_element(expr),
            Mode::Binding => self.create_array_binding_element(expr),
        }
    }

    // --- Assignment mode callbacks ---

    // Go: transformers/destructuring.go:105 flattener.createArrayAssignmentPattern
    fn create_array_assignment_pattern(&self, elements: &[Node]) -> Node {
        let f = self.factory();
        f.new_array_literal_expression(f.new_node_list(elements), false)
    }

    // Go: transformers/destructuring.go:109 flattener.createObjectAssignmentPattern
    fn create_object_assignment_pattern(&self, elements: &[Node]) -> Node {
        let f = self.factory();
        f.new_object_literal_expression(f.new_node_list(elements), false)
    }

    // Go: transformers/destructuring.go:113 flattener.createArrayAssignmentElement
    fn create_array_assignment_element(&self, expr: Node) -> Node {
        expr
    }

    // Go: transformers/destructuring.go:117 flattener.emitAssignment
    fn emit_assignment(
        &mut self,
        v: &mut NodeVisitor<'a, C>,
        target: Node,
        value: Node,
        location: TextRange,
        original: Node,
    ) {
        let expression;
        if self.create_assignment_callback.is_some() && is_identifier(target) {
            let callback = self
                .create_assignment_callback
                .as_mut()
                .expect("create assignment callback");
            expression = callback(v, target, value, Some(location));
        } else {
            let target = v.visit_node(target);
            expression = self.factory().new_assignment_expression(target, value);
            set_node_loc(expression, location);
        }
        self.emit_context.set_original(expression, original);
        self.emit_expression(expression);
    }

    // --- Binding mode callbacks ---

    // Go: transformers/destructuring.go:131 flattener.createArrayBindingPattern
    fn create_array_binding_pattern(&self, elements: &[Node]) -> Node {
        let f = self.factory();
        f.new_binding_pattern(SyntaxKind::ArrayBindingPattern, f.new_node_list(elements))
    }

    // Go: transformers/destructuring.go:135 flattener.createObjectBindingPattern
    fn create_object_binding_pattern(&self, elements: &[Node]) -> Node {
        let f = self.factory();
        f.new_binding_pattern(SyntaxKind::ObjectBindingPattern, f.new_node_list(elements))
    }

    // Go: transformers/destructuring.go:139 flattener.createArrayBindingElement
    fn create_array_binding_element(&self, expr: Node) -> Node {
        self.factory()
            .new_binding_element(Node::NIL, Node::NIL, expr, Node::NIL)
    }

    // Go: transformers/destructuring.go:143 flattener.emitBinding
    fn emit_binding(&mut self, target: Node, mut value: Node, location: TextRange, original: Node) {
        if !self.expressions.is_empty() {
            let mut expressions = std::mem::take(&mut self.expressions);
            expressions.push(value);
            value = self.factory().inline_expressions(&expressions);
        }
        self.declarations.push(PendingDecl {
            pending_expressions: Vec::new(),
            name: target,
            value,
            location,
            original,
        });
    }

    // --- Shared helpers ---

    // Go: transformers/destructuring.go:158 flattener.emitExpression
    fn emit_expression(&mut self, expr: Node) {
        self.expressions.push(expr);
    }

    // Go: transformers/destructuring.go:162 flattener.ensureIdentifier
    fn ensure_identifier(
        &mut self,
        v: &mut NodeVisitor<'a, C>,
        value: Node,
        reuse_identifier_expressions: bool,
        location: TextRange,
    ) -> Node {
        if reuse_identifier_expressions && is_identifier(value) {
            return value;
        }
        let temp = self.factory().new_temp_variable();
        if self.hoist_temp_variables {
            self.emit_context.add_variable_declaration(temp);
            let assign = self.factory().new_assignment_expression(temp, value);
            set_node_loc(assign, location);
            self.emit_expression(assign);
        } else {
            self.emit_binding_or_assignment(v, temp, value, location, Node::NIL);
        }
        temp
    }

    // Go: transformers/destructuring.go:178 flattener.createDefaultValueCheck
    fn create_default_value_check(
        &mut self,
        v: &mut NodeVisitor<'a, C>,
        value: Node,
        default_value: Node,
        location: TextRange,
    ) -> Node {
        let value = self.ensure_identifier(v, value, true, location);
        let f = self.factory();
        f.new_conditional_expression(
            f.new_type_check(value, "undefined"),
            f.new_token(SyntaxKind::QuestionToken),
            default_value,
            f.new_token(SyntaxKind::ColonToken),
            value,
        )
    }

    // Go: transformers/destructuring.go:189 flattener.createDestructuringPropertyAccess
    fn create_destructuring_property_access(
        &mut self,
        v: &mut NodeVisitor<'a, C>,
        value: Node,
        property_name: Node,
    ) -> Node {
        if is_computed_property_name(property_name) {
            let visited = v.visit_node(property_name.expression());
            let argument_expression =
                self.ensure_identifier(v, visited, false, property_name.loc());
            self.factory().new_element_access_expression(
                value,
                Node::NIL,
                argument_expression,
                NodeFlags::NONE,
            )
        } else if is_string_or_numeric_literal_like(property_name)
            || is_big_int_literal(property_name)
        {
            let argument_expression = self.factory().clone_node(property_name);
            self.factory().new_element_access_expression(
                value,
                Node::NIL,
                argument_expression,
                NodeFlags::NONE,
            )
        } else {
            let name = self.factory().new_identifier(property_name.text());
            self.factory()
                .new_property_access_expression(value, Node::NIL, name, NodeFlags::NONE)
        }
    }

    // --- Entry points ---

    // Go: transformers/destructuring.go:204 flattener.flattenDestructuringAssignment
    fn flatten_destructuring_assignment(
        &mut self,
        v: &mut NodeVisitor<'a, C>,
        mut node: Node,
        needs_value: bool,
    ) -> Node {
        let mut location = node.loc();
        let mut value = Node::NIL;
        if is_destructuring_assignment(node) {
            value = node.right();
            while is_empty_array_literal(node.left()) || is_empty_object_literal(node.left()) {
                if is_destructuring_assignment(value) {
                    node = value;
                    location = node.loc();
                    value = node.right();
                } else {
                    return v.visit_node(value);
                }
            }
        }

        if value.is_some() {
            value = v.visit_node(value);
            if is_identifier(value)
                && binding_or_assignment_element_assigns_to_name(node, value.text())
                || binding_or_assignment_element_contains_non_literal_computed_name(node)
            {
                value = self.ensure_identifier(v, value, false, location);
            } else if needs_value {
                value = self.ensure_identifier(v, value, true, location);
            } else if node_is_synthesized(node) {
                location = value.loc();
            }
        }

        self.flatten_binding_or_assignment_element(
            v,
            node,
            value,
            location,
            is_destructuring_assignment(node),
        );

        if value.is_some() && needs_value {
            if self.expressions.is_empty() {
                return value;
            }
            self.expressions.push(value);
        }

        let res = self.factory().inline_expressions(&self.expressions);
        if res.is_some() {
            return res;
        }
        self.factory().new_omitted_expression()
    }

    // Go: transformers/destructuring.go:247 flattener.flattenDestructuringBinding
    fn flatten_destructuring_binding(
        &mut self,
        v: &mut NodeVisitor<'a, C>,
        mut node: Node,
        rval: Node,
        skip_initializer: bool,
    ) -> Node {
        if is_variable_declaration(node) {
            let mut initializer = get_initializer_of_binding_or_assignment_element(node);
            if initializer.is_some()
                && (is_identifier(initializer)
                    && binding_or_assignment_element_assigns_to_name(node, initializer.text())
                    || binding_or_assignment_element_contains_non_literal_computed_name(node))
            {
                let visited = v.visit_node(initializer);
                initializer = self.ensure_identifier(v, visited, false, initializer.loc());
                node = self.factory().update_variable_declaration(
                    node,
                    node.name(),
                    Node::NIL,
                    Node::NIL,
                    initializer,
                );
            }
        }

        self.flatten_binding_or_assignment_element(v, node, rval, node.loc(), skip_initializer);

        if !self.expressions.is_empty() {
            let temp = self.factory().new_temp_variable();
            if self.hoist_temp_variables {
                let expressions = std::mem::take(&mut self.expressions);
                let value = self.factory().inline_expressions(&expressions);
                self.emit_binding_or_assignment(v, temp, value, TextRange::default(), Node::NIL);
            } else {
                self.emit_context.add_variable_declaration(temp);
                let last_value = self
                    .declarations
                    .last()
                    .expect("flattenDestructuringBinding: no declarations")
                    .value;
                let assignment = self.factory().new_assignment_expression(temp, last_value);
                let expressions = self.expressions.clone();
                let last = self
                    .declarations
                    .last_mut()
                    .expect("flattenDestructuringBinding: no declarations");
                last.pending_expressions.push(assignment);
                last.pending_expressions.extend(expressions);
                last.value = temp;
            }
        }

        let mut decls: Vec<Node> = Vec::with_capacity(self.declarations.len());
        for pending in &self.declarations {
            let mut expr = pending.value;
            if !pending.pending_expressions.is_empty() {
                let mut expressions = pending.pending_expressions.clone();
                expressions.push(pending.value);
                expr = self.factory().inline_expressions(&expressions);
            }
            let decl =
                self.factory()
                    .new_variable_declaration(pending.name, Node::NIL, Node::NIL, expr);
            set_node_loc(decl, pending.location);
            if pending.original.is_some() {
                self.emit_context.set_original(decl, pending.original);
            }
            decls.push(decl);
        }

        if decls.len() == 1 {
            return decls[0];
        }
        if decls.is_empty() {
            return Node::NIL;
        }
        self.factory().new_syntax_list(&decls)
    }

    // --- Core flattening ---

    // Go: transformers/destructuring.go:298 flattener.flattenBindingOrAssignmentElement
    fn flatten_binding_or_assignment_element(
        &mut self,
        v: &mut NodeVisitor<'a, C>,
        element: Node,
        mut value: Node,
        location: TextRange,
        skip_initializer: bool,
    ) {
        let binding_target = get_target_of_binding_or_assignment_element(element);
        if binding_target.is_nil() {
            return;
        }
        if !skip_initializer {
            let initializer =
                v.visit_node(get_initializer_of_binding_or_assignment_element(element));
            if initializer.is_some() {
                if value.is_some() {
                    value = self.create_default_value_check(v, value, initializer, location);
                    if !is_simple_copiable_expression(initializer)
                        && (is_binding_pattern(binding_target)
                            || is_assignment_pattern(binding_target))
                    {
                        value = self.ensure_identifier(v, value, true, location);
                    }
                } else {
                    value = initializer;
                }
            } else if value.is_nil() {
                value = self.factory().new_void_zero_expression();
            }
        }

        if is_object_binding_or_assignment_pattern(binding_target) {
            self.flatten_object_binding_or_assignment_pattern(
                v,
                element,
                binding_target,
                value,
                location,
            );
        } else if is_array_binding_or_assignment_pattern(binding_target) {
            self.flatten_array_binding_or_assignment_pattern(
                v,
                element,
                binding_target,
                value,
                location,
            );
        } else {
            self.emit_binding_or_assignment(v, binding_target, value, location, element);
        }
    }

    // Go: transformers/destructuring.go:328 flattener.flattenObjectBindingOrAssignmentPattern
    fn flatten_object_binding_or_assignment_pattern(
        &mut self,
        v: &mut NodeVisitor<'a, C>,
        parent: Node,
        pattern: Node,
        mut value: Node,
        location: TextRange,
    ) {
        let elements = get_elements_of_binding_or_assignment_pattern(pattern);
        let num_elements = elements.len();
        if num_elements != 1 {
            let reuse_identifier_expressions =
                !is_declaration_binding_element(parent) || num_elements != 0;
            value = self.ensure_identifier(v, value, reuse_identifier_expressions, location);
        }
        let mut binding_elements: Vec<Node> = Vec::new();
        let mut computed_temp_variables: Vec<Node> = Vec::new();
        let rest_facts = SubtreeFacts::SUBTREE_CONTAINS_REST_OR_SPREAD
            | SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD;
        for (i, &element) in elements.iter().enumerate() {
            if get_rest_indicator_of_binding_or_assignment_element(element).is_nil() {
                let property_name = try_get_property_name_of_binding_or_assignment_element(element);
                if self.level >= FlattenLevel::ObjectRest
                    && !element.subtree_facts().intersects(rest_facts)
                    && !get_target_of_binding_or_assignment_element(element)
                        .subtree_facts()
                        .intersects(rest_facts)
                    && !is_computed_property_name(property_name)
                {
                    binding_elements.push(v.visit_node(element));
                } else {
                    if !binding_elements.is_empty() {
                        let pattern_node =
                            self.create_object_binding_or_assignment_pattern(&binding_elements);
                        self.emit_binding_or_assignment(v, pattern_node, value, location, pattern);
                        binding_elements.clear();
                    }
                    let rhs_value =
                        self.create_destructuring_property_access(v, value, property_name);
                    if is_computed_property_name(property_name) {
                        computed_temp_variables.push(rhs_value.argument_expression());
                    }
                    self.flatten_binding_or_assignment_element(
                        v,
                        element,
                        rhs_value,
                        element.loc(),
                        false,
                    );
                }
            } else if i == num_elements - 1 {
                if !binding_elements.is_empty() {
                    let pattern_node =
                        self.create_object_binding_or_assignment_pattern(&binding_elements);
                    self.emit_binding_or_assignment(v, pattern_node, value, location, pattern);
                    binding_elements.clear();
                }
                let computed = if computed_temp_variables.is_empty() {
                    None
                } else {
                    Some(computed_temp_variables.as_slice())
                };
                let rhs_value =
                    self.factory()
                        .new_rest_helper(value, &elements, computed, pattern.loc());
                self.flatten_binding_or_assignment_element(
                    v,
                    element,
                    rhs_value,
                    element.loc(),
                    false,
                );
            }
        }
        if !binding_elements.is_empty() {
            let pattern_node = self.create_object_binding_or_assignment_pattern(&binding_elements);
            self.emit_binding_or_assignment(v, pattern_node, value, location, pattern);
        }
    }

    // Go: transformers/destructuring.go:375 flattener.flattenArrayBindingOrAssignmentPattern
    fn flatten_array_binding_or_assignment_pattern(
        &mut self,
        v: &mut NodeVisitor<'a, C>,
        parent: Node,
        pattern: Node,
        mut value: Node,
        location: TextRange,
    ) {
        let elements = get_elements_of_binding_or_assignment_pattern(pattern);
        let num_elements = elements.len();
        if num_elements != 1 && (self.level < FlattenLevel::ObjectRest || num_elements == 0)
            || elements.iter().all(|&e| is_omitted_expression(e))
        {
            let reuse_identifier_expressions =
                !is_declaration_binding_element(parent) || num_elements != 0;
            value = self.ensure_identifier(v, value, reuse_identifier_expressions, location);
        }
        let mut binding_elements: Vec<Node> = Vec::new();
        // Go `restIdElemPair{id, element}`.
        let mut rest_containing_elements: Vec<(Node, Node)> = Vec::new();
        for (i, &element) in elements.iter().enumerate() {
            if self.level >= FlattenLevel::ObjectRest {
                if element
                    .subtree_facts()
                    .intersects(SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD)
                    || self.has_transformed_prior_element
                        && !is_simple_binding_or_assignment_element(element)
                {
                    self.has_transformed_prior_element = true;
                    let temp = self.factory().new_temp_variable();
                    if self.hoist_temp_variables {
                        self.emit_context.add_variable_declaration(temp);
                    }
                    rest_containing_elements.push((temp, element));
                    binding_elements.push(self.create_array_binding_or_assignment_element(temp));
                } else {
                    binding_elements.push(element);
                }
            } else if is_omitted_expression(element) {
                continue;
            } else if get_rest_indicator_of_binding_or_assignment_element(element).is_nil() {
                let f = self.factory();
                let rhs_value = f.new_element_access_expression(
                    value,
                    Node::NIL,
                    f.new_numeric_literal(i.to_string(), TokenFlags::NONE),
                    NodeFlags::NONE,
                );
                self.flatten_binding_or_assignment_element(
                    v,
                    element,
                    rhs_value,
                    element.loc(),
                    false,
                );
            } else if i == num_elements - 1 {
                let rhs_value = self.factory().new_array_slice_call(value, i as i32);
                self.flatten_binding_or_assignment_element(
                    v,
                    element,
                    rhs_value,
                    element.loc(),
                    false,
                );
            }
        }
        if !binding_elements.is_empty() {
            let pattern_node = self.create_array_binding_or_assignment_pattern(&binding_elements);
            self.emit_binding_or_assignment(v, pattern_node, value, location, pattern);
        }
        for (id, element) in rest_containing_elements {
            self.flatten_binding_or_assignment_element(v, element, id, element.loc(), false);
        }
    }
}

// --- Exported helper functions ---

// Go: transformers/destructuring.go:420 BindingOrAssignmentElementAssignsToName
// BindingOrAssignmentElementAssignsToName checks if any target in a binding/assignment pattern assigns to the given name.
pub fn binding_or_assignment_element_assigns_to_name(element: Node, name: &str) -> bool {
    let target = get_target_of_binding_or_assignment_element(element);
    if target.is_nil() {
        return false;
    }
    if is_binding_pattern(target) || is_assignment_pattern(target) {
        return binding_or_assignment_pattern_assigns_to_name(target, name);
    } else if is_identifier(target) {
        return target.text() == name;
    }
    false
}

// Go: transformers/destructuring.go:433 bindingOrAssignmentPatternAssignsToName
fn binding_or_assignment_pattern_assigns_to_name(pattern: Node, name: &str) -> bool {
    get_elements_of_binding_or_assignment_pattern(pattern)
        .into_iter()
        .any(|element| binding_or_assignment_element_assigns_to_name(element, name))
}

// Go: transformers/destructuring.go:444 BindingOrAssignmentElementContainsNonLiteralComputedName
// BindingOrAssignmentElementContainsNonLiteralComputedName checks if any element has a non-literal computed property name.
pub fn binding_or_assignment_element_contains_non_literal_computed_name(element: Node) -> bool {
    let property_name = try_get_property_name_of_binding_or_assignment_element(element);
    if property_name.is_some()
        && is_computed_property_name(property_name)
        && !is_literal_expression(property_name.expression())
    {
        return true;
    }
    let target = get_target_of_binding_or_assignment_element(element);
    target.is_some()
        && (is_binding_pattern(target) || is_assignment_pattern(target))
        && binding_or_assignment_pattern_contains_non_literal_computed_name(target)
}

// Go: transformers/destructuring.go:453 bindingOrAssignmentPatternContainsNonLiteralComputedName
fn binding_or_assignment_pattern_contains_non_literal_computed_name(pattern: Node) -> bool {
    get_elements_of_binding_or_assignment_pattern(pattern)
        .into_iter()
        .any(binding_or_assignment_element_contains_non_literal_computed_name)
}

// Go: transformers/destructuring.go:459 GetInitializerOfBindingOrAssignmentElement
// GetInitializerOfBindingOrAssignmentElement returns the initializer/default value of a binding or assignment element.
pub fn get_initializer_of_binding_or_assignment_element(binding_element: Node) -> Node {
    if binding_element.is_nil() {
        return Node::NIL;
    }
    if is_declaration_binding_element(binding_element) {
        return binding_element.initializer();
    }
    if is_property_assignment(binding_element) {
        let initializer = binding_element.initializer();
        if is_assignment_expression(initializer, true) {
            return initializer.right();
        }
        return Node::NIL;
    }
    if is_shorthand_property_assignment(binding_element) {
        return binding_element.object_assignment_initializer();
    }
    if is_assignment_expression(binding_element, true) {
        return binding_element.right();
    }
    if is_spread_element(binding_element) {
        return get_initializer_of_binding_or_assignment_element(binding_element.expression());
    }
    Node::NIL
}

// Go: transformers/destructuring.go:485 isObjectBindingOrAssignmentPattern
fn is_object_binding_or_assignment_pattern(node: Node) -> bool {
    node.is_some()
        && (node.kind() == SyntaxKind::ObjectBindingPattern
            || node.kind() == SyntaxKind::ObjectLiteralExpression)
}

// Go: transformers/destructuring.go:489 isArrayBindingOrAssignmentPattern
fn is_array_binding_or_assignment_pattern(node: Node) -> bool {
    node.is_some()
        && (node.kind() == SyntaxKind::ArrayBindingPattern
            || node.kind() == SyntaxKind::ArrayLiteralExpression)
}

// Go: transformers/destructuring.go:493 isSimpleBindingOrAssignmentElement
fn is_simple_binding_or_assignment_element(element: Node) -> bool {
    let target = get_target_of_binding_or_assignment_element(element);
    if target.is_nil() || is_omitted_expression(target) {
        return true;
    }
    let property_name = try_get_property_name_of_binding_or_assignment_element(element);
    if property_name.is_some() && !is_property_name_literal(property_name) {
        return false;
    }
    let initializer = get_initializer_of_binding_or_assignment_element(element);
    if initializer.is_some() && !is_simple_inlineable_expression(initializer) {
        return false;
    }
    if is_binding_pattern(target) || is_assignment_pattern(target) {
        return get_elements_of_binding_or_assignment_pattern(target)
            .into_iter()
            .all(is_simple_binding_or_assignment_element);
    }
    is_identifier(target)
}
