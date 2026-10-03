//! Port of Go `transformers/estransforms/namedevaluation.go`.

use super::class_this::is_class_this_assignment_block;
use crate::prelude::*;
use crate::printer::EmitContext;

// Go: transformers/estransforms/namedevaluation.go:16 isClassNamedEvaluationHelperBlock
/// Gets whether a node is a `static {}` block containing only a single call to the `__setFunctionName` helper where that
/// call's second argument is the value stored in the `assignedName` property of the block's `EmitNode`.
pub(crate) fn is_class_named_evaluation_helper_block(
    emit_context: &EmitContext,
    node: Node,
) -> bool {
    if !is_class_static_block_declaration(node) || node.body().statements().len() != 1 {
        return false;
    }

    let statement = node.body().statements().get(0);
    if is_expression_statement(statement) {
        let expression = statement.expression();
        if emit_context.is_call_to_helper(expression, "__setFunctionName") {
            let arguments = expression.arguments();
            return arguments.len() >= 2 && arguments.get(1) == emit_context.assigned_name(node);
        }
    }
    false
}

// Go: transformers/estransforms/namedevaluation.go:38 classHasExplicitlyAssignedName
/// Gets whether a `ClassLikeDeclaration` has a `static {}` block containing only a single call to the
/// `__setFunctionName` helper.
pub(crate) fn class_has_explicitly_assigned_name(emit_context: &EmitContext, node: Node) -> bool {
    let assigned_name = emit_context.assigned_name(node);
    if assigned_name.is_some() {
        for member in node.members().iter() {
            if is_class_named_evaluation_helper_block(emit_context, member) {
                return true;
            }
        }
    }
    false
}

// Go: transformers/estransforms/namedevaluation.go:54 classHasDeclaredOrExplicitlyAssignedName
/// Gets whether a `ClassLikeDeclaration` has a declared name or contains a `static {}` block containing only a single
/// call to the `__setFunctionName` helper.
pub(crate) fn class_has_declared_or_explicitly_assigned_name(
    emit_context: &EmitContext,
    node: Node,
) -> bool {
    node.name().is_some() || class_has_explicitly_assigned_name(emit_context, node)
}

/// Go `func(*anonymousFunctionDefinition) bool`.
pub(crate) type AnonymousFunctionDefinitionCallback<'a> = &'a mut dyn FnMut(Node) -> bool;

// Go: transformers/estransforms/namedevaluation.go:63 isAnonymousFunctionDefinition
/// Indicates whether an expression is an anonymous function definition.
///
/// See https://tc39.es/ecma262/#sec-isanonymousfunctiondefinition
pub(crate) fn is_anonymous_function_definition(
    emit_context: &EmitContext,
    node: Node,
    cb: Option<AnonymousFunctionDefinitionCallback<'_>>,
) -> bool {
    let node = skip_outer_expressions(node, OuterExpressionKinds::OEK_ALL);
    match node.kind() {
        SyntaxKind::ClassExpression => {
            if class_has_declared_or_explicitly_assigned_name(emit_context, node) {
                return false;
            }
        }
        SyntaxKind::FunctionExpression => {
            if node.name().is_some() {
                return false;
            }
        }
        SyntaxKind::ArrowFunction => {
            // arrow functions are always anonymous
        }
        _ => return false,
    }
    if let Some(cb) = cb {
        return cb(node);
    }
    true
}

// Go: transformers/estransforms/namedevaluation.go:85 isNamedEvaluation
pub(crate) fn is_named_evaluation(emit_context: &EmitContext, node: Node) -> bool {
    is_named_evaluation_and(emit_context, node, None)
}

// Go: transformers/estransforms/namedevaluation.go:89 isNamedEvaluationAnd
pub(crate) fn is_named_evaluation_and(
    emit_context: &EmitContext,
    node: Node,
    cb: Option<AnonymousFunctionDefinitionCallback<'_>>,
) -> bool {
    if !is_named_evaluation_source(node) {
        return false;
    }
    match node.kind() {
        SyntaxKind::ShorthandPropertyAssignment => {
            is_anonymous_function_definition(emit_context, node.object_assignment_initializer(), cb)
        }
        SyntaxKind::PropertyAssignment
        | SyntaxKind::VariableDeclaration
        | SyntaxKind::Parameter
        | SyntaxKind::BindingElement
        | SyntaxKind::PropertyDeclaration => {
            is_anonymous_function_definition(emit_context, node.initializer(), cb)
        }
        SyntaxKind::BinaryExpression => {
            is_anonymous_function_definition(emit_context, node.right(), cb)
        }
        SyntaxKind::ExportAssignment => {
            is_anonymous_function_definition(emit_context, node.expression(), cb)
        }
        _ => crate::gostd::debug::fail("Unhandled case in isNamedEvaluation"),
    }
}

// Go: transformers/estransforms/namedevaluation.go:109 getAssignedNameOfIdentifier
/// Gets a string literal to use as the assigned name of an anonymous class or function declaration.
pub(crate) fn get_assigned_name_of_identifier(
    emit_context: &EmitContext,
    name: Node,
    expression: Node, /*WrappedExpression<AnonymousFunctionDefinition>*/
) -> Node {
    let original = emit_context.most_original(skip_outer_expressions(
        expression,
        OuterExpressionKinds::OEK_ALL,
    ));
    if (is_class_declaration(original) || is_function_declaration(original))
        && original.name().is_nil()
        && has_syntactic_modifier(original, ModifierFlags::DEFAULT)
    {
        return emit_context
            .factory()
            .new_string_literal("default", TokenFlags::NONE);
    }
    emit_context.factory().new_string_literal_from_node(name)
}

// Go: transformers/estransforms/namedevaluation.go:118 getAssignedNameOfPropertyName
/// Returns `(assignedName, updatedName)`.
pub(crate) fn get_assigned_name_of_property_name(
    emit_context: &EmitContext,
    name: Node,
    assigned_name_text: &str,
) -> (Node, Node) {
    let factory = emit_context.factory();
    if !assigned_name_text.is_empty() {
        let assigned_name = factory.new_string_literal(assigned_name_text, TokenFlags::NONE);
        return (assigned_name, name);
    }

    if is_property_name_literal(name) || is_private_identifier(name) {
        let assigned_name = factory.new_string_literal_from_node(name);
        return (assigned_name, name);
    }

    let expression = name.expression();
    if is_property_name_literal(expression) && !is_identifier(expression) {
        let assigned_name = factory.new_string_literal_from_node(expression);
        return (assigned_name, name);
    }

    go_assert!(
        is_computed_property_name(name),
        "Expected computed property name"
    );

    let assigned_name = factory.new_generated_name_for_node(name);
    emit_context.add_variable_declaration(assigned_name);

    let key = factory.new_prop_key_helper(expression);
    let assignment = factory.new_assignment_expression(assigned_name, key);
    let updated_name = factory.update_computed_property_name(name, assignment);
    (assigned_name, updated_name)
}

// Go: transformers/estransforms/namedevaluation.go:153 createClassNamedEvaluationHelperBlock
/// Creates a class `static {}` block used to dynamically set the name of a class.
///
/// The assignedName parameter is the expression used to resolve the assigned name at runtime. This expression should not produce
/// side effects.
/// The thisExpression parameter overrides the expression to use for the actual `this` reference. This can be used to provide an
/// expression that has already had its `EmitFlags` set or may have been tracked to prevent substitution.
pub(crate) fn create_class_named_evaluation_helper_block(
    emit_context: &EmitContext,
    assigned_name: Node,
    mut this_expression: Node,
) -> Node {
    // produces:
    //
    //  static { __setFunctionName(this, "C"); }
    //

    if this_expression.is_nil() {
        this_expression = emit_context.factory().new_this_expression();
    }

    let factory = emit_context.factory();
    let expression =
        factory.new_set_function_name_helper(this_expression, assigned_name, "" /*prefix*/);
    let statement = factory.new_expression_statement(expression);
    let body = factory.new_block(
        factory.new_node_list(&[statement]),
        false, /*multiLine*/
    );
    let block =
        factory.new_class_static_block_declaration(ModifierList::NIL /*modifiers*/, body);

    // We use `emitNode.assignedName` to indicate this is a NamedEvaluation helper block
    // and to stash the expression used to resolve the assigned name.
    emit_context.set_assigned_name(block, assigned_name);
    block
}

// Go: transformers/estransforms/namedevaluation.go:176 injectClassNamedEvaluationHelperBlockIfMissing
/// Injects a class `static {}` block used to dynamically set the name of a class, if one does not already exist.
pub(crate) fn inject_class_named_evaluation_helper_block_if_missing(
    emit_context: &EmitContext,
    mut node: Node,
    assigned_name: Node,
    this_expression: Node,
) -> Node {
    // given:
    //
    //  let C = class {
    //  };
    //
    // produces:
    //
    //  let C = class {
    //      static { __setFunctionName(this, "C"); }
    //  };

    // NOTE: If the class has a `_classThis` assignment block, this helper will be injected after that block.

    if class_has_explicitly_assigned_name(emit_context, node) {
        return node;
    }

    let factory = emit_context.factory();
    let named_evaluation_block =
        create_class_named_evaluation_helper_block(emit_context, assigned_name, this_expression);
    if node.name().is_some() {
        emit_context.set_source_map_range(
            named_evaluation_block.body().statements().get(0),
            node.name().loc(),
        );
    }

    let node_members = node.members().to_vec();
    // PORT: Go `slices.IndexFunc(...) + 1`; -1 + 1 is 0.
    let insertion_index = node_members
        .iter()
        .position(|&n| is_class_this_assignment_block(emit_context, n))
        .map_or(0, |i| i + 1);
    let leading = &node_members[..insertion_index];
    let trailing = &node_members[insertion_index..];

    let mut members: Vec<Node> = Vec::with_capacity(node_members.len() + 1);
    members.extend_from_slice(leading);
    members.push(named_evaluation_block);
    members.extend_from_slice(trailing);
    let members_list = factory.new_node_list_with_loc(&members, node.member_list().loc());

    let old_node = node;
    if is_class_declaration(node) {
        node = factory.update_class_declaration(
            node,
            node.modifiers(),
            node.name(),
            node.type_parameter_list(),
            node.heritage_clauses(),
            members_list,
        );
    } else {
        node = factory.update_class_expression(
            node,
            node.modifiers(),
            node.name(),
            node.type_parameter_list(),
            node.heritage_clauses(),
            members_list,
        );
    }

    emit_context.set_assigned_name(node, assigned_name);

    // Transfer ClassThis from old to new node, since UpdateClassExpression creates
    // a new node that won't have ClassThis set on it.
    let ct = emit_context.class_this(old_node);
    if ct.is_some() {
        emit_context.set_class_this(node, ct);
    }

    node
}

// Go: transformers/estransforms/namedevaluation.go:250 finishTransformNamedEvaluation
pub(crate) fn finish_transform_named_evaluation(
    emit_context: &EmitContext,
    expression: Node, // WrappedExpression<AnonymousFunctionDefinition>,
    assigned_name: Node,
    ignore_empty_string_literal: bool,
) -> Node {
    if ignore_empty_string_literal
        && is_string_literal(assigned_name)
        && assigned_name.text().is_empty()
    {
        return expression;
    }

    let factory = emit_context.factory();
    let inner_expression = skip_outer_expressions(expression, OuterExpressionKinds::OEK_ALL);

    let updated_expression = if is_class_expression(inner_expression) {
        inject_class_named_evaluation_helper_block_if_missing(
            emit_context,
            inner_expression,
            assigned_name,
            Node::NIL, /*thisExpression*/
        )
    } else {
        factory.new_set_function_name_helper(inner_expression, assigned_name, "" /*prefix*/)
    };

    factory.restore_outer_expressions(
        expression,
        updated_expression,
        OuterExpressionKinds::OEK_ALL,
    )
}

/// Go `if len(assignedNameText) > 0 { NewStringLiteral(..) } else { getAssignedNameOfIdentifier(..) }`.
fn assigned_name_or_identifier(
    emit_context: &EmitContext,
    assigned_name_text: &str,
    name: Node,
    expression: Node,
) -> Node {
    if !assigned_name_text.is_empty() {
        emit_context
            .factory()
            .new_string_literal(assigned_name_text, TokenFlags::NONE)
    } else {
        get_assigned_name_of_identifier(emit_context, name, expression)
    }
}

// Go: transformers/estransforms/namedevaluation.go:273 transformNamedEvaluationOfPropertyAssignment
pub(crate) fn transform_named_evaluation_of_property_assignment(
    context: &EmitContext,
    node: Node, /*NamedEvaluation & PropertyAssignment*/
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> Node {
    // 13.2.5.5 RS: PropertyDefinitionEvaluation
    //   PropertyAssignment : PropertyName `:` AssignmentExpression
    //     ...
    //     5. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true* and _isProtoSetter_ is *false*, then
    //        a. Let _popValue_ be ? NamedEvaluation of |AssignmentExpression| with argument _propKey_.
    //     ...

    let factory = context.factory();
    let (assigned_name, name) =
        get_assigned_name_of_property_name(context, node.name(), assigned_name_text);
    let initializer = finish_transform_named_evaluation(
        context,
        node.initializer(),
        assigned_name,
        ignore_empty_string_literal,
    );
    factory.update_property_assignment(
        node,
        ModifierList::NIL, /*modifiers*/
        name,
        Node::NIL, /*postfixToken*/
        Node::NIL, /*typeNode*/
        initializer,
    )
}

// Go: transformers/estransforms/namedevaluation.go:287 transformNamedEvaluationOfShorthandAssignmentProperty
pub(crate) fn transform_named_evaluation_of_shorthand_assignment_property(
    emit_context: &EmitContext,
    node: Node, /*NamedEvaluation & ShorthandPropertyAssignment*/
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> Node {
    // 13.15.5.3 RS: PropertyDestructuringAssignmentEvaluation
    //   AssignmentProperty : IdentifierReference Initializer?
    //     ...
    //     4. If |Initializer?| is present and _v_ is *undefined*, then
    //        a. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //           i. Set _v_ to ? NamedEvaluation of |Initializer| with argument _P_.
    //     ...

    let factory = emit_context.factory();
    let assigned_name = assigned_name_or_identifier(
        emit_context,
        assigned_name_text,
        node.name(),
        node.object_assignment_initializer(),
    );
    let object_assignment_initializer = finish_transform_named_evaluation(
        emit_context,
        node.object_assignment_initializer(),
        assigned_name,
        ignore_empty_string_literal,
    );
    factory.update_shorthand_property_assignment(
        node,
        ModifierList::NIL, /*modifiers*/
        node.name(),
        Node::NIL, /*postfixToken*/
        Node::NIL, /*typeNode*/
        node.equals_token(),
        object_assignment_initializer,
    )
}

// Go: transformers/estransforms/namedevaluation.go:315 transformNamedEvaluationOfVariableDeclaration
pub(crate) fn transform_named_evaluation_of_variable_declaration(
    emit_context: &EmitContext,
    node: Node, /*NamedEvaluation & VariableDeclaration*/
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> Node {
    // 14.3.1.2 RS: Evaluation
    //   LexicalBinding : BindingIdentifier Initializer
    //     ...
    //     3. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //        a. Let _value_ be ? NamedEvaluation of |Initializer| with argument _bindingId_.
    //     ...
    //
    // 14.3.2.1 RS: Evaluation
    //   VariableDeclaration : BindingIdentifier Initializer
    //     ...
    //     3. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //        a. Let _value_ be ? NamedEvaluation of |Initializer| with argument _bindingId_.
    //     ...

    let factory = emit_context.factory();
    let assigned_name = assigned_name_or_identifier(
        emit_context,
        assigned_name_text,
        node.name(),
        node.initializer(),
    );
    let initializer = finish_transform_named_evaluation(
        emit_context,
        node.initializer(),
        assigned_name,
        ignore_empty_string_literal,
    );
    factory.update_variable_declaration(
        node,
        node.name(),
        Node::NIL, /*exclamationToken*/
        Node::NIL, /*typeNode*/
        initializer,
    )
}

// Go: transformers/estransforms/namedevaluation.go:347 transformNamedEvaluationOfParameterDeclaration
pub(crate) fn transform_named_evaluation_of_parameter_declaration(
    emit_context: &EmitContext,
    node: Node, /*NamedEvaluation & ParameterDeclaration*/
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> Node {
    // 8.6.3 RS: IteratorBindingInitialization
    //   SingleNameBinding : BindingIdentifier Initializer?
    //     ...
    //     5. If |Initializer| is present and _v_ is *undefined*, then
    //        a. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //           i. Set _v_ to ? NamedEvaluation of |Initializer| with argument _bindingId_.
    //     ...
    //
    // 14.3.3.3 RS: KeyedBindingInitialization
    //   SingleNameBinding : BindingIdentifier Initializer?
    //     ...
    //     4. If |Initializer| is present and _v_ is *undefined*, then
    //        a. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //           i. Set _v_ to ? NamedEvaluation of |Initializer| with argument _bindingId_.
    //     ...

    let factory = emit_context.factory();
    let assigned_name = assigned_name_or_identifier(
        emit_context,
        assigned_name_text,
        node.name(),
        node.initializer(),
    );
    let initializer = finish_transform_named_evaluation(
        emit_context,
        node.initializer(),
        assigned_name,
        ignore_empty_string_literal,
    );
    factory.update_parameter_declaration(
        node,
        ModifierList::NIL, /*modifiers*/
        node.dot_dot_dot_token(),
        node.name(),
        Node::NIL, /*questionToken*/
        Node::NIL, /*typeNode*/
        initializer,
    )
}

// Go: transformers/estransforms/namedevaluation.go:383 transformNamedEvaluationOfBindingElement
pub(crate) fn transform_named_evaluation_of_binding_element(
    emit_context: &EmitContext,
    node: Node, /*NamedEvaluation & BindingElement*/
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> Node {
    // 8.6.3 RS: IteratorBindingInitialization
    //   SingleNameBinding : BindingIdentifier Initializer?
    //     ...
    //     5. If |Initializer| is present and _v_ is *undefined*, then
    //        a. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //           i. Set _v_ to ? NamedEvaluation of |Initializer| with argument _bindingId_.
    //     ...
    //
    // 14.3.3.3 RS: KeyedBindingInitialization
    //   SingleNameBinding : BindingIdentifier Initializer?
    //     ...
    //     4. If |Initializer| is present and _v_ is *undefined*, then
    //        a. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //           i. Set _v_ to ? NamedEvaluation of |Initializer| with argument _bindingId_.
    //     ...

    let factory = emit_context.factory();
    let assigned_name = assigned_name_or_identifier(
        emit_context,
        assigned_name_text,
        node.name(),
        node.initializer(),
    );
    let initializer = finish_transform_named_evaluation(
        emit_context,
        node.initializer(),
        assigned_name,
        ignore_empty_string_literal,
    );
    factory.update_binding_element(
        node,
        node.dot_dot_dot_token(),
        node.property_name(),
        node.name(),
        initializer,
    )
}

// Go: transformers/estransforms/namedevaluation.go:417 transformNamedEvaluationOfPropertyDeclaration
pub(crate) fn transform_named_evaluation_of_property_declaration(
    emit_context: &EmitContext,
    node: Node, /*NamedEvaluation & PropertyDeclaration*/
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> Node {
    // 10.2.1.3 RS: EvaluateBody
    //   Initializer : `=` AssignmentExpression
    //     ...
    //     3. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true*, then
    //        a. Let _value_ be ? NamedEvaluation of |Initializer| with argument _functionObject_.[[ClassFieldInitializerName]].
    //     ...

    let factory = emit_context.factory();
    let (assigned_name, name) =
        get_assigned_name_of_property_name(emit_context, node.name(), assigned_name_text);
    let initializer = finish_transform_named_evaluation(
        emit_context,
        node.initializer(),
        assigned_name,
        ignore_empty_string_literal,
    );
    factory.update_property_declaration(
        node,
        node.modifiers(),
        name,
        Node::NIL, /*postfixToken*/
        Node::NIL, /*typeNode*/
        initializer,
    )
}

// Go: transformers/estransforms/namedevaluation.go:438 transformNamedEvaluationOfAssignmentExpression
pub(crate) fn transform_named_evaluation_of_assignment_expression(
    emit_context: &EmitContext,
    node: Node, /*NamedEvaluation & BinaryExpression*/
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> Node {
    // 13.15.2 RS: Evaluation
    //   AssignmentExpression : LeftHandSideExpression `=` AssignmentExpression
    //     1. If |LeftHandSideExpression| is neither an |ObjectLiteral| nor an |ArrayLiteral|, then
    //        a. Let _lref_ be ? Evaluation of |LeftHandSideExpression|.
    //        b. If IsAnonymousFunctionDefinition(|AssignmentExpression|) and IsIdentifierRef of |LeftHandSideExpression| are both *true*, then
    //           i. Let _rval_ be ? NamedEvaluation of |AssignmentExpression| with argument _lref_.[[ReferencedName]].
    //     ...
    //
    //   AssignmentExpression : LeftHandSideExpression `&&=` AssignmentExpression
    //     ...
    //     5. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true* and IsIdentifierRef of |LeftHandSideExpression| is *true*, then
    //        a. Let _rval_ be ? NamedEvaluation of |AssignmentExpression| with argument _lref_.[[ReferencedName]].
    //     ...
    //
    //   AssignmentExpression : LeftHandSideExpression `||=` AssignmentExpression
    //     ...
    //     5. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true* and IsIdentifierRef of |LeftHandSideExpression| is *true*, then
    //        a. Let _rval_ be ? NamedEvaluation of |AssignmentExpression| with argument _lref_.[[ReferencedName]].
    //     ...
    //
    //   AssignmentExpression : LeftHandSideExpression `??=` AssignmentExpression
    //     ...
    //     4. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true* and IsIdentifierRef of |LeftHandSideExpression| is *true*, then
    //        a. Let _rval_ be ? NamedEvaluation of |AssignmentExpression| with argument _lref_.[[ReferencedName]].
    //     ...

    let factory = emit_context.factory();
    let assigned_name =
        assigned_name_or_identifier(emit_context, assigned_name_text, node.left(), node.right());
    let right = finish_transform_named_evaluation(
        emit_context,
        node.right(),
        assigned_name,
        ignore_empty_string_literal,
    );
    factory.update_binary_expression(
        node,
        ModifierList::NIL, /*modifiers*/
        node.left(),
        Node::NIL, /*typeNode*/
        node.operator_token(),
        right,
    )
}

// Go: transformers/estransforms/namedevaluation.go:483 transformNamedEvaluationOfExportAssignment
pub(crate) fn transform_named_evaluation_of_export_assignment(
    emit_context: &EmitContext,
    node: Node, /*NamedEvaluation & ExportAssignment*/
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> Node {
    // 16.2.3.7 RS: Evaluation
    //   ExportDeclaration : `export` `default` AssignmentExpression `;`
    //     1. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true*, then
    //        a. Let _value_ be ? NamedEvaluation of |AssignmentExpression| with argument `"default"`.
    //     ...

    // NOTE: Since emit for `export =` translates to `module.exports = ...`, the assigned name of the class or function
    // is `""`.

    let factory = emit_context.factory();
    let assigned_name = if !assigned_name_text.is_empty() {
        factory.new_string_literal(assigned_name_text, TokenFlags::NONE)
    } else if node.is_export_equals() {
        factory.new_string_literal("", TokenFlags::NONE)
    } else {
        factory.new_string_literal("default", TokenFlags::NONE)
    };
    let expression = finish_transform_named_evaluation(
        emit_context,
        node.expression(),
        assigned_name,
        ignore_empty_string_literal,
    );
    factory.update_export_assignment(
        node,
        ModifierList::NIL, /*modifiers*/
        node.is_export_equals(),
        Node::NIL, /*typeNode*/
        expression,
    )
}

// Go: transformers/estransforms/namedevaluation.go:513 transformNamedEvaluation
/// Performs a shallow transformation of a `NamedEvaluation` node, such that a valid name will be assigned.
pub(crate) fn transform_named_evaluation(
    context: &EmitContext,
    node: Node, /*NamedEvaluation*/
    ignore_empty_string_literal: bool,
    assigned_name: &str,
) -> Node {
    match node.kind() {
        SyntaxKind::PropertyAssignment => transform_named_evaluation_of_property_assignment(
            context,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        SyntaxKind::ShorthandPropertyAssignment => {
            transform_named_evaluation_of_shorthand_assignment_property(
                context,
                node,
                ignore_empty_string_literal,
                assigned_name,
            )
        }
        SyntaxKind::VariableDeclaration => transform_named_evaluation_of_variable_declaration(
            context,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        SyntaxKind::Parameter => transform_named_evaluation_of_parameter_declaration(
            context,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        SyntaxKind::BindingElement => transform_named_evaluation_of_binding_element(
            context,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        SyntaxKind::PropertyDeclaration => transform_named_evaluation_of_property_declaration(
            context,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        SyntaxKind::BinaryExpression => transform_named_evaluation_of_assignment_expression(
            context,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        SyntaxKind::ExportAssignment => transform_named_evaluation_of_export_assignment(
            context,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        _ => crate::gostd::debug::fail("Unhandled case in transformNamedEvaluation"),
    }
}
