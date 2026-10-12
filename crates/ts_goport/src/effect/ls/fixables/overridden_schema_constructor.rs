//! Port of Effect-TS/tsgo `internal/fixables/overridden_schema_constructor.go`.

use crate::ast::visitor::{NodeVisitorHooks, new_node_visitor};
use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::overridden_schema_constructor::analyze_overridden_schema_constructor;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/overridden_schema_constructor.go:12 OverriddenSchemaConstructorFix
pub static OVERRIDDEN_SCHEMA_CONSTRUCTOR_FIX: Fixable = Fixable {
    name: "overriddenSchemaConstructorFix",
    description: "Remove or rewrite constructor in Schema class",
    // Go: tsdiag.This_Schema_subclass_defines_its_own_constructor_For_Schema_classes_constructor_overrides_break_decoding_behavior_for_the_class_shape_Custom_construction_can_be_expressed_through_a_static_new_method_instead_effect_overriddenSchemaConstructor
    error_codes: &[377044],
    fix_ids: &[
        "overriddenSchemaConstructor_fix",
        "overriddenSchemaConstructor_static",
    ],
    run: run_overridden_schema_constructor_fix,
};

// Go: fixables/overridden_schema_constructor.go:23 runOverriddenSchemaConstructorFix
fn run_overridden_schema_constructor_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_overridden_schema_constructor(ctx.tp, sf);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        let mut actions = Vec::new();

        // _static action: Rewrite using the static 'new' pattern (only when body exists)
        if m.has_body && constructor_supports_static_rewrite(m.constructor_node) {
            if let Some(action) = ctx.new_fix_action(
                "Rewrite using the static 'new' pattern".to_string(),
                |tracker| {
                    let new_method = static_new_method(tracker.node_factory(), m.constructor_node);
                    tracker.replace_node(sf, m.constructor_node, new_method, None);
                },
            ) {
                actions.push(action);
            }
        }

        // _fix action: Remove the constructor override (always available)
        if let Some(action) =
            ctx.new_fix_action("Remove the constructor override".to_string(), |tracker| {
                tracker.delete(sf, m.constructor_node);
            })
        {
            actions.push(action);
        }

        return actions;
    }

    Vec::new()
}

// Go: fixables/overridden_schema_constructor.go:41-108 (the _static action's Run)
/// The `public static new(...)` method that replaces the constructor: `super(...)`
/// statements become `const _this = new this(...)`, `this` becomes `_this`, and
/// `return _this` ends the body.
fn static_new_method(f: &NodeFactory, ctor: Node) -> Node {
    // Build a visitor that transforms super(...) calls and this keywords
    let mut v = new_node_visitor(
        |node: Node, v| {
            // Replace super(...) expression statements with: const _this = new this(...)
            if node.kind() == SyntaxKind::ExpressionStatement {
                let expr = node.expression();
                if expr.kind() == SyntaxKind::CallExpression
                    && expr.expression().kind() == SyntaxKind::SuperKeyword
                {
                    let f = v.factory();
                    let construct_this = f.new_new_expression(
                        f.new_identifier("this"),
                        NodeList::NIL,
                        expr.argument_list(),
                    );
                    return f.new_variable_statement(
                        ModifierList::NIL,
                        f.new_variable_declaration_list(
                            f.new_node_list(&[f.new_variable_declaration(
                                f.new_identifier("_this"),
                                Node::NIL,
                                Node::NIL,
                                construct_this,
                            )]),
                            NodeFlags::CONST,
                        ),
                    );
                }
            }
            // Replace this keywords with _this identifier
            if node.kind() == SyntaxKind::ThisKeyword {
                return v.factory().new_identifier("_this");
            }
            v.visit_each_child(node)
        },
        Some(f),
        NodeVisitorHooks::default(),
        (),
    );

    // Transform the constructor body
    let new_body = v.visit_node(ctor.body());
    // Go: fixables/overridden_schema_constructor.go:86 `newBody.AsBlock()`
    // panics on another kind. The analyzer sets `HasBody` only for a block
    // body, and the visitor gives a block for a block.
    if new_body.kind() != SyntaxKind::Block {
        go_node_as_panic(new_body, "Block");
    }

    // Append return _this to the transformed body's statements
    let mut new_statements: Vec<Node> = new_body.statements().iter().collect();
    new_statements.push(f.new_return_statement(f.new_identifier("_this")));
    let new_block = f.new_block(f.new_node_list(&new_statements), true);

    // Build modifier list with public and static
    let modifiers = f.new_modifier_list(&[
        f.new_modifier(SyntaxKind::PublicKeyword),
        f.new_modifier(SyntaxKind::StaticKeyword),
    ]);

    // Build the replacement method declaration
    f.new_method_declaration(
        modifiers,
        Node::NIL,
        f.new_identifier("new"),
        Node::NIL,
        ctor.type_parameter_list(),
        ctor.parameter_list(),
        ctor.type_(),
        Node::NIL,
        new_block,
    )
}

// Go: fixables/overridden_schema_constructor.go:134 constructorSupportsStaticRewrite
fn constructor_supports_static_rewrite(ctor_node: Node) -> bool {
    let parameters = ctor_node.parameter_list();
    if parameters.is_nil() {
        return true;
    }
    for param_node in parameters.nodes().iter() {
        if is_parameter_property_declaration(param_node, ctor_node) {
            return false;
        }
    }
    true
}
