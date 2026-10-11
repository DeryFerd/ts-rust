//! Port of Effect-TS/tsgo `internal/refactors/async_await_to_fn.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::async_await_to_gen::{
    build_yield_star_promise, find_async_function, get_modifiers_without_async,
    replace_expression_via_statement, transform_body_await_to_yield,
};
use crate::effect::ls::refactors::{clone_node_list, with_kind};
use crate::effect::ls::rewriter::Tracker;
use crate::effect::typeparser::{
    find_effect_module_identifier, get_function_like_body, get_function_like_name,
};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/async_await_to_fn.go:12 AsyncAwaitToFn
pub static ASYNC_AWAIT_TO_FN: Refactor = Refactor {
    name: "asyncAwaitToFn",
    description: "Convert async/await to Effect.fn",
    kind: "rewrite.effect.asyncAwaitToFn",
    run: run_async_await_to_fn,
};

// Go: refactors/async_await_to_fn.go:19 runAsyncAwaitToFn
fn run_async_await_to_fn(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    // Walk ancestor chain to find the nearest async function
    let async_fn = find_async_function(token);
    if async_fn.is_nil() {
        return Vec::new();
    }

    let effect_module_name = find_effect_module_identifier(ctx.source_file);

    let sf = ctx.source_file;
    let action = ctx.new_refactor_action("Rewrite to Effect.fn", |tracker| {
        let new_decl = transform_async_to_effect_fn(tracker, async_fn, &effect_module_name);
        if new_decl.is_some() {
            set_parent_in_children(new_decl);
            // For function declarations, we replace the whole declaration with a variable statement
            if async_fn.kind() == SyntaxKind::FunctionDeclaration {
                tracker.replace_node(sf, async_fn, new_decl, None);
            } else {
                replace_expression_via_statement(tracker, sf, async_fn, new_decl);
            }
        }
    });
    with_kind(action, "refactor.rewrite.effect.asyncAwaitToFn")
}

// Go: refactors/async_await_to_fn.go:57 transformAsyncToEffectFn
/// transformAsyncToEffectFn transforms an async function to use Effect.fn.
fn transform_async_to_effect_fn(tracker: &Tracker, node: Node, effect_module_name: &str) -> Node {
    let body = get_function_like_body(node);
    if body.is_nil() {
        return Node::NIL;
    }

    // Transform await expressions to yield* Effect.promise(...)
    let transformed_body = transform_body_await_to_yield(tracker, body, &mut |t, expr| {
        build_yield_star_promise(t, expr, effect_module_name)
    });

    // Get the function name for the trace string
    let fn_name = get_function_like_name(node);

    // Build Effect.fn("name")(function*(params) { body })
    let effect_fn_call = build_effect_fn_call(
        tracker,
        node,
        transformed_body,
        effect_module_name,
        &fn_name,
    );

    // Build declaration wrapping the fn call
    build_fn_declaration(tracker, node, effect_fn_call)
}

// Go: refactors/async_await_to_fn.go:79 buildEffectFnCall
/// buildEffectFnCall builds: Effect.fn("name")(function*(params) { body })
pub(super) fn build_effect_fn_call(
    tracker: &Tracker,
    node: Node,
    body: Node,
    effect_module_name: &str,
    fn_name: &str,
) -> Node {
    let f = tracker.node_factory();
    let block_body = if body.kind() == SyntaxKind::Block {
        body
    } else {
        // Expression body: wrap in { return <expr> }
        let return_stmt = f.new_return_statement(body);
        f.new_block(f.new_node_list(&[return_stmt]), true)
    };

    // Get type parameters and parameters from original function
    // PORT: Go has one case per kind (arrow, declaration, expression) with
    // the same fields.
    let (type_params, mut params) = match node.kind() {
        SyntaxKind::ArrowFunction
        | SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionExpression => (
            clone_node_list(tracker, node.type_parameter_list()),
            clone_node_list(tracker, node.parameter_list()),
        ),
        _ => (NodeList::NIL, NodeList::NIL),
    };

    if params.is_nil() {
        params = f.new_node_list(&[]);
    }

    // function*(params) { ... }
    let gen_fn = f.new_function_expression(
        ModifierList::NIL,                      // modifiers
        f.new_token(SyntaxKind::AsteriskToken), // asterisk (generator)
        Node::NIL,                              // name
        type_params,                            // typeParameters
        params,                                 // parameters
        Node::NIL,                              // returnType
        Node::NIL,                              // fullSignature
        block_body,
    );

    // Build Effect.fn or Effect.fn("name")
    let effect_id = f.new_identifier(effect_module_name);
    let fn_access = f.new_property_access_expression(
        effect_id,
        Node::NIL,
        f.new_identifier("fn"),
        NodeFlags::NONE,
    );

    let fn_call_expr = if !fn_name.is_empty() {
        // Effect.fn("name")
        f.new_call_expression(
            fn_access,
            Node::NIL,
            NodeList::NIL,
            f.new_node_list(&[f.new_string_literal(fn_name, TokenFlags::NONE)]),
            NodeFlags::NONE,
        )
    } else {
        fn_access
    };

    // Effect.fn("name")(function*(params) { ... })
    f.new_call_expression(
        fn_call_expr,
        Node::NIL,
        NodeList::NIL,
        f.new_node_list(&[gen_fn]),
        NodeFlags::NONE,
    )
}

// Go: refactors/async_await_to_fn.go:153 buildFnDeclaration
/// buildFnDeclaration builds the appropriate declaration wrapping the Effect.fn call.
/// For function declarations: const name = Effect.fn("name")(...)
/// For expressions/arrows: just the Effect.fn("name")(...) expression
// PORT: Go's unused fourth parameter (the function name) is dropped.
pub(super) fn build_fn_declaration(tracker: &Tracker, node: Node, effect_fn_call: Node) -> Node {
    if node.kind() == SyntaxKind::FunctionDeclaration {
        if node.name().is_nil() {
            return effect_fn_call;
        }

        // Build modifiers without async
        let modifiers = get_modifiers_without_async(tracker, node);

        // const name = Effect.fn("name")(...)
        let f = tracker.node_factory();
        let var_decl = f.new_variable_declaration(
            f.deep_clone_node(node.name()),
            Node::NIL, // exclamationToken
            Node::NIL, // type
            effect_fn_call,
        );
        let var_decl_list =
            f.new_variable_declaration_list(f.new_node_list(&[var_decl]), NodeFlags::CONST);
        return f.new_variable_statement(modifiers, var_decl_list);
    }

    // For arrow functions and function expressions, return the expression directly
    effect_fn_call
}
