//! Port of Effect-TS/tsgo `internal/refactors/async_await_to_fn_try_promise.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::async_await_to_fn::{build_effect_fn_call, build_fn_declaration};
use crate::effect::ls::refactors::async_await_to_gen::{
    find_async_function, transform_body_await_to_yield,
};
use crate::effect::ls::refactors::async_await_to_gen_try_promise::{
    build_tagged_error_class, build_yield_star_try_promise, insert_error_classes_and_replace,
    is_exported_for_error_classes,
};
use crate::effect::ls::refactors::with_kind;
use crate::effect::ls::rewriter::Tracker;
use crate::effect::typeparser::{
    find_effect_module_identifier, find_module_identifier, get_function_like_body,
    get_function_like_name,
};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/async_await_to_fn_try_promise.go:14 AsyncAwaitToFnTryPromise
pub static ASYNC_AWAIT_TO_FN_TRY_PROMISE: Refactor = Refactor {
    name: "asyncAwaitToFnTryPromise",
    description: "Convert async/await to Effect.fn (with error handling)",
    kind: "rewrite.effect.asyncAwaitToFnTryPromise",
    run: run_async_await_to_fn_try_promise,
};

// Go: refactors/async_await_to_fn_try_promise.go:21 runAsyncAwaitToFnTryPromise
fn run_async_await_to_fn_try_promise(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
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
    let data_module_name = find_module_identifier(ctx.source_file, "Data");

    let sf = ctx.source_file;
    let action = ctx.new_refactor_action("Rewrite to Effect.fn with failures", |tracker| {
        transform_async_to_effect_fn_try_promise(
            tracker,
            sf,
            async_fn,
            &effect_module_name,
            &data_module_name,
        );
    });
    with_kind(action, "refactor.rewrite.effect.asyncAwaitToFnTryPromise")
}

// Go: refactors/async_await_to_fn_try_promise.go:50 transformAsyncToEffectFnTryPromise
fn transform_async_to_effect_fn_try_promise(
    tracker: &mut Tracker,
    sf: Node,
    node: Node,
    effect_module_name: &str,
    data_module_name: &str,
) {
    let body = get_function_like_body(node);
    if body.is_nil() {
        return;
    }

    // Track error classes to generate
    let mut error_count = 0;
    let mut error_classes: Vec<Node> = Vec::new();

    // Determine if function is exported (error classes should match)
    let is_exported = is_exported_for_error_classes(node);

    // Transform await expressions to yield* Effect.tryPromise(...)
    let transformed_body = transform_body_await_to_yield(tracker, body, &mut |t, expr| {
        error_count += 1;
        let error_name = format!("Error{error_count}");

        // Build the error class declaration
        let error_class = build_tagged_error_class(t, data_module_name, &error_name, is_exported);
        error_classes.push(error_class);

        build_yield_star_try_promise(t, expr, effect_module_name, &error_name)
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
    let new_decl = build_fn_declaration(tracker, node, effect_fn_call);
    if new_decl.is_nil() {
        return;
    }

    set_parent_in_children(new_decl);

    insert_error_classes_and_replace(tracker, sf, node, new_decl, error_classes);
}
