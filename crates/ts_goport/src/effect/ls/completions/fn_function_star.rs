//! Port of Effect-TS/tsgo `internal/completions/fn_function_star.go`
//! (effect-tsgo 0.51.1), with the enclosing variable name helper.

use super::effect_schema_self_in_classes::{byte_span_to_range, make_completion_item};
use crate::effect::ls::completion::{
    Completion, CompletionContext, parse_accessed_expression_for_completion,
};
use crate::effect::typeparser::find_effect_module_identifier;
use crate::ls::prelude::*;

// Go: completions/fn_function_star.go:16 fnFunctionStar
/// fnFunctionStar provides completions for `fn(function*(){})` when dot-accessing
/// the Effect module identifier (e.g., `Effect.fn|`). This is AST-based and does
/// not require the type checker.
pub static FN_FUNCTION_STAR: Completion = Completion {
    name: "fnFunctionStar",
    description: "Provides fn(function*(){}) completion when accessing the Effect module",
    run: run_fn_function_star,
};

// Go: completions/fn_function_star.go:22 runFnFunctionStar
fn run_fn_function_star(ctx: &mut CompletionContext<'_, '_>) -> Vec<lsproto::CompletionItem> {
    let Some(result) = parse_accessed_expression_for_completion(ctx.source_file, ctx.position)
    else {
        return Vec::new();
    };

    // Resolve the local Effect module identifier and compare
    let effect_identifier = find_effect_module_identifier(ctx.source_file);
    let accessed_text = get_text_of_node(result.accessed_object);
    if accessed_text != effect_identifier {
        return Vec::new();
    }

    // Replacement span: from after the dot to the cursor position
    let span_start = result.accessed_object.end() + 1;
    let span_length = (ctx.position - span_start).max(0);

    let replacement_range = byte_span_to_range(ctx, span_start, span_length);
    let sort_text = "11";

    let mut items = Vec::new();

    // Try to find enclosing variable declaration to extract variable name
    let var_name = find_enclosing_variable_name(result.outer_node);
    if !var_name.is_empty() {
        items.push(make_completion_item(
            format!(r#"fn("{var_name}")"#),
            format!(r#"fn("{var_name}")(function*(${{1}}){{${{0}}}})"#),
            sort_text,
            replacement_range,
            lsproto::CompletionItemKind::VARIABLE,
        ));
    }

    // Always add generic fn and fnUntraced
    items.push(make_completion_item(
        "fn(function*(){})".to_string(),
        "fn(function*(${1}){${0}})".to_string(),
        sort_text,
        replacement_range,
        lsproto::CompletionItemKind::VARIABLE,
    ));
    items.push(make_completion_item(
        "fnUntraced(function*(){})".to_string(),
        "fnUntraced(function*(${1}){${0}})".to_string(),
        sort_text,
        replacement_range,
        lsproto::CompletionItemKind::VARIABLE,
    ));

    items
}

// Go: completions/fn_function_star.go:76 findEnclosingVariableName
/// findEnclosingVariableName walks up from the given node to find an enclosing
/// VariableDeclaration and returns its identifier name, or "" if not found.
pub fn find_enclosing_variable_name(node: Node) -> String {
    let var_decl = find_ancestor(node, |n| n.kind() == SyntaxKind::VariableDeclaration);
    if var_decl.is_nil() {
        return String::new();
    }

    let name = var_decl.name();
    if name.is_nil() || !is_identifier(name) {
        return String::new();
    }

    get_text_of_node(name)
}
