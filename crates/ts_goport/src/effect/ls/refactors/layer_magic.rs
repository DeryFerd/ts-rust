//! Port of Effect-TS/tsgo `internal/refactors/layer_magic.go`.
//!
//! The refactor gives one action at most: "build" turns
//! `[l1, l2, ...] as any as Layer.Layer<ROut>` into a `Layer.*` pipe that
//! provides ROut, or else "prepare" flattens a layer expression into that
//! form. The graph work is in `effect::layergraph` (`magic.go`).

use crate::astnav;
use crate::effect::layergraph::{
    ExtractLayerGraphOptions, LayerMagicResult, convert_outline_graph_to_layer_magic,
    extract_layer_graph, extract_outline_graph,
};
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::async_await_to_gen::replace_expression_via_statement;
use crate::effect::ls::refactors::with_kind;
use crate::effect::ls::rewriter::Tracker;
use crate::effect::typeparser::find_module_identifier;
use crate::gostd::slices::sort_slice;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/layer_magic.go:17 LayerMagic
pub static LAYER_MAGIC: Refactor = Refactor {
    name: "layerMagic",
    description: "Layer Magic",
    kind: "rewrite.effect.layerMagic",
    run: run_layer_magic,
};

// Go: refactors/layer_magic.go:24 runLayerMagic
fn run_layer_magic(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    let layer_identifier = find_module_identifier(ctx.source_file, "Layer");

    // Collect ancestor nodes from the token up to the source file.
    let mut ancestors: Vec<Node> = Vec::new();
    let mut node = token;
    while node.is_some() && node.kind() != SyntaxKind::SourceFile {
        ancestors.push(node);
        node = node.parent();
    }

    // Try build first on all ancestors, then prepare as fallback.
    for &node in &ancestors {
        let action = try_build_refactor(ctx, node, &layer_identifier);
        if !action.is_empty() {
            return action;
        }
    }
    for &node in &ancestors {
        let action = try_prepare_refactor(ctx, node, &layer_identifier);
        if !action.is_empty() {
            return action;
        }
    }

    Vec::new()
}

// Go: refactors/layer_magic.go:59 adjustedNode
// adjustedNode redirects from a variable/property declaration name to the initializer.
fn adjusted_node(node: Node) -> Node {
    let parent = node.parent();
    if parent.is_some() && node.kind() == SyntaxKind::Identifier {
        if parent.kind() == SyntaxKind::VariableDeclaration
            && parent.initializer().is_some()
            && parent.name() == node
        {
            return parent.initializer();
        }
        if parent.kind() == SyntaxKind::PropertyDeclaration
            && parent.initializer().is_some()
            && parent.name() == node
        {
            return parent.initializer();
        }
    }
    node
}

// Go: refactors/layer_magic.go:80 tryBuildRefactor
// tryBuildRefactor tries to produce the "build" refactor action for the given node.
// It detects the `(expr as any) as Layer.Layer<ROut>` pattern.
// PORT: Go passes the type parser and the checker; both are in `ctx.tp`.
fn try_build_refactor(
    ctx: &mut RefactorContext<'_, '_>,
    node: Node,
    layer_identifier: &str,
) -> Vec<CodeAction> {
    let at_location = adjusted_node(node);

    // Must be an AsExpression: `... as Layer.Layer<ROut>`
    if at_location.kind() != SyntaxKind::AsExpression {
        return Vec::new();
    }
    let outer_type_node = at_location.type_();
    if outer_type_node.is_nil() || outer_type_node.kind() != SyntaxKind::TypeReference {
        return Vec::new();
    }

    // Inner expression must be `expr as any`
    let inner_expr = at_location.expression();
    if inner_expr.kind() != SyntaxKind::AsExpression {
        return Vec::new();
    }
    let inner_type_node = inner_expr.type_();
    if inner_type_node.is_nil() || inner_type_node.kind() != SyntaxKind::AnyKeyword {
        return Vec::new();
    }

    // Parse the outer type as a Layer type to get ROut
    let outer_type = ctx.tp.get_type_at_location(outer_type_node);
    if outer_type.is_nil() {
        return Vec::new();
    }
    let Some(layer) = ctx.tp.layer_type(outer_type) else {
        return Vec::new();
    };

    // The inner expression (before `as any`) is the casted structure
    let casted_structure = inner_expr.expression();

    // Extract layer graph from the casted structure
    // PORT: Go checks for a nil graph; `ExtractLayerGraph` never returns nil.
    let layer_graph = extract_layer_graph(
        ctx.tp,
        &[casted_structure],
        ctx.source_file,
        ExtractLayerGraphOptions {
            array_literal_as_merge: true,
            explode_only_layer_calls: true,
            follow_symbols_depth: 0,
            ..ExtractLayerGraphOptions::default()
        },
    );

    // Extract outline graph
    let outline_graph = extract_outline_graph(ctx.tp, &layer_graph);
    if outline_graph.node_count() <= 1 {
        return Vec::new();
    }

    // Get target output types from the Layer ROut
    let target_output_types = ctx.tp.unroll_union_members(layer.r_out);

    // Convert to magic result
    let magic_result =
        convert_outline_graph_to_layer_magic(ctx.tp, &outline_graph, &target_output_types);
    if magic_result.nodes.is_empty() {
        return Vec::new();
    }

    // PORT: Go prints the missing types in the tracker closure
    // (`buildLayerMagicBuild`), which cannot borrow the checker here. Nothing
    // else uses the checker between this point and there.
    let missing_type_names: Vec<String> = magic_result
        .missing_output_types
        .iter()
        .map(|&t| {
            ctx.tp
                .checker
                .type_to_string_ex(t, Node::NIL, TypeFormatFlags::NO_TRUNCATION, None)
        })
        .collect();

    let sf = ctx.source_file;
    let action = ctx.new_refactor_action(
        "Compose layers automatically with target output services",
        |tracker| {
            build_layer_magic_build(
                tracker,
                sf,
                at_location,
                &magic_result,
                &missing_type_names,
                layer_identifier,
            );
        },
    );
    with_kind(action, "refactor.rewrite.effect.layerMagicBuild")
}

// Go: refactors/layer_magic.go:155 buildLayerMagicBuild
// buildLayerMagicBuild generates a pipe from the first requested output layer, or Layer.empty
// when the first layer does not provide a requested output.
// PORT: `missing_type_names` are Go's `typeNames`, printed by the caller.
fn build_layer_magic_build(
    tracker: &mut Tracker,
    sf: Node,
    old_node: Node,
    magic_result: &LayerMagicResult,
    missing_type_names: &[String],
    layer_identifier: &str,
) {
    let nodes = &magic_result.nodes;
    if nodes.is_empty() {
        return;
    }

    let mut new_declaration = {
        let f = tracker.node_factory();
        let receiver;
        let mut first_pipe_arg = 0;
        if nodes[0].merges {
            receiver = f.deep_clone_node(nodes[0].node);
            first_pipe_arg = 1;
        } else {
            receiver = f.new_property_access_expression(
                f.new_identifier(layer_identifier),
                Node::NIL,
                f.new_identifier("empty"),
                NodeFlags::NONE,
            );
        }

        let mut pipe_args: Vec<Node> = Vec::new();
        for mn in &nodes[first_pipe_arg..] {
            // Determine combinator name
            let combinator_name = if mn.merges && mn.provides {
                "provideMerge"
            } else if mn.merges {
                "merge"
            } else {
                "provide"
            };

            // Layer.provideMerge(expr) or Layer.provide(expr) or Layer.merge(expr)
            let layer_id = f.new_identifier(layer_identifier);
            let combinator_access = f.new_property_access_expression(
                layer_id,
                Node::NIL,
                f.new_identifier(combinator_name),
                NodeFlags::NONE,
            );
            let cloned_expr = f.deep_clone_node(mn.node);
            let call = f.new_call_expression(
                combinator_access,
                Node::NIL,
                NodeList::NIL,
                f.new_node_list(&[cloned_expr]),
                NodeFlags::NONE,
            );
            pipe_args.push(call);
        }

        let pipe_access = f.new_property_access_expression(
            receiver,
            Node::NIL,
            f.new_identifier("pipe"),
            NodeFlags::NONE,
        );
        f.new_call_expression(
            pipe_access,
            Node::NIL,
            NodeList::NIL,
            f.new_node_list(&pipe_args),
            NodeFlags::NONE,
        )
    };

    // Add trailing comment for missing output types
    if !magic_result.missing_output_types.is_empty() {
        let comment = " Unable to find ".to_string()
            + &missing_type_names.join(", ")
            + " in the provided layers. ";
        new_declaration = tracker.emit_context.add_synthetic_trailing_comment(
            new_declaration,
            SyntaxKind::MultiLineCommentTrivia,
            &comment,
            false,
        );
    }

    set_parent_in_children(new_declaration);

    // If the old node is an expression inside a variable declaration, use replaceExpressionViaStatement
    if old_node.parent().is_some() && old_node.parent().kind() == SyntaxKind::VariableDeclaration {
        replace_expression_via_statement(tracker, sf, old_node, new_declaration);
    } else {
        tracker.replace_node(sf, old_node, new_declaration, None);
    }
}

// Go: refactors/layer_magic.go:230 tryPrepareRefactor
// tryPrepareRefactor tries to produce the "prepare" refactor action for the given node.
// It flattens a layer expression into `[...] as any as Layer.Layer<T>`.
// PORT: Go passes the type parser and the checker; both are in `ctx.tp`.
fn try_prepare_refactor(
    ctx: &mut RefactorContext<'_, '_>,
    node: Node,
    layer_identifier: &str,
) -> Vec<CodeAction> {
    let at_location = adjusted_node(node);

    // Skip if already in `as any as Layer.Layer<T>` form
    if is_as_any_as_layer_form(at_location) {
        return Vec::new();
    }

    // Must be an expression
    if !is_expression(at_location) {
        return Vec::new();
    }

    // Extract layer graph
    // PORT: Go checks for a nil graph; `ExtractLayerGraph` never returns nil.
    let layer_graph = extract_layer_graph(
        ctx.tp,
        &[at_location],
        ctx.source_file,
        ExtractLayerGraphOptions {
            array_literal_as_merge: true,
            explode_only_layer_calls: true,
            follow_symbols_depth: 0,
            ..ExtractLayerGraphOptions::default()
        },
    );

    // Extract outline graph
    let outline_graph = extract_outline_graph(ctx.tp, &layer_graph);
    if outline_graph.node_count() <= 1 {
        return Vec::new();
    }

    // Collect all Provides types from outline nodes
    // PORT: Go `map[*checker.Type]bool`; the port keeps first-insertion order
    // (Go walks the map in random order before the sort below).
    let mut layer_output_types: IndexSet<TypeId> = IndexSet::default();
    for (_, node_info) in outline_graph.nodes() {
        for &p in &node_info.provides {
            layer_output_types.insert(p);
        }
    }

    // Collect leaf layer nodes (sorted by position)
    let mut layer_nodes: Vec<Node> = Vec::new();
    for (_, node_info) in outline_graph.nodes() {
        if node_info.node.is_some() && is_expression(node_info.node) {
            layer_nodes.push(node_info.node);
        }
    }
    let sf = ctx.source_file;
    sort_slice(&mut layer_nodes, |a, b| {
        astnav::get_start_of_node(*a, sf, false) < astnav::get_start_of_node(*b, sf, false)
    });

    if layer_nodes.is_empty() {
        return Vec::new();
    }

    // Parse the expression's current type as a Layer to find "previously provided" types
    let expr_type = ctx.tp.get_type_at_location(at_location);
    let mut previously_provided = TypeId::NIL;
    if expr_type.is_some()
        && let Some(parsed_layer) = ctx.tp.layer_type(expr_type)
    {
        previously_provided = parsed_layer.r_out;
    }

    // Partition types into newlyIntroduced and existingBefore
    let all_output_types = sorted_type_slice(ctx.tp.checker, layer_output_types);
    let mut newly_introduced: Vec<TypeId> = Vec::new();
    let mut existing_before: Vec<TypeId> = Vec::new();
    for t in all_output_types {
        if previously_provided.is_some()
            && ctx.tp.checker.is_type_assignable_to(t, previously_provided)
        {
            existing_before.push(t);
        } else {
            newly_introduced.push(t);
        }
    }

    // PORT: Go prints the types in the tracker closure
    // (`buildLayerMagicPrepare`: the new ones, then the existing ones), which
    // cannot borrow the checker here. Nothing else uses the checker between
    // this point and there.
    let newly_introduced_names: Vec<String> = newly_introduced
        .iter()
        .map(|&t| {
            ctx.tp
                .checker
                .type_to_string_ex(t, Node::NIL, TypeFormatFlags::NO_TRUNCATION, None)
        })
        .collect();
    let existing_before_names: Vec<String> = existing_before
        .iter()
        .map(|&t| {
            ctx.tp
                .checker
                .type_to_string_ex(t, Node::NIL, TypeFormatFlags::NO_TRUNCATION, None)
        })
        .collect();

    let action = ctx.new_refactor_action("Prepare layers for automatic composition", |tracker| {
        build_layer_magic_prepare(
            tracker,
            sf,
            at_location,
            &layer_nodes,
            &newly_introduced_names,
            &existing_before_names,
            layer_identifier,
        );
    });
    with_kind(action, "refactor.rewrite.effect.layerMagicPrepare")
}

// Go: refactors/layer_magic.go:319 buildLayerMagicPrepare
// buildLayerMagicPrepare generates: [leaf1, leaf2, ...] as any as Layer.Layer<NewTypes /* ExistingTypes */>
// PORT: Go takes the types and prints them here; the port takes the printed
// names (`newly_introduced`, `existing_before`), in the same order.
fn build_layer_magic_prepare(
    tracker: &mut Tracker,
    sf: Node,
    old_node: Node,
    layer_nodes: &[Node],
    newly_introduced: &[String],
    existing_before: &[String],
    layer_identifier: &str,
) {
    let (inner_as, mut provides_type) = {
        let f = tracker.node_factory();

        // Build array of cloned layer expressions
        let elements: Vec<Node> = layer_nodes
            .iter()
            .map(|&entry| f.deep_clone_node(entry))
            .collect();
        let array_literal = f.new_array_literal_expression(f.new_node_list(&elements), false);

        // Build `any` type node
        let any_type = f.new_keyword_type_node(SyntaxKind::AnyKeyword);

        // Inner as expression: `[...] as any`
        let inner_as = f.new_as_expression(array_literal, any_type);

        // Build the provides union type node
        let provides_type = if newly_introduced.is_empty() {
            f.new_type_reference_node(f.new_identifier("never"), NodeList::NIL)
        } else {
            let type_nodes: Vec<Node> = newly_introduced
                .iter()
                .map(|type_str| {
                    f.new_type_reference_node(f.new_identifier(type_str), NodeList::NIL)
                })
                .collect();
            if type_nodes.len() == 1 {
                type_nodes[0]
            } else {
                f.new_union_type_node(f.new_node_list(&type_nodes))
            }
        };
        (inner_as, provides_type)
    };

    // Add trailing comment for existing types
    if !existing_before.is_empty() {
        let comment = " ".to_string() + &existing_before.join(" | ") + " ";
        provides_type = tracker.emit_context.add_synthetic_trailing_comment(
            provides_type,
            SyntaxKind::MultiLineCommentTrivia,
            &comment,
            false,
        );
    }

    let outer_as = {
        let f = tracker.node_factory();

        // Build Layer.Layer<providesType>
        let qualified_name = f.new_qualified_name(
            f.new_identifier(layer_identifier),
            f.new_identifier("Layer"),
        );
        let layer_type_ref =
            f.new_type_reference_node(qualified_name, f.new_node_list(&[provides_type]));

        // Outer as expression: `([...] as any) as Layer.Layer<T>`
        f.new_as_expression(inner_as, layer_type_ref)
    };

    set_parent_in_children(outer_as);

    // If the old node is an expression inside a variable declaration, use replaceExpressionViaStatement
    if old_node.parent().is_some() && old_node.parent().kind() == SyntaxKind::VariableDeclaration {
        replace_expression_via_statement(tracker, sf, old_node, outer_as);
    } else {
        tracker.replace_node(sf, old_node, outer_as, None);
    }
}

// Go: refactors/layer_magic.go:387 isAsAnyAsLayerForm
// isAsAnyAsLayerForm checks if a node is already in the `(expr as any) as Layer.Layer<T>` form.
fn is_as_any_as_layer_form(node: Node) -> bool {
    if node.kind() != SyntaxKind::AsExpression {
        return false;
    }
    let outer_type = node.type_();
    if outer_type.is_nil() || outer_type.kind() != SyntaxKind::TypeReference {
        return false;
    }
    let inner_expr = node.expression();
    if inner_expr.kind() != SyntaxKind::AsExpression {
        return false;
    }
    let inner_type = inner_expr.type_();
    inner_type.is_some() && inner_type.kind() == SyntaxKind::AnyKeyword
}

// Go: refactors/layer_magic.go:404 sortedTypeSlice
// sortedTypeSlice converts a type set to a sorted slice using TypeToString for deterministic ordering.
// PORT: the set keeps first-insertion order, which is one of the orders Go's
// map walk gives; `sort_slice` is Go's `sort.Slice`.
fn sorted_type_slice(c: &mut Checker, types: IndexSet<TypeId>) -> Vec<TypeId> {
    let mut result: Vec<TypeId> = types.into_iter().collect();
    sort_slice(&mut result, |a, b| {
        c.type_to_string_ex(*a, Node::NIL, TypeFormatFlags::NO_TRUNCATION, None)
            < c.type_to_string_ex(*b, Node::NIL, TypeFormatFlags::NO_TRUNCATION, None)
    });
    result
}
