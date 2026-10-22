//! Port of Effect-TS/tsgo `internal/fixables/service_not_as_class.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::service_not_as_class::analyze_service_not_as_class;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/service_not_as_class.go:12 ServiceNotAsClassFix
pub static SERVICE_NOT_AS_CLASS_FIX: Fixable = Fixable {
    name: "serviceNotAsClass",
    description: "Convert to class declaration",
    // Go: tsdiag.Context_Service_is_assigned_to_a_variable_here_but_this_API_is_intended_for_a_class_declaration_shape_such_as_0_effect_serviceNotAsClass
    error_codes: &[377056],
    fix_ids: &["serviceNotAsClass_fix"],
    run: run_service_not_as_class_fix,
};

// Go: fixables/service_not_as_class.go:20 runServiceNotAsClassFix
fn run_service_not_as_class_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_service_not_as_class(ctx.tp, sf);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        if let Some(action) =
            ctx.new_fix_action("Convert to class declaration".to_string(), |tracker| {
                // Go: fixables/service_not_as_class.go:34
                // `CallExprNode.AsCallExpression()` panics on another kind;
                // the analyzer only keeps call expressions.
                let call_expr = m.call_expr_node;
                if call_expr.kind() != SyntaxKind::CallExpression {
                    go_node_as_panic(call_expr, "CallExpression");
                }
                let f = tracker.node_factory();

                // Build the original service namespace property access.
                let service_map_service = f.new_property_access_expression(
                    f.new_identifier(m.service_module.as_str()),
                    Node::NIL,
                    f.new_identifier("Service"),
                    NodeFlags::NONE,
                );

                // Build combined type arguments: <ClassName, ...OriginalTypeArgs>
                let self_type_ref = f.new_type_reference_node(
                    f.new_identifier(m.variable_name.as_str()),
                    NodeList::NIL,
                );
                let mut type_arg_nodes = vec![self_type_ref];
                let type_arguments = call_expr.type_argument_list();
                if type_arguments.is_some() {
                    for ta in type_arguments.nodes().iter() {
                        type_arg_nodes.push(f.deep_clone_node(ta));
                    }
                }

                // Build inner call: <ServiceModule>.Service<Self, ...TypeArgs>()
                let inner_call = f.new_call_expression(
                    service_map_service,
                    Node::NIL,
                    f.new_node_list(&type_arg_nodes),
                    NodeList::NIL,
                    NodeFlags::NONE,
                );

                // Build outer call: innerCall(args...)
                let mut cloned_args = NodeList::NIL;
                let arguments = call_expr.argument_list();
                if arguments.is_some() && !arguments.nodes().is_empty() {
                    let arg_nodes: Vec<Node> = arguments
                        .nodes()
                        .iter()
                        .map(|arg| f.deep_clone_node(arg))
                        .collect();
                    cloned_args = f.new_node_list(&arg_nodes);
                }
                let outer_call = f.new_call_expression(
                    inner_call,
                    Node::NIL,
                    NodeList::NIL,
                    cloned_args,
                    NodeFlags::NONE,
                );

                // Build heritage clause: extends outerCall
                let expr_with_type_args =
                    f.new_expression_with_type_arguments(outer_call, NodeList::NIL);
                let heritage_clause = f.new_heritage_clause(
                    SyntaxKind::ExtendsKeyword,
                    f.new_node_list(&[expr_with_type_args]),
                );

                // Build modifiers for the class declaration
                let mut modifiers = ModifierList::NIL;
                if m.modifier_nodes.is_some() && !m.modifier_nodes.nodes().is_empty() {
                    let mod_nodes: Vec<Node> = m
                        .modifier_nodes
                        .nodes()
                        .iter()
                        .map(|modifier| f.new_modifier(modifier.kind()))
                        .collect();
                    modifiers = f.new_modifier_list(&mod_nodes);
                }

                // Build class declaration
                let class_decl = f.new_class_declaration(
                    modifiers,
                    f.new_identifier(m.variable_name.as_str()),
                    NodeList::NIL, // no type parameters
                    f.new_node_list(&[heritage_clause]),
                    f.new_node_list(&[]), // empty members
                );

                set_parent_in_children(class_decl);
                tracker.replace_node(sf, m.target_node, class_decl, None);
            })
        {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
