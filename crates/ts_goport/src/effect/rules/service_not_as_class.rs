//! Port of Effect-TS/tsgo `internal/rules/service_not_as_class.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules/service_not_as_class.go ServiceNotAsClass
pub static SERVICE_NOT_AS_CLASS: Rule = Rule {
    name: "serviceNotAsClass",
    group: "style",
    description: "Warns when Context.Service is used as a variable instead of a class declaration",
    default_severity: Severity::Off,
    supported_effect: &["v4"],
    codes: &[377056],
    run: run_service_not_as_class,
};

fn run_service_not_as_class(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_service_not_as_class(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Context_Service_is_assigned_to_a_variable_here_but_this_API_is_intended_for_a_class_declaration_shape_such_as_0_effect_serviceNotAsClass,
            Vec::new(),
            vec![m.suggested_usage.clone()],
        ));
    }
    diags
}

/// ServiceNotAsClassMatch holds the data needed by both the diagnostic and the quickfix.
// Go: rules/service_not_as_class.go ServiceNotAsClassMatch
#[derive(Clone, Debug)]
pub struct ServiceNotAsClassMatch {
    pub source_file: Node,
    /// Error range for the call expression
    pub location: TextRange,
    /// The full suggested class declaration string for the diagnostic message
    pub suggested_usage: String,
    /// The call expression node (ServiceMap.Service<...>(...) or Context.Service<...>(...))
    pub call_expr_node: Node,
    /// The variable/class name
    pub variable_name: String,
    /// Text of original type arguments (e.g. "ConfigService")
    pub type_args_text: String,
    /// Text of original call arguments (e.g. `"Config"`)
    pub args_text: String,
    /// Service namespace identifier (e.g. "ServiceMap" or "Context")
    pub service_module: String,
    /// The node to replace (variable statement or declaration list)
    pub target_node: Node,
    /// Modifiers from the variable statement (e.g. export)
    pub modifier_nodes: ModifierList,
}

/// AnalyzeServiceNotAsClass finds all const variable declarations using the v4 service constructor
/// that should be class declarations instead. V4-only rule.
// Go: rules/service_not_as_class.go AnalyzeServiceNotAsClass
pub fn analyze_service_not_as_class(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<ServiceNotAsClassMatch> {
    if tp.supported_effect_version() != EffectMajorVersion::V4 {
        return Vec::new();
    }

    let mut matches: Vec<ServiceNotAsClassMatch> = Vec::new();

    let mut node_to_visit: Vec<Node> = Vec::new();
    sf.for_each_child(|child| {
        node_to_visit.push(child);
        false
    });

    while let Some(node) = node_to_visit.pop() {
        if node.kind() == SyntaxKind::VariableDeclaration {
            if let Some(m) = check_service_not_as_class(tp, sf, node) {
                matches.push(m);
            }
        }

        node.for_each_child(|child| {
            node_to_visit.push(child);
            false
        });
    }

    matches
}

// Go: rules/service_not_as_class.go checkServiceNotAsClass
fn check_service_not_as_class(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
) -> Option<ServiceNotAsClassMatch> {
    let var_decl = node;
    if var_decl.is_nil() || var_decl.initializer().is_nil() {
        return None;
    }

    if var_decl.initializer().kind() != SyntaxKind::CallExpression {
        return None;
    }

    let call_expr = var_decl.initializer();
    if call_expr.type_argument_list().is_nil() || call_expr.type_arguments().is_empty() {
        return None;
    }

    // Check parent is a const declaration list
    let decl_list = node.parent();
    if decl_list.is_nil() || decl_list.kind() != SyntaxKind::VariableDeclarationList {
        return None;
    }
    if !decl_list.flags().intersects(NodeFlags::CONST) {
        return None;
    }

    let mut service_module = "";
    if tp.is_node_reference_to_effect_context_module_api(call_expr.expression(), "Service") {
        service_module = "Context";
    }
    if service_module.is_empty() {
        return None;
    }

    let text = source_file_text(sf);

    // Extract variable name
    let variable_name = extract_node_text(sf, &text, node.name());

    // Extract type arguments text
    let type_args = call_expr.type_arguments();
    let mut type_arg_texts: Vec<String> = Vec::with_capacity(type_args.len());
    for ta in type_args {
        type_arg_texts.push(extract_node_text(sf, &text, ta));
    }
    let type_args_text = type_arg_texts.join(", ");

    // Extract call arguments text
    let mut args_text = String::new();
    if !call_expr.arguments().is_empty() {
        let mut arg_texts: Vec<String> = Vec::with_capacity(call_expr.arguments().len());
        for arg in call_expr.arguments() {
            arg_texts.push(extract_node_text(sf, &text, arg));
        }
        args_text = arg_texts.join(", ");
    }

    // Build suggested usage string using the matched service namespace.
    let suggested_usage = if !args_text.is_empty() {
        format!(
            "class {variable_name} extends {service_module}.Service<{variable_name}, {type_args_text}>()({args_text}) {{}}"
        )
    } else {
        format!(
            "class {variable_name} extends {service_module}.Service<{variable_name}, {type_args_text}>() {{}}"
        )
    };

    // Determine target node and modifiers
    let variable_statement = decl_list.parent();
    let target_node;
    let mut modifier_nodes = ModifierList::NIL;
    if variable_statement.is_some() && variable_statement.kind() == SyntaxKind::VariableStatement {
        target_node = variable_statement;
        modifier_nodes = variable_statement.modifiers();
    } else {
        target_node = decl_list;
    }

    Some(ServiceNotAsClassMatch {
        source_file: sf,
        location: get_error_range_for_node(sf, var_decl.initializer()),
        suggested_usage,
        call_expr_node: var_decl.initializer(),
        variable_name,
        type_args_text,
        args_text,
        service_module: service_module.to_string(),
        target_node,
        modifier_nodes,
    })
}

/// extractNodeText gets the source text of a node, skipping leading trivia.
// Go: rules/service_not_as_class.go extractNodeText
fn extract_node_text(sf: Node, text: &str, node: Node) -> String {
    if node.is_nil() {
        return String::new();
    }
    let start = get_token_pos_of_node(node, sf, false);
    let end = node.end();
    if start >= 0 && end >= start && end as usize <= text.len() {
        return go_cut_slice(text, start as usize, end as usize).into_owned();
    }
    String::new()
}
