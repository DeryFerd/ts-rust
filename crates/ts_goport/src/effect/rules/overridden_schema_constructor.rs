//! Port of Effect-TS/tsgo `internal/rules/overridden_schema_constructor.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules/overridden_schema_constructor.go OverriddenSchemaConstructor
pub static OVERRIDDEN_SCHEMA_CONSTRUCTOR: Rule = Rule {
    name: "overriddenSchemaConstructor",
    group: "correctness",
    description: "Prevents overriding constructors in Schema classes which breaks decoding behavior",
    default_severity: Severity::Error,
    supported_effect: &["v3", "v4"],
    codes: &[377044],
    run: run_overridden_schema_constructor,
};

fn run_overridden_schema_constructor(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_overridden_schema_constructor(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_Schema_subclass_defines_its_own_constructor_For_Schema_classes_constructor_overrides_break_decoding_behavior_for_the_class_shape_Custom_construction_can_be_expressed_through_a_static_new_method_instead_effect_overriddenSchemaConstructor,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

/// OverriddenSchemaConstructorMatch holds the AST nodes needed by both the diagnostic rule
/// and the quick-fixes for the overriddenSchemaConstructor pattern.
// Go: rules/overridden_schema_constructor.go OverriddenSchemaConstructorMatch
#[derive(Clone, Copy)]
pub struct OverriddenSchemaConstructorMatch {
    pub source_file: Node,
    /// The error range for the constructor node
    pub location: TextRange,
    /// The constructor declaration AST node
    pub constructor_node: Node,
    /// Whether the constructor has a body (the static fix is only available when true)
    pub has_body: bool,
}

/// AnalyzeOverriddenSchemaConstructor finds all class declarations extending Schema
/// that have an overridden constructor which is not an allowed passthrough pattern.
// Go: rules/overridden_schema_constructor.go AnalyzeOverriddenSchemaConstructor
pub fn analyze_overridden_schema_constructor(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<OverriddenSchemaConstructorMatch> {
    let mut matches = Vec::new();

    let mut node_to_visit: Vec<Node> = Vec::new();
    sf.for_each_child(|child| {
        node_to_visit.push(child);
        false
    });

    while let Some(node) = node_to_visit.pop() {
        if node.kind() == SyntaxKind::ClassDeclaration
            && let Some(m) = check_overridden_schema_constructor(tp, sf, node)
        {
            matches.push(m);
        }

        node.for_each_child(|child| {
            node_to_visit.push(child);
            false
        });
    }

    matches
}

// Go: rules/overridden_schema_constructor.go checkOverriddenSchemaConstructor
fn check_overridden_schema_constructor(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
) -> Option<OverriddenSchemaConstructorMatch> {
    let extends_elements = get_extends_heritage_clause_elements(node);
    if extends_elements.is_empty() {
        return None;
    }

    let mut extends_schema = false;
    for elem in extends_elements {
        if elem.kind() != SyntaxKind::ExpressionWithTypeArguments {
            continue;
        }
        let expr = elem.expression();
        let t = tp.get_type_at_location(expr);
        if t.is_some() && tp.is_schema_type(t) {
            extends_schema = true;
            break;
        }
    }

    if !extends_schema {
        return None;
    }

    if node.kind() != SyntaxKind::ClassDeclaration {
        return None;
    }
    let class_decl = node;
    if class_decl.member_list().is_nil() {
        return None;
    }

    for member in class_decl.member_list().nodes().iter() {
        if member.kind() == SyntaxKind::Constructor {
            if is_allowed_constructor(member) {
                continue;
            }
            let ctor = member;
            let has_body = ctor.body().is_some() && ctor.body().kind() == SyntaxKind::Block;
            return Some(OverriddenSchemaConstructorMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, member),
                constructor_node: member,
                has_body,
            });
        }
    }

    None
}

/// isAllowedConstructor checks if a constructor is a passthrough that simply forwards
/// exactly 2 parameters to super(). This pattern is used internally by Schema and is allowed.
// Go: rules/overridden_schema_constructor.go isAllowedConstructor
fn is_allowed_constructor(ctor_node: Node) -> bool {
    let ctor = ctor_node;
    if ctor.body().is_nil() || ctor.body().kind() != SyntaxKind::Block {
        return false;
    }
    let block = ctor.body();
    if block.statement_list().is_nil() || block.statement_list().nodes().len() != 1 {
        return false;
    }

    let stmt = block.statement_list().nodes().get(0);
    if stmt.kind() != SyntaxKind::ExpressionStatement {
        return false;
    }

    let expr = stmt.expression();
    if expr.kind() != SyntaxKind::CallExpression {
        return false;
    }

    let call = expr;
    if call.expression().kind() != SyntaxKind::SuperKeyword {
        return false;
    }

    // Constructor must have exactly 2 parameters
    if ctor.parameter_list().is_nil() || ctor.parameter_list().nodes().len() != 2 {
        return false;
    }

    // Collect parameter names (must all be simple identifiers)
    let mut expected_names: Vec<String> = Vec::with_capacity(2);
    for param in ctor.parameter_list().nodes().iter() {
        let name = param.name();
        if name.is_nil() || name.kind() != SyntaxKind::Identifier {
            return false;
        }
        expected_names.push(get_text_of_node(name));
    }

    // super() call must have exactly 2 arguments matching parameter names in order
    if call.argument_list().is_nil() || call.argument_list().nodes().len() != 2 {
        return false;
    }

    for (i, arg) in call.argument_list().nodes().iter().enumerate() {
        if arg.kind() != SyntaxKind::Identifier {
            return false;
        }
        if get_text_of_node(arg) != expected_names[i] {
            return false;
        }
    }

    true
}
