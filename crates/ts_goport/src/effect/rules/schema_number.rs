// Go: internal/rules/schema_number.go

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

pub static SCHEMA_NUMBER: Rule = Rule {
    name: "schemaNumber",
    group: "style",
    description: "Suggests Schema.Finite and Schema.FiniteFromString instead of Schema.Number APIs when describing domain numbers",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377098],
    run: run_schema_number,
};

fn run_schema_number(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_schema_number(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_Schema_number_API_accepts_NaN_Infinity_and_Infinity_Use_0_for_finite_domain_numbers_If_non_finite_values_are_intentional_disable_this_diagnostic_for_that_line_effect_schemaNumber,
            Vec::new(),
            vec![m.replacement.clone()],
        ));
    }
    diags
}

#[derive(Clone, Debug)]
pub struct SchemaNumberMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub reference_node: Node,
    pub replacement: String,
    pub replacement_identifier: String,
}

// Go: rules/schema_number.go AnalyzeSchemaNumber
pub fn analyze_schema_number(tp: &mut TypeParser<'_>, sf: Node) -> Vec<SchemaNumberMatch> {
    if tp.supported_effect_version() != EffectMajorVersion::V4 {
        return Vec::new();
    }

    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        matches: &mut Vec<SchemaNumberMatch>,
        node: Node,
    ) -> bool {
        if node.is_nil() {
            return false;
        }

        match node.kind() {
            SyntaxKind::ImportDeclaration | SyntaxKind::ImportEqualsDeclaration => {
                return false;
            }
            SyntaxKind::PropertyAccessExpression => {
                if let Some(m) = analyze_schema_number_reference(tp, sf, node) {
                    matches.push(m);
                    return false;
                }
            }
            SyntaxKind::Identifier => {
                if let Some(m) = analyze_schema_number_reference(tp, sf, node) {
                    matches.push(m);
                }
            }
            _ => {}
        }

        node.for_each_child(|child| walk(tp, sf, matches, child));
        false
    }

    let mut matches = Vec::new();
    walk(tp, sf, &mut matches, sf);

    let flows = tp.piping_flows(sf, false);
    let mut filtered = Vec::with_capacity(matches.len());
    for m in matches {
        if schema_number_has_finite_method_check(tp, m.reference_node)
            || schema_number_has_finite_piping_check(tp, m.reference_node, &flows)
        {
            continue;
        }
        filtered.push(m);
    }
    filtered
}

// Go: rules/schema_number.go analyzeSchemaNumberReference
fn analyze_schema_number_reference(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
) -> Option<SchemaNumberMatch> {
    for api in SCHEMA_NUMBER_APIS {
        if tp.is_node_reference_to_effect_schema_module_api(node, api.name) {
            let reference_node = schema_number_reference_location(node);
            return Some(SchemaNumberMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, reference_node),
                reference_node,
                replacement: api.replacement.to_string(),
                replacement_identifier: api.replacement_identifier.to_string(),
            });
        }
    }
    None
}

// Go: rules/schema_number.go schemaNumberHasFiniteMethodCheck
fn schema_number_has_finite_method_check(tp: &mut TypeParser<'_>, node: Node) -> bool {
    let mut schema_expression = node;
    if node.kind() == SyntaxKind::Identifier
        && node.parent().is_some()
        && node.parent().kind() == SyntaxKind::PropertyAccessExpression
    {
        let access = node.parent();
        if access.name() == node {
            schema_expression = node.parent();
        }
    }
    while schema_expression.parent().is_some()
        && schema_expression.parent().kind() == SyntaxKind::PropertyAccessExpression
    {
        let access_node = schema_expression.parent();
        let access = access_node;
        if access.expression() != schema_expression
            || access.name().is_nil()
            || access_node.parent().is_nil()
            || access_node.parent().kind() != SyntaxKind::CallExpression
        {
            return false;
        }

        let call = access_node.parent();
        if call.expression() != access_node {
            return false;
        }
        match access.name().text() {
            "annotate" => {
                schema_expression = access_node.parent();
            }
            "check" => {
                if call.argument_list().is_nil() {
                    return false;
                }
                return schema_number_has_finite_predicate(tp, &call.arguments().to_vec());
            }
            _ => {
                return false;
            }
        }
    }
    false
}

// Go: rules/schema_number.go schemaNumberHasFinitePipingCheck
fn schema_number_has_finite_piping_check(
    tp: &mut TypeParser<'_>,
    reference: Node,
    flows: &[Rc<PipingFlow>],
) -> bool {
    for flow in flows {
        if flow.subject.node.is_nil() || !schema_number_node_contains(flow.subject.node, reference)
        {
            continue;
        }
        for transformation in &flow.transformations {
            if transformation.callee.is_some()
                && tp.is_node_reference_to_effect_schema_module_api(transformation.callee, "check")
                && schema_number_has_finite_predicate(tp, &transformation.args)
            {
                return true;
            }
        }
    }
    false
}

// Go: rules/schema_number.go schemaNumberHasFinitePredicate
fn schema_number_has_finite_predicate(tp: &mut TypeParser<'_>, arguments: &[Node]) -> bool {
    for &argument in arguments {
        let argument = skip_parentheses(argument);
        if argument.kind() != SyntaxKind::CallExpression {
            continue;
        }
        let predicate_call = argument;
        if predicate_call.expression().is_nil() {
            continue;
        }
        if tp.is_node_reference_to_effect_schema_module_api(predicate_call.expression(), "isFinite")
            || tp
                .is_node_reference_to_effect_schema_module_api(predicate_call.expression(), "isInt")
        {
            return true;
        }
    }
    false
}

// Go: rules/schema_number.go schemaNumberNodeContains
fn schema_number_node_contains(ancestor: Node, target: Node) -> bool {
    ancestor.is_some()
        && target.is_some()
        && ancestor.pos() <= target.pos()
        && target.end() <= ancestor.end()
}

/// Go `schemaNumberApi`.
pub struct SchemaNumberApi {
    pub name: &'static str,
    pub replacement: &'static str,
    pub replacement_identifier: &'static str,
}

static SCHEMA_NUMBER_APIS: &[SchemaNumberApi] = &[
    SchemaNumberApi {
        name: "Number",
        replacement: "Schema.Finite",
        replacement_identifier: "Finite",
    },
    SchemaNumberApi {
        name: "NumberFromString",
        replacement: "Schema.FiniteFromString",
        replacement_identifier: "FiniteFromString",
    },
];

// Go: rules/schema_number.go schemaNumberReferenceLocation
fn schema_number_reference_location(node: Node) -> Node {
    if node.kind() == SyntaxKind::PropertyAccessExpression {
        let name = node.name();
        if name.is_some() {
            return name;
        }
    }
    node
}
