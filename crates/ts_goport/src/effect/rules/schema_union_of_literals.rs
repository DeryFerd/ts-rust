//! Port of Effect-TS/tsgo `internal/rules/schema_union_of_literals.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// SchemaUnionOfLiterals detects Schema.Union(...) calls where all arguments
/// are Schema.Literal(...) calls and suggests combining them into a single
/// Schema.Literal call. This rule is V3-only and disabled by default.
pub static SCHEMA_UNION_OF_LITERALS: Rule = Rule {
    name: "schemaUnionOfLiterals",
    group: "style",
    description: "Suggests combining multiple Schema.Literal calls in Schema.Union into a single Schema.Literal",
    default_severity: Severity::Off,
    supported_effect: &["v3"],
    codes: &[377038],
    run: run_schema_union_of_literals,
};

fn run_schema_union_of_literals(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_schema_union_of_literals(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_Schema_Union_contains_multiple_Schema_Literal_members_and_can_be_simplified_to_a_single_Schema_Literal_call_effect_schemaUnionOfLiterals,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

/// SchemaUnionOfLiteralsMatch holds the AST nodes needed by both the diagnostic rule
/// and the quick-fix for the schemaUnionOfLiterals pattern.
#[derive(Default)]
pub struct SchemaUnionOfLiteralsMatch {
    pub source_file: Node,
    /// Pre-computed error range for the diagnostic
    pub location: TextRange,
    /// The full Schema.Union(...) call expression to be replaced
    pub union_call_node: Node,
    /// The callee expression (Schema.Literal) from the first argument
    pub first_literal_expression: Node,
    /// All arguments collected from every Schema.Literal(...) call, in order
    pub all_literal_args: Vec<Node>,
}

/// AnalyzeSchemaUnionOfLiterals finds all Schema.Union(...) calls where every argument
/// is a Schema.Literal(...) call, returning matches with captured nodes for diagnostics and fixes.
// Go: rules/schema_union_of_literals.go AnalyzeSchemaUnionOfLiterals
pub fn analyze_schema_union_of_literals(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<SchemaUnionOfLiteralsMatch> {
    // V3-only rule
    if tp.supported_effect_version() != EffectMajorVersion::V3 {
        return Vec::new();
    }

    let mut matches = Vec::new();

    let mut node_to_visit: Vec<Node> = Vec::new();
    sf.for_each_child(|child| {
        node_to_visit.push(child);
        false
    });

    while let Some(node) = node_to_visit.pop() {
        if node.kind() == SyntaxKind::CallExpression {
            let (m, ok) = analyze_schema_union_of_literals_node(tp, sf, node);
            if ok {
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

/// analyzeSchemaUnionOfLiteralsNode checks if a call expression is Schema.Union(...)
/// where all arguments are Schema.Literal(...) calls.
// Go: rules/schema_union_of_literals.go analyzeSchemaUnionOfLiteralsNode
fn analyze_schema_union_of_literals_node(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
) -> (SchemaUnionOfLiteralsMatch, bool) {
    let call = node;

    // Check if this is Schema.Union
    if !tp.is_node_reference_to_effect_schema_module_api(call.expression(), "Union") {
        return (SchemaUnionOfLiteralsMatch::default(), false);
    }

    // Must have at least 2 arguments
    if call.argument_list().is_nil() || call.argument_list().nodes().len() < 2 {
        return (SchemaUnionOfLiteralsMatch::default(), false);
    }

    let mut first_literal_expression = Node::NIL;
    let mut all_literal_args: Vec<Node> = Vec::new();

    // Check that every argument is a call expression referencing Schema.Literal
    for (i, arg) in call.argument_list().nodes().iter().enumerate() {
        if arg.is_nil() || arg.kind() != SyntaxKind::CallExpression {
            return (SchemaUnionOfLiteralsMatch::default(), false);
        }
        let arg_call = arg;
        if !tp.is_node_reference_to_effect_schema_module_api(arg_call.expression(), "Literal") {
            return (SchemaUnionOfLiteralsMatch::default(), false);
        }

        if i == 0 {
            first_literal_expression = arg_call.expression();
        }

        // Collect all arguments from this Schema.Literal(...) call
        if arg_call.argument_list().is_some() {
            all_literal_args.extend(arg_call.argument_list().nodes().iter());
        }
    }

    (
        SchemaUnionOfLiteralsMatch {
            source_file: sf,
            location: get_error_range_for_node(sf, node),
            union_call_node: node,
            first_literal_expression,
            all_literal_args,
        },
        true,
    )
}
