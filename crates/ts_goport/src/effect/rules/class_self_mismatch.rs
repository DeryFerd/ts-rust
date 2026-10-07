//! Port of Effect-TS/tsgo `internal/rules/class_self_mismatch.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// ClassSelfMismatch ensures the Self type parameter matches the class name in
// Effect.Service, Context.Service, Context.Tag, Effect.Tag, Schema.Class,
// Schema.TaggedClass, Schema.TaggedError, Schema.TaggedRequest,
// Schema.RequestClass, and Model.Class declarations.
pub static CLASS_SELF_MISMATCH: Rule = Rule {
    name: "classSelfMismatch",
    group: "correctness",
    description: "Ensures Self type parameter matches the class name in Context/Service/Tag/Schema classes",
    default_severity: Severity::Error,
    supported_effect: &["v3", "v4"],
    codes: &[377046],
    run: run_class_self_mismatch,
};

fn run_class_self_mismatch(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_class_self_mismatch(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::The_Self_type_parameter_for_this_class_should_be_0_effect_classSelfMismatch,
            Vec::new(),
            vec![m.expected_name.clone()],
        ));
    }
    diags
}

// ClassSelfMismatchMatch holds the AST nodes needed by both the diagnostic rule
// and the quick-fix for the classSelfMismatch pattern.
#[derive(Clone, Debug)]
pub struct ClassSelfMismatchMatch {
    /// The source file of the match
    pub source_file: Node,
    /// The pre-computed error range for the selfTypeNode
    pub location: TextRange,
    /// The Self type argument node
    pub self_type_node: Node,
    /// The class name identifier
    pub class_name: Node,
    /// The expected name (from the class declaration)
    pub expected_name: String,
    /// The actual name found in the Self type parameter
    pub actual_name: String,
}

// AnalyzeClassSelfMismatch finds all class declarations where the Self type
// parameter does not match the class name.
pub fn analyze_class_self_mismatch(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<ClassSelfMismatchMatch> {
    let mut matches = Vec::new();

    let mut node_to_visit: Vec<Node> = Vec::new();
    sf.for_each_child(|child| {
        node_to_visit.push(child);
        false
    });

    while let Some(node) = node_to_visit.pop() {
        if node.kind() == SyntaxKind::ClassDeclaration && node.name().is_some() {
            if let Some(m) = check_class_self_mismatch(tp, sf, node) {
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

fn check_class_self_mismatch(
    tp: &mut TypeParser<'_>,
    sf: Node,
    class_node: Node,
) -> Option<ClassSelfMismatchMatch> {
    let self_type_node;
    let class_name;

    // Try extends* functions in order, matching the TS reference
    if let Some(result) = tp.extends_effect_v3_service(class_node) {
        self_type_node = result.self_type_node;
        class_name = result.class_name;
    } else if let Some(result) = tp.extends_context_service(class_node) {
        self_type_node = result.self_type_node;
        class_name = result.class_name;
    } else if let Some(result) = tp.extends_context_tag(class_node) {
        self_type_node = result.self_type_node;
        class_name = result.class_name;
    } else if let Some(result) = tp.extends_effect_tag(class_node) {
        self_type_node = result.self_type_node;
        class_name = result.class_name;
    } else if let Some(result) = tp.extends_schema_class(class_node) {
        self_type_node = result.self_type_node;
        class_name = result.class_name;
    } else if let Some(result) = tp.extends_schema_tagged_class(class_node) {
        self_type_node = result.self_type_node;
        class_name = result.class_name;
    } else if let Some(result) = tp.extends_schema_tagged_error(class_node) {
        self_type_node = result.self_type_node;
        class_name = result.class_name;
    } else if let Some(result) = tp.extends_schema_tagged_request(class_node) {
        self_type_node = result.self_type_node;
        class_name = result.class_name;
    } else if let Some(result) = tp.extends_schema_request_class(class_node) {
        self_type_node = result.self_type_node;
        class_name = result.class_name;
    } else if let Some(result) = tp.extends_effect_sql_model_class(class_node) {
        self_type_node = result.self_type_node;
        class_name = result.class_name;
    } else if let Some(result) = tp.extends_effect_model_class(class_node) {
        self_type_node = result.self_type_node;
        class_name = result.class_name;
    } else {
        self_type_node = Node::NIL;
        class_name = Node::NIL;
    }

    if self_type_node.is_nil() || class_name.is_nil() {
        return None;
    }

    // Extract actual name from the Self type node
    let actual_name = extract_self_type_name(sf, self_type_node);

    // Get expected name from the class name
    let expected_name = get_text_of_node(class_name);

    if actual_name == expected_name {
        return None;
    }

    Some(ClassSelfMismatchMatch {
        source_file: sf,
        location: get_error_range_for_node(sf, self_type_node),
        self_type_node,
        class_name,
        expected_name,
        actual_name,
    })
}

// extractSelfTypeName extracts the name text from a Self type node.
// For TypeReferenceNode with Identifier typeName → identifier text.
// For TypeReferenceNode with QualifiedName typeName → right identifier text.
// Fallback → source text substring between node pos and end.
fn extract_self_type_name(sf: Node, self_type_node: Node) -> String {
    if is_type_reference_node(self_type_node) {
        let type_name = self_type_node.type_name();
        if is_identifier(type_name) {
            return type_name.text().to_string();
        }
        if is_qualified_name(type_name) {
            return type_name.right().text().to_string();
        }
    }
    // Fallback: use source text
    let text = source_file_text(sf);
    let pos = self_type_node.pos();
    let end = self_type_node.end();
    if pos >= 0 && end >= pos && end as usize <= text.len() {
        return text[pos as usize..end as usize].to_string();
    }
    String::new()
}
