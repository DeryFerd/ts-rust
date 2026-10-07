//! Port of Effect-TS/tsgo `internal/rules/redundant_schema_tag_identifier.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

pub static REDUNDANT_SCHEMA_TAG_IDENTIFIER: Rule = Rule {
    name: "redundantSchemaTagIdentifier",
    group: "style",
    description: "Suggests removing redundant identifier argument when it equals the tag value in Schema.TaggedClass/TaggedError/TaggedRequest",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377045],
    run: run_redundant_schema_tag_identifier,
};

fn run_redundant_schema_tag_identifier(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_redundant_schema_tag_identifier(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        if m.key_string_literal.kind() != SyntaxKind::StringLiteral {
            continue;
        }
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Identifier_0_is_redundant_since_it_equals_the_tag_value_effect_redundantSchemaTagIdentifier,
            Vec::new(),
            vec![m.key_string_literal.text().to_string()],
        ));
    }
    diags
}

// RedundantSchemaTagIdentifierMatch holds the AST nodes needed by both the diagnostic rule
// and the quick-fix for the redundantSchemaTagIdentifier pattern.
#[derive(Clone, Debug)]
pub struct RedundantSchemaTagIdentifierMatch {
    pub source_file: Node,
    /// Pre-computed error range for the diagnostic (on KeyStringLiteral)
    pub location: TextRange,
    /// The redundant identifier string literal in the inner call
    pub key_string_literal: Node,
}

// AnalyzeRedundantSchemaTagIdentifier finds all class declarations where the identifier
// string literal equals the tag value in Schema.TaggedClass/TaggedError/TaggedRequest.
pub fn analyze_redundant_schema_tag_identifier(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<RedundantSchemaTagIdentifierMatch> {
    let mut matches = Vec::new();

    let mut node_to_visit: Vec<Node> = Vec::new();
    sf.for_each_child(|child| {
        node_to_visit.push(child);
        false
    });

    while let Some(node) = node_to_visit.pop() {
        if node.kind() == SyntaxKind::ClassDeclaration {
            if let Some(m) = analyze_redundant_schema_tag_identifier_node(tp, sf, node) {
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

fn analyze_redundant_schema_tag_identifier_node(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
) -> Option<RedundantSchemaTagIdentifierMatch> {
    // Try ExtendsSchemaTaggedClass, then TaggedError, then TaggedRequest (short-circuit on first match)
    let mut result = tp.extends_schema_tagged_class(node);
    if result.is_none() {
        result = tp.extends_schema_tagged_error(node);
    }
    if result.is_none() {
        result = tp.extends_schema_tagged_request(node);
    }
    let result = result?;

    // Both key and tag must be present and must be string literals
    if result.key_string_literal.is_nil() || result.tag_string_literal.is_nil() {
        return None;
    }
    if result.key_string_literal.kind() != SyntaxKind::StringLiteral
        || result.tag_string_literal.kind() != SyntaxKind::StringLiteral
    {
        return None;
    }

    let key_text = result.key_string_literal.text();
    let tag_text = result.tag_string_literal.text();

    if key_text != tag_text {
        return None;
    }

    Some(RedundantSchemaTagIdentifierMatch {
        source_file: sf,
        location: get_error_range_for_node(sf, result.key_string_literal),
        key_string_literal: result.key_string_literal,
    })
}
