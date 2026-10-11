//! Port of Effect-TS/tsgo `internal/completion` (effect-tsgo 0.51.1,
//! `47cb1ed7`): the custom completion type (`completion.go`), the context a
//! completion runs with (`context.go`) and the cursor position parsers
//! (`position.go`). The completions are in `effect::ls::completions`.

use crate::effect::typeparser::TypeParser;
use crate::ls::prelude::*;

// Go: completion/completion.go:13 Completion
/// Completion defines a custom completion provider.
/// Each completion has a name, description, and a Run function that returns
/// additional completion items to merge into the existing completion list.
pub struct Completion {
    /// Name is the unique identifier for this completion (e.g., "genFunctionStar").
    pub name: &'static str,

    /// Description explains what this completion provides (used in documentation/tooling).
    pub description: &'static str,

    /// Run executes the completion and returns additional completion items.
    /// The Context provides access to the source file, cursor position,
    /// existing completion items, and type checker.
    /// Return an empty list if no custom completions are applicable.
    pub run: fn(&mut CompletionContext<'_, '_>) -> Vec<lsproto::CompletionItem>,
}

// Go: completion/context.go:16 Context
/// Context bundles the completion request data and provides helpers for completion implementations.
/// It provides access to the source file, cursor position, existing completion items,
// PORT: Go `completion.Context`; the Rust name avoids the Go
// `context.Context` port (`Context`), as `FixableContext` does. Go's
// `Checker` is `tp.checker`. Go keeps the language service in a private
// field that nothing reads; the port does not keep it.
pub struct CompletionContext<'a, 'c> {
    pub source_file: Node,
    pub position: i32,
    pub existing_items: &'a [lsproto::CompletionItem],
    pub program: &'a compiler::NewProgram,
    pub tp: &'a mut TypeParser<'c>,

    pub context: &'a Context,
}

// Go: completion/context.go:29 NewContext
/// NewContext creates a completion Context from the completion callback parameters.
// PORT: Go panics on a nil program or checker; Rust references are never
// nil. Go also takes the language service and the checker (the checker is
// `tp.checker`).
pub fn new_context<'a, 'c>(
    ctx: &'a Context,
    source_file: Node,
    position: i32,
    existing_items: &'a [lsproto::CompletionItem],
    program: &'a compiler::NewProgram,
    tp: &'a mut TypeParser<'c>,
) -> CompletionContext<'a, 'c> {
    CompletionContext {
        source_file,
        position,
        existing_items,
        program,
        tp,
        context: ctx,
    }
}

// Go: completion/position.go:11 ExtendsClassCompletionData
/// ExtendsClassCompletionData holds the parsed context for a completion
/// triggered in the extends clause of a class declaration.
#[derive(Clone, Copy, Debug)]
pub struct ExtendsClassCompletionData {
    pub accessed_object: Node,
    pub class_declaration: Node,
    pub class_name: Node,
    pub replacement_start: i32,
    pub replacement_length: i32,
}

// Go: completion/position.go:20 AccessedExpressionResult
/// AccessedExpressionResult is the result from parsing an accessed expression at a cursor position.
#[derive(Clone, Copy, Debug)]
pub struct AccessedExpressionResult {
    pub accessed_object: Node,
    pub outer_node: Node,
    pub replacement_start: i32,
    pub replacement_length: i32,
}

// Go: completion/position.go:32 ParseAccessedExpressionForCompletion
/// ParseAccessedExpressionForCompletion finds the accessed expression at the given cursor position.
/// It handles three cases:
///   - extends Schema.Tag| — cursor after a property name in a PropertyAccessExpression
///   - extends Schema.| — cursor right after the dot
///   - extends Schema| — cursor after a standalone identifier
pub fn parse_accessed_expression_for_completion(
    sf: Node,
    position: i32,
) -> Option<AccessedExpressionResult> {
    let preceding_token = astnav::find_preceding_token(sf, position);
    if preceding_token.is_nil() {
        return None;
    }

    let accessed_object;
    let outer_node;
    let replacement_start;
    let replacement_length;

    let parent = preceding_token.parent();
    if is_identifier(preceding_token) && parent.is_some() && is_property_access_expression(parent) {
        // extends Schema.Tag|
        let span_start = astnav::get_start_of_node(parent, sf, false);
        replacement_start = span_start;
        replacement_length = preceding_token.end() - span_start;
        accessed_object = parent.expression();
        outer_node = parent;
    } else if is_token_kind(preceding_token.kind())
        && preceding_token.kind() == SyntaxKind::DotToken
        && parent.is_some()
        && is_property_access_expression(parent)
    {
        // extends Schema.|
        let span_start = astnav::get_start_of_node(parent, sf, false);
        replacement_start = span_start;
        replacement_length = preceding_token.end() - span_start;
        accessed_object = parent.expression();
        outer_node = parent;
    } else if is_identifier(preceding_token) && parent.is_some() {
        // extends Schema|
        let span_start = astnav::get_start_of_node(preceding_token, sf, false);
        replacement_start = span_start;
        replacement_length = preceding_token.end() - span_start;
        accessed_object = preceding_token;
        outer_node = preceding_token;
    } else {
        return None;
    }

    // Skip if accessed object is inside an import declaration
    let import_decl = find_ancestor(accessed_object, is_import_declaration);
    if import_decl.is_some() {
        return None;
    }

    Some(AccessedExpressionResult {
        accessed_object,
        outer_node,
        replacement_start,
        replacement_length,
    })
}

// Go: completion/position.go:90 ParseDataForExtendsClassCompletion
/// ParseDataForExtendsClassCompletion parses position context for a completion in the
/// extends clause of a class declaration. It calls ParseAccessedExpressionForCompletion
/// and then walks up the AST to find the enclosing ClassDeclaration.
pub fn parse_data_for_extends_class_completion(
    sf: Node,
    position: i32,
) -> Option<ExtendsClassCompletionData> {
    let result = parse_accessed_expression_for_completion(sf, position)?;

    if !is_identifier(result.accessed_object) {
        return None;
    }

    // Walk up from OuterNode.parent through ExpressionWithTypeArguments and HeritageClause
    let mut class_decl = result.outer_node.parent();
    while class_decl.is_some()
        && (is_expression_with_type_arguments(class_decl) || is_heritage_clause(class_decl))
    {
        if class_decl.parent().is_nil() {
            break;
        }
        class_decl = class_decl.parent();
    }

    if class_decl.is_nil() || !is_class_declaration(class_decl) {
        return None;
    }

    let class_name = class_decl.name();
    if class_name.is_nil() {
        return None;
    }

    Some(ExtendsClassCompletionData {
        accessed_object: result.accessed_object,
        class_declaration: class_decl,
        class_name,
        replacement_start: result.replacement_start,
        replacement_length: result.replacement_length,
    })
}

impl ExtendsClassCompletionData {
    // Go: completion/position.go:129 AccessedObjectText
    /// AccessedObjectText returns the text of the accessed object node.
    #[must_use]
    pub fn accessed_object_text(&self) -> String {
        get_text_of_node(self.accessed_object)
    }

    // Go: completion/position.go:134 ClassNameText
    /// ClassNameText returns the text of the class name node.
    #[must_use]
    pub fn class_name_text(&self) -> String {
        get_text_of_node(self.class_name)
    }
}

// Go: completion/position_test.go
#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::parser::{SourceFileParseOptions, parse_source_file};

    // Go: completion/position_test.go:12 parseSource
    // PORT: the parser takes `&'static str`, so the tests pass literals.
    fn parse_source(source: &'static str) -> Node {
        parse_source_file(
            &SourceFileParseOptions {
                file_name: "/test.ts".to_string(),
                ..Default::default()
            },
            source,
            ScriptKind::TS,
        )
        .root
    }

    /// Go `len(source)` as a position.
    fn len(source: &str) -> i32 {
        i32::try_from(source.len()).expect("a short source")
    }

    // Go: completion/position_test.go:18 TestParseDataForExtendsClassCompletion_AfterDot
    #[test]
    fn test_parse_data_for_extends_class_completion_after_dot() {
        // class Foo extends Schema.| (cursor after the dot)
        let source = "class Foo extends Schema.";
        let sf = parse_source(source);
        let data = parse_data_for_extends_class_completion(sf, len(source))
            .expect("expected non-nil result for 'class Foo extends Schema.'");
        assert_eq!(data.accessed_object_text(), "Schema");
        assert_eq!(data.class_name_text(), "Foo");
    }

    // Go: completion/position_test.go:37 TestParseDataForExtendsClassCompletion_AfterPropertyName
    #[test]
    fn test_parse_data_for_extends_class_completion_after_property_name() {
        // class Foo extends Schema.Class| (cursor after Class)
        let source = "class Foo extends Schema.Class";
        let sf = parse_source(source);
        let data = parse_data_for_extends_class_completion(sf, len(source))
            .expect("expected non-nil result for 'class Foo extends Schema.Class'");
        assert_eq!(data.accessed_object_text(), "Schema");
        assert_eq!(data.class_name_text(), "Foo");
    }

    // Go: completion/position_test.go:56 TestParseDataForExtendsClassCompletion_StandaloneIdentifier
    #[test]
    fn test_parse_data_for_extends_class_completion_standalone_identifier() {
        // class Foo extends Schema| (cursor after standalone identifier)
        let source = "class Foo extends Schema";
        let sf = parse_source(source);
        let data = parse_data_for_extends_class_completion(sf, len(source))
            .expect("expected non-nil result for 'class Foo extends Schema'");
        assert_eq!(get_text_of_node(data.accessed_object), "Schema");
        assert_eq!(data.class_name_text(), "Foo");
    }

    // Go: completion/position_test.go:76 TestParseDataForExtendsClassCompletion_NonClassContext
    #[test]
    fn test_parse_data_for_extends_class_completion_non_class_context() {
        // Not in a class extends clause
        let source = "const x = Schema.Class";
        let sf = parse_source(source);
        assert!(
            parse_data_for_extends_class_completion(sf, len(source)).is_none(),
            "expected nil result for non-class context"
        );
    }

    // Go: completion/position_test.go:89 TestParseDataForExtendsClassCompletion_InsideImportDeclaration
    #[test]
    fn test_parse_data_for_extends_class_completion_inside_import_declaration() {
        let source = r#"import { Schema } from "effect""#;
        let sf = parse_source(source);
        // Position after "Schema" inside the import
        let pos = len("import { Schema");
        assert!(
            parse_data_for_extends_class_completion(sf, pos).is_none(),
            "expected nil result for position inside import declaration"
        );
    }

    // Go: completion/position_test.go:102 TestParseDataForExtendsClassCompletion_ReplacementSpan
    #[test]
    fn test_parse_data_for_extends_class_completion_replacement_span() {
        let source = "class Foo extends Schema.Class";
        let sf = parse_source(source);
        let data = parse_data_for_extends_class_completion(sf, len(source))
            .expect("expected non-nil result");
        // The replacement span should cover "Schema.Class"
        assert!(
            data.replacement_length > 0,
            "expected positive ReplacementLength, got {}",
            data.replacement_length
        );
        let start = usize::try_from(data.replacement_start).expect("a start");
        let end = start + usize::try_from(data.replacement_length).expect("a length");
        assert_eq!(&source[start..end], "Schema.Class");
    }
}
