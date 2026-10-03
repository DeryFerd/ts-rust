//! Port of Go `transformers/estransforms/taggedtemplate.go`.

use super::contract::{TransformOptions, TransformerBox};
use super::utilities::{TxVisitors, impl_es_transformer, source_file_is_external_module};
use crate::prelude::*;
use crate::printer::EmitContext;
use crate::printer::factory::NodeFactory;

// Go: transformers/estransforms/taggedtemplate.go:13 newlineNormalizer
fn newline_normalizer_replace(text: &str) -> String {
    text.replace("\r\n", "\n").replace('\r', "\n")
}

// Go: transformers/estransforms/taggedtemplate.go:15 taggedTemplateTransformer
pub struct TaggedTemplateTransformer {
    emit_context: Rc<EmitContext>,
    current_source_file: Node,

    tagged_template_string_declarations: Vec<Node>,
}

impl_es_transformer!(TaggedTemplateTransformer);

// Go: transformers/estransforms/taggedtemplate.go:22 newTaggedTemplateLiftRestrictionTransformer
pub fn new_tagged_template_lift_restriction_transformer(
    opts: &TransformOptions,
) -> Option<TransformerBox> {
    Some(Box::new(TaggedTemplateTransformer {
        emit_context: opts.context.clone(),
        current_source_file: Node::NIL,
        tagged_template_string_declarations: Vec::new(),
    }))
}

impl TaggedTemplateTransformer {
    // Go: transformers/estransforms/taggedtemplate.go:27 taggedTemplateTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_INVALID_TEMPLATE_ESCAPE)
        {
            return node;
        }
        match node.kind() {
            SyntaxKind::SourceFile => self.visit_source_file(node),
            SyntaxKind::TaggedTemplateExpression => self.visit_tagged_template_expression(node),
            _ => self.visit_each_child(node),
        }
    }

    // Go: transformers/estransforms/taggedtemplate.go:41 taggedTemplateTransformer.visitSourceFile
    fn visit_source_file(&mut self, node: Node) -> Node {
        self.current_source_file = node;
        self.tagged_template_string_declarations = Vec::new();
        let mut visited = self.visit_each_child(node);

        let ec = self.ec();
        let f = ec.factory();
        if !self.tagged_template_string_declarations.is_empty() {
            let mut statements: Vec<Node> = visited.statements().to_vec();
            statements.push(f.new_variable_statement(
                ModifierList::NIL, /*modifiers*/
                f.new_variable_declaration_list(
                    f.new_node_list(&self.tagged_template_string_declarations),
                    NodeFlags::NONE,
                ),
            ));
            let stmt_list = f.new_node_list_with_loc(&statements, node.statement_list().loc());
            visited = f.update_source_file(visited, stmt_list, visited.end_of_file_token());
        }

        ec.add_emit_helper(visited, &ec.read_emit_helpers());
        visited
    }

    // Go: transformers/estransforms/taggedtemplate.go:67 taggedTemplateTransformer.visitTaggedTemplateExpression
    fn visit_tagged_template_expression(&mut self, node: Node) -> Node {
        self.process_tagged_template_expression(node)
    }

    // Go: transformers/estransforms/taggedtemplate.go:71 taggedTemplateTransformer.processTaggedTemplateExpression
    fn process_tagged_template_expression(&mut self, node: Node) -> Node {
        let tag = self.visit_node(node.tag());
        let template = node.template();

        if !has_invalid_escape(template) {
            return self.visit_each_child(node);
        }

        let ec = self.ec();
        let f = ec.factory();

        // Build up the template arguments and the raw and cooked strings for the template.
        let mut template_arguments: Vec<Node> = vec![Node::NIL]; // placeholder for the template object
        let mut cooked_strings: Vec<Node> = Vec::new();
        let mut raw_strings: Vec<Node> = Vec::new();

        if is_no_substitution_template_literal(template) {
            cooked_strings.push(create_template_cooked(f, template));
            raw_strings.push(get_raw_literal(f, template));
        } else {
            let head = template.head();
            cooked_strings.push(create_template_cooked(f, head));
            raw_strings.push(get_raw_literal(f, head));
            for span in template.template_spans().nodes().iter() {
                cooked_strings.push(create_template_cooked(f, span.literal()));
                raw_strings.push(get_raw_literal(f, span.literal()));
                template_arguments.push(self.visit_node(span.expression()));
            }
        }

        let helper_call = f.new_template_object_helper(
            f.new_array_literal_expression(f.new_node_list(&cooked_strings), false),
            f.new_array_literal_expression(f.new_node_list(&raw_strings), false),
        );

        // Create a variable to cache the template object if we're in a module.
        // Do not do this in the global scope, as any variable we currently generate could conflict with
        // variables from outside of the current compilation. In the future, we can revisit this behavior.
        if source_file_is_external_module(self.current_source_file) {
            let temp_var = f.new_unique_name("templateObject");
            self.tagged_template_string_declarations
                .push(f.new_variable_declaration(temp_var, Node::NIL, Node::NIL, Node::NIL));
            template_arguments[0] = f.new_logical_or_expression(
                temp_var,
                f.new_assignment_expression(temp_var, helper_call),
            );
        } else {
            template_arguments[0] = helper_call;
        }

        let call = f.new_call_expression(
            tag,
            Node::NIL,     /*questionDotToken*/
            NodeList::NIL, /*typeArguments*/
            f.new_node_list(&template_arguments),
            NodeFlags::NONE,
        );
        set_node_loc(call, node.loc());
        call
    }
}

// Go: transformers/estransforms/taggedtemplate.go:128 createTemplateCooked
// PORT: Go takes the `TemplateLiteralLikeNodeBase`; this takes the node.
fn create_template_cooked(f: &NodeFactory, template: Node) -> Node {
    if template.template_flags().intersects(TokenFlags::IS_INVALID) {
        return f.new_void_zero_expression();
    }
    f.new_string_literal(template.text(), TokenFlags::NONE)
}

// Go: transformers/estransforms/taggedtemplate.go:135 getRawLiteral
fn get_raw_literal(f: &NodeFactory, node: Node) -> Node {
    let mut text = node.raw_text().to_string();
    if text.is_empty() {
        text = get_source_text_of_node_from_source_file(
            get_source_file_of_node(node),
            node,
            false, /*includeTrivia*/
        );
        // text contains the original source, it will also contain quotes ("`"), dollar signs and braces ("${" and "}"),
        // thus we need to remove those characters.
        // First template piece starts with "`", others with "}"
        // Last template piece ends with "`", others with "${"
        let is_last = node.kind() == SyntaxKind::NoSubstitutionTemplateLiteral
            || node.kind() == SyntaxKind::TemplateTail;
        let end_len = if is_last { 1 } else { 2 };
        text = text[1..text.len() - end_len].to_string();
    }

    // Newline normalization:
    // ES6 Spec 11.8.6.1 - Static Semantics of TV's and TRV's
    // <CR><LF> and <CR> LineTerminatorSequences are normalized to <LF> for both TV and TRV.
    let text = newline_normalizer_replace(&text);

    let result = f.new_string_literal(text, TokenFlags::NONE);
    set_node_loc(result, node.loc());
    result
}

// Go: transformers/estransforms/taggedtemplate.go:161 hasInvalidEscape
fn has_invalid_escape(template: Node) -> bool {
    if is_no_substitution_template_literal(template) {
        return template
            .template_flags()
            .intersects(TokenFlags::CONTAINS_INVALID_ESCAPE);
    }
    if template
        .head()
        .template_flags()
        .intersects(TokenFlags::CONTAINS_INVALID_ESCAPE)
    {
        return true;
    }
    for span in template.template_spans().nodes().iter() {
        if span
            .literal()
            .template_flags()
            .intersects(TokenFlags::CONTAINS_INVALID_ESCAPE)
        {
            return true;
        }
    }
    false
}
