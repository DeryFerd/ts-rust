//! Port of Go `transformers/estransforms/optionalcatch.go`.

use super::contract::{TransformOptions, TransformerBox};
use super::utilities::{TxVisitors, impl_es_transformer};
use crate::prelude::*;
use crate::printer::EmitContext;

// Go: transformers/estransforms/optionalcatch.go:8 optionalCatchTransformer
pub struct OptionalCatchTransformer {
    emit_context: Rc<EmitContext>,
}

impl_es_transformer!(OptionalCatchTransformer);

impl OptionalCatchTransformer {
    // Go: transformers/estransforms/optionalcatch.go:12 optionalCatchTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_MISSING_CATCH_CLAUSE_VARIABLE)
        {
            return node;
        }
        match node.kind() {
            SyntaxKind::CatchClause => self.visit_catch_clause(node),
            _ => self.visit_each_child(node),
        }
    }

    // Go: transformers/estransforms/optionalcatch.go:24 optionalCatchTransformer.visitCatchClause
    fn visit_catch_clause(&mut self, node: Node) -> Node {
        if node.variable_declaration().is_nil() {
            let ec = self.ec();
            let f = ec.factory();
            let declaration =
                f.new_variable_declaration(f.new_temp_variable(), Node::NIL, Node::NIL, Node::NIL);
            // PORT: Go calls `ch.Visitor().Visit(node.Block)`, the raw callback.
            let block = self.visit(node.block());
            return f.new_catch_clause(declaration, block);
        }
        self.visit_each_child(node)
    }
}

// Go: transformers/estransforms/optionalcatch.go:34 newOptionalCatchTransformer
pub fn new_optional_catch_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    Some(Box::new(OptionalCatchTransformer {
        emit_context: opts.context.clone(),
    }))
}
