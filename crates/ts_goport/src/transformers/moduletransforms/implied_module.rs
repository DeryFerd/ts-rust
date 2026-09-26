//! Port of Go `transformers/moduletransforms/impliedmodule.go`.

use super::commonjs_module::new_commonjs_module_transformer;
use super::es_module::new_es_module_transformer;
use super::utilities::is_declaration_file_of;
use crate::ast::visitor::NodeVisitor;
use crate::prelude::*;
use crate::transformers::transformer::{
    TransformOptions, TransformReferenceResolver, Transformer, TransformerBox,
};

// Go: transformers/moduletransforms/impliedmodule.go:10 ImpliedModuleTransformer
pub struct ImpliedModuleTransformer {
    emit_context: Rc<EmitContext>,
    opts: TransformOptions,
    #[allow(dead_code)]
    resolver: Rc<dyn TransformReferenceResolver>,
    get_emit_module_format_of_file: Rc<dyn Fn(Node) -> ModuleKind>,
    cjs_transformer: Option<TransformerBox>,
    esm_transformer: Option<TransformerBox>,
}

// Go: transformers/moduletransforms/impliedmodule.go:19 NewImpliedModuleTransformer
pub fn new_implied_module_transformer(opts: &TransformOptions) -> TransformerBox {
    Box::new(ImpliedModuleTransformer {
        emit_context: opts.context.clone(),
        opts: opts.clone(),
        resolver: opts.resolver.clone(),
        get_emit_module_format_of_file: opts.get_emit_module_format_of_file.clone(),
        cjs_transformer: None,
        esm_transformer: None,
    })
}

impl Transformer for ImpliedModuleTransformer {
    fn emit_context(&self) -> &Rc<EmitContext> {
        &self.emit_context
    }

    // Go: transformers/transformer.go:39 Transformer.TransformSourceFile
    fn transform_source_file(&mut self, file: Node) -> Node {
        let emit_context = self.emit_context.clone();
        let mut visitor = emit_context.new_node_visitor(
            |node, v: &mut NodeVisitor<'_, &mut ImpliedModuleTransformer>| v.ctx.visit(node),
            self,
        );
        visitor.visit_source_file(file)
    }
}

impl ImpliedModuleTransformer {
    // Go: transformers/moduletransforms/impliedmodule.go:24 ImpliedModuleTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        match node.kind() {
            SyntaxKind::SourceFile => self.visit_source_file(node),
            _ => node,
        }
    }

    // Go: transformers/moduletransforms/impliedmodule.go:32 ImpliedModuleTransformer.visitSourceFile
    fn visit_source_file(&mut self, node: Node) -> Node {
        if is_declaration_file_of(node) {
            return node;
        }

        let format = (self.get_emit_module_format_of_file)(node);

        let transformer = if format >= ModuleKind::ES2015 {
            if self.esm_transformer.is_none() {
                self.esm_transformer = Some(new_es_module_transformer(&self.opts));
            }
            self.esm_transformer.as_mut()
        } else {
            if self.cjs_transformer.is_none() {
                self.cjs_transformer = Some(new_commonjs_module_transformer(&self.opts));
            }
            self.cjs_transformer.as_mut()
        };

        transformer
            .expect("module transformer was just created")
            .transform_source_file(node)
    }
}
