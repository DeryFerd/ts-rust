//! Port of Go `transformers/estransforms/usestrict.go`.

use super::contract::{TransformOptions, TransformerBox};
use super::utilities::{
    TxVisitors, impl_es_transformer, source_file_is_external_module, source_file_script_kind,
};
use crate::prelude::*;
use crate::printer::EmitContext;

// Go: transformers/estransforms/usestrict.go:17 useStrictTransformer
pub struct UseStrictTransformer {
    emit_context: Rc<EmitContext>,
    compiler_options: &'static CompilerOptions,
    get_emit_module_format_of_file: Rc<dyn Fn(Node) -> ModuleKind>,
}

impl_es_transformer!(UseStrictTransformer);

// Go: transformers/estransforms/usestrict.go:9 NewUseStrictTransformer
pub fn new_use_strict_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    Some(Box::new(UseStrictTransformer {
        emit_context: opts.context.clone(),
        compiler_options: opts.compiler_options,
        get_emit_module_format_of_file: opts.get_emit_module_format_of_file.clone(),
    }))
}

impl UseStrictTransformer {
    // Go: transformers/estransforms/usestrict.go:23 useStrictTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        if node.kind() != SyntaxKind::SourceFile {
            return node;
        }
        self.visit_source_file(node)
    }

    // Go: transformers/estransforms/usestrict.go:30 useStrictTransformer.visitSourceFile
    fn visit_source_file(&mut self, node: Node) -> Node {
        if source_file_script_kind(node) == ScriptKind::JSON {
            return node;
        }

        let is_external_module = source_file_is_external_module(node);
        let module_kind = self.compiler_options.get_emit_module_kind();
        let format = (self.get_emit_module_format_of_file)(node);

        // ESM is always strict. If the file is ESM, and CJS emit
        // has not been requested, then skip adding "use strict".
        if is_external_module
            && module_kind >= ModuleKind::ES2015
            && (module_kind == ModuleKind::PRESERVE || format >= ModuleKind::ES2015)
        {
            return node;
        }

        let ec = self.ec();
        let f = ec.factory();
        let statements = f.ensure_use_strict(&node.statements().to_vec());
        let statement_list = f.new_node_list_with_loc(&statements, node.statement_list().loc());
        f.update_source_file(node, statement_list, node.end_of_file_token())
    }
}
