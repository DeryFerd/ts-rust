//! Port of Go `transformers/chain.go`.

use crate::prelude::*;

use super::transformer::{TransformOptions, Transformer, TransformerBox, TransformerFactory};

// Go: transformers/chain.go:10 chainedTransformer
pub struct ChainedTransformer {
    emit_context: Rc<EmitContext>,
    components: Vec<TransformerBox>,
}

impl ChainedTransformer {
    // Go: transformers/chain.go:15 chainedTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        if node.kind() != SyntaxKind::SourceFile {
            panic!("Chained transform passed non-sourcefile initial node");
        }
        let mut result = node;
        for t in &mut self.components {
            result = t.transform_source_file(result);
        }
        result
    }
}

impl Transformer for ChainedTransformer {
    fn emit_context(&self) -> &Rc<EmitContext> {
        &self.emit_context
    }

    // Go: transformers/transformer.go:39 TransformSourceFile
    // PORT: Go `tx.visitor.VisitSourceFile(file)` calls `visit` once on the
    // source file and checks that the result is a source file.
    fn transform_source_file(&mut self, file: Node) -> Node {
        let visited = self.visit(file);
        assert!(
            visited.is_some() && visited.kind() == SyntaxKind::SourceFile,
            "VisitSourceFile: the result is not a SourceFile"
        );
        visited
    }
}

// Go: transformers/chain.go:38 Chain
// Chains transforms in left-to-right order, running them one at a time in order (as opposed to interleaved at each node)
// - the resulting combined transform only operates on SourceFile nodes
// PORT: Go returns a new factory. Rust closures cannot be named in a
// `const`, so this applies the chained factories to `opt` directly. A caller
// writes the Go factory as a named fn:
// `fn new_es2021_transformer(o: &TransformOptions) -> Option<TransformerBox> { chain(o, &[..]) }`.
pub fn chain(opt: &TransformOptions, transforms: &[&TransformerFactory]) -> Option<TransformerBox> {
    if transforms.len() < 2 {
        if transforms.is_empty() {
            panic!("Expected some number of transforms to chain, but got none");
        }
        return transforms[0](opt);
    }
    let mut constructed: Vec<TransformerBox> = Vec::with_capacity(transforms.len());
    for t in transforms {
        // TODO: flatten nested chains?
        if let Some(result) = t(opt) {
            constructed.push(result);
        }
    }
    match constructed.len() {
        0 => return None,
        1 => return constructed.pop(),
        _ => {}
    }
    Some(Box::new(ChainedTransformer {
        emit_context: opt.context.clone(),
        components: constructed,
    }))
}
