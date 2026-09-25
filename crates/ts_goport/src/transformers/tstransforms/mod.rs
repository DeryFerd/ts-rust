//! Go package `transformers/tstransforms`: the TypeScript-only script
//! transforms (type erasure, import elision, runtime syntax, legacy
//! decorators and decorator metadata).
//!
//! PORT: Go embeds `transformers.Transformer`, which owns one root visitor
//! (`tx.Visitor()`) whose `Visit` is `tx.visit`. Here each transformer
//! implements `TransformerVisit`, and [`TxVisit`] adds the Go
//! `tx.Visitor().X(...)` helpers on top of it. Go
//! `tx.Visitor().VisitNode(n)` is `self.visit_node(n)`.

use crate::prelude::*;
use crate::transformers::transformer::TransformerVisit;

pub mod import_elision;
pub mod legacy_decorators;
pub mod metadata;
pub mod runtime_syntax;
pub mod type_eraser;
pub mod type_serializer;
pub mod utilities;

pub use import_elision::{ImportElisionTransformer, new_import_elision_transformer};
pub use legacy_decorators::{LegacyDecoratorsTransformer, new_legacy_decorators_transformer};
pub use metadata::{MetadataTransformer, new_metadata_transformer};
pub use runtime_syntax::{RuntimeSyntaxTransformer, new_runtime_syntax_transformer};
pub use type_eraser::{TypeEraserTransformer, new_type_eraser_transformer};
pub use type_serializer::get_set_accessor_value_parameter;

/// Go `tx.Visitor().X(...)` helpers over the shared root visitor
/// (`TransformerVisit::with_visitor`).
pub(crate) trait TxVisit: TransformerVisit {
    /// Go `tx.Visitor().VisitNode(node)`.
    fn visit_node(&mut self, node: Node) -> Node {
        self.with_visitor(|v| v.visit_node(node))
    }

    /// Go `tx.Visitor().VisitNodes(nodes)`.
    fn visit_nodes(&mut self, nodes: NodeList) -> NodeList {
        self.with_visitor(|v| v.visit_nodes(nodes))
    }

    /// Go `tx.Visitor().VisitModifiers(nodes)`.
    fn visit_modifiers(&mut self, nodes: ModifierList) -> ModifierList {
        self.with_visitor(|v| v.visit_modifiers(nodes))
    }

    /// Go `tx.Visitor().VisitSlice(nodes)`.
    fn visit_slice(&mut self, nodes: &[Node]) -> (Vec<Node>, bool) {
        self.with_visitor(|v| v.visit_slice(nodes))
    }

    /// Go `tx.Visitor().VisitEachChild(node)`.
    fn visit_each_child(&mut self, node: Node) -> Node {
        self.with_visitor(|v| v.visit_each_child(node))
    }

    /// Go `tx.EmitContext().VisitFunctionBody(node, tx.Visitor())`.
    fn visit_function_body(&mut self, node: Node) -> Node {
        let emit_context = self.emit_context_rc();
        self.with_visitor(|v| emit_context.visit_function_body(node, v))
    }

    /// Go `tx.EmitContext().VisitParameters(nodes, tx.Visitor())`.
    fn visit_parameters(&mut self, nodes: NodeList) -> NodeList {
        let emit_context = self.emit_context_rc();
        self.with_visitor(|v| emit_context.visit_parameters(nodes, v))
    }
}

impl<T: TransformerVisit> TxVisit for T {}
