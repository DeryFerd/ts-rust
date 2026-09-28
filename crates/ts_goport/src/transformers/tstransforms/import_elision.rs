//! Port of `transformers/tstransforms/importelision.go`.

use super::TxVisit;
use crate::prelude::*;
use crate::transformers::transformer::{
    TransformOptions, Transformer, TransformerBox, TransformerVisit,
};

// Go: transformers/tstransforms/importelision.go:10 ImportElisionTransformer
pub struct ImportElisionTransformer {
    emit_context: Rc<EmitContext>,
    compiler_options: &'static CompilerOptions,
    current_source_file: Node,
    emit_resolver: Rc<dyn EmitResolver>,
}

// Go: transformers/tstransforms/importelision.go:17 NewImportElisionTransformer
// PORT: Go never returns nil here. The result is an `Option` so the
// constructor has the `TransformerFactory` shape.
pub fn new_import_elision_transformer(opt: &TransformOptions) -> Option<TransformerBox> {
    let compiler_options = opt.compiler_options;
    let emit_context = opt.context.clone();
    if compiler_options.verbatim_module_syntax.is_true() {
        panic!("ImportElisionTransformer should not be used with VerbatimModuleSyntax");
    }
    let tx = ImportElisionTransformer {
        emit_context,
        compiler_options,
        current_source_file: Node::NIL,
        emit_resolver: opt.emit_resolver.clone(),
    };
    Some(Box::new(tx))
}

impl Transformer for ImportElisionTransformer {
    fn emit_context(&self) -> &Rc<EmitContext> {
        &self.emit_context
    }

    fn transform_source_file(&mut self, file: Node) -> Node {
        self.visit_source_file_root(file)
    }
}

impl TransformerVisit for ImportElisionTransformer {
    fn emit_context_rc(&self) -> Rc<EmitContext> {
        self.emit_context.clone()
    }

    // Go: transformers/tstransforms/importelision.go:27 ImportElisionTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        // PORT: Go also tests `tx.emitResolver != nil`; the Rust transformer
        // always has one.
        if is_source_file(node) {
            let original = self.emit_context.most_original(node);
            self.emit_resolver
                .mark_linked_references_recursively(original);
        }

        let ec = self.emit_context.clone();
        let f = ec.factory();
        match node.kind() {
            SyntaxKind::ImportEqualsDeclaration => {
                if is_external_module_import_equals_declaration(node) {
                    if !self.should_emit_alias_declaration(node) {
                        return Node::NIL;
                    }
                } else if !self.should_emit_import_equals_declaration(node) {
                    return Node::NIL;
                }
                self.visit_each_child(node)
            }
            SyntaxKind::ImportDeclaration => {
                // Do not elide a side-effect only import declaration.
                //  import "foo";
                if node.import_clause().is_some() {
                    let import_clause = self.visit_node(node.import_clause());
                    if import_clause.is_nil() {
                        return Node::NIL;
                    }
                    let attributes = self.visit_node(node.attributes());
                    return f.update_import_declaration(
                        node,
                        node.modifiers(),
                        import_clause,
                        node.module_specifier(),
                        attributes,
                    );
                }
                self.visit_each_child(node)
            }
            SyntaxKind::ImportClause => {
                let name = if self.should_emit_alias_declaration(node) {
                    node.name()
                } else {
                    Node::NIL
                };
                let named_bindings = self.visit_node(node.named_bindings());
                if name.is_nil() && named_bindings.is_nil() {
                    // all import bindings were elided
                    return Node::NIL;
                }
                f.update_import_clause(node, node.phase_modifier(), name, named_bindings)
            }
            SyntaxKind::NamespaceImport => {
                if !self.should_emit_alias_declaration(node) {
                    // elide unused imports
                    return Node::NIL;
                }
                node
            }
            SyntaxKind::NamedImports => {
                let elements = self.visit_nodes(node.element_list());
                if elements.nodes().is_empty() {
                    // all import specifiers were elided
                    return Node::NIL;
                }
                f.update_named_imports(node, elements)
            }
            SyntaxKind::ImportSpecifier => {
                if !self.should_emit_alias_declaration(node) {
                    // elide type-only or unused imports
                    return Node::NIL;
                }
                node
            }
            SyntaxKind::ExportAssignment => {
                if !self.compiler_options.verbatim_module_syntax.is_true()
                    && !self.is_value_alias_declaration(node)
                {
                    // elide unused import
                    return Node::NIL;
                }
                self.visit_each_child(node)
            }
            SyntaxKind::ExportDeclaration => {
                let mut export_clause = Node::NIL;
                if node.export_clause().is_some() {
                    export_clause = self.visit_node(node.export_clause());
                    if export_clause.is_nil() {
                        // all export bindings were elided
                        return Node::NIL;
                    }
                }
                let module_specifier = self.visit_node(node.module_specifier());
                let attributes = self.visit_node(node.attributes());
                f.update_export_declaration(
                    node,
                    ModifierList::NIL, /*modifiers*/
                    false,             /*isTypeOnly*/
                    export_clause,
                    module_specifier,
                    attributes,
                )
            }
            SyntaxKind::NamedExports => {
                let elements = self.visit_nodes(node.element_list());
                if elements.nodes().is_empty() {
                    // all export specifiers were elided
                    return Node::NIL;
                }
                f.update_named_exports(node, elements)
            }
            SyntaxKind::ExportSpecifier => {
                if !self.is_value_alias_declaration(node) {
                    // elide unused export
                    return Node::NIL;
                }
                node
            }
            SyntaxKind::SourceFile => {
                let saved_current_source_file = self.current_source_file;
                self.current_source_file = node;
                let node = self.visit_each_child(node);
                self.current_source_file = saved_current_source_file;
                node
            }
            SyntaxKind::ModuleDeclaration | SyntaxKind::ModuleBlock => self.visit_each_child(node),
            _ => node,
        }
    }
}

impl ImportElisionTransformer {
    // Go: transformers/tstransforms/importelision.go:121 ImportElisionTransformer.shouldEmitAliasDeclaration
    fn should_emit_alias_declaration(&self, node: Node) -> bool {
        is_in_js_file(node) || self.is_referenced_alias_declaration(node)
    }

    // Go: transformers/tstransforms/importelision.go:125 ImportElisionTransformer.shouldEmitImportEqualsDeclaration
    fn should_emit_import_equals_declaration(&self, node: Node) -> bool {
        // preserve old compiler's behavior: emit import declaration (even if we do not consider them referenced) when
        // - current file is not external module
        // - import declaration is top level and target is value imported by entity name
        self.should_emit_alias_declaration(node)
            || (!is_external_module(self.current_source_file)
                && self.is_top_level_value_import_equals_with_entity_name(node))
    }

    // Go: transformers/tstransforms/importelision.go:132 ImportElisionTransformer.isReferencedAliasDeclaration
    fn is_referenced_alias_declaration(&self, node: Node) -> bool {
        let node = self.emit_context.parse_node(node);
        node.is_nil() || self.emit_resolver.is_referenced_alias_declaration(node)
    }

    // Go: transformers/tstransforms/importelision.go:137 ImportElisionTransformer.isValueAliasDeclaration
    fn is_value_alias_declaration(&self, node: Node) -> bool {
        let node = self.emit_context.parse_node(node);
        node.is_nil() || self.emit_resolver.is_value_alias_declaration(node)
    }

    // Go: transformers/tstransforms/importelision.go:142 ImportElisionTransformer.isTopLevelValueImportEqualsWithEntityName
    fn is_top_level_value_import_equals_with_entity_name(&self, node: Node) -> bool {
        let node = self.emit_context.parse_node(node);
        node.is_some()
            && self
                .emit_resolver
                .is_top_level_value_import_equals_with_entity_name(node)
    }
}
