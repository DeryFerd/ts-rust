//! Port of `transformers/tstransforms/legacydecorators.go`.

use super::TxVisit;
use crate::prelude::*;
use crate::printer::factory::{
    AssignedNameOptions, NameOptions, NodeFactory as PrinterNodeFactory,
};
use crate::transformers::transformer::{
    TransformOptions, TransformReferenceResolver, Transformer, TransformerBox, TransformerVisit,
};
use crate::transformers::utilities::{
    is_generated_identifier, is_simple_inlineable_expression, move_range_past_modifiers,
};

// Go: transformers/tstransforms/legacydecorators.go:12 LegacyDecoratorsTransformer
pub struct LegacyDecoratorsTransformer {
    emit_context: Rc<EmitContext>,
    language_version: ScriptTarget,
    reference_resolver: Rc<dyn TransformReferenceResolver>,

    /// A map that keeps track of aliases created for classes with decorators to avoid issues
    /// with the double-binding behavior of classes.
    // PORT: `None` is a nil Go map.
    class_aliases: Option<FxHashMap<Node, Node>>,
    enclosing_classes: Vec<Node>,
}

// Go: transformers/tstransforms/legacydecorators.go:25 NewLegacyDecoratorsTransformer
// PORT: Go never returns nil here. The result is an `Option` so the
// constructor has the `TransformerFactory` shape.
pub fn new_legacy_decorators_transformer(opt: &TransformOptions) -> Option<TransformerBox> {
    let tx = LegacyDecoratorsTransformer {
        emit_context: opt.context.clone(),
        language_version: opt.compiler_options.get_emit_script_target(),
        reference_resolver: opt.resolver.clone(),
        class_aliases: None,
        enclosing_classes: Vec::new(),
    };
    Some(Box::new(tx))
}

impl Transformer for LegacyDecoratorsTransformer {
    fn emit_context(&self) -> &Rc<EmitContext> {
        &self.emit_context
    }

    fn transform_source_file(&mut self, file: Node) -> Node {
        self.visit_source_file_root(file)
    }
}

impl TransformerVisit for LegacyDecoratorsTransformer {
    fn emit_context_rc(&self) -> Rc<EmitContext> {
        self.emit_context.clone()
    }

    // Go: transformers/tstransforms/legacydecorators.go:30 LegacyDecoratorsTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        // we have to visit all identifiers in classes, just in case they require substitution
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_DECORATORS)
            && self.enclosing_classes.is_empty()
        {
            return node;
        }

        match node.kind() {
            SyntaxKind::Identifier => self.visit_identifier(node),
            SyntaxKind::PropertyAccessExpression => self.visit_property_access_expression(node),
            // Decorators are elided. They will be emitted as part of `visitClassDeclaration`.
            SyntaxKind::Decorator => Node::NIL,
            SyntaxKind::ClassDeclaration => self.visit_class_declaration(node),
            SyntaxKind::ClassExpression => self.visit_class_expression(node),
            SyntaxKind::Constructor => self.visit_constructor_declaration(node),
            SyntaxKind::MethodDeclaration => self.visit_method_declaration(node),
            SyntaxKind::SetAccessor => self.visit_set_accessor_declaration(node),
            SyntaxKind::GetAccessor => self.visit_get_accessor_declaration(node),
            SyntaxKind::PropertyDeclaration => self.visit_property_declaration(node),
            SyntaxKind::Parameter => self.visit_paramer_declaration(node),
            SyntaxKind::SourceFile => {
                self.class_aliases = Some(FxHashMap::default());
                self.enclosing_classes = Vec::new();
                let result = self.visit_each_child(node);
                let ec = self.emit_context.clone();
                ec.add_emit_helper(result, &ec.read_emit_helpers());
                self.class_aliases = None;
                self.enclosing_classes = Vec::new();
                result
            }
            _ => self.visit_each_child(node),
        }
    }
}

impl LegacyDecoratorsTransformer {
    /// Go `tx.classAliases[node]` (a nil map reads as empty).
    fn class_alias_of(&self, node: Node) -> Option<Node> {
        self.class_aliases
            .as_ref()
            .and_then(|aliases| aliases.get(&node).copied())
    }

    // Go: transformers/tstransforms/legacydecorators.go:73 LegacyDecoratorsTransformer.visitIdentifier
    fn visit_identifier(&mut self, node: Node) -> Node {
        // takes the place of `substituteIdentifier` in the strada transform
        let ec = &self.emit_context;
        for &d in &self.enclosing_classes {
            if let Some(alias) = self.class_alias_of(d) {
                if self
                    .reference_resolver
                    .get_referenced_value_declaration(ec.most_original(node))
                    == ec.most_original(d)
                {
                    return alias;
                }
            }
        }
        node
    }

    // Go: transformers/tstransforms/legacydecorators.go:83 LegacyDecoratorsTransformer.visitPropertyAccessExpression
    fn visit_property_access_expression(&mut self, node: Node) -> Node {
        // Visit the expression but not the name, since property access names should not be substituted.
        // Strada's onSubstituteNode only fires for EmitHint.Expression, which excludes the
        // .name of PropertyAccessExpression.
        let expression = self.visit_node(node.expression());
        if expression != node.expression() {
            return self
                .emit_context
                .factory()
                .update_property_access_expression(
                    node,
                    expression,
                    node.question_dot_token(),
                    node.name(),
                    node.flags(),
                );
        }
        node
    }

    // Go: transformers/tstransforms/legacydecorators.go:118 LegacyDecoratorsTransformer.finishClassElement
    fn finish_class_element(&self, updated: Node, original: Node) -> Node {
        if updated != original {
            // While we emit the source map for the node after skipping decorators and modifiers,
            // we need to emit the comments for the original range.
            self.emit_context.set_comment_range(updated, original.loc());
            self.emit_context
                .set_source_map_range(updated, move_range_past_modifiers(original));
        }
        updated
    }

    // Go: transformers/tstransforms/legacydecorators.go:128 LegacyDecoratorsTransformer.visitParamerDeclaration
    fn visit_paramer_declaration(&mut self, node: Node) -> Node {
        let ec = self.emit_context.clone();
        let f = ec.factory();
        let modifiers = elide_modifiers(f, node.modifiers());
        let name = self.visit_node(node.name());
        let initializer = self.visit_node(node.initializer());
        let updated = f.update_parameter_declaration(
            node,
            modifiers,
            node.dot_dot_dot_token(),
            name,
            Node::NIL,
            Node::NIL,
            initializer,
        );
        if updated != node {
            // While we emit the source map for the node after skipping decorators and modifiers,
            // we need to emit the comments for the original range.
            ec.set_comment_range(updated, node.loc());
            let new_loc = move_range_past_modifiers(node);
            set_node_loc(updated, new_loc);
            ec.set_source_map_range(updated, new_loc);
            ec.set_emit_flags(updated.name(), EmitFlags::NO_TRAILING_SOURCE_MAP);
        }
        updated
    }

    // Go: transformers/tstransforms/legacydecorators.go:153 LegacyDecoratorsTransformer.visitPropertyNameOfClassElement
    /// visitPropertyNameOfClassElement visits the property name of a class element,
    /// for use when emitting property initializers. For a computed property on a node
    /// with decorators, a temporary value is stored for later use.
    fn visit_property_name_of_class_element(&mut self, member: Node) -> Node {
        let name = member.name();
        if is_computed_property_name(name) && has_decorators(member) {
            let expression = self.visit_node(name.expression());
            let inner_expression = skip_partially_emitted_expressions(expression);
            if !is_simple_inlineable_expression(inner_expression) {
                let ec = self.emit_context.clone();
                let f = ec.factory();
                let generated_name = f.new_generated_name_for_node(name);
                ec.add_variable_declaration(generated_name);
                return f.update_computed_property_name(
                    name,
                    f.new_assignment_expression(generated_name, expression),
                );
            }
        }
        self.visit_node(name)
    }

    // Go: transformers/tstransforms/legacydecorators.go:167 LegacyDecoratorsTransformer.visitPropertyDeclaration
    fn visit_property_declaration(&mut self, node: Node) -> Node {
        if node.flags().intersects(NodeFlags::AMBIENT) {
            return Node::NIL;
        }
        if has_syntactic_modifier(node, ModifierFlags::AMBIENT | ModifierFlags::ABSTRACT) {
            return Node::NIL;
        }

        let modifiers = self.visit_modifiers(node.modifiers());
        let name = self.visit_property_name_of_class_element(node);
        let initializer = self.visit_node(node.initializer());
        let updated = self.emit_context.factory().update_property_declaration(
            node,
            modifiers,
            name,
            Node::NIL,
            Node::NIL,
            initializer,
        );
        self.finish_class_element(updated, node)
    }

    // Go: transformers/tstransforms/legacydecorators.go:188 LegacyDecoratorsTransformer.visitGetAccessorDeclaration
    fn visit_get_accessor_declaration(&mut self, node: Node) -> Node {
        let modifiers = self.visit_modifiers(node.modifiers());
        let name = self.visit_property_name_of_class_element(node);
        let parameters = self.visit_nodes(node.parameter_list());
        let body = self.visit_node(node.body());
        let updated = self.emit_context.factory().update_get_accessor_declaration(
            node,
            modifiers,
            name,
            NodeList::NIL,
            parameters,
            Node::NIL,
            Node::NIL,
            body,
        );
        self.finish_class_element(updated, node)
    }

    // Go: transformers/tstransforms/legacydecorators.go:204 LegacyDecoratorsTransformer.visitSetAccessorDeclaration
    fn visit_set_accessor_declaration(&mut self, node: Node) -> Node {
        let modifiers = self.visit_modifiers(node.modifiers());
        let name = self.visit_property_name_of_class_element(node);
        let parameters = self.visit_nodes(node.parameter_list());
        let body = self.visit_node(node.body());
        let updated = self.emit_context.factory().update_set_accessor_declaration(
            node,
            modifiers,
            name,
            NodeList::NIL,
            parameters,
            Node::NIL,
            Node::NIL,
            body,
        );
        self.finish_class_element(updated, node)
    }

    // Go: transformers/tstransforms/legacydecorators.go:220 LegacyDecoratorsTransformer.visitMethodDeclaration
    fn visit_method_declaration(&mut self, node: Node) -> Node {
        let modifiers = self.visit_modifiers(node.modifiers());
        let name = self.visit_property_name_of_class_element(node);
        let parameters = self.visit_nodes(node.parameter_list());
        let body = self.visit_node(node.body());
        let updated = self.emit_context.factory().update_method_declaration(
            node,
            modifiers,
            node.asterisk_token(),
            name,
            Node::NIL,
            NodeList::NIL,
            parameters,
            Node::NIL,
            Node::NIL,
            body,
        );
        self.finish_class_element(updated, node)
    }

    // Go: transformers/tstransforms/legacydecorators.go:238 LegacyDecoratorsTransformer.visitConstructorDeclaration
    fn visit_constructor_declaration(&mut self, node: Node) -> Node {
        let modifiers = self.visit_modifiers(node.modifiers());
        let parameters = self.visit_nodes(node.parameter_list());
        let body = self.visit_node(node.body());
        self.emit_context.factory().update_constructor_declaration(
            node,
            modifiers,
            NodeList::NIL,
            parameters,
            Node::NIL,
            Node::NIL,
            body,
        )
    }

    // Go: transformers/tstransforms/legacydecorators.go:250 LegacyDecoratorsTransformer.visitClassExpression
    fn visit_class_expression(&mut self, node: Node) -> Node {
        // Legacy decorators were not supported on class expressions
        let modifiers = self.visit_modifiers(node.modifiers());
        let heritage_clauses = self.visit_nodes(node.heritage_clauses());
        let members = self.visit_nodes(node.member_list());
        self.emit_context.factory().update_class_expression(
            node,
            modifiers,
            node.name(),
            NodeList::NIL,
            heritage_clauses,
            members,
        )
    }

    // Go: transformers/tstransforms/legacydecorators.go:262 LegacyDecoratorsTransformer.visitClassDeclaration
    fn visit_class_declaration(&mut self, node: Node) -> Node {
        let decorated = class_or_constructor_parameter_is_decorated(true, node);
        if !(decorated || child_is_decorated(true, node, Node::NIL)) {
            return self.visit_each_child(node);
        }

        if decorated {
            return self.transform_class_declaration_with_class_decorators(node, node.name());
        }
        self.transform_class_declaration_without_class_decorators(node, node.name())
    }

    // Go: transformers/tstransforms/legacydecorators.go:280 LegacyDecoratorsTransformer.transformClassDeclarationWithoutClassDecorators
    /// Transforms a non-decorated class declaration.
    ///
    /// @param node A ClassDeclaration node.
    /// @param name The name of the class.
    fn transform_class_declaration_without_class_decorators(
        &mut self,
        node: Node,
        name: Node,
    ) -> Node {
        //  ${modifiers} class ${name} ${heritageClauses} {
        //      ${members}
        //  }
        let modifiers = self.visit_modifiers(node.modifiers());
        let heritage_clauses = self.visit_nodes(node.heritage_clauses());
        let initial_members = self.visit_nodes(node.member_list());
        let (members, decoration_statements) =
            self.transform_decorators_of_class_elements(node, initial_members);

        let ec = self.emit_context.clone();
        let f = ec.factory();
        let mut name = name;
        if name.is_nil() && !decoration_statements.is_empty() {
            name = f.new_generated_name_for_node(node);
        }

        let updated = f.update_class_declaration(
            node,
            modifiers,
            name,
            NodeList::NIL,
            heritage_clauses,
            members,
        );

        if decoration_statements.is_empty() {
            return updated;
        }
        let mut statements = vec![updated];
        statements.extend(decoration_statements);
        f.new_syntax_list(&statements)
    }

    // Go: transformers/tstransforms/legacydecorators.go:308 LegacyDecoratorsTransformer.popEnclosingClass
    fn pop_enclosing_class(&mut self) {
        self.enclosing_classes.pop();
    }

    // Go: transformers/tstransforms/legacydecorators.go:312 LegacyDecoratorsTransformer.pushEnclosingClass
    fn push_enclosing_class(&mut self, cls: Node) {
        self.enclosing_classes.push(cls);
    }

    // Go: transformers/tstransforms/legacydecorators.go:320 LegacyDecoratorsTransformer.transformClassDeclarationWithClassDecorators
    /// Transforms a decorated class declaration and appends the resulting statements. If
    /// the class requires an alias to avoid issues with double-binding, the alias is returned.
    fn transform_class_declaration_with_class_decorators(
        &mut self,
        node: Node,
        name: Node,
    ) -> Node {
        // When we emit an ES6 class that has a class decorator, we must tailor the
        // emit to certain specific cases.
        //
        // In the simplest case, we emit the class declaration as a let declaration, and
        // evaluate decorators after the close of the class body:
        //
        //  [Example 1]
        //  ---------------------------------------------------------------------
        //  TypeScript                      | Javascript
        //  ---------------------------------------------------------------------
        //  @dec                            | let C = class C {
        //  class C {                       | }
        //  }                               | C = __decorate([dec], C);
        //  ---------------------------------------------------------------------
        //  @dec                            | let C = class C {
        //  export class C {                | }
        //  }                               | C = __decorate([dec], C);
        //                                  | export { C };
        //  ---------------------------------------------------------------------
        //
        // If a class declaration contains a reference to itself *inside* of the class body,
        // this introduces two bindings to the class: One outside of the class body, and one
        // inside of the class body. If we apply decorators as in [Example 1] above, there
        // is the possibility that the decorator `dec` will return a new value for the
        // constructor, which would result in the binding inside of the class no longer
        // pointing to the same reference as the binding outside of the class.
        //
        // As a result, we must instead rewrite all references to the class *inside* of the
        // class body to instead point to a local temporary alias for the class:
        //
        //  [Example 2]
        //  ---------------------------------------------------------------------
        //  TypeScript                      | Javascript
        //  ---------------------------------------------------------------------
        //  @dec                            | let C = C_1 = class C {
        //  class C {                       |   static x() { return C_1.y; }
        //    static x() { return C.y; }    | }
        //    static y = 1;                 | C.y = 1;
        //  }                               | C = C_1 = __decorate([dec], C);
        //                                  | var C_1;
        //  ---------------------------------------------------------------------
        //  @dec                            | let C = class C {
        //  export class C {                |   static x() { return C_1.y; }
        //    static x() { return C.y; }    | }
        //    static y = 1;                 | C.y = 1;
        //  }                               | C = C_1 = __decorate([dec], C);
        //                                  | export { C };
        //                                  | var C_1;
        //  ---------------------------------------------------------------------
        //
        // If a class declaration is the default export of a module, we instead emit
        // the export after the decorated declaration:
        //
        //  [Example 3]
        //  ---------------------------------------------------------------------
        //  TypeScript                      | Javascript
        //  ---------------------------------------------------------------------
        //  @dec                            | let default_1 = class {
        //  export default class {          | }
        //  }                               | default_1 = __decorate([dec], default_1);
        //                                  | export default default_1;
        //  ---------------------------------------------------------------------
        //  @dec                            | let C = class C {
        //  export default class C {        | }
        //  }                               | C = __decorate([dec], C);
        //                                  | export default C;
        //  ---------------------------------------------------------------------
        //
        // If the class declaration is the default export and a reference to itself
        // inside of the class body, we must emit both an alias for the class *and*
        // move the export after the declaration:
        //
        //  [Example 4]
        //  ---------------------------------------------------------------------
        //  TypeScript                      | Javascript
        //  ---------------------------------------------------------------------
        //  @dec                            | let C = class C {
        //  export default class C {        |   static x() { return C_1.y; }
        //    static x() { return C.y; }    | }
        //    static y = 1;                 | C.y = 1;
        //  }                               | C = C_1 = __decorate([dec], C);
        //                                  | export default C;
        //                                  | var C_1;
        //  ---------------------------------------------------------------------
        //

        let ec = self.emit_context.clone();
        let f = ec.factory();
        let is_export = has_syntactic_modifier(node, ModifierFlags::EXPORT);
        let is_default = has_syntactic_modifier(node, ModifierFlags::DEFAULT);
        let mut modifiers = ModifierList::NIL;
        if node.modifiers().is_some() && !node.modifiers().nodes().is_empty() {
            let modifier_nodes: Vec<Node> = node
                .modifiers()
                .nodes()
                .iter()
                .filter(|&m| is_not_export_or_default_or_decorator(m))
                .collect();
            if modifier_nodes.len() != node.modifiers().nodes().len() {
                modifiers = f.new_modifier_list_with_loc(
                    &modifier_nodes,
                    node.modifiers().node_list().loc(),
                );
            } else {
                modifiers = node.modifiers();
            }
        }

        let location = move_range_past_modifiers(node);
        let class_alias = self.get_class_alias_if_needed(node);
        if class_alias.is_some() {
            self.push_enclosing_class(node);
        }

        let result = self.transform_class_declaration_with_class_decorators_worker(
            node,
            name,
            is_export,
            is_default,
            modifiers,
            location,
            class_alias,
        );

        // PORT: Go `defer tx.popEnclosingClass()`.
        if class_alias.is_some() {
            self.pop_enclosing_class();
        }
        result
    }

    /// The rest of Go `transformClassDeclarationWithClassDecorators` (before
    /// the deferred `popEnclosingClass`).
    #[allow(clippy::too_many_arguments)]
    fn transform_class_declaration_with_class_decorators_worker(
        &mut self,
        node: Node,
        name: Node,
        is_export: bool,
        is_default: bool,
        modifiers: ModifierList,
        location: TextRange,
        class_alias: Node,
    ) -> Node {
        let ec = self.emit_context.clone();
        let f = ec.factory();

        // When we used to transform to ES5/3 this would be moved inside an IIFE and should reference the name
        // without any block-scoped variable collision handling - but we don't support that anymore, so we always
        // use the local name for the class
        let decl_name = f.get_local_name_ex(
            node,
            AssignedNameOptions {
                allow_comments: false,
                allow_source_maps: true,
                ..Default::default()
            },
        );

        //  ... = class ${name} ${heritageClauses} {
        //      ${members}
        //  }
        let heritage_clauses = self.visit_nodes(node.heritage_clauses());
        let members = self.visit_nodes(node.member_list());

        let (mut members, decoration_statements) =
            self.transform_decorators_of_class_elements(node, members);

        // If we're emitting to ES2022 or later then we need to reassign the class alias before
        // static initializers are evaluated.
        let assign_class_alias_in_static_block = self.language_version >= ScriptTarget::ES2022
            && class_alias.is_some()
            && members.is_some()
            && !members.nodes().is_empty()
            && members
                .nodes()
                .iter()
                .any(is_class_static_block_declaration_or_static_property);
        if assign_class_alias_in_static_block {
            let mut member_list: Vec<Node> = Vec::new();
            member_list.push(f.new_class_static_block_declaration(
                ModifierList::NIL,
                f.new_block(
                    f.new_node_list(&[f.new_expression_statement(f.new_assignment_expression(
                        class_alias,
                        f.new_keyword_expression(SyntaxKind::ThisKeyword),
                    ))]),
                    false,
                ),
            ));
            member_list.extend(members.nodes().iter());
            members = f.new_node_list_with_loc(&member_list, members.loc());
        }

        let mut expr_name = name;
        if name.is_some() && is_generated_identifier(&ec, name) {
            expr_name = Node::NIL;
        }
        let class_expression = f.new_class_expression(
            modifiers,
            expr_name,
            NodeList::NIL,
            heritage_clauses,
            members,
        );

        ec.set_original(class_expression, node);
        set_node_loc(class_expression, location);

        //  let ${name} = ${classExpression} where name is either declaredName if the class doesn't contain self-reference
        //                                         or decoratedClassAlias if the class contain self-reference.
        let mut var_initializer = class_expression;
        if class_alias.is_some() && !assign_class_alias_in_static_block {
            var_initializer = f.new_assignment_expression(class_alias, class_expression);
        }
        let var_decl = f.new_variable_declaration(decl_name, Node::NIL, Node::NIL, var_initializer);
        ec.set_original(var_decl, node);

        let var_decl_list =
            f.new_variable_declaration_list(f.new_node_list(&[var_decl]), NodeFlags::LET);
        let var_statement = f.new_variable_statement(ModifierList::NIL, var_decl_list);
        ec.set_original(var_statement, node);
        set_node_loc(var_statement, location);
        ec.set_comment_range(var_statement, node.loc());

        let mut statements = vec![var_statement];
        statements.extend(decoration_statements);
        // PORT: Go appends the result even when it is nil.
        statements.push(self.get_constructor_decoration_statement(node));

        if is_export {
            let export_statement = if is_default {
                f.new_export_default(decl_name)
            } else {
                f.new_external_module_export(f.get_declaration_name(node))
            };
            statements.push(export_statement);
        }

        if statements.len() == 1 {
            return statements[0];
        }
        f.new_syntax_list(&statements)
    }

    // Go: transformers/tstransforms/legacydecorators.go:512 LegacyDecoratorsTransformer.hasInternalStaticReference
    fn has_internal_static_reference(&self, node: Node) -> bool {
        let ec = &self.emit_context;
        let resolver = &*self.reference_resolver;
        let class_node = ec.most_original(node);
        for member in node.members().iter() {
            if member.for_each_child(|n| {
                is_or_contains_static_self_reference(ec, resolver, class_node, n)
            }) {
                return true;
            }
        }
        false
    }

    // Go: transformers/tstransforms/legacydecorators.go:539 LegacyDecoratorsTransformer.getClassAliasIfNeeded
    /// Gets a local alias for a class declaration if it is a decorated class with an internal
    /// reference to the static side of the class. This is necessary to avoid issues with
    /// double-binding semantics for the class name.
    fn get_class_alias_if_needed(&mut self, node: Node) -> Node {
        if !self.has_internal_static_reference(node) {
            return Node::NIL;
        }
        let ec = self.emit_context.clone();
        let mut name_text = "default";
        if node.name().is_some() && !is_generated_identifier(&ec, node.name()) {
            name_text = node.name().text();
        }

        let class_alias = ec.factory().new_unique_name(name_text);
        ec.add_variable_declaration(class_alias);
        self.class_aliases
            .as_mut()
            .expect("assignment to entry in nil map")
            .insert(node, class_alias);

        class_alias
    }

    // Go: transformers/tstransforms/legacydecorators.go:560 LegacyDecoratorsTransformer.getConstructorDecorationStatement
    /// Generates a __decorate helper call for a class constructor.
    ///
    /// @param node The class node.
    fn get_constructor_decoration_statement(&mut self, node: Node) -> Node {
        let expression = self.generate_constructor_decoration_expression(node);
        if expression.is_some() {
            let result = self
                .emit_context
                .factory()
                .new_expression_statement(expression);
            self.emit_context.set_original(result, node);
            return result;
        }
        Node::NIL
    }

    // Go: transformers/tstransforms/legacydecorators.go:575 LegacyDecoratorsTransformer.generateConstructorDecorationExpression
    /// Generates a __decorate helper call for a class constructor.
    ///
    /// @param node The class node.
    fn generate_constructor_decoration_expression(&mut self, node: Node) -> Node {
        let all_decorators = get_all_decorators_of_class(node, true);
        // Decorator expressions are evaluated outside the class body, so references to the
        // class name should use the original binding, not the class alias. In Strada, this is
        // handled by NodeCheckFlags.ConstructorReference which is only set for identifiers
        // inside the class body. Since Corsa lacks per-node flags, we temporarily pop the
        // enclosing class to prevent alias substitution during decorator expression visiting.
        let has_alias = self.enclosing_classes.last() == Some(&node);
        if has_alias {
            self.pop_enclosing_class();
        }
        let decorator_expressions = self.transform_all_decorators_of_declaration(&all_decorators);
        if has_alias {
            self.push_enclosing_class(node);
        }
        if decorator_expressions.is_empty() {
            return Node::NIL;
        }

        let class_alias = self.class_alias_of(node).unwrap_or(Node::NIL);

        let ec = self.emit_context.clone();
        let f = ec.factory();
        // When we used to transform to ES5/3 this would be moved inside an IIFE and should reference the name
        // without any block-scoped variable collision handling - but we don't support that anymore, so we always
        // use the local name for the class
        let local_name = f.get_declaration_name_ex(
            node,
            NameOptions {
                allow_comments: false,
                allow_source_maps: true,
            },
        );
        let decorate =
            f.new_decorate_helper(&decorator_expressions, local_name, Node::NIL, Node::NIL);
        let mut assignment_target = decorate;
        if class_alias.is_some() {
            assignment_target = f.new_assignment_expression(class_alias, decorate);
        }
        let expression = f.new_assignment_expression(local_name, assignment_target);
        ec.set_emit_flags(expression, EmitFlags::NO_COMMENTS);
        ec.set_source_map_range(expression, move_range_past_modifiers(node));
        expression
    }

    // Go: transformers/tstransforms/legacydecorators.go:793 LegacyDecoratorsTransformer.transformDecoratorsOfClassElements
    fn transform_decorators_of_class_elements(
        &mut self,
        node: Node,
        members: NodeList,
    ) -> (NodeList, Vec<Node>) {
        let mut decoration_statements: Vec<Node> = Vec::new();
        decoration_statements.extend(self.get_class_element_decoration_statements(node, false));
        decoration_statements.extend(self.get_class_element_decoration_statements(node, true));
        let mut members = members;
        if has_class_element_with_decorator_containing_private_identifier_in_expression(node) {
            let f = self.emit_context.factory();
            let mut member_nodes: Vec<Node> = Vec::new();
            if members.is_some() && !members.nodes().is_empty() {
                member_nodes = members.nodes().to_vec();
            }
            member_nodes.push(f.new_class_static_block_declaration(
                ModifierList::NIL,
                f.new_block(f.new_node_list(&decoration_statements), true),
            ));
            members = f.new_node_list(&member_nodes);
            decoration_statements = Vec::new();
        }

        (members, decoration_statements)
    }

    // Go: transformers/tstransforms/legacydecorators.go:822 LegacyDecoratorsTransformer.getClassElementDecorationStatements
    /// Generates statements used to apply decorators to either the static or instance members
    /// of a class.
    ///
    /// @param node The class node.
    /// @param isStatic A value indicating whether to generate statements for static or
    ///                 instance members.
    fn get_class_element_decoration_statements(
        &mut self,
        node: Node,
        is_static: bool,
    ) -> Vec<Node> {
        let exprs = self.generate_class_element_decoration_expressions(node, is_static);
        let f = self.emit_context.factory();
        let mut statements = Vec::new();
        for e in exprs {
            statements.push(f.new_expression_statement(e));
        }
        statements
    }

    // Go: transformers/tstransforms/legacydecorators.go:870 LegacyDecoratorsTransformer.generateClassElementDecorationExpressions
    /// Generates expressions used to apply decorators to either the static or instance members
    /// of a class.
    ///
    /// @param node The class node.
    /// @param isStatic A value indicating whether to generate expressions for static or
    ///                 instance members.
    fn generate_class_element_decoration_expressions(
        &mut self,
        node: Node,
        is_static: bool,
    ) -> Vec<Node> {
        let members = get_decorated_class_elements(node, is_static);
        let mut expressions = Vec::new();
        for member in members {
            let expr = self.generate_class_element_decoration_expression(node, member);
            if expr.is_some() {
                expressions.push(expr);
            }
        }
        expressions
    }

    // Go: transformers/tstransforms/legacydecorators.go:888 LegacyDecoratorsTransformer.generateClassElementDecorationExpression
    /// Generates an expression used to evaluate class element decorators at runtime.
    ///
    /// @param node The class node that contains the member.
    /// @param member The class member.
    fn generate_class_element_decoration_expression(&mut self, node: Node, member: Node) -> Node {
        let all_decorators = get_all_decorators_of_class_element(member, node, true);
        let decorator_expressions = self.transform_all_decorators_of_declaration(&all_decorators);
        if decorator_expressions.is_empty() {
            return Node::NIL;
        }

        // Emit the call to __decorate. Given the following:
        //
        //   class C {
        //     @dec method(@dec2 x) {}
        //     @dec get accessor() {}
        //     @dec prop;
        //   }
        //
        // The emit for a method is:
        //
        //   __decorate([
        //       dec,
        //       __param(0, dec2),
        //       __metadata("design:type", Function),
        //       __metadata("design:paramtypes", [Object]),
        //       __metadata("design:returntype", void 0)
        //   ], C.prototype, "method", null);
        //
        // The emit for an accessor is:
        //
        //   __decorate([
        //       dec
        //   ], C.prototype, "accessor", null);
        //
        // The emit for a property is:
        //
        //   __decorate([
        //       dec
        //   ], C.prototype, "prop");
        //

        let ec = self.emit_context.clone();
        let f = ec.factory();
        let prefix = self.get_class_member_prefix(node, member);
        let member_name = self.get_expression_for_property_name(
            member,
            !member.flags().intersects(NodeFlags::AMBIENT),
        );
        let descriptor = if is_property_declaration(member) && !has_accessor_modifier(member) {
            // We emit `void 0` here to indicate to `__decorate` that it can invoke `Object.defineProperty` directly, but that it
            // should not invoke `Object.getOwnPropertyDescriptor`.
            f.new_void_zero_expression()
        } else {
            // We emit `null` here to indicate to `__decorate` that it can invoke `Object.getOwnPropertyDescriptor` directly.
            // We have this extra argument here so that we can inject an explicit property descriptor at a later date.
            f.new_keyword_expression(SyntaxKind::NullKeyword)
        };

        let helper = f.new_decorate_helper(&decorator_expressions, prefix, member_name, descriptor);

        ec.set_emit_flags(helper, EmitFlags::NO_COMMENTS);
        ec.set_source_map_range(helper, move_range_past_modifiers(member));
        helper
    }

    // Go: transformers/tstransforms/legacydecorators.go:951 LegacyDecoratorsTransformer.isSyntheticMetadataDecorator
    fn is_synthetic_metadata_decorator(&self, node: Node) -> bool {
        self.emit_context
            .is_call_to_helper(node.expression(), "__metadata")
    }

    // Go: transformers/tstransforms/legacydecorators.go:960 LegacyDecoratorsTransformer.transformAllDecoratorsOfDeclaration
    /// Transforms all of the decorators for a declaration into an array of expressions.
    ///
    /// @param allDecorators An object containing all of the decorators for the declaration.
    fn transform_all_decorators_of_declaration(
        &mut self,
        all_decorators: &Option<AllDecorators>,
    ) -> Vec<Node> {
        let Some(all_decorators) = all_decorators else {
            return Vec::new();
        };

        // ensure that metadata decorators are last
        let (metadata, decorators): (Vec<Node>, Vec<Node>) = all_decorators
            .decorators
            .iter()
            .copied()
            .partition(|&d| self.is_synthetic_metadata_decorator(d));

        let mut decorator_expressions = Vec::new();
        decorator_expressions.extend(self.transform_decorators(&decorators));
        decorator_expressions
            .extend(self.transform_decorators_of_parameters(&all_decorators.parameters));
        decorator_expressions.extend(self.transform_decorators(&metadata));
        decorator_expressions
    }

    // Go: transformers/tstransforms/legacydecorators.go:977 LegacyDecoratorsTransformer.transformDecoratorsOfParameters
    fn transform_decorators_of_parameters(&mut self, parameters: &[Vec<Node>]) -> Vec<Node> {
        let ec = self.emit_context.clone();
        let f = ec.factory();
        let mut results = Vec::new();
        for (i, decorators) in parameters.iter().enumerate() {
            if !decorators.is_empty() {
                for &decorator in decorators {
                    let expression = self.visit_node(decorator.expression());
                    let helper =
                        f.new_param_helper(expression, i as i32, decorator.expression().loc());
                    ec.set_emit_flags(helper, EmitFlags::NO_COMMENTS);
                    results.push(helper);
                }
            }
        }
        results
    }

    // Go: transformers/tstransforms/legacydecorators.go:1000 LegacyDecoratorsTransformer.transformDecorators
    /// Transforms a list of decorators into an expression.
    ///
    /// @param decorator The decorator node.
    fn transform_decorators(&mut self, decorators: &[Node]) -> Vec<Node> {
        let mut results = Vec::new();
        for &d in decorators {
            results.push(self.visit_node(d.expression()));
        }
        results
    }

    // Go: transformers/tstransforms/legacydecorators.go:1008 LegacyDecoratorsTransformer.getClassMemberPrefix
    fn get_class_member_prefix(&self, node: Node, member: Node) -> Node {
        if is_static(member) {
            return self.emit_context.factory().get_declaration_name(node);
        }
        self.get_class_prototype(node)
    }

    // Go: transformers/tstransforms/legacydecorators.go:1015 LegacyDecoratorsTransformer.getClassPrototype
    fn get_class_prototype(&self, node: Node) -> Node {
        let f = self.emit_context.factory();
        f.new_property_access_expression(
            f.get_declaration_name(node),
            Node::NIL,
            f.new_identifier("prototype"),
            NodeFlags::NONE,
        )
    }

    // Go: transformers/tstransforms/legacydecorators.go:1024 LegacyDecoratorsTransformer.getExpressionForPropertyName
    fn get_expression_for_property_name(
        &self,
        member: Node,
        generate_name_for_computed_property_name: bool,
    ) -> Node {
        let f = self.emit_context.factory();
        let name = member.name();
        if is_private_identifier(name) {
            f.new_identifier("")
        } else if is_computed_property_name(name) {
            if generate_name_for_computed_property_name
                && !is_simple_inlineable_expression(name.expression())
            {
                return f.new_generated_name_for_node(name);
            }
            name.expression()
        } else if is_identifier(name) {
            f.new_string_literal(name.text(), TokenFlags::NONE)
        } else {
            f.deep_clone_node(name)
        }
    }
}

// Go: transformers/tstransforms/legacydecorators.go:94 elideNodes
fn elide_nodes(f: &PrinterNodeFactory, nodes: NodeList) -> NodeList {
    if nodes.is_nil() {
        return NodeList::NIL;
    }
    if nodes.nodes().is_empty() {
        return nodes;
    }
    f.new_node_list_with_loc(&[], nodes.loc())
}

// Go: transformers/tstransforms/legacydecorators.go:106 elideModifiers
fn elide_modifiers(f: &PrinterNodeFactory, nodes: ModifierList) -> ModifierList {
    if nodes.is_nil() {
        return ModifierList::NIL;
    }
    if nodes.nodes().is_empty() {
        return nodes;
    }
    f.new_modifier_list_with_loc(&[], nodes.node_list().loc())
}

/// Go `isOrContainsStaticSelfReference`, the recursive closure inside
/// `hasInternalStaticReference`.
fn is_or_contains_static_self_reference(
    ec: &EmitContext,
    resolver: &dyn TransformReferenceResolver,
    class_node: Node,
    n: Node,
) -> bool {
    if is_identifier(n)
        && resolver.get_referenced_value_declaration(ec.most_original(n)) == class_node
    {
        return true;
    }
    // For PropertyAccessExpression, only check the expression, not the name.
    // The .Name() is a property access name, not a value reference to the class.
    if is_property_access_expression(n) {
        return is_or_contains_static_self_reference(ec, resolver, class_node, n.expression());
    }
    n.for_each_child(|child| is_or_contains_static_self_reference(ec, resolver, class_node, child))
}

// Go: transformers/tstransforms/legacydecorators.go:614 isClassStaticBlockDeclarationOrStaticProperty
fn is_class_static_block_declaration_or_static_property(node: Node) -> bool {
    is_class_static_block_declaration(node)
        || (is_property_declaration(node) && has_static_modifier(node))
}

// Go: transformers/tstransforms/legacydecorators.go:618 isNotExportOrDefaultOrDecorator
fn is_not_export_or_default_or_decorator(node: Node) -> bool {
    !(is_decorator(node)
        || node.kind() == SyntaxKind::ExportKeyword
        || node.kind() == SyntaxKind::DefaultKeyword)
}

// Go: transformers/tstransforms/legacydecorators.go:622 decoratorContainsPrivateIdentifierInExpression
fn decorator_contains_private_identifier_in_expression(decorator: Node) -> bool {
    decorator
        .subtree_facts()
        .intersects(SubtreeFacts::SUBTREE_CONTAINS_PRIVATE_IDENTIFIER_IN_EXPRESSION)
}

// Go: transformers/tstransforms/legacydecorators.go:626 parameterDecoratorsContainPrivateIdentifierInExpression
fn parameter_decorators_contain_private_identifier_in_expression(
    parameter_decorators: &[Node],
) -> bool {
    parameter_decorators
        .iter()
        .any(|&d| decorator_contains_private_identifier_in_expression(d))
}

// Go: transformers/tstransforms/legacydecorators.go:630 hasClassElementWithDecoratorContainingPrivateIdentifierInExpression
fn has_class_element_with_decorator_containing_private_identifier_in_expression(
    node: Node,
) -> bool {
    if node.member_list().is_nil() || node.member_list().nodes().is_empty() {
        return false;
    }
    for member in node.members().iter() {
        if !can_have_decorators(member) {
            continue;
        }
        let Some(all_decorators) = get_all_decorators_of_class_element(member, node, true) else {
            continue;
        };
        if all_decorators
            .decorators
            .iter()
            .any(|&d| decorator_contains_private_identifier_in_expression(d))
        {
            return true;
        }
        if all_decorators
            .parameters
            .iter()
            .any(|p| parameter_decorators_contain_private_identifier_in_expression(p))
        {
            return true;
        }
    }
    false
}

// Go: transformers/tstransforms/legacydecorators.go:652 allDecorators
pub(super) struct AllDecorators {
    pub(super) decorators: Vec<Node>,
    pub(super) parameters: Vec<Vec<Node>>,
}

// Go: transformers/tstransforms/legacydecorators.go:665 getAllDecoratorsOfClass
/// Gets an allDecorators object containing the decorators for the class and the decorators for the
/// parameters of the constructor of the class.
///
/// @param node The class node.
///
/// @internal
fn get_all_decorators_of_class(node: Node, use_legacy_decorators: bool) -> Option<AllDecorators> {
    let decorators = node.decorators().to_vec();
    let mut parameters = Vec::new();
    if use_legacy_decorators {
        parameters = get_decorators_of_parameters(get_first_constructor_with_body(node));
    }
    if decorators.is_empty() && parameters.is_empty() {
        return None;
    }
    Some(AllDecorators {
        decorators,
        parameters,
    })
}

// Go: transformers/tstransforms/legacydecorators.go:685 getAllDecoratorsOfClassElement
/// Gets an allDecorators object containing the decorators for the member and its parameters.
///
/// @param parent The class node that contains the member.
/// @param member The class member.
///
/// @internal
fn get_all_decorators_of_class_element(
    member: Node,
    parent: Node,
    use_legacy_decorators: bool,
) -> Option<AllDecorators> {
    match member.kind() {
        SyntaxKind::GetAccessor | SyntaxKind::SetAccessor => {
            if !use_legacy_decorators {
                return get_all_decorators_of_method(member, false);
            }
            get_all_decorators_of_accessors(member, parent, true)
        }
        SyntaxKind::MethodDeclaration => {
            get_all_decorators_of_method(member, use_legacy_decorators)
        }
        SyntaxKind::PropertyDeclaration => get_all_decorators_of_property(member),
        _ => None,
    }
}

// Go: transformers/tstransforms/legacydecorators.go:707 getAllDecoratorsOfAccessors
/// Gets an allDecorators object containing the decorators for the accessor and its parameters.
///
/// @param parent The class node that contains the accessor.
/// @param accessor The class accessor member.
fn get_all_decorators_of_accessors(
    accessor: Node,
    parent: Node,
    use_legacy_decorators: bool,
) -> Option<AllDecorators> {
    if accessor.body().is_nil() {
        return None;
    }
    let decls = get_all_accessor_declarations(&parent.members().to_vec(), accessor);
    let mut first_accessor_with_decorators = Node::NIL;
    if has_decorators(decls.first_accessor) {
        first_accessor_with_decorators = decls.first_accessor;
    } else if decls.second_accessor.is_some() && has_decorators(decls.second_accessor) {
        first_accessor_with_decorators = decls.second_accessor;
    }

    if first_accessor_with_decorators.is_nil() || accessor != first_accessor_with_decorators {
        return None;
    }

    let decorators = first_accessor_with_decorators.decorators().to_vec();
    let mut parameters = Vec::new();
    if use_legacy_decorators && decls.set_accessor.is_some() {
        parameters = get_decorators_of_parameters(decls.set_accessor);
    }

    if decorators.is_empty() && parameters.is_empty() {
        return None;
    }

    Some(AllDecorators {
        decorators,
        parameters,
    })
}

// Go: transformers/tstransforms/legacydecorators.go:739 getAllDecoratorsOfProperty
fn get_all_decorators_of_property(property: Node) -> Option<AllDecorators> {
    let decorators = property.decorators().to_vec();
    if decorators.is_empty() {
        return None;
    }
    Some(AllDecorators {
        decorators,
        parameters: Vec::new(),
    })
}

// Go: transformers/tstransforms/legacydecorators.go:747 getAllDecoratorsOfMethod
fn get_all_decorators_of_method(
    method: Node,
    use_legacy_decorators: bool,
) -> Option<AllDecorators> {
    if method.body().is_nil() {
        return None;
    }
    let decorators = method.decorators().to_vec();
    let mut parameters = Vec::new();
    if use_legacy_decorators {
        parameters = get_decorators_of_parameters(method);
    }
    if decorators.is_empty() && parameters.is_empty() {
        return None;
    }
    Some(AllDecorators {
        decorators,
        parameters,
    })
}

// Go: transformers/tstransforms/legacydecorators.go:768 getDecoratorsOfParameters
/// Gets an array of arrays of decorators for the parameters of a function-like node.
/// The offset into the result array should correspond to the offset of the parameter.
///
/// @param node The function-like node.
pub(super) fn get_decorators_of_parameters(node: Node) -> Vec<Vec<Node>> {
    let mut decorators: Vec<Vec<Node>> = Vec::new();
    if node.is_some() {
        let parameters = node.parameters();
        let first_parameter_is_this =
            !parameters.is_empty() && is_this_parameter(parameters.get(0));
        let mut first_parameter_offset = 0;
        let mut num_parameters = parameters.len();
        if first_parameter_is_this {
            first_parameter_offset = 1;
            num_parameters -= 1;
        }
        for i in 0..num_parameters {
            let p = parameters.get(i + first_parameter_offset);
            if !decorators.is_empty() || has_decorators(p) {
                if decorators.is_empty() {
                    decorators = vec![Vec::new(); num_parameters];
                }
                decorators[i] = p.decorators().to_vec();
            }
        }
    }
    decorators
}

// Go: transformers/tstransforms/legacydecorators.go:837 isDecoratedClassElement
/// Determines whether a class member is either a static or an instance member of a class
/// that is decorated, or has parameters that are decorated.
///
/// @param member The class member.
fn is_decorated_class_element(member: Node, is_static_element: bool, parent: Node) -> bool {
    is_static_element == is_static(member)
        && node_or_child_is_decorated(true, member, parent, Node::NIL)
}

// Go: transformers/tstransforms/legacydecorators.go:849 getDecoratedClassElements
/// Gets either the static or instance members of a class that are decorated, or have
/// parameters that are decorated.
///
/// @param node The class containing the member.
/// @param isStatic A value indicating whether to retrieve static or instance members of
///                 the class.
fn get_decorated_class_elements(node: Node, is_static: bool) -> Vec<Node> {
    if node.member_list().is_nil() || node.member_list().nodes().is_empty() {
        return Vec::new();
    }
    let mut members = Vec::new();
    for member in node.members().iter() {
        if is_decorated_class_element(member, is_static, node) {
            members.push(member);
        }
    }
    members
}
