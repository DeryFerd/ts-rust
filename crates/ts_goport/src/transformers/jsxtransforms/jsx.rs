//! Port of Go `transformers/jsxtransforms/jsx.go`: the JSX transform for
//! `jsx: react`, `react-jsx` and `react-jsxdev`.
//!
//! PORT: Go `tx.Visitor().Visit(n)` is the raw visit callback, so it is
//! `self.visit(n)` here. The other visitor methods (`VisitEachChild`,
//! `VisitSlice`) go through `TransformerVisit::with_visitor`.
//!
//! PORT: the entity table (Go `var entities`) is in `entities.rs`.

use super::entities::entity_code_point;
use crate::prelude::*;
use crate::printer::{AutoGenerateOptions, EmitResolver, GeneratedIdentifierFlags};
use crate::transformers::transformer::{
    TransformOptions, Transformer, TransformerBox, TransformerVisit,
};

/// Go `JSXTransformer`.
pub struct JsxTransformer {
    // Go embedded transformers.Transformer
    emit_context: Rc<EmitContext>,

    compiler_options: &'static CompilerOptions,
    emit_resolver: Rc<dyn EmitResolver>,

    import_specifier: String,
    filename_declaration: Node,
    // PORT: Go `collections.OrderedMap[string, map[string]*ast.Node]`.
    utilized_implicit_runtime_imports: IndexMap<String, FxHashMap<String, Node>>,
    in_jsx_child: bool,

    current_source_file: Node,
}

/// Which Go `tagTransform` method value `visitJsxElement` and
/// `visitJsxSelfClosingElement` picked.
// PORT: Go stores a method value in a local; a bool picks the method here.
#[derive(Clone, Copy)]
enum TagTransform {
    Jsx,
    CreateElement,
}

// Go: transformers/jsxtransforms/jsx.go:32 NewJSXTransformer
// PORT: Go never returns nil here, so this returns a plain `TransformerBox`.
pub fn new_jsx_transformer(opts: &TransformOptions) -> TransformerBox {
    let compiler_options = opts.compiler_options;
    let emit_context = opts.context.clone();
    Box::new(JsxTransformer {
        emit_context,
        compiler_options,
        emit_resolver: opts.emit_resolver.clone(),
        import_specifier: String::new(),
        filename_declaration: Node::NIL,
        utilized_implicit_runtime_imports: IndexMap::new(),
        in_jsx_child: false,
        current_source_file: Node::NIL,
    })
}

impl Transformer for JsxTransformer {
    // Go: transformers/transformer.go:27 Transformer.EmitContext
    fn emit_context(&self) -> &Rc<EmitContext> {
        &self.emit_context
    }

    // Go: transformers/transformer.go:39 Transformer.TransformSourceFile
    fn transform_source_file(&mut self, file: Node) -> Node {
        self.visit_source_file_root(file)
    }
}

impl TransformerVisit for JsxTransformer {
    fn emit_context_rc(&self) -> Rc<EmitContext> {
        self.emit_context.clone()
    }

    // Go: transformers/jsxtransforms/jsx.go:106 JSXTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        if node.is_nil() {
            return Node::NIL;
        }
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_JSX)
        {
            return node;
        }
        match node.kind() {
            SyntaxKind::SourceFile => {
                self.set_in_child(false);
                return self.visit_source_file(node);
            }
            SyntaxKind::JsxElement => return self.visit_jsx_element(node),
            SyntaxKind::JsxSelfClosingElement => return self.visit_jsx_self_closing_element(node),
            SyntaxKind::JsxFragment => return self.visit_jsx_fragment(node),
            SyntaxKind::JsxOpeningElement => {
                panic!("JsxOpeningElement should not be visited, handled in visitJsxElement")
            }
            SyntaxKind::JsxOpeningFragment => {
                panic!("JsxOpeningFragment should not be visited, handled in visitJsxFragment")
            }
            SyntaxKind::JsxText => {
                self.set_in_child(false);
                return self.visit_jsx_text(node);
            }
            SyntaxKind::JsxExpression => {
                self.set_in_child(false);
                return self.visit_jsx_expression(node);
            }
            _ => {}
        }
        self.set_in_child(false);
        self.with_visitor(|v| v.visit_each_child(node)) // by default, do nothing
    }
}

/// Go `file.IsDeclarationFile`, `ast.IsExternalModule(file)` and
/// `ast.IsExternalOrCommonJSModule(file)` for a parsed or factory SourceFile.
// PORT: the crate helpers read `source_file_info`, which only exists for
// parsed files. An earlier transformer can hand this one an updated (factory)
// SourceFile, whose parser fields are a copy (Go `copyFrom`). Read them here
// from whichever form the file has.
fn source_file_module_facts(file: Node) -> (bool, bool, bool) {
    if is_synthetic_node(file) {
        return with_synthetic_source_file(file, |d| {
            (
                d.is_declaration_file,
                d.external_module_indicator.is_some(),
                d.external_module_indicator.is_some() || d.common_js_module_indicator.is_some(),
            )
        });
    }
    (
        source_file_info(file).is_declaration_file,
        is_external_module(file),
        is_external_or_common_js_module(file),
    )
}

impl JsxTransformer {
    // Go: transformers/jsxtransforms/jsx.go:42 JSXTransformer.getCurrentFileNameExpression
    fn get_current_file_name_expression(&mut self) -> Node {
        if self.filename_declaration.is_some() {
            return self.filename_declaration.name();
        }
        let ec = self.emit_context.clone();
        let f = ec.factory();
        let d = f.new_variable_declaration(
            f.new_unique_name_ex(
                "_jsxFileName",
                AutoGenerateOptions {
                    flags: GeneratedIdentifierFlags::OPTIMISTIC
                        | GeneratedIdentifierFlags::FILE_LEVEL,
                    ..Default::default()
                },
            ),
            Node::NIL,
            Node::NIL,
            f.new_string_literal(
                source_file_file_name(self.current_source_file),
                TokenFlags::NONE,
            ),
        );
        self.filename_declaration = d;
        d.name()
    }

    // Go: transformers/jsxtransforms/jsx.go:58 JSXTransformer.getJsxFactoryCalleePrimitive
    fn get_jsx_factory_callee_primitive(&self, is_static_children: bool) -> &'static str {
        if self.compiler_options.jsx == JsxEmit::REACT_JSX_DEV {
            return "jsxDEV";
        }
        if is_static_children {
            return "jsxs";
        }
        "jsx"
    }

    // Go: transformers/jsxtransforms/jsx.go:68 JSXTransformer.getJsxFactoryCallee
    fn get_jsx_factory_callee(&mut self, is_static_children: bool) -> Node {
        let t = self.get_jsx_factory_callee_primitive(is_static_children);
        self.get_implicit_import_for_name(t)
    }

    // Go: transformers/jsxtransforms/jsx.go:73 JSXTransformer.getImplicitJsxFragmentReference
    fn get_implicit_jsx_fragment_reference(&mut self) -> Node {
        self.get_implicit_import_for_name("Fragment")
    }

    // Go: transformers/jsxtransforms/jsx.go:77 JSXTransformer.getImplicitImportForName
    fn get_implicit_import_for_name(&mut self, name: &str) -> Node {
        let mut import_source = self.import_specifier.clone();
        if name != "createElement" {
            import_source = get_jsx_runtime_import(&import_source, self.compiler_options);
        }
        match self.utilized_implicit_runtime_imports.get(&import_source) {
            Some(existing) => {
                if let Some(elem) = existing.get(name) {
                    return elem.name();
                }
            }
            None => {
                self.utilized_implicit_runtime_imports
                    .insert(import_source.clone(), FxHashMap::default());
            }
        }

        let ec = self.emit_context.clone();
        let f = ec.factory();
        let generated_name = f.new_unique_name_ex(
            &format!("_{name}"),
            AutoGenerateOptions {
                flags: GeneratedIdentifierFlags::OPTIMISTIC
                    | GeneratedIdentifierFlags::FILE_LEVEL
                    | GeneratedIdentifierFlags::ALLOW_NAME_SUBSTITUTION,
                ..Default::default()
            },
        );
        let specifier = f.new_import_specifier(false, f.new_identifier(name), generated_name);
        self.emit_resolver
            .set_referenced_import_declaration(generated_name, specifier);
        self.utilized_implicit_runtime_imports
            .get_mut(&import_source)
            .expect("inserted above")
            .insert(name.to_string(), specifier);
        specifier.name()
    }

    // Go: transformers/jsxtransforms/jsx.go:102 JSXTransformer.setInChild
    fn set_in_child(&mut self, v: bool) {
        self.in_jsx_child = v;
    }

    // Go: transformers/jsxtransforms/jsx.go:157 JSXTransformer.shouldUseCreateElement
    fn should_use_create_element(&self, node: Node) -> bool {
        self.import_specifier.is_empty() || has_key_after_props_spread(node)
    }

    // Go: transformers/jsxtransforms/jsx.go:175 JSXTransformer.isAnyPrologueDirective
    fn is_any_prologue_directive(&self, node: Node) -> bool {
        is_prologue_directive(node)
            || self
                .emit_context
                .emit_flags(node)
                .intersects(EmitFlags::CUSTOM_PROLOGUE)
    }

    // Go: transformers/jsxtransforms/jsx.go:179 JSXTransformer.insertStatementAfterCustomPrologue
    fn insert_statement_after_custom_prologue(&self, to: Vec<Node>, statement: Node) -> Vec<Node> {
        insert_statement_after_prologue(to, statement, |n| self.is_any_prologue_directive(n))
    }

    // Go: transformers/jsxtransforms/jsx.go:197 JSXTransformer.visitSourceFile
    fn visit_source_file(&mut self, file: Node) -> Node {
        let (is_declaration_file, is_external, is_external_or_cjs) = source_file_module_facts(file);
        if is_declaration_file {
            return file;
        }

        self.current_source_file = file;
        // PORT: `get_jsx_implicit_import_base` reads the pragmas from
        // `source_file_info`, which a factory SourceFile does not have. Its
        // pragmas are a copy of the parsed file's (Go `copyFrom`), so read them
        // from the parsed file.
        let pragma_file = if is_synthetic_node(file) {
            self.emit_context.most_original(file)
        } else {
            file
        };
        self.import_specifier = get_jsx_implicit_import_base(self.compiler_options, pragma_file);
        self.filename_declaration = Node::NIL;
        self.utilized_implicit_runtime_imports.clear();

        let ec = self.emit_context.clone();
        let f = ec.factory();
        let mut visited = self.with_visitor(|v| v.visit_each_child(file));
        ec.add_emit_helper(visited, &ec.read_emit_helpers());
        let mut statements = visited.statements().to_vec();
        let mut statements_updated = false;
        if self.filename_declaration.is_some() {
            let statement = f.new_variable_statement(
                ModifierList::NIL,
                f.new_variable_declaration_list(
                    f.new_node_list(&[self.filename_declaration]),
                    NodeFlags::CONST,
                ),
            );
            statements = self.insert_statement_after_custom_prologue(statements, statement);
            statements_updated = true;
        }

        if !self.utilized_implicit_runtime_imports.is_empty() {
            if is_external {
                statements_updated = true;
                let mut new_statements: Vec<Node> =
                    Vec::with_capacity(self.utilized_implicit_runtime_imports.len());
                for (import_source, import_specifiers_map) in
                    &self.utilized_implicit_runtime_imports
                {
                    let s = f.new_import_declaration(
                        ModifierList::NIL,
                        f.new_import_clause(
                            SyntaxKind::Unknown,
                            Node::NIL,
                            f.new_named_imports(
                                f.new_node_list(&get_sorted_specifiers(import_specifiers_map)),
                            ),
                        ),
                        f.new_string_literal(import_source.as_str(), TokenFlags::NONE),
                        Node::NIL,
                    );
                    set_parent_in_children(s);
                    new_statements.push(s);
                }
                for e in new_statements {
                    statements = self.insert_statement_after_custom_prologue(statements, e);
                }
            } else if is_external_or_cjs {
                statements_updated = true;
                let mut new_statements: Vec<Node> =
                    Vec::with_capacity(self.utilized_implicit_runtime_imports.len());
                for (import_source, import_specifiers_map) in
                    &self.utilized_implicit_runtime_imports
                {
                    let sorted = get_sorted_specifiers(import_specifiers_map);
                    let mut as_binding_elems: Vec<Node> = Vec::with_capacity(sorted.len());
                    for elem in sorted {
                        as_binding_elems.push(f.new_binding_element(
                            Node::NIL,
                            elem.property_name(),
                            elem.name(),
                            Node::NIL,
                        ));
                    }
                    let s = f.new_variable_statement(
                        ModifierList::NIL,
                        f.new_variable_declaration_list(
                            f.new_node_list(&[f.new_variable_declaration(
                                f.new_binding_pattern(
                                    SyntaxKind::ObjectBindingPattern,
                                    f.new_node_list(&as_binding_elems),
                                ),
                                Node::NIL,
                                Node::NIL,
                                f.new_call_expression(
                                    f.new_identifier("require"),
                                    Node::NIL,
                                    NodeList::NIL,
                                    f.new_node_list(&[f.new_string_literal(
                                        import_source.as_str(),
                                        TokenFlags::NONE,
                                    )]),
                                    NodeFlags::NONE,
                                ),
                            )]),
                            NodeFlags::CONST,
                        ),
                    );
                    set_parent_in_children(s);
                    new_statements.push(s);
                }
                for e in new_statements {
                    statements = self.insert_statement_after_custom_prologue(statements, e);
                }
            } else {
                // Do nothing (script file) - consider an error in the checker?
            }
        }

        if statements_updated {
            visited =
                f.update_source_file(file, f.new_node_list(&statements), file.end_of_file_token());
        }

        self.current_source_file = Node::NIL;
        self.import_specifier = String::new();
        self.filename_declaration = Node::NIL;
        self.utilized_implicit_runtime_imports.clear();

        visited
    }

    /// Go `core.NewTextRange(scanner.SkipTrivia(tx.currentSourceFile.Text(), node.Pos()), node.End())`.
    fn trivia_skipped_location(&self, node: Node) -> TextRange {
        TextRange::new(
            skip_trivia(source_file_text(self.current_source_file), node.pos()),
            node.end(),
        )
    }

    /// Calls the Go `tagTransform` method value.
    fn run_tag_transform(
        &mut self,
        tag_transform: TagTransform,
        element: Node,
        children: NodeList,
        location: TextRange,
    ) -> Node {
        match tag_transform {
            TagTransform::Jsx => {
                self.visit_jsx_opening_like_element_jsx(element, children, location)
            }
            TagTransform::CreateElement => {
                self.visit_jsx_opening_like_element_create_element(element, children, location)
            }
        }
    }

    // Go: transformers/jsxtransforms/jsx.go:280 JSXTransformer.visitJsxElement
    fn visit_jsx_element(&mut self, element: Node) -> Node {
        let mut tag_transform = TagTransform::Jsx;
        if self.should_use_create_element(element) {
            tag_transform = TagTransform::CreateElement;
        }
        let location = self.trivia_skipped_location(element);
        self.run_tag_transform(
            tag_transform,
            element.opening_element(),
            element.children(),
            location,
        )
    }

    // Go: transformers/jsxtransforms/jsx.go:289 JSXTransformer.visitJsxSelfClosingElement
    fn visit_jsx_self_closing_element(&mut self, element: Node) -> Node {
        let mut tag_transform = TagTransform::Jsx;
        if self.should_use_create_element(element) {
            tag_transform = TagTransform::CreateElement;
        }
        let location = self.trivia_skipped_location(element);
        self.run_tag_transform(tag_transform, element, NodeList::NIL, location)
    }

    // Go: transformers/jsxtransforms/jsx.go:298 JSXTransformer.visitJsxFragment
    fn visit_jsx_fragment(&mut self, fragment: Node) -> Node {
        let location = self.trivia_skipped_location(fragment);
        if self.import_specifier.is_empty() {
            return self.visit_jsx_opening_fragment_create_element(
                fragment.opening_fragment(),
                fragment.children(),
                location,
            );
        }
        self.visit_jsx_opening_fragment_jsx(
            fragment.opening_fragment(),
            fragment.children(),
            location,
        )
    }

    // Go: transformers/jsxtransforms/jsx.go:307 JSXTransformer.convertJsxChildrenToChildrenPropObject
    fn convert_jsx_children_to_children_prop_object(&mut self, children: &[Node]) -> Node {
        let prop = self.convert_jsx_children_to_children_prop_assignment(children);
        if prop.is_nil() {
            return Node::NIL;
        }
        let ec = self.emit_context.clone();
        let f = ec.factory();
        f.new_object_literal_expression(f.new_node_list(&[prop]), false)
    }

    // Go: transformers/jsxtransforms/jsx.go:315 JSXTransformer.transformJsxChildToExpression
    fn transform_jsx_child_to_expression(&mut self, node: Node) -> Node {
        let prev = self.in_jsx_child;
        self.set_in_child(true);
        let result = self.visit(node);
        self.set_in_child(prev);
        result
    }

    // Go: transformers/jsxtransforms/jsx.go:322 JSXTransformer.convertJsxChildrenToChildrenPropAssignment
    fn convert_jsx_children_to_children_prop_assignment(&mut self, children: &[Node]) -> Node {
        let ec = self.emit_context.clone();
        let f = ec.factory();
        let non_whitespce_children = get_semantic_jsx_children(children);
        if non_whitespce_children.len() == 1
            && (non_whitespce_children[0].kind() != SyntaxKind::JsxExpression
                || non_whitespce_children[0].dot_dot_dot_token().is_nil())
        {
            let result = self.transform_jsx_child_to_expression(non_whitespce_children[0]);
            if result.is_nil() {
                return Node::NIL;
            }
            return f.new_property_assignment(
                ModifierList::NIL,
                f.new_identifier("children"),
                Node::NIL,
                Node::NIL,
                result,
            );
        }
        // For multiple children in the children property array, don't set StartOnNewLine
        // on child elements — the array literal is single-line.
        let mut results: Vec<Node> = Vec::with_capacity(non_whitespce_children.len());
        for child in non_whitespce_children {
            let res = self.transform_jsx_child_to_expression(child);
            if res.is_nil() {
                continue;
            }
            ec.set_emit_flags(
                res,
                ec.emit_flags(res).without(EmitFlags::START_ON_NEW_LINE),
            );
            results.push(res);
        }
        if results.is_empty() {
            return Node::NIL;
        }
        f.new_property_assignment(
            ModifierList::NIL,
            f.new_identifier("children"),
            Node::NIL,
            Node::NIL,
            f.new_array_literal_expression(f.new_node_list(&results), false),
        )
    }

    // Go: transformers/jsxtransforms/jsx.go:348 JSXTransformer.getTagName
    fn get_tag_name(&mut self, node: Node) -> Node {
        let ec = self.emit_context.clone();
        let f = ec.factory();
        if node.kind() == SyntaxKind::JsxElement {
            self.get_tag_name(node.opening_element())
        } else if is_jsx_opening_like_element(node) {
            let tag_name = node.tag_name();
            if is_identifier(tag_name) && is_intrinsic_jsx_name(tag_name.text()) {
                f.new_string_literal(tag_name.text(), TokenFlags::NONE)
            } else if is_jsx_namespaced_name(tag_name) {
                f.new_string_literal(
                    format!("{}:{}", tag_name.namespace().text(), tag_name.name().text()),
                    TokenFlags::NONE,
                )
            } else {
                f.create_expression_from_entity_name(tag_name)
            }
        } else {
            panic!(
                "unhandled node kind passed to getTagName: {:?}",
                node.kind()
            )
        }
    }

    // Go: transformers/jsxtransforms/jsx.go:367 JSXTransformer.visitJsxOpeningLikeElementJSX
    fn visit_jsx_opening_like_element_jsx(
        &mut self,
        element: Node,
        children: NodeList,
        location: TextRange,
    ) -> Node {
        let ec = self.emit_context.clone();
        let f = ec.factory();
        let tag_name = self.get_tag_name(element);
        let mut children_prop = Node::NIL;
        if children.is_some() && !children.nodes().is_empty() {
            children_prop =
                self.convert_jsx_children_to_children_prop_assignment(&children.nodes().to_vec());
        }
        let mut key_attr = Node::NIL;
        let mut attrs = element.attributes().properties().to_vec();
        for (i, p) in attrs.iter().copied().enumerate() {
            if p.kind() == SyntaxKind::JsxAttribute
                && p.name().is_some()
                && is_identifier(p.name())
                && p.name().text() == "key"
            {
                key_attr = p;
                attrs.remove(i);
                break;
            }
        }
        let object;
        if !attrs.is_empty() {
            object = self.transform_jsx_attributes_to_object_props(&attrs, children_prop);
        } else {
            let mut object_children: Vec<Node> = Vec::new();
            if children_prop.is_some() {
                object_children.push(children_prop);
            }
            object = f.new_object_literal_expression(f.new_node_list(&object_children), false); // When there are no attributes, React wants {}
        }
        self.visit_jsx_opening_like_element_or_fragment_jsx(
            tag_name, object, key_attr, children, location,
        )
    }

    // Go: transformers/jsxtransforms/jsx.go:402 JSXTransformer.transformJsxAttributesToObjectProps
    fn transform_jsx_attributes_to_object_props(
        &mut self,
        attrs: &[Node],
        children_prop: Node,
    ) -> Node {
        let target = self.compiler_options.get_emit_script_target();
        if target >= ScriptTarget::ES2018 {
            // target has object spreads, can keep as-is
            let props = self.transform_jsx_attributes_to_props(attrs, children_prop);
            let ec = self.emit_context.clone();
            let f = ec.factory();
            return f.new_object_literal_expression(f.new_node_list(&props), false);
        }
        self.transform_jsx_attributes_to_expression(attrs, children_prop)
    }

    // Go: transformers/jsxtransforms/jsx.go:411 JSXTransformer.transformJsxAttributesToExpression
    fn transform_jsx_attributes_to_expression(
        &mut self,
        attrs: &[Node],
        children_prop: Node,
    ) -> Node {
        let mut expressions: Vec<Node> = Vec::with_capacity(2);
        let mut properties: Vec<Node> = Vec::with_capacity(attrs.len());

        for &attr in attrs {
            if is_jsx_spread_attribute(attr) {
                // as an optimization we try to flatten the first level of spread inline object
                // as if its props would be passed as JSX attributes
                if is_object_literal_expression(attr.expression()) && !has_proto(attr.expression())
                {
                    for prop in attr.expression().properties().iter() {
                        if is_spread_assignment(prop) {
                            self.combine_properties_into_new_expression(
                                &mut expressions,
                                &mut properties,
                            );
                            let e = self.visit(prop.expression());
                            expressions.push(e);
                            continue;
                        }
                        let p = self.visit(prop);
                        properties.push(p);
                    }
                    continue;
                }
                self.combine_properties_into_new_expression(&mut expressions, &mut properties);
                let e = self.visit(attr.expression());
                expressions.push(e);
                continue;
            }
            let p = self.transform_jsx_attribute_to_object_literal_element(attr);
            properties.push(p);
        }

        if children_prop.is_some() {
            properties.push(children_prop);
        }

        self.combine_properties_into_new_expression(&mut expressions, &mut properties);

        let ec = self.emit_context.clone();
        let f = ec.factory();
        if !expressions.is_empty() && !is_object_literal_expression(expressions[0]) {
            // We must always emit at least one object literal before a spread attribute
            // as the JSX always factory expects a fresh object, so we need to make a copy here
            // we also avoid mutating an external reference by doing this (first expression is used as assign's target)
            expressions.insert(
                0,
                f.new_object_literal_expression(f.new_node_list(&[]), false),
            );
        }

        if expressions.len() == 1 {
            return expressions[0];
        }
        f.new_assign_helper(&expressions, self.compiler_options.get_emit_script_target())
    }

    // Go: transformers/jsxtransforms/jsx.go:456 JSXTransformer.combinePropertiesIntoNewExpression
    // PORT: Go returns the updated slices; this updates them in place.
    fn combine_properties_into_new_expression(
        &mut self,
        expressions: &mut Vec<Node>,
        props: &mut Vec<Node>,
    ) {
        if props.is_empty() {
            return;
        }
        let ec = self.emit_context.clone();
        let f = ec.factory();
        let new_obj = f.new_object_literal_expression(f.new_node_list(props), false);
        expressions.push(new_obj);
        props.clear();
    }

    // Go: transformers/jsxtransforms/jsx.go:465 JSXTransformer.transformJsxAttributesToProps
    fn transform_jsx_attributes_to_props(
        &mut self,
        attrs: &[Node],
        children_prop: Node,
    ) -> Vec<Node> {
        let mut props: Vec<Node> = Vec::with_capacity(attrs.len());
        for &attr in attrs {
            if attr.kind() == SyntaxKind::JsxSpreadAttribute {
                let res = self.transform_jsx_spread_attributes_to_props(attr);
                props.extend(res);
            } else {
                let p = self.transform_jsx_attribute_to_object_literal_element(attr);
                props.push(p);
            }
        }
        if children_prop.is_some() {
            props.push(children_prop);
        }
        props
    }

    // Go: transformers/jsxtransforms/jsx.go:490 JSXTransformer.transformJsxSpreadAttributesToProps
    fn transform_jsx_spread_attributes_to_props(&mut self, node: Node) -> Vec<Node> {
        let expression = node.expression();
        if is_object_literal_expression(expression) && !has_proto(expression) {
            let properties = expression.properties().to_vec();
            let (res, _) = self.with_visitor(|v| v.visit_slice(&properties));
            return res;
        }
        let e = self.visit(expression);
        vec![self.emit_context.factory().new_spread_assignment(e)]
    }

    // Go: transformers/jsxtransforms/jsx.go:498 JSXTransformer.transformJsxAttributeToObjectLiteralElement
    fn transform_jsx_attribute_to_object_literal_element(&mut self, node: Node) -> Node {
        let name = self.get_attribute_name(node);
        let expression = self.transform_jsx_attribute_initializer(node.initializer());
        self.emit_context.factory().new_property_assignment(
            ModifierList::NIL,
            name,
            Node::NIL,
            Node::NIL,
            expression,
        )
    }

    // Go: transformers/jsxtransforms/jsx.go:509 JSXTransformer.getAttributeName
    /// Emit an attribute name, which is quoted if it needs to be quoted. Because
    /// these emit into an object literal property name, we don't need to be worried
    /// about keywords, just non-identifier characters
    fn get_attribute_name(&mut self, node: Node) -> Node {
        let f = self.emit_context.factory();
        let name = node.name();
        if is_identifier(name) {
            let text = name.text();
            if is_identifier_text(text, LanguageVariant::STANDARD) {
                return name;
            }
            return f.new_string_literal(text, TokenFlags::NONE);
        }
        // must be jsx namespace
        f.new_string_literal(
            format!("{}:{}", name.namespace().text(), name.name().text()),
            TokenFlags::NONE,
        )
    }

    // Go: transformers/jsxtransforms/jsx.go:524 JSXTransformer.transformJsxAttributeInitializer
    fn transform_jsx_attribute_initializer(&mut self, node: Node) -> Node {
        let ec = self.emit_context.clone();
        let f = ec.factory();
        if node.is_nil() {
            return f.new_true_expression();
        }
        if node.kind() == SyntaxKind::StringLiteral {
            // Always recreate the literal to escape any escape sequences or newlines which may be in the original jsx string and which
            // Need to be escaped to be handled correctly in a normal string
            let res = f.new_string_literal(decode_entities(node.text()), node.token_flags());
            set_node_loc(res, node.loc());
            // Preserve the original quote style (single vs double quotes)
            // PORT: Go `res.AsStringLiteral().TokenFlags = node.AsStringLiteral().TokenFlags`
            // writes the flags without the `NewStringLiteral` mask.
            replace_node_data(
                res,
                ts_ast::NodeData::StringLiteral(Box::new(ts_ast::StringLiteralData {
                    text: res.text().to_string(),
                    token_flags: ts_ast::TokenFlags(node.token_flags().bits() as u32),
                })),
            );
            return res;
        }
        if node.kind() == SyntaxKind::JsxExpression {
            if node.expression().is_nil() {
                return f.new_true_expression();
            }
            return self.visit(node.expression());
        }
        if is_jsx_element(node) || is_jsx_self_closing_element(node) || is_jsx_fragment(node) {
            self.set_in_child(false);
            return self.visit(node);
        }
        panic!(
            "Unhandled node kind found in jsx initializer: {:?}",
            node.kind()
        )
    }

    // Go: transformers/jsxtransforms/jsx.go:550 JSXTransformer.visitJsxOpeningLikeElementOrFragmentJSX
    fn visit_jsx_opening_like_element_or_fragment_jsx(
        &mut self,
        tag_name: Node,
        object: Node,
        key_attr: Node,
        children: NodeList,
        location: TextRange,
    ) -> Node {
        let ec = self.emit_context.clone();
        let f = ec.factory();
        let mut non_whitespace_children: Vec<Node> = Vec::new();
        if children.is_some() {
            non_whitespace_children = get_semantic_jsx_children(&children.nodes().to_vec());
        }
        let is_static_children = non_whitespace_children.len() > 1
            || (non_whitespace_children.len() == 1
                && is_jsx_expression(non_whitespace_children[0])
                && non_whitespace_children[0].dot_dot_dot_token().is_some());
        let mut args: Vec<Node> = Vec::with_capacity(3);
        args.push(tag_name);
        args.push(object);
        // function jsx(type, config, maybeKey) {}
        // "maybeKey" is optional. It is acceptable to use "_jsx" without a third argument
        if key_attr.is_some() {
            let key = self.transform_jsx_attribute_initializer(key_attr.initializer());
            args.push(key);
        }

        if self.compiler_options.jsx == JsxEmit::REACT_JSX_DEV {
            let original_file = ec.most_original(self.current_source_file);
            if original_file.is_some() && is_source_file(original_file) {
                // "maybeKey" has to be replaced with "void 0" to not break the jsxDEV signature
                if key_attr.is_nil() {
                    args.push(f.new_void_zero_expression());
                }
                // isStaticChildren development flag
                if is_static_children {
                    args.push(f.new_true_expression());
                } else {
                    args.push(f.new_false_expression());
                }
                // __source development flag
                let (line, col) =
                    get_ecma_line_and_utf16_character_of_position(original_file, location.pos());
                let file_name = self.get_current_file_name_expression();
                args.push(f.new_object_literal_expression(
                    f.new_node_list(&[
                        f.new_property_assignment(
                            ModifierList::NIL,
                            f.new_identifier("fileName"),
                            Node::NIL,
                            Node::NIL,
                            file_name,
                        ),
                        f.new_property_assignment(
                            ModifierList::NIL,
                            f.new_identifier("lineNumber"),
                            Node::NIL,
                            Node::NIL,
                            f.new_numeric_literal(
                                (i64::from(line) + 1).to_string(),
                                TokenFlags::NONE,
                            ),
                        ),
                        f.new_property_assignment(
                            ModifierList::NIL,
                            f.new_identifier("columnNumber"),
                            Node::NIL,
                            Node::NIL,
                            f.new_numeric_literal(
                                (i64::from(col) + 1).to_string(),
                                TokenFlags::NONE,
                            ),
                        ),
                    ]),
                    false,
                ));
                // __self development flag
                args.push(f.new_this_expression());
            }
        }

        let callee = self.get_jsx_factory_callee(is_static_children);
        let element = f.new_call_expression(
            callee,
            Node::NIL,
            NodeList::NIL,
            f.new_node_list(&args),
            NodeFlags::NONE,
        );
        set_node_loc(element, location);

        if self.in_jsx_child {
            ec.add_emit_flags(element, EmitFlags::START_ON_NEW_LINE);
        }

        element
    }

    // Go: transformers/jsxtransforms/jsx.go:605 JSXTransformer.visitJsxOpeningFragmentJSX
    fn visit_jsx_opening_fragment_jsx(
        &mut self,
        _fragment: Node,
        children: NodeList,
        location: TextRange,
    ) -> Node {
        let mut children_props = Node::NIL;
        if children.is_some() && !children.nodes().is_empty() {
            let result =
                self.convert_jsx_children_to_children_prop_object(&children.nodes().to_vec());
            if result.is_some() {
                children_props = result;
            }
        }
        if children_props.is_nil() {
            let f = self.emit_context.factory();
            children_props = f.new_object_literal_expression(f.new_node_list(&[]), false);
        }
        let tag_name = self.get_implicit_jsx_fragment_reference();
        self.visit_jsx_opening_like_element_or_fragment_jsx(
            tag_name,
            children_props,
            Node::NIL,
            children,
            location,
        )
    }

    // Go: transformers/jsxtransforms/jsx.go:625 JSXTransformer.createReactNamespace
    fn create_react_namespace(&mut self, react_namespace: &str, parent: Node) -> Node {
        // To ensure the emit resolver can properly resolve the namespace, we need to
        // treat this identifier as if it were a source tree node by clearing the `Synthesized`
        // flag and setting a parent node. TODO: Is this still true? The emit resolver is supposed to be
        // hardened aginast this, so long as the node retains original node pointers back to a parsed node
        let react_namespace = if react_namespace.is_empty() {
            "React"
        } else {
            react_namespace
        };
        let ec = self.emit_context.clone();
        let f = ec.factory();
        let react = f.new_identifier(react_namespace);
        set_node_flags(react, react.flags().without(NodeFlags::SYNTHESIZED));

        // Set the parent that is in parse tree
        // this makes sure that parent chain is intact for checker to traverse complete scope tree
        set_node_parent(react, ec.parse_node(parent));

        // If the identifier refers to an exported member of a namespace, substitute with
        // a qualified namespace property access (e.g., `React` -> `M.React`).
        // See also: RuntimeSyntaxTransformer.visitExpressionIdentifier in runtimesyntax.go
        let container = self
            .emit_resolver
            .get_referenced_export_container(react, false /*prefixLocals*/);
        if container.is_some() && is_module_declaration(container) {
            let container_name = f.new_generated_name_for_node(container);
            return f.new_property_access_expression(
                container_name,
                Node::NIL,
                react,
                NodeFlags::NONE,
            );
        }

        react
    }

    // Go: transformers/jsxtransforms/jsx.go:651 JSXTransformer.createJsxFactoryExpressionFromEntityName
    fn create_jsx_factory_expression_from_entity_name(&mut self, e: Node, parent: Node) -> Node {
        if is_qualified_name(e) {
            let left = self.create_jsx_factory_expression_from_entity_name(e.left(), parent);
            let f = self.emit_context.factory();
            let right = f.new_identifier(e.right().text());
            return f.new_property_access_expression(left, Node::NIL, right, NodeFlags::NONE);
        }
        self.create_react_namespace(e.text(), parent)
    }

    // Go: transformers/jsxtransforms/jsx.go:660 JSXTransformer.createJsxPseudoFactoryExpression
    fn create_jsx_pseudo_factory_expression(
        &mut self,
        parent: Node,
        e: Node,
        target: &str,
    ) -> Node {
        if e.is_some() {
            return self.create_jsx_factory_expression_from_entity_name(e, parent);
        }
        let compiler_options = self.compiler_options;
        let namespace = self.create_react_namespace(&compiler_options.react_namespace, parent);
        let f = self.emit_context.factory();
        f.new_property_access_expression(
            namespace,
            Node::NIL,
            f.new_identifier(target),
            NodeFlags::NONE,
        )
    }

    // Go: transformers/jsxtransforms/jsx.go:672 JSXTransformer.createJsxFactoryExpression
    fn create_jsx_factory_expression(&mut self, parent: Node) -> Node {
        let e = self
            .emit_resolver
            .get_jsx_factory_entity(self.current_source_file);
        self.create_jsx_pseudo_factory_expression(parent, e, "createElement")
    }

    // Go: transformers/jsxtransforms/jsx.go:677 JSXTransformer.createJsxFragmentFactoryExpression
    fn create_jsx_fragment_factory_expression(&mut self, parent: Node) -> Node {
        let e = self
            .emit_resolver
            .get_jsx_fragment_factory_entity(self.current_source_file);
        self.create_jsx_pseudo_factory_expression(parent, e, "Fragment")
    }

    /// Go: the children loop and the `StartOnNewLine` loop that
    /// `visitJsxOpeningLikeElementCreateElement` and
    /// `visitJsxOpeningFragmentCreateElement` both write inline.
    fn transform_create_element_children(&mut self, children: NodeList) -> Vec<Node> {
        let mut new_children: Vec<Node> = Vec::new();
        if children.is_some() && !children.nodes().is_empty() {
            for c in children.nodes().iter() {
                let res = self.transform_jsx_child_to_expression(c);
                if res.is_some() {
                    new_children.push(res);
                }
            }
        }

        // Add StartOnNewLine flag only if there are multiple actual children (after filtering)
        if new_children.len() > 1 {
            for &child in &new_children {
                self.emit_context
                    .add_emit_flags(child, EmitFlags::START_ON_NEW_LINE);
            }
        }
        new_children
    }

    // Go: transformers/jsxtransforms/jsx.go:682 JSXTransformer.visitJsxOpeningLikeElementCreateElement
    fn visit_jsx_opening_like_element_create_element(
        &mut self,
        element: Node,
        children: NodeList,
        location: TextRange,
    ) -> Node {
        let tag_name = self.get_tag_name(element);
        let attrs = element.attributes().properties().to_vec();
        let object_properties = if !attrs.is_empty() {
            self.transform_jsx_attributes_to_object_props(&attrs, Node::NIL)
        } else {
            self.emit_context
                .factory()
                .new_keyword_expression(SyntaxKind::NullKeyword) // When there are no attributes, React wants "null"
        };

        let callee = if self.import_specifier.is_empty() {
            self.create_jsx_factory_expression(element)
        } else {
            self.get_implicit_import_for_name("createElement")
        };

        let new_children = self.transform_create_element_children(children);

        let mut args: Vec<Node> = Vec::with_capacity(new_children.len() + 2);
        args.push(tag_name);
        args.push(object_properties);
        args.extend(new_children);

        let ec = self.emit_context.clone();
        let f = ec.factory();
        let result = f.new_call_expression(
            callee,
            Node::NIL,
            NodeList::NIL,
            f.new_node_list(&args),
            NodeFlags::NONE,
        );
        set_node_loc(result, location);

        if self.in_jsx_child {
            ec.add_emit_flags(result, EmitFlags::START_ON_NEW_LINE);
        }
        result
    }

    // Go: transformers/jsxtransforms/jsx.go:736 JSXTransformer.visitJsxOpeningFragmentCreateElement
    fn visit_jsx_opening_fragment_create_element(
        &mut self,
        fragment: Node,
        children: NodeList,
        location: TextRange,
    ) -> Node {
        let tag_name = self.create_jsx_fragment_factory_expression(fragment);
        let callee = self.create_jsx_factory_expression(fragment);

        let new_children = self.transform_create_element_children(children);

        let ec = self.emit_context.clone();
        let f = ec.factory();
        let mut args: Vec<Node> = Vec::with_capacity(new_children.len() + 2);
        args.push(tag_name);
        args.push(f.new_keyword_expression(SyntaxKind::NullKeyword));
        args.extend(new_children);

        let result = f.new_call_expression(
            callee,
            Node::NIL,
            NodeList::NIL,
            f.new_node_list(&args),
            NodeFlags::NONE,
        );
        set_node_loc(result, location);

        if self.in_jsx_child {
            ec.add_emit_flags(result, EmitFlags::START_ON_NEW_LINE);
        }
        result
    }

    // Go: transformers/jsxtransforms/jsx.go:777 JSXTransformer.visitJsxText
    fn visit_jsx_text(&mut self, text: Node) -> Node {
        let fixed = fixup_whitespace_and_decode_entities(text.text());
        if fixed.is_empty() {
            return Node::NIL;
        }
        self.emit_context
            .factory()
            .new_string_literal(fixed, TokenFlags::NONE)
    }

    // Go: transformers/jsxtransforms/jsx.go:852 JSXTransformer.visitJsxExpression
    fn visit_jsx_expression(&mut self, expression: Node) -> Node {
        let e = self.visit(expression.expression());
        if expression.dot_dot_dot_token().is_some() {
            return self.emit_context.factory().new_spread_element(e);
        }
        e
    }
}

// Go: transformers/jsxtransforms/jsx.go:141 hasKeyAfterPropsSpread
/// The react jsx/jsxs transform falls back to `createElement` when an explicit `key` argument comes after a spread
fn has_key_after_props_spread(node: Node) -> bool {
    let mut spread = false;
    let mut opener = node;
    if node.kind() == SyntaxKind::JsxElement {
        opener = node.opening_element();
    } // otherwise self-closing
    for elem in opener.attributes().properties().iter() {
        if is_jsx_spread_attribute(elem)
            && (!is_object_literal_expression(elem.expression())
                || elem
                    .expression()
                    .properties()
                    .iter()
                    .any(is_spread_assignment))
        {
            spread = true;
        } else if spread
            && is_jsx_attribute(elem)
            && is_identifier(elem.name())
            && elem.name().text() == "key"
        {
            return true;
        }
    }
    false
}

// Go: transformers/jsxtransforms/jsx.go:161 insertStatementAfterPrologue
// PORT: Go passes a method expression plus its receiver; a closure does both here.
fn insert_statement_after_prologue(
    mut to: Vec<Node>,
    statement: Node,
    is_prologue_directive: impl Fn(Node) -> bool,
) -> Vec<Node> {
    if statement.is_nil() {
        return to;
    }
    let mut statement_idx = 0;
    // skip all prologue directives to insert at the correct position
    while statement_idx < to.len() {
        if !is_prologue_directive(to[statement_idx]) {
            break;
        }
        statement_idx += 1;
    }
    to.insert(statement_idx, statement);
    to
}

// Go: transformers/jsxtransforms/jsx.go:183 sortImportSpecifiers
fn sort_import_specifiers(a: &Node, b: &Node) -> std::cmp::Ordering {
    // PORT: Go `stringutil.CompareStringsCaseSensitive` is `strings.Compare`,
    // a byte order compare, as `str::cmp` is.
    let res = a.property_name().text().cmp(b.property_name().text());
    if res != std::cmp::Ordering::Equal {
        return res;
    }
    a.name().text().cmp(b.name().text())
}

// Go: transformers/jsxtransforms/jsx.go:191 getSortedSpecifiers
fn get_sorted_specifiers(m: &FxHashMap<String, Node>) -> Vec<Node> {
    let mut res: Vec<Node> = m.values().copied().collect();
    res.sort_by(sort_import_specifiers);
    res
}

// Go: transformers/jsxtransforms/jsx.go:481 hasProto
/// PORT: Go takes `*ast.ObjectLiteralExpression`; this takes the node.
fn has_proto(obj: Node) -> bool {
    for p in obj.properties().iter() {
        if is_property_assignment(p)
            && (is_string_literal(p.name()) || is_identifier(p.name()))
            && p.name().text() == "__proto__"
        {
            return true;
        }
    }
    false
}

// Go: transformers/jsxtransforms/jsx.go:785 addLineOfJsxText
fn add_line_of_jsx_text(b: &mut String, trimmed_line: &str, is_initial: bool) {
    // We do not escape the string here as that is handled by the printer
    // when it emits the literal. We do, however, need to decode JSX entities.
    let decoded = decode_entities(trimmed_line);
    if !is_initial {
        b.push(' ');
    }
    b.push_str(&decoded);
}

// Go: transformers/jsxtransforms/jsx.go:810 fixupWhitespaceAndDecodeEntities
/// JSX trims whitespace at the end and beginning of lines, except that the
/// start/end of a tag is considered a start/end of a line only if that line is
/// on the same line as the closing tag. See examples in
/// tests/cases/conformance/jsx/tsxReactEmitWhitespace.tsx
/// See also https://www.w3.org/TR/html4/struct/text.html#h-9.1 and https://www.w3.org/TR/CSS2/text.html#white-space-model
///
/// An equivalent algorithm would be:
/// - If there is only one line, return it.
/// - If there is only whitespace (but multiple lines), return `undefined`.
/// - Split the text into lines.
/// - 'trimRight' the first line, 'trimLeft' the last line, 'trim' middle lines.
/// - Decode entities on each line (individually).
/// - Remove empty lines and join the rest with " ".
pub fn fixup_whitespace_and_decode_entities(text: &str) -> String {
    let mut acc = String::new();
    let mut initial = true;
    // First non-whitespace character on this line.
    let mut first_non_whitespace: isize = 0;
    // End byte position of the last non-whitespace character on this line.
    let mut last_non_whitespace_end: isize = -1;
    // These initial values are special because the first line is:
    // firstNonWhitespace = 0 to indicate that we want leading whitespace,
    // but lastNonWhitespaceEnd = -1 as a special flag to indicate that we *don't* include the line if it's all whitespace.
    // PORT: Go decodes one rune per step and skips its extra bytes; `char_indices` does both.
    for (i, c) in text.char_indices() {
        let size = c.len_utf8();
        if is_line_break(c) {
            // If we've seen any non-whitespace characters on this line, add the 'trim' of the line.
            // (lastNonWhitespaceEnd === -1 is a special flag to detect whether the first line is all whitespace.)
            if first_non_whitespace != -1 && last_non_whitespace_end != -1 {
                add_line_of_jsx_text(
                    &mut acc,
                    &text[first_non_whitespace as usize..(last_non_whitespace_end + 1) as usize],
                    initial,
                );
                initial = false;
            }

            // Reset firstNonWhitespace for the next line.
            // Don't bother to reset lastNonWhitespaceEnd because we ignore it if firstNonWhitespace = -1.
            first_non_whitespace = -1;
        } else if !is_white_space_single_line(c) {
            last_non_whitespace_end = (i + size - 1) as isize; // Store the end byte position of the character
            if first_non_whitespace == -1 {
                first_non_whitespace = i as isize;
            }
        }
    }

    if first_non_whitespace != -1 {
        // Last line had a non-whitespace character. Emit the 'trimLeft', meaning keep trailing whitespace.
        add_line_of_jsx_text(&mut acc, &text[first_non_whitespace as usize..], initial);
    }
    acc
}

// Go: transformers/jsxtransforms/jsx.go:864 decodeEntities
/// Replace entities like "&nbsp;", "&#123;", and "&#xDEADBEEF;" with the characters they encode.
/// See https://en.wikipedia.org/wiki/List_of_XML_and_HTML_character_entity_references
pub fn decode_entities(text: &str) -> String {
    let Some(mut i) = text.find('&') else {
        return text.to_string();
    };

    let mut text = text;
    let mut result = String::with_capacity(text.len());
    loop {
        result.push_str(&text[..i]);
        text = &text[i..];

        let Some(mut semi) = text.find(';') else {
            break;
        };

        // Skip past any intervening '&' characters between the current '&'
        // and the ';'. Each such '&' is not part of a valid entity, so emit
        // it (and any text before the next '&') as literals.
        while let Some(next_amp) = text[1..semi].find('&') {
            result.push_str(&text[..next_amp + 1]);
            text = &text[next_amp + 1..];
            semi -= next_amp + 1;
        }

        let entity = &text[1..semi];
        match decode_entity(entity) {
            Some(decoded) => {
                // Use the JS-string encoder so lone surrogates (e.g. "&#xD800;")
                // are preserved rather than being lost to U+FFFD by WriteRune.
                result.push_str(&encode_js_string_rune(decoded));
            }
            None => result.push_str(&text[..semi + 1]),
        }
        text = &text[semi + 1..];

        match text.find('&') {
            Some(next) => i = next,
            None => break,
        }
    }
    result.push_str(text);
    result
}

// Go: transformers/jsxtransforms/jsx.go:914 decodeEntity
/// PORT: Go returns `(rune, bool)`; `None` is Go `false`. The rune is a
/// `u32` because a lone surrogate is not a Rust `char`.
fn decode_entity(entity: &str) -> Option<u32> {
    if entity.is_empty() {
        return None;
    }

    if let Some(rest) = entity.strip_prefix('#') {
        let mut entity = rest;
        if entity.is_empty() {
            return None;
        }

        let mut base = 10;
        if let Some(hex) = entity.strip_prefix('x') {
            base = 16;
            entity = hex;
        }

        if entity.is_empty() {
            return None;
        }

        for c in entity.chars() {
            if base == 16 && !is_hex_digit(c) {
                return None;
            }
            if base == 10 && !is_digit(c) {
                return None;
            }
        }

        // PORT: Go `strconv.ParseInt(entity, base, 32)` fails on values
        // above `math.MaxInt32`; `i32::from_str_radix` does the same. Only
        // digits reach here, so no sign is accepted.
        let parsed = i32::from_str_radix(entity, base).ok()?;
        return Some(parsed as u32);
    }

    entity_code_point(entity)
}
