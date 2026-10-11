//! Port of Effect-TS/tsgo `internal/typeparser/expected_and_real_type.go`.

use crate::effect::typeparser::*;
use crate::prelude::*;
use std::collections::VecDeque;

/// Go `ExpectedAndRealType`: a pair of expected and actual types at an
/// assignment site. This is used by diagnostic rules that need to compare
/// what type was expected at a location versus what type was actually
/// provided.
#[derive(Clone, Copy, Debug)]
pub struct ExpectedAndRealType {
    /// The location node (for diagnostic reporting)
    pub node: Node,
    /// The type expected at this location
    pub expected_type: TypeId,
    /// The actual value node
    pub value_node: Node,
    /// The actual type of the value
    pub real_type: TypeId,
}

impl TypeParser<'_> {
    /// Go `getInferredReturnType`: extracts the return type from a
    /// function-like declaration. It handles overloaded functions (multiple
    /// call signatures), type predicates, and regular signature return types.
    pub fn get_inferred_return_type(&mut self, declaration: Node) -> TypeId {
        if declaration.is_nil() {
            return TypeId::NIL;
        }

        // Check that the declaration has a body
        // PORT: Go `bodyData == nil || bodyData.Body == nil` is Go
        // `declaration.Body() == nil`.
        if declaration.body().is_nil() {
            return TypeId::NIL;
        }

        let mut return_type = TypeId::NIL;

        // Try overloaded function handling:
        // Get the type at the declaration location, get call signatures,
        // and if there are multiple signatures, union their return types.
        let decl_type = self.get_type_at_location(declaration);
        if decl_type.is_some() {
            let signatures = self
                .checker
                .get_signatures_of_type_exported(decl_type, SignatureKind::CALL);
            if signatures.len() > 1 {
                let mut return_types: Vec<TypeId> = Vec::new();
                for sig in signatures {
                    let rt = self.checker.get_return_type_of_signature_exported(sig);
                    if rt.is_some() {
                        return_types.push(rt);
                    }
                }
                if !return_types.is_empty() {
                    return_type = self.checker.get_union_type_exported(&return_types);
                }
            }
        }

        if return_type.is_nil() {
            let sig = self
                .checker
                .get_signature_from_declaration_exported(declaration);
            if sig.is_some() {
                let type_predicate = self.checker.get_type_predicate_of_signature_exported(sig);
                if type_predicate.is_some() && self.checker.pred(type_predicate).t.is_some() {
                    return self.checker.pred(type_predicate).t;
                }
                return_type = self.checker.get_return_type_of_signature_exported(sig);
            }
        }

        return_type
    }

    /// Go `ExpectedAndRealTypes`: walks the AST of a source file using
    /// breadth-first traversal and collects pairs of expected vs actual types
    /// at assignment sites.
    ///
    /// It recognizes 8 assignment site patterns:
    /// 1. Variable declaration with initializer (const a: T = expr)
    /// 2. Call expression arguments (fn(a))
    /// 3. Object literal property keys ({ key: expr } as { key: T })
    /// 4. Binary assignment (a = expr)
    /// 5. Return statement (return expr)
    /// 6. Arrow function body without type params ((): T => expr)
    /// 7. Arrow function body with type params (<A>(): T => expr)
    /// 8. Satisfies expression (expr satisfies T)
    ///
    /// PORT: the Go `tp == nil || tp.checker == nil` guard cannot fail here.
    /// The Go nil result for a nil `sf` is an empty list.
    pub fn expected_and_real_types(&mut self, sf: Node) -> Rc<Vec<ExpectedAndRealType>> {
        if sf.is_nil() {
            return Rc::new(Vec::new());
        }

        cached!(self, expected_and_real_types, sf, {
            let mut result: Vec<ExpectedAndRealType> = Vec::new();

            // Initialize BFS queue with the source file node
            let mut queue: VecDeque<Node> = VecDeque::new();
            queue.push_back(sf);

            // Dequeue from front (FIFO/breadth-first) to match TypeScript's shift() behavior
            while let Some(node) = queue.pop_front() {
                if node.is_nil() {
                    continue;
                }

                // Pattern 1: Variable declaration with initializer
                if node.kind() == SyntaxKind::VariableDeclaration {
                    let initializer = node.initializer();
                    if initializer.is_some() {
                        let name_node = node.name();
                        if name_node.is_some() {
                            let expected_type = self.get_type_at_location(name_node);
                            let real_type = self.get_type_at_location(initializer);
                            result.push(ExpectedAndRealType {
                                node: name_node,
                                expected_type,
                                value_node: initializer,
                                real_type,
                            });
                        }
                        queue.push_back(initializer);
                        continue;
                    }
                }

                // Pattern 2: Call expression arguments
                if node.kind() == SyntaxKind::CallExpression {
                    let resolved_sig = self.checker.get_resolved_signature_exported(node);
                    if resolved_sig.is_some() {
                        let params = self.checker.sig(resolved_sig).parameters.clone();
                        // PORT: Go `call.Arguments != nil` guards the loop; a
                        // nil list reads as empty here, so the loop does
                        // nothing either way.
                        let arguments = node.arguments();
                        for (i, param) in params.iter().copied().enumerate() {
                            if i >= arguments.len() {
                                break;
                            }
                            let arg = arguments.get(i);
                            if arg.is_nil() {
                                continue;
                            }
                            let expected_type =
                                self.checker.get_type_of_symbol_at_location(param, node);
                            let real_type = self.get_type_at_location(arg);
                            result.push(ExpectedAndRealType {
                                node: arg,
                                expected_type,
                                value_node: arg,
                                real_type,
                            });
                        }
                    }
                    node.for_each_child(|child| {
                        queue.push_back(child);
                        false
                    });
                    continue;
                }

                // Pattern 3: Object literal property keys
                if node.kind() == SyntaxKind::Identifier
                    || node.kind() == SyntaxKind::StringLiteral
                    || node.kind() == SyntaxKind::NumericLiteral
                    || node.kind() == SyntaxKind::NoSubstitutionTemplateLiteral
                {
                    let parent = node.parent();
                    if parent.is_some() && is_object_literal_element(parent) {
                        let grandparent = parent.parent();
                        if grandparent.is_some()
                            && grandparent.kind() == SyntaxKind::ObjectLiteralExpression
                        {
                            // Check that this node is the name of the property (not the value)
                            let name_node = get_object_literal_element_name(parent);
                            if name_node == node {
                                let contextual_type = self
                                    .checker
                                    .get_contextual_type_exported(grandparent, ContextFlags::NONE);
                                if contextual_type.is_some() {
                                    let name = get_node_text_for_property_lookup(node);
                                    if !name.is_empty() {
                                        let sym = self
                                            .checker
                                            .get_property_of_type_exported(contextual_type, &name);
                                        if sym.is_some() {
                                            let expected_type = self
                                                .checker
                                                .get_type_of_symbol_at_location(sym, node);
                                            let real_type = self.get_type_at_location(node);
                                            result.push(ExpectedAndRealType {
                                                node,
                                                expected_type,
                                                value_node: node,
                                                real_type,
                                            });
                                        }
                                    }
                                }
                            }
                        }
                    }
                    node.for_each_child(|child| {
                        queue.push_back(child);
                        false
                    });
                    continue;
                }

                // Pattern 4: Binary assignment (a = expr)
                if node.kind() == SyntaxKind::BinaryExpression {
                    let operator_token = node.operator_token();
                    if operator_token.is_some() && operator_token.kind() == SyntaxKind::EqualsToken
                    {
                        let left = node.left();
                        let right = node.right();
                        if left.is_some() && right.is_some() {
                            let expected_type = self.get_type_at_location(left);
                            let real_type = self.get_type_at_location(right);
                            result.push(ExpectedAndRealType {
                                node: left,
                                expected_type,
                                value_node: right,
                                real_type,
                            });
                        }
                        if right.is_some() {
                            queue.push_back(right);
                        }
                        continue;
                    }
                }

                // Pattern 5: Return statement
                if node.kind() == SyntaxKind::ReturnStatement {
                    let ret_expression = node.expression();
                    if ret_expression.is_some() {
                        let parent_decl = get_containing_function(node);
                        if parent_decl.is_some() {
                            let expected_type = self.get_inferred_return_type(parent_decl);
                            if expected_type.is_some() {
                                let real_type = self.get_type_at_location(ret_expression);
                                result.push(ExpectedAndRealType {
                                    node,
                                    expected_type,
                                    value_node: node,
                                    real_type,
                                });
                            }
                        }
                    }
                    node.for_each_child(|child| {
                        queue.push_back(child);
                        false
                    });
                    continue;
                }

                // Pattern 6 & 7: Arrow function body (expression body)
                if node.kind() == SyntaxKind::ArrowFunction {
                    let body = node.body();
                    if body.is_some() && body.kind() != SyntaxKind::Block {
                        let has_type_params = !node.type_parameters().is_empty();

                        if !has_type_params {
                            // Pattern 6: No type parameters — use contextual type
                            let expected_type = self
                                .checker
                                .get_contextual_type_exported(body, ContextFlags::NONE);
                            if expected_type.is_some() {
                                let real_type = self.get_type_at_location(body);
                                result.push(ExpectedAndRealType {
                                    node: body,
                                    expected_type,
                                    value_node: body,
                                    real_type,
                                });
                            }
                        } else {
                            // Pattern 7: With type parameters — use inferred return type
                            let expected_type = self.get_inferred_return_type(node);
                            if expected_type.is_some() {
                                let real_type = self.get_type_at_location(body);
                                result.push(ExpectedAndRealType {
                                    node: body,
                                    expected_type,
                                    value_node: body,
                                    real_type,
                                });
                            }
                        }
                        body.for_each_child(|child| {
                            queue.push_back(child);
                            false
                        });
                        continue;
                    }
                }

                // Pattern 8: Satisfies expression
                if node.kind() == SyntaxKind::SatisfiesExpression {
                    let sat_expression = node.expression();
                    let sat_type = node.type_();
                    if sat_expression.is_some() && sat_type.is_some() {
                        let expected_type = self.get_type_at_location(sat_type);
                        let real_type = self.get_type_at_location(sat_expression);
                        result.push(ExpectedAndRealType {
                            node: sat_expression,
                            expected_type,
                            value_node: sat_expression,
                            real_type,
                        });
                        queue.push_back(sat_expression);
                        continue;
                    }
                }

                // No pattern matched — queue all children for traversal
                node.for_each_child(|child| {
                    queue.push_back(child);
                    false
                });
            }

            Rc::new(result)
        })
    }
}

/// Go `getObjectLiteralElementName`: the name node of an object literal
/// element (PropertyAssignment, ShorthandPropertyAssignment, etc.), or nil.
pub fn get_object_literal_element_name(node: Node) -> Node {
    if node.is_nil() {
        return Node::NIL;
    }
    match node.kind() {
        SyntaxKind::PropertyAssignment | SyntaxKind::ShorthandPropertyAssignment => node.name(),
        _ => Node::NIL,
    }
}

/// Go `getNodeTextForPropertyLookup`: extracts the text from an identifier
/// or string literal node for use in property type lookup.
pub fn get_node_text_for_property_lookup(node: Node) -> String {
    if node.is_nil() {
        return String::new();
    }
    match node.kind() {
        SyntaxKind::Identifier => get_text_of_node(node),
        SyntaxKind::StringLiteral => node.text().to_string(),
        _ => String::new(),
    }
}
