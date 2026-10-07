//! Port of Effect-TS/tsgo `internal/typeparser/function_node.go`.

use crate::effect::typeparser::*;
use crate::prelude::*;

/// GetFunctionLikeName returns the name string from a function-like node.
/// Handles FunctionDeclaration, FunctionExpression, MethodDeclaration (with identifier name),
/// and falls back to checking the parent VariableDeclaration for arrow/expression functions.
// Go: typeparser/function_node.go GetFunctionLikeName
pub fn get_function_like_name(node: Node) -> String {
    match node.kind() {
        SyntaxKind::FunctionDeclaration => {
            let fd = node;
            if fd.name().is_some() {
                return fd.name().text().to_string();
            }
        }
        SyntaxKind::FunctionExpression => {
            let fe = node;
            if fe.name().is_some() {
                return fe.name().text().to_string();
            }
        }
        SyntaxKind::MethodDeclaration => {
            let md = node;
            if md.name().is_some() && md.name().kind() == SyntaxKind::Identifier {
                return md.name().text().to_string();
            }
        }
        _ => {}
    }

    // Check parent variable declaration for arrow/expression functions
    if node.parent().is_some() && node.parent().kind() == SyntaxKind::VariableDeclaration {
        let vd = node.parent();
        if vd.name().is_some() && vd.name().kind() == SyntaxKind::Identifier {
            return vd.name().text().to_string();
        }
    }

    String::new()
}

/// GetFunctionLikeBody returns the body node from a function-like node.
/// Handles FunctionDeclaration, FunctionExpression, ArrowFunction, and MethodDeclaration.
// Go: typeparser/function_node.go GetFunctionLikeBody
pub fn get_function_like_body(node: Node) -> Node {
    match node.kind() {
        SyntaxKind::FunctionDeclaration => {
            let fd = node;
            if fd.body().is_some() {
                return fd.body();
            }
        }
        SyntaxKind::FunctionExpression => {
            let fe = node;
            if fe.body().is_some() {
                return fe.body();
            }
        }
        SyntaxKind::ArrowFunction => {
            let af = node;
            if af.body().is_some() {
                return af.body();
            }
        }
        SyntaxKind::MethodDeclaration => {
            let md = node;
            if md.body().is_some() {
                return md.body();
            }
        }
        _ => {}
    }
    Node::NIL
}

/// GetFunctionLikeTypeParameters returns the type parameters NodeList from a function-like node.
/// Handles ArrowFunction, FunctionExpression, FunctionDeclaration, and MethodDeclaration.
// Go: typeparser/function_node.go GetFunctionLikeTypeParameters
pub fn get_function_like_type_parameters(node: Node) -> NodeList {
    match node.kind() {
        SyntaxKind::ArrowFunction => node.type_parameter_list(),
        SyntaxKind::FunctionExpression => node.type_parameter_list(),
        SyntaxKind::FunctionDeclaration => node.type_parameter_list(),
        SyntaxKind::MethodDeclaration => node.type_parameter_list(),
        _ => NodeList::NIL,
    }
}

/// GetFunctionLikeParameters returns the parameters NodeList from a function-like node.
/// Handles ArrowFunction, FunctionExpression, FunctionDeclaration, and MethodDeclaration.
// Go: typeparser/function_node.go GetFunctionLikeParameters
pub fn get_function_like_parameters(node: Node) -> NodeList {
    match node.kind() {
        SyntaxKind::ArrowFunction => node.parameter_list(),
        SyntaxKind::FunctionExpression => node.parameter_list(),
        SyntaxKind::FunctionDeclaration => node.parameter_list(),
        SyntaxKind::MethodDeclaration => node.parameter_list(),
        _ => NodeList::NIL,
    }
}
