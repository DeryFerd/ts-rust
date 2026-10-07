//! Port of Effect-TS/tsgo `internal/typeparser/expression_stability.go`.

use crate::effect::typeparser::*;
use crate::prelude::*;

impl TypeParser<'_> {
    /// IsExpressionValueStableAtLocation reports whether evaluating expression at
    /// location produces the same value as evaluating it at its original site.
    // Go: typeparser/expression_stability.go IsExpressionValueStableAtLocation
    pub fn is_expression_value_stable_at_location(
        &mut self,
        expression: Node,
        location: Node,
    ) -> bool {
        if expression.is_nil() || location.is_nil() {
            return false;
        }

        let expression = skip_parentheses(expression);
        if expression.is_nil() {
            return false;
        }

        match expression.kind() {
            SyntaxKind::StringLiteral
            | SyntaxKind::NumericLiteral
            | SyntaxKind::BigIntLiteral
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::TrueKeyword
            | SyntaxKind::FalseKeyword
            | SyntaxKind::NullKeyword => {
                return true;
            }
            SyntaxKind::Identifier => {
                let symbol = self.get_symbol_at_location(expression);
                if expression.text() == "undefined" {
                    return symbol.is_some()
                        && symbol
                            == self.checker.get_global_symbol_exported(
                                "undefined",
                                SymbolFlags::VALUE,
                                None,
                            );
                }
                if symbol.is_nil() {
                    return false;
                }
                let value_declaration = self.checker.sym(symbol).value_declaration;
                if value_declaration.is_nil()
                    || value_declaration.kind() != SyntaxKind::VariableDeclaration
                {
                    return false;
                }

                let declaration_node = value_declaration;
                let declaration = declaration_node;
                if declaration.initializer().is_nil()
                    || declaration_node.parent().is_nil()
                    || declaration_node.parent().kind() != SyntaxKind::VariableDeclarationList
                {
                    return false;
                }
                if !declaration_node
                    .parent()
                    .flags()
                    .intersects(NodeFlags::CONST)
                    || get_source_file_of_node(declaration_node)
                        != get_source_file_of_node(location)
                {
                    return false;
                }

                // Symbol resolution already proves the declaration is visible here. A
                // const's value is stable across nested lexical scopes as long as its
                // initializer occurs before the use; the same-container restriction would
                // incorrectly reject module constants referenced inside a function.
                return declaration.initializer().end() <= location.pos();
            }
            _ => {}
        }

        false
    }
}
