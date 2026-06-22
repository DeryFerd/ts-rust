//! TypeScript parser.

use ts_ast::{
    BigIntLiteralData, BinaryExpressionData, BlockData, EmptyStatementData,
    ExpressionStatementData, IdentifierData, KeywordExpressionData, KeywordTypeNodeData,
    NoSubstitutionTemplateLiteralData, Node, NodeArena, NodeData, NodeFlags, NodeId, NodeList,
    NumericLiteralData, ParenthesizedExpressionData, QualifiedNameData, SourceFileData,
    StringLiteralData, SymbolTable, SyntaxKind, TokenData, TokenFlags, TypeReferenceNodeData,
    VariableDeclarationData, VariableDeclarationListData, VariableStatementData,
};
use ts_core::{Diagnostic, TextPos, TextRange};
use ts_scanner::{Scanner, Token, TokenFlags as ScannerTokenFlags};

const NODE_FLAG_LET: NodeFlags = NodeFlags(1 << 0);
const NODE_FLAG_CONST: NodeFlags = NodeFlags(1 << 1);
const NODE_FLAG_HAS_ERROR: NodeFlags = NodeFlags(1 << 15);

/// Result of parsing one source file.
#[derive(Debug)]
pub struct ParseResult {
    pub arena: NodeArena,
    pub source_file: NodeId,
    pub diagnostics: Vec<Diagnostic>,
}

/// Parse a TypeScript source file into the generated arena-backed AST.
#[must_use]
pub fn parse_source_file(source: &str) -> ParseResult {
    Parser::new(source).parse_source_file()
}

struct Parser<'a> {
    scanner: Scanner<'a>,
    current: Token<'a>,
    arena: NodeArena,
    diagnostics: Vec<Diagnostic>,
}

impl<'a> Parser<'a> {
    fn new(source: &'a str) -> Self {
        let mut scanner = Scanner::new(source);
        let current = scanner.scan();
        Self {
            scanner,
            current,
            arena: NodeArena::new(),
            diagnostics: Vec::new(),
        }
    }

    fn parse_source_file(mut self) -> ParseResult {
        let start = TextPos::new(0);
        let statements = self.parse_statement_list(SyntaxKind::EndOfFile);
        let eof_range = self.current.range;
        let eof = self.alloc_node(
            SyntaxKind::EndOfFile,
            eof_range,
            NodeData::Token(Box::new(TokenData)),
            &[],
        );
        let source_range = TextRange::new(start, eof_range.end);
        let mut children = statements.nodes.clone();
        children.push(eof);
        let source_file = self.alloc_node(
            SyntaxKind::SourceFile,
            source_range,
            NodeData::SourceFile(Box::new(SourceFileData {
                end_of_file_token: eof,
                locals: SymbolTable,
                next_container: None,
                statements,
                symbol: None,
                facts: 0,
            })),
            &children,
        );
        self.diagnostics
            .extend(self.scanner.diagnostics().iter().cloned());
        ParseResult {
            arena: self.arena,
            source_file,
            diagnostics: self.diagnostics,
        }
    }

    fn parse_statement_list(&mut self, terminator: SyntaxKind) -> NodeList {
        let start = self.current.full_start;
        let mut statements = Vec::new();
        while self.current.kind != terminator && self.current.kind != SyntaxKind::EndOfFile {
            let before = (self.current.kind, self.current.range);
            statements.push(self.parse_statement());
            if before == (self.current.kind, self.current.range) {
                self.error_current("Parser made no progress while parsing a statement.");
                self.bump();
            }
        }
        NodeList {
            range: TextRange::new(start, self.current.full_start),
            nodes: statements,
            has_trailing_comma: false,
        }
    }

    fn parse_statement(&mut self) -> NodeId {
        match self.current.kind {
            SyntaxKind::OpenBraceToken => self.parse_block(),
            SyntaxKind::VarKeyword | SyntaxKind::LetKeyword | SyntaxKind::ConstKeyword => {
                self.parse_variable_statement()
            }
            SyntaxKind::SemicolonToken => self.parse_empty_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_block(&mut self) -> NodeId {
        let start = self.current.range.start;
        self.bump();
        let statements = self.parse_statement_list(SyntaxKind::CloseBraceToken);
        let end = if self.current.kind == SyntaxKind::CloseBraceToken {
            self.consume().range.end
        } else {
            self.error_current("Expected '}'.");
            self.current.range.start
        };
        let children = statements.nodes.clone();
        self.alloc_node(
            SyntaxKind::Block,
            TextRange::new(start, end),
            NodeData::Block(Box::new(BlockData {
                flow_node: None,
                locals: SymbolTable,
                multi_line: false,
                next_container: None,
                statements,
                facts: 0,
            })),
            &children,
        )
    }

    fn parse_empty_statement(&mut self) -> NodeId {
        let range = self.consume().range;
        self.alloc_node(
            SyntaxKind::EmptyStatement,
            range,
            NodeData::EmptyStatement(Box::new(EmptyStatementData { flow_node: None })),
            &[],
        )
    }

    fn parse_variable_statement(&mut self) -> NodeId {
        let keyword = self.consume();
        let declaration_flags = match keyword.kind {
            SyntaxKind::LetKeyword => NODE_FLAG_LET,
            SyntaxKind::ConstKeyword => NODE_FLAG_CONST,
            _ => NodeFlags::default(),
        };
        let declaration_start = self.current.range.start;
        let mut declarations = Vec::new();
        loop {
            declarations.push(self.parse_variable_declaration());
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
        }
        let declarations_end = declarations
            .last()
            .and_then(|id| self.arena.get(*id))
            .map_or(declaration_start, |node| node.range.end);
        let declaration_list = self.alloc_node_with_flags(
            SyntaxKind::VariableDeclarationList,
            declaration_flags,
            TextRange::new(declaration_start, declarations_end),
            NodeData::VariableDeclarationList(Box::new(VariableDeclarationListData {
                declarations: NodeList {
                    range: TextRange::new(declaration_start, declarations_end),
                    nodes: declarations.clone(),
                    has_trailing_comma: false,
                },
                facts: 0,
            })),
            &declarations,
        );
        let end = self.parse_semicolon(declarations_end);
        self.alloc_node(
            SyntaxKind::VariableStatement,
            TextRange::new(keyword.range.start, end),
            NodeData::VariableStatement(Box::new(VariableStatementData {
                declaration_list,
                flow_node: None,
                facts: 0,
                modifiers: None,
            })),
            &[declaration_list],
        )
    }

    fn parse_variable_declaration(&mut self) -> NodeId {
        let start = self.current.range.start;
        let name = self.parse_identifier("Expected a variable name.");
        let type_node = if self.current.kind == SyntaxKind::ColonToken {
            self.bump();
            Some(self.parse_type())
        } else {
            None
        };
        let initializer = if self.current.kind == SyntaxKind::EqualsToken {
            self.bump();
            Some(self.parse_binary_expression(2))
        } else {
            None
        };
        let end = initializer
            .or(type_node)
            .and_then(|id| self.arena.get(id))
            .map_or_else(|| self.node_end(name), |node| node.range.end);
        let mut children = vec![name];
        children.extend(type_node);
        children.extend(initializer);
        self.alloc_node(
            SyntaxKind::VariableDeclaration,
            TextRange::new(start, end),
            NodeData::VariableDeclaration(Box::new(VariableDeclarationData {
                exclamation_token: None,
                initializer,
                local_symbol: None,
                symbol: None,
                type_: type_node,
                facts: 0,
                name,
            })),
            &children,
        )
    }

    fn parse_expression_statement(&mut self) -> NodeId {
        let start = self.current.range.start;
        let expression = self.parse_binary_expression(0);
        let expression_end = self.node_end(expression);
        let end = self.parse_semicolon(expression_end);
        self.alloc_node(
            SyntaxKind::ExpressionStatement,
            TextRange::new(start, end),
            NodeData::ExpressionStatement(Box::new(ExpressionStatementData {
                expression,
                flow_node: None,
            })),
            &[expression],
        )
    }

    fn parse_binary_expression(&mut self, minimum_precedence: u8) -> NodeId {
        let mut left = self.parse_primary_expression();
        loop {
            if self.current.kind == SyntaxKind::GreaterThanToken {
                self.current = self.scanner.rescan_greater_than_token();
            }
            let Some((precedence, right_associative)) = binary_precedence(self.current.kind) else {
                break;
            };
            if precedence < minimum_precedence {
                break;
            }
            let operator = self.consume();
            let operator_node = self.alloc_node(
                operator.kind,
                operator.range,
                NodeData::Token(Box::new(TokenData)),
                &[],
            );
            let right = self.parse_binary_expression(if right_associative {
                precedence
            } else {
                precedence + 1
            });
            let range = TextRange::new(self.node_start(left), self.node_end(right));
            left = self.alloc_node(
                SyntaxKind::BinaryExpression,
                range,
                NodeData::BinaryExpression(Box::new(BinaryExpressionData {
                    left,
                    operator_token: operator_node,
                    right,
                    symbol: None,
                    type_: None,
                    facts: 0,
                    modifiers: None,
                })),
                &[left, operator_node, right],
            );
        }
        left
    }

    fn parse_primary_expression(&mut self) -> NodeId {
        match self.current.kind {
            SyntaxKind::Identifier => self.parse_identifier("Expected an expression."),
            SyntaxKind::NumericLiteral => self.parse_numeric_literal(),
            SyntaxKind::BigIntLiteral => self.parse_bigint_literal(),
            SyntaxKind::StringLiteral => self.parse_string_literal(),
            SyntaxKind::NoSubstitutionTemplateLiteral => self.parse_template_literal(),
            SyntaxKind::NullKeyword | SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword => {
                self.parse_keyword_expression()
            }
            SyntaxKind::OpenParenToken => self.parse_parenthesized_expression(),
            _ => {
                let position = self.current.range.start;
                self.error_current("Expected an expression.");
                if !is_expression_terminator(self.current.kind) {
                    self.bump();
                }
                self.missing_identifier(position)
            }
        }
    }

    fn parse_parenthesized_expression(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let expression = self.parse_binary_expression(0);
        let end = if self.current.kind == SyntaxKind::CloseParenToken {
            self.consume().range.end
        } else {
            self.error_current("Expected ')'.");
            self.node_end(expression)
        };
        self.alloc_node(
            SyntaxKind::ParenthesizedExpression,
            TextRange::new(start, end),
            NodeData::ParenthesizedExpression(Box::new(ParenthesizedExpressionData { expression })),
            &[expression],
        )
    }

    fn parse_identifier(&mut self, message: &str) -> NodeId {
        if self.current.kind != SyntaxKind::Identifier {
            let position = self.current.range.start;
            self.error_current(message);
            return self.missing_identifier(position);
        }
        let token = self.consume();
        let text = token
            .value
            .as_ref()
            .map_or_else(|| token.text.to_owned(), ts_core::JsString::to_string_lossy);
        self.alloc_node(
            SyntaxKind::Identifier,
            token.range,
            NodeData::Identifier(Box::new(IdentifierData {
                flow_node: None,
                text,
            })),
            &[],
        )
    }

    fn missing_identifier(&mut self, position: TextPos) -> NodeId {
        self.alloc_node_with_flags(
            SyntaxKind::Identifier,
            NODE_FLAG_HAS_ERROR,
            TextRange::new(position, position),
            NodeData::Identifier(Box::new(IdentifierData {
                flow_node: None,
                text: String::new(),
            })),
            &[],
        )
    }

    fn parse_numeric_literal(&mut self) -> NodeId {
        let token = self.consume();
        self.alloc_node(
            SyntaxKind::NumericLiteral,
            token.range,
            NodeData::NumericLiteral(Box::new(NumericLiteralData {
                text: token.text.to_owned(),
                token_flags: TokenFlags::default(),
            })),
            &[],
        )
    }

    fn parse_bigint_literal(&mut self) -> NodeId {
        let token = self.consume();
        self.alloc_node(
            SyntaxKind::BigIntLiteral,
            token.range,
            NodeData::BigIntLiteral(Box::new(BigIntLiteralData {
                text: token.text.to_owned(),
                token_flags: TokenFlags::default(),
            })),
            &[],
        )
    }

    fn parse_string_literal(&mut self) -> NodeId {
        let token = self.consume();
        let text = token
            .value
            .as_ref()
            .map_or_else(|| token.text.to_owned(), ts_core::JsString::to_string_lossy);
        self.alloc_node(
            SyntaxKind::StringLiteral,
            token.range,
            NodeData::StringLiteral(Box::new(StringLiteralData {
                text,
                token_flags: TokenFlags::default(),
            })),
            &[],
        )
    }

    fn parse_template_literal(&mut self) -> NodeId {
        let token = self.consume();
        let text = token
            .value
            .as_ref()
            .map_or_else(|| token.text.to_owned(), ts_core::JsString::to_string_lossy);
        self.alloc_node(
            SyntaxKind::NoSubstitutionTemplateLiteral,
            token.range,
            NodeData::NoSubstitutionTemplateLiteral(Box::new(NoSubstitutionTemplateLiteralData {
                raw_text: token.text.to_owned(),
                symbol: None,
                template_flags: TokenFlags::default(),
                text,
                token_flags: TokenFlags::default(),
            })),
            &[],
        )
    }

    fn parse_keyword_expression(&mut self) -> NodeId {
        let token = self.consume();
        self.alloc_node(
            token.kind,
            token.range,
            NodeData::KeywordExpression(Box::new(KeywordExpressionData { flow_node: None })),
            &[],
        )
    }

    fn parse_type(&mut self) -> NodeId {
        if is_keyword_type(self.current.kind) {
            let token = self.consume();
            return self.alloc_node(
                token.kind,
                token.range,
                NodeData::KeywordTypeNode(Box::new(KeywordTypeNodeData)),
                &[],
            );
        }

        let start = self.current.range.start;
        let mut type_name = self.parse_identifier("Expected a type name.");
        while self.current.kind == SyntaxKind::DotToken {
            self.bump();
            let right = self.parse_identifier("Expected an identifier after '.'.");
            type_name = self.alloc_node(
                SyntaxKind::QualifiedName,
                TextRange::new(self.node_start(type_name), self.node_end(right)),
                NodeData::QualifiedName(Box::new(QualifiedNameData {
                    flow_node: None,
                    left: type_name,
                    right,
                    facts: 0,
                })),
                &[type_name, right],
            );
        }
        let type_arguments = self.parse_type_arguments();
        let end = type_arguments
            .as_ref()
            .map_or_else(|| self.node_end(type_name), |arguments| arguments.range.end);
        let mut children = vec![type_name];
        if let Some(arguments) = &type_arguments {
            children.extend(arguments.nodes.iter().copied());
        }
        self.alloc_node(
            SyntaxKind::TypeReference,
            TextRange::new(start, end),
            NodeData::TypeReferenceNode(Box::new(TypeReferenceNodeData {
                type_arguments,
                type_name,
            })),
            &children,
        )
    }

    fn parse_type_arguments(&mut self) -> Option<NodeList> {
        if self.current.kind != SyntaxKind::LessThanToken {
            return None;
        }
        let start = self.consume().range.start;
        let mut arguments = Vec::new();
        while self.current.kind != SyntaxKind::GreaterThanToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            arguments.push(self.parse_type());
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
        }
        let end = if self.current.kind == SyntaxKind::GreaterThanToken {
            self.consume().range.end
        } else {
            self.error_current("Expected '>'.");
            arguments
                .last()
                .map_or(self.current.range.start, |id| self.node_end(*id))
        };
        Some(NodeList {
            range: TextRange::new(start, end),
            nodes: arguments,
            has_trailing_comma: false,
        })
    }

    fn parse_semicolon(&mut self, fallback_end: TextPos) -> TextPos {
        if self.current.kind == SyntaxKind::SemicolonToken {
            return self.consume().range.end;
        }
        if self.current.kind == SyntaxKind::CloseBraceToken
            || self.current.kind == SyntaxKind::EndOfFile
            || self
                .current
                .flags
                .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
        {
            return fallback_end;
        }
        self.error_current("Expected ';'.");
        fallback_end
    }

    fn alloc_node(
        &mut self,
        kind: SyntaxKind,
        range: TextRange,
        data: NodeData,
        children: &[NodeId],
    ) -> NodeId {
        self.alloc_node_with_flags(kind, NodeFlags::default(), range, data, children)
    }

    fn alloc_node_with_flags(
        &mut self,
        kind: SyntaxKind,
        flags: NodeFlags,
        range: TextRange,
        data: NodeData,
        children: &[NodeId],
    ) -> NodeId {
        let id = self.arena.alloc(Node {
            kind,
            flags,
            range,
            parent: None,
            data,
        });
        for &child in children {
            if let Some(node) = self.arena.get_mut(child) {
                node.parent = Some(id);
            }
        }
        id
    }

    fn node_start(&self, id: NodeId) -> TextPos {
        self.arena.get(id).unwrap().range.start
    }

    fn node_end(&self, id: NodeId) -> TextPos {
        self.arena.get(id).unwrap().range.end
    }

    fn error_current(&mut self, message: &str) {
        self.diagnostics
            .push(Diagnostic::new(self.current.range, message));
    }

    fn bump(&mut self) {
        self.current = self.scanner.scan();
    }

    fn consume(&mut self) -> Token<'a> {
        let next = self.scanner.scan();
        std::mem::replace(&mut self.current, next)
    }
}

fn is_expression_terminator(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::SemicolonToken
            | SyntaxKind::CommaToken
            | SyntaxKind::CloseParenToken
            | SyntaxKind::CloseBraceToken
            | SyntaxKind::EndOfFile
    )
}

fn is_keyword_type(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::AnyKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::IntrinsicKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::VoidKeyword
    )
}

fn binary_precedence(kind: SyntaxKind) -> Option<(u8, bool)> {
    let (precedence, right_associative) = match kind {
        SyntaxKind::CommaToken => (1, false),
        SyntaxKind::EqualsToken
        | SyntaxKind::PlusEqualsToken
        | SyntaxKind::MinusEqualsToken
        | SyntaxKind::AsteriskEqualsToken
        | SyntaxKind::AsteriskAsteriskEqualsToken
        | SyntaxKind::SlashEqualsToken
        | SyntaxKind::PercentEqualsToken
        | SyntaxKind::LessThanLessThanEqualsToken
        | SyntaxKind::GreaterThanGreaterThanEqualsToken
        | SyntaxKind::GreaterThanGreaterThanGreaterThanEqualsToken
        | SyntaxKind::AmpersandEqualsToken
        | SyntaxKind::BarEqualsToken
        | SyntaxKind::CaretEqualsToken
        | SyntaxKind::BarBarEqualsToken
        | SyntaxKind::AmpersandAmpersandEqualsToken
        | SyntaxKind::QuestionQuestionEqualsToken => (2, true),
        SyntaxKind::QuestionQuestionToken => (3, false),
        SyntaxKind::BarBarToken => (4, false),
        SyntaxKind::AmpersandAmpersandToken => (5, false),
        SyntaxKind::BarToken => (6, false),
        SyntaxKind::CaretToken => (7, false),
        SyntaxKind::AmpersandToken => (8, false),
        SyntaxKind::EqualsEqualsToken
        | SyntaxKind::ExclamationEqualsToken
        | SyntaxKind::EqualsEqualsEqualsToken
        | SyntaxKind::ExclamationEqualsEqualsToken => (9, false),
        SyntaxKind::LessThanToken
        | SyntaxKind::LessThanEqualsToken
        | SyntaxKind::GreaterThanToken
        | SyntaxKind::GreaterThanEqualsToken
        | SyntaxKind::InKeyword
        | SyntaxKind::InstanceOfKeyword => (10, false),
        SyntaxKind::LessThanLessThanToken
        | SyntaxKind::GreaterThanGreaterThanToken
        | SyntaxKind::GreaterThanGreaterThanGreaterThanToken => (11, false),
        SyntaxKind::PlusToken | SyntaxKind::MinusToken => (12, false),
        SyntaxKind::AsteriskToken | SyntaxKind::SlashToken | SyntaxKind::PercentToken => {
            (13, false)
        }
        SyntaxKind::AsteriskAsteriskToken => (14, true),
        _ => return None,
    };
    Some((precedence, right_associative))
}

#[cfg(test)]
mod tests {
    use ts_ast::{NodeData, NodeFlags, NodeId, SyntaxKind};

    use super::{ParseResult, parse_source_file};

    #[test]
    fn parses_variable_types_and_binary_precedence() {
        let source = "let value: ns.Item = 1 + 2 * 3; const other: string = (value + 4);";
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        let source_node = result.arena.get(result.source_file).unwrap();
        assert_eq!(source_node.range.start.get(), 0);
        assert_eq!(
            source_node.range.end.get(),
            u32::try_from(source.len()).unwrap()
        );
        let (first_list, first_statement) = variable_list(&result, statements[0]);
        assert_eq!(result.arena.get(first_list).unwrap().flags, NodeFlags(1));
        assert_eq!(
            result.arena.get(first_list).unwrap().parent,
            Some(statements[0])
        );
        let first_declaration = declaration_nodes(&result, first_list)[0];
        let (type_node, initializer) = declaration_type_and_initializer(&result, first_declaration);
        assert_eq!(
            result.arena.get(type_node).unwrap().kind,
            SyntaxKind::TypeReference
        );
        assert_eq!(
            result.arena.get(type_node).unwrap().parent,
            Some(first_declaration)
        );
        let NodeData::BinaryExpression(addition) = &result.arena.get(initializer).unwrap().data
        else {
            panic!("expected addition");
        };
        assert_eq!(
            result.arena.get(addition.operator_token).unwrap().kind,
            SyntaxKind::PlusToken
        );
        let NodeData::BinaryExpression(multiplication) =
            &result.arena.get(addition.right).unwrap().data
        else {
            panic!("expected multiplication on the right");
        };
        assert_eq!(
            result
                .arena
                .get(multiplication.operator_token)
                .unwrap()
                .kind,
            SyntaxKind::AsteriskToken
        );
        assert_eq!(
            result.arena.get(addition.left).unwrap().parent,
            Some(initializer)
        );
        let initializer_range = result.arena.get(initializer).unwrap().range;
        assert_eq!(
            &source[initializer_range.start.get() as usize..initializer_range.end.get() as usize],
            "1 + 2 * 3"
        );

        let (second_list, _) = variable_list(&result, statements[1]);
        assert_eq!(result.arena.get(second_list).unwrap().flags, NodeFlags(2));
        let second_declaration = declaration_nodes(&result, second_list)[0];
        let (type_node, initializer) =
            declaration_type_and_initializer(&result, second_declaration);
        assert_eq!(
            result.arena.get(type_node).unwrap().kind,
            SyntaxKind::StringKeyword
        );
        assert_eq!(
            result.arena.get(initializer).unwrap().kind,
            SyntaxKind::ParenthesizedExpression
        );
        assert_eq!(first_statement, statements[0]);
    }

    #[test]
    fn parses_blocks_and_comma_separated_declarations() {
        let result = parse_source_file("{ var a = 1, b = 2; a + b; }");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1);
        let block = result.arena.get(statements[0]).unwrap();
        let NodeData::Block(block_data) = &block.data else {
            panic!("expected block");
        };
        assert_eq!(block_data.statements.nodes.len(), 2);
        let (list, _) = variable_list(&result, block_data.statements.nodes[0]);
        assert_eq!(declaration_nodes(&result, list).len(), 2);
        for child in &block_data.statements.nodes {
            assert_eq!(
                result.arena.get(*child).unwrap().parent,
                Some(statements[0])
            );
        }
    }

    #[test]
    fn rescans_shift_operators_and_parses_nested_type_arguments() {
        let result = parse_source_file("let item: Box<Box<string>>; item >> 1 + 2;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let NodeData::ExpressionStatement(expression_statement) =
            &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected expression statement");
        };
        let NodeData::BinaryExpression(shift) = &result
            .arena
            .get(expression_statement.expression)
            .unwrap()
            .data
        else {
            panic!("expected shift expression");
        };
        assert_eq!(
            result.arena.get(shift.operator_token).unwrap().kind,
            SyntaxKind::GreaterThanGreaterThanToken
        );
        assert_eq!(
            result.arena.get(shift.right).unwrap().kind,
            SyntaxKind::BinaryExpression
        );
    }

    #[test]
    fn recovers_with_missing_names_expressions_and_braces() {
        let result = parse_source_file("let : Missing = ;\n{ const y = 1 + ;");
        assert!(result.diagnostics.len() >= 3, "{:?}", result.diagnostics);
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("variable name"))
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("expression"))
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("Expected '}'"))
        );
        let missing_name = result
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.message.contains("variable name"))
            .unwrap();
        assert_eq!(missing_name.range.start.get(), 4);
        assert_eq!(source_statements(&result).len(), 2);
    }

    fn source_statements(result: &ParseResult) -> &[NodeId] {
        let source = result.arena.get(result.source_file).unwrap();
        let NodeData::SourceFile(data) = &source.data else {
            panic!("expected source file");
        };
        &data.statements.nodes
    }

    fn variable_list(result: &ParseResult, statement: NodeId) -> (NodeId, NodeId) {
        let node = result.arena.get(statement).unwrap();
        let NodeData::VariableStatement(data) = &node.data else {
            panic!("expected variable statement");
        };
        (data.declaration_list, statement)
    }

    fn declaration_nodes(result: &ParseResult, list: NodeId) -> &[NodeId] {
        let node = result.arena.get(list).unwrap();
        let NodeData::VariableDeclarationList(data) = &node.data else {
            panic!("expected variable declaration list");
        };
        &data.declarations.nodes
    }

    fn declaration_type_and_initializer(
        result: &ParseResult,
        declaration: NodeId,
    ) -> (NodeId, NodeId) {
        let node = result.arena.get(declaration).unwrap();
        let NodeData::VariableDeclaration(data) = &node.data else {
            panic!("expected variable declaration");
        };
        (data.type_.unwrap(), data.initializer.unwrap())
    }
}
