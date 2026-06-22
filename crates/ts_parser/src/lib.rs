//! TypeScript parser.

use ts_ast::{
    ArrayLiteralExpressionData, ArrowFunctionData, BigIntLiteralData, BinaryExpressionData,
    BlockData, CallExpressionData, ClassDeclarationData, EmptyStatementData, EnumDeclarationData,
    EnumMemberData, ExportAssignmentData, ExportDeclarationData, ExportSpecifierData,
    ExpressionStatementData, ExpressionWithTypeArgumentsData, ForStatementData,
    FunctionDeclarationData, HeritageClauseData, IdentifierData, IfStatementData, ImportClauseData,
    ImportDeclarationData, ImportSpecifierData, InterfaceDeclarationData, KeywordExpressionData,
    KeywordTypeNodeData, MethodDeclarationData, NamedExportsData, NamedImportsData,
    NoSubstitutionTemplateLiteralData, Node, NodeArena, NodeData, NodeFlags, NodeId, NodeList,
    NumericLiteralData, ObjectLiteralExpressionData, ParameterDeclarationData,
    ParenthesizedExpressionData, PropertyAccessExpressionData, PropertyAssignmentData,
    PropertyDeclarationData, QualifiedNameData, ReturnStatementData, SourceFileData,
    StringLiteralData, SymbolTable, SyntaxKind, TemplateExpressionData, TemplateHeadData,
    TemplateMiddleData, TemplateSpanData, TemplateTailData, TokenData, TokenFlags,
    TypeAliasDeclarationData, TypeParameterDeclarationData, TypeReferenceNodeData,
    VariableDeclarationData, VariableDeclarationListData, VariableStatementData,
    WhileStatementData,
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
            SyntaxKind::FunctionKeyword => self.parse_function_declaration(),
            SyntaxKind::ClassKeyword => self.parse_class_declaration(),
            SyntaxKind::InterfaceKeyword => self.parse_interface_declaration(),
            SyntaxKind::TypeKeyword => self.parse_type_alias_declaration(),
            SyntaxKind::EnumKeyword => self.parse_enum_declaration(),
            SyntaxKind::ReturnKeyword => self.parse_return_statement(),
            SyntaxKind::IfKeyword => self.parse_if_statement(),
            SyntaxKind::WhileKeyword => self.parse_while_statement(),
            SyntaxKind::ForKeyword => self.parse_for_statement(),
            SyntaxKind::ImportKeyword => self.parse_import_declaration(),
            SyntaxKind::ExportKeyword => self.parse_export_declaration(),
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

    fn parse_function_declaration(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let name = if self.current.kind == SyntaxKind::Identifier {
            Some(self.parse_identifier("Expected a function name."))
        } else {
            self.error_current("Expected a function name.");
            None
        };
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameter_list();
        let return_type = self.parse_optional_type_annotation();
        let body = if self.current.kind == SyntaxKind::OpenBraceToken {
            Some(self.parse_block())
        } else {
            self.parse_semicolon(self.current.range.start);
            None
        };
        let end = body
            .or(return_type)
            .and_then(|id| self.arena.get(id))
            .map_or(parameters.range.end, |node| node.range.end);
        let mut children = Vec::new();
        children.extend(name);
        extend_list_children(&mut children, type_parameters.as_ref());
        children.extend(parameters.nodes.iter().copied());
        children.extend(return_type);
        children.extend(body);
        self.alloc_node(
            SyntaxKind::FunctionDeclaration,
            TextRange::new(start, end),
            NodeData::FunctionDeclaration(Box::new(FunctionDeclarationData {
                asterisk_token: None,
                body,
                end_flow_node: None,
                flow_node: None,
                full_signature: None,
                local_symbol: None,
                locals: SymbolTable,
                next_container: None,
                parameters,
                return_flow_node: None,
                symbol: None,
                type_: return_type,
                type_parameters,
                facts: 0,
                modifiers: None,
                name,
            })),
            &children,
        )
    }

    fn parse_parameter_list(&mut self) -> NodeList {
        let start = self.current.range.start;
        if self.current.kind != SyntaxKind::OpenParenToken {
            self.error_current("Expected '('.");
            return NodeList {
                range: TextRange::new(start, start),
                nodes: Vec::new(),
                has_trailing_comma: false,
            };
        }
        self.bump();
        let mut parameters = Vec::new();
        let mut trailing = false;
        while self.current.kind != SyntaxKind::CloseParenToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            parameters.push(self.parse_parameter());
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
            trailing = self.current.kind == SyntaxKind::CloseParenToken;
        }
        let end = if self.current.kind == SyntaxKind::CloseParenToken {
            self.consume().range.end
        } else {
            self.error_current("Expected ')'.");
            parameters
                .last()
                .map_or(start, |parameter| self.node_end(*parameter))
        };
        NodeList {
            range: TextRange::new(start, end),
            nodes: parameters,
            has_trailing_comma: trailing,
        }
    }

    fn parse_parameter(&mut self) -> NodeId {
        let start = self.current.range.start;
        let dot_dot_dot_token = if self.current.kind == SyntaxKind::DotDotDotToken {
            Some(self.consume_token_node())
        } else {
            None
        };
        let name = self.parse_identifier("Expected a parameter name.");
        let question_token = if self.current.kind == SyntaxKind::QuestionToken {
            Some(self.consume_token_node())
        } else {
            None
        };
        let type_node = self.parse_optional_type_annotation();
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
        children.extend(dot_dot_dot_token);
        children.extend(question_token);
        children.extend(type_node);
        children.extend(initializer);
        self.alloc_node(
            SyntaxKind::Parameter,
            TextRange::new(start, end),
            NodeData::ParameterDeclaration(Box::new(ParameterDeclarationData {
                dot_dot_dot_token,
                initializer,
                question_token,
                symbol: None,
                type_: type_node,
                facts: 0,
                modifiers: None,
                name,
            })),
            &children,
        )
    }

    fn parse_type_parameters(&mut self) -> Option<NodeList> {
        if self.current.kind != SyntaxKind::LessThanToken {
            return None;
        }
        let start = self.consume().range.start;
        let mut parameters = Vec::new();
        while self.current.kind != SyntaxKind::GreaterThanToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            let parameter_start = self.current.range.start;
            let name = self.parse_identifier("Expected a type parameter name.");
            let constraint = if self.current.kind == SyntaxKind::ExtendsKeyword {
                self.bump();
                Some(self.parse_type())
            } else {
                None
            };
            let default_type = if self.current.kind == SyntaxKind::EqualsToken {
                self.bump();
                Some(self.parse_type())
            } else {
                None
            };
            let end = default_type
                .or(constraint)
                .map_or_else(|| self.node_end(name), |id| self.node_end(id));
            let mut children = vec![name];
            children.extend(constraint);
            children.extend(default_type);
            parameters.push(self.alloc_node(
                SyntaxKind::TypeParameter,
                TextRange::new(parameter_start, end),
                NodeData::TypeParameterDeclaration(Box::new(TypeParameterDeclarationData {
                    constraint,
                    default_type,
                    expression: None,
                    symbol: None,
                    modifiers: None,
                    name,
                })),
                &children,
            ));
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
        }
        let end = if self.current.kind == SyntaxKind::GreaterThanToken {
            self.consume().range.end
        } else {
            self.error_current("Expected '>'.");
            parameters.last().map_or(start, |id| self.node_end(*id))
        };
        Some(NodeList {
            range: TextRange::new(start, end),
            nodes: parameters,
            has_trailing_comma: false,
        })
    }

    fn parse_optional_type_annotation(&mut self) -> Option<NodeId> {
        if self.current.kind == SyntaxKind::ColonToken {
            self.bump();
            Some(self.parse_type())
        } else {
            None
        }
    }

    fn parse_class_declaration(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let name = if self.current.kind == SyntaxKind::Identifier {
            Some(self.parse_identifier("Expected a class name."))
        } else {
            self.error_current("Expected a class name.");
            None
        };
        let type_parameters = self.parse_type_parameters();
        let heritage_clauses = self.parse_heritage_clauses();
        let members = self.parse_class_members(false);
        let end = members.range.end;
        let mut children = Vec::new();
        children.extend(name);
        extend_list_children(&mut children, type_parameters.as_ref());
        extend_list_children(&mut children, heritage_clauses.as_ref());
        children.extend(members.nodes.iter().copied());
        self.alloc_node(
            SyntaxKind::ClassDeclaration,
            TextRange::new(start, end),
            NodeData::ClassDeclaration(Box::new(ClassDeclarationData {
                flow_node: None,
                heritage_clauses,
                local_symbol: None,
                locals: SymbolTable,
                members,
                next_container: None,
                symbol: None,
                type_parameters,
                facts: 0,
                modifiers: None,
                name,
            })),
            &children,
        )
    }

    fn parse_interface_declaration(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let name = self.parse_identifier("Expected an interface name.");
        let type_parameters = self.parse_type_parameters();
        let heritage_clauses = self.parse_heritage_clauses();
        let members = self.parse_class_members(true);
        let end = members.range.end;
        let mut children = vec![name];
        extend_list_children(&mut children, type_parameters.as_ref());
        extend_list_children(&mut children, heritage_clauses.as_ref());
        children.extend(members.nodes.iter().copied());
        self.alloc_node(
            SyntaxKind::InterfaceDeclaration,
            TextRange::new(start, end),
            NodeData::InterfaceDeclaration(Box::new(InterfaceDeclarationData {
                flow_node: None,
                heritage_clauses,
                local_symbol: None,
                members,
                symbol: None,
                type_parameters,
                modifiers: None,
                name,
            })),
            &children,
        )
    }

    fn parse_heritage_clauses(&mut self) -> Option<NodeList> {
        if !matches!(
            self.current.kind,
            SyntaxKind::ExtendsKeyword | SyntaxKind::ImplementsKeyword
        ) {
            return None;
        }
        let start = self.current.range.start;
        let mut clauses = Vec::new();
        while matches!(
            self.current.kind,
            SyntaxKind::ExtendsKeyword | SyntaxKind::ImplementsKeyword
        ) {
            let keyword = self.consume();
            let mut types = Vec::new();
            loop {
                let expression = self.parse_identifier("Expected a base type.");
                let type_arguments = self.parse_type_arguments();
                let end = type_arguments
                    .as_ref()
                    .map_or_else(|| self.node_end(expression), |list| list.range.end);
                let mut expression_children = vec![expression];
                extend_list_children(&mut expression_children, type_arguments.as_ref());
                types.push(self.alloc_node(
                    SyntaxKind::ExpressionWithTypeArguments,
                    TextRange::new(self.node_start(expression), end),
                    NodeData::ExpressionWithTypeArguments(Box::new(
                        ExpressionWithTypeArgumentsData {
                            expression,
                            type_arguments,
                            facts: 0,
                        },
                    )),
                    &expression_children,
                ));
                if self.current.kind != SyntaxKind::CommaToken {
                    break;
                }
                self.bump();
            }
            let end = types
                .last()
                .map_or(keyword.range.end, |id| self.node_end(*id));
            clauses.push(self.alloc_node(
                SyntaxKind::HeritageClause,
                TextRange::new(keyword.range.start, end),
                NodeData::HeritageClause(Box::new(HeritageClauseData {
                    token: keyword.kind,
                    types: NodeList {
                        range: TextRange::new(keyword.range.end, end),
                        nodes: types.clone(),
                        has_trailing_comma: false,
                    },
                    facts: 0,
                })),
                &types,
            ));
        }
        let end = clauses.last().map_or(start, |id| self.node_end(*id));
        Some(NodeList {
            range: TextRange::new(start, end),
            nodes: clauses,
            has_trailing_comma: false,
        })
    }

    fn parse_class_members(&mut self, signature_only: bool) -> NodeList {
        let start = self.current.range.start;
        if self.current.kind != SyntaxKind::OpenBraceToken {
            self.error_current("Expected '{'.");
            return NodeList {
                range: TextRange::new(start, start),
                nodes: Vec::new(),
                has_trailing_comma: false,
            };
        }
        self.bump();
        let mut members = Vec::new();
        while self.current.kind != SyntaxKind::CloseBraceToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            if self.current.kind == SyntaxKind::SemicolonToken {
                self.bump();
                continue;
            }
            members.push(self.parse_class_member(signature_only));
        }
        let end = if self.current.kind == SyntaxKind::CloseBraceToken {
            self.consume().range.end
        } else {
            self.error_current("Expected '}'.");
            self.current.range.start
        };
        NodeList {
            range: TextRange::new(start, end),
            nodes: members,
            has_trailing_comma: false,
        }
    }

    fn parse_class_member(&mut self, signature_only: bool) -> NodeId {
        let start = self.current.range.start;
        let name = self.parse_identifier("Expected a member name.");
        if self.current.kind == SyntaxKind::OpenParenToken {
            let parameters = self.parse_parameter_list();
            let return_type = self.parse_optional_type_annotation();
            let body = if !signature_only && self.current.kind == SyntaxKind::OpenBraceToken {
                Some(self.parse_block())
            } else {
                self.parse_semicolon(parameters.range.end);
                None
            };
            let end = body
                .or(return_type)
                .map_or(parameters.range.end, |id| self.node_end(id));
            let mut children = vec![name];
            children.extend(parameters.nodes.iter().copied());
            children.extend(return_type);
            children.extend(body);
            self.alloc_node(
                SyntaxKind::MethodDeclaration,
                TextRange::new(start, end),
                NodeData::MethodDeclaration(Box::new(MethodDeclarationData {
                    asterisk_token: None,
                    body,
                    end_flow_node: None,
                    flow_node: None,
                    full_signature: None,
                    locals: SymbolTable,
                    next_container: None,
                    parameters,
                    postfix_token: None,
                    symbol: None,
                    type_: return_type,
                    type_parameters: None,
                    facts: 0,
                    modifiers: None,
                    name,
                })),
                &children,
            )
        } else {
            let type_node = self.parse_optional_type_annotation();
            let initializer = if !signature_only && self.current.kind == SyntaxKind::EqualsToken {
                self.bump();
                Some(self.parse_binary_expression(2))
            } else {
                None
            };
            let fallback = type_node.map_or_else(|| self.node_end(name), |id| self.node_end(id));
            let end = self.parse_semicolon(initializer.map_or(fallback, |id| self.node_end(id)));
            let mut children = vec![name];
            children.extend(type_node);
            children.extend(initializer);
            self.alloc_node(
                SyntaxKind::PropertyDeclaration,
                TextRange::new(start, end),
                NodeData::PropertyDeclaration(Box::new(PropertyDeclarationData {
                    initializer,
                    postfix_token: None,
                    symbol: None,
                    type_: type_node,
                    facts: 0,
                    modifiers: None,
                    name,
                })),
                &children,
            )
        }
    }

    fn parse_type_alias_declaration(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let name = self.parse_identifier("Expected a type alias name.");
        let type_parameters = self.parse_type_parameters();
        if self.current.kind == SyntaxKind::EqualsToken {
            self.bump();
        } else {
            self.error_current("Expected '='.");
        }
        let type_node = self.parse_type();
        let end = self.parse_semicolon(self.node_end(type_node));
        let mut children = vec![name, type_node];
        extend_list_children(&mut children, type_parameters.as_ref());
        self.alloc_node(
            SyntaxKind::TypeAliasDeclaration,
            TextRange::new(start, end),
            NodeData::TypeAliasDeclaration(Box::new(TypeAliasDeclarationData {
                flow_node: None,
                local_symbol: None,
                locals: SymbolTable,
                next_container: None,
                symbol: None,
                type_: type_node,
                type_parameters,
                modifiers: None,
                name,
            })),
            &children,
        )
    }

    fn parse_enum_declaration(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let name = self.parse_identifier("Expected an enum name.");
        let body_start = self.current.range.start;
        if self.current.kind == SyntaxKind::OpenBraceToken {
            self.bump();
        } else {
            self.error_current("Expected '{'.");
        }
        let mut members = Vec::new();
        while self.current.kind != SyntaxKind::CloseBraceToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            let entry_start = self.current.range.start;
            let member_name = self.parse_identifier("Expected an enum member name.");
            let initializer = if self.current.kind == SyntaxKind::EqualsToken {
                self.bump();
                Some(self.parse_binary_expression(2))
            } else {
                None
            };
            let end =
                initializer.map_or_else(|| self.node_end(member_name), |id| self.node_end(id));
            let mut children = vec![member_name];
            children.extend(initializer);
            members.push(self.alloc_node(
                SyntaxKind::EnumMember,
                TextRange::new(entry_start, end),
                NodeData::EnumMember(Box::new(EnumMemberData {
                    initializer,
                    postfix_token: None,
                    symbol: None,
                    facts: 0,
                    modifiers: None,
                    name: member_name,
                })),
                &children,
            ));
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
        }
        let end = if self.current.kind == SyntaxKind::CloseBraceToken {
            self.consume().range.end
        } else {
            self.error_current("Expected '}'.");
            members.last().map_or(body_start, |id| self.node_end(*id))
        };
        let mut children = vec![name];
        children.extend(members.iter().copied());
        self.alloc_node(
            SyntaxKind::EnumDeclaration,
            TextRange::new(start, end),
            NodeData::EnumDeclaration(Box::new(EnumDeclarationData {
                flow_node: None,
                local_symbol: None,
                members: NodeList {
                    range: TextRange::new(body_start, end),
                    nodes: members,
                    has_trailing_comma: false,
                },
                symbol: None,
                facts: 0,
                modifiers: None,
                name,
            })),
            &children,
        )
    }

    fn parse_return_statement(&mut self) -> NodeId {
        let keyword = self.consume();
        let expression = if self.current.kind == SyntaxKind::SemicolonToken
            || self.current.kind == SyntaxKind::CloseBraceToken
            || self.current.kind == SyntaxKind::EndOfFile
            || self
                .current
                .flags
                .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
        {
            None
        } else {
            Some(self.parse_binary_expression(0))
        };
        let expression_end = expression.map_or(keyword.range.end, |id| self.node_end(id));
        let end = self.parse_semicolon(expression_end);
        let children: Vec<_> = expression.into_iter().collect();
        self.alloc_node(
            SyntaxKind::ReturnStatement,
            TextRange::new(keyword.range.start, end),
            NodeData::ReturnStatement(Box::new(ReturnStatementData {
                expression,
                flow_node: None,
                facts: 0,
            })),
            &children,
        )
    }

    fn parse_if_statement(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let expression = self.parse_parenthesized_condition();
        let then_statement = self.parse_statement();
        let else_statement = if self.current.kind == SyntaxKind::ElseKeyword {
            self.bump();
            Some(self.parse_statement())
        } else {
            None
        };
        let end =
            else_statement.map_or_else(|| self.node_end(then_statement), |id| self.node_end(id));
        let mut children = vec![expression, then_statement];
        children.extend(else_statement);
        self.alloc_node(
            SyntaxKind::IfStatement,
            TextRange::new(start, end),
            NodeData::IfStatement(Box::new(IfStatementData {
                else_statement,
                expression,
                flow_node: None,
                then_statement,
                facts: 0,
            })),
            &children,
        )
    }

    fn parse_while_statement(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let expression = self.parse_parenthesized_condition();
        let statement = self.parse_statement();
        let end = self.node_end(statement);
        self.alloc_node(
            SyntaxKind::WhileStatement,
            TextRange::new(start, end),
            NodeData::WhileStatement(Box::new(WhileStatementData {
                expression,
                flow_node: None,
                statement,
                facts: 0,
            })),
            &[expression, statement],
        )
    }

    fn parse_for_statement(&mut self) -> NodeId {
        let start = self.consume().range.start;
        self.expect_and_bump(SyntaxKind::OpenParenToken, "Expected '('.");
        let initializer = if self.current.kind == SyntaxKind::SemicolonToken {
            None
        } else if matches!(
            self.current.kind,
            SyntaxKind::VarKeyword | SyntaxKind::LetKeyword | SyntaxKind::ConstKeyword
        ) {
            let keyword = self.consume();
            let flags = match keyword.kind {
                SyntaxKind::LetKeyword => NODE_FLAG_LET,
                SyntaxKind::ConstKeyword => NODE_FLAG_CONST,
                _ => NodeFlags::default(),
            };
            let declaration = self.parse_variable_declaration();
            Some(self.alloc_node_with_flags(
                SyntaxKind::VariableDeclarationList,
                flags,
                TextRange::new(keyword.range.start, self.node_end(declaration)),
                NodeData::VariableDeclarationList(Box::new(VariableDeclarationListData {
                    declarations: NodeList {
                        range: self.arena.get(declaration).unwrap().range,
                        nodes: vec![declaration],
                        has_trailing_comma: false,
                    },
                    facts: 0,
                })),
                &[declaration],
            ))
        } else {
            Some(self.parse_binary_expression(0))
        };
        self.expect_and_bump(SyntaxKind::SemicolonToken, "Expected ';'.");
        let condition = if self.current.kind == SyntaxKind::SemicolonToken {
            None
        } else {
            Some(self.parse_binary_expression(0))
        };
        self.expect_and_bump(SyntaxKind::SemicolonToken, "Expected ';'.");
        let incrementor = if self.current.kind == SyntaxKind::CloseParenToken {
            None
        } else {
            Some(self.parse_binary_expression(0))
        };
        self.expect_and_bump(SyntaxKind::CloseParenToken, "Expected ')'.");
        let statement = self.parse_statement();
        let mut children = vec![statement];
        children.extend(initializer);
        children.extend(condition);
        children.extend(incrementor);
        self.alloc_node(
            SyntaxKind::ForStatement,
            TextRange::new(start, self.node_end(statement)),
            NodeData::ForStatement(Box::new(ForStatementData {
                condition,
                flow_node: None,
                incrementor,
                initializer,
                locals: SymbolTable,
                next_container: None,
                statement,
                facts: 0,
            })),
            &children,
        )
    }

    fn parse_parenthesized_condition(&mut self) -> NodeId {
        self.expect_and_bump(SyntaxKind::OpenParenToken, "Expected '('.");
        let expression = self.parse_binary_expression(0);
        self.expect_and_bump(SyntaxKind::CloseParenToken, "Expected ')'.");
        expression
    }

    fn parse_import_declaration(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let mut children = Vec::new();
        let import_clause = if self.current.kind == SyntaxKind::StringLiteral {
            None
        } else {
            let clause_start = self.current.range.start;
            let name = if self.current.kind == SyntaxKind::Identifier {
                Some(self.parse_identifier("Expected an import binding."))
            } else {
                None
            };
            if name.is_some() && self.current.kind == SyntaxKind::CommaToken {
                self.bump();
            }
            let named_bindings = if self.current.kind == SyntaxKind::OpenBraceToken {
                Some(self.parse_named_imports())
            } else {
                None
            };
            let end = named_bindings
                .or(name)
                .map_or(clause_start, |id| self.node_end(id));
            let mut clause_children = Vec::new();
            clause_children.extend(name);
            clause_children.extend(named_bindings);
            Some(self.alloc_node(
                SyntaxKind::ImportClause,
                TextRange::new(clause_start, end),
                NodeData::ImportClause(Box::new(ImportClauseData {
                    local_symbol: None,
                    named_bindings,
                    phase_modifier: None,
                    symbol: None,
                    facts: 0,
                    name,
                })),
                &clause_children,
            ))
        };
        if import_clause.is_some() {
            self.expect_and_bump(SyntaxKind::FromKeyword, "Expected 'from'.");
        }
        let module_specifier = if self.current.kind == SyntaxKind::StringLiteral {
            self.parse_string_literal()
        } else {
            self.error_current("Expected a module specifier.");
            self.missing_identifier(self.current.range.start)
        };
        children.extend(import_clause);
        children.push(module_specifier);
        let end = self.parse_semicolon(self.node_end(module_specifier));
        self.alloc_node(
            SyntaxKind::ImportDeclaration,
            TextRange::new(start, end),
            NodeData::ImportDeclaration(Box::new(ImportDeclarationData {
                attributes: None,
                flow_node: None,
                import_clause,
                module_specifier,
                symbol: None,
                facts: 0,
                modifiers: None,
            })),
            &children,
        )
    }

    fn parse_named_imports(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let mut elements = Vec::new();
        while self.current.kind != SyntaxKind::CloseBraceToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            let specifier_start = self.current.range.start;
            let first = self.parse_identifier("Expected an import name.");
            let (property_name, name) = if self.current.kind == SyntaxKind::AsKeyword {
                self.bump();
                (
                    Some(first),
                    self.parse_identifier("Expected a local import name."),
                )
            } else {
                (None, first)
            };
            let mut specifier_children = vec![name];
            specifier_children.extend(property_name);
            elements.push(self.alloc_node(
                SyntaxKind::ImportSpecifier,
                TextRange::new(specifier_start, self.node_end(name)),
                NodeData::ImportSpecifier(Box::new(ImportSpecifierData {
                    is_type_only: false,
                    local_symbol: None,
                    property_name,
                    symbol: None,
                    facts: 0,
                    name,
                })),
                &specifier_children,
            ));
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
        }
        let end = if self.current.kind == SyntaxKind::CloseBraceToken {
            self.consume().range.end
        } else {
            self.error_current("Expected '}'.");
            elements.last().map_or(start, |id| self.node_end(*id))
        };
        self.alloc_node(
            SyntaxKind::NamedImports,
            TextRange::new(start, end),
            NodeData::NamedImports(Box::new(NamedImportsData {
                elements: NodeList {
                    range: TextRange::new(start, end),
                    nodes: elements.clone(),
                    has_trailing_comma: false,
                },
                facts: 0,
            })),
            &elements,
        )
    }

    fn parse_export_declaration(&mut self) -> NodeId {
        let start = self.consume().range.start;
        if self.current.kind == SyntaxKind::DefaultKeyword {
            self.bump();
            let expression = self.parse_binary_expression(0);
            let end = self.parse_semicolon(self.node_end(expression));
            return self.alloc_node(
                SyntaxKind::ExportAssignment,
                TextRange::new(start, end),
                NodeData::ExportAssignment(Box::new(ExportAssignmentData {
                    expression,
                    flow_node: None,
                    is_export_equals: false,
                    symbol: None,
                    type_: expression,
                    facts: 0,
                    modifiers: None,
                })),
                &[expression],
            );
        }
        let export_clause = if self.current.kind == SyntaxKind::OpenBraceToken {
            Some(self.parse_named_exports())
        } else if self.current.kind == SyntaxKind::AsteriskToken {
            self.bump();
            None
        } else {
            self.error_current("Expected an export clause.");
            None
        };
        let module_specifier = if self.current.kind == SyntaxKind::FromKeyword {
            self.bump();
            if self.current.kind == SyntaxKind::StringLiteral {
                Some(self.parse_string_literal())
            } else {
                self.error_current("Expected a module specifier.");
                None
            }
        } else {
            None
        };
        let fallback = export_clause
            .or(module_specifier)
            .map_or(start, |id| self.node_end(id));
        let end = self.parse_semicolon(fallback);
        let mut children = Vec::new();
        children.extend(export_clause);
        children.extend(module_specifier);
        self.alloc_node(
            SyntaxKind::ExportDeclaration,
            TextRange::new(start, end),
            NodeData::ExportDeclaration(Box::new(ExportDeclarationData {
                attributes: None,
                export_clause,
                flow_node: None,
                is_type_only: false,
                module_specifier,
                symbol: None,
                facts: 0,
                modifiers: None,
            })),
            &children,
        )
    }

    fn parse_named_exports(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let mut elements = Vec::new();
        while self.current.kind != SyntaxKind::CloseBraceToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            let specifier_start = self.current.range.start;
            let first = self.parse_identifier("Expected an export name.");
            let (property_name, name) = if self.current.kind == SyntaxKind::AsKeyword {
                self.bump();
                (
                    Some(first),
                    self.parse_identifier("Expected an exported name."),
                )
            } else {
                (None, first)
            };
            let mut specifier_children = vec![name];
            specifier_children.extend(property_name);
            elements.push(self.alloc_node(
                SyntaxKind::ExportSpecifier,
                TextRange::new(specifier_start, self.node_end(name)),
                NodeData::ExportSpecifier(Box::new(ExportSpecifierData {
                    is_type_only: false,
                    local_symbol: None,
                    property_name,
                    symbol: None,
                    facts: 0,
                    name,
                })),
                &specifier_children,
            ));
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
        }
        let end = if self.current.kind == SyntaxKind::CloseBraceToken {
            self.consume().range.end
        } else {
            self.error_current("Expected '}'.");
            elements.last().map_or(start, |id| self.node_end(*id))
        };
        self.alloc_node(
            SyntaxKind::NamedExports,
            TextRange::new(start, end),
            NodeData::NamedExports(Box::new(NamedExportsData {
                elements: NodeList {
                    range: TextRange::new(start, end),
                    nodes: elements.clone(),
                    has_trailing_comma: false,
                },
                facts: 0,
            })),
            &elements,
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
        if self.current.kind == SyntaxKind::OpenParenToken && self.is_parenthesized_arrow() {
            return self.parse_parenthesized_arrow_function();
        }
        let mut left = self.parse_postfix_expression();
        if self.current.kind == SyntaxKind::EqualsGreaterThanToken
            && self.arena.get(left).unwrap().kind == SyntaxKind::Identifier
        {
            return self.parse_single_parameter_arrow_function(left);
        }
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

    fn parse_postfix_expression(&mut self) -> NodeId {
        let mut expression = self.parse_primary_expression();
        loop {
            match self.current.kind {
                SyntaxKind::DotToken => {
                    self.bump();
                    let name = self.parse_identifier("Expected a property name.");
                    expression = self.alloc_node(
                        SyntaxKind::PropertyAccessExpression,
                        TextRange::new(self.node_start(expression), self.node_end(name)),
                        NodeData::PropertyAccessExpression(Box::new(
                            PropertyAccessExpressionData {
                                expression,
                                flow_node: None,
                                question_dot_token: None,
                                facts: 0,
                                name,
                            },
                        )),
                        &[expression, name],
                    );
                }
                SyntaxKind::OpenParenToken => {
                    let arguments = self.parse_argument_list();
                    let end = arguments.range.end;
                    let mut children = vec![expression];
                    children.extend(arguments.nodes.iter().copied());
                    expression = self.alloc_node(
                        SyntaxKind::CallExpression,
                        TextRange::new(self.node_start(expression), end),
                        NodeData::CallExpression(Box::new(CallExpressionData {
                            arguments,
                            expression,
                            question_dot_token: None,
                            symbol: None,
                            type_arguments: None,
                            facts: 0,
                        })),
                        &children,
                    );
                }
                _ => break,
            }
        }
        expression
    }

    fn parse_argument_list(&mut self) -> NodeList {
        let start = self.consume().range.start;
        let mut arguments = Vec::new();
        let mut trailing = false;
        while self.current.kind != SyntaxKind::CloseParenToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            arguments.push(self.parse_binary_expression(2));
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
            trailing = self.current.kind == SyntaxKind::CloseParenToken;
        }
        let end = if self.current.kind == SyntaxKind::CloseParenToken {
            self.consume().range.end
        } else {
            self.error_current("Expected ')'.");
            arguments.last().map_or(start, |id| self.node_end(*id))
        };
        NodeList {
            range: TextRange::new(start, end),
            nodes: arguments,
            has_trailing_comma: trailing,
        }
    }

    fn is_parenthesized_arrow(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let mut depth = 1_u32;
        let mut token = self.scanner.scan();
        while token.kind != SyntaxKind::EndOfFile {
            match token.kind {
                SyntaxKind::OpenParenToken => depth += 1,
                SyntaxKind::CloseParenToken => {
                    depth -= 1;
                    if depth == 0 {
                        token = self.scanner.scan();
                        if token.kind == SyntaxKind::ColonToken {
                            while !matches!(
                                token.kind,
                                SyntaxKind::EqualsGreaterThanToken | SyntaxKind::EndOfFile
                            ) {
                                token = self.scanner.scan();
                            }
                        }
                        let result = token.kind == SyntaxKind::EqualsGreaterThanToken;
                        self.scanner.rewind(checkpoint);
                        return result;
                    }
                }
                _ => {}
            }
            token = self.scanner.scan();
        }
        self.scanner.rewind(checkpoint);
        false
    }

    fn parse_parenthesized_arrow_function(&mut self) -> NodeId {
        let start = self.current.range.start;
        let parameters = self.parse_parameter_list();
        let return_type = self.parse_optional_type_annotation();
        let arrow =
            self.parse_expected_token_node(SyntaxKind::EqualsGreaterThanToken, "Expected '=>'.");
        let body = if self.current.kind == SyntaxKind::OpenBraceToken {
            self.parse_block()
        } else {
            self.parse_binary_expression(2)
        };
        let mut children = parameters.nodes.clone();
        children.extend(return_type);
        children.push(arrow);
        children.push(body);
        self.alloc_node(
            SyntaxKind::ArrowFunction,
            TextRange::new(start, self.node_end(body)),
            NodeData::ArrowFunction(Box::new(ArrowFunctionData {
                asterisk_token: None,
                body,
                end_flow_node: None,
                equals_greater_than_token: arrow,
                flow_node: None,
                full_signature: None,
                locals: SymbolTable,
                next_container: None,
                parameters,
                symbol: None,
                type_: return_type,
                type_parameters: None,
                facts: 0,
                modifiers: None,
            })),
            &children,
        )
    }

    fn parse_single_parameter_arrow_function(&mut self, name: NodeId) -> NodeId {
        let start = self.node_start(name);
        let parameter = self.alloc_node(
            SyntaxKind::Parameter,
            self.arena.get(name).unwrap().range,
            NodeData::ParameterDeclaration(Box::new(ParameterDeclarationData {
                dot_dot_dot_token: None,
                initializer: None,
                question_token: None,
                symbol: None,
                type_: None,
                facts: 0,
                modifiers: None,
                name,
            })),
            &[name],
        );
        let arrow = self.consume_token_node();
        let body = if self.current.kind == SyntaxKind::OpenBraceToken {
            self.parse_block()
        } else {
            self.parse_binary_expression(2)
        };
        self.alloc_node(
            SyntaxKind::ArrowFunction,
            TextRange::new(start, self.node_end(body)),
            NodeData::ArrowFunction(Box::new(ArrowFunctionData {
                asterisk_token: None,
                body,
                end_flow_node: None,
                equals_greater_than_token: arrow,
                flow_node: None,
                full_signature: None,
                locals: SymbolTable,
                next_container: None,
                parameters: NodeList {
                    range: TextRange::new(start, self.node_end(parameter)),
                    nodes: vec![parameter],
                    has_trailing_comma: false,
                },
                symbol: None,
                type_: None,
                type_parameters: None,
                facts: 0,
                modifiers: None,
            })),
            &[parameter, arrow, body],
        )
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
            SyntaxKind::OpenBracketToken => self.parse_array_literal(),
            SyntaxKind::OpenBraceToken => self.parse_object_literal(),
            SyntaxKind::TemplateHead => self.parse_template_expression(),
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

    fn parse_array_literal(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let mut elements = Vec::new();
        let mut trailing = false;
        while self.current.kind != SyntaxKind::CloseBracketToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            elements.push(self.parse_binary_expression(2));
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
            trailing = self.current.kind == SyntaxKind::CloseBracketToken;
        }
        let end = if self.current.kind == SyntaxKind::CloseBracketToken {
            self.consume().range.end
        } else {
            self.error_current("Expected ']'.");
            elements.last().map_or(start, |id| self.node_end(*id))
        };
        self.alloc_node(
            SyntaxKind::ArrayLiteralExpression,
            TextRange::new(start, end),
            NodeData::ArrayLiteralExpression(Box::new(ArrayLiteralExpressionData {
                elements: NodeList {
                    range: TextRange::new(start, end),
                    nodes: elements.clone(),
                    has_trailing_comma: trailing,
                },
                multi_line: false,
                facts: 0,
            })),
            &elements,
        )
    }

    fn parse_object_literal(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let mut properties = Vec::new();
        while self.current.kind != SyntaxKind::CloseBraceToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            let property_start = self.current.range.start;
            let name = self.parse_identifier("Expected a property name.");
            if self.current.kind == SyntaxKind::ColonToken {
                self.bump();
            } else {
                self.error_current("Expected ':'.");
            }
            let initializer = self.parse_binary_expression(2);
            properties.push(self.alloc_node(
                SyntaxKind::PropertyAssignment,
                TextRange::new(property_start, self.node_end(initializer)),
                NodeData::PropertyAssignment(Box::new(PropertyAssignmentData {
                    initializer,
                    postfix_token: None,
                    symbol: None,
                    type_: initializer,
                    facts: 0,
                    modifiers: None,
                    name,
                })),
                &[name, initializer],
            ));
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
        }
        let end = if self.current.kind == SyntaxKind::CloseBraceToken {
            self.consume().range.end
        } else {
            self.error_current("Expected '}'.");
            properties.last().map_or(start, |id| self.node_end(*id))
        };
        self.alloc_node(
            SyntaxKind::ObjectLiteralExpression,
            TextRange::new(start, end),
            NodeData::ObjectLiteralExpression(Box::new(ObjectLiteralExpressionData {
                multi_line: false,
                properties: NodeList {
                    range: TextRange::new(start, end),
                    nodes: properties.clone(),
                    has_trailing_comma: false,
                },
                symbol: None,
                facts: 0,
            })),
            &properties,
        )
    }

    fn parse_template_expression(&mut self) -> NodeId {
        let head_token = self.consume();
        let start = head_token.range.start;
        let head = self.alloc_node(
            SyntaxKind::TemplateHead,
            head_token.range,
            NodeData::TemplateHead(Box::new(TemplateHeadData {
                raw_text: head_token.text.to_owned(),
                template_flags: TokenFlags::default(),
                text: token_value(&head_token),
                token_flags: TokenFlags::default(),
            })),
            &[],
        );
        let mut spans = Vec::new();
        loop {
            let expression = self.parse_binary_expression(0);
            if self.current.kind != SyntaxKind::CloseBraceToken {
                self.error_current("Expected '}'.");
                break;
            }
            self.current = self.scanner.rescan_template_token();
            let literal_token = self.consume();
            let literal = match literal_token.kind {
                SyntaxKind::TemplateMiddle => self.alloc_node(
                    SyntaxKind::TemplateMiddle,
                    literal_token.range,
                    NodeData::TemplateMiddle(Box::new(TemplateMiddleData {
                        raw_text: literal_token.text.to_owned(),
                        template_flags: TokenFlags::default(),
                        text: token_value(&literal_token),
                        token_flags: TokenFlags::default(),
                    })),
                    &[],
                ),
                SyntaxKind::TemplateTail => self.alloc_node(
                    SyntaxKind::TemplateTail,
                    literal_token.range,
                    NodeData::TemplateTail(Box::new(TemplateTailData {
                        raw_text: literal_token.text.to_owned(),
                        template_flags: TokenFlags::default(),
                        text: token_value(&literal_token),
                        token_flags: TokenFlags::default(),
                    })),
                    &[],
                ),
                _ => {
                    self.error_current("Expected a template continuation.");
                    self.missing_identifier(literal_token.range.start)
                }
            };
            spans.push(self.alloc_node(
                SyntaxKind::TemplateSpan,
                TextRange::new(self.node_start(expression), self.node_end(literal)),
                NodeData::TemplateSpan(Box::new(TemplateSpanData {
                    expression,
                    literal,
                })),
                &[expression, literal],
            ));
            if literal_token.kind == SyntaxKind::TemplateTail {
                break;
            }
        }
        let end = spans
            .last()
            .map_or(self.node_end(head), |id| self.node_end(*id));
        let mut children = vec![head];
        children.extend(spans.iter().copied());
        self.alloc_node(
            SyntaxKind::TemplateExpression,
            TextRange::new(start, end),
            NodeData::TemplateExpression(Box::new(TemplateExpressionData {
                head,
                template_spans: NodeList {
                    range: TextRange::new(self.node_end(head), end),
                    nodes: spans,
                    has_trailing_comma: false,
                },
                facts: 0,
            })),
            &children,
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

    fn expect_and_bump(&mut self, kind: SyntaxKind, message: &str) {
        if self.current.kind == kind {
            self.bump();
        } else {
            self.error_current(message);
        }
    }

    fn consume_token_node(&mut self) -> NodeId {
        let token = self.consume();
        self.alloc_node(
            token.kind,
            token.range,
            NodeData::Token(Box::new(TokenData)),
            &[],
        )
    }

    fn parse_expected_token_node(&mut self, kind: SyntaxKind, message: &str) -> NodeId {
        if self.current.kind == kind {
            return self.consume_token_node();
        }
        let position = self.current.range.start;
        self.error_current(message);
        self.alloc_node_with_flags(
            kind,
            NODE_FLAG_HAS_ERROR,
            TextRange::new(position, position),
            NodeData::Token(Box::new(TokenData)),
            &[],
        )
    }

    fn consume(&mut self) -> Token<'a> {
        let next = self.scanner.scan();
        std::mem::replace(&mut self.current, next)
    }
}

fn extend_list_children(children: &mut Vec<NodeId>, list: Option<&NodeList>) {
    if let Some(list) = list {
        children.extend(list.nodes.iter().copied());
    }
}

fn token_value(token: &Token<'_>) -> String {
    token
        .value
        .as_ref()
        .map_or_else(|| token.text.to_owned(), ts_core::JsString::to_string_lossy)
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
    fn parses_declarations_signatures_and_control_flow() {
        let source = r"
            function add<T>(a: T, b: T): T { if (a) return b; else return a; }
            class Box<T> extends Base<T> { value: T; map(x: T): T { return x; } }
            interface Shape<T> { area(x: T): number; value: T; }
            type Pair<T> = Box<T>;
            enum Color { Red = 1, Blue }
            for (let i = 0; i < 3; i = i + 1) { while (i) return; }
        ";
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let kinds: Vec<_> = source_statements(&result)
            .iter()
            .map(|id| result.arena.get(*id).unwrap().kind)
            .collect();
        assert_eq!(
            kinds,
            [
                SyntaxKind::FunctionDeclaration,
                SyntaxKind::ClassDeclaration,
                SyntaxKind::InterfaceDeclaration,
                SyntaxKind::TypeAliasDeclaration,
                SyntaxKind::EnumDeclaration,
                SyntaxKind::ForStatement,
            ]
        );
        let NodeData::FunctionDeclaration(function) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
        else {
            panic!("expected function");
        };
        assert_eq!(function.parameters.nodes.len(), 2);
        assert_eq!(function.type_parameters.as_ref().unwrap().nodes.len(), 1);
        assert_eq!(
            result.arena.get(function.body.unwrap()).unwrap().parent,
            Some(source_statements(&result)[0])
        );
        let NodeData::ClassDeclaration(class) = &result
            .arena
            .get(source_statements(&result)[1])
            .unwrap()
            .data
        else {
            panic!("expected class");
        };
        assert_eq!(class.members.nodes.len(), 2);
        assert_eq!(class.heritage_clauses.as_ref().unwrap().nodes.len(), 1);
        for member in &class.members.nodes {
            assert_eq!(
                result.arena.get(*member).unwrap().parent,
                Some(source_statements(&result)[1])
            );
        }
    }

    #[test]
    fn parses_arrow_postfix_aggregate_and_template_expressions() {
        let source = r"
            const f = (x: number): number => x + 1;
            f({value: [1, 2]}).value;
            const t = `a${f(1)}b${2}`;
        ";
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let (list, _) = variable_list(&result, statements[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected declaration");
        };
        assert_eq!(
            result
                .arena
                .get(declaration.initializer.unwrap())
                .unwrap()
                .kind,
            SyntaxKind::ArrowFunction
        );
        let NodeData::ExpressionStatement(postfix) = &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected expression statement");
        };
        assert_eq!(
            result.arena.get(postfix.expression).unwrap().kind,
            SyntaxKind::PropertyAccessExpression
        );
        let NodeData::PropertyAccessExpression(property_access) =
            &result.arena.get(postfix.expression).unwrap().data
        else {
            panic!("expected property access");
        };
        let NodeData::CallExpression(call) =
            &result.arena.get(property_access.expression).unwrap().data
        else {
            panic!("expected call expression");
        };
        let object = call.arguments.nodes[0];
        let NodeData::ObjectLiteralExpression(object) = &result.arena.get(object).unwrap().data
        else {
            panic!("expected object literal");
        };
        let NodeData::PropertyAssignment(property) =
            &result.arena.get(object.properties.nodes[0]).unwrap().data
        else {
            panic!("expected property assignment");
        };
        assert_eq!(
            result.arena.get(property.initializer).unwrap().kind,
            SyntaxKind::ArrayLiteralExpression
        );
        let (list, _) = variable_list(&result, statements[2]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected template declaration");
        };
        let template = declaration.initializer.unwrap();
        let NodeData::TemplateExpression(template_data) = &result.arena.get(template).unwrap().data
        else {
            panic!("expected template expression");
        };
        assert_eq!(template_data.template_spans.nodes.len(), 2);
        for span in &template_data.template_spans.nodes {
            assert_eq!(result.arena.get(*span).unwrap().parent, Some(template));
        }
    }

    #[test]
    fn parses_imports_and_exports() {
        let source = r#"
            import base, {x as y, z} from "m";
            import "side";
            export {y as value} from "m";
            export default y;
        "#;
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let kinds: Vec<_> = source_statements(&result)
            .iter()
            .map(|id| result.arena.get(*id).unwrap().kind)
            .collect();
        assert_eq!(
            kinds,
            [
                SyntaxKind::ImportDeclaration,
                SyntaxKind::ImportDeclaration,
                SyntaxKind::ExportDeclaration,
                SyntaxKind::ExportAssignment,
            ]
        );
        let NodeData::ImportDeclaration(first_import) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
        else {
            panic!("expected import declaration");
        };
        assert_eq!(
            result
                .arena
                .get(first_import.import_clause.unwrap())
                .unwrap()
                .parent,
            Some(source_statements(&result)[0])
        );
    }

    #[test]
    fn recovers_across_malformed_declarations_modules_and_templates() {
        let source = r"
            function broken<T>(x: T { return x; }
            class Missing { value: ; }
            import {x as} from ;
            const t = `x${1;
        ";
        let result = parse_source_file(source);
        assert!(result.diagnostics.len() >= 4, "{:?}", result.diagnostics);
        let kinds: Vec<_> = source_statements(&result)
            .iter()
            .map(|id| result.arena.get(*id).unwrap().kind)
            .collect();
        assert!(kinds.contains(&SyntaxKind::FunctionDeclaration));
        assert!(kinds.contains(&SyntaxKind::ClassDeclaration));
        assert!(kinds.contains(&SyntaxKind::ImportDeclaration));
        assert!(kinds.contains(&SyntaxKind::VariableStatement));
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
