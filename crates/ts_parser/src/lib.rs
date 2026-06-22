//! TypeScript parser.

use ts_ast::{
    ArrayLiteralExpressionData, ArrayTypeNodeData, ArrowFunctionData, AsExpressionData,
    AwaitExpressionData, BigIntLiteralData, BinaryExpressionData, BindingElementData,
    BindingPatternData, BlockData, BreakStatementData, CallExpressionData,
    CallSignatureDeclarationData, CaseBlockData, CaseOrDefaultClauseData, CatchClauseData,
    ClassDeclarationData, ClassStaticBlockDeclarationData, ComputedPropertyNameData,
    ConditionalExpressionData, ConditionalTypeNodeData, ConstructSignatureDeclarationData,
    ConstructorTypeNodeData, ContinueStatementData, DecoratorData, DoStatementData,
    ElementAccessExpressionData, EmptyStatementData, EnumDeclarationData, EnumMemberData,
    ExportAssignmentData, ExportDeclarationData, ExportSpecifierData, ExpressionStatementData,
    ExpressionWithTypeArgumentsData, ExternalModuleReferenceData, ForInOrOfStatementData,
    ForStatementData, FunctionDeclarationData, FunctionTypeNodeData, GetAccessorDeclarationData,
    HeritageClauseData, IdentifierData, IfStatementData, ImportAttributeData, ImportAttributesData,
    ImportClauseData, ImportDeclarationData, ImportEqualsDeclarationData, ImportSpecifierData,
    ImportTypeNodeData, IndexSignatureDeclarationData, IndexedAccessTypeNodeData,
    InferTypeNodeData, InterfaceDeclarationData, IntersectionTypeNodeData, JsDocData,
    JsDocTextData, JsDocUnknownTagData, JsxAttributeData, JsxAttributesData, JsxClosingElementData,
    JsxClosingFragmentData, JsxElementData, JsxExpressionData, JsxFragmentData,
    JsxOpeningElementData, JsxOpeningFragmentData, JsxSelfClosingElementData,
    JsxSpreadAttributeData, JsxTextData, KeywordExpressionData, KeywordTypeNodeData,
    LiteralTypeNodeData, MappedTypeNodeData, MethodDeclarationData, MethodSignatureDeclarationData,
    ModifierList, ModuleBlockData, ModuleDeclarationData, NamedExportsData, NamedImportsData,
    NamespaceImportData, NewExpressionData, NoSubstitutionTemplateLiteralData, Node, NodeArena,
    NodeData, NodeFlags, NodeId, NodeList, NonNullExpressionData, NumericLiteralData,
    ObjectLiteralExpressionData, ParameterDeclarationData, ParenthesizedExpressionData,
    ParenthesizedTypeNodeData, PostfixUnaryExpressionData, PrefixUnaryExpressionData,
    PrivateIdentifierData, PropertyAccessExpressionData, PropertyAssignmentData,
    PropertyDeclarationData, QualifiedNameData, RestTypeNodeData, ReturnStatementData,
    SatisfiesExpressionData, SetAccessorDeclarationData, ShorthandPropertyAssignmentData,
    SourceFileData, SpreadAssignmentData, SpreadElementData, StringLiteralData,
    SwitchStatementData, SymbolTable, SyntaxKind, TemplateExpressionData, TemplateHeadData,
    TemplateLiteralTypeNodeData, TemplateLiteralTypeSpanData, TemplateMiddleData, TemplateSpanData,
    TemplateTailData, ThisTypeNodeData, ThrowStatementData, TokenData, TokenFlags,
    TryStatementData, TupleTypeNodeData, TypeAliasDeclarationData, TypeAssertionData,
    TypeLiteralNodeData, TypeOperatorNodeData, TypeParameterDeclarationData, TypePredicateNodeData,
    TypeQueryNodeData, TypeReferenceNodeData, UnionTypeNodeData, VariableDeclarationData,
    VariableDeclarationListData, VariableStatementData, WhileStatementData, YieldExpressionData,
};
use ts_core::{Diagnostic, DiagnosticCategory, TextPos, TextRange};
use ts_diagnostics::{Category, message_by_code};
use ts_scanner::{LanguageVariant, Scanner, Token, TokenFlags as ScannerTokenFlags};

const NODE_FLAG_LET: NodeFlags = NodeFlags(1 << 0);
const NODE_FLAG_CONST: NodeFlags = NodeFlags(1 << 1);
const NODE_FLAG_USING: NodeFlags = NodeFlags(1 << 2);
const NODE_FLAG_AWAIT_USING: NodeFlags = NodeFlags((1 << 1) | (1 << 2));
const NODE_FLAG_HAS_ERROR: NodeFlags = NodeFlags(1 << 15);

/// Result of parsing one source file.
#[derive(Debug)]
pub struct ParseResult {
    pub arena: NodeArena,
    pub source_file: NodeId,
    pub diagnostics: Vec<Diagnostic>,
}

/// Result of parsing a standalone `JSDoc` comment.
#[derive(Debug)]
pub struct JsDocParseResult {
    pub arena: NodeArena,
    pub jsdoc: NodeId,
    pub diagnostics: Vec<Diagnostic>,
}

/// Parse a TypeScript source file into the generated arena-backed AST.
#[must_use]
pub fn parse_source_file(source: &str) -> ParseResult {
    Parser::new(source).parse_source_file()
}

/// Parse a TSX/JSX source file.
#[must_use]
pub fn parse_jsx_source_file(source: &str) -> ParseResult {
    Parser::new_with_variant(source, LanguageVariant::Jsx).parse_source_file()
}

/// Parse the text and tag names of a standalone `/** ... */` comment.
#[must_use]
pub fn parse_jsdoc_comment(source: &str) -> JsDocParseResult {
    let mut scanner = Scanner::new(source);
    scanner.reset_pos(if source.starts_with("/**") { 3 } else { 0 });
    scanner.set_skip_jsdoc_leading_asterisks(true);
    let mut arena = NodeArena::new();
    let mut comments = Vec::new();
    let mut tags = Vec::new();
    loop {
        let token = scanner.scan_jsdoc_comment_text_token(false);
        if token.kind == SyntaxKind::EndOfFile
            || token.range.start.get() as usize >= source.len().saturating_sub(2)
        {
            break;
        }
        if token.kind == SyntaxKind::AtToken {
            let tag = scanner.scan_jsdoc_token();
            if tag.kind == SyntaxKind::Identifier {
                let tag_name = arena.alloc(Node {
                    kind: SyntaxKind::Identifier,
                    flags: NodeFlags::default(),
                    range: tag.range,
                    parent: None,
                    data: NodeData::Identifier(Box::new(IdentifierData {
                        flow_node: None,
                        text: token_value(&tag),
                    })),
                });
                let tag_node = arena.alloc(Node {
                    kind: SyntaxKind::JsDocUnknownTag,
                    flags: NodeFlags::default(),
                    range: TextRange::new(token.range.start, tag.range.end),
                    parent: None,
                    data: NodeData::JsDocUnknownTag(Box::new(JsDocUnknownTagData {
                        comment: None,
                        tag_name,
                    })),
                });
                if let Some(node) = arena.get_mut(tag_name) {
                    node.parent = Some(tag_node);
                }
                tags.push(tag_node);
            }
        } else if token.kind == SyntaxKind::JsDocCommentTextToken {
            comments.push(arena.alloc(Node {
                kind: SyntaxKind::JsDocText,
                flags: NodeFlags::default(),
                range: token.range,
                parent: None,
                data: NodeData::JsDocText(Box::new(JsDocTextData {
                    text: vec![token_value(&token)],
                })),
            }));
        }
    }
    let end = TextPos::new(u32::try_from(source.len()).unwrap_or(u32::MAX));
    let mut children = comments.clone();
    children.extend(tags.iter().copied());
    let jsdoc = arena.alloc(Node {
        kind: SyntaxKind::JsDoc,
        flags: NodeFlags::default(),
        range: TextRange::new(TextPos::new(0), end),
        parent: None,
        data: NodeData::JsDoc(Box::new(JsDocData {
            comment: NodeList {
                range: TextRange::new(TextPos::new(0), end),
                nodes: comments,
                has_trailing_comma: false,
            },
            tags: (!tags.is_empty()).then_some(NodeList {
                range: TextRange::new(TextPos::new(0), end),
                nodes: tags,
                has_trailing_comma: false,
            }),
        })),
    });
    for child in children {
        if let Some(node) = arena.get_mut(child) {
            node.parent = Some(jsdoc);
        }
    }
    JsDocParseResult {
        arena,
        jsdoc,
        diagnostics: scanner.diagnostics().to_vec(),
    }
}

struct Parser<'a> {
    scanner: Scanner<'a>,
    current: Token<'a>,
    language_variant: LanguageVariant,
    arena: NodeArena,
    diagnostics: Vec<Diagnostic>,
}

impl<'a> Parser<'a> {
    fn new(source: &'a str) -> Self {
        Self::new_with_variant(source, LanguageVariant::Standard)
    }

    fn new_with_variant(source: &'a str, variant: LanguageVariant) -> Self {
        let mut scanner = Scanner::new(source);
        scanner.set_language_variant(variant);
        let current = scanner.scan();
        Self {
            scanner,
            current,
            language_variant: variant,
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
            SyntaxKind::UsingKeyword => self.parse_using_statement(),
            SyntaxKind::AwaitKeyword => self.parse_await_statement(),
            SyntaxKind::FunctionKeyword => self.parse_function_declaration(),
            SyntaxKind::ClassKeyword => self.parse_class_declaration(),
            SyntaxKind::InterfaceKeyword => self.parse_interface_declaration(),
            SyntaxKind::TypeKeyword => self.parse_type_alias_declaration(),
            SyntaxKind::EnumKeyword => self.parse_enum_declaration(),
            SyntaxKind::ReturnKeyword => self.parse_return_statement(),
            SyntaxKind::IfKeyword => self.parse_if_statement(),
            SyntaxKind::WhileKeyword => self.parse_while_statement(),
            SyntaxKind::ForKeyword => self.parse_for_statement(),
            SyntaxKind::SwitchKeyword => self.parse_switch_statement(),
            SyntaxKind::TryKeyword => self.parse_try_statement(),
            SyntaxKind::ThrowKeyword => self.parse_throw_statement(),
            SyntaxKind::DoKeyword => self.parse_do_statement(),
            SyntaxKind::BreakKeyword | SyntaxKind::ContinueKeyword => {
                self.parse_break_or_continue_statement()
            }
            SyntaxKind::NamespaceKeyword
            | SyntaxKind::ModuleKeyword
            | SyntaxKind::GlobalKeyword => self.parse_module_declaration(),
            SyntaxKind::AtToken => self.parse_decorated_statement(),
            SyntaxKind::DeclareKeyword | SyntaxKind::AbstractKeyword | SyntaxKind::AsyncKeyword => {
                self.parse_modified_statement()
            }
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
        self.parse_variable_statement_tail(keyword.range.start, declaration_flags)
    }

    fn parse_using_statement(&mut self) -> NodeId {
        let start = self.consume().range.start;
        self.parse_variable_statement_tail(start, NODE_FLAG_USING)
    }

    fn parse_await_statement(&mut self) -> NodeId {
        if self.next_token_kind() != SyntaxKind::UsingKeyword {
            return self.parse_expression_statement();
        }
        let start = self.consume().range.start;
        self.bump();
        self.parse_variable_statement_tail(start, NODE_FLAG_AWAIT_USING)
    }

    fn next_token_kind(&mut self) -> SyntaxKind {
        let checkpoint = self.scanner.mark();
        let kind = self.scanner.scan().kind;
        self.scanner.rewind(checkpoint);
        kind
    }

    fn parse_variable_statement_tail(
        &mut self,
        statement_start: TextPos,
        declaration_flags: NodeFlags,
    ) -> NodeId {
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
            TextRange::new(statement_start, end),
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
        let name = self.parse_binding_name("Expected a variable name.");
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
        let asterisk_token = if self.current.kind == SyntaxKind::AsteriskToken {
            Some(self.consume_token_node())
        } else {
            None
        };
        let name = if self.current.kind == SyntaxKind::Identifier || self.current.kind.is_keyword()
        {
            Some(self.parse_identifier_name("Expected a function name."))
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
        children.extend(asterisk_token);
        children.extend(name);
        extend_list_children(&mut children, type_parameters.as_ref());
        children.extend(parameters.nodes.iter().copied());
        children.extend(return_type);
        children.extend(body);
        self.alloc_node(
            SyntaxKind::FunctionDeclaration,
            TextRange::new(start, end),
            NodeData::FunctionDeclaration(Box::new(FunctionDeclarationData {
                asterisk_token,
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
        let name = self.parse_binding_name("Expected a parameter name.");
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

    fn parse_array_binding_pattern(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let mut elements = Vec::new();
        while !matches!(
            self.current.kind,
            SyntaxKind::CloseBracketToken | SyntaxKind::EndOfFile
        ) {
            if self.current.kind == SyntaxKind::CommaToken {
                self.bump();
                continue;
            }
            let before = (self.current.kind, self.current.range);
            let element_start = self.current.range.start;
            let dot_dot_dot_token = if self.current.kind == SyntaxKind::DotDotDotToken {
                Some(self.consume_token_node())
            } else {
                None
            };
            let name = self.parse_binding_name("Expected a binding name.");
            let initializer = if self.current.kind == SyntaxKind::EqualsToken {
                self.bump();
                Some(self.parse_binary_expression(2))
            } else {
                None
            };
            let mut children = vec![name];
            children.extend(dot_dot_dot_token);
            children.extend(initializer);
            let end = initializer.map_or_else(|| self.node_end(name), |id| self.node_end(id));
            elements.push(self.alloc_node(
                SyntaxKind::BindingElement,
                TextRange::new(element_start, end),
                NodeData::BindingElement(Box::new(BindingElementData {
                    dot_dot_dot_token,
                    flow_node: None,
                    initializer,
                    local_symbol: None,
                    property_name: None,
                    symbol: None,
                    facts: 0,
                    name: Some(name),
                })),
                &children,
            ));
            if self.current.kind == SyntaxKind::CommaToken {
                self.bump();
            }
            if before == (self.current.kind, self.current.range) {
                self.error_current("Parser made no progress while parsing a binding element.");
                self.bump();
            }
        }
        let end = if self.current.kind == SyntaxKind::CloseBracketToken {
            self.consume().range.end
        } else {
            self.error_current("Expected ']'.");
            elements.last().map_or(start, |node| self.node_end(*node))
        };
        self.alloc_node(
            SyntaxKind::ArrayBindingPattern,
            TextRange::new(start, end),
            NodeData::BindingPattern(Box::new(BindingPatternData {
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

    fn parse_binding_name(&mut self, message: &str) -> NodeId {
        match self.current.kind {
            SyntaxKind::OpenBracketToken => self.parse_array_binding_pattern(),
            SyntaxKind::OpenBraceToken => self.parse_object_binding_pattern(),
            _ => self.parse_identifier_name(message),
        }
    }

    fn parse_object_binding_pattern(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let mut elements = Vec::new();
        while !matches!(
            self.current.kind,
            SyntaxKind::CloseBraceToken | SyntaxKind::EndOfFile
        ) {
            let element_start = self.current.range.start;
            let dot_dot_dot_token = if self.current.kind == SyntaxKind::DotDotDotToken {
                Some(self.consume_token_node())
            } else {
                None
            };
            let first_name = self.parse_identifier_name("Expected a binding name.");
            let (property_name, name) = if self.current.kind == SyntaxKind::ColonToken {
                self.bump();
                (
                    Some(first_name),
                    self.parse_binding_name("Expected a binding name."),
                )
            } else {
                (None, first_name)
            };
            let initializer = if self.current.kind == SyntaxKind::EqualsToken {
                self.bump();
                Some(self.parse_binary_expression(2))
            } else {
                None
            };
            let end = initializer.map_or_else(|| self.node_end(name), |id| self.node_end(id));
            let mut children = Vec::new();
            children.extend(dot_dot_dot_token);
            children.extend(property_name);
            children.push(name);
            children.extend(initializer);
            elements.push(self.alloc_node(
                SyntaxKind::BindingElement,
                TextRange::new(element_start, end),
                NodeData::BindingElement(Box::new(BindingElementData {
                    dot_dot_dot_token,
                    flow_node: None,
                    initializer,
                    local_symbol: None,
                    property_name,
                    symbol: None,
                    facts: 0,
                    name: Some(name),
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
            elements.last().map_or(start, |node| self.node_end(*node))
        };
        self.alloc_node(
            SyntaxKind::ObjectBindingPattern,
            TextRange::new(start, end),
            NodeData::BindingPattern(Box::new(BindingPatternData {
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
                let expression = self.parse_entity_name();
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
            let before = (self.current.kind, self.current.range);
            if self.current.kind == SyntaxKind::SemicolonToken {
                self.bump();
                continue;
            }
            members.push(if signature_only {
                self.parse_type_member()
            } else {
                self.parse_class_member(false)
            });
            if before == (self.current.kind, self.current.range) {
                self.error_current("Parser made no progress while parsing a member.");
                self.bump();
            }
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
        if self.current.kind == SyntaxKind::StaticKeyword && self.next_token_is_open_brace() {
            return self.parse_class_static_block(start);
        }
        let mut modifier_nodes = Vec::new();
        while self.current.kind.is_modifier() {
            modifier_nodes.push(self.consume_token_node());
        }
        let modifiers = (!modifier_nodes.is_empty()).then(|| ModifierList {
            list: NodeList {
                range: TextRange::new(start, self.current.range.start),
                nodes: modifier_nodes.clone(),
                has_trailing_comma: false,
            },
            flags: ts_ast::ModifierFlags::default(),
        });
        if matches!(
            self.current.kind,
            SyntaxKind::GetKeyword | SyntaxKind::SetKeyword
        ) && self.is_accessor_signature()
        {
            return self.parse_class_accessor(start, modifiers, modifier_nodes);
        }
        let asterisk_token = if self.current.kind == SyntaxKind::AsteriskToken {
            Some(self.consume_token_node())
        } else {
            None
        };
        let name = self.parse_property_name("Expected a member name.");
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
            let mut children = modifier_nodes.clone();
            children.extend(asterisk_token);
            children.push(name);
            children.extend(parameters.nodes.iter().copied());
            children.extend(return_type);
            children.extend(body);
            self.alloc_node(
                SyntaxKind::MethodDeclaration,
                TextRange::new(start, end),
                NodeData::MethodDeclaration(Box::new(MethodDeclarationData {
                    asterisk_token,
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
                    modifiers: modifiers.clone(),
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
            let mut children = modifier_nodes;
            children.push(name);
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
                    modifiers,
                    name,
                })),
                &children,
            )
        }
    }

    fn parse_class_accessor(
        &mut self,
        start: TextPos,
        modifiers: Option<ModifierList>,
        modifier_nodes: Vec<NodeId>,
    ) -> NodeId {
        let kind = self.consume().kind;
        let name = self.parse_property_name("Expected an accessor name.");
        let parameters = self.parse_parameter_list();
        let return_type = self.parse_optional_type_annotation();
        let body = if self.current.kind == SyntaxKind::OpenBraceToken {
            Some(self.parse_block())
        } else {
            self.parse_semicolon(
                return_type.map_or(parameters.range.end, |node| self.node_end(node)),
            );
            None
        };
        let end = body
            .or(return_type)
            .map_or(parameters.range.end, |node| self.node_end(node));
        let mut children = modifier_nodes;
        children.push(name);
        children.extend(parameters.nodes.iter().copied());
        children.extend(return_type);
        children.extend(body);
        let data = if kind == SyntaxKind::GetKeyword {
            NodeData::GetAccessorDeclaration(Box::new(GetAccessorDeclarationData {
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
                modifiers,
                name,
            }))
        } else {
            NodeData::SetAccessorDeclaration(Box::new(SetAccessorDeclarationData {
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
                modifiers,
                name,
            }))
        };
        self.alloc_node(
            if kind == SyntaxKind::GetKeyword {
                SyntaxKind::GetAccessor
            } else {
                SyntaxKind::SetAccessor
            },
            TextRange::new(start, end),
            data,
            &children,
        )
    }

    fn next_token_is_open_brace(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let next = self.scanner.scan();
        self.scanner.rewind(checkpoint);
        next.kind == SyntaxKind::OpenBraceToken
    }

    fn parse_class_static_block(&mut self, start: TextPos) -> NodeId {
        let static_modifier = self.consume_token_node();
        let body = self.parse_block();
        self.alloc_node(
            SyntaxKind::ClassStaticBlockDeclaration,
            TextRange::new(start, self.node_end(body)),
            NodeData::ClassStaticBlockDeclaration(Box::new(ClassStaticBlockDeclarationData {
                body,
                locals: SymbolTable,
                next_container: None,
                return_flow_node: None,
                symbol: None,
                facts: 0,
                modifiers: Some(ModifierList {
                    list: NodeList {
                        range: TextRange::new(start, self.node_start(body)),
                        nodes: vec![static_modifier],
                        has_trailing_comma: false,
                    },
                    flags: ts_ast::ModifierFlags::default(),
                }),
            })),
            &[static_modifier, body],
        )
    }

    fn parse_type_member(&mut self) -> NodeId {
        let start = self.current.range.start;
        let mut modifier_nodes = Vec::new();
        while self.current.kind == SyntaxKind::ReadonlyKeyword {
            modifier_nodes.push(self.consume_token_node());
        }
        let modifiers = (!modifier_nodes.is_empty()).then(|| ModifierList {
            list: NodeList {
                range: TextRange::new(start, self.current.range.start),
                nodes: modifier_nodes.clone(),
                has_trailing_comma: false,
            },
            flags: ts_ast::ModifierFlags::default(),
        });
        let index_signature =
            self.current.kind == SyntaxKind::OpenBracketToken && self.is_index_signature();
        let accessor_signature = matches!(
            self.current.kind,
            SyntaxKind::GetKeyword | SyntaxKind::SetKeyword
        ) && self.is_accessor_signature();

        let member = match self.current.kind {
            SyntaxKind::OpenParenToken | SyntaxKind::LessThanToken => {
                self.parse_signature_member(start, SyntaxKind::CallSignature)
            }
            SyntaxKind::NewKeyword => {
                self.bump();
                self.parse_signature_member(start, SyntaxKind::ConstructSignature)
            }
            SyntaxKind::OpenBracketToken if index_signature => {
                self.parse_index_signature(start, modifiers)
            }
            SyntaxKind::GetKeyword | SyntaxKind::SetKeyword if accessor_signature => {
                self.parse_accessor_signature(start, modifiers)
            }
            _ => self.parse_named_type_member(start, modifiers),
        };
        for modifier in modifier_nodes {
            self.arena.get_mut(modifier).unwrap().parent = Some(member);
        }
        member
    }

    fn is_index_signature(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let name = self.scanner.scan();
        let colon = self.scanner.scan();
        self.scanner.rewind(checkpoint);
        (name.kind == SyntaxKind::Identifier || name.kind.is_keyword())
            && colon.kind == SyntaxKind::ColonToken
    }

    fn is_accessor_signature(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let name = self.scanner.scan();
        self.scanner.rewind(checkpoint);
        matches!(
            name.kind,
            SyntaxKind::Identifier
                | SyntaxKind::StringLiteral
                | SyntaxKind::NumericLiteral
                | SyntaxKind::OpenBracketToken
        ) || name.kind.is_keyword()
    }

    fn parse_signature_member(&mut self, start: TextPos, kind: SyntaxKind) -> NodeId {
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameter_list();
        let return_type = self.parse_optional_type_annotation();
        let fallback = return_type.map_or(parameters.range.end, |node| self.node_end(node));
        let end = self.parse_semicolon(fallback);
        let mut children = Vec::new();
        extend_list_children(&mut children, type_parameters.as_ref());
        children.extend(parameters.nodes.iter().copied());
        children.extend(return_type);
        let data = if kind == SyntaxKind::CallSignature {
            NodeData::CallSignatureDeclaration(Box::new(CallSignatureDeclarationData {
                full_signature: None,
                locals: SymbolTable,
                next_container: None,
                parameters,
                symbol: None,
                type_: return_type,
                type_parameters,
            }))
        } else {
            NodeData::ConstructSignatureDeclaration(Box::new(ConstructSignatureDeclarationData {
                full_signature: None,
                locals: SymbolTable,
                next_container: None,
                parameters,
                symbol: None,
                type_: return_type,
                type_parameters,
            }))
        };
        self.alloc_node(kind, TextRange::new(start, end), data, &children)
    }

    fn parse_accessor_signature(
        &mut self,
        start: TextPos,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let kind = self.consume().kind;
        let name = self.parse_property_name("Expected an accessor name.");
        let parameters = self.parse_parameter_list();
        let return_type = self.parse_optional_type_annotation();
        let fallback = return_type.map_or(parameters.range.end, |node| self.node_end(node));
        let end = self.parse_semicolon(fallback);
        let mut children = vec![name];
        children.extend(parameters.nodes.iter().copied());
        children.extend(return_type);
        let data = if kind == SyntaxKind::GetKeyword {
            NodeData::GetAccessorDeclaration(Box::new(GetAccessorDeclarationData {
                asterisk_token: None,
                body: None,
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
                modifiers,
                name,
            }))
        } else {
            NodeData::SetAccessorDeclaration(Box::new(SetAccessorDeclarationData {
                asterisk_token: None,
                body: None,
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
                modifiers,
                name,
            }))
        };
        self.alloc_node(
            if kind == SyntaxKind::GetKeyword {
                SyntaxKind::GetAccessor
            } else {
                SyntaxKind::SetAccessor
            },
            TextRange::new(start, end),
            data,
            &children,
        )
    }

    fn parse_index_signature(&mut self, start: TextPos, modifiers: Option<ModifierList>) -> NodeId {
        let parameters_start = self.consume().range.start;
        let mut parameter_nodes = Vec::new();
        while !matches!(
            self.current.kind,
            SyntaxKind::CloseBracketToken | SyntaxKind::EndOfFile
        ) {
            parameter_nodes.push(self.parse_parameter());
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
        }
        let parameters_end = if self.current.kind == SyntaxKind::CloseBracketToken {
            self.consume().range.end
        } else {
            self.error_current("Expected ']'.");
            parameter_nodes
                .last()
                .map_or(parameters_start, |node| self.node_end(*node))
        };
        if self.current.kind == SyntaxKind::ColonToken {
            self.bump();
        } else {
            self.error_current("Expected a type annotation.");
        }
        let type_node = self.parse_type();
        let end = self.parse_semicolon(self.node_end(type_node));
        let parameters = NodeList {
            range: TextRange::new(parameters_start, parameters_end),
            nodes: parameter_nodes.clone(),
            has_trailing_comma: false,
        };
        let mut children = parameter_nodes;
        children.push(type_node);
        self.alloc_node(
            SyntaxKind::IndexSignature,
            TextRange::new(start, end),
            NodeData::IndexSignatureDeclaration(Box::new(IndexSignatureDeclarationData {
                full_signature: None,
                locals: SymbolTable,
                next_container: None,
                parameters,
                symbol: None,
                type_: type_node,
                type_parameters: None,
                modifiers,
            })),
            &children,
        )
    }

    fn parse_named_type_member(
        &mut self,
        start: TextPos,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let name = self.parse_property_name("Expected a member name.");
        let postfix_token = if self.current.kind == SyntaxKind::QuestionToken {
            Some(self.consume_token_node())
        } else {
            None
        };
        if matches!(
            self.current.kind,
            SyntaxKind::LessThanToken | SyntaxKind::OpenParenToken
        ) {
            let type_parameters = self.parse_type_parameters();
            let parameters = self.parse_parameter_list();
            let return_type = self.parse_optional_type_annotation();
            let fallback = return_type.map_or(parameters.range.end, |node| self.node_end(node));
            let end = self.parse_semicolon(fallback);
            let mut children = vec![name];
            children.extend(postfix_token);
            extend_list_children(&mut children, type_parameters.as_ref());
            children.extend(parameters.nodes.iter().copied());
            children.extend(return_type);
            return self.alloc_node(
                SyntaxKind::MethodSignature,
                TextRange::new(start, end),
                NodeData::MethodSignatureDeclaration(Box::new(MethodSignatureDeclarationData {
                    full_signature: None,
                    locals: SymbolTable,
                    next_container: None,
                    parameters,
                    postfix_token,
                    symbol: None,
                    type_: return_type,
                    type_parameters,
                    modifiers,
                    name,
                })),
                &children,
            );
        }

        let type_node = self.parse_optional_type_annotation();
        let fallback = type_node.map_or_else(|| self.node_end(name), |node| self.node_end(node));
        let end = self.parse_semicolon(fallback);
        let mut children = vec![name];
        children.extend(postfix_token);
        children.extend(type_node);
        self.alloc_node(
            SyntaxKind::PropertyDeclaration,
            TextRange::new(start, end),
            NodeData::PropertyDeclaration(Box::new(PropertyDeclarationData {
                initializer: None,
                postfix_token,
                symbol: None,
                type_: type_node,
                facts: 0,
                modifiers,
                name,
            })),
            &children,
        )
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

    #[allow(clippy::too_many_lines)]
    fn parse_for_statement(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let await_modifier = if self.current.kind == SyntaxKind::AwaitKeyword {
            Some(self.consume_token_node())
        } else {
            None
        };
        self.expect_and_bump(SyntaxKind::OpenParenToken, "Expected '('.");
        let initializer = if self.current.kind == SyntaxKind::SemicolonToken {
            None
        } else if matches!(
            self.current.kind,
            SyntaxKind::VarKeyword
                | SyntaxKind::LetKeyword
                | SyntaxKind::ConstKeyword
                | SyntaxKind::UsingKeyword
        ) {
            let keyword = self.consume();
            let flags = match keyword.kind {
                SyntaxKind::LetKeyword => NODE_FLAG_LET,
                SyntaxKind::ConstKeyword => NODE_FLAG_CONST,
                SyntaxKind::UsingKeyword => NODE_FLAG_USING,
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
            Some(self.parse_binary_expression(11))
        };
        if matches!(
            self.current.kind,
            SyntaxKind::InKeyword | SyntaxKind::OfKeyword
        ) {
            let loop_kind = if self.current.kind == SyntaxKind::InKeyword {
                SyntaxKind::ForInStatement
            } else {
                SyntaxKind::ForOfStatement
            };
            self.bump();
            let expression = self.parse_binary_expression(0);
            self.expect_and_bump(SyntaxKind::CloseParenToken, "Expected ')'.");
            let statement = self.parse_statement();
            let initializer = initializer.unwrap_or_else(|| {
                self.error_current("Expected a for-in/of initializer.");
                self.missing_identifier(self.current.range.start)
            });
            return self.alloc_node(
                loop_kind,
                TextRange::new(start, self.node_end(statement)),
                NodeData::ForInOrOfStatement(Box::new(ForInOrOfStatementData {
                    await_modifier,
                    expression,
                    flow_node: None,
                    initializer,
                    locals: SymbolTable,
                    next_container: None,
                    statement,
                    facts: 0,
                })),
                &await_modifier
                    .into_iter()
                    .chain([initializer, expression, statement])
                    .collect::<Vec<_>>(),
            );
        }
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

    fn parse_switch_statement(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let expression = self.parse_parenthesized_condition();
        let block_start = self.current.range.start;
        self.expect_and_bump(SyntaxKind::OpenBraceToken, "Expected '{'.");
        let mut clauses = Vec::new();
        while !matches!(
            self.current.kind,
            SyntaxKind::CloseBraceToken | SyntaxKind::EndOfFile
        ) {
            let clause_start = self.current.range.start;
            let (kind, clause_expression) = if self.current.kind == SyntaxKind::CaseKeyword {
                self.bump();
                (SyntaxKind::CaseClause, self.parse_binary_expression(0))
            } else if self.current.kind == SyntaxKind::DefaultKeyword {
                self.bump();
                (
                    SyntaxKind::DefaultClause,
                    self.missing_identifier(self.current.range.start),
                )
            } else {
                self.error_current("Expected 'case' or 'default'.");
                self.bump();
                continue;
            };
            self.expect_and_bump(SyntaxKind::ColonToken, "Expected ':'.");
            let statements = self.parse_case_statements();
            let end = statements
                .nodes
                .last()
                .map_or_else(|| self.node_end(clause_expression), |id| self.node_end(*id));
            let mut children = vec![clause_expression];
            children.extend(statements.nodes.iter().copied());
            clauses.push(self.alloc_node(
                kind,
                TextRange::new(clause_start, end),
                NodeData::CaseOrDefaultClause(Box::new(CaseOrDefaultClauseData {
                    expression: clause_expression,
                    fallthrough_flow_node: None,
                    statements,
                    facts: 0,
                })),
                &children,
            ));
        }
        let end = if self.current.kind == SyntaxKind::CloseBraceToken {
            self.consume().range.end
        } else {
            self.error_current("Expected '}'.");
            self.current.range.start
        };
        let case_block = self.alloc_node(
            SyntaxKind::CaseBlock,
            TextRange::new(block_start, end),
            NodeData::CaseBlock(Box::new(CaseBlockData {
                clauses: NodeList {
                    range: TextRange::new(block_start, end),
                    nodes: clauses.clone(),
                    has_trailing_comma: false,
                },
                locals: SymbolTable,
                next_container: None,
                facts: 0,
            })),
            &clauses,
        );
        self.alloc_node(
            SyntaxKind::SwitchStatement,
            TextRange::new(start, end),
            NodeData::SwitchStatement(Box::new(SwitchStatementData {
                case_block,
                expression,
                flow_node: None,
                facts: 0,
            })),
            &[expression, case_block],
        )
    }

    fn parse_case_statements(&mut self) -> NodeList {
        let start = self.current.full_start;
        let mut statements = Vec::new();
        while !matches!(
            self.current.kind,
            SyntaxKind::CaseKeyword
                | SyntaxKind::DefaultKeyword
                | SyntaxKind::CloseBraceToken
                | SyntaxKind::EndOfFile
        ) {
            let before = (self.current.kind, self.current.range);
            statements.push(self.parse_statement());
            if before == (self.current.kind, self.current.range) {
                self.error_current("Parser made no progress while parsing a case statement.");
                self.bump();
            }
        }
        NodeList {
            range: TextRange::new(start, self.current.full_start),
            nodes: statements,
            has_trailing_comma: false,
        }
    }

    fn parse_try_statement(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let try_block = self.parse_block();
        let catch_clause = if self.current.kind == SyntaxKind::CatchKeyword {
            let catch_start = self.consume().range.start;
            let variable_declaration = if self.current.kind == SyntaxKind::OpenParenToken {
                self.bump();
                let declaration = self.parse_variable_declaration();
                self.expect_and_bump(SyntaxKind::CloseParenToken, "Expected ')'.");
                Some(declaration)
            } else {
                None
            };
            let block = self.parse_block();
            let mut children = vec![block];
            children.extend(variable_declaration);
            Some(self.alloc_node(
                SyntaxKind::CatchClause,
                TextRange::new(catch_start, self.node_end(block)),
                NodeData::CatchClause(Box::new(CatchClauseData {
                    block,
                    locals: SymbolTable,
                    next_container: None,
                    variable_declaration,
                    facts: 0,
                })),
                &children,
            ))
        } else {
            None
        };
        let finally_block = if self.current.kind == SyntaxKind::FinallyKeyword {
            self.bump();
            Some(self.parse_block())
        } else {
            None
        };
        if catch_clause.is_none() && finally_block.is_none() {
            self.error_current("Expected 'catch' or 'finally'.");
        }
        let end = finally_block
            .or(catch_clause)
            .map_or_else(|| self.node_end(try_block), |id| self.node_end(id));
        let mut children = vec![try_block];
        children.extend(catch_clause);
        children.extend(finally_block);
        self.alloc_node(
            SyntaxKind::TryStatement,
            TextRange::new(start, end),
            NodeData::TryStatement(Box::new(TryStatementData {
                catch_clause,
                finally_block,
                flow_node: None,
                try_block,
                facts: 0,
            })),
            &children,
        )
    }

    fn parse_throw_statement(&mut self) -> NodeId {
        let keyword = self.consume();
        if self
            .current
            .flags
            .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
        {
            self.error_current("Line break not permitted after 'throw'.");
        }
        let expression = self.parse_binary_expression(0);
        let end = self.parse_semicolon(self.node_end(expression));
        self.alloc_node(
            SyntaxKind::ThrowStatement,
            TextRange::new(keyword.range.start, end),
            NodeData::ThrowStatement(Box::new(ThrowStatementData {
                expression,
                flow_node: None,
                facts: 0,
            })),
            &[expression],
        )
    }

    fn parse_do_statement(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let statement = self.parse_statement();
        self.expect_and_bump(SyntaxKind::WhileKeyword, "Expected 'while'.");
        let expression = self.parse_parenthesized_condition();
        let end = self.parse_semicolon(self.node_end(expression));
        self.alloc_node(
            SyntaxKind::DoStatement,
            TextRange::new(start, end),
            NodeData::DoStatement(Box::new(DoStatementData {
                expression,
                flow_node: None,
                statement,
                facts: 0,
            })),
            &[statement, expression],
        )
    }

    fn parse_break_or_continue_statement(&mut self) -> NodeId {
        let keyword = self.consume();
        let label = if self.current.kind == SyntaxKind::Identifier
            && !self
                .current
                .flags
                .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
        {
            Some(self.parse_identifier("Expected a label."))
        } else {
            None
        };
        let end = self.parse_semicolon(label.map_or(keyword.range.end, |id| self.node_end(id)));
        let data = if keyword.kind == SyntaxKind::BreakKeyword {
            NodeData::BreakStatement(Box::new(BreakStatementData {
                flow_node: None,
                label,
            }))
        } else {
            NodeData::ContinueStatement(Box::new(ContinueStatementData {
                flow_node: None,
                label,
            }))
        };
        self.alloc_node(
            if keyword.kind == SyntaxKind::BreakKeyword {
                SyntaxKind::BreakStatement
            } else {
                SyntaxKind::ContinueStatement
            },
            TextRange::new(keyword.range.start, end),
            data,
            &label.into_iter().collect::<Vec<_>>(),
        )
    }

    fn parse_module_declaration(&mut self) -> NodeId {
        let keyword = self.consume();
        let name = if keyword.kind == SyntaxKind::GlobalKeyword {
            self.alloc_node(
                SyntaxKind::Identifier,
                keyword.range,
                NodeData::Identifier(Box::new(IdentifierData {
                    flow_node: None,
                    text: token_value(&keyword),
                })),
                &[],
            )
        } else if self.current.kind == SyntaxKind::StringLiteral {
            self.parse_string_literal()
        } else {
            self.parse_identifier("Expected a module name.")
        };
        let body = if self.current.kind == SyntaxKind::OpenBraceToken {
            let block = self.parse_block();
            let block_node = self.arena.get(block).unwrap();
            let NodeData::Block(block_data) = &block_node.data else {
                unreachable!()
            };
            Some(self.alloc_node(
                SyntaxKind::ModuleBlock,
                block_node.range,
                NodeData::ModuleBlock(Box::new(ModuleBlockData {
                    flow_node: None,
                    statements: block_data.statements.clone(),
                    facts: 0,
                })),
                &block_data.statements.nodes.clone(),
            ))
        } else {
            self.error_current("Expected '{'.");
            None
        };
        let end = body.map_or_else(|| self.node_end(name), |id| self.node_end(id));
        let mut children = vec![name];
        children.extend(body);
        self.alloc_node(
            SyntaxKind::ModuleDeclaration,
            TextRange::new(keyword.range.start, end),
            NodeData::ModuleDeclaration(Box::new(ModuleDeclarationData {
                asterisk_token: None,
                body,
                end_flow_node: None,
                flow_node: None,
                keyword: keyword.kind,
                local_symbol: None,
                locals: SymbolTable,
                next_container: None,
                symbol: None,
                facts: 0,
                modifiers: None,
                name,
            })),
            &children,
        )
    }

    fn parse_decorated_statement(&mut self) -> NodeId {
        let start = self.current.range.start;
        let mut decorators = Vec::new();
        while self.current.kind == SyntaxKind::AtToken {
            self.bump();
            let expression = self.parse_postfix_expression();
            decorators.push(self.alloc_node(
                SyntaxKind::Decorator,
                TextRange::new(start, self.node_end(expression)),
                NodeData::Decorator(Box::new(DecoratorData {
                    expression,
                    facts: 0,
                })),
                &[expression],
            ));
        }
        let declaration = self.parse_statement();
        self.attach_modifiers(declaration, decorators, start);
        declaration
    }

    fn parse_modified_statement(&mut self) -> NodeId {
        let start = self.current.range.start;
        let mut modifiers = Vec::new();
        while matches!(
            self.current.kind,
            SyntaxKind::DeclareKeyword | SyntaxKind::AbstractKeyword | SyntaxKind::AsyncKeyword
        ) {
            modifiers.push(self.consume_token_node());
        }
        let declaration = self.parse_statement();
        self.attach_modifiers(declaration, modifiers, start);
        declaration
    }

    fn attach_modifiers(
        &mut self,
        declaration: NodeId,
        mut modifier_nodes: Vec<NodeId>,
        start: TextPos,
    ) {
        let existing = self
            .arena
            .get(declaration)
            .and_then(|node| match &node.data {
                NodeData::ClassDeclaration(data) => data.modifiers.clone(),
                NodeData::FunctionDeclaration(data) => data.modifiers.clone(),
                NodeData::InterfaceDeclaration(data) => data.modifiers.clone(),
                NodeData::TypeAliasDeclaration(data) => data.modifiers.clone(),
                NodeData::EnumDeclaration(data) => data.modifiers.clone(),
                NodeData::VariableStatement(data) => data.modifiers.clone(),
                NodeData::ModuleDeclaration(data) => data.modifiers.clone(),
                _ => None,
            });
        if let Some(existing) = existing {
            modifier_nodes.extend(existing.list.nodes);
        }
        let modifiers = ModifierList {
            list: NodeList {
                range: TextRange::new(start, self.node_start(declaration)),
                nodes: modifier_nodes.clone(),
                has_trailing_comma: false,
            },
            flags: ts_ast::ModifierFlags::default(),
        };
        if let Some(node) = self.arena.get_mut(declaration) {
            match &mut node.data {
                NodeData::ClassDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::FunctionDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::InterfaceDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::TypeAliasDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::EnumDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::VariableStatement(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::ModuleDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                _ => self.diagnostics.push(parser_diagnostic(
                    node.range,
                    "Decorators are not valid here.",
                )),
            }
            node.range.start = start;
        }
        for modifier in modifier_nodes {
            self.arena.get_mut(modifier).unwrap().parent = Some(declaration);
        }
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
            if let Some(name) = name
                && self.current.kind == SyntaxKind::EqualsToken
            {
                return self.parse_import_equals_declaration(start, name);
            }
            if name.is_some() && self.current.kind == SyntaxKind::CommaToken {
                self.bump();
            }
            let named_bindings = if self.current.kind == SyntaxKind::OpenBraceToken {
                Some(self.parse_named_imports())
            } else if self.current.kind == SyntaxKind::AsteriskToken {
                Some(self.parse_namespace_import())
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
        let attributes = self.parse_import_attributes();
        children.extend(attributes);
        let fallback = attributes.map_or_else(
            || self.node_end(module_specifier),
            |node| self.node_end(node),
        );
        let end = self.parse_semicolon(fallback);
        self.alloc_node(
            SyntaxKind::ImportDeclaration,
            TextRange::new(start, end),
            NodeData::ImportDeclaration(Box::new(ImportDeclarationData {
                attributes,
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

    fn parse_import_attributes(&mut self) -> Option<NodeId> {
        if !matches!(
            self.current.kind,
            SyntaxKind::WithKeyword | SyntaxKind::AssertKeyword
        ) {
            return None;
        }
        let keyword = self.consume();
        self.expect_and_bump(SyntaxKind::OpenBraceToken, "Expected '{'.");
        let list_start = self.current.range.start;
        let mut attributes = Vec::new();
        while !matches!(
            self.current.kind,
            SyntaxKind::CloseBraceToken | SyntaxKind::EndOfFile
        ) {
            let start = self.current.range.start;
            let name = self.parse_property_name("Expected an import attribute name.");
            self.expect_and_bump(SyntaxKind::ColonToken, "Expected ':'.");
            let value = if self.current.kind == SyntaxKind::StringLiteral {
                self.parse_string_literal()
            } else {
                self.parse_identifier_name("Expected an import attribute value.")
            };
            attributes.push(self.alloc_node(
                SyntaxKind::ImportAttribute,
                TextRange::new(start, self.node_end(value)),
                NodeData::ImportAttribute(Box::new(ImportAttributeData {
                    value,
                    facts: 0,
                    name,
                })),
                &[name, value],
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
            attributes
                .last()
                .map_or(list_start, |node| self.node_end(*node))
        };
        Some(self.alloc_node(
            SyntaxKind::ImportAttributes,
            TextRange::new(keyword.range.start, end),
            NodeData::ImportAttributes(Box::new(ImportAttributesData {
                attributes: NodeList {
                    range: TextRange::new(list_start, end),
                    nodes: attributes.clone(),
                    has_trailing_comma: false,
                },
                multi_line: false,
                token: keyword.kind,
                facts: 0,
            })),
            &attributes,
        ))
    }

    fn parse_namespace_import(&mut self) -> NodeId {
        let start = self.consume().range.start;
        self.expect_and_bump(SyntaxKind::AsKeyword, "Expected 'as'.");
        let name = self.parse_identifier("Expected a namespace import name.");
        self.alloc_node(
            SyntaxKind::NamespaceImport,
            TextRange::new(start, self.node_end(name)),
            NodeData::NamespaceImport(Box::new(NamespaceImportData {
                local_symbol: None,
                symbol: None,
                name,
            })),
            &[name],
        )
    }

    fn parse_import_equals_declaration(&mut self, start: TextPos, name: NodeId) -> NodeId {
        self.bump();
        let module_reference = if self.current.kind == SyntaxKind::RequireKeyword {
            let reference_start = self.consume().range.start;
            self.expect_and_bump(SyntaxKind::OpenParenToken, "Expected '('.");
            let expression = if self.current.kind == SyntaxKind::StringLiteral {
                self.parse_string_literal()
            } else {
                self.error_current("Expected a module specifier.");
                self.missing_identifier(self.current.range.start)
            };
            let end = if self.current.kind == SyntaxKind::CloseParenToken {
                self.consume().range.end
            } else {
                self.error_current("Expected ')'.");
                self.node_end(expression)
            };
            self.alloc_node(
                SyntaxKind::ExternalModuleReference,
                TextRange::new(reference_start, end),
                NodeData::ExternalModuleReference(Box::new(ExternalModuleReferenceData {
                    expression,
                })),
                &[expression],
            )
        } else {
            self.parse_entity_name()
        };
        let end = self.parse_semicolon(self.node_end(module_reference));
        self.alloc_node(
            SyntaxKind::ImportEqualsDeclaration,
            TextRange::new(start, end),
            NodeData::ImportEqualsDeclaration(Box::new(ImportEqualsDeclarationData {
                flow_node: None,
                is_type_only: false,
                local_symbol: None,
                module_reference,
                symbol: None,
                facts: 0,
                modifiers: None,
                name,
            })),
            &[name, module_reference],
        )
    }

    fn parse_entity_name(&mut self) -> NodeId {
        let mut entity = self.parse_identifier("Expected a module reference.");
        while self.current.kind == SyntaxKind::DotToken {
            self.bump();
            let right = self.parse_identifier("Expected an identifier after '.'.");
            entity = self.alloc_node(
                SyntaxKind::QualifiedName,
                TextRange::new(self.node_start(entity), self.node_end(right)),
                NodeData::QualifiedName(Box::new(QualifiedNameData {
                    flow_node: None,
                    left: entity,
                    right,
                    facts: 0,
                })),
                &[entity, right],
            );
        }
        entity
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

    #[allow(clippy::too_many_lines)]
    fn parse_export_declaration(&mut self) -> NodeId {
        let export_token = self.consume();
        let start = export_token.range.start;
        let export_modifier = self.alloc_node(
            SyntaxKind::ExportKeyword,
            export_token.range,
            NodeData::Token(Box::new(TokenData)),
            &[],
        );
        if matches!(
            self.current.kind,
            SyntaxKind::FunctionKeyword
                | SyntaxKind::ClassKeyword
                | SyntaxKind::InterfaceKeyword
                | SyntaxKind::TypeKeyword
                | SyntaxKind::EnumKeyword
                | SyntaxKind::NamespaceKeyword
                | SyntaxKind::ModuleKeyword
                | SyntaxKind::VarKeyword
                | SyntaxKind::LetKeyword
                | SyntaxKind::ConstKeyword
                | SyntaxKind::DeclareKeyword
                | SyntaxKind::AbstractKeyword
                | SyntaxKind::AsyncKeyword
        ) {
            let declaration = self.parse_statement();
            self.attach_modifiers(declaration, vec![export_modifier], start);
            return declaration;
        }
        if self.current.kind == SyntaxKind::DefaultKeyword {
            let default_modifier = self.consume_token_node();
            if matches!(
                self.current.kind,
                SyntaxKind::FunctionKeyword | SyntaxKind::ClassKeyword
            ) {
                let declaration = self.parse_statement();
                self.attach_modifiers(declaration, vec![export_modifier, default_modifier], start);
                return declaration;
            }
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
                    modifiers: Some(ModifierList {
                        list: NodeList {
                            range: TextRange::new(start, self.node_start(expression)),
                            nodes: vec![export_modifier, default_modifier],
                            has_trailing_comma: false,
                        },
                        flags: ts_ast::ModifierFlags::default(),
                    }),
                })),
                &[export_modifier, default_modifier, expression],
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
        let attributes = self.parse_import_attributes();
        let fallback = attributes
            .or(module_specifier)
            .or(export_clause)
            .map_or(start, |id| self.node_end(id));
        let end = self.parse_semicolon(fallback);
        let mut children = vec![export_modifier];
        children.extend(export_clause);
        children.extend(module_specifier);
        children.extend(attributes);
        self.alloc_node(
            SyntaxKind::ExportDeclaration,
            TextRange::new(start, end),
            NodeData::ExportDeclaration(Box::new(ExportDeclarationData {
                attributes,
                export_clause,
                flow_node: None,
                is_type_only: false,
                module_specifier,
                symbol: None,
                facts: 0,
                modifiers: Some(ModifierList {
                    list: NodeList {
                        range: TextRange::new(start, start),
                        nodes: vec![export_modifier],
                        has_trailing_comma: false,
                    },
                    flags: ts_ast::ModifierFlags::default(),
                }),
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
        if self.current.kind == SyntaxKind::AsyncKeyword && self.is_async_arrow_function() {
            return self.parse_async_arrow_function();
        }
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
        if minimum_precedence <= 2 && self.current.kind == SyntaxKind::QuestionToken {
            let question_token = self.consume_token_node();
            let when_true = self.parse_binary_expression(0);
            let colon_token =
                self.parse_expected_token_node(SyntaxKind::ColonToken, "Expected ':'.");
            let when_false = self.parse_binary_expression(0);
            left = self.alloc_node(
                SyntaxKind::ConditionalExpression,
                TextRange::new(self.node_start(left), self.node_end(when_false)),
                NodeData::ConditionalExpression(Box::new(ConditionalExpressionData {
                    colon_token,
                    condition: left,
                    question_token,
                    when_false,
                    when_true,
                    facts: 0,
                })),
                &[left, question_token, when_true, colon_token, when_false],
            );
        }
        left
    }

    fn is_async_arrow_function(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let first = self.scanner.scan();
        let result = if first.kind == SyntaxKind::Identifier {
            self.scanner.scan().kind == SyntaxKind::EqualsGreaterThanToken
        } else if first.kind == SyntaxKind::OpenParenToken {
            let mut depth = 1_u32;
            let mut token = self.scanner.scan();
            while token.kind != SyntaxKind::EndOfFile && depth > 0 {
                match token.kind {
                    SyntaxKind::OpenParenToken => depth += 1,
                    SyntaxKind::CloseParenToken => depth -= 1,
                    _ => {}
                }
                if depth > 0 {
                    token = self.scanner.scan();
                }
            }
            self.scanner.scan().kind == SyntaxKind::EqualsGreaterThanToken
        } else {
            false
        };
        self.scanner.rewind(checkpoint);
        result
    }

    fn parse_async_arrow_function(&mut self) -> NodeId {
        let async_modifier = self.consume_token_node();
        let start = self.node_start(async_modifier);
        let parameters = if self.current.kind == SyntaxKind::OpenParenToken {
            self.parse_parameter_list()
        } else {
            let name = self.parse_identifier("Expected a parameter name.");
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
            NodeList {
                range: self.arena.get(parameter).unwrap().range,
                nodes: vec![parameter],
                has_trailing_comma: false,
            }
        };
        let return_type = self.parse_optional_type_annotation();
        let arrow =
            self.parse_expected_token_node(SyntaxKind::EqualsGreaterThanToken, "Expected '=>'.");
        let body = if self.current.kind == SyntaxKind::OpenBraceToken {
            self.parse_block()
        } else {
            self.parse_binary_expression(2)
        };
        let mut children = vec![async_modifier];
        children.extend(parameters.nodes.iter().copied());
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
                modifiers: Some(ModifierList {
                    list: NodeList {
                        range: TextRange::new(start, self.node_end(async_modifier)),
                        nodes: vec![async_modifier],
                        has_trailing_comma: false,
                    },
                    flags: ts_ast::ModifierFlags::default(),
                }),
            })),
            &children,
        )
    }

    #[allow(clippy::too_many_lines)]
    fn parse_postfix_expression(&mut self) -> NodeId {
        if self.current.kind == SyntaxKind::AwaitKeyword {
            return self.parse_await_expression();
        }
        if self.current.kind == SyntaxKind::YieldKeyword {
            return self.parse_yield_expression();
        }
        if is_prefix_operator(self.current.kind) {
            let operator_token = self.consume();
            let operator = operator_token.kind;
            let operand = self.parse_postfix_expression();
            return self.alloc_node(
                SyntaxKind::PrefixUnaryExpression,
                TextRange::new(operator_token.range.start, self.node_end(operand)),
                NodeData::PrefixUnaryExpression(Box::new(PrefixUnaryExpressionData {
                    operand,
                    operator,
                })),
                &[operand],
            );
        }
        let mut expression = if self.current.kind == SyntaxKind::NewKeyword {
            self.parse_new_expression()
        } else {
            self.parse_primary_expression()
        };
        loop {
            match self.current.kind {
                SyntaxKind::DotToken => {
                    self.bump();
                    let name = self.parse_property_name("Expected a property name.");
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
                SyntaxKind::QuestionDotToken => {
                    let question_dot_token = self.consume_token_node();
                    if self.current.kind == SyntaxKind::OpenParenToken {
                        let arguments = self.parse_argument_list();
                        let end = arguments.range.end;
                        let mut children = vec![expression, question_dot_token];
                        children.extend(arguments.nodes.iter().copied());
                        expression = self.alloc_node(
                            SyntaxKind::CallExpression,
                            TextRange::new(self.node_start(expression), end),
                            NodeData::CallExpression(Box::new(CallExpressionData {
                                arguments,
                                expression,
                                question_dot_token: Some(question_dot_token),
                                symbol: None,
                                type_arguments: None,
                                facts: 0,
                            })),
                            &children,
                        );
                    } else if self.current.kind == SyntaxKind::OpenBracketToken {
                        self.bump();
                        let argument_expression = self.parse_binary_expression(0);
                        let end = if self.current.kind == SyntaxKind::CloseBracketToken {
                            self.consume().range.end
                        } else {
                            self.error_current("Expected ']'.");
                            self.node_end(argument_expression)
                        };
                        expression = self.alloc_node(
                            SyntaxKind::ElementAccessExpression,
                            TextRange::new(self.node_start(expression), end),
                            NodeData::ElementAccessExpression(Box::new(
                                ElementAccessExpressionData {
                                    argument_expression,
                                    expression,
                                    flow_node: None,
                                    question_dot_token: Some(question_dot_token),
                                    facts: 0,
                                },
                            )),
                            &[expression, question_dot_token, argument_expression],
                        );
                    } else {
                        let name = self.parse_property_name("Expected a property name.");
                        expression = self.alloc_node(
                            SyntaxKind::PropertyAccessExpression,
                            TextRange::new(self.node_start(expression), self.node_end(name)),
                            NodeData::PropertyAccessExpression(Box::new(
                                PropertyAccessExpressionData {
                                    expression,
                                    flow_node: None,
                                    question_dot_token: Some(question_dot_token),
                                    facts: 0,
                                    name,
                                },
                            )),
                            &[expression, question_dot_token, name],
                        );
                    }
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
                SyntaxKind::OpenBracketToken => {
                    self.bump();
                    let argument_expression = self.parse_binary_expression(0);
                    let end = if self.current.kind == SyntaxKind::CloseBracketToken {
                        self.consume().range.end
                    } else {
                        self.error_current("Expected ']'.");
                        self.node_end(argument_expression)
                    };
                    expression = self.alloc_node(
                        SyntaxKind::ElementAccessExpression,
                        TextRange::new(self.node_start(expression), end),
                        NodeData::ElementAccessExpression(Box::new(ElementAccessExpressionData {
                            argument_expression,
                            expression,
                            flow_node: None,
                            question_dot_token: None,
                            facts: 0,
                        })),
                        &[expression, argument_expression],
                    );
                }
                SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken => {
                    let operator = self.consume().kind;
                    expression = self.alloc_node(
                        SyntaxKind::PostfixUnaryExpression,
                        TextRange::new(self.node_start(expression), self.current.full_start),
                        NodeData::PostfixUnaryExpression(Box::new(PostfixUnaryExpressionData {
                            operand: expression,
                            operator,
                        })),
                        &[expression],
                    );
                }
                SyntaxKind::ExclamationToken => {
                    let end = self.consume().range.end;
                    expression = self.alloc_node(
                        SyntaxKind::NonNullExpression,
                        TextRange::new(self.node_start(expression), end),
                        NodeData::NonNullExpression(Box::new(NonNullExpressionData { expression })),
                        &[expression],
                    );
                }
                SyntaxKind::AsKeyword | SyntaxKind::SatisfiesKeyword => {
                    let kind = self.consume().kind;
                    let type_node = self.parse_type();
                    let data = if kind == SyntaxKind::AsKeyword {
                        NodeData::AsExpression(Box::new(AsExpressionData {
                            expression,
                            type_: type_node,
                        }))
                    } else {
                        NodeData::SatisfiesExpression(Box::new(SatisfiesExpressionData {
                            expression,
                            type_: type_node,
                        }))
                    };
                    expression = self.alloc_node(
                        if kind == SyntaxKind::AsKeyword {
                            SyntaxKind::AsExpression
                        } else {
                            SyntaxKind::SatisfiesExpression
                        },
                        TextRange::new(self.node_start(expression), self.node_end(type_node)),
                        data,
                        &[expression, type_node],
                    );
                }
                _ => break,
            }
        }
        expression
    }

    fn parse_await_expression(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let expression = self.parse_postfix_expression();
        self.alloc_node(
            SyntaxKind::AwaitExpression,
            TextRange::new(start, self.node_end(expression)),
            NodeData::AwaitExpression(Box::new(AwaitExpressionData { expression })),
            &[expression],
        )
    }

    fn parse_yield_expression(&mut self) -> NodeId {
        let keyword = self.consume();
        let asterisk_token = if self.current.kind == SyntaxKind::AsteriskToken {
            Some(self.consume_token_node())
        } else {
            None
        };
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
            Some(self.parse_binary_expression(2))
        };
        let end = expression.map_or(keyword.range.end, |node| self.node_end(node));
        let mut children = Vec::new();
        children.extend(asterisk_token);
        children.extend(expression);
        self.alloc_node(
            SyntaxKind::YieldExpression,
            TextRange::new(keyword.range.start, end),
            NodeData::YieldExpression(Box::new(YieldExpressionData {
                asterisk_token,
                expression,
            })),
            &children,
        )
    }

    fn parse_new_expression(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let expression = self.parse_primary_expression();
        let type_arguments = self.parse_type_arguments();
        let arguments = if self.current.kind == SyntaxKind::OpenParenToken {
            Some(self.parse_argument_list())
        } else {
            None
        };
        let end = arguments
            .as_ref()
            .map_or_else(|| self.node_end(expression), |list| list.range.end);
        let mut children = vec![expression];
        extend_list_children(&mut children, type_arguments.as_ref());
        extend_list_children(&mut children, arguments.as_ref());
        self.alloc_node(
            SyntaxKind::NewExpression,
            TextRange::new(start, end),
            NodeData::NewExpression(Box::new(NewExpressionData {
                arguments,
                expression,
                type_arguments,
                facts: 0,
            })),
            &children,
        )
    }

    fn parse_argument_list(&mut self) -> NodeList {
        let start = self.consume().range.start;
        let mut arguments = Vec::new();
        let mut trailing = false;
        while self.current.kind != SyntaxKind::CloseParenToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            arguments.push(self.parse_spread_element_or_expression());
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

    fn parse_spread_element_or_expression(&mut self) -> NodeId {
        if self.current.kind != SyntaxKind::DotDotDotToken {
            return self.parse_binary_expression(2);
        }
        let start = self.consume().range.start;
        let expression = self.parse_binary_expression(2);
        self.alloc_node(
            SyntaxKind::SpreadElement,
            TextRange::new(start, self.node_end(expression)),
            NodeData::SpreadElement(Box::new(SpreadElementData { expression })),
            &[expression],
        )
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
            SyntaxKind::PrivateIdentifier => self.parse_private_identifier(),
            SyntaxKind::NumericLiteral => self.parse_numeric_literal(),
            SyntaxKind::BigIntLiteral => self.parse_bigint_literal(),
            SyntaxKind::StringLiteral => self.parse_string_literal(),
            SyntaxKind::NoSubstitutionTemplateLiteral => self.parse_template_literal(),
            SyntaxKind::NullKeyword
            | SyntaxKind::TrueKeyword
            | SyntaxKind::FalseKeyword
            | SyntaxKind::ThisKeyword
            | SyntaxKind::SuperKeyword => self.parse_keyword_expression(),
            SyntaxKind::OpenParenToken => self.parse_parenthesized_expression(),
            SyntaxKind::OpenBracketToken => self.parse_array_literal(),
            SyntaxKind::OpenBraceToken => self.parse_object_literal(),
            SyntaxKind::TemplateHead => self.parse_template_expression(),
            SyntaxKind::LessThanToken if self.language_variant == LanguageVariant::Jsx => {
                self.parse_jsx_element(false)
            }
            SyntaxKind::LessThanToken => self.parse_type_assertion(),
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

    fn parse_type_assertion(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let type_node = self.parse_type();
        self.expect_and_bump(SyntaxKind::GreaterThanToken, "Expected '>'.");
        let expression = self.parse_postfix_expression();
        self.alloc_node(
            SyntaxKind::TypeAssertionExpression,
            TextRange::new(start, self.node_end(expression)),
            NodeData::TypeAssertion(Box::new(TypeAssertionData {
                expression,
                type_: type_node,
            })),
            &[type_node, expression],
        )
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
            elements.push(self.parse_spread_element_or_expression());
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

    #[allow(clippy::too_many_lines)]
    fn parse_object_literal(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let mut properties = Vec::new();
        while self.current.kind != SyntaxKind::CloseBraceToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            let property_start = self.current.range.start;
            if self.current.kind == SyntaxKind::DotDotDotToken {
                self.bump();
                let expression = self.parse_binary_expression(2);
                properties.push(self.alloc_node(
                    SyntaxKind::SpreadAssignment,
                    TextRange::new(property_start, self.node_end(expression)),
                    NodeData::SpreadAssignment(Box::new(SpreadAssignmentData {
                        expression,
                        symbol: None,
                    })),
                    &[expression],
                ));
                if self.current.kind == SyntaxKind::CommaToken {
                    self.bump();
                }
                continue;
            }
            let mut modifier_nodes = Vec::new();
            if self.current.kind == SyntaxKind::AsyncKeyword
                && !matches!(
                    self.next_token_kind(),
                    SyntaxKind::OpenParenToken
                        | SyntaxKind::ColonToken
                        | SyntaxKind::CommaToken
                        | SyntaxKind::CloseBraceToken
                )
            {
                modifier_nodes.push(self.consume_token_node());
            }
            let modifiers = (!modifier_nodes.is_empty()).then(|| ModifierList {
                list: NodeList {
                    range: TextRange::new(property_start, self.current.range.start),
                    nodes: modifier_nodes.clone(),
                    has_trailing_comma: false,
                },
                flags: ts_ast::ModifierFlags::default(),
            });
            let asterisk_token = if self.current.kind == SyntaxKind::AsteriskToken {
                Some(self.consume_token_node())
            } else {
                None
            };
            let name = self.parse_property_name("Expected a property name.");
            if matches!(
                self.current.kind,
                SyntaxKind::LessThanToken | SyntaxKind::OpenParenToken
            ) {
                let type_parameters = self.parse_type_parameters();
                let parameters = self.parse_parameter_list();
                let return_type = self.parse_optional_type_annotation();
                let body = if self.current.kind == SyntaxKind::OpenBraceToken {
                    Some(self.parse_block())
                } else {
                    self.error_current("Expected a method body.");
                    None
                };
                let end = body.map_or(parameters.range.end, |id| self.node_end(id));
                let mut children = modifier_nodes;
                children.extend(asterisk_token);
                children.push(name);
                extend_list_children(&mut children, type_parameters.as_ref());
                children.extend(parameters.nodes.iter().copied());
                children.extend(return_type);
                children.extend(body);
                properties.push(self.alloc_node(
                    SyntaxKind::MethodDeclaration,
                    TextRange::new(property_start, end),
                    NodeData::MethodDeclaration(Box::new(MethodDeclarationData {
                        asterisk_token,
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
                        type_parameters,
                        facts: 0,
                        modifiers,
                        name,
                    })),
                    &children,
                ));
            } else if self.current.kind == SyntaxKind::ColonToken {
                self.bump();
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
            } else {
                properties.push(self.alloc_node(
                    SyntaxKind::ShorthandPropertyAssignment,
                    TextRange::new(property_start, self.node_end(name)),
                    NodeData::ShorthandPropertyAssignment(Box::new(
                        ShorthandPropertyAssignmentData {
                            equals_token: None,
                            object_assignment_initializer: None,
                            postfix_token: None,
                            symbol: None,
                            type_: name,
                            facts: 0,
                            modifiers: None,
                            name,
                        },
                    )),
                    &[name],
                ));
            }
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

    #[allow(clippy::too_many_lines)]
    fn parse_jsx_element(&mut self, resume_jsx: bool) -> NodeId {
        let start = self.current.range.start;
        self.bump();
        if self.current.kind == SyntaxKind::GreaterThanToken {
            return self.parse_jsx_fragment(start, resume_jsx);
        }
        let tag_name = self.parse_identifier("Expected a JSX tag name.");
        let attributes = self.parse_jsx_attributes();
        if self.current.kind == SyntaxKind::SlashToken {
            self.bump();
            let end = self.finish_jsx_tag(resume_jsx);
            return self.alloc_node(
                SyntaxKind::JsxSelfClosingElement,
                TextRange::new(start, end),
                NodeData::JsxSelfClosingElement(Box::new(JsxSelfClosingElementData {
                    attributes,
                    tag_name,
                    type_arguments: None,
                    facts: 0,
                })),
                &[tag_name, attributes],
            );
        }
        let opening_end = self.finish_jsx_tag(true);
        let opening = self.alloc_node(
            SyntaxKind::JsxOpeningElement,
            TextRange::new(start, opening_end),
            NodeData::JsxOpeningElement(Box::new(JsxOpeningElementData {
                attributes,
                tag_name,
                type_arguments: None,
                facts: 0,
            })),
            &[tag_name, attributes],
        );
        let children = self.parse_jsx_children();
        let closing_start = self.current.range.start;
        if self.current.kind == SyntaxKind::LessThanSlashToken {
            self.current = self.scanner.scan();
        } else {
            self.error_current("Expected a JSX closing tag.");
        }
        let closing_name = self.parse_identifier("Expected a JSX closing tag name.");
        let end = self.finish_jsx_tag(resume_jsx);
        let closing = self.alloc_node(
            SyntaxKind::JsxClosingElement,
            TextRange::new(closing_start, end),
            NodeData::JsxClosingElement(Box::new(JsxClosingElementData {
                tag_name: closing_name,
            })),
            &[closing_name],
        );
        let mut all_children = vec![opening];
        all_children.extend(children.iter().copied());
        all_children.push(closing);
        self.alloc_node(
            SyntaxKind::JsxElement,
            TextRange::new(start, end),
            NodeData::JsxElement(Box::new(JsxElementData {
                children: NodeList {
                    range: TextRange::new(opening_end, closing_start),
                    nodes: children,
                    has_trailing_comma: false,
                },
                closing_element: closing,
                opening_element: opening,
                facts: 0,
            })),
            &all_children,
        )
    }

    fn parse_jsx_children(&mut self) -> Vec<NodeId> {
        let mut children = Vec::new();
        while !matches!(
            self.current.kind,
            SyntaxKind::LessThanSlashToken | SyntaxKind::EndOfFile
        ) {
            match self.current.kind {
                SyntaxKind::JsxText | SyntaxKind::JsxTextAllWhiteSpaces => {
                    let token = self.current.clone();
                    self.current = self.scanner.scan_jsx_token();
                    children.push(self.alloc_node(
                        token.kind,
                        token.range,
                        NodeData::JsxText(Box::new(JsxTextData {
                            contains_only_trivia_white_spaces: token.kind
                                == SyntaxKind::JsxTextAllWhiteSpaces,
                            text: token_value(&token),
                            token_flags: TokenFlags::default(),
                        })),
                        &[],
                    ));
                }
                SyntaxKind::OpenBraceToken => {
                    let expression_start = self.current.range.start;
                    self.current = self.scanner.scan();
                    let expression = if self.current.kind == SyntaxKind::CloseBraceToken {
                        None
                    } else {
                        Some(self.parse_binary_expression(0))
                    };
                    let end = if self.current.kind == SyntaxKind::CloseBraceToken {
                        let end = self.current.range.end;
                        self.current = self.scanner.scan_jsx_token();
                        end
                    } else {
                        self.error_current("Expected '}'.");
                        self.current.range.start
                    };
                    let expression_children: Vec<_> = expression.into_iter().collect();
                    children.push(self.alloc_node(
                        SyntaxKind::JsxExpression,
                        TextRange::new(expression_start, end),
                        NodeData::JsxExpression(Box::new(JsxExpressionData {
                            dot_dot_dot_token: None,
                            expression,
                        })),
                        &expression_children,
                    ));
                }
                SyntaxKind::LessThanToken => children.push(self.parse_jsx_element(true)),
                _ => {
                    self.error_current("Unexpected token in JSX children.");
                    self.current = self.scanner.scan_jsx_token();
                }
            }
        }
        children
    }

    fn parse_jsx_fragment(&mut self, start: TextPos, resume_jsx: bool) -> NodeId {
        let opening_end = self.finish_jsx_tag(true);
        let opening = self.alloc_node(
            SyntaxKind::JsxOpeningFragment,
            TextRange::new(start, opening_end),
            NodeData::JsxOpeningFragment(Box::new(JsxOpeningFragmentData)),
            &[],
        );
        let children = self.parse_jsx_children();
        let closing_start = self.current.range.start;
        if self.current.kind == SyntaxKind::LessThanSlashToken {
            self.current = self.scanner.scan();
        } else {
            self.error_current("Expected a JSX closing fragment.");
        }
        let end = self.finish_jsx_tag(resume_jsx);
        let closing = self.alloc_node(
            SyntaxKind::JsxClosingFragment,
            TextRange::new(closing_start, end),
            NodeData::JsxClosingFragment(Box::new(JsxClosingFragmentData)),
            &[],
        );
        let mut all_children = vec![opening];
        all_children.extend(children.iter().copied());
        all_children.push(closing);
        self.alloc_node(
            SyntaxKind::JsxFragment,
            TextRange::new(start, end),
            NodeData::JsxFragment(Box::new(JsxFragmentData {
                children: NodeList {
                    range: TextRange::new(opening_end, closing_start),
                    nodes: children,
                    has_trailing_comma: false,
                },
                closing_fragment: closing,
                opening_fragment: opening,
                facts: 0,
            })),
            &all_children,
        )
    }

    fn parse_jsx_attributes(&mut self) -> NodeId {
        let start = self.current.full_start;
        let mut attributes = Vec::new();
        while matches!(
            self.current.kind,
            SyntaxKind::Identifier | SyntaxKind::OpenBraceToken
        ) {
            let attribute_start = self.current.range.start;
            if self.current.kind == SyntaxKind::OpenBraceToken {
                self.bump();
                self.expect_and_bump(SyntaxKind::DotDotDotToken, "Expected '...'.");
                let expression = self.parse_binary_expression(0);
                let end = if self.current.kind == SyntaxKind::CloseBraceToken {
                    self.consume().range.end
                } else {
                    self.error_current("Expected '}'.");
                    self.node_end(expression)
                };
                attributes.push(self.alloc_node(
                    SyntaxKind::JsxSpreadAttribute,
                    TextRange::new(attribute_start, end),
                    NodeData::JsxSpreadAttribute(Box::new(JsxSpreadAttributeData { expression })),
                    &[expression],
                ));
                continue;
            }
            let name = self.parse_identifier("Expected a JSX attribute name.");
            let initializer = if self.current.kind == SyntaxKind::EqualsToken {
                self.bump();
                if self.current.kind == SyntaxKind::StringLiteral {
                    Some(self.parse_string_literal())
                } else if self.current.kind == SyntaxKind::OpenBraceToken {
                    let expression_start = self.current.range.start;
                    self.bump();
                    let expression = self.parse_binary_expression(0);
                    let end = if self.current.kind == SyntaxKind::CloseBraceToken {
                        self.consume().range.end
                    } else {
                        self.error_current("Expected '}'.");
                        self.node_end(expression)
                    };
                    Some(self.alloc_node(
                        SyntaxKind::JsxExpression,
                        TextRange::new(expression_start, end),
                        NodeData::JsxExpression(Box::new(JsxExpressionData {
                            dot_dot_dot_token: None,
                            expression: Some(expression),
                        })),
                        &[expression],
                    ))
                } else {
                    self.error_current("Expected a JSX attribute value.");
                    None
                }
            } else {
                None
            };
            let end = initializer.map_or_else(|| self.node_end(name), |id| self.node_end(id));
            let mut attribute_children = vec![name];
            attribute_children.extend(initializer);
            attributes.push(self.alloc_node(
                SyntaxKind::JsxAttribute,
                TextRange::new(attribute_start, end),
                NodeData::JsxAttribute(Box::new(JsxAttributeData {
                    initializer,
                    symbol: None,
                    facts: 0,
                    name,
                })),
                &attribute_children,
            ));
        }
        let end = attributes.last().map_or(start, |id| self.node_end(*id));
        self.alloc_node(
            SyntaxKind::JsxAttributes,
            TextRange::new(start, end),
            NodeData::JsxAttributes(Box::new(JsxAttributesData {
                properties: NodeList {
                    range: TextRange::new(start, end),
                    nodes: attributes.clone(),
                    has_trailing_comma: false,
                },
                symbol: None,
                facts: 0,
            })),
            &attributes,
        )
    }

    fn finish_jsx_tag(&mut self, resume_jsx: bool) -> TextPos {
        if self.current.kind != SyntaxKind::GreaterThanToken {
            self.error_current("Expected '>'.");
            return self.current.range.start;
        }
        let end = self.current.range.end;
        self.current = if resume_jsx {
            self.scanner.scan_jsx_token()
        } else {
            self.scanner.scan()
        };
        end
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

    fn parse_identifier_name(&mut self, message: &str) -> NodeId {
        if self.current.kind != SyntaxKind::Identifier && !self.current.kind.is_keyword() {
            let position = self.current.range.start;
            self.error_current(message);
            return self.missing_identifier(position);
        }
        let token = self.consume();
        self.alloc_node(
            SyntaxKind::Identifier,
            token.range,
            NodeData::Identifier(Box::new(IdentifierData {
                flow_node: None,
                text: token_value(&token),
            })),
            &[],
        )
    }

    fn parse_property_name(&mut self, message: &str) -> NodeId {
        match self.current.kind {
            SyntaxKind::StringLiteral => self.parse_string_literal(),
            SyntaxKind::NumericLiteral => self.parse_numeric_literal(),
            SyntaxKind::PrivateIdentifier => self.parse_private_identifier(),
            SyntaxKind::OpenBracketToken => {
                let start = self.consume().range.start;
                let expression = self.parse_binary_expression(0);
                let end = if self.current.kind == SyntaxKind::CloseBracketToken {
                    self.consume().range.end
                } else {
                    self.error_current("Expected ']'.");
                    self.node_end(expression)
                };
                self.alloc_node(
                    SyntaxKind::ComputedPropertyName,
                    TextRange::new(start, end),
                    NodeData::ComputedPropertyName(Box::new(ComputedPropertyNameData {
                        expression,
                        facts: 0,
                    })),
                    &[expression],
                )
            }
            _ => self.parse_identifier_name(message),
        }
    }

    fn parse_private_identifier(&mut self) -> NodeId {
        let token = self.consume();
        self.alloc_node(
            SyntaxKind::PrivateIdentifier,
            token.range,
            NodeData::PrivateIdentifier(Box::new(PrivateIdentifierData {
                text: token_value(&token),
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
        if self.is_type_predicate() {
            return self.parse_type_predicate();
        }
        let check_type = self.parse_union_type();
        if self.current.kind != SyntaxKind::ExtendsKeyword {
            return check_type;
        }
        self.bump();
        let extends_type = self.parse_union_type();
        self.expect_and_bump(SyntaxKind::QuestionToken, "Expected '?'.");
        let true_type = self.parse_type();
        self.expect_and_bump(SyntaxKind::ColonToken, "Expected ':'.");
        let false_type = self.parse_type();
        self.alloc_node(
            SyntaxKind::ConditionalType,
            TextRange::new(self.node_start(check_type), self.node_end(false_type)),
            NodeData::ConditionalTypeNode(Box::new(ConditionalTypeNodeData {
                check_type,
                extends_type,
                false_type,
                locals: SymbolTable,
                next_container: None,
                true_type,
            })),
            &[check_type, extends_type, true_type, false_type],
        )
    }

    fn is_type_predicate(&mut self) -> bool {
        if !matches!(
            self.current.kind,
            SyntaxKind::Identifier | SyntaxKind::ThisKeyword
        ) {
            return false;
        }
        let checkpoint = self.scanner.mark();
        let next = self.scanner.scan();
        self.scanner.rewind(checkpoint);
        next.kind == SyntaxKind::IsKeyword
    }

    fn parse_type_predicate(&mut self) -> NodeId {
        let start = self.current.range.start;
        let parameter_name = if self.current.kind == SyntaxKind::ThisKeyword {
            let token = self.consume();
            self.alloc_node(
                SyntaxKind::ThisType,
                token.range,
                NodeData::ThisTypeNode(Box::new(ThisTypeNodeData)),
                &[],
            )
        } else {
            self.parse_identifier("Expected a predicate parameter name.")
        };
        self.expect_and_bump(SyntaxKind::IsKeyword, "Expected 'is'.");
        let type_node = self.parse_type();
        self.alloc_node(
            SyntaxKind::TypePredicate,
            TextRange::new(start, self.node_end(type_node)),
            NodeData::TypePredicateNode(Box::new(TypePredicateNodeData {
                asserts_modifier: None,
                parameter_name,
                type_: Some(type_node),
            })),
            &[parameter_name, type_node],
        )
    }

    fn parse_union_type(&mut self) -> NodeId {
        let start = self.current.range.start;
        if self.current.kind == SyntaxKind::BarToken {
            self.bump();
        }
        let first = self.parse_intersection_type();
        if self.current.kind != SyntaxKind::BarToken {
            return first;
        }
        let mut types = vec![first];
        while self.current.kind == SyntaxKind::BarToken {
            self.bump();
            types.push(self.parse_intersection_type());
        }
        let end = types.last().map_or(start, |node| self.node_end(*node));
        self.alloc_node(
            SyntaxKind::UnionType,
            TextRange::new(start, end),
            NodeData::UnionTypeNode(Box::new(UnionTypeNodeData {
                types: NodeList {
                    range: TextRange::new(start, end),
                    nodes: types.clone(),
                    has_trailing_comma: false,
                },
            })),
            &types,
        )
    }

    fn parse_intersection_type(&mut self) -> NodeId {
        let start = self.current.range.start;
        if self.current.kind == SyntaxKind::AmpersandToken {
            self.bump();
        }
        let first = self.parse_type_operator_or_postfix();
        if self.current.kind != SyntaxKind::AmpersandToken {
            return first;
        }
        let mut types = vec![first];
        while self.current.kind == SyntaxKind::AmpersandToken {
            self.bump();
            types.push(self.parse_type_operator_or_postfix());
        }
        let end = types.last().map_or(start, |node| self.node_end(*node));
        self.alloc_node(
            SyntaxKind::IntersectionType,
            TextRange::new(start, end),
            NodeData::IntersectionTypeNode(Box::new(IntersectionTypeNodeData {
                types: NodeList {
                    range: TextRange::new(start, end),
                    nodes: types.clone(),
                    has_trailing_comma: false,
                },
            })),
            &types,
        )
    }

    fn parse_type_operator_or_postfix(&mut self) -> NodeId {
        if matches!(
            self.current.kind,
            SyntaxKind::KeyOfKeyword | SyntaxKind::ReadonlyKeyword | SyntaxKind::UniqueKeyword
        ) {
            let operator = self.consume();
            let type_node = self.parse_type_operator_or_postfix();
            return self.alloc_node(
                SyntaxKind::TypeOperator,
                TextRange::new(operator.range.start, self.node_end(type_node)),
                NodeData::TypeOperatorNode(Box::new(TypeOperatorNodeData {
                    operator: operator.kind,
                    type_: type_node,
                })),
                &[type_node],
            );
        }
        let mut type_node = self.parse_primary_type();
        while self.current.kind == SyntaxKind::OpenBracketToken {
            self.bump();
            if self.current.kind == SyntaxKind::CloseBracketToken {
                let end = self.consume().range.end;
                type_node = self.alloc_node(
                    SyntaxKind::ArrayType,
                    TextRange::new(self.node_start(type_node), end),
                    NodeData::ArrayTypeNode(Box::new(ArrayTypeNodeData {
                        element_type: type_node,
                    })),
                    &[type_node],
                );
            } else {
                let index_type = self.parse_type();
                let end = if self.current.kind == SyntaxKind::CloseBracketToken {
                    self.consume().range.end
                } else {
                    self.error_current("Expected ']'.");
                    self.node_end(index_type)
                };
                type_node = self.alloc_node(
                    SyntaxKind::IndexedAccessType,
                    TextRange::new(self.node_start(type_node), end),
                    NodeData::IndexedAccessTypeNode(Box::new(IndexedAccessTypeNodeData {
                        index_type,
                        object_type: type_node,
                    })),
                    &[type_node, index_type],
                );
            }
        }
        type_node
    }

    #[allow(clippy::too_many_lines)]
    fn parse_primary_type(&mut self) -> NodeId {
        let parenthesized_function =
            self.current.kind == SyntaxKind::OpenParenToken && self.is_parenthesized_arrow();
        let mapped_type = self.current.kind == SyntaxKind::OpenBraceToken && self.is_mapped_type();
        match self.current.kind {
            SyntaxKind::OpenBraceToken if mapped_type => self.parse_mapped_type(),
            SyntaxKind::OpenBraceToken => {
                let members = self.parse_class_members(true);
                let range = members.range;
                let children = members.nodes.clone();
                self.alloc_node(
                    SyntaxKind::TypeLiteral,
                    range,
                    NodeData::TypeLiteralNode(Box::new(TypeLiteralNodeData {
                        members,
                        symbol: None,
                    })),
                    &children,
                )
            }
            kind if is_keyword_type(kind) => {
                let token = self.consume();
                self.alloc_node(
                    token.kind,
                    token.range,
                    NodeData::KeywordTypeNode(Box::new(KeywordTypeNodeData)),
                    &[],
                )
            }
            SyntaxKind::ThisKeyword => {
                let token = self.consume();
                self.alloc_node(
                    SyntaxKind::ThisType,
                    token.range,
                    NodeData::ThisTypeNode(Box::new(ThisTypeNodeData)),
                    &[],
                )
            }
            SyntaxKind::InferKeyword => self.parse_infer_type(),
            SyntaxKind::TypeOfKeyword => self.parse_type_query(),
            SyntaxKind::ImportKeyword => self.parse_import_type(),
            SyntaxKind::OpenParenToken if parenthesized_function => self.parse_function_type(None),
            SyntaxKind::LessThanToken => {
                let type_parameters = self.parse_type_parameters();
                self.parse_function_type(type_parameters)
            }
            SyntaxKind::NewKeyword => self.parse_constructor_type(),
            SyntaxKind::AbstractKeyword => self.parse_abstract_constructor_type(),
            SyntaxKind::OpenParenToken => {
                let start = self.consume().range.start;
                let type_node = self.parse_type();
                let end = if self.current.kind == SyntaxKind::CloseParenToken {
                    self.consume().range.end
                } else {
                    self.error_current("Expected ')'.");
                    self.node_end(type_node)
                };
                self.alloc_node(
                    SyntaxKind::ParenthesizedType,
                    TextRange::new(start, end),
                    NodeData::ParenthesizedTypeNode(Box::new(ParenthesizedTypeNodeData {
                        type_: type_node,
                    })),
                    &[type_node],
                )
            }
            SyntaxKind::OpenBracketToken => self.parse_tuple_type(),
            SyntaxKind::TemplateHead => self.parse_template_literal_type(),
            SyntaxKind::MinusToken => self.parse_negative_literal_type(),
            SyntaxKind::StringLiteral
            | SyntaxKind::NumericLiteral
            | SyntaxKind::BigIntLiteral
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::TrueKeyword
            | SyntaxKind::FalseKeyword
            | SyntaxKind::NullKeyword => self.parse_literal_type(),
            _ => self.parse_type_reference(),
        }
    }

    fn parse_type_reference(&mut self) -> NodeId {
        let start = self.current.range.start;
        let type_name = self.parse_entity_name();
        let type_arguments = self.parse_type_arguments();
        let end = type_arguments
            .as_ref()
            .map_or_else(|| self.node_end(type_name), |arguments| arguments.range.end);
        let mut children = vec![type_name];
        extend_list_children(&mut children, type_arguments.as_ref());
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

    fn parse_function_type(&mut self, type_parameters: Option<NodeList>) -> NodeId {
        let start = type_parameters
            .as_ref()
            .map_or(self.current.range.start, |parameters| {
                parameters.range.start
            });
        let parameters = self.parse_parameter_list();
        self.expect_and_bump(SyntaxKind::EqualsGreaterThanToken, "Expected '=>'.");
        let return_type = self.parse_type();
        let mut children = Vec::new();
        extend_list_children(&mut children, type_parameters.as_ref());
        children.extend(parameters.nodes.iter().copied());
        children.push(return_type);
        self.alloc_node(
            SyntaxKind::FunctionType,
            TextRange::new(start, self.node_end(return_type)),
            NodeData::FunctionTypeNode(Box::new(FunctionTypeNodeData {
                full_signature: None,
                locals: SymbolTable,
                next_container: None,
                parameters,
                symbol: None,
                type_: Some(return_type),
                type_parameters,
                modifiers: None,
            })),
            &children,
        )
    }

    fn parse_constructor_type(&mut self) -> NodeId {
        let start = self.consume().range.start;
        self.parse_constructor_type_tail(start, None)
    }

    fn parse_abstract_constructor_type(&mut self) -> NodeId {
        let start = self.current.range.start;
        let abstract_modifier = self.consume_token_node();
        self.expect_and_bump(SyntaxKind::NewKeyword, "Expected 'new'.");
        let modifiers = Some(ModifierList {
            list: NodeList {
                range: TextRange::new(start, self.current.range.start),
                nodes: vec![abstract_modifier],
                has_trailing_comma: false,
            },
            flags: ts_ast::ModifierFlags::default(),
        });
        self.parse_constructor_type_tail(start, modifiers)
    }

    fn parse_constructor_type_tail(
        &mut self,
        start: TextPos,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameter_list();
        self.expect_and_bump(SyntaxKind::EqualsGreaterThanToken, "Expected '=>'.");
        let return_type = self.parse_type();
        let mut children = Vec::new();
        if let Some(modifiers) = &modifiers {
            children.extend(modifiers.list.nodes.iter().copied());
        }
        extend_list_children(&mut children, type_parameters.as_ref());
        children.extend(parameters.nodes.iter().copied());
        children.push(return_type);
        self.alloc_node(
            SyntaxKind::ConstructorType,
            TextRange::new(start, self.node_end(return_type)),
            NodeData::ConstructorTypeNode(Box::new(ConstructorTypeNodeData {
                full_signature: None,
                locals: SymbolTable,
                next_container: None,
                parameters,
                symbol: None,
                type_: Some(return_type),
                type_parameters,
                modifiers,
            })),
            &children,
        )
    }

    fn parse_type_query(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let expr_name = self.parse_entity_name();
        let type_arguments = self.parse_type_arguments();
        let end = type_arguments
            .as_ref()
            .map_or_else(|| self.node_end(expr_name), |arguments| arguments.range.end);
        let mut children = vec![expr_name];
        extend_list_children(&mut children, type_arguments.as_ref());
        self.alloc_node(
            SyntaxKind::TypeQuery,
            TextRange::new(start, end),
            NodeData::TypeQueryNode(Box::new(TypeQueryNodeData {
                expr_name,
                type_arguments,
            })),
            &children,
        )
    }

    fn parse_import_type(&mut self) -> NodeId {
        let start = self.consume().range.start;
        self.expect_and_bump(SyntaxKind::OpenParenToken, "Expected '('.");
        let argument = self.parse_literal_type();
        self.expect_and_bump(SyntaxKind::CloseParenToken, "Expected ')'.");
        let qualifier = if self.current.kind == SyntaxKind::DotToken {
            self.bump();
            Some(self.parse_entity_name())
        } else {
            None
        };
        let type_arguments = self.parse_type_arguments();
        let end = type_arguments.as_ref().map_or_else(
            || qualifier.map_or_else(|| self.node_end(argument), |node| self.node_end(node)),
            |arguments| arguments.range.end,
        );
        let mut children = vec![argument];
        children.extend(qualifier);
        extend_list_children(&mut children, type_arguments.as_ref());
        self.alloc_node(
            SyntaxKind::ImportType,
            TextRange::new(start, end),
            NodeData::ImportTypeNode(Box::new(ImportTypeNodeData {
                argument,
                attributes: None,
                is_type_of: false,
                qualifier,
                type_arguments,
            })),
            &children,
        )
    }

    fn parse_literal_type(&mut self) -> NodeId {
        let literal = match self.current.kind {
            SyntaxKind::StringLiteral => self.parse_string_literal(),
            SyntaxKind::NumericLiteral => self.parse_numeric_literal(),
            SyntaxKind::BigIntLiteral => self.parse_bigint_literal(),
            SyntaxKind::NoSubstitutionTemplateLiteral => self.parse_template_literal(),
            _ => self.parse_keyword_expression(),
        };
        self.alloc_node(
            SyntaxKind::LiteralType,
            self.arena.get(literal).unwrap().range,
            NodeData::LiteralTypeNode(Box::new(LiteralTypeNodeData { literal })),
            &[literal],
        )
    }

    fn parse_negative_literal_type(&mut self) -> NodeId {
        let operator = self.consume();
        let operand = if self.current.kind == SyntaxKind::BigIntLiteral {
            self.parse_bigint_literal()
        } else {
            self.parse_numeric_literal()
        };
        let literal = self.alloc_node(
            SyntaxKind::PrefixUnaryExpression,
            TextRange::new(operator.range.start, self.node_end(operand)),
            NodeData::PrefixUnaryExpression(Box::new(PrefixUnaryExpressionData {
                operand,
                operator: operator.kind,
            })),
            &[operand],
        );
        self.alloc_node(
            SyntaxKind::LiteralType,
            TextRange::new(operator.range.start, self.node_end(literal)),
            NodeData::LiteralTypeNode(Box::new(LiteralTypeNodeData { literal })),
            &[literal],
        )
    }

    fn parse_template_literal_type(&mut self) -> NodeId {
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
            let type_node = self.parse_type();
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
                SyntaxKind::TemplateLiteralTypeSpan,
                TextRange::new(self.node_start(type_node), self.node_end(literal)),
                NodeData::TemplateLiteralTypeSpan(Box::new(TemplateLiteralTypeSpanData {
                    literal,
                    type_: type_node,
                })),
                &[type_node, literal],
            ));
            if literal_token.kind == SyntaxKind::TemplateTail {
                break;
            }
        }
        let end = spans
            .last()
            .map_or(self.node_end(head), |node| self.node_end(*node));
        let mut children = vec![head];
        children.extend(spans.iter().copied());
        self.alloc_node(
            SyntaxKind::TemplateLiteralType,
            TextRange::new(start, end),
            NodeData::TemplateLiteralTypeNode(Box::new(TemplateLiteralTypeNodeData {
                head,
                template_spans: NodeList {
                    range: TextRange::new(self.node_end(head), end),
                    nodes: spans,
                    has_trailing_comma: false,
                },
            })),
            &children,
        )
    }

    fn parse_infer_type(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let name = self.parse_identifier("Expected a type parameter name.");
        let type_parameter = self.alloc_node(
            SyntaxKind::TypeParameter,
            self.arena.get(name).unwrap().range,
            NodeData::TypeParameterDeclaration(Box::new(TypeParameterDeclarationData {
                constraint: None,
                default_type: None,
                expression: None,
                symbol: None,
                modifiers: None,
                name,
            })),
            &[name],
        );
        self.alloc_node(
            SyntaxKind::InferType,
            TextRange::new(start, self.node_end(type_parameter)),
            NodeData::InferTypeNode(Box::new(InferTypeNodeData { type_parameter })),
            &[type_parameter],
        )
    }

    fn is_mapped_type(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let mut token = self.scanner.scan();
        if matches!(token.kind, SyntaxKind::PlusToken | SyntaxKind::MinusToken) {
            token = self.scanner.scan();
        }
        if token.kind == SyntaxKind::ReadonlyKeyword {
            token = self.scanner.scan();
        }
        let result = if token.kind == SyntaxKind::OpenBracketToken {
            let name = self.scanner.scan();
            let in_token = self.scanner.scan();
            name.kind == SyntaxKind::Identifier && in_token.kind == SyntaxKind::InKeyword
        } else {
            false
        };
        self.scanner.rewind(checkpoint);
        result
    }

    fn parse_mapped_type(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let readonly_token = if matches!(
            self.current.kind,
            SyntaxKind::PlusToken | SyntaxKind::MinusToken
        ) {
            let token = Some(self.consume_token_node());
            self.expect_and_bump(SyntaxKind::ReadonlyKeyword, "Expected 'readonly'.");
            token
        } else if self.current.kind == SyntaxKind::ReadonlyKeyword {
            Some(self.consume_token_node())
        } else {
            None
        };
        self.expect_and_bump(SyntaxKind::OpenBracketToken, "Expected '['.");
        let parameter_start = self.current.range.start;
        let name = self.parse_identifier("Expected a type parameter name.");
        self.expect_and_bump(SyntaxKind::InKeyword, "Expected 'in'.");
        let constraint = self.parse_type();
        let name_type = if self.current.kind == SyntaxKind::AsKeyword {
            self.bump();
            Some(self.parse_type())
        } else {
            None
        };
        self.expect_and_bump(SyntaxKind::CloseBracketToken, "Expected ']'.");
        let question_token = if matches!(
            self.current.kind,
            SyntaxKind::PlusToken | SyntaxKind::MinusToken
        ) {
            let token = Some(self.consume_token_node());
            self.expect_and_bump(SyntaxKind::QuestionToken, "Expected '?'.");
            token
        } else if self.current.kind == SyntaxKind::QuestionToken {
            Some(self.consume_token_node())
        } else {
            None
        };
        let type_node = if self.current.kind == SyntaxKind::ColonToken {
            self.bump();
            Some(self.parse_type())
        } else {
            None
        };
        self.parse_semicolon(
            type_node.map_or(self.current.range.start, |node| self.node_end(node)),
        );
        let end = if self.current.kind == SyntaxKind::CloseBraceToken {
            self.consume().range.end
        } else {
            self.error_current("Expected '}'.");
            type_node.map_or(self.current.range.start, |node| self.node_end(node))
        };
        let type_parameter = self.alloc_node(
            SyntaxKind::TypeParameter,
            TextRange::new(parameter_start, self.node_end(constraint)),
            NodeData::TypeParameterDeclaration(Box::new(TypeParameterDeclarationData {
                constraint: Some(constraint),
                default_type: None,
                expression: None,
                symbol: None,
                modifiers: None,
                name,
            })),
            &[name, constraint],
        );
        let mut children = vec![type_parameter];
        children.extend(readonly_token);
        children.extend(name_type);
        children.extend(question_token);
        children.extend(type_node);
        self.alloc_node(
            SyntaxKind::MappedType,
            TextRange::new(start, end),
            NodeData::MappedTypeNode(Box::new(MappedTypeNodeData {
                locals: SymbolTable,
                members: None,
                name_type,
                next_container: None,
                question_token,
                readonly_token,
                symbol: None,
                type_: type_node,
                type_parameter,
            })),
            &children,
        )
    }

    fn parse_tuple_type(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let mut elements = Vec::new();
        while !matches!(
            self.current.kind,
            SyntaxKind::CloseBracketToken | SyntaxKind::EndOfFile
        ) {
            if self.current.kind == SyntaxKind::DotDotDotToken {
                let rest_start = self.consume().range.start;
                let type_node = self.parse_type();
                elements.push(self.alloc_node(
                    SyntaxKind::RestType,
                    TextRange::new(rest_start, self.node_end(type_node)),
                    NodeData::RestTypeNode(Box::new(RestTypeNodeData { type_: type_node })),
                    &[type_node],
                ));
            } else {
                elements.push(self.parse_type());
            }
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
        }
        let end = if self.current.kind == SyntaxKind::CloseBracketToken {
            self.consume().range.end
        } else {
            self.error_current("Expected ']'.");
            elements.last().map_or(start, |node| self.node_end(*node))
        };
        self.alloc_node(
            SyntaxKind::TupleType,
            TextRange::new(start, end),
            NodeData::TupleTypeNode(Box::new(TupleTypeNodeData {
                elements: NodeList {
                    range: TextRange::new(start, end),
                    nodes: elements.clone(),
                    has_trailing_comma: false,
                },
            })),
            &elements,
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
            .push(parser_diagnostic(self.current.range, message));
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

fn parser_diagnostic(range: TextRange, message: &str) -> Diagnostic {
    let catalog = match message {
        "Expected an expression." => Some((1109, Vec::new())),
        "Expected a type name." | "Expected a type annotation." => Some((1110, Vec::new())),
        "Expected 'case' or 'default'." => Some((1130, Vec::new())),
        "Expected a member name." => Some((1131, Vec::new())),
        "Expected a variable name." => Some((1134, Vec::new())),
        "Expected an argument." => Some((1135, Vec::new())),
        "Expected a string literal." | "Expected a module specifier." => Some((1141, Vec::new())),
        "Expected 'catch' or 'finally'." => Some((1472, Vec::new())),
        "Decorators are not valid here." => Some((1206, Vec::new())),
        "Line break not permitted after 'throw'." => Some((1142, Vec::new())),
        "Expected a function name."
        | "Expected a class name."
        | "Expected a parameter name."
        | "Expected a binding name."
        | "Expected a type parameter name."
        | "Expected a property name."
        | "Expected an accessor name."
        | "Expected a module name."
        | "Expected a module reference."
        | "Expected an identifier after '.'."
        | "Expected an import binding."
        | "Expected an import name."
        | "Expected a local import name."
        | "Expected a namespace import name."
        | "Expected an export name."
        | "Expected an exported name."
        | "Expected a predicate parameter name." => Some((1003, Vec::new())),
        "Expected a method body." => Some((1005, vec!["{".to_owned()])),
        _ => expected_token_argument(message).map(|token| (1005, vec![token])),
    };
    let Some((code, arguments)) = catalog else {
        return Diagnostic::new(range, message);
    };
    let catalog = message_by_code(code).expect("parser diagnostic code exists");
    Diagnostic::typescript(
        range,
        code,
        parser_diagnostic_category(catalog.category()),
        catalog
            .format(&arguments)
            .expect("parser diagnostic arguments match catalog message"),
    )
}

fn expected_token_argument(message: &str) -> Option<String> {
    Some(
        message
            .strip_prefix("Expected '")?
            .strip_suffix("'.")?
            .to_owned(),
    )
}

const fn parser_diagnostic_category(category: Category) -> DiagnosticCategory {
    match category {
        Category::Warning => DiagnosticCategory::Warning,
        Category::Error => DiagnosticCategory::Error,
        Category::Suggestion => DiagnosticCategory::Suggestion,
        Category::Message => DiagnosticCategory::Message,
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

fn is_prefix_operator(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::PlusToken
            | SyntaxKind::MinusToken
            | SyntaxKind::TildeToken
            | SyntaxKind::ExclamationToken
            | SyntaxKind::PlusPlusToken
            | SyntaxKind::MinusMinusToken
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
    use ts_core::DiagnosticCategory;

    use super::{
        NODE_FLAG_AWAIT_USING, NODE_FLAG_USING, ParseResult, parse_jsdoc_comment,
        parse_jsx_source_file, parse_source_file,
    };

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
    fn parses_remaining_core_statements_and_expressions() {
        let source = r"
            switch (x) { case 1: break; default: continue label; }
            try { throw x; } catch (error) { do { error++; } while (error); } finally {}
            for (key in obj) ;
            for (value of array) ;
            namespace N { const x = 1; }
            @sealed class C {}
            const result = new Factory(1)[0]!.value as T satisfies U ? ++x : x--;
            const record = {x, ...rest, method(a) { return a; }};
        ";
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let kinds: Vec<_> = source_statements(&result)
            .iter()
            .map(|id| result.arena.get(*id).unwrap().kind)
            .collect();
        assert_eq!(kinds[0], SyntaxKind::SwitchStatement);
        assert_eq!(kinds[1], SyntaxKind::TryStatement);
        assert_eq!(kinds[2], SyntaxKind::ForInStatement);
        assert_eq!(kinds[3], SyntaxKind::ForOfStatement);
        assert_eq!(kinds[4], SyntaxKind::ModuleDeclaration);
        assert_eq!(kinds[5], SyntaxKind::ClassDeclaration);
        let (list, _) = variable_list(&result, source_statements(&result)[6]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        assert_eq!(
            result
                .arena
                .get(declaration.initializer.unwrap())
                .unwrap()
                .kind,
            SyntaxKind::ConditionalExpression
        );
        let class = result.arena.get(source_statements(&result)[5]).unwrap();
        let NodeData::ClassDeclaration(class_data) = &class.data else {
            panic!("expected decorated class");
        };
        assert_eq!(class_data.modifiers.as_ref().unwrap().list.nodes.len(), 1);
    }

    #[test]
    fn attaches_declaration_and_export_modifiers_with_parent_links() {
        let result = parse_source_file("declare function f(): void; export declare class C {}");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);

        for (index, declaration) in statements.iter().enumerate() {
            let node = result.arena.get(*declaration).unwrap();
            let modifiers = match &node.data {
                NodeData::FunctionDeclaration(data) => data.modifiers.as_ref(),
                NodeData::ClassDeclaration(data) => data.modifiers.as_ref(),
                _ => panic!("expected a declaration with modifiers"),
            }
            .unwrap();
            assert_eq!(modifiers.list.nodes.len(), index + 1);
            for modifier in &modifiers.list.nodes {
                assert_eq!(
                    result.arena.get(*modifier).unwrap().parent,
                    Some(*declaration)
                );
            }
            assert_eq!(
                node.range.start,
                result
                    .arena
                    .get(modifiers.list.nodes[0])
                    .unwrap()
                    .range
                    .start
            );
        }
    }

    #[test]
    fn parses_declaration_file_type_members() {
        let result = parse_source_file(
            r"
                interface Callable<T> {
                    readonly [key: string]: T;
                    new <U>(value: U): Callable<U>;
                    <U>(value: U): U;
                    method?<U>(value: U): U;
                }
                type Inline = {
                    (value: string): number;
                    new(): Inline;
                    [key: string]: unknown;
                    run(): void;
                };
            ",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let NodeData::InterfaceDeclaration(interface) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected interface declaration");
        };
        let interface_kinds: Vec<_> = interface
            .members
            .nodes
            .iter()
            .map(|node| result.arena.get(*node).unwrap().kind)
            .collect();
        assert_eq!(
            interface_kinds,
            [
                SyntaxKind::IndexSignature,
                SyntaxKind::ConstructSignature,
                SyntaxKind::CallSignature,
                SyntaxKind::MethodSignature,
            ]
        );

        let NodeData::TypeAliasDeclaration(alias) = &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected type alias");
        };
        let NodeData::TypeLiteralNode(literal) = &result.arena.get(alias.type_).unwrap().data
        else {
            panic!("expected type literal");
        };
        assert_eq!(literal.members.nodes.len(), 4);
    }

    #[test]
    fn parses_advanced_declaration_types_without_recovery() {
        let result = parse_source_file(
            r#"
                type Advanced<T, K extends keyof T = keyof T> =
                    T extends readonly (infer U)[]
                        ? { readonly [P in K]-?: T[P] }
                        : import("pkg").Thing<T>;
                type Predicate<T> = (this: T, value: T, ...rest: [...T[]]) => value is T;
                type Constructor<T> = abstract new (...args: any[]) => T;
                type Query = typeof ns.value;
                interface LiteralNames { "prototype": Query; 0: string; }
            "#,
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let kinds: Vec<_> = result.arena.iter().map(|(_, node)| node.kind).collect();
        for expected in [
            SyntaxKind::ConditionalType,
            SyntaxKind::TypeOperator,
            SyntaxKind::InferType,
            SyntaxKind::ArrayType,
            SyntaxKind::MappedType,
            SyntaxKind::IndexedAccessType,
            SyntaxKind::ImportType,
            SyntaxKind::FunctionType,
            SyntaxKind::TypePredicate,
            SyntaxKind::RestType,
            SyntaxKind::ConstructorType,
            SyntaxKind::TypeQuery,
        ] {
            assert!(kinds.contains(&expected), "missing {expected:?}");
        }
    }

    #[test]
    fn parses_bundled_library_declaration_forms() {
        let result = parse_source_file(
            r"
                declare global {
                    interface IterableValue {
                        get value(): string;
                        set value(next: string);
                        [Symbol.iterator](): IterableValue;
                    }
                    type Key = `${string}-${number}` | -1;
                    function consume(...[value]: [string]): void;
                }
                declare abstract class Base {
                    private constructor();
                    abstract next(): void;
                }
            ",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let kinds: Vec<_> = result.arena.iter().map(|(_, node)| node.kind).collect();
        for expected in [
            SyntaxKind::ModuleDeclaration,
            SyntaxKind::GetAccessor,
            SyntaxKind::SetAccessor,
            SyntaxKind::ComputedPropertyName,
            SyntaxKind::TemplateLiteralType,
            SyntaxKind::ArrayBindingPattern,
        ] {
            assert!(kinds.contains(&expected), "missing {expected:?}");
        }
    }

    #[test]
    fn parses_modern_async_class_resource_and_import_syntax() {
        let result = parse_source_file(
            r#"
                async function* stream(source: any) {
                    await source?.next?.();
                    yield* source?.[0]!;
                }
                class Box {
                    #value = 1;
                    *values() { yield this.#value; }
                    async read() { return await this?.#value; }
                    static { this.#value++; }
                }
                for await (const item of items) { item; }
                using resource = acquire();
                await using asyncResource = acquire();
                const methods = {
                    async run() { await resource?.close?.(); },
                    *iterate() { yield 1; }
                };
                import data from "pkg" with { type: "json" };
                export { data } from "pkg" with { type: "json" };
            "#,
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let kinds: Vec<_> = result.arena.iter().map(|(_, node)| node.kind).collect();
        for expected in [
            SyntaxKind::AwaitExpression,
            SyntaxKind::YieldExpression,
            SyntaxKind::PrivateIdentifier,
            SyntaxKind::ClassStaticBlockDeclaration,
            SyntaxKind::ForOfStatement,
            SyntaxKind::ImportAttributes,
        ] {
            assert!(kinds.contains(&expected), "missing {expected:?}");
        }
        let declaration_flags: Vec<_> = result
            .arena
            .iter()
            .filter_map(|(_, node)| {
                (node.kind == SyntaxKind::VariableDeclarationList).then_some(node.flags)
            })
            .collect();
        assert!(declaration_flags.contains(&NODE_FLAG_USING));
        assert!(declaration_flags.contains(&NODE_FLAG_AWAIT_USING));
    }

    #[test]
    fn parses_namespace_imports_import_equals_exports_and_type_assertions() {
        let result = parse_source_file(
            r#"
                import * as ns from "pkg";
                import alias = require("pkg");
                import nested = ns.value;
                export const value = <number>input;
                export function f(): void;
                export class C {}
                export interface I {}
            "#,
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let NodeData::ImportDeclaration(import) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected import declaration");
        };
        let NodeData::ImportClause(clause) = &result
            .arena
            .get(import.import_clause.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected import clause");
        };
        assert_eq!(
            result
                .arena
                .get(clause.named_bindings.unwrap())
                .unwrap()
                .kind,
            SyntaxKind::NamespaceImport
        );
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::ImportEqualsDeclaration
        );
        assert_eq!(
            result.arena.get(statements[2]).unwrap().kind,
            SyntaxKind::ImportEqualsDeclaration
        );
        let (list, _) = variable_list(&result, statements[3]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        assert_eq!(
            result
                .arena
                .get(declaration.initializer.unwrap())
                .unwrap()
                .kind,
            SyntaxKind::TypeAssertionExpression
        );
        for statement in &statements[3..] {
            let has_export = match &result.arena.get(*statement).unwrap().data {
                NodeData::VariableStatement(data) => data.modifiers.is_some(),
                NodeData::FunctionDeclaration(data) => data.modifiers.is_some(),
                NodeData::ClassDeclaration(data) => data.modifiers.is_some(),
                NodeData::InterfaceDeclaration(data) => data.modifiers.is_some(),
                _ => false,
            };
            assert!(has_export);
        }
    }

    #[test]
    fn parses_jsx_elements_attributes_children_and_expressions() {
        let result = parse_jsx_source_file(
            "const view = <div id=\"x\">hello {name}<span value={1} /></div>;",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let (list, _) = variable_list(&result, source_statements(&result)[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected declaration");
        };
        let jsx = declaration.initializer.unwrap();
        let NodeData::JsxElement(element) = &result.arena.get(jsx).unwrap().data else {
            panic!("expected JSX element");
        };
        assert_eq!(element.children.nodes.len(), 3);
        assert_eq!(
            result.arena.get(element.children.nodes[0]).unwrap().kind,
            SyntaxKind::JsxText
        );
        assert_eq!(
            result.arena.get(element.children.nodes[1]).unwrap().kind,
            SyntaxKind::JsxExpression
        );
        assert_eq!(
            result.arena.get(element.children.nodes[2]).unwrap().kind,
            SyntaxKind::JsxSelfClosingElement
        );
    }

    #[test]
    fn parses_jsdoc_text_and_tag_names() {
        let result = parse_jsdoc_comment("/** Summary\n * @custom value\n */");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let NodeData::JsDoc(jsdoc) = &result.arena.get(result.jsdoc).unwrap().data else {
            panic!("expected JSDoc root");
        };
        assert!(!jsdoc.comment.nodes.is_empty());
        assert_eq!(jsdoc.tags.as_ref().unwrap().nodes.len(), 1);
        assert_eq!(
            result
                .arena
                .get(jsdoc.tags.as_ref().unwrap().nodes[0])
                .unwrap()
                .parent,
            Some(result.jsdoc)
        );
    }

    #[test]
    fn interface_members_preserve_progress() {
        let result = parse_source_file(
            "interface Indexed { [key: string]: unknown; optional?: string; } const done = 1;",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert!(result.arena.len() < 100, "unexpected AST growth");
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::VariableStatement
        );
    }

    #[test]
    fn unsupported_case_statements_always_make_progress() {
        let result = parse_source_file(
            "switch (x) { case 1: (function() { return x }); break; } const done = 1;",
        );
        assert!(!result.diagnostics.is_empty());
        assert!(result.arena.len() < 100, "unexpected AST growth");
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::VariableStatement
        );
    }

    #[test]
    fn parses_complex_binding_patterns() {
        let result = parse_source_file(
            "function f([value = 1, { nested }, [tail]]: unknown): void; const done = 1;",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert!(result.arena.len() < 200, "unexpected AST growth");
        assert!(source_statements(&result).iter().any(|statement| {
            result.arena.get(*statement).unwrap().kind == SyntaxKind::VariableStatement
        }));
    }

    #[test]
    fn recovers_with_missing_names_expressions_and_braces() {
        let result = parse_source_file("let : Missing = ;\n{ const y = 1 + ;");
        assert!(result.diagnostics.len() >= 3, "{:?}", result.diagnostics);
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1134))
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1109))
        );
        assert!(result.diagnostics.iter().any(
            |diagnostic| diagnostic.code == Some(1005) && diagnostic.message == "'}' expected."
        ));
        let missing_name = result
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code == Some(1134))
            .unwrap();
        assert_eq!(missing_name.range.start.get(), 4);
        assert_eq!(missing_name.category, DiagnosticCategory::Error);
        assert_eq!(source_statements(&result).len(), 2);
    }

    #[test]
    fn reports_catalog_codes_for_expected_parser_tokens() {
        let result = parse_source_file("function () { const value = ;");
        for (code, message) in [
            (1003, "Identifier expected."),
            (1109, "Expression expected."),
            (1005, "'}' expected."),
        ] {
            let diagnostic = result
                .diagnostics
                .iter()
                .find(|diagnostic| diagnostic.code == Some(code))
                .unwrap_or_else(|| panic!("missing TS{code}: {:?}", result.diagnostics));
            assert_eq!(diagnostic.message, message);
            assert_eq!(diagnostic.category, DiagnosticCategory::Error);
        }
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
