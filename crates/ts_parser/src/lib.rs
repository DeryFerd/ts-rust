//! TypeScript parser.

use ts_ast::{
    ArrayLiteralExpressionData, ArrayTypeNodeData, ArrowFunctionData, AsExpressionData,
    AwaitExpressionData, BigIntLiteralData, BinaryExpressionData, BindingElementData,
    BindingPatternData, BlockData, BreakStatementData, CallExpressionData,
    CallSignatureDeclarationData, CaseBlockData, CaseOrDefaultClauseData, CatchClauseData,
    ClassDeclarationData, ClassExpressionData, ClassStaticBlockDeclarationData,
    ComputedPropertyNameData, ConditionalExpressionData, ConditionalTypeNodeData,
    ConstructSignatureDeclarationData, ConstructorTypeNodeData, ContinueStatementData,
    DebuggerStatementData, DecoratorData, DeleteExpressionData, DoStatementData,
    ElementAccessExpressionData, EmptyStatementData, EnumDeclarationData, EnumMemberData,
    ExportAssignmentData, ExportDeclarationData, ExportSpecifierData, ExpressionStatementData,
    ExpressionWithTypeArgumentsData, ExternalModuleReferenceData, ForInOrOfStatementData,
    ForStatementData, FunctionDeclarationData, FunctionExpressionData, FunctionTypeNodeData,
    GetAccessorDeclarationData, HeritageClauseData, IdentifierData, IfStatementData,
    ImportAttributeData, ImportAttributesData, ImportClauseData, ImportDeclarationData,
    ImportEqualsDeclarationData, ImportSpecifierData, ImportTypeNodeData,
    IndexSignatureDeclarationData, IndexedAccessTypeNodeData, InferTypeNodeData,
    InterfaceDeclarationData, IntersectionTypeNodeData, JsDocData, JsDocTextData,
    JsDocUnknownTagData, JsxAttributeData, JsxAttributesData, JsxClosingElementData,
    JsxClosingFragmentData, JsxElementData, JsxExpressionData, JsxFragmentData,
    JsxOpeningElementData, JsxOpeningFragmentData, JsxSelfClosingElementData,
    JsxSpreadAttributeData, JsxTextData, KeywordExpressionData, KeywordTypeNodeData,
    LabeledStatementData, LiteralTypeNodeData, MappedTypeNodeData, MethodDeclarationData,
    MethodSignatureDeclarationData, ModifierList, ModuleBlockData, ModuleDeclarationData,
    NamedExportsData, NamedImportsData, NamespaceExportDeclarationData, NamespaceImportData,
    NewExpressionData, NoSubstitutionTemplateLiteralData, Node, NodeArena, NodeData, NodeFlags,
    NodeId, NodeList, NonNullExpressionData, NumericLiteralData, ObjectLiteralExpressionData,
    OmittedExpressionData, ParameterDeclarationData, ParenthesizedExpressionData,
    ParenthesizedTypeNodeData, PostfixUnaryExpressionData, PrefixUnaryExpressionData,
    PrivateIdentifierData, PropertyAccessExpressionData, PropertyAssignmentData,
    PropertyDeclarationData, QualifiedNameData, RegularExpressionLiteralData, RestTypeNodeData,
    ReturnStatementData, SatisfiesExpressionData, SetAccessorDeclarationData,
    ShorthandPropertyAssignmentData, SourceFileData, SpreadAssignmentData, SpreadElementData,
    StringLiteralData, SwitchStatementData, SymbolTable, SyntaxKind, TemplateExpressionData,
    TemplateHeadData, TemplateLiteralTypeNodeData, TemplateLiteralTypeSpanData, TemplateMiddleData,
    TemplateSpanData, TemplateTailData, ThisTypeNodeData, ThrowStatementData, TokenData,
    TokenFlags, TryStatementData, TupleTypeNodeData, TypeAliasDeclarationData, TypeAssertionData,
    TypeLiteralNodeData, TypeOfExpressionData, TypeOperatorNodeData, TypeParameterDeclarationData,
    TypePredicateNodeData, TypeQueryNodeData, TypeReferenceNodeData, UnionTypeNodeData,
    VariableDeclarationData, VariableDeclarationListData, VariableStatementData,
    WhileStatementData, WithStatementData, YieldExpressionData,
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
    pub amd_dependencies: Vec<AmdDependency>,
    pub amd_module_name: Option<String>,
    pub amd_module_names: Vec<AmdModuleName>,
}

/// One leading `amd-dependency` triple-slash directive.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AmdDependency {
    pub path: String,
    pub name: Option<String>,
    pub range: TextRange,
}

/// One leading `amd-module` triple-slash directive.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AmdModuleName {
    pub name: String,
    pub range: TextRange,
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

fn parse_amd_pragmas(source: &str) -> (Vec<AmdDependency>, Vec<AmdModuleName>, Vec<Diagnostic>) {
    let mut dependencies = Vec::new();
    let mut module_names = Vec::new();
    let mut diagnostics = Vec::new();
    for range in leading_line_comment_ranges(source) {
        let start = usize::try_from(range.start.get()).unwrap_or(usize::MAX);
        let end = usize::try_from(range.end.get()).unwrap_or(usize::MAX);
        let Some(comment) = source.get(start..end) else {
            continue;
        };
        let Some(directive) = comment.strip_prefix("///").map(str::trim_start) else {
            continue;
        };
        if let Some(attributes) = pragma_attributes(directive, "amd-dependency") {
            if let Some(path) = pragma_attribute(&attributes, "path") {
                dependencies.push(AmdDependency {
                    path: path.to_owned(),
                    name: pragma_attribute(&attributes, "name").map(str::to_owned),
                    range,
                });
            }
        } else if let Some(attributes) = pragma_attributes(directive, "amd-module")
            && let Some(name) = pragma_attribute(&attributes, "name")
        {
            if !module_names.is_empty() {
                diagnostics.push(diagnostic_with_code(range, 2458));
            }
            module_names.push(AmdModuleName {
                name: name.to_owned(),
                range,
            });
        }
    }
    (dependencies, module_names, diagnostics)
}

fn leading_line_comment_ranges(source: &str) -> Vec<TextRange> {
    let bytes = source.as_bytes();
    let mut ranges = Vec::new();
    let mut position = if bytes.starts_with(&[0xef, 0xbb, 0xbf]) {
        3
    } else {
        0
    };
    while position < bytes.len() {
        while bytes.get(position).is_some_and(u8::is_ascii_whitespace) {
            position += 1;
        }
        if bytes.get(position..position.saturating_add(2)) == Some(b"//") {
            let start = position;
            position += 2;
            while bytes
                .get(position)
                .is_some_and(|byte| !matches!(byte, b'\r' | b'\n'))
            {
                position += 1;
            }
            ranges.push(text_range(start, position));
            continue;
        }
        if bytes.get(position..position.saturating_add(2)) == Some(b"/*") {
            position += 2;
            while position < bytes.len()
                && bytes.get(position..position.saturating_add(2)) != Some(b"*/")
            {
                position += 1;
            }
            position = position.saturating_add(2).min(bytes.len());
            continue;
        }
        break;
    }
    ranges
}

fn pragma_attributes<'a>(directive: &'a str, name: &str) -> Option<Vec<(&'a str, &'a str)>> {
    let body = directive.strip_prefix('<')?;
    let body = body.strip_prefix(name)?;
    if !body.as_bytes().first().is_some_and(u8::is_ascii_whitespace) {
        return None;
    }
    let body = body.trim_end().strip_suffix("/>")?;
    parse_pragma_attributes(body)
}

fn parse_pragma_attributes(mut text: &str) -> Option<Vec<(&str, &str)>> {
    let mut attributes = Vec::new();
    loop {
        text = text.trim_start();
        if text.is_empty() {
            return Some(attributes);
        }
        let name_end = text
            .find(|character: char| {
                !(character.is_ascii_alphanumeric() || matches!(character, '_' | '-'))
            })
            .unwrap_or(text.len());
        if name_end == 0 {
            return None;
        }
        let name = &text[..name_end];
        text = text[name_end..].trim_start();
        text = text.strip_prefix('=')?.trim_start();
        let quote = text.chars().next()?;
        if !matches!(quote, '\'' | '"') {
            return None;
        }
        text = &text[quote.len_utf8()..];
        let value_end = text.find(quote)?;
        attributes.push((name, &text[..value_end]));
        text = &text[value_end + quote.len_utf8()..];
    }
}

fn pragma_attribute<'a>(attributes: &[(&'a str, &'a str)], name: &str) -> Option<&'a str> {
    attributes
        .iter()
        .find_map(|(attribute, value)| (*attribute == name).then_some(*value))
}

fn text_range(start: usize, end: usize) -> TextRange {
    TextRange::new(
        TextPos::new(u32::try_from(start).unwrap_or(u32::MAX)),
        TextPos::new(u32::try_from(end).unwrap_or(u32::MAX)),
    )
}

fn diagnostic_with_code(range: TextRange, code: u32) -> Diagnostic {
    let message = message_by_code(code).expect("parser diagnostic code exists");
    Diagnostic::typescript(
        range,
        code,
        parser_diagnostic_category(message.category()),
        message
            .format(&[])
            .expect("parser diagnostic arguments match catalog message"),
    )
}

/// Parse the text and tag names of a standalone `/** ... */` comment.
#[must_use]
pub fn parse_jsdoc_comment(source: &str) -> JsDocParseResult {
    let mut scanner = Scanner::new(source);
    scanner.reset_pos(if source.starts_with("/**") { 3 } else { 0 });
    scanner.set_skip_jsdoc_leading_asterisks(true);
    let mut arena = NodeArena::new();
    arena.set_source_text(source);
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
    invalid_token_recovery_ranges: Vec<TextRange>,
    amd_dependencies: Vec<AmdDependency>,
    amd_module_names: Vec<AmdModuleName>,
    disallow_in: bool,
}

impl<'a> Parser<'a> {
    fn new(source: &'a str) -> Self {
        Self::new_with_variant(source, LanguageVariant::Standard)
    }

    fn new_with_variant(source: &'a str, variant: LanguageVariant) -> Self {
        let (amd_dependencies, amd_module_names, diagnostics) = parse_amd_pragmas(source);
        let mut scanner = Scanner::new(source);
        scanner.set_language_variant(variant);
        let current = scanner.scan();
        let mut arena = NodeArena::new();
        arena.set_source_text(source);
        Self {
            scanner,
            current,
            language_variant: variant,
            arena,
            diagnostics,
            invalid_token_recovery_ranges: Vec::new(),
            amd_dependencies,
            amd_module_names,
            disallow_in: false,
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
        for diagnostic in self.scanner.diagnostics().iter().cloned() {
            if diagnostic.code == Some(1127)
                && self.invalid_token_recovery_ranges.iter().any(|range| {
                    range.start <= diagnostic.range.start && diagnostic.range.end <= range.end
                })
            {
                continue;
            }
            self.diagnostics.push(diagnostic);
        }
        self.diagnostics.extend(
            self.invalid_token_recovery_ranges
                .iter()
                .copied()
                .map(|range| diagnostic_with_code(range, 1127)),
        );
        ParseResult {
            arena: self.arena,
            source_file,
            diagnostics: self.diagnostics,
            amd_dependencies: self.amd_dependencies,
            amd_module_name: self
                .amd_module_names
                .last()
                .map(|directive| directive.name.clone()),
            amd_module_names: self.amd_module_names,
        }
    }

    fn parse_statement_list(&mut self, terminator: SyntaxKind) -> NodeList {
        let start = self.current.full_start;
        let mut statements = Vec::new();
        while self.current.kind != terminator && self.current.kind != SyntaxKind::EndOfFile {
            if self.current.kind == SyntaxKind::Unknown
                || (self.current.kind == SyntaxKind::AtToken
                    && self.next_token_kind() == SyntaxKind::Unknown)
            {
                if self.current.kind == SyntaxKind::AtToken {
                    self.bump();
                }
                self.error_code_at(self.current.range, 1128, std::iter::empty::<String>());
                self.recover_invalid_token_statement(terminator);
                continue;
            }
            if terminator == SyntaxKind::EndOfFile
                && self.current.kind == SyntaxKind::CloseBraceToken
            {
                self.error_code_at(self.current.range, 1128, std::iter::empty::<String>());
                self.bump();
                continue;
            }
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

    fn recover_invalid_token_statement(&mut self, terminator: SyntaxKind) {
        let start = self.current.range.start;
        let mut end = self.current.range.end;
        let mut first = true;
        while self.current.kind != SyntaxKind::EndOfFile
            && self.current.kind != terminator
            && self.current.kind != SyntaxKind::CloseBraceToken
        {
            if !first
                && self
                    .current
                    .flags
                    .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
            {
                break;
            }
            first = false;
            let at_semicolon = self.current.kind == SyntaxKind::SemicolonToken;
            if !at_semicolon {
                end = self.current.range.end;
            }
            self.bump();
            if at_semicolon {
                break;
            }
        }
        self.invalid_token_recovery_ranges
            .push(TextRange::new(start, end));
    }

    fn parse_statement(&mut self) -> NodeId {
        let is_labeled_statement = self.current.kind == SyntaxKind::Identifier
            && self.next_token_kind() == SyntaxKind::ColonToken;
        let is_const_enum = self.current.kind == SyntaxKind::ConstKeyword
            && self.next_token_kind() == SyntaxKind::EnumKeyword;
        let is_module_declaration = match self.current.kind {
            SyntaxKind::GlobalKeyword => self.next_token_kind() == SyntaxKind::OpenBraceToken,
            SyntaxKind::NamespaceKeyword => self.next_token_kind() == SyntaxKind::Identifier,
            SyntaxKind::ModuleKeyword => matches!(
                self.next_token_kind(),
                SyntaxKind::Identifier | SyntaxKind::StringLiteral
            ),
            _ => false,
        };
        let abstract_starts_expression = self.current.kind == SyntaxKind::AbstractKeyword
            && self.next_token_preceded_by_line_break();
        let async_starts_function = self.current.kind == SyntaxKind::AsyncKeyword
            && !self.next_token_preceded_by_line_break()
            && self.next_token_kind() == SyntaxKind::FunctionKeyword;
        match self.current.kind {
            SyntaxKind::OpenBraceToken => self.parse_block(),
            SyntaxKind::ConstKeyword if is_const_enum => self.parse_const_enum_declaration(),
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
            SyntaxKind::DebuggerKeyword => self.parse_debugger_statement(),
            SyntaxKind::WithKeyword => self.parse_with_statement(),
            SyntaxKind::NamespaceKeyword
            | SyntaxKind::ModuleKeyword
            | SyntaxKind::GlobalKeyword
                if is_module_declaration =>
            {
                self.parse_module_declaration()
            }
            SyntaxKind::AtToken => self.parse_decorated_statement(),
            SyntaxKind::AbstractKeyword if abstract_starts_expression => {
                self.parse_expression_statement()
            }
            SyntaxKind::AsyncKeyword if !async_starts_function => self.parse_expression_statement(),
            SyntaxKind::DeclareKeyword | SyntaxKind::AbstractKeyword | SyntaxKind::AsyncKeyword => {
                self.parse_modified_statement()
            }
            SyntaxKind::ImportKeyword => self.parse_import_declaration(),
            SyntaxKind::ExportKeyword => self.parse_export_declaration(),
            SyntaxKind::SemicolonToken => self.parse_empty_statement(),
            SyntaxKind::Identifier if is_labeled_statement => self.parse_labeled_statement(),
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

    fn parse_debugger_statement(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let end = self.parse_semicolon(self.current.full_start);
        self.alloc_node(
            SyntaxKind::DebuggerStatement,
            TextRange::new(start, end),
            NodeData::DebuggerStatement(Box::new(DebuggerStatementData { flow_node: None })),
            &[],
        )
    }

    fn parse_with_statement(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let expression = self.parse_parenthesized_condition();
        let statement = self.parse_statement();
        self.alloc_node(
            SyntaxKind::WithStatement,
            TextRange::new(start, self.node_end(statement)),
            NodeData::WithStatement(Box::new(WithStatementData {
                expression,
                flow_node: None,
                statement,
                facts: 0,
            })),
            &[expression, statement],
        )
    }

    fn parse_labeled_statement(&mut self) -> NodeId {
        let start = self.current.range.start;
        let label = self.parse_identifier("Expected a label.");
        self.expect_and_bump(SyntaxKind::ColonToken, "Expected ':'.");
        let statement = self.parse_statement();
        self.alloc_node(
            SyntaxKind::LabeledStatement,
            TextRange::new(start, self.node_end(statement)),
            NodeData::LabeledStatement(Box::new(LabeledStatementData {
                flow_node: None,
                label,
                statement,
            })),
            &[label, statement],
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

    fn parse_const_enum_declaration(&mut self) -> NodeId {
        let start = self.current.range.start;
        let const_modifier = self.consume_token_node();
        let declaration = self.parse_enum_declaration();
        self.attach_modifiers(declaration, vec![const_modifier], start);
        declaration
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

    fn next_token_preceded_by_line_break(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let has_line_break = self
            .scanner
            .scan()
            .flags
            .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK);
        self.scanner.rewind(checkpoint);
        has_line_break
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
        let exclamation_token = if self.current.kind == SyntaxKind::ExclamationToken {
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
        let mut shift_recovery = false;
        let mut initializer = if self.current.kind == SyntaxKind::EqualsToken {
            self.bump();
            shift_recovery = self.current.kind == SyntaxKind::LessThanLessThanToken;
            Some(self.parse_binary_expression(2))
        } else {
            None
        };
        if shift_recovery
            && self.current.kind == SyntaxKind::EqualsGreaterThanToken
            && let Some(left) = initializer
        {
            self.error_current("Expected ','.");
            let arrow = self.consume();
            if self.current.kind == SyntaxKind::Identifier {
                let right = self.alloc_node(
                    SyntaxKind::Identifier,
                    self.current.range,
                    NodeData::Identifier(Box::new(IdentifierData {
                        flow_node: None,
                        text: token_value(&self.current),
                    })),
                    &[],
                );
                let comma = self.alloc_node(
                    SyntaxKind::CommaToken,
                    arrow.range,
                    NodeData::Token(Box::new(TokenData)),
                    &[],
                );
                initializer = Some(self.alloc_node(
                    SyntaxKind::BinaryExpression,
                    TextRange::new(self.node_start(left), self.node_end(right)),
                    NodeData::BinaryExpression(Box::new(BinaryExpressionData {
                        left,
                        operator_token: comma,
                        right,
                        symbol: None,
                        type_: None,
                        facts: 0,
                        modifiers: None,
                    })),
                    &[left, comma, right],
                ));
            }
        }
        let end = initializer
            .or(type_node)
            .or(exclamation_token)
            .and_then(|id| self.arena.get(id))
            .map_or_else(|| self.node_end(name), |node| node.range.end);
        let mut children = vec![name];
        children.extend(exclamation_token);
        children.extend(type_node);
        children.extend(initializer);
        self.alloc_node(
            SyntaxKind::VariableDeclaration,
            TextRange::new(start, end),
            NodeData::VariableDeclaration(Box::new(VariableDeclarationData {
                exclamation_token,
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
        let mut modifier_nodes = Vec::new();
        while self.current_token_is_parameter_modifier() {
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
        let mut children = modifier_nodes;
        children.extend(dot_dot_dot_token);
        children.push(name);
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
                modifiers,
                name,
            })),
            &children,
        )
    }

    fn current_token_is_parameter_modifier(&mut self) -> bool {
        if !matches!(
            self.current.kind,
            SyntaxKind::OverrideKeyword
                | SyntaxKind::PrivateKeyword
                | SyntaxKind::ProtectedKeyword
                | SyntaxKind::PublicKeyword
                | SyntaxKind::ReadonlyKeyword
        ) {
            return false;
        }
        let next = self.next_token_kind();
        matches!(
            next,
            SyntaxKind::DotDotDotToken
                | SyntaxKind::Identifier
                | SyntaxKind::OpenBraceToken
                | SyntaxKind::OpenBracketToken
                | SyntaxKind::OverrideKeyword
                | SyntaxKind::PrivateKeyword
                | SyntaxKind::ProtectedKeyword
                | SyntaxKind::PublicKeyword
                | SyntaxKind::ReadonlyKeyword
        ) || next.is_keyword()
    }

    fn parse_array_binding_pattern(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let mut elements = Vec::new();
        let mut has_trailing_comma = false;
        while !matches!(
            self.current.kind,
            SyntaxKind::CloseBracketToken | SyntaxKind::EndOfFile
        ) {
            if self.current.kind == SyntaxKind::CommaToken {
                let position = self.current.range.start;
                elements.push(self.alloc_node(
                    SyntaxKind::OmittedExpression,
                    TextRange::new(position, position),
                    NodeData::OmittedExpression(Box::new(OmittedExpressionData)),
                    &[],
                ));
                self.bump();
                has_trailing_comma = self.current.kind == SyntaxKind::CloseBracketToken;
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
                has_trailing_comma = self.current.kind == SyntaxKind::CloseBracketToken;
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
                    has_trailing_comma,
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
        let name = if self.current.kind == SyntaxKind::Identifier || self.current.kind.is_keyword()
        {
            Some(self.parse_identifier_name("Expected a class name."))
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

    fn parse_class_expression(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let name = if self.current.kind != SyntaxKind::ExtendsKeyword
            && (self.current.kind == SyntaxKind::Identifier || self.current.kind.is_keyword())
        {
            Some(self.parse_identifier_name("Expected a class name."))
        } else {
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
            SyntaxKind::ClassExpression,
            TextRange::new(start, end),
            NodeData::ClassExpression(Box::new(ClassExpressionData {
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
        if is_keyword_type(self.current.kind) {
            let name = token_value(&self.current);
            self.error_code_at(self.current.range, 2427, [name]);
        }
        let name = self.parse_identifier_name("Expected an interface name.");
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
                let expression = self.parse_heritage_expression();
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

    fn parse_heritage_expression(&mut self) -> NodeId {
        let mut expression = self.parse_entity_name();
        while self.current.kind == SyntaxKind::OpenParenToken {
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
        expression
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
        let mut recovered_at_statement = false;
        while self.current.kind != SyntaxKind::CloseBraceToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            if !signature_only && self.current.kind == SyntaxKind::VarKeyword {
                self.error_code_at(self.current.range, 1068, std::iter::empty::<String>());
                recovered_at_statement = true;
                break;
            }
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
        let end = if recovered_at_statement {
            self.current.full_start
        } else if self.current.kind == SyntaxKind::CloseBraceToken {
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

    #[allow(clippy::too_many_lines)]
    fn parse_class_member(&mut self, signature_only: bool) -> NodeId {
        let start = self.current.range.start;
        if self.current.kind == SyntaxKind::StaticKeyword && self.next_token_is_open_brace() {
            return self.parse_class_static_block(start);
        }
        let mut modifier_nodes = Vec::new();
        while self.current.kind.is_modifier() && !self.current_modifier_is_member_name() {
            modifier_nodes.push(self.consume_token_node());
        }
        self.recover_invalid_class_var_modifier(&mut modifier_nodes);
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
            return self.parse_class_accessor(start, modifiers, modifier_nodes, false);
        }
        let asterisk_token = if self.current.kind == SyntaxKind::AsteriskToken {
            Some(self.consume_token_node())
        } else {
            None
        };
        let name = self.parse_property_name("Expected a member name.");
        let type_parameters = self.parse_type_parameters();
        if type_parameters.is_some() || self.current.kind == SyntaxKind::OpenParenToken {
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
            extend_list_children(&mut children, type_parameters.as_ref());
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
                    type_parameters,
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

    fn recover_invalid_class_var_modifier(&mut self, modifier_nodes: &mut Vec<NodeId>) {
        if self.current.kind != SyntaxKind::VarKeyword || modifier_nodes.is_empty() {
            return;
        }
        self.error_code_at(self.current.range, 1440, std::iter::empty::<String>());
        self.bump();
        while self.current.kind.is_modifier() && !self.current_modifier_is_member_name() {
            modifier_nodes.push(self.consume_token_node());
        }
    }

    fn current_modifier_is_member_name(&mut self) -> bool {
        if !self.current.kind.is_modifier() {
            return false;
        }
        if self.next_token_preceded_by_line_break() {
            return true;
        }
        matches!(
            self.next_token_kind(),
            SyntaxKind::LessThanToken
                | SyntaxKind::OpenParenToken
                | SyntaxKind::QuestionToken
                | SyntaxKind::ColonToken
                | SyntaxKind::EqualsToken
                | SyntaxKind::SemicolonToken
                | SyntaxKind::CloseBraceToken
                | SyntaxKind::EndOfFile
        )
    }

    fn parse_class_accessor(
        &mut self,
        start: TextPos,
        modifiers: Option<ModifierList>,
        modifier_nodes: Vec<NodeId>,
        body_required: bool,
    ) -> NodeId {
        let kind = self.consume().kind;
        let name = self.parse_property_name("Expected an accessor name.");
        let parameters = self.parse_parameter_list();
        let return_type = self.parse_optional_type_annotation();
        let body = if self.current.kind == SyntaxKind::OpenBraceToken {
            Some(self.parse_block())
        } else {
            if body_required {
                self.error_current("Expected '{'.");
            } else {
                self.parse_semicolon(
                    return_type.map_or(parameters.range.end, |node| self.node_end(node)),
                );
            }
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
        while self.current.kind == SyntaxKind::ReadonlyKeyword
            && !self.current_modifier_is_member_name()
        {
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
        let body = if self.current.kind == SyntaxKind::OpenBraceToken {
            let body = self.parse_block();
            self.error_code_at(
                self.arena.get(body).unwrap().range,
                1183,
                std::iter::empty::<String>(),
            );
            Some(body)
        } else {
            self.parse_semicolon(fallback);
            None
        };
        let end = body.map_or(fallback, |node| self.node_end(node));
        let mut children = vec![name];
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
            let member_name = self.parse_enum_member_name();
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

    fn parse_enum_member_name(&mut self) -> NodeId {
        if matches!(
            self.current.kind,
            SyntaxKind::StringLiteral | SyntaxKind::NumericLiteral | SyntaxKind::OpenBracketToken
        ) {
            self.parse_property_name("Expected an enum member name.")
        } else {
            self.parse_identifier_name("Expected an enum member name.")
        }
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
            let previous_disallow_in = self.disallow_in;
            self.disallow_in = true;
            let expression = self.parse_binary_expression(0);
            self.disallow_in = previous_disallow_in;
            Some(expression)
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
        let allows_dotted_name = keyword.kind != SyntaxKind::GlobalKeyword
            && self.current.kind != SyntaxKind::StringLiteral;
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
        let body = if allows_dotted_name && self.current.kind == SyntaxKind::DotToken {
            self.bump();
            Some(self.parse_nested_module_declaration(keyword.kind))
        } else {
            self.parse_module_block()
        };
        self.alloc_module_declaration(keyword.range.start, keyword.kind, name, body)
    }

    fn parse_nested_module_declaration(&mut self, keyword: SyntaxKind) -> NodeId {
        let start = self.current.range.start;
        let name = self.parse_identifier("Expected a module name.");
        let body = if self.current.kind == SyntaxKind::DotToken {
            self.bump();
            Some(self.parse_nested_module_declaration(keyword))
        } else {
            self.parse_module_block()
        };
        self.alloc_module_declaration(start, keyword, name, body)
    }

    fn parse_module_block(&mut self) -> Option<NodeId> {
        if self.current.kind == SyntaxKind::OpenBraceToken {
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
        }
    }

    fn alloc_module_declaration(
        &mut self,
        start: TextPos,
        keyword: SyntaxKind,
        name: NodeId,
        body: Option<NodeId>,
    ) -> NodeId {
        let end = body.map_or_else(|| self.node_end(name), |id| self.node_end(id));
        let mut children = vec![name];
        children.extend(body);
        self.alloc_node(
            SyntaxKind::ModuleDeclaration,
            TextRange::new(start, end),
            NodeData::ModuleDeclaration(Box::new(ModuleDeclarationData {
                asterisk_token: None,
                body,
                end_flow_node: None,
                flow_node: None,
                keyword,
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
                NodeData::FunctionExpression(data) => data.modifiers.clone(),
                NodeData::InterfaceDeclaration(data) => data.modifiers.clone(),
                NodeData::TypeAliasDeclaration(data) => data.modifiers.clone(),
                NodeData::EnumDeclaration(data) => data.modifiers.clone(),
                NodeData::ImportEqualsDeclaration(data) => data.modifiers.clone(),
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
                NodeData::FunctionExpression(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::InterfaceDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::TypeAliasDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::EnumDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::ImportEqualsDeclaration(data) => {
                    data.modifiers = Some(modifiers.clone());
                }
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
        let name = if is_contextual_keyword(self.current.kind) {
            self.parse_identifier_name("Expected a namespace import name.")
        } else {
            self.parse_identifier("Expected a namespace import name.")
        };
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
        let mut entity = if self.current.kind == SyntaxKind::UndefinedKeyword {
            self.parse_identifier_name("Expected a module reference.")
        } else {
            self.parse_identifier("Expected a module reference.")
        };
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
            let first = self.parse_module_export_name("Expected an import name.");
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
                | SyntaxKind::ImportKeyword
                | SyntaxKind::DeclareKeyword
                | SyntaxKind::AbstractKeyword
                | SyntaxKind::AsyncKeyword
        ) {
            let declaration = self.parse_statement();
            self.attach_modifiers(declaration, vec![export_modifier], start);
            return declaration;
        }
        if self.current.kind == SyntaxKind::EqualsToken {
            self.bump();
            let expression = self.parse_binary_expression(0);
            let end = self.parse_semicolon(self.node_end(expression));
            return self.alloc_node(
                SyntaxKind::ExportAssignment,
                TextRange::new(start, end),
                NodeData::ExportAssignment(Box::new(ExportAssignmentData {
                    expression,
                    flow_node: None,
                    is_export_equals: true,
                    symbol: None,
                    type_: expression,
                    facts: 0,
                    modifiers: Some(ModifierList {
                        list: NodeList {
                            range: TextRange::new(start, self.node_start(expression)),
                            nodes: vec![export_modifier],
                            has_trailing_comma: false,
                        },
                        flags: ts_ast::ModifierFlags::default(),
                    }),
                })),
                &[export_modifier, expression],
            );
        }
        if self.current.kind == SyntaxKind::AsKeyword {
            self.bump();
            self.expect_and_bump(
                SyntaxKind::NamespaceKeyword,
                "Expected 'namespace' after 'export as'.",
            );
            let name = self.parse_identifier("Expected a namespace export name.");
            let end = self.parse_semicolon(self.node_end(name));
            return self.alloc_node(
                SyntaxKind::NamespaceExportDeclaration,
                TextRange::new(start, end),
                NodeData::NamespaceExportDeclaration(Box::new(NamespaceExportDeclarationData {
                    flow_node: None,
                    symbol: None,
                    modifiers: Some(ModifierList {
                        list: NodeList {
                            range: TextRange::new(start, self.node_start(name)),
                            nodes: vec![export_modifier],
                            has_trailing_comma: false,
                        },
                        flags: ts_ast::ModifierFlags::default(),
                    }),
                    name,
                })),
                &[export_modifier, name],
            );
        }
        if self.current.kind == SyntaxKind::DefaultKeyword {
            let default_modifier = self.consume_token_node();
            if matches!(
                self.current.kind,
                SyntaxKind::FunctionKeyword
                    | SyntaxKind::ClassKeyword
                    | SyntaxKind::InterfaceKeyword
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
            let first = self.parse_module_export_name("Expected an export name.");
            let (property_name, name) = if self.current.kind == SyntaxKind::AsKeyword {
                self.bump();
                (
                    Some(first),
                    self.parse_module_export_name("Expected an exported name."),
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
        if minimum_precedence <= 2
            && self.current.kind == SyntaxKind::AsyncKeyword
            && self.is_async_arrow_function()
        {
            return self.parse_async_arrow_function();
        }
        if minimum_precedence <= 2
            && self.current.kind == SyntaxKind::LessThanToken
            && self.language_variant != LanguageVariant::Jsx
            && self.is_generic_arrow_function()
        {
            return self.parse_generic_arrow_function();
        }
        if minimum_precedence <= 2
            && self.current.kind == SyntaxKind::OpenParenToken
            && self.is_parenthesized_arrow()
        {
            return self.parse_parenthesized_arrow_function();
        }
        let mut left = self.parse_postfix_expression();
        if minimum_precedence <= 2
            && self.current.kind == SyntaxKind::EqualsGreaterThanToken
            && self.arena.get(left).unwrap().kind == SyntaxKind::Identifier
        {
            return self.parse_single_parameter_arrow_function(left);
        }
        loop {
            if self.disallow_in && self.current.kind == SyntaxKind::InKeyword {
                break;
            }
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
        } else if first.kind == SyntaxKind::LessThanToken {
            let mut angle_depth = 1_u32;
            let mut token = self.scanner.scan();
            while token.kind != SyntaxKind::EndOfFile && angle_depth != 0 {
                match token.kind {
                    SyntaxKind::LessThanToken => angle_depth += 1,
                    SyntaxKind::GreaterThanToken => angle_depth -= 1,
                    _ => {}
                }
                if angle_depth != 0 {
                    token = self.scanner.scan();
                }
            }
            if angle_depth != 0 || self.scanner.scan().kind != SyntaxKind::OpenParenToken {
                false
            } else {
                let mut parenthesis_depth = 1_u32;
                token = self.scanner.scan();
                while token.kind != SyntaxKind::EndOfFile && parenthesis_depth != 0 {
                    match token.kind {
                        SyntaxKind::OpenParenToken => parenthesis_depth += 1,
                        SyntaxKind::CloseParenToken => parenthesis_depth -= 1,
                        _ => {}
                    }
                    if parenthesis_depth != 0 {
                        token = self.scanner.scan();
                    }
                }
                token = self.scanner.scan();
                if token.kind == SyntaxKind::ColonToken {
                    while !matches!(
                        token.kind,
                        SyntaxKind::EqualsGreaterThanToken
                            | SyntaxKind::SemicolonToken
                            | SyntaxKind::EndOfFile
                    ) {
                        token = self.scanner.scan();
                    }
                }
                token.kind == SyntaxKind::EqualsGreaterThanToken
            }
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
            let mut token = self.scanner.scan();
            if token.kind == SyntaxKind::ColonToken {
                while !matches!(
                    token.kind,
                    SyntaxKind::EqualsGreaterThanToken
                        | SyntaxKind::SemicolonToken
                        | SyntaxKind::EndOfFile
                ) {
                    token = self.scanner.scan();
                }
            }
            token.kind == SyntaxKind::EqualsGreaterThanToken
        } else {
            false
        };
        self.scanner.rewind(checkpoint);
        result
    }

    fn is_generic_arrow_function(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let mut token = self.scanner.scan();
        if token.kind != SyntaxKind::Identifier {
            self.scanner.rewind(checkpoint);
            return false;
        }

        let mut angle_depth = 1_u32;
        while token.kind != SyntaxKind::EndOfFile {
            token = self.scanner.scan();
            match token.kind {
                SyntaxKind::LessThanToken => angle_depth += 1,
                SyntaxKind::GreaterThanToken => {
                    angle_depth -= 1;
                    if angle_depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
        }
        if angle_depth != 0 || self.scanner.scan().kind != SyntaxKind::OpenParenToken {
            self.scanner.rewind(checkpoint);
            return false;
        }

        let mut parenthesis_depth = 1_u32;
        token = self.scanner.scan();
        while token.kind != SyntaxKind::EndOfFile && parenthesis_depth != 0 {
            match token.kind {
                SyntaxKind::OpenParenToken => parenthesis_depth += 1,
                SyntaxKind::CloseParenToken => parenthesis_depth -= 1,
                _ => {}
            }
            if parenthesis_depth != 0 {
                token = self.scanner.scan();
            }
        }
        if parenthesis_depth != 0 {
            self.scanner.rewind(checkpoint);
            return false;
        }

        token = self.scanner.scan();
        let result = if token.kind == SyntaxKind::EqualsGreaterThanToken {
            true
        } else if token.kind == SyntaxKind::ColonToken {
            let mut delimiter_depth = 0_i32;
            loop {
                token = self.scanner.scan();
                match token.kind {
                    SyntaxKind::OpenParenToken
                    | SyntaxKind::OpenBracketToken
                    | SyntaxKind::OpenBraceToken
                    | SyntaxKind::LessThanToken => delimiter_depth += 1,
                    SyntaxKind::CloseParenToken
                    | SyntaxKind::CloseBracketToken
                    | SyntaxKind::CloseBraceToken
                    | SyntaxKind::GreaterThanToken => delimiter_depth -= 1,
                    SyntaxKind::EqualsGreaterThanToken if delimiter_depth == 0 => break true,
                    SyntaxKind::EndOfFile | SyntaxKind::SemicolonToken => break false,
                    _ => {}
                }
            }
        } else {
            false
        };
        self.scanner.rewind(checkpoint);
        result
    }

    fn parse_generic_arrow_function(&mut self) -> NodeId {
        let start = self.current.range.start;
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameter_list();
        let return_type = self.parse_optional_type_annotation();
        let arrow =
            self.parse_expected_token_node(SyntaxKind::EqualsGreaterThanToken, "Expected '=>'.");
        let body = self.parse_arrow_function_body();
        let mut children = Vec::new();
        extend_list_children(&mut children, type_parameters.as_ref());
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
                type_parameters,
                facts: 0,
                modifiers: None,
            })),
            &children,
        )
    }

    fn parse_async_arrow_function(&mut self) -> NodeId {
        let async_modifier = self.consume_token_node();
        let start = self.node_start(async_modifier);
        let type_parameters = self.parse_type_parameters();
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
        let body = self.parse_arrow_function_body();
        let mut children = vec![async_modifier];
        extend_list_children(&mut children, type_parameters.as_ref());
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
                type_parameters,
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
        let async_function = self.current.kind == SyntaxKind::AsyncKeyword
            && !self.next_token_preceded_by_line_break()
            && self.next_token_kind() == SyntaxKind::FunctionKeyword;
        if self.current.kind == SyntaxKind::AwaitKeyword {
            return self.parse_await_expression();
        }
        if self.current.kind == SyntaxKind::YieldKeyword {
            return self.parse_yield_expression();
        }
        if self.current.kind == SyntaxKind::TypeOfKeyword {
            let start = self.consume().range.start;
            let expression = self.parse_postfix_expression();
            return self.alloc_node(
                SyntaxKind::TypeOfExpression,
                TextRange::new(start, self.node_end(expression)),
                NodeData::TypeOfExpression(Box::new(TypeOfExpressionData { expression })),
                &[expression],
            );
        }
        if self.current.kind == SyntaxKind::DeleteKeyword {
            let start = self.consume().range.start;
            let expression = self.parse_postfix_expression();
            return self.alloc_node(
                SyntaxKind::DeleteExpression,
                TextRange::new(start, self.node_end(expression)),
                NodeData::DeleteExpression(Box::new(DeleteExpressionData { expression })),
                &[expression],
            );
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
        let mut expression = if async_function {
            self.parse_async_function_expression()
        } else if self.current.kind == SyntaxKind::NewKeyword {
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
                SyntaxKind::LessThanToken => {
                    if !self.is_type_argument_expression_suffix() {
                        break;
                    }
                    let type_arguments = self
                        .parse_type_arguments()
                        .expect("type argument suffix starts with '<'");
                    if self.current.kind == SyntaxKind::OpenParenToken {
                        let arguments = self.parse_argument_list();
                        let end = arguments.range.end;
                        let mut children = vec![expression];
                        children.extend(type_arguments.nodes.iter().copied());
                        children.extend(arguments.nodes.iter().copied());
                        expression = self.alloc_node(
                            SyntaxKind::CallExpression,
                            TextRange::new(self.node_start(expression), end),
                            NodeData::CallExpression(Box::new(CallExpressionData {
                                arguments,
                                expression,
                                question_dot_token: None,
                                symbol: None,
                                type_arguments: Some(type_arguments),
                                facts: 0,
                            })),
                            &children,
                        );
                    } else {
                        let start = self.node_start(expression);
                        let end = type_arguments.range.end;
                        expression = self.alloc_node(
                            SyntaxKind::ParenthesizedExpression,
                            TextRange::new(start, end),
                            NodeData::ParenthesizedExpression(Box::new(
                                ParenthesizedExpressionData { expression },
                            )),
                            &[expression],
                        );
                    }
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

    fn is_type_argument_expression_suffix(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let mut depth = 1_u32;
        let mut token = self.scanner.scan();
        while token.kind != SyntaxKind::EndOfFile {
            match token.kind {
                SyntaxKind::LessThanToken => depth += 1,
                SyntaxKind::GreaterThanToken => {
                    depth -= 1;
                    if depth == 0 {
                        token = self.scanner.scan();
                        break;
                    }
                }
                _ => {}
            }
            token = self.scanner.scan();
        }
        self.scanner.rewind(checkpoint);
        depth == 0
            && (token.kind == SyntaxKind::OpenParenToken || token.kind.is_assignment_operator())
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
        let mut parenthesis_depth = 1_u32;
        let mut brace_depth = 0_u32;
        let mut bracket_depth = 0_u32;
        let mut typed_parameter = false;
        let mut top_level_question = false;
        let mut previous_kind = SyntaxKind::OpenParenToken;
        let mut token = self.scanner.scan();
        while token.kind != SyntaxKind::EndOfFile {
            match token.kind {
                SyntaxKind::OpenParenToken => parenthesis_depth += 1,
                SyntaxKind::CloseParenToken => {
                    parenthesis_depth -= 1;
                    if parenthesis_depth == 0 {
                        token = self.scanner.scan();
                        let result = matches!(
                            token.kind,
                            SyntaxKind::EqualsGreaterThanToken
                                | SyntaxKind::OpenBraceToken
                                | SyntaxKind::ColonToken
                        ) || typed_parameter;
                        self.scanner.rewind(checkpoint);
                        return result;
                    }
                }
                SyntaxKind::OpenBraceToken => brace_depth += 1,
                SyntaxKind::CloseBraceToken => brace_depth = brace_depth.saturating_sub(1),
                SyntaxKind::OpenBracketToken => bracket_depth += 1,
                SyntaxKind::CloseBracketToken => bracket_depth = bracket_depth.saturating_sub(1),
                SyntaxKind::QuestionToken
                    if parenthesis_depth == 1 && brace_depth == 0 && bracket_depth == 0 =>
                {
                    top_level_question = true;
                }
                SyntaxKind::ColonToken
                    if parenthesis_depth == 1 && brace_depth == 0 && bracket_depth == 0 =>
                {
                    if previous_kind == SyntaxKind::QuestionToken || !top_level_question {
                        typed_parameter = true;
                    }
                    top_level_question = false;
                }
                _ => {}
            }
            previous_kind = token.kind;
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
        let body = self.parse_arrow_function_body();
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
        let body = self.parse_arrow_function_body();
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

    fn parse_arrow_function_body(&mut self) -> NodeId {
        if self.current.kind == SyntaxKind::OpenBraceToken {
            return self.parse_block();
        }
        if self.current.kind == SyntaxKind::VarKeyword {
            return self.parse_arrow_body_with_missing_open_brace();
        }
        let body = self.parse_binary_expression(2);
        let body = self.parenthesize_asserted_object_literal(body);
        self.collapse_redundant_parentheses_around_asserted_object(body)
    }

    fn parse_arrow_body_with_missing_open_brace(&mut self) -> NodeId {
        self.error_current("Expected '{'.");
        let start = self.current.range.start;
        let statement = self.parse_statement();
        let statement_end = self.node_end(statement);
        let end = if self.current.kind == SyntaxKind::CloseBraceToken {
            self.consume().range.end
        } else {
            statement_end
        };
        self.alloc_node(
            SyntaxKind::Block,
            TextRange::new(start, end),
            NodeData::Block(Box::new(BlockData {
                flow_node: None,
                locals: SymbolTable,
                multi_line: false,
                next_container: None,
                statements: NodeList {
                    range: TextRange::new(start, statement_end),
                    nodes: vec![statement],
                    has_trailing_comma: false,
                },
                facts: 0,
            })),
            &[statement],
        )
    }

    fn parenthesize_asserted_object_literal(&mut self, expression: NodeId) -> NodeId {
        let child = match &self.arena.get(expression).unwrap().data {
            NodeData::TypeAssertion(assertion) => Some(assertion.expression),
            NodeData::AsExpression(assertion) => Some(assertion.expression),
            NodeData::SatisfiesExpression(assertion) => Some(assertion.expression),
            NodeData::ParenthesizedExpression(parenthesized)
                if matches!(
                    self.arena
                        .get(parenthesized.expression)
                        .map(|node| &node.data),
                    Some(
                        NodeData::TypeAssertion(_)
                            | NodeData::AsExpression(_)
                            | NodeData::SatisfiesExpression(_)
                    )
                ) =>
            {
                Some(parenthesized.expression)
            }
            NodeData::ObjectLiteralExpression(_) => {
                let range = self.arena.get(expression).unwrap().range;
                return self.alloc_node(
                    SyntaxKind::ParenthesizedExpression,
                    range,
                    NodeData::ParenthesizedExpression(Box::new(ParenthesizedExpressionData {
                        expression,
                    })),
                    &[expression],
                );
            }
            _ => None,
        };
        if let Some(child) = child {
            let protected = self.parenthesize_asserted_object_literal(child);
            if protected != child {
                match &mut self.arena.get_mut(expression).unwrap().data {
                    NodeData::TypeAssertion(assertion) => assertion.expression = protected,
                    NodeData::AsExpression(assertion) => assertion.expression = protected,
                    NodeData::SatisfiesExpression(assertion) => assertion.expression = protected,
                    NodeData::ParenthesizedExpression(parenthesized) => {
                        parenthesized.expression = protected;
                    }
                    _ => unreachable!(),
                }
                self.arena.get_mut(protected).unwrap().parent = Some(expression);
            }
        }
        expression
    }

    fn collapse_redundant_parentheses_around_asserted_object(
        &self,
        mut expression: NodeId,
    ) -> NodeId {
        loop {
            let NodeData::ParenthesizedExpression(parenthesized) =
                &self.arena.get(expression).unwrap().data
            else {
                return expression;
            };
            if !matches!(
                self.arena
                    .get(parenthesized.expression)
                    .map(|node| &node.data),
                Some(NodeData::ParenthesizedExpression(_))
            ) || !self.contains_asserted_object_literal(parenthesized.expression, false)
            {
                return expression;
            }
            expression = parenthesized.expression;
        }
    }

    fn contains_asserted_object_literal(&self, expression: NodeId, asserted: bool) -> bool {
        match &self.arena.get(expression).unwrap().data {
            NodeData::TypeAssertion(assertion) => {
                self.contains_asserted_object_literal(assertion.expression, true)
            }
            NodeData::AsExpression(assertion) => {
                self.contains_asserted_object_literal(assertion.expression, true)
            }
            NodeData::SatisfiesExpression(assertion) => {
                self.contains_asserted_object_literal(assertion.expression, true)
            }
            NodeData::ParenthesizedExpression(parenthesized) => {
                self.contains_asserted_object_literal(parenthesized.expression, asserted)
            }
            NodeData::ObjectLiteralExpression(_) => asserted,
            _ => false,
        }
    }

    fn parse_primary_expression(&mut self) -> NodeId {
        match self.current.kind {
            SyntaxKind::Identifier => self.parse_identifier("Expected an expression."),
            SyntaxKind::PrivateIdentifier => self.parse_private_identifier(),
            SyntaxKind::NumericLiteral => self.parse_numeric_literal(),
            SyntaxKind::BigIntLiteral => self.parse_bigint_literal(),
            SyntaxKind::StringLiteral => self.parse_string_literal(),
            SyntaxKind::SlashToken | SyntaxKind::SlashEqualsToken => {
                self.parse_regular_expression_literal()
            }
            SyntaxKind::FunctionKeyword => self.parse_function_expression(),
            SyntaxKind::ClassKeyword => self.parse_class_expression(),
            SyntaxKind::NoSubstitutionTemplateLiteral => self.parse_template_literal(),
            SyntaxKind::NullKeyword
            | SyntaxKind::TrueKeyword
            | SyntaxKind::FalseKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::ThisKeyword
            | SyntaxKind::SuperKeyword => self.parse_keyword_expression(),
            kind if is_contextual_keyword(kind) => {
                self.parse_identifier_name("Expected an expression.")
            }
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
                if binary_precedence(self.current.kind).is_none()
                    && !is_expression_terminator(self.current.kind)
                {
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
        } else if self.current.kind == SyntaxKind::ColonToken {
            self.error_current("Expected ')'.");
            self.bump();
            self.parse_type();
            if self.current.kind == SyntaxKind::CloseParenToken {
                self.consume().range.end
            } else {
                self.node_end(expression)
            }
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
        let mut trailing = false;
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
            if matches!(
                self.current.kind,
                SyntaxKind::GetKeyword | SyntaxKind::SetKeyword
            ) && self.is_accessor_signature()
            {
                properties.push(self.parse_class_accessor(property_start, None, Vec::new(), true));
                if self.current.kind != SyntaxKind::CommaToken {
                    break;
                }
                self.bump();
                trailing = self.current.kind == SyntaxKind::CloseBraceToken;
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
            trailing = self.current.kind == SyntaxKind::CloseBraceToken;
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
                    has_trailing_comma: trailing,
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
        let tag_name = self.parse_jsx_tag_name("Expected a JSX tag name.");
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
        let closing_name = self.parse_jsx_tag_name("Expected a JSX closing tag name.");
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
            self.current = self.scanner.scan_jsx_identifier();
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

    fn parse_jsx_tag_name(&mut self, message: &str) -> NodeId {
        self.current = self.scanner.scan_jsx_identifier();
        let mut expression = self.parse_identifier(message);
        while self.current.kind == SyntaxKind::DotToken {
            self.bump();
            self.current = self.scanner.scan_jsx_identifier();
            let name = self.parse_identifier(message);
            expression = self.alloc_node(
                SyntaxKind::PropertyAccessExpression,
                TextRange::new(self.node_start(expression), self.node_end(name)),
                NodeData::PropertyAccessExpression(Box::new(PropertyAccessExpressionData {
                    expression,
                    flow_node: None,
                    question_dot_token: None,
                    facts: 0,
                    name,
                })),
                &[expression, name],
            );
        }
        expression
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

    fn parse_module_export_name(&mut self, message: &str) -> NodeId {
        if self.current.kind == SyntaxKind::StringLiteral {
            self.parse_string_literal()
        } else {
            self.parse_identifier_name(message)
        }
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

    fn parse_regular_expression_literal(&mut self) -> NodeId {
        let token = self.scanner.rescan_slash_token();
        self.current = self.scanner.scan();
        self.alloc_node(
            SyntaxKind::RegularExpressionLiteral,
            token.range,
            NodeData::RegularExpressionLiteral(Box::new(RegularExpressionLiteralData {
                text: token.text.to_owned(),
                token_flags: TokenFlags::default(),
            })),
            &[],
        )
    }

    fn parse_function_expression(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let asterisk_token =
            (self.current.kind == SyntaxKind::AsteriskToken).then(|| self.consume_token_node());
        let name = (self.current.kind == SyntaxKind::Identifier || self.current.kind.is_keyword())
            .then(|| self.parse_identifier_name("Expected a function name."));
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameter_list();
        let return_type = self.parse_optional_type_annotation();
        let body = if self.current.kind == SyntaxKind::OpenBraceToken {
            self.parse_block()
        } else {
            self.error_current("Expected '{'.");
            let position = self.current.range.start;
            self.alloc_node(
                SyntaxKind::Block,
                TextRange::new(position, position),
                NodeData::Block(Box::new(BlockData {
                    flow_node: None,
                    locals: SymbolTable,
                    multi_line: false,
                    next_container: None,
                    statements: NodeList {
                        range: TextRange::new(position, position),
                        nodes: Vec::new(),
                        has_trailing_comma: false,
                    },
                    facts: 0,
                })),
                &[],
            )
        };
        let mut children = Vec::new();
        children.extend(asterisk_token);
        children.extend(name);
        extend_list_children(&mut children, type_parameters.as_ref());
        children.extend(parameters.nodes.iter().copied());
        children.extend(return_type);
        children.push(body);
        self.alloc_node(
            SyntaxKind::FunctionExpression,
            TextRange::new(start, self.node_end(body)),
            NodeData::FunctionExpression(Box::new(FunctionExpressionData {
                asterisk_token,
                body,
                end_flow_node: None,
                flow_node: None,
                full_signature: None,
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

    fn parse_async_function_expression(&mut self) -> NodeId {
        let start = self.current.range.start;
        let async_modifier = self.consume_token_node();
        let expression = self.parse_function_expression();
        self.attach_modifiers(expression, vec![async_modifier], start);
        expression
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
        if self.current.kind == SyntaxKind::AssertsKeyword {
            return true;
        }
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
        let asserts_modifier =
            (self.current.kind == SyntaxKind::AssertsKeyword).then(|| self.consume_token_node());
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
        let type_node = if self.current.kind == SyntaxKind::IsKeyword {
            self.bump();
            Some(self.parse_type())
        } else if asserts_modifier.is_some() {
            None
        } else {
            self.expect_and_bump(SyntaxKind::IsKeyword, "Expected 'is'.");
            Some(self.parse_type())
        };
        let end =
            type_node.map_or_else(|| self.node_end(parameter_name), |node| self.node_end(node));
        let mut children = Vec::new();
        children.extend(asserts_modifier);
        children.push(parameter_name);
        children.extend(type_node);
        self.alloc_node(
            SyntaxKind::TypePredicate,
            TextRange::new(start, end),
            NodeData::TypePredicateNode(Box::new(TypePredicateNodeData {
                asserts_modifier,
                parameter_name,
                type_: type_node,
            })),
            &children,
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
            SyntaxKind::ConstKeyword => {
                let start = self.current.range.start;
                let type_name = self.parse_identifier_name("Expected 'const'.");
                self.alloc_node(
                    SyntaxKind::TypeReference,
                    TextRange::new(start, self.node_end(type_name)),
                    NodeData::TypeReferenceNode(Box::new(TypeReferenceNodeData {
                        type_arguments: None,
                        type_name,
                    })),
                    &[type_name],
                )
            }
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

    fn error_code_at(
        &mut self,
        range: TextRange,
        code: u32,
        arguments: impl IntoIterator<Item = String>,
    ) {
        let message = message_by_code(code).expect("parser diagnostic code exists");
        let arguments = arguments.into_iter().collect::<Vec<_>>();
        self.diagnostics.push(Diagnostic::typescript(
            range,
            code,
            parser_diagnostic_category(message.category()),
            message
                .format(&arguments)
                .expect("parser diagnostic arguments match catalog message"),
        ));
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

fn is_contextual_keyword(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::PrivateKeyword | SyntaxKind::ProtectedKeyword | SyntaxKind::PublicKeyword
    ) || (kind as u16) >= (SyntaxKind::AbstractKeyword as u16)
        && (kind as u16) <= (SyntaxKind::DeferKeyword as u16)
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
        NODE_FLAG_AWAIT_USING, NODE_FLAG_HAS_ERROR, NODE_FLAG_USING, ParseResult,
        parse_jsdoc_comment, parse_jsx_source_file, parse_source_file,
    };

    #[test]
    fn parses_leading_amd_pragmas_and_reports_duplicate_module_names() {
        let source = concat!(
            "\u{feff}/* header */\n",
            "/// <reference path='types.d.ts' />\n",
            "  /// <amd-dependency name = \"first\" path = 'alpha' />\r\n",
            "///<amd-dependency path=\"beta\"/>\n",
            "///<amd-module name='First'/>\n",
            "/// <amd-module name = \"Second\" />\n",
            "const value = 1;\n",
            "///<amd-dependency path='late'/>\n",
        );
        let result = parse_source_file(source);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2458]
        );
        assert_eq!(
            result
                .amd_dependencies
                .iter()
                .map(|dependency| (dependency.path.as_str(), dependency.name.as_deref()))
                .collect::<Vec<_>>(),
            [("alpha", Some("first")), ("beta", None)]
        );
        assert_eq!(
            result
                .amd_module_names
                .iter()
                .map(|directive| directive.name.as_str())
                .collect::<Vec<_>>(),
            ["First", "Second"]
        );
        assert_eq!(result.amd_module_name.as_deref(), Some("Second"));
        assert_eq!(
            result.diagnostics[0].range,
            result.amd_module_names[1].range
        );

        for range in result
            .amd_dependencies
            .iter()
            .map(|dependency| dependency.range)
            .chain(
                result
                    .amd_module_names
                    .iter()
                    .map(|directive| directive.range),
            )
        {
            let start = usize::try_from(range.start.get()).unwrap();
            let end = usize::try_from(range.end.get()).unwrap();
            assert!(source[start..end].starts_with("///"));
            assert!(!source[start..end].contains('\n'));
            assert!(!source[start..end].contains('\r'));
        }
    }

    #[test]
    fn ignores_malformed_and_non_leading_amd_pragmas() {
        let source = concat!(
            "///<amd-dependency name='missing-path'/>\n",
            "///<amd-module />\n",
            "const value = 1;\n",
            "///<amd-dependency path='late'/>\n",
            "///<amd-module name='Late'/>\n",
        );
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert!(result.amd_dependencies.is_empty());
        assert!(result.amd_module_names.is_empty());
        assert!(result.amd_module_name.is_none());
    }

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
    fn parses_enum_property_names_initializers_and_ranges() {
        let source = concat!(
            "enum E { ",
            "A, ",
            "\"non identifier\", ",
            "1 = seed, ",
            "[key] = seed + 1, ",
            "[ns.value]",
            " }",
        );
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1);
        let NodeData::EnumDeclaration(declaration) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected enum declaration");
        };
        assert_eq!(declaration.members.nodes.len(), 5);

        for ((member, expected_kind), expected_text) in declaration
            .members
            .nodes
            .iter()
            .zip([
                SyntaxKind::Identifier,
                SyntaxKind::StringLiteral,
                SyntaxKind::NumericLiteral,
                SyntaxKind::ComputedPropertyName,
                SyntaxKind::ComputedPropertyName,
            ])
            .zip([
                "A",
                "\"non identifier\"",
                "1 = seed",
                "[key] = seed + 1",
                "[ns.value]",
            ])
        {
            let member_node = result.arena.get(*member).unwrap();
            let NodeData::EnumMember(member_data) = &member_node.data else {
                panic!("expected enum member");
            };
            assert_eq!(
                result.arena.get(member_data.name).unwrap().kind,
                expected_kind
            );
            assert_eq!(
                result.arena.get(member_data.name).unwrap().parent,
                Some(*member)
            );
            assert_eq!(
                &source
                    [member_node.range.start.get() as usize..member_node.range.end.get() as usize],
                expected_text
            );
            if let Some(initializer) = member_data.initializer {
                assert_eq!(result.arena.get(initializer).unwrap().parent, Some(*member));
            }
            if let NodeData::ComputedPropertyName(computed) =
                &result.arena.get(member_data.name).unwrap().data
            {
                assert_eq!(
                    result.arena.get(computed.expression).unwrap().parent,
                    Some(member_data.name)
                );
            }
        }
    }

    #[test]
    fn enum_member_name_recovery_preserves_later_members_and_statements() {
        let result = parse_source_file("enum E { A, , \"quoted\" = 1 } const after = 1;");
        assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        let NodeData::EnumDeclaration(declaration) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected enum declaration");
        };
        assert_eq!(declaration.members.nodes.len(), 3);
        let missing_member = result.arena.get(declaration.members.nodes[1]).unwrap();
        let NodeData::EnumMember(missing_member) = &missing_member.data else {
            panic!("expected recovered enum member");
        };
        assert_eq!(
            result.arena.get(missing_member.name).unwrap().flags,
            NODE_FLAG_HAS_ERROR
        );
        let NodeData::EnumMember(quoted_member) =
            &result.arena.get(declaration.members.nodes[2]).unwrap().data
        else {
            panic!("expected quoted enum member");
        };
        assert_eq!(
            result.arena.get(quoted_member.name).unwrap().kind,
            SyntaxKind::StringLiteral
        );
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::VariableStatement
        );
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
    fn distinguishes_generic_arrows_from_generic_function_type_assertions() {
        let source = "var r = <T>(x: T) => x;\nvar r2 = < <T>(x: T) => T>f;";
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);

        let (list, _) = variable_list(&result, statements[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let arrow_id = declaration.initializer.unwrap();
        let NodeData::ArrowFunction(arrow) = &result.arena.get(arrow_id).unwrap().data else {
            panic!("expected generic arrow function");
        };
        let type_parameters = arrow.type_parameters.as_ref().unwrap();
        assert_eq!(type_parameters.nodes.len(), 1);
        assert_eq!(arrow.parameters.nodes.len(), 1);
        assert_eq!(
            result.arena.get(arrow.body).unwrap().kind,
            SyntaxKind::Identifier
        );
        assert_eq!(
            result.arena.get(type_parameters.nodes[0]).unwrap().parent,
            Some(arrow_id)
        );

        let (list, _) = variable_list(&result, statements[1]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let assertion_id = declaration.initializer.unwrap();
        let NodeData::TypeAssertion(assertion) = &result.arena.get(assertion_id).unwrap().data
        else {
            panic!("expected type assertion");
        };
        let NodeData::FunctionTypeNode(function_type) =
            &result.arena.get(assertion.type_).unwrap().data
        else {
            panic!("expected generic function type");
        };
        assert_eq!(
            function_type.type_parameters.as_ref().unwrap().nodes.len(),
            1
        );
        assert_eq!(
            result.arena.get(assertion.expression).unwrap().kind,
            SyntaxKind::Identifier
        );
    }

    #[test]
    fn keeps_asserted_object_literals_as_arrow_expression_bodies() {
        let result = parse_source_file(concat!(
            "var a = value => <any>{};\n",
            "var b = value => <any><any>{};\n",
            "var c = () => (<Error>{ name: 'x' });\n",
            "var d = () => ({ name: 'x' });\n",
        ));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        for statement in source_statements(&result) {
            let (list, _) = variable_list(&result, *statement);
            let declaration = declaration_nodes(&result, list)[0];
            let NodeData::VariableDeclaration(declaration) =
                &result.arena.get(declaration).unwrap().data
            else {
                panic!("expected variable declaration");
            };
            let arrow = declaration.initializer.unwrap();
            let NodeData::ArrowFunction(arrow) = &result.arena.get(arrow).unwrap().data else {
                panic!("expected arrow function");
            };
            assert_ne!(
                result.arena.get(arrow.body).unwrap().kind,
                SyntaxKind::Block
            );
            let object =
                find_descendant_kind(&result, arrow.body, SyntaxKind::ObjectLiteralExpression)
                    .expect("expected object literal body");
            assert_eq!(
                result
                    .arena
                    .get(result.arena.get(object).unwrap().parent.unwrap())
                    .unwrap()
                    .kind,
                SyntaxKind::ParenthesizedExpression
            );
        }
    }

    #[test]
    fn parses_async_generic_arrows_in_object_literal_properties() {
        let result = parse_source_file(concat!(
            "const fn1 = () => ({\n",
            "  test: async <T = undefined>(value: T): Promise<T> => value,\n",
            "  extra: () => {},\n",
            "});\n",
        ));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let arrows = result
            .arena
            .iter()
            .filter_map(|(id, node)| matches!(node.data, NodeData::ArrowFunction(_)).then_some(id))
            .collect::<Vec<_>>();
        assert_eq!(arrows.len(), 3);
        let generic = arrows
            .into_iter()
            .find(|id| {
                matches!(
                    &result.arena.get(*id).unwrap().data,
                    NodeData::ArrowFunction(arrow) if arrow.type_parameters.is_some()
                )
            })
            .expect("expected async generic arrow");
        let NodeData::ArrowFunction(generic) = &result.arena.get(generic).unwrap().data else {
            unreachable!();
        };
        assert_eq!(generic.type_parameters.as_ref().unwrap().nodes.len(), 1);
        assert_eq!(generic.parameters.nodes.len(), 1);
        assert!(generic.modifiers.as_ref().is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|modifier| {
                result.arena.get(*modifier).unwrap().kind == SyntaxKind::AsyncKeyword
            })
        }));
        assert_eq!(
            result.arena.get(generic.body).unwrap().kind,
            SyntaxKind::Identifier
        );
    }

    #[test]
    fn recovers_missing_arrow_tokens_without_confusing_parenthesized_objects() {
        let missing_body_brace = parse_source_file("var a = () => var k = 10;}");
        assert_eq!(
            missing_body_brace
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [1005]
        );
        let (list, _) = variable_list(
            &missing_body_brace,
            source_statements(&missing_body_brace)[0],
        );
        let declaration = declaration_nodes(&missing_body_brace, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &missing_body_brace.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let NodeData::ArrowFunction(arrow) = &missing_body_brace
            .arena
            .get(declaration.initializer.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected recovered arrow");
        };
        assert_eq!(
            missing_body_brace.arena.get(arrow.body).unwrap().kind,
            SyntaxKind::Block
        );

        let missing_arrow = parse_source_file("var typed = (x: number);");
        let (list, _) = variable_list(&missing_arrow, source_statements(&missing_arrow)[0]);
        let declaration = declaration_nodes(&missing_arrow, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &missing_arrow.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        assert_eq!(
            missing_arrow
                .arena
                .get(declaration.initializer.unwrap())
                .unwrap()
                .kind,
            SyntaxKind::ArrowFunction
        );

        let object = parse_source_file(
            "const test = () => ({ prop: !value, run: () => { if (!a.b()) return 'x'; } });",
        );
        assert!(object.diagnostics.is_empty(), "{:?}", object.diagnostics);
        assert_eq!(
            object
                .arena
                .iter()
                .filter(|(_, node)| matches!(node.data, NodeData::ArrowFunction(_)))
                .count(),
            2
        );
    }

    #[test]
    fn keeps_double_less_than_on_the_shift_recovery_path() {
        let source = "var r3 = <<T>(x: T) => T>f;";
        let result = parse_source_file(source);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [1109, 1005, 1005, 1005]
        );
        assert_eq!(
            result.diagnostics[0].range.start.get(),
            u32::try_from(source.find("<<").unwrap()).unwrap()
        );
        let statements = source_statements(&result);
        let (list, _) = variable_list(&result, statements[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected recovered variable declaration");
        };
        let initializer = declaration.initializer.unwrap();
        let NodeData::BinaryExpression(comma) = &result.arena.get(initializer).unwrap().data else {
            panic!("expected recovered comma expression");
        };
        assert_eq!(
            result.arena.get(comma.operator_token).unwrap().kind,
            SyntaxKind::CommaToken
        );
        assert_eq!(
            result.arena.get(comma.right).unwrap().kind,
            SyntaxKind::Identifier
        );
        let NodeData::BinaryExpression(greater_than) = &result.arena.get(comma.left).unwrap().data
        else {
            panic!("expected recovered shift comparison");
        };
        assert_eq!(
            result.arena.get(greater_than.operator_token).unwrap().kind,
            SyntaxKind::GreaterThanToken
        );
        assert_eq!(statements.len(), 2);
    }

    #[test]
    fn parses_object_accessors_and_recovers_a_missing_body() {
        let result = parse_source_file(
            "const value = { get item() { return 1; }, set item(next: number) };",
        );
        assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
        assert_eq!(result.diagnostics[0].code, Some(1005));
        let statements = source_statements(&result);
        let (list, _) = variable_list(&result, statements[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected declaration");
        };
        let NodeData::ObjectLiteralExpression(object) = &result
            .arena
            .get(declaration.initializer.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected object literal");
        };
        assert_eq!(object.properties.nodes.len(), 2);
        let NodeData::GetAccessorDeclaration(getter) =
            &result.arena.get(object.properties.nodes[0]).unwrap().data
        else {
            panic!("expected getter");
        };
        assert!(getter.body.is_some());
        let NodeData::SetAccessorDeclaration(setter) =
            &result.arena.get(object.properties.nodes[1]).unwrap().data
        else {
            panic!("expected setter");
        };
        assert!(setter.body.is_none());
    }

    #[test]
    fn type_accessor_implementations_own_their_bodies() {
        let source = concat!(
            "type A = { get foo() { return 0 } };\n",
            "type B = { set foo(v: any) { } };\n",
            "interface X { get foo() { return 0 } }\n",
            "interface Y { set foo(v: any) { } }\n",
        );
        let result = parse_source_file(source);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [1183, 1183, 1183, 1183]
        );

        let statements = source_statements(&result);
        assert_eq!(statements.len(), 4, "{:?}", result.diagnostics);
        assert_eq!(
            statements
                .iter()
                .map(|statement| result.arena.get(*statement).unwrap().kind)
                .collect::<Vec<_>>(),
            [
                SyntaxKind::TypeAliasDeclaration,
                SyntaxKind::TypeAliasDeclaration,
                SyntaxKind::InterfaceDeclaration,
                SyntaxKind::InterfaceDeclaration,
            ]
        );
        assert!(
            result
                .arena
                .iter()
                .all(|(_, node)| node.kind != SyntaxKind::EmptyStatement)
        );

        let accessors = result
            .arena
            .iter()
            .filter_map(|(id, node)| match &node.data {
                NodeData::GetAccessorDeclaration(accessor) => Some((id, accessor.body)),
                NodeData::SetAccessorDeclaration(accessor) => Some((id, accessor.body)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(accessors.len(), 4);
        for (accessor, body) in accessors {
            let body = body.expect("type accessor implementation should retain its body");
            assert_eq!(result.arena.get(body).unwrap().kind, SyntaxKind::Block);
            assert_eq!(result.arena.get(body).unwrap().parent, Some(accessor));
        }

        for statement in &statements[..2] {
            let range = result.arena.get(*statement).unwrap().range;
            assert_eq!(source.as_bytes()[range.end.get() as usize - 1], b';');
        }
    }

    #[test]
    fn coalesces_invalid_token_statement_tails_without_creating_statements() {
        let source = "G@\u{0004}\u{fffd}\u{0004}G@\u{0005}\u{fffd}\u{0005}";
        let result = parse_source_file(source);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1, "{:?}", result.diagnostics);
        let NodeData::ExpressionStatement(statement) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected the leading G expression statement");
        };
        let NodeData::Identifier(identifier) =
            &result.arena.get(statement.expression).unwrap().data
        else {
            panic!("expected the leading G identifier");
        };
        assert_eq!(identifier.text, "G");
        assert!(
            result
                .arena
                .iter()
                .all(|(_, node)| node.kind != SyntaxKind::EmptyStatement)
        );

        let invalid_character_diagnostics = result
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == Some(1127))
            .collect::<Vec<_>>();
        assert_eq!(invalid_character_diagnostics.len(), 1);
        assert_eq!(invalid_character_diagnostics[0].range.start.get(), 2);
        assert_eq!(
            invalid_character_diagnostics[0].range.end.get(),
            u32::try_from(source.len()).unwrap()
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1128))
        );
    }

    #[test]
    fn invalid_token_recovery_preserves_following_and_explicit_empty_statements() {
        let result = parse_source_file("\u{0004} junk;\nG;;");
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2, "{:?}", result.diagnostics);
        assert_eq!(
            statements
                .iter()
                .map(|statement| result.arena.get(*statement).unwrap().kind)
                .collect::<Vec<_>>(),
            [SyntaxKind::ExpressionStatement, SyntaxKind::EmptyStatement]
        );
    }

    #[test]
    fn parses_parameter_modifiers_and_keyword_class_names() {
        let source = r"
            var v = (public x: string) => x;
            class C { constructor(public readonly value: string) {} }
            class any {}
        ";
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);

        let (list, _) = variable_list(&result, statements[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let NodeData::ArrowFunction(arrow) = &result
            .arena
            .get(declaration.initializer.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected arrow function");
        };
        let NodeData::ParameterDeclaration(parameter) =
            &result.arena.get(arrow.parameters.nodes[0]).unwrap().data
        else {
            panic!("expected arrow parameter");
        };
        let NodeData::Identifier(name) = &result.arena.get(parameter.name).unwrap().data else {
            panic!("expected parameter identifier");
        };
        assert_eq!(name.text, "x");
        assert_eq!(parameter.modifiers.as_ref().unwrap().list.nodes.len(), 1);
        assert_eq!(
            result
                .arena
                .get(parameter.modifiers.as_ref().unwrap().list.nodes[0])
                .unwrap()
                .kind,
            SyntaxKind::PublicKeyword
        );

        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        let NodeData::MethodDeclaration(constructor) =
            &result.arena.get(class.members.nodes[0]).unwrap().data
        else {
            panic!("expected constructor method");
        };
        let NodeData::ParameterDeclaration(parameter) = &result
            .arena
            .get(constructor.parameters.nodes[0])
            .unwrap()
            .data
        else {
            panic!("expected constructor parameter");
        };
        let modifier_kinds = parameter
            .modifiers
            .as_ref()
            .unwrap()
            .list
            .nodes
            .iter()
            .map(|modifier| result.arena.get(*modifier).unwrap().kind)
            .collect::<Vec<_>>();
        assert_eq!(
            modifier_kinds,
            [SyntaxKind::PublicKeyword, SyntaxKind::ReadonlyKeyword]
        );
        let NodeData::Identifier(name) = &result.arena.get(parameter.name).unwrap().data else {
            panic!("expected parameter identifier");
        };
        assert_eq!(name.text, "value");

        let NodeData::ClassDeclaration(keyword_named) =
            &result.arena.get(statements[2]).unwrap().data
        else {
            panic!("expected keyword-named class declaration");
        };
        let NodeData::Identifier(name) =
            &result.arena.get(keyword_named.name.unwrap()).unwrap().data
        else {
            panic!("expected class name");
        };
        assert_eq!(name.text, "any");
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
    fn parses_default_exported_interfaces_as_declarations() {
        let result = parse_source_file("export default interface Shape { value: string; }");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1);
        let NodeData::InterfaceDeclaration(interface) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected interface declaration");
        };
        let NodeData::Identifier(name) = &result.arena.get(interface.name).unwrap().data else {
            panic!("expected interface name");
        };
        assert_eq!(name.text, "Shape");
        let modifier_kinds = interface
            .modifiers
            .as_ref()
            .unwrap()
            .list
            .nodes
            .iter()
            .map(|modifier| result.arena.get(*modifier).unwrap().kind)
            .collect::<Vec<_>>();
        assert_eq!(
            modifier_kinds,
            [SyntaxKind::ExportKeyword, SyntaxKind::DefaultKeyword]
        );
    }

    #[test]
    fn parses_ambient_default_and_namespace_exports_without_recovery_diagnostics() {
        let source = concat!(
            "export default 2 + 2;\n",
            "export as namespace Foo;\n",
            "declare module \"indirect\" { export default typeof Foo.default; }\n",
        );
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 3);
        assert!(matches!(
            result.arena.get(statements[0]).unwrap().data,
            NodeData::ExportAssignment(_)
        ));
        let namespace_id = statements[1];
        let NodeData::NamespaceExportDeclaration(namespace) =
            &result.arena.get(namespace_id).unwrap().data
        else {
            panic!("expected namespace export declaration");
        };
        let NodeData::Identifier(name) = &result.arena.get(namespace.name).unwrap().data else {
            panic!("expected namespace export name");
        };
        assert_eq!(name.text, "Foo");
        assert_eq!(
            result.arena.get(namespace.name).unwrap().parent,
            Some(namespace_id)
        );
        assert_eq!(
            namespace
                .modifiers
                .as_ref()
                .unwrap()
                .list
                .nodes
                .iter()
                .map(|modifier| result.arena.get(*modifier).unwrap().kind)
                .collect::<Vec<_>>(),
            [SyntaxKind::ExportKeyword]
        );
        let NodeData::ModuleDeclaration(module) = &result.arena.get(statements[2]).unwrap().data
        else {
            panic!("expected ambient module");
        };
        let NodeData::ModuleBlock(block) = &result.arena.get(module.body.unwrap()).unwrap().data
        else {
            panic!("expected ambient module block");
        };
        assert!(matches!(
            result.arena.get(block.statements.nodes[0]).unwrap().data,
            NodeData::ExportAssignment(_)
        ));
    }

    #[test]
    fn preserves_default_export_declaration_forms() {
        let result = parse_source_file(concat!(
            "export default interface Shape {}\n",
            "export default class Model {}\n",
            "export default function make() {}\n",
        ));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(
            statements
                .iter()
                .map(|statement| result.arena.get(*statement).unwrap().kind)
                .collect::<Vec<_>>(),
            [
                SyntaxKind::InterfaceDeclaration,
                SyntaxKind::ClassDeclaration,
                SyntaxKind::FunctionDeclaration,
            ]
        );
        for statement in statements {
            let modifiers = match &result.arena.get(*statement).unwrap().data {
                NodeData::InterfaceDeclaration(declaration) => declaration.modifiers.as_ref(),
                NodeData::ClassDeclaration(declaration) => declaration.modifiers.as_ref(),
                NodeData::FunctionDeclaration(declaration) => declaration.modifiers.as_ref(),
                _ => None,
            }
            .unwrap();
            assert_eq!(
                modifiers
                    .list
                    .nodes
                    .iter()
                    .map(|modifier| result.arena.get(*modifier).unwrap().kind)
                    .collect::<Vec<_>>(),
                [SyntaxKind::ExportKeyword, SyntaxKind::DefaultKeyword]
            );
        }
    }

    #[test]
    fn parses_keyword_named_import_specifiers() {
        let result = parse_source_file("import { default as Foo } from \"./b\";");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let NodeData::ImportDeclaration(import) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
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
        let NodeData::NamedImports(imports) = &result
            .arena
            .get(clause.named_bindings.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected named imports");
        };
        let NodeData::ImportSpecifier(specifier) =
            &result.arena.get(imports.elements.nodes[0]).unwrap().data
        else {
            panic!("expected import specifier");
        };
        let NodeData::Identifier(property) = &result
            .arena
            .get(specifier.property_name.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected imported identifier name");
        };
        assert_eq!(property.text, "default");
    }

    #[test]
    fn parses_identifier_name_and_string_literal_import_names() {
        let result = parse_source_file(
            r#"import { default as DefaultThing, "source-name" as sourceName, class as classValue } from "./mod";"#,
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1);

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
        let NodeData::NamedImports(imports) = &result
            .arena
            .get(clause.named_bindings.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected named imports");
        };
        let imported_names = imports
            .elements
            .nodes
            .iter()
            .map(|specifier| {
                let NodeData::ImportSpecifier(specifier) =
                    &result.arena.get(*specifier).unwrap().data
                else {
                    panic!("expected import specifier");
                };
                (
                    result
                        .arena
                        .get(specifier.property_name.unwrap())
                        .unwrap()
                        .kind,
                    result.arena.get(specifier.name).unwrap().kind,
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            imported_names,
            [
                (SyntaxKind::Identifier, SyntaxKind::Identifier),
                (SyntaxKind::StringLiteral, SyntaxKind::Identifier),
                (SyntaxKind::Identifier, SyntaxKind::Identifier),
            ]
        );
    }

    #[test]
    fn parses_identifier_name_and_string_literal_export_names() {
        let result = parse_source_file(
            r#"
                export { zzz as default };
                export { default as zzz, zzz as "public-name", "source-name" as class } from "./mod";
            "#,
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);

        let NodeData::ExportDeclaration(export) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected export declaration");
        };
        let NodeData::NamedExports(exports) = &result
            .arena
            .get(export.export_clause.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected named exports");
        };
        let NodeData::ExportSpecifier(default_export) =
            &result.arena.get(exports.elements.nodes[0]).unwrap().data
        else {
            panic!("expected export specifier");
        };
        let NodeData::Identifier(exported_name) =
            &result.arena.get(default_export.name).unwrap().data
        else {
            panic!("expected exported identifier name");
        };
        assert_eq!(exported_name.text, "default");

        let NodeData::ExportDeclaration(export) = &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected export declaration");
        };
        let NodeData::NamedExports(exports) = &result
            .arena
            .get(export.export_clause.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected named exports");
        };
        let export_name_kinds = exports
            .elements
            .nodes
            .iter()
            .map(|specifier| {
                let NodeData::ExportSpecifier(specifier) =
                    &result.arena.get(*specifier).unwrap().data
                else {
                    panic!("expected export specifier");
                };
                (
                    result
                        .arena
                        .get(specifier.property_name.unwrap())
                        .unwrap()
                        .kind,
                    result.arena.get(specifier.name).unwrap().kind,
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            export_name_kinds,
            [
                (SyntaxKind::Identifier, SyntaxKind::Identifier),
                (SyntaxKind::Identifier, SyntaxKind::StringLiteral),
                (SyntaxKind::StringLiteral, SyntaxKind::Identifier),
            ]
        );
    }

    #[test]
    fn parses_export_equals_assignments() {
        let result = parse_source_file("export = runtimeValue;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let NodeData::ExportAssignment(assignment) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected export assignment");
        };
        assert!(assignment.is_export_equals);
        let NodeData::Identifier(expression) =
            &result.arena.get(assignment.expression).unwrap().data
        else {
            panic!("expected identifier expression");
        };
        assert_eq!(expression.text, "runtimeValue");
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
    fn parses_dotted_ambient_namespaces_as_nested_declarations() {
        let source = "declare namespace Foo.Bar { export var foo; }; Foo.Bar.foo = 5;";
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 3);
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::EmptyStatement
        );
        assert_eq!(
            result.arena.get(statements[2]).unwrap().kind,
            SyntaxKind::ExpressionStatement
        );

        let outer_id = statements[0];
        let outer_node = result.arena.get(outer_id).unwrap();
        let NodeData::ModuleDeclaration(outer) = &outer_node.data else {
            panic!("expected outer namespace");
        };
        assert_eq!(outer_node.range.start.get(), 0);
        assert_eq!(
            outer_node.range.end.get(),
            u32::try_from(source.find('}').unwrap()).unwrap() + 1
        );
        assert_eq!(result.arena.get(outer.name).unwrap().parent, Some(outer_id));
        let modifiers = outer.modifiers.as_ref().unwrap();
        assert_eq!(modifiers.list.nodes.len(), 1);
        assert_eq!(
            result.arena.get(modifiers.list.nodes[0]).unwrap().kind,
            SyntaxKind::DeclareKeyword
        );

        let inner_id = outer.body.unwrap();
        let inner_node = result.arena.get(inner_id).unwrap();
        let NodeData::ModuleDeclaration(inner) = &inner_node.data else {
            panic!("expected nested namespace");
        };
        assert_eq!(inner_node.parent, Some(outer_id));
        assert_eq!(
            inner_node.range.start.get(),
            u32::try_from(source.find("Bar").unwrap()).unwrap()
        );
        assert_eq!(inner_node.range.end, outer_node.range.end);
        assert!(inner.modifiers.is_none());
        assert_eq!(result.arena.get(inner.name).unwrap().parent, Some(inner_id));

        let block_id = inner.body.unwrap();
        let block_node = result.arena.get(block_id).unwrap();
        let NodeData::ModuleBlock(block) = &block_node.data else {
            panic!("expected nested namespace block");
        };
        assert_eq!(block_node.parent, Some(inner_id));
        assert_eq!(block.statements.nodes.len(), 1);
        assert_eq!(
            result.arena.get(block.statements.nodes[0]).unwrap().parent,
            Some(block_id)
        );
    }

    #[test]
    fn retains_namespace_recovery_after_a_missing_dotted_name() {
        let result = parse_source_file(
            "namespace Plain { const value = 1; } namespace Broken. { const recovered = 2; }",
        );
        assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        assert!(statements.iter().all(|statement| {
            result.arena.get(*statement).unwrap().kind == SyntaxKind::ModuleDeclaration
        }));
    }

    #[test]
    fn parses_labeled_debugger_and_with_statements() {
        let result =
            parse_source_file("outer: while (value) { debugger; break outer; } with (obj) value;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        assert_eq!(
            result.arena.get(statements[0]).unwrap().kind,
            SyntaxKind::LabeledStatement
        );
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::WithStatement
        );
        let NodeData::LabeledStatement(label) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected labeled statement");
        };
        let NodeData::WhileStatement(loop_) = &result.arena.get(label.statement).unwrap().data
        else {
            panic!("expected labeled loop");
        };
        let NodeData::Block(block) = &result.arena.get(loop_.statement).unwrap().data else {
            panic!("expected loop block");
        };
        assert_eq!(
            result.arena.get(block.statements.nodes[0]).unwrap().kind,
            SyntaxKind::DebuggerStatement
        );
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
    fn parses_const_enums_with_composed_modifiers() {
        let result = parse_source_file(
            r"
                const value = 1;
                const enum Local { A }
                declare const enum Ambient { A }
                export const enum Exported { A }
                export declare const enum ExportedAmbient { A }
            ",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(
            statements
                .iter()
                .map(|statement| result.arena.get(*statement).unwrap().kind)
                .collect::<Vec<_>>(),
            [
                SyntaxKind::VariableStatement,
                SyntaxKind::EnumDeclaration,
                SyntaxKind::EnumDeclaration,
                SyntaxKind::EnumDeclaration,
                SyntaxKind::EnumDeclaration,
            ]
        );

        for (statement, expected) in statements[1..].iter().zip([
            vec![SyntaxKind::ConstKeyword],
            vec![SyntaxKind::DeclareKeyword, SyntaxKind::ConstKeyword],
            vec![SyntaxKind::ExportKeyword, SyntaxKind::ConstKeyword],
            vec![
                SyntaxKind::ExportKeyword,
                SyntaxKind::DeclareKeyword,
                SyntaxKind::ConstKeyword,
            ],
        ]) {
            let NodeData::EnumDeclaration(data) = &result.arena.get(*statement).unwrap().data
            else {
                panic!("expected enum declaration");
            };
            let modifiers = data.modifiers.as_ref().unwrap();
            assert_eq!(
                modifiers
                    .list
                    .nodes
                    .iter()
                    .map(|modifier| result.arena.get(*modifier).unwrap().kind)
                    .collect::<Vec<_>>(),
                expected
            );
            for modifier in &modifiers.list.nodes {
                assert_eq!(
                    result.arena.get(*modifier).unwrap().parent,
                    Some(*statement)
                );
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn parses_class_and_type_member_property_names() {
        let source = r#"
            declare class BaseClass {
                static extends<A>(a: A): new () => A & BaseClass;
                static<T>(): T;
                async(): void;
                "quoted"<T>(value: T): T;
                0(): void;
                [computed]<T>(value: T): T;
                get value(): string;
                set value(next: string);
                get(): void;
            }
            interface Members {
                readonly(): void;
                readonly: string;
                "quoted"<T>(value: T): T;
                1: number;
                [computed]<T>(value: T): T;
                get value(): string;
                set value(next: string);
                get(): void;
            }
        "#;
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);

        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 9);
        let NodeData::MethodDeclaration(extends_method) =
            &result.arena.get(class.members.nodes[0]).unwrap().data
        else {
            panic!("expected static generic method");
        };
        let NodeData::Identifier(extends_name) =
            &result.arena.get(extends_method.name).unwrap().data
        else {
            panic!("expected keyword method name to be an identifier");
        };
        assert_eq!(extends_name.text, "extends");
        assert_eq!(
            extends_method
                .modifiers
                .as_ref()
                .unwrap()
                .list
                .nodes
                .iter()
                .map(|modifier| result.arena.get(*modifier).unwrap().kind)
                .collect::<Vec<_>>(),
            [SyntaxKind::StaticKeyword]
        );
        let type_parameters = extends_method.type_parameters.as_ref().unwrap();
        assert_eq!(type_parameters.nodes.len(), 1);
        assert_eq!(
            result.arena.get(type_parameters.nodes[0]).unwrap().parent,
            Some(class.members.nodes[0])
        );

        let class_name_kinds = class.members.nodes[..6]
            .iter()
            .map(|member| match &result.arena.get(*member).unwrap().data {
                NodeData::MethodDeclaration(method) => result.arena.get(method.name).unwrap().kind,
                _ => panic!("expected method declaration"),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            class_name_kinds,
            [
                SyntaxKind::Identifier,
                SyntaxKind::Identifier,
                SyntaxKind::Identifier,
                SyntaxKind::StringLiteral,
                SyntaxKind::NumericLiteral,
                SyntaxKind::ComputedPropertyName,
            ]
        );
        let NodeData::MethodDeclaration(static_name) =
            &result.arena.get(class.members.nodes[1]).unwrap().data
        else {
            panic!("expected static-named method");
        };
        assert!(static_name.modifiers.is_none());
        let NodeData::Identifier(static_name) = &result.arena.get(static_name.name).unwrap().data
        else {
            panic!("expected identifier name");
        };
        assert_eq!(static_name.text, "static");
        assert!(matches!(
            result.arena.get(class.members.nodes[6]).unwrap().data,
            NodeData::GetAccessorDeclaration(_)
        ));
        assert!(matches!(
            result.arena.get(class.members.nodes[7]).unwrap().data,
            NodeData::SetAccessorDeclaration(_)
        ));
        let NodeData::MethodDeclaration(get_method) =
            &result.arena.get(class.members.nodes[8]).unwrap().data
        else {
            panic!("expected get-named method");
        };
        assert_eq!(
            result.arena.get(get_method.name).unwrap().kind,
            SyntaxKind::Identifier
        );

        let NodeData::InterfaceDeclaration(interface) =
            &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected interface declaration");
        };
        assert_eq!(interface.members.nodes.len(), 8);
        let NodeData::MethodSignatureDeclaration(readonly_method) =
            &result.arena.get(interface.members.nodes[0]).unwrap().data
        else {
            panic!("expected readonly-named method");
        };
        assert!(readonly_method.modifiers.is_none());
        let NodeData::PropertyDeclaration(readonly_property) =
            &result.arena.get(interface.members.nodes[1]).unwrap().data
        else {
            panic!("expected readonly-named property");
        };
        assert!(readonly_property.modifiers.is_none());
        assert_eq!(
            interface.members.nodes[2..5]
                .iter()
                .map(|member| match &result.arena.get(*member).unwrap().data {
                    NodeData::MethodSignatureDeclaration(method) => {
                        result.arena.get(method.name).unwrap().kind
                    }
                    NodeData::PropertyDeclaration(property) => {
                        result.arena.get(property.name).unwrap().kind
                    }
                    _ => panic!("expected named type member"),
                })
                .collect::<Vec<_>>(),
            [
                SyntaxKind::StringLiteral,
                SyntaxKind::NumericLiteral,
                SyntaxKind::ComputedPropertyName,
            ]
        );
        assert!(matches!(
            result.arena.get(interface.members.nodes[5]).unwrap().data,
            NodeData::GetAccessorDeclaration(_)
        ));
        assert!(matches!(
            result.arena.get(interface.members.nodes[6]).unwrap().data,
            NodeData::SetAccessorDeclaration(_)
        ));
        assert!(matches!(
            result.arena.get(interface.members.nodes[7]).unwrap().data,
            NodeData::MethodSignatureDeclaration(_)
        ));

        let value_access = parse_source_file(
            "const ExtendedClass = BaseClass.extends({ f: function() { return 'ok'; } }); const module = {}; module.exports = ExtendedClass;",
        );
        assert!(
            value_access.diagnostics.is_empty(),
            "{:?}",
            value_access.diagnostics
        );
    }

    #[test]
    fn recovers_after_a_generic_class_method_missing_parameters() {
        let result =
            parse_source_file("class Broken { static extends<T>; \"after\"() {} } const done = 1;");
        assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
        assert_eq!(result.diagnostics[0].code, Some(1005));
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 2);
        assert_eq!(
            result.arena.get(class.members.nodes[1]).unwrap().kind,
            SyntaxKind::MethodDeclaration
        );
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::VariableStatement
        );
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
    fn parses_assertion_predicates_in_functions_methods_and_properties() {
        let result = parse_source_file(
            r"
                declare function assertTruth(value: unknown): asserts value;
                function assertType<T>(value: unknown): asserts value is T {}
                interface Assertions {
                    assert(value: unknown): asserts value is string;
                    property: (value: unknown) => asserts value;
                }
            ",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let predicates = result
            .arena
            .iter()
            .filter_map(|(id, node)| {
                let NodeData::TypePredicateNode(predicate) = &node.data else {
                    return None;
                };
                Some((id, predicate))
            })
            .collect::<Vec<_>>();
        assert_eq!(predicates.len(), 4);
        assert_eq!(
            predicates
                .iter()
                .filter(|(_, predicate)| predicate.type_.is_some())
                .count(),
            2
        );
        for (predicate_id, predicate) in predicates {
            let asserts = predicate.asserts_modifier.expect("assertion modifier");
            assert_eq!(
                result.arena.get(asserts).unwrap().kind,
                SyntaxKind::AssertsKeyword
            );
            assert_eq!(
                result.arena.get(asserts).unwrap().parent,
                Some(predicate_id)
            );
            assert_eq!(
                result.arena.get(predicate.parameter_name).unwrap().parent,
                Some(predicate_id)
            );
        }
    }

    #[test]
    fn parses_asserts_as_a_namespace_import_binding_and_expression() {
        let result = parse_source_file(
            r#"
                import * as asserts from "./asserts";
                function test(value: unknown): void {
                    asserts.isNonNullable(value);
                }
            "#,
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        let NodeData::ImportDeclaration(import) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected import declaration");
        };
        let NodeData::ImportClause(clause) = &result
            .arena
            .get(import.import_clause.expect("import clause"))
            .unwrap()
            .data
        else {
            panic!("expected import clause");
        };
        let NodeData::NamespaceImport(namespace_import) = &result
            .arena
            .get(clause.named_bindings.expect("namespace import"))
            .unwrap()
            .data
        else {
            panic!("expected namespace import");
        };
        let NodeData::Identifier(name) = &result.arena.get(namespace_import.name).unwrap().data
        else {
            panic!("expected namespace import identifier");
        };
        assert_eq!(name.text, "asserts");

        let NodeData::FunctionDeclaration(function) =
            &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected function declaration");
        };
        let NodeData::Block(body) = &result
            .arena
            .get(function.body.expect("function body"))
            .unwrap()
            .data
        else {
            panic!("expected function body");
        };
        let NodeData::ExpressionStatement(statement) =
            &result.arena.get(body.statements.nodes[0]).unwrap().data
        else {
            panic!("expected expression statement");
        };
        assert_eq!(
            result.arena.get(statement.expression).unwrap().kind,
            SyntaxKind::CallExpression
        );
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
    fn parses_exported_import_equals_declarations() {
        let result = parse_source_file(
            r#"
                import alias = require("foo");
                export import cls2 = alias.Class;
                namespace M { export import cls = alias.Class; }
            "#,
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);

        let assert_exported_alias = |declaration: NodeId| {
            let NodeData::ImportEqualsDeclaration(data) =
                &result.arena.get(declaration).unwrap().data
            else {
                panic!("expected import-equals declaration");
            };
            let modifiers = data.modifiers.as_ref().unwrap();
            assert_eq!(modifiers.list.nodes.len(), 1);
            assert_eq!(
                result.arena.get(modifiers.list.nodes[0]).unwrap().kind,
                SyntaxKind::ExportKeyword
            );
            assert_eq!(
                result.arena.get(modifiers.list.nodes[0]).unwrap().parent,
                Some(declaration)
            );
            assert_eq!(
                result.arena.get(data.module_reference).unwrap().kind,
                SyntaxKind::QualifiedName
            );
        };

        assert_exported_alias(statements[1]);
        let NodeData::ModuleDeclaration(module) = &result.arena.get(statements[2]).unwrap().data
        else {
            panic!("expected namespace declaration");
        };
        let NodeData::ModuleBlock(block) = &result.arena.get(module.body.unwrap()).unwrap().data
        else {
            panic!("expected namespace block");
        };
        assert_exported_alias(block.statements.nodes[0]);
    }

    #[test]
    fn parses_undefined_as_an_import_equals_entity_name() {
        let result = parse_source_file("import value = undefined;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1);
        let NodeData::ImportEqualsDeclaration(import) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected import-equals declaration");
        };
        let NodeData::Identifier(reference) =
            &result.arena.get(import.module_reference).unwrap().data
        else {
            panic!("expected identifier module reference");
        };
        assert_eq!(reference.text, "undefined");
    }

    #[test]
    fn rescans_regular_expression_literals_in_expression_contexts() {
        let result = parse_source_file("const first = /a[b\\/]c+/giu; const second = /=foo/;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let expected = ["/a[b\\/]c+/giu", "/=foo/"];
        for (statement, expected) in statements.iter().zip(expected) {
            let (list, _) = variable_list(&result, *statement);
            let declaration = declaration_nodes(&result, list)[0];
            let NodeData::VariableDeclaration(declaration) =
                &result.arena.get(declaration).unwrap().data
            else {
                panic!("expected variable declaration");
            };
            let initializer = result.arena.get(declaration.initializer.unwrap()).unwrap();
            let NodeData::RegularExpressionLiteral(regex) = &initializer.data else {
                panic!("expected regular expression literal");
            };
            assert_eq!(regex.text, expected);
        }
    }

    #[test]
    fn parses_named_generator_and_anonymous_function_expressions() {
        let result = parse_source_file(
            "const callback = function (value: number): number { return value; }; const generator = function* named() { yield 1; };",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        for statement in statements {
            let (list, _) = variable_list(&result, *statement);
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
                SyntaxKind::FunctionExpression
            );
        }
    }

    #[test]
    fn parses_async_generator_declarations_and_expressions_with_parent_links() {
        let source = concat!(
            "async function * declared(source) { yield source; yield* source; } ",
            "const expression = async function* named() { yield; };",
        );
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);

        let declaration_id = statements[0];
        let declaration_node = result.arena.get(declaration_id).unwrap();
        let NodeData::FunctionDeclaration(declaration) = &declaration_node.data else {
            panic!("expected async generator declaration");
        };
        assert_eq!(
            &source[declaration_node.range.start.get() as usize
                ..declaration_node.range.end.get() as usize],
            "async function * declared(source) { yield source; yield* source; }"
        );
        let declaration_modifier = declaration.modifiers.as_ref().unwrap().list.nodes[0];
        assert_eq!(
            result.arena.get(declaration_modifier).unwrap().kind,
            SyntaxKind::AsyncKeyword
        );
        assert_eq!(
            result.arena.get(declaration_modifier).unwrap().parent,
            Some(declaration_id)
        );
        assert_eq!(
            result
                .arena
                .get(declaration.asterisk_token.unwrap())
                .unwrap()
                .parent,
            Some(declaration_id)
        );
        assert_eq!(
            result.arena.get(declaration.body.unwrap()).unwrap().parent,
            Some(declaration_id)
        );

        let (list, _) = variable_list(&result, statements[1]);
        let variable = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(variable) = &result.arena.get(variable).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let expression_id = variable.initializer.unwrap();
        let expression_node = result.arena.get(expression_id).unwrap();
        let NodeData::FunctionExpression(expression) = &expression_node.data else {
            panic!("expected async generator expression");
        };
        assert_eq!(
            &source[expression_node.range.start.get() as usize
                ..expression_node.range.end.get() as usize],
            "async function* named() { yield; }"
        );
        let expression_modifier = expression.modifiers.as_ref().unwrap().list.nodes[0];
        for child in [
            expression_modifier,
            expression.asterisk_token.unwrap(),
            expression.body,
        ] {
            assert_eq!(result.arena.get(child).unwrap().parent, Some(expression_id));
        }

        let yields = result
            .arena
            .iter()
            .filter_map(|(id, node)| (node.kind == SyntaxKind::YieldExpression).then_some(id))
            .collect::<Vec<_>>();
        assert_eq!(yields.len(), 3);
        let delegated = yields
            .into_iter()
            .find(|yield_id| {
                matches!(
                    &result.arena.get(*yield_id).unwrap().data,
                    NodeData::YieldExpression(yield_expression)
                        if yield_expression.asterisk_token.is_some()
                )
            })
            .expect("expected delegated yield");
        let NodeData::YieldExpression(delegated_yield) = &result.arena.get(delegated).unwrap().data
        else {
            unreachable!();
        };
        assert_eq!(
            result
                .arena
                .get(delegated_yield.asterisk_token.unwrap())
                .unwrap()
                .parent,
            Some(delegated)
        );
    }

    #[test]
    fn recovers_after_an_async_generator_expression_missing_its_body() {
        let result = parse_source_file("const broken = async function* named(); const after = 1;");
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1005))
        );
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2, "{:?}", result.diagnostics);
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::VariableStatement
        );

        let (list, _) = variable_list(&result, statements[0]);
        let variable = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(variable) = &result.arena.get(variable).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let expression = variable.initializer.unwrap();
        let NodeData::FunctionExpression(function) = &result.arena.get(expression).unwrap().data
        else {
            panic!("expected recovered function expression");
        };
        let body = result.arena.get(function.body).unwrap();
        assert_eq!(body.kind, SyntaxKind::Block);
        assert_eq!(body.range.start, body.range.end);
        assert_eq!(body.parent, Some(expression));
    }

    #[test]
    fn parses_anonymous_and_named_class_expressions_with_parent_links() {
        let result = parse_source_file(
            "const Anonymous = class extends Base { method() {} }; const Named = class Inner<T> extends Base { value = 1; }; const Kind = typeof class {};",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);

        let class_expression = |statement| {
            let (list, _) = variable_list(&result, statement);
            let declaration = declaration_nodes(&result, list)[0];
            let NodeData::VariableDeclaration(declaration) =
                &result.arena.get(declaration).unwrap().data
            else {
                panic!("expected variable declaration");
            };
            declaration.initializer.unwrap()
        };

        let anonymous_id = class_expression(statements[0]);
        let NodeData::ClassExpression(anonymous) = &result.arena.get(anonymous_id).unwrap().data
        else {
            panic!("expected anonymous class expression");
        };
        assert!(anonymous.name.is_none());
        for child in anonymous
            .heritage_clauses
            .iter()
            .flat_map(|clauses| &clauses.nodes)
            .chain(&anonymous.members.nodes)
        {
            assert_eq!(result.arena.get(*child).unwrap().parent, Some(anonymous_id));
        }

        let named_id = class_expression(statements[1]);
        let NodeData::ClassExpression(named) = &result.arena.get(named_id).unwrap().data else {
            panic!("expected named class expression");
        };
        let name = named.name.unwrap();
        let NodeData::Identifier(name_data) = &result.arena.get(name).unwrap().data else {
            panic!("expected class expression name");
        };
        assert_eq!(name_data.text, "Inner");
        assert_eq!(result.arena.get(name).unwrap().parent, Some(named_id));
        for child in named
            .type_parameters
            .iter()
            .flat_map(|parameters| &parameters.nodes)
            .chain(
                named
                    .heritage_clauses
                    .iter()
                    .flat_map(|clauses| &clauses.nodes),
            )
            .chain(&named.members.nodes)
        {
            assert_eq!(result.arena.get(*child).unwrap().parent, Some(named_id));
        }

        let typeof_id = class_expression(statements[2]);
        let NodeData::TypeOfExpression(typeof_expression) =
            &result.arena.get(typeof_id).unwrap().data
        else {
            panic!("expected typeof expression");
        };
        let class_id = typeof_expression.expression;
        assert!(matches!(
            result.arena.get(class_id).unwrap().data,
            NodeData::ClassExpression(_)
        ));
        assert_eq!(result.arena.get(class_id).unwrap().parent, Some(typeof_id));
    }

    #[test]
    fn parses_call_expressions_in_class_heritage() {
        let source = "class User {} class TimestampedUser extends Timestamped(User) { constructor() { super(); } }";
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let class_id = statements[1];
        let NodeData::ClassDeclaration(class) = &result.arena.get(class_id).unwrap().data else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 1);
        let clause_id = class.heritage_clauses.as_ref().unwrap().nodes[0];
        assert_eq!(result.arena.get(clause_id).unwrap().parent, Some(class_id));
        let NodeData::HeritageClause(clause) = &result.arena.get(clause_id).unwrap().data else {
            panic!("expected heritage clause");
        };
        let heritage_id = clause.types.nodes[0];
        assert_eq!(
            result.arena.get(heritage_id).unwrap().parent,
            Some(clause_id)
        );
        let NodeData::ExpressionWithTypeArguments(heritage) =
            &result.arena.get(heritage_id).unwrap().data
        else {
            panic!("expected heritage expression");
        };
        let call_id = heritage.expression;
        assert_eq!(result.arena.get(call_id).unwrap().parent, Some(heritage_id));
        let NodeData::CallExpression(call) = &result.arena.get(call_id).unwrap().data else {
            panic!("expected call expression");
        };
        assert_eq!(call.arguments.nodes.len(), 1);
        assert_eq!(
            result.arena.get(call.expression).unwrap().parent,
            Some(call_id)
        );
        assert_eq!(
            result.arena.get(call.arguments.nodes[0]).unwrap().parent,
            Some(call_id)
        );
        let range = result.arena.get(call_id).unwrap().range;
        assert_eq!(
            &source[usize::try_from(range.start.get()).unwrap()
                ..usize::try_from(range.end.get()).unwrap()],
            "Timestamped(User)"
        );

        let generic = parse_source_file("interface Derived<T> extends ns.Base<T> {} ");
        assert!(generic.diagnostics.is_empty(), "{:?}", generic.diagnostics);
        let generic_statement = source_statements(&generic)[0];
        let NodeData::InterfaceDeclaration(interface) =
            &generic.arena.get(generic_statement).unwrap().data
        else {
            panic!("expected interface declaration");
        };
        let clause_id = interface.heritage_clauses.as_ref().unwrap().nodes[0];
        let NodeData::HeritageClause(clause) = &generic.arena.get(clause_id).unwrap().data else {
            panic!("expected heritage clause");
        };
        let heritage_id = clause.types.nodes[0];
        let NodeData::ExpressionWithTypeArguments(heritage) =
            &generic.arena.get(heritage_id).unwrap().data
        else {
            panic!("expected heritage expression");
        };
        assert!(matches!(
            generic.arena.get(heritage.expression).unwrap().data,
            NodeData::QualifiedName(_)
        ));
        assert_eq!(heritage.type_arguments.as_ref().unwrap().nodes.len(), 1);
    }

    #[test]
    fn recovers_after_a_class_expression_missing_its_body() {
        let result = parse_source_file("const Broken = class Named; const after = 1;");
        assert!(!result.diagnostics.is_empty());
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2, "{:?}", result.diagnostics);
        let (first_list, _) = variable_list(&result, statements[0]);
        let first_declaration = declaration_nodes(&result, first_list)[0];
        let NodeData::VariableDeclaration(first_declaration) =
            &result.arena.get(first_declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        assert_eq!(
            result
                .arena
                .get(first_declaration.initializer.unwrap())
                .unwrap()
                .kind,
            SyntaxKind::ClassExpression
        );
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::VariableStatement
        );
    }

    #[test]
    fn parses_contextual_keyword_spellings_as_value_identifiers() {
        let result = parse_source_file(
            "function read(symbol: symbol, type: string) { if (!symbol) return; if (!type) return; return symbol; }",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let NodeData::FunctionDeclaration(function) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected function declaration");
        };
        let NodeData::Block(body) = &result.arena.get(function.body.unwrap()).unwrap().data else {
            panic!("expected function body");
        };
        let NodeData::IfStatement(if_statement) =
            &result.arena.get(body.statements.nodes[0]).unwrap().data
        else {
            panic!("expected if statement");
        };
        let NodeData::PrefixUnaryExpression(condition) =
            &result.arena.get(if_statement.expression).unwrap().data
        else {
            panic!("expected prefix condition");
        };
        assert_eq!(
            result.arena.get(condition.operand).unwrap().kind,
            SyntaxKind::Identifier
        );
    }

    #[test]
    fn parses_delete_expressions() {
        let result = parse_source_file("delete value.optional; delete value['indexed'];");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let delete_expressions = result
            .arena
            .iter()
            .filter(|(_, node)| node.kind == SyntaxKind::DeleteExpression)
            .collect::<Vec<_>>();
        assert_eq!(delete_expressions.len(), 2);
        for (_, node) in delete_expressions {
            let NodeData::DeleteExpression(delete) = &node.data else {
                panic!("expected delete expression");
            };
            assert!(matches!(
                result.arena.get(delete.expression).unwrap().kind,
                SyntaxKind::PropertyAccessExpression | SyntaxKind::ElementAccessExpression
            ));
        }
    }

    #[test]
    fn keeps_keyword_named_interfaces_as_single_erased_declarations() {
        let result = parse_source_file("interface string {}");
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2427]
        );
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1);
        let NodeData::InterfaceDeclaration(interface) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected interface declaration");
        };
        let NodeData::Identifier(name) = &result.arena.get(interface.name).unwrap().data else {
            panic!("expected interface name");
        };
        assert_eq!(name.text, "string");
    }

    #[test]
    fn recovers_variable_and_arrow_statements_after_a_malformed_class_member() {
        let result = parse_source_file(
            "class C { public const var export foo = 10; var constructor() { } }",
        );
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [1440, 1068, 1005, 1005, 1128]
        );
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 3, "{:?}", result.diagnostics);
        assert_eq!(
            statements
                .iter()
                .map(|statement| result.arena.get(*statement).unwrap().kind)
                .collect::<Vec<_>>(),
            [
                SyntaxKind::ClassDeclaration,
                SyntaxKind::VariableStatement,
                SyntaxKind::ExpressionStatement,
            ]
        );
        let NodeData::ExpressionStatement(statement) =
            &result.arena.get(statements[2]).unwrap().data
        else {
            panic!("expected expression statement");
        };
        assert_eq!(
            result.arena.get(statement.expression).unwrap().kind,
            SyntaxKind::ArrowFunction
        );
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
    fn parses_dotted_jsx_member_tag_names() {
        let result = parse_jsx_source_file("const view = <UI.Controls.Button />;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let identifier = |node| match &result.arena.get(node).unwrap().data {
            NodeData::Identifier(identifier) => identifier.text.as_str(),
            _ => panic!("expected identifier"),
        };
        let (list, _) = variable_list(&result, source_statements(&result)[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected declaration");
        };
        let NodeData::JsxSelfClosingElement(element) = &result
            .arena
            .get(declaration.initializer.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected self-closing JSX element");
        };
        let NodeData::PropertyAccessExpression(button) =
            &result.arena.get(element.tag_name).unwrap().data
        else {
            panic!("expected member tag name");
        };
        assert_eq!(identifier(button.name), "Button");
        let NodeData::PropertyAccessExpression(controls) =
            &result.arena.get(button.expression).unwrap().data
        else {
            panic!("expected nested member tag name");
        };
        assert_eq!(identifier(controls.name), "Controls");
        assert_eq!(identifier(controls.expression), "UI");

        let custom = parse_jsx_source_file("const view = <my-widget data-id='x' />;");
        assert!(custom.diagnostics.is_empty(), "{:?}", custom.diagnostics);
    }

    #[test]
    fn parses_jsdoc_text_and_tag_names() {
        let source = "/** Summary\n * @custom value\n */";
        let result = parse_jsdoc_comment(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert_eq!(result.arena.source_text(), Some(source));
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
    fn function_expressions_in_case_statements_make_progress() {
        let result = parse_source_file(
            "switch (x) { case 1: (function() { return x }); break; } const done = 1;",
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
    fn preserves_omitted_array_binding_elements_and_their_comma_positions() {
        let source = concat!(
            "let [, b, , a] = results;\n",
            "function f([, a, , b, , , ] = results) {}\n",
        );
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);

        let (list, _) = variable_list(&result, statements[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let NodeData::BindingPattern(pattern) = &result.arena.get(declaration.name).unwrap().data
        else {
            panic!("expected array binding pattern");
        };
        assert_eq!(pattern.elements.nodes.len(), 4);
        assert_eq!(
            pattern
                .elements
                .nodes
                .iter()
                .map(|element| result.arena.get(*element).unwrap().kind)
                .collect::<Vec<_>>(),
            [
                SyntaxKind::OmittedExpression,
                SyntaxKind::BindingElement,
                SyntaxKind::OmittedExpression,
                SyntaxKind::BindingElement,
            ]
        );
        for omitted in [pattern.elements.nodes[0], pattern.elements.nodes[2]] {
            let node = result.arena.get(omitted).unwrap();
            assert_eq!(node.range.start, node.range.end);
            assert_eq!(source.as_bytes()[node.range.start.get() as usize], b',');
            assert_eq!(node.parent, Some(declaration.name));
        }

        let NodeData::FunctionDeclaration(function) =
            &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected function declaration");
        };
        let NodeData::ParameterDeclaration(parameter) =
            &result.arena.get(function.parameters.nodes[0]).unwrap().data
        else {
            panic!("expected parameter");
        };
        let NodeData::BindingPattern(pattern) = &result.arena.get(parameter.name).unwrap().data
        else {
            panic!("expected array binding pattern");
        };
        assert_eq!(
            pattern
                .elements
                .nodes
                .iter()
                .filter(|element| {
                    result.arena.get(**element).unwrap().kind == SyntaxKind::OmittedExpression
                })
                .count(),
            4
        );
        assert!(pattern.elements.has_trailing_comma);
    }

    #[test]
    fn applies_asi_to_line_broken_contextual_declaration_and_member_keywords() {
        let source = concat!(
            "abstract\nclass A {}\n",
            "public\nclass B {}\n",
            "private\nclass D {}\n",
            "protected\nclass E {}\n",
            "class C { abstract\nmethod() {} public\nprivate other() {} }\n",
        );
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 9);
        for (index, keyword) in ["abstract", "public", "private", "protected"]
            .into_iter()
            .enumerate()
        {
            let statement = statements[index * 2];
            let NodeData::ExpressionStatement(expression) =
                &result.arena.get(statement).unwrap().data
            else {
                panic!("expected contextual keyword expression");
            };
            let NodeData::Identifier(identifier) =
                &result.arena.get(expression.expression).unwrap().data
            else {
                panic!("expected contextual keyword identifier");
            };
            assert_eq!(identifier.text, keyword);
            let range = result.arena.get(statement).unwrap().range;
            assert_eq!(
                &source[range.start.get() as usize..range.end.get() as usize],
                keyword
            );
        }

        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[8]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 4);
        assert_eq!(
            class
                .members
                .nodes
                .iter()
                .map(|member| result.arena.get(*member).unwrap().kind)
                .collect::<Vec<_>>(),
            [
                SyntaxKind::PropertyDeclaration,
                SyntaxKind::MethodDeclaration,
                SyntaxKind::PropertyDeclaration,
                SyntaxKind::MethodDeclaration,
            ]
        );
    }

    #[test]
    fn keeps_line_broken_arithmetic_as_one_binary_with_nested_prefix_operands() {
        let source = "var z =\nx\n+\n+\n+\ny;\nvar c =\nx\n-\n-\n-\ny;";
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);

        for (statement, operator) in statements
            .iter()
            .copied()
            .zip([SyntaxKind::PlusToken, SyntaxKind::MinusToken])
        {
            let (list, _) = variable_list(&result, statement);
            let declaration = declaration_nodes(&result, list)[0];
            let NodeData::VariableDeclaration(declaration) =
                &result.arena.get(declaration).unwrap().data
            else {
                panic!("expected variable declaration");
            };
            let initializer = declaration.initializer.unwrap();
            let NodeData::BinaryExpression(binary) = &result.arena.get(initializer).unwrap().data
            else {
                panic!("expected binary expression");
            };
            assert_eq!(
                result.arena.get(binary.operator_token).unwrap().kind,
                operator
            );
            let NodeData::PrefixUnaryExpression(first_prefix) =
                &result.arena.get(binary.right).unwrap().data
            else {
                panic!("expected first prefix expression");
            };
            assert_eq!(first_prefix.operator, operator);
            let NodeData::PrefixUnaryExpression(second_prefix) =
                &result.arena.get(first_prefix.operand).unwrap().data
            else {
                panic!("expected second prefix expression");
            };
            assert_eq!(second_prefix.operator, operator);
            assert_eq!(
                result.arena.get(second_prefix.operand).unwrap().kind,
                SyntaxKind::Identifier
            );
            let range = result.arena.get(initializer).unwrap().range;
            assert_eq!(source.as_bytes()[range.start.get() as usize], b'x');
            assert_eq!(source.as_bytes()[range.end.get() as usize - 1], b'y');
        }
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

    #[test]
    fn parses_type_argument_expression_suffixes_and_definite_assignment_declarations() {
        let result = parse_source_file(concat!(
            "Object.create<Object>(\"\");\n",
            "obj.fn<number> = value;\n",
            "let getValue!: <T>() => T;\n",
            "getValue<number> = value;\n",
        ));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let statements = source_statements(&result);
        assert_eq!(statements.len(), 4);

        let NodeData::ExpressionStatement(call_statement) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected call expression statement");
        };
        let NodeData::CallExpression(call) =
            &result.arena.get(call_statement.expression).unwrap().data
        else {
            panic!("expected generic call expression");
        };
        assert_eq!(call.type_arguments.as_ref().unwrap().nodes.len(), 1);

        for statement in [statements[1], statements[3]] {
            let NodeData::ExpressionStatement(statement) =
                &result.arena.get(statement).unwrap().data
            else {
                panic!("expected assignment statement");
            };
            let NodeData::BinaryExpression(assignment) =
                &result.arena.get(statement.expression).unwrap().data
            else {
                panic!("expected assignment expression");
            };
            assert_eq!(
                result.arena.get(assignment.left).unwrap().kind,
                SyntaxKind::ParenthesizedExpression
            );
        }

        let (list, _) = variable_list(&result, statements[2]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        assert!(declaration.exclamation_token.is_some());
    }

    fn source_statements(result: &ParseResult) -> &[NodeId] {
        let source = result.arena.get(result.source_file).unwrap();
        let NodeData::SourceFile(data) = &source.data else {
            panic!("expected source file");
        };
        &data.statements.nodes
    }

    #[test]
    fn parses_typed_async_arrows_and_assignment_for_initializers() {
        let result = parse_source_file(concat!(
            "const f = async (): Promise<void> => {};\n",
            "for (i = 1; i < limit; ++i) {}\n",
            "for (key in value) {}\n",
        ));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert!(result.arena.iter().any(|(_, node)| {
            matches!(
                &node.data,
                NodeData::ArrowFunction(arrow)
                    if arrow.type_.is_some() && arrow.modifiers.is_some()
            )
        }));
        let for_statements = result
            .arena
            .iter()
            .filter_map(|(_, node)| match &node.data {
                NodeData::ForStatement(for_) => Some(for_),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(for_statements.len(), 1);
        let initializer = for_statements[0].initializer.expect("initializer");
        assert_eq!(
            result.arena.get(initializer).unwrap().kind,
            SyntaxKind::BinaryExpression
        );
        assert!(
            result
                .arena
                .iter()
                .any(|(_, node)| matches!(node.data, NodeData::ForInOrOfStatement(_)))
        );
    }

    fn find_descendant_kind(
        result: &ParseResult,
        ancestor: NodeId,
        kind: SyntaxKind,
    ) -> Option<NodeId> {
        result.arena.iter().find_map(|(id, node)| {
            if node.kind != kind {
                return None;
            }
            let mut parent = node.parent;
            while let Some(current) = parent {
                if current == ancestor {
                    return Some(id);
                }
                parent = result.arena.get(current).and_then(|node| node.parent);
            }
            None
        })
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
