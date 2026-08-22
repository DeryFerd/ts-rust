//! TypeScript parser.

use ts_ast::{
    ArrayLiteralExpressionData, ArrayTypeNodeData, ArrowFunctionData, AsExpressionData,
    AwaitExpressionData, BigIntLiteralData, BinaryExpressionData, BindingElementData,
    BindingPatternData, BlockData, BreakStatementData, CallExpressionData,
    CallSignatureDeclarationData, CaseBlockData, CaseOrDefaultClauseData, CatchClauseData,
    ClassDeclarationData, ClassExpressionData, ClassStaticBlockDeclarationData,
    ComputedPropertyNameData, ConditionalExpressionData, ConditionalTypeNodeData,
    ConstructSignatureDeclarationData, ConstructorDeclarationData, ConstructorTypeNodeData,
    ContinueStatementData, DebuggerStatementData, DecoratorData, DeleteExpressionData,
    DoStatementData, ElementAccessExpressionData, EmptyStatementData, EnumDeclarationData,
    EnumMemberData, ExportAssignmentData, ExportDeclarationData, ExportSpecifierData,
    ExpressionStatementData, ExpressionWithTypeArgumentsData, ExternalModuleReferenceData,
    ForInOrOfStatementData, ForStatementData, FunctionDeclarationData, FunctionExpressionData,
    FunctionTypeNodeData, GetAccessorDeclarationData, HeritageClauseData, IdentifierData,
    IfStatementData, ImportAttributeData, ImportAttributesData, ImportClauseData,
    ImportDeclarationData, ImportEqualsDeclarationData, ImportSpecifierData, ImportTypeNodeData,
    IndexSignatureDeclarationData, IndexedAccessTypeNodeData, InferTypeNodeData,
    InterfaceDeclarationData, IntersectionTypeNodeData, JsDocAllTypeData, JsDocData,
    JsDocNonNullableTypeData, JsDocNullableTypeData, JsDocTextData, JsDocUnknownTagData,
    JsxAttributeData, JsxAttributesData, JsxClosingElementData, JsxClosingFragmentData,
    JsxElementData, JsxExpressionData, JsxFragmentData, JsxNamespacedNameData,
    JsxOpeningElementData, JsxOpeningFragmentData, JsxSelfClosingElementData,
    JsxSpreadAttributeData, JsxTextData, KeywordExpressionData, KeywordTypeNodeData,
    LabeledStatementData, LiteralTypeNodeData, MappedTypeNodeData, MetaPropertyData,
    MethodDeclarationData, MethodSignatureDeclarationData, ModifierList, ModuleBlockData,
    ModuleDeclarationData, NamedExportsData, NamedImportsData, NamedTupleMemberData,
    NamespaceExportData, NamespaceExportDeclarationData, NamespaceImportData, NewExpressionData,
    NoSubstitutionTemplateLiteralData, Node, NodeArena, NodeData, NodeFlags, NodeId, NodeList,
    NonNullExpressionData, NotEmittedStatementData, NumericLiteralData,
    ObjectLiteralExpressionData, OmittedExpressionData, OptionalTypeNodeData,
    ParameterDeclarationData, ParenthesizedExpressionData, ParenthesizedTypeNodeData,
    PostfixUnaryExpressionData, PrefixUnaryExpressionData, PrivateIdentifierData,
    PropertyAccessExpressionData, PropertyAssignmentData, PropertyDeclarationData,
    QualifiedNameData, RegularExpressionLiteralData, RestTypeNodeData, ReturnStatementData,
    SatisfiesExpressionData, SemicolonClassElementData, SetAccessorDeclarationData,
    ShorthandPropertyAssignmentData, SourceFileData, SpreadAssignmentData, SpreadElementData,
    StringLiteralData, SwitchStatementData, SymbolTable, SyntaxKind, TaggedTemplateExpressionData,
    TemplateExpressionData, TemplateHeadData, TemplateLiteralTypeNodeData,
    TemplateLiteralTypeSpanData, TemplateMiddleData, TemplateSpanData, TemplateTailData,
    ThisTypeNodeData, ThrowStatementData, TokenData, TokenFlags, TryStatementData,
    TupleTypeNodeData, TypeAliasDeclarationData, TypeAssertionData, TypeLiteralNodeData,
    TypeOfExpressionData, TypeOperatorNodeData, TypeParameterDeclarationData,
    TypePredicateNodeData, TypeQueryNodeData, TypeReferenceNodeData, UnionTypeNodeData,
    VariableDeclarationData, VariableDeclarationListData, VariableStatementData,
    VoidExpressionData, WhileStatementData, WithStatementData, YieldExpressionData,
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

/// A parser-validated standalone `Identifier | QualifiedName` tree.
///
/// Construction is sealed so downstream semantic stores can trust that the
/// complete input was parsed in JavaScript context without diagnostics.
#[derive(Debug)]
pub struct IsolatedEntityName {
    arena: NodeArena,
    root: NodeId,
}

impl IsolatedEntityName {
    #[must_use]
    pub const fn arena(&self) -> &NodeArena {
        &self.arena
    }

    #[must_use]
    pub const fn root(&self) -> NodeId {
        self.root
    }
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

/// Parse a JavaScript source file using JSX lexical rules.
#[must_use]
pub fn parse_javascript_source_file(source: &str) -> ParseResult {
    Parser::new_with_variant_and_javascript(source, LanguageVariant::Jsx, true).parse_source_file()
}

/// Parses one complete entity name using the pinned checker's isolated JS
/// grammar. Reserved words are accepted as identifier names, while trailing
/// tokens and every scanner or parser diagnostic reject the entire result.
#[must_use]
pub fn parse_isolated_entity_name(source: &str) -> Option<IsolatedEntityName> {
    Parser::new_isolated_entity_name(source).parse_isolated_entity_name()
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

#[derive(Clone, Copy, Eq, PartialEq)]
enum TypeParseContext {
    Normal,
    ExpressionCast,
    TupleElement,
}

#[allow(clippy::struct_excessive_bools)] // Parser flags are independent modes.
struct Parser<'a> {
    scanner: Scanner<'a>,
    current: Token<'a>,
    language_variant: LanguageVariant,
    javascript_file: bool,
    arena: NodeArena,
    diagnostics: Vec<Diagnostic>,
    invalid_token_recovery_ranges: Vec<TextRange>,
    amd_dependencies: Vec<AmdDependency>,
    amd_module_names: Vec<AmdModuleName>,
    disallow_in: bool,
    await_context: bool,
    yield_context: bool,
    await_identifier_context: bool,
    next_function_is_async: bool,
    type_parse_context: TypeParseContext,
}

impl<'a> Parser<'a> {
    fn new(source: &'a str) -> Self {
        Self::new_with_variant(source, LanguageVariant::Standard)
    }

    fn new_with_variant(source: &'a str, variant: LanguageVariant) -> Self {
        Self::new_with_variant_and_javascript(source, variant, false)
    }

    fn new_with_variant_and_javascript(
        source: &'a str,
        variant: LanguageVariant,
        javascript_file: bool,
    ) -> Self {
        Self::new_with_context(source, variant, javascript_file, true)
    }

    fn new_isolated_entity_name(source: &'a str) -> Self {
        Self::new_with_context(source, LanguageVariant::Standard, true, false)
    }

    fn new_with_context(
        source: &'a str,
        variant: LanguageVariant,
        javascript_file: bool,
        parse_source_file_pragmas: bool,
    ) -> Self {
        let (amd_dependencies, amd_module_names, diagnostics) = if parse_source_file_pragmas {
            parse_amd_pragmas(source)
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };
        let mut scanner = Scanner::new(source);
        scanner.set_language_variant(variant);
        let current = scanner.scan();
        let mut arena = NodeArena::new();
        arena.set_source_text(source);
        Self {
            scanner,
            current,
            language_variant: variant,
            javascript_file,
            arena,
            diagnostics,
            invalid_token_recovery_ranges: Vec::new(),
            amd_dependencies,
            amd_module_names,
            disallow_in: false,
            await_context: false,
            yield_context: false,
            await_identifier_context: false,
            next_function_is_async: false,
            type_parse_context: TypeParseContext::Normal,
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
            if self.diagnostics.iter().any(|reported| {
                reported.range.start == diagnostic.range.start
                    && reported.code == diagnostic.code
                    && reported.message == diagnostic.message
            }) {
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
        self.parse_statement_list_with_class_member_recovery(terminator, false)
    }

    #[allow(clippy::too_many_lines)] // Statement recovery is one dispatch.
    fn parse_statement_list_with_class_member_recovery(
        &mut self,
        terminator: SyntaxKind,
        recover_static_member: bool,
    ) -> NodeList {
        let start = self.current.full_start;
        let mut statements = Vec::new();
        while self.current.kind != terminator && self.current.kind != SyntaxKind::EndOfFile {
            if recover_static_member && self.starts_recovered_class_member() {
                break;
            }
            if self.current.kind == SyntaxKind::Unknown
                && self.current.text == "#"
                && self.next_token_kind() == SyntaxKind::ExclamationToken
            {
                self.bump();
                continue;
            }
            if self.current.kind == SyntaxKind::Unknown && self.current.text == "#" {
                let range = self.current.range;
                self.invalid_token_recovery_ranges.push(range);
                self.bump();
                let private_identifier = self.alloc_node(
                    SyntaxKind::PrivateIdentifier,
                    range,
                    NodeData::PrivateIdentifier(Box::new(PrivateIdentifierData {
                        text: "#".to_owned(),
                    })),
                    &[],
                );
                let end = self.parse_semicolon(range.end);
                statements.push(self.alloc_node(
                    SyntaxKind::ExpressionStatement,
                    TextRange::new(range.start, end),
                    NodeData::ExpressionStatement(Box::new(ExpressionStatementData {
                        expression: private_identifier,
                        flow_node: None,
                    })),
                    &[private_identifier],
                ));
                continue;
            }
            if self.current.kind == SyntaxKind::Unknown
                && self.current.text == "\\"
                && self.next_token_kind() == SyntaxKind::Identifier
            {
                // Keep the identifier after an incomplete unicode escape available for
                // ordinary statement recovery (`a\\u` becomes `a; u;`). The scanner has
                // already reported the invalid character for the backslash.
                self.bump();
                continue;
            }
            if self.current.kind == SyntaxKind::Unknown
                && self.next_token_kind() == SyntaxKind::EqualsToken
            {
                // Keep the right-hand expression after an invalid identifier
                // continuation (`var a₁ = "value"`) available as the next
                // statement, matching TypeScript's declaration recovery.
                self.bump();
                self.error_current("Expected a variable name.");
                self.bump();
                if self.current.kind == SyntaxKind::StringLiteral {
                    self.error_current("Expected a variable name.");
                }
                continue;
            }
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
            if matches!(
                self.current.kind,
                SyntaxKind::CommaToken
                    | SyntaxKind::CloseParenToken
                    | SyntaxKind::CloseBracketToken
                    | SyntaxKind::QuestionToken
                    | SyntaxKind::DotToken
                    | SyntaxKind::EqualsGreaterThanToken
            ) {
                self.error_current("Declaration or statement expected.");
                self.bump();
                continue;
            }
            if self.current.kind == SyntaxKind::CaseKeyword {
                // A `case` token terminates a switch clause list, but outside a
                // switch it is an unexpected statement-list terminator. Drop
                // only that token so a declaration on the next line survives.
                self.error_code_at(self.current.range, 1128, std::iter::empty::<String>());
                self.bump();
                continue;
            }
            if matches!(
                self.current.kind,
                SyntaxKind::PublicKeyword
                    | SyntaxKind::PrivateKeyword
                    | SyntaxKind::ProtectedKeyword
            ) && !self.next_token_preceded_by_line_break()
            {
                self.error_current("Declaration or statement expected.");
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

    #[allow(clippy::too_many_lines)] // Grammar dispatch over statement kinds.
    fn parse_statement(&mut self) -> NodeId {
        let is_labeled_statement = self.current.kind == SyntaxKind::Identifier
            && self.next_token_kind() == SyntaxKind::ColonToken;
        let is_const_enum = self.current.kind == SyntaxKind::ConstKeyword
            && self.next_token_kind() == SyntaxKind::EnumKeyword;
        let is_module_declaration = self.current_token_starts_module_declaration();
        let contextual_type_starts_declaration =
            self.current_token_starts_contextual_type_declaration();
        let abstract_starts_expression = self.current.kind == SyntaxKind::AbstractKeyword
            && self.next_token_preceded_by_line_break();
        let declare_starts_expression = self.current.kind == SyntaxKind::DeclareKeyword
            && (self.next_token_kind() == SyntaxKind::InstanceOfKeyword
                || self.next_tokens_are(SyntaxKind::ModuleKeyword, SyntaxKind::OpenBraceToken)
                || self.declare_precedes_invalid_namespace_name());
        let async_starts_function = self.current.kind == SyntaxKind::AsyncKeyword
            && !self.next_token_preceded_by_line_break()
            && self.next_token_kind() == SyntaxKind::FunctionKeyword;
        let async_starts_declaration = self.current.kind == SyntaxKind::AsyncKeyword
            && !self.next_token_preceded_by_line_break()
            && matches!(
                self.next_token_kind(),
                SyntaxKind::ClassKeyword
                    | SyntaxKind::EnumKeyword
                    | SyntaxKind::InterfaceKeyword
                    | SyntaxKind::NamespaceKeyword
                    | SyntaxKind::ModuleKeyword
            );
        let let_starts_declaration = self.is_let_declaration();
        let static_starts_recovered_call = self.static_starts_recovered_call_statement();
        let (import_starts_expression, invalid_import_declaration) =
            self.classify_import_statement_start();
        let import_starts_modified_class = self.current.kind == SyntaxKind::ImportKeyword
            && self.next_tokens_are(SyntaxKind::AbstractKeyword, SyntaxKind::ClassKeyword);
        let recovered_bigint_module_clause = match self.current.kind {
            SyntaxKind::ImportKeyword => self.module_clause_has_unquoted_bigint(false),
            SyntaxKind::ExportKeyword => self.module_clause_has_unquoted_bigint(true),
            _ => false,
        };
        match self.current.kind {
            SyntaxKind::OpenBraceToken => self.parse_block(),
            SyntaxKind::ConstKeyword if is_const_enum => self.parse_const_enum_declaration(),
            SyntaxKind::VarKeyword | SyntaxKind::ConstKeyword => self.parse_variable_statement(),
            SyntaxKind::LetKeyword if let_starts_declaration => self.parse_variable_statement(),
            SyntaxKind::UsingKeyword => self.parse_using_statement(),
            SyntaxKind::AwaitKeyword => self.parse_await_statement(),
            SyntaxKind::FunctionKeyword => self.parse_function_declaration(),
            SyntaxKind::ClassKeyword => self.parse_class_declaration(),
            SyntaxKind::InterfaceKeyword | SyntaxKind::TypeKeyword
                if contextual_type_starts_declaration =>
            {
                self.parse_contextual_type_declaration()
            }
            SyntaxKind::EnumKeyword => self.parse_enum_declaration(),
            SyntaxKind::ReturnKeyword => self.parse_return_statement(),
            SyntaxKind::IfKeyword => self.parse_if_statement(),
            SyntaxKind::WhileKeyword => self.parse_while_statement(),
            SyntaxKind::ForKeyword => self.parse_for_statement(),
            SyntaxKind::SwitchKeyword => self.parse_switch_statement(),
            SyntaxKind::TryKeyword => self.parse_try_statement(),
            SyntaxKind::CatchKeyword => self.parse_recovered_catch_statement(),
            SyntaxKind::FinallyKeyword => self.parse_recovered_finally_statement(),
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
            SyntaxKind::DefaultKeyword => self.parse_modified_statement(),
            SyntaxKind::AbstractKeyword if abstract_starts_expression => {
                self.parse_expression_statement()
            }
            SyntaxKind::DeclareKeyword if declare_starts_expression => {
                self.parse_expression_statement()
            }
            SyntaxKind::AsyncKeyword if !async_starts_function && !async_starts_declaration => {
                self.parse_expression_statement()
            }
            SyntaxKind::StaticKeyword if static_starts_recovered_call => {
                self.bump();
                self.parse_expression_statement()
            }
            SyntaxKind::DeclareKeyword | SyntaxKind::AbstractKeyword | SyntaxKind::AsyncKeyword => {
                self.parse_modified_statement()
            }
            SyntaxKind::ImportKeyword if import_starts_expression => {
                self.parse_expression_statement()
            }
            SyntaxKind::ImportKeyword if import_starts_modified_class => {
                let start = self.current.range.start;
                let import_modifier = self.consume_token_node();
                let declaration = self.parse_modified_statement();
                self.attach_modifiers(declaration, vec![import_modifier], start);
                declaration
            }
            SyntaxKind::ImportKeyword if invalid_import_declaration => {
                self.parse_invalid_import_statement()
            }
            SyntaxKind::ImportKeyword if recovered_bigint_module_clause => {
                self.parse_recovered_bigint_module_clause(false)
            }
            SyntaxKind::ImportKeyword => self.parse_import_declaration(),
            SyntaxKind::ExportKeyword if recovered_bigint_module_clause => {
                self.parse_recovered_bigint_module_clause(true)
            }
            SyntaxKind::ExportKeyword => self.parse_export_declaration(),
            SyntaxKind::ColonToken => self.parse_recovered_labeled_statement(),
            SyntaxKind::SemicolonToken => self.parse_empty_statement(),
            SyntaxKind::Identifier if is_labeled_statement => self.parse_labeled_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    fn static_starts_recovered_call_statement(&mut self) -> bool {
        if self.current.kind != SyntaxKind::StaticKeyword {
            return false;
        }
        let checkpoint = self.scanner.mark();
        let name = self.scanner.scan();
        let next = self.scanner.scan().kind;
        self.scanner.rewind(checkpoint);
        !name.flags.contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
            && (name.kind == SyntaxKind::Identifier || name.kind.is_keyword())
            && next == SyntaxKind::OpenParenToken
    }

    fn current_token_starts_module_declaration(&mut self) -> bool {
        match self.current.kind {
            SyntaxKind::GlobalKeyword => matches!(
                self.next_token_kind(),
                SyntaxKind::OpenBraceToken | SyntaxKind::Identifier | SyntaxKind::ExportKeyword
            ),
            SyntaxKind::NamespaceKeyword => is_module_name_token(self.next_token_kind()),
            SyntaxKind::ModuleKeyword => {
                let next = self.next_token_kind();
                next == SyntaxKind::StringLiteral || is_module_name_token(next)
            }
            _ => false,
        }
    }

    fn current_token_starts_contextual_type_declaration(&mut self) -> bool {
        matches!(
            self.current.kind,
            SyntaxKind::InterfaceKeyword | SyntaxKind::TypeKeyword
        ) && {
            let next = self.next_token_kind();
            next == SyntaxKind::Identifier || next.is_keyword()
        }
    }

    fn parse_contextual_type_declaration(&mut self) -> NodeId {
        match self.current.kind {
            SyntaxKind::InterfaceKeyword => self.parse_interface_declaration(),
            SyntaxKind::TypeKeyword => self.parse_type_alias_declaration(),
            _ => unreachable!("expected a contextual type declaration"),
        }
    }

    fn module_clause_has_unquoted_bigint(&mut self, require_first: bool) -> bool {
        let checkpoint = self.scanner.mark();
        let mut token = self.scanner.scan();
        if token.kind != SyntaxKind::OpenBraceToken {
            self.scanner.rewind(checkpoint);
            return false;
        }
        token = self.scanner.scan();
        let result = if require_first {
            token.kind == SyntaxKind::BigIntLiteral
        } else {
            let mut found = token.kind == SyntaxKind::BigIntLiteral;
            while !found
                && !matches!(
                    token.kind,
                    SyntaxKind::CloseBraceToken | SyntaxKind::EndOfFile
                )
            {
                token = self.scanner.scan();
                found = token.kind == SyntaxKind::BigIntLiteral;
            }
            found
        };
        self.scanner.rewind(checkpoint);
        result
    }

    fn parse_recovered_bigint_module_clause(&mut self, leave_bigint: bool) -> NodeId {
        let start = self.consume().range.start;
        self.expect_and_bump(SyntaxKind::OpenBraceToken, "Expected '{'.");
        if !leave_bigint {
            while !matches!(
                self.current.kind,
                SyntaxKind::CloseBraceToken | SyntaxKind::EndOfFile
            ) {
                self.bump();
            }
            if self.current.kind == SyntaxKind::CloseBraceToken {
                self.bump();
            }
        }
        self.alloc_node(
            SyntaxKind::NotEmittedStatement,
            TextRange::new(start, self.current.range.start),
            NodeData::NotEmittedStatement(Box::new(NotEmittedStatementData { flow_node: None })),
            &[],
        )
    }

    fn parse_invalid_import_statement(&mut self) -> NodeId {
        let token = self.consume();
        self.error_code_at(token.range, 1128, std::iter::empty::<String>());
        self.alloc_node_with_flags(
            SyntaxKind::NotEmittedStatement,
            NODE_FLAG_HAS_ERROR,
            token.range,
            NodeData::NotEmittedStatement(Box::new(NotEmittedStatementData { flow_node: None })),
            &[],
        )
    }

    fn classify_import_statement_start(&mut self) -> (bool, bool) {
        let next = (self.current.kind == SyntaxKind::ImportKeyword).then(|| self.next_token_kind());
        let line_broken_import =
            next == Some(SyntaxKind::ImportKeyword) && self.next_token_preceded_by_line_break();
        (
            matches!(
                next,
                Some(SyntaxKind::OpenParenToken | SyntaxKind::DotToken)
            ),
            matches!(
                next,
                Some(SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral)
            ) || line_broken_import,
        )
    }

    fn parse_block(&mut self) -> NodeId {
        self.parse_block_with_class_member_recovery(false)
    }

    fn parse_class_member_block(&mut self) -> NodeId {
        self.parse_block_with_class_member_recovery(true)
    }

    fn parse_block_with_class_member_recovery(&mut self, recover_static_member: bool) -> NodeId {
        let start = self.current.range.start;
        self.bump();
        let statements = self.parse_statement_list_with_class_member_recovery(
            SyntaxKind::CloseBraceToken,
            recover_static_member,
        );
        let end = if recover_static_member && self.starts_recovered_class_member() {
            self.error_code_at(self.current.range, 1128, std::iter::empty::<String>());
            self.current.full_start
        } else if self.current.kind == SyntaxKind::CloseBraceToken {
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

    fn starts_recovered_class_member(&mut self) -> bool {
        let next = self.next_token_kind();
        if self.current.kind == SyntaxKind::StaticKeyword {
            return next == SyntaxKind::Identifier
                || next.is_keyword()
                || matches!(
                    next,
                    SyntaxKind::StringLiteral
                        | SyntaxKind::NumericLiteral
                        | SyntaxKind::BigIntLiteral
                        | SyntaxKind::PrivateIdentifier
                        | SyntaxKind::OpenBracketToken
                        | SyntaxKind::AsteriskToken
                );
        }
        matches!(
            self.current.kind,
            SyntaxKind::CaseKeyword | SyntaxKind::DefaultKeyword
        ) && matches!(
            next,
            SyntaxKind::OpenParenToken
                | SyntaxKind::QuestionToken
                | SyntaxKind::ColonToken
                | SyntaxKind::EqualsToken
                | SyntaxKind::SemicolonToken
                | SyntaxKind::CloseBraceToken
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

    fn parse_recovered_labeled_statement(&mut self) -> NodeId {
        let start = self.current.range.start;
        let label = self.missing_identifier(start);
        self.error_current("Expected a label.");
        self.bump();
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

    fn next_tokens_are(&mut self, first: SyntaxKind, second: SyntaxKind) -> bool {
        let checkpoint = self.scanner.mark();
        let matches = self.scanner.scan().kind == first && self.scanner.scan().kind == second;
        self.scanner.rewind(checkpoint);
        matches
    }

    fn import_meta_follows(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let dot = self.scanner.scan();
        let name = self.scanner.scan();
        self.scanner.rewind(checkpoint);
        dot.kind == SyntaxKind::DotToken
            && name.kind == SyntaxKind::Identifier
            && name.text == "meta"
    }

    fn declare_precedes_invalid_namespace_name(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let namespace = self.scanner.scan().kind;
        let name = self.scanner.scan().kind;
        self.scanner.rewind(checkpoint);
        namespace == SyntaxKind::NamespaceKeyword && !is_module_name_token(name)
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

    fn is_let_declaration(&mut self) -> bool {
        if self.current.kind != SyntaxKind::LetKeyword {
            return false;
        }
        let next = self.next_token_kind();
        next == SyntaxKind::LetKeyword
            || is_import_binding_identifier_kind(next)
            || matches!(
                next,
                SyntaxKind::OpenBraceToken | SyntaxKind::OpenBracketToken | SyntaxKind::ColonToken
            )
    }

    #[allow(clippy::too_many_lines)] // Declaration-list recovery is one unit.
    fn parse_variable_statement_tail(
        &mut self,
        statement_start: TextPos,
        declaration_flags: NodeFlags,
    ) -> NodeId {
        let declaration_start = self.current.range.start;
        let mut declarations = Vec::new();
        loop {
            if declarations.is_empty()
                && self.current.kind == SyntaxKind::Unknown
                && self.current.text == "\\"
                && self.next_token_kind() == SyntaxKind::Identifier
            {
                self.bump();
                continue;
            }
            let declaration = self.parse_variable_declaration();
            let recover_private_after_invalid_indexed_access = self.current.kind
                == SyntaxKind::PrivateIdentifier
                && self
                    .arena
                    .get(declaration)
                    .and_then(|node| match &node.data {
                        NodeData::VariableDeclaration(declaration) => declaration.type_,
                        _ => None,
                    })
                    .and_then(|type_node| match &self.arena.get(type_node)?.data {
                        NodeData::IndexedAccessTypeNode(indexed) => Some(indexed.index_type),
                        _ => None,
                    })
                    .and_then(|index_type| match &self.arena.get(index_type)?.data {
                        NodeData::TypeReferenceNode(reference) => Some(reference.type_name),
                        _ => None,
                    })
                    .is_some_and(|name| {
                        matches!(
                            self.arena.get(name).map(|node| &node.data),
                            Some(NodeData::Identifier(identifier)) if identifier.text.is_empty()
                        )
                    });
            declarations.push(declaration);
            if self.current.kind != SyntaxKind::CommaToken {
                if self.current.kind == SyntaxKind::ColonToken {
                    self.error_current("Expected ','.");
                    self.bump();
                    continue;
                }
                if self.current.kind == SyntaxKind::Unknown
                    && self.current.text == "\\"
                    && self.next_token_kind() == SyntaxKind::Identifier
                {
                    self.error_current("Expected ','.");
                    self.bump();
                    continue;
                }
                if self.current.kind == SyntaxKind::DotToken
                    && self.next_token_kind() == SyntaxKind::Identifier
                {
                    self.bump();
                    continue;
                }
                if (self.current.kind == SyntaxKind::Identifier
                    || recover_private_after_invalid_indexed_access)
                    && !self
                        .current
                        .flags
                        .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
                    && self.current.range.start >= self.node_end(declaration)
                {
                    self.error_current("Expected ','.");
                    continue;
                }
                if self.current.kind == SyntaxKind::LessThanToken {
                    self.error_current("Expected ','.");
                }
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
        let end = if self.current.kind == SyntaxKind::Unknown
            && self.next_token_kind() == SyntaxKind::EqualsToken
            || self.current.range.start < declarations_end
        {
            declarations_end
        } else {
            self.parse_semicolon(declarations_end)
        };
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
        let name = if self.current.kind == SyntaxKind::PrivateIdentifier {
            self.parse_private_identifier()
        } else {
            self.parse_binding_name("Expected a variable name.")
        };
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
            let close = self.node_end(left);
            self.error_code_at(
                TextRange::new(TextPos::new(close.get().saturating_sub(1)), close),
                1005,
                [",".to_owned()],
            );
            self.error_current("Expected ';'.");
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
        let is_async = self.next_function_is_async;
        self.next_function_is_async = false;
        let previous_await_context = self.await_context;
        let previous_yield_context = self.yield_context;
        self.await_context = is_async;
        let start = self.consume().range.start;
        let asterisk_token = if self.current.kind == SyntaxKind::AsteriskToken {
            Some(self.consume_token_node())
        } else {
            None
        };
        self.yield_context = asterisk_token.is_some();
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
        } else if self.current.kind == SyntaxKind::CommaToken {
            self.error_current("Expected '{'.");
            let position = self.current.full_start;
            Some(self.alloc_node(
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
            ))
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
        self.await_context = previous_await_context;
        self.yield_context = previous_yield_context;
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
            let parameter = self.parse_parameter();
            parameters.push(parameter);
            if self.current.kind != SyntaxKind::CommaToken {
                let recovers_modifier_after_rest = matches!(
                    self.arena.get(parameter).map(|node| &node.data),
                    Some(NodeData::ParameterDeclaration(parameter))
                        if parameter.dot_dot_dot_token.is_some()
                            && matches!(
                                self.arena.get(parameter.name).map(|node| &node.data),
                                Some(NodeData::Identifier(identifier))
                                    if matches!(
                                        identifier.text.as_str(),
                                        "override"
                                            | "private"
                                            | "protected"
                                            | "public"
                                            | "readonly"
                                    )
                            )
                ) && (self.current.kind
                    == SyntaxKind::Identifier
                    || self.current.kind.is_keyword());
                if recovers_modifier_after_rest || self.current.kind == SyntaxKind::AtToken {
                    self.error_current("Expected ','.");
                    continue;
                }
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

    #[allow(clippy::too_many_lines)] // Parameter grammar has many forms.
    fn parse_parameter(&mut self) -> NodeId {
        let start = self.current.range.start;
        let mut modifier_nodes = Vec::new();
        while self.current.kind == SyntaxKind::AtToken {
            modifier_nodes.push(self.parse_decorator());
        }
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
        let name = if self.current.kind == SyntaxKind::PrivateIdentifier {
            self.parse_private_identifier()
        } else {
            self.parse_binding_name("Expected a parameter name.")
        };
        let question_token = if self.current.kind == SyntaxKind::QuestionToken {
            Some(self.consume_token_node())
        } else {
            None
        };
        let type_node = self.parse_optional_type_annotation();
        let mut await_arrow_recovery = false;
        let mut initializer = if self.current.kind == SyntaxKind::EqualsToken {
            self.bump();
            await_arrow_recovery = self.await_context
                && self.current.kind == SyntaxKind::AwaitKeyword
                && self.next_token_kind() == SyntaxKind::EqualsGreaterThanToken;
            Some(self.parse_binary_expression(2))
        } else {
            None
        };
        if await_arrow_recovery
            && matches!(
                self.current.kind,
                SyntaxKind::EqualsGreaterThanToken | SyntaxKind::AwaitKeyword
            )
            && let Some(left) = initializer
        {
            let arrow_range = if self.current.kind == SyntaxKind::EqualsGreaterThanToken {
                self.error_current("Expected ','.");
                self.consume().range
            } else {
                self.arena
                    .get(left)
                    .and_then(|left| match &left.data {
                        NodeData::AwaitExpression(awaited) => self
                            .arena
                            .get(awaited.expression)
                            .map(|operand| operand.range),
                        _ => None,
                    })
                    .unwrap_or(self.current.range)
            };
            if self.current.kind == SyntaxKind::AwaitKeyword {
                let right_token = self.consume();
                let right = self.alloc_node(
                    SyntaxKind::Identifier,
                    right_token.range,
                    NodeData::Identifier(Box::new(IdentifierData {
                        flow_node: None,
                        text: token_value(&right_token),
                    })),
                    &[],
                );
                let comma = self.alloc_node(
                    SyntaxKind::CommaToken,
                    arrow_range,
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
            .or(question_token)
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
        if !self.current.kind.is_modifier() {
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

    fn parse_decorator(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let expression = self.parse_postfix_expression_in_decorator();
        self.alloc_node(
            SyntaxKind::Decorator,
            TextRange::new(start, self.node_end(expression)),
            NodeData::Decorator(Box::new(DecoratorData {
                expression,
                facts: 0,
            })),
            &[expression],
        )
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
            if !matches!(
                self.current.kind,
                SyntaxKind::DotDotDotToken
                    | SyntaxKind::Identifier
                    | SyntaxKind::OpenBracketToken
                    | SyntaxKind::OpenBraceToken
            ) && !self.current.kind.is_keyword()
            {
                self.error_code_at(self.current.range, 1181, std::iter::empty::<String>());
                break;
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
        let mut has_trailing_comma = false;
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
            let first_name = self.parse_property_name("Expected a binding name.");
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
            has_trailing_comma = self.current.kind == SyntaxKind::CloseBraceToken;
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
                    has_trailing_comma,
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
            let mut modifier_nodes = Vec::new();
            loop {
                let is_const = self.current.kind == SyntaxKind::ConstKeyword;
                let is_variance = matches!(
                    self.current.kind,
                    SyntaxKind::InKeyword | SyntaxKind::OutKeyword
                ) && self.type_parameter_variance_modifier_has_name();
                if !is_const && !is_variance {
                    break;
                }
                modifier_nodes.push(self.consume_token_node());
            }
            let modifiers = (!modifier_nodes.is_empty()).then(|| ModifierList {
                list: NodeList {
                    range: TextRange::new(parameter_start, self.current.range.start),
                    nodes: modifier_nodes.clone(),
                    has_trailing_comma: false,
                },
                flags: ts_ast::ModifierFlags::default(),
            });
            // Contextual and reserved words are still identifier names for recovery here.  In
            // particular, consuming them keeps a malformed list such as `<implements,
            // interface>` synchronized through its closing `>` instead of abandoning the
            // declaration at the first keyword.
            let name = self.parse_identifier_name("Expected a type parameter name.");
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
            let mut children = modifier_nodes;
            children.push(name);
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
                    modifiers,
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

    fn type_parameter_variance_modifier_has_name(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let mut next = self.scanner.scan().kind;
        while matches!(
            next,
            SyntaxKind::ConstKeyword | SyntaxKind::InKeyword | SyntaxKind::OutKeyword
        ) {
            next = self.scanner.scan().kind;
        }
        self.scanner.rewind(checkpoint);
        (next == SyntaxKind::Identifier || next.is_keyword())
            && !matches!(
                next,
                SyntaxKind::ExtendsKeyword
                    | SyntaxKind::EqualsToken
                    | SyntaxKind::CommaToken
                    | SyntaxKind::GreaterThanToken
                    | SyntaxKind::EndOfFile
            )
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
        let heritage_keyword_is_recovered_name = matches!(
            self.current.kind,
            SyntaxKind::ExtendsKeyword | SyntaxKind::ImplementsKeyword
        ) && matches!(
            self.next_token_kind(),
            SyntaxKind::LessThanToken
                | SyntaxKind::OpenBraceToken
                | SyntaxKind::ExtendsKeyword
                | SyntaxKind::ImplementsKeyword
        );
        let name = if self.current.kind != SyntaxKind::VoidKeyword
            && (self.current.kind == SyntaxKind::Identifier || self.current.kind.is_keyword())
            && (!matches!(
                self.current.kind,
                SyntaxKind::ExtendsKeyword | SyntaxKind::ImplementsKeyword
            ) || heritage_keyword_is_recovered_name)
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
        let name = if self.current.kind != SyntaxKind::VoidKeyword
            && !matches!(
                self.current.kind,
                SyntaxKind::ExtendsKeyword | SyntaxKind::ImplementsKeyword
            )
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

    fn parse_decorated_class_expression(&mut self) -> NodeId {
        let start = self.current.range.start;
        let mut decorators = Vec::new();
        while self.current.kind == SyntaxKind::AtToken {
            let decorator_start = self.consume().range.start;
            let expression = if self.decorator_precedes_invalid_empty_arrow() {
                self.parse_identifier_name("Expected a decorator expression.")
            } else {
                self.parse_postfix_expression()
            };
            decorators.push(self.alloc_node(
                SyntaxKind::Decorator,
                TextRange::new(decorator_start, self.node_end(expression)),
                NodeData::Decorator(Box::new(DecoratorData {
                    expression,
                    facts: 0,
                })),
                &[expression],
            ));
        }
        if self.current.kind != SyntaxKind::ClassKeyword {
            self.error_current("Expected 'class' after decorators.");
            return self.missing_identifier(self.current.range.start);
        }
        let expression = self.parse_class_expression();
        self.attach_modifiers(expression, decorators, start);
        expression
    }

    fn decorator_precedes_invalid_empty_arrow(&mut self) -> bool {
        if self.current.kind != SyntaxKind::Identifier {
            return false;
        }
        let checkpoint = self.scanner.mark();
        let open = self.scanner.scan().kind;
        let close = self.scanner.scan().kind;
        let arrow = self.scanner.scan().kind;
        self.scanner.rewind(checkpoint);
        open == SyntaxKind::OpenParenToken
            && close == SyntaxKind::CloseParenToken
            && arrow == SyntaxKind::EqualsGreaterThanToken
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
            let mut has_trailing_comma = false;
            loop {
                let mut expression = self.parse_heritage_expression();
                let mut type_arguments = self.parse_type_arguments();
                while self.current.kind == SyntaxKind::OpenParenToken {
                    let arguments = self.parse_argument_list();
                    let end = arguments.range.end;
                    let mut children = vec![expression];
                    extend_list_children(&mut children, type_arguments.as_ref());
                    children.extend(arguments.nodes.iter().copied());
                    expression = self.alloc_node(
                        SyntaxKind::CallExpression,
                        TextRange::new(self.node_start(expression), end),
                        NodeData::CallExpression(Box::new(CallExpressionData {
                            arguments,
                            expression,
                            question_dot_token: None,
                            symbol: None,
                            type_arguments,
                            facts: 0,
                        })),
                        &children,
                    );
                    type_arguments = self.parse_type_arguments();
                }
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
                let comma = self.consume();
                if matches!(
                    self.current.kind,
                    SyntaxKind::OpenBraceToken
                        | SyntaxKind::ExtendsKeyword
                        | SyntaxKind::ImplementsKeyword
                        | SyntaxKind::EndOfFile
                ) {
                    has_trailing_comma = true;
                    self.error_code_at(comma.range, 1009, std::iter::empty::<String>());
                    break;
                }
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
                        has_trailing_comma,
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
        // A class heritage expression is not restricted to an entity name.
        // In particular, field initializers can contain anonymous classes such
        // as `class extends this.base {}`.  `parse_entity_name` recovers `this`
        // as a missing identifier and leaves the property access behind, which
        // then prematurely terminates the containing class member.
        let mut expression = if matches!(
            self.current.kind,
            SyntaxKind::ThisKeyword
                | SyntaxKind::SuperKeyword
                | SyntaxKind::StringLiteral
                | SyntaxKind::NumericLiteral
                | SyntaxKind::NullKeyword
                | SyntaxKind::OpenParenToken
                | SyntaxKind::OpenBracketToken
                | SyntaxKind::OpenBraceToken
                | SyntaxKind::ClassKeyword
        ) {
            self.parse_postfix_expression()
        } else if self.current.kind == SyntaxKind::VoidKeyword {
            // `extends void {}` is recovered by TypeScript as a missing heritage name,
            // leaving `void {}` to be parsed as the following statement.
            self.error_current("Expected a heritage name.");
            self.missing_identifier(self.current.range.start)
        } else if is_keyword_type(self.current.kind) {
            // Invalid primitive heritage names still belong to the clause. Consuming the token
            // here lets semantic checking report the invalid implementation without losing the
            // class body and following declarations during parser recovery.
            self.parse_identifier_name("Expected a heritage name.")
        } else {
            self.parse_entity_name(true)
        };
        while self.current.kind == SyntaxKind::QuestionDotToken {
            let question_dot_token = self.consume_token_node();
            let name = self.parse_property_name("Expected a property name.");
            expression = self.alloc_node(
                SyntaxKind::PropertyAccessExpression,
                TextRange::new(self.node_start(expression), self.node_end(name)),
                NodeData::PropertyAccessExpression(Box::new(PropertyAccessExpressionData {
                    expression,
                    flow_node: None,
                    question_dot_token: Some(question_dot_token),
                    facts: 0,
                    name,
                })),
                &[expression, question_dot_token, name],
            );
        }
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
            if !signature_only && self.current.kind == SyntaxKind::FunctionKeyword {
                self.error_current("Declaration expected.");
                recovered_at_statement = true;
                break;
            }
            if !signature_only && self.class_var_keyword_starts_recovered_statement() {
                self.error_code_at(self.current.range, 1068, std::iter::empty::<String>());
                recovered_at_statement = true;
                break;
            }
            // A modifier followed directly by a block cannot form a member. Consume the orphaned
            // modifier and leave the block for statement parsing instead of treating its closing
            // brace as the class terminator.
            if !signature_only
                && self.current.kind.is_modifier()
                && self.current.kind != SyntaxKind::StaticKeyword
                && self.next_token_kind() == SyntaxKind::OpenBraceToken
            {
                self.error_current("Declaration expected.");
                self.bump();
                recovered_at_statement = true;
                break;
            }
            if !signature_only
                && self.current.kind == SyntaxKind::TryKeyword
                && self.next_token_kind() == SyntaxKind::OpenBraceToken
            {
                self.error_current("Declaration expected.");
                recovered_at_statement = true;
                break;
            }
            let before = (self.current.kind, self.current.range);
            if self.current.kind == SyntaxKind::SemicolonToken {
                let range = self.consume().range;
                if !signature_only {
                    members.push(self.alloc_node(
                        SyntaxKind::SemicolonClassElement,
                        range,
                        NodeData::SemicolonClassElement(Box::new(SemicolonClassElementData {
                            symbol: None,
                        })),
                        &[],
                    ));
                }
                continue;
            }
            if self.current.kind == SyntaxKind::CommaToken {
                self.bump();
                continue;
            }
            if signature_only && !self.current_token_can_start_type_member() {
                recovered_at_statement = true;
                break;
            }
            if !signature_only && !self.current_token_can_start_class_member() {
                self.error_current("Declaration expected.");
                recovered_at_statement = true;
                break;
            }
            members.push(if signature_only {
                self.parse_type_member()
            } else {
                self.parse_class_member(false)
            });
            if signature_only
                && before.0 == SyntaxKind::LessThanToken
                && self.current.kind == SyntaxKind::MinusToken
            {
                break;
            }
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

    fn class_var_keyword_starts_recovered_statement(&mut self) -> bool {
        self.current.kind == SyntaxKind::VarKeyword
            && !self.next_token_preceded_by_line_break()
            && !matches!(
                self.next_token_kind(),
                SyntaxKind::LessThanToken
                    | SyntaxKind::OpenParenToken
                    | SyntaxKind::QuestionToken
                    | SyntaxKind::ExclamationToken
                    | SyntaxKind::ColonToken
                    | SyntaxKind::EqualsToken
                    | SyntaxKind::SemicolonToken
                    | SyntaxKind::CloseBraceToken
            )
    }

    fn current_token_can_start_class_member(&mut self) -> bool {
        let recovered_global = self.current.kind == SyntaxKind::GlobalKeyword
            && matches!(
                self.next_token_kind(),
                SyntaxKind::OpenBraceToken | SyntaxKind::Identifier | SyntaxKind::ExportKeyword
            )
            && !self.next_token_preceded_by_line_break();
        if recovered_global {
            return false;
        }
        self.current.kind == SyntaxKind::Identifier
            || self.current.kind.is_keyword()
            || matches!(
                self.current.kind,
                SyntaxKind::StringLiteral
                    | SyntaxKind::NumericLiteral
                    | SyntaxKind::BigIntLiteral
                    | SyntaxKind::PrivateIdentifier
                    | SyntaxKind::OpenBracketToken
                    | SyntaxKind::AsteriskToken
                    | SyntaxKind::AtToken
            )
    }

    fn current_token_can_start_type_member(&mut self) -> bool {
        if matches!(
            self.current.kind,
            SyntaxKind::GetKeyword | SyntaxKind::SetKeyword
        ) && self.is_accessor_signature()
        {
            return true;
        }
        if self.current.kind.is_modifier() && !self.current_modifier_is_member_name() {
            return true;
        }
        if matches!(
            self.current.kind,
            SyntaxKind::OpenParenToken
                | SyntaxKind::LessThanToken
                | SyntaxKind::OpenBracketToken
                | SyntaxKind::NewKeyword
        ) {
            return true;
        }

        let checkpoint = self.scanner.mark();
        let mut name = self.current.kind;
        if name == SyntaxKind::ReadonlyKeyword && !self.current_modifier_is_member_name() {
            name = self.scanner.scan().kind;
        }
        if !(name == SyntaxKind::Identifier
            || name == SyntaxKind::PrivateIdentifier
            || name.is_keyword()
            || matches!(
                name,
                SyntaxKind::StringLiteral | SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral
            ))
        {
            self.scanner.rewind(checkpoint);
            return false;
        }
        let next = self.scanner.scan();
        self.scanner.rewind(checkpoint);
        matches!(
            next.kind,
            SyntaxKind::OpenParenToken
                | SyntaxKind::LessThanToken
                | SyntaxKind::QuestionToken
                | SyntaxKind::ColonToken
                | SyntaxKind::CommaToken
                | SyntaxKind::SemicolonToken
                | SyntaxKind::CloseBraceToken
                | SyntaxKind::EndOfFile
        ) || next.flags.contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
    }

    #[allow(clippy::too_many_lines)]
    fn parse_class_member(&mut self, signature_only: bool) -> NodeId {
        let start = self.current.range.start;
        if self.current.kind == SyntaxKind::StaticKeyword && self.next_token_is_open_brace() {
            return self.parse_class_static_block(start);
        }
        let mut modifier_nodes = Vec::new();
        while self.current.kind == SyntaxKind::AtToken {
            modifier_nodes.push(self.parse_decorator());
        }
        while self.current.kind.is_modifier()
            && !self.current_modifier_is_member_name()
            && !(self.current.kind == SyntaxKind::StaticKeyword && self.next_token_is_open_brace())
        {
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
        if self.current.kind == SyntaxKind::StaticKeyword && self.next_token_is_open_brace() {
            return self.parse_class_static_block(start);
        }
        if self.current.kind == SyntaxKind::OpenBracketToken && self.is_index_signature() {
            let member = self.parse_index_signature(start, modifiers);
            for modifier in modifier_nodes {
                self.arena.get_mut(modifier).unwrap().parent = Some(member);
            }
            return member;
        }
        if matches!(
            self.current.kind,
            SyntaxKind::GetKeyword | SyntaxKind::SetKeyword
        ) && self.is_accessor_signature()
        {
            return self.parse_class_accessor(start, modifiers, modifier_nodes, false);
        }
        if self.current_token_starts_constructor_declaration() {
            return self.parse_constructor_declaration(start, modifiers, modifier_nodes);
        }
        let asterisk_token = if self.current.kind == SyntaxKind::AsteriskToken {
            Some(self.consume_token_node())
        } else {
            None
        };
        let is_async_method = modifier_nodes.iter().any(|modifier| {
            self.arena
                .get(*modifier)
                .is_some_and(|modifier| modifier.kind == SyntaxKind::AsyncKeyword)
        });
        let name = self.parse_property_name("Expected a member name.");
        let postfix_token = if matches!(
            self.current.kind,
            SyntaxKind::QuestionToken | SyntaxKind::ExclamationToken
        ) {
            Some(self.consume_token_node())
        } else {
            None
        };
        let type_parameters = self.parse_type_parameters();
        if type_parameters.is_some() || self.current.kind == SyntaxKind::OpenParenToken {
            let previous_await_context = self.await_context;
            let previous_yield_context = self.yield_context;
            self.await_context = is_async_method;
            self.yield_context = asterisk_token.is_some();
            let parameters = self.parse_parameter_list();
            let return_type = self.parse_optional_type_annotation();
            let body = if !signature_only && self.current.kind == SyntaxKind::OpenBraceToken {
                Some(self.parse_class_member_block())
            } else if !signature_only
                && !matches!(
                    self.current.kind,
                    SyntaxKind::SemicolonToken
                        | SyntaxKind::CloseBraceToken
                        | SyntaxKind::EndOfFile
                )
                && !self.current_token_can_start_class_member()
            {
                self.error_current("Expected '{'.");
                let recovered_comma = self.current.kind == SyntaxKind::CommaToken;
                let position = self.current.full_start;
                let body = self.alloc_node(
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
                );
                if recovered_comma {
                    self.bump();
                }
                Some(body)
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
            children.extend(postfix_token);
            extend_list_children(&mut children, type_parameters.as_ref());
            children.extend(parameters.nodes.iter().copied());
            children.extend(return_type);
            children.extend(body);
            self.await_context = previous_await_context;
            self.yield_context = previous_yield_context;
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
                    postfix_token,
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
            if type_node.is_some_and(|type_node| {
                matches!(
                    self.arena.get(type_node).map(|node| &node.data),
                    Some(NodeData::TypeReferenceNode(reference))
                        if matches!(
                            self.arena.get(reference.type_name).map(|node| &node.data),
                            Some(NodeData::Identifier(identifier)) if identifier.text == "super"
                        )
                )
            }) && self.current.kind == SyntaxKind::OpenParenToken
            {
                let mut depth = 0_u32;
                loop {
                    match self.current.kind {
                        SyntaxKind::OpenParenToken => depth += 1,
                        SyntaxKind::CloseParenToken => {
                            depth = depth.saturating_sub(1);
                            self.bump();
                            if depth == 0 {
                                break;
                            }
                            continue;
                        }
                        SyntaxKind::EndOfFile => break,
                        _ => {}
                    }
                    self.bump();
                }
            }
            let initializer = if !signature_only && self.current.kind == SyntaxKind::EqualsToken {
                self.bump();
                Some(self.parse_binary_expression(2))
            } else {
                None
            };
            let fallback = type_node.map_or_else(
                || postfix_token.map_or_else(|| self.node_end(name), |id| self.node_end(id)),
                |id| self.node_end(id),
            );
            let end = self.parse_semicolon(initializer.map_or(fallback, |id| self.node_end(id)));
            let mut children = modifier_nodes;
            children.push(name);
            children.extend(postfix_token);
            children.extend(type_node);
            children.extend(initializer);
            self.alloc_node(
                SyntaxKind::PropertyDeclaration,
                TextRange::new(start, end),
                NodeData::PropertyDeclaration(Box::new(PropertyDeclarationData {
                    initializer,
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
    }

    fn current_token_starts_constructor_declaration(&mut self) -> bool {
        if self.current.kind == SyntaxKind::ConstructorKeyword {
            return true;
        }
        self.current.kind == SyntaxKind::StringLiteral
            && token_value(&self.current) == "constructor"
            && self.next_token_kind() == SyntaxKind::OpenParenToken
    }

    fn parse_constructor_declaration(
        &mut self,
        start: TextPos,
        modifiers: Option<ModifierList>,
        modifier_nodes: Vec<NodeId>,
    ) -> NodeId {
        // The constructor name is syntax, not an AST child. This is true even for the
        // quoted spelling accepted by TypeScript's parser.
        self.bump();
        let previous_await_context = self.await_context;
        let previous_yield_context = self.yield_context;
        let previous_await_identifier_context = self.await_identifier_context;
        self.await_context = false;
        self.yield_context = false;
        self.await_identifier_context = false;
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameter_list();
        let return_type = self.parse_optional_type_annotation();
        let fallback_end = return_type.map_or(parameters.range.end, |id| self.node_end(id));
        let (body, end) = if self.current.kind == SyntaxKind::OpenBraceToken {
            let body = self.parse_class_member_block();
            (Some(body), self.node_end(body))
        } else if !matches!(
            self.current.kind,
            SyntaxKind::SemicolonToken | SyntaxKind::CloseBraceToken | SyntaxKind::EndOfFile
        ) && !self.current_token_can_start_class_member()
        {
            self.error_current("Expected '{'.");
            let recovered_comma = self.current.kind == SyntaxKind::CommaToken;
            let position = self.current.full_start;
            let body = self.alloc_node(
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
            );
            if recovered_comma {
                self.bump();
            }
            (Some(body), self.node_end(body))
        } else {
            (None, self.parse_semicolon(fallback_end))
        };
        let mut children = modifier_nodes;
        extend_list_children(&mut children, type_parameters.as_ref());
        children.extend(parameters.nodes.iter().copied());
        children.extend(return_type);
        children.extend(body);
        self.await_context = previous_await_context;
        self.yield_context = previous_yield_context;
        self.await_identifier_context = previous_await_identifier_context;
        self.alloc_node(
            SyntaxKind::Constructor,
            TextRange::new(start, end),
            NodeData::ConstructorDeclaration(Box::new(ConstructorDeclarationData {
                asterisk_token: None,
                body,
                end_flow_node: None,
                full_signature: None,
                locals: SymbolTable,
                next_container: None,
                parameters,
                return_flow_node: None,
                symbol: None,
                type_: return_type,
                type_parameters,
                facts: 0,
                modifiers,
            })),
            &children,
        )
    }

    fn recover_invalid_class_var_modifier(&mut self, modifier_nodes: &mut Vec<NodeId>) {
        if self.current.kind != SyntaxKind::VarKeyword || modifier_nodes.is_empty() {
            return;
        }
        // `var` can itself be a recovered property name (`public var = 0`). Only discard it as
        // the invalid declaration keyword in forms where another token must provide the name.
        if self.next_token_preceded_by_line_break()
            || matches!(
                self.next_token_kind(),
                SyntaxKind::LessThanToken
                    | SyntaxKind::OpenParenToken
                    | SyntaxKind::QuestionToken
                    | SyntaxKind::ColonToken
                    | SyntaxKind::EqualsToken
            )
        {
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
        let previous_await_context = self.await_context;
        let previous_yield_context = self.yield_context;
        self.await_context = false;
        self.yield_context = false;
        let kind = self.consume().kind;
        let name = self.parse_property_name("Expected an accessor name.");
        let parameters = self.parse_parameter_list();
        let return_type = self.parse_optional_type_annotation();
        let body = if self.current.kind == SyntaxKind::OpenBraceToken {
            Some(self.parse_class_member_block())
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
        self.await_context = previous_await_context;
        self.yield_context = previous_yield_context;
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
        let previous_await_context = self.await_context;
        let previous_yield_context = self.yield_context;
        let previous_await_identifier_context = self.await_identifier_context;
        self.await_context = true;
        self.yield_context = false;
        self.await_identifier_context = true;
        let body = self.parse_block();
        self.await_context = previous_await_context;
        self.yield_context = previous_yield_context;
        self.await_identifier_context = previous_await_identifier_context;
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
        while self.current.kind.is_modifier() && !self.current_modifier_is_member_name() {
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
        let construct_signature = self.current.kind == SyntaxKind::NewKeyword
            && matches!(
                self.next_token_kind(),
                SyntaxKind::OpenParenToken | SyntaxKind::LessThanToken
            );

        let member = match self.current.kind {
            SyntaxKind::OpenParenToken | SyntaxKind::LessThanToken => {
                self.parse_signature_member(start, SyntaxKind::CallSignature)
            }
            SyntaxKind::NewKeyword if construct_signature => {
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
        let mut name = self.scanner.scan();
        while name.kind.is_modifier() {
            name = self.scanner.scan();
        }
        if name.kind == SyntaxKind::DotDotDotToken {
            self.scanner.rewind(checkpoint);
            return true;
        }
        let mut colon = self.scanner.scan();
        if colon.kind == SyntaxKind::QuestionToken {
            colon = self.scanner.scan();
        }
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
                | SyntaxKind::PrivateIdentifier
                | SyntaxKind::StringLiteral
                | SyntaxKind::NumericLiteral
                | SyntaxKind::OpenBracketToken
        ) || name.kind.is_keyword()
    }

    fn parse_signature_member(&mut self, start: TextPos, kind: SyntaxKind) -> NodeId {
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameter_list();
        let return_type = if self.current.kind == SyntaxKind::EqualsGreaterThanToken {
            self.error_current("Expected ':'.");
            self.bump();
            Some(self.parse_type())
        } else {
            self.parse_optional_type_annotation()
        };
        let fallback = return_type.map_or(parameters.range.end, |node| self.node_end(node));
        let end = self.parse_type_member_terminator(fallback);
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
            self.parse_type_member_terminator(fallback);
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
        let end = self.parse_type_member_terminator(self.node_end(type_node));
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
            let end = self.parse_type_member_terminator(fallback);
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
        let end = self.parse_type_member_terminator(fallback);
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
        let name = self.parse_identifier_name("Expected an enum name.");
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
            if self.current.kind == SyntaxKind::AtToken {
                self.bump();
                self.parse_postfix_expression();
                break;
            }
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
            match self.current.kind {
                SyntaxKind::CommaToken | SyntaxKind::SemicolonToken | SyntaxKind::ColonToken => {
                    self.bump();
                }
                SyntaxKind::CloseBraceToken | SyntaxKind::EndOfFile => break,
                kind if kind == SyntaxKind::Identifier
                    || kind.is_keyword()
                    || matches!(
                        kind,
                        SyntaxKind::StringLiteral
                            | SyntaxKind::NumericLiteral
                            | SyntaxKind::BigIntLiteral
                            | SyntaxKind::OpenBracketToken
                    ) => {}
                _ => {
                    self.bump();
                }
            }
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
            SyntaxKind::StringLiteral
                | SyntaxKind::NumericLiteral
                | SyntaxKind::BigIntLiteral
                | SyntaxKind::OpenBracketToken
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
        let mut recovered_block_as_for_initializer = false;
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
            let previous_disallow_in = self.disallow_in;
            self.disallow_in = true;
            let declaration_start = self.current.range.start;
            let mut declarations = Vec::new();
            let permits_empty_list = self.current.kind == SyntaxKind::InKeyword
                || (self.current.kind == SyntaxKind::OfKeyword
                    && matches!(self.next_token_kind(), SyntaxKind::Identifier));
            if !permits_empty_list {
                loop {
                    declarations.push(self.parse_variable_declaration());
                    if self.current.kind == SyntaxKind::CommaToken {
                        self.bump();
                        continue;
                    }
                    if matches!(
                        self.current.kind,
                        SyntaxKind::Identifier
                            | SyntaxKind::OpenBracketToken
                            | SyntaxKind::OpenBraceToken
                    ) || (self.current.kind.is_keyword()
                        && !matches!(
                            self.current.kind,
                            SyntaxKind::InKeyword | SyntaxKind::OfKeyword
                        ))
                    {
                        self.error_current("Expected ','.");
                        continue;
                    }
                    break;
                }
                if self.current.kind == SyntaxKind::CloseParenToken
                    && self.next_token_kind() == SyntaxKind::OpenBraceToken
                {
                    self.error_current("Expected ','.");
                    self.bump();
                    let diagnostics_len = self.diagnostics.len();
                    declarations.push(self.parse_variable_declaration());
                    self.diagnostics.truncate(diagnostics_len);
                    self.error_current("Expected ','.");
                    recovered_block_as_for_initializer = true;
                }
            }
            self.disallow_in = previous_disallow_in;
            let declarations_end = declarations
                .last()
                .map_or(declaration_start, |declaration| self.node_end(*declaration));
            Some(self.alloc_node_with_flags(
                SyntaxKind::VariableDeclarationList,
                flags,
                TextRange::new(keyword.range.start, declarations_end),
                NodeData::VariableDeclarationList(Box::new(VariableDeclarationListData {
                    declarations: NodeList {
                        range: TextRange::new(declaration_start, declarations_end),
                        nodes: declarations.clone(),
                        has_trailing_comma: false,
                    },
                    facts: 0,
                })),
                &declarations,
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
        if !recovered_block_as_for_initializer {
            self.expect_and_bump(SyntaxKind::SemicolonToken, "Expected ';'.");
        }
        let condition = if self.current.kind == SyntaxKind::SemicolonToken {
            None
        } else {
            Some(self.parse_binary_expression(0))
        };
        self.expect_and_bump(SyntaxKind::SemicolonToken, "Expected ';'.");
        let recovered_close_brace =
            recovered_block_as_for_initializer && self.current.kind == SyntaxKind::CloseBraceToken;
        let incrementor = if recovered_close_brace {
            self.error_current("Expected an expression.");
            None
        } else if matches!(
            self.current.kind,
            SyntaxKind::CloseParenToken | SyntaxKind::CloseBracketToken
        ) {
            None
        } else {
            Some(self.parse_binary_expression(0))
        };
        let statement = if recovered_close_brace {
            let range = self.consume().range;
            self.alloc_node(
                SyntaxKind::EmptyStatement,
                range,
                NodeData::EmptyStatement(Box::new(EmptyStatementData { flow_node: None })),
                &[],
            )
        } else {
            self.expect_and_bump(SyntaxKind::CloseParenToken, "Expected ')'.");
            self.parse_statement()
        };
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
        if self.current.kind != SyntaxKind::OpenParenToken {
            self.error_current("Expected '('.");
            return self.missing_identifier(self.current.range.start);
        }
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
        self.parse_try_statement_tail(start, try_block)
    }

    fn parse_recovered_catch_statement(&mut self) -> NodeId {
        let start = self.current.range.start;
        self.error_current("'try' expected.");
        let block_start = self.current.full_start;
        let block_end = self.current.range.start;
        let try_block = self.alloc_node(
            SyntaxKind::Block,
            TextRange::new(block_start, block_end),
            NodeData::Block(Box::new(BlockData {
                flow_node: None,
                locals: SymbolTable,
                multi_line: false,
                next_container: None,
                statements: NodeList {
                    range: TextRange::new(block_start, block_end),
                    nodes: Vec::new(),
                    has_trailing_comma: false,
                },
                facts: 0,
            })),
            &[],
        );
        self.parse_try_statement_tail(start, try_block)
    }

    fn parse_recovered_finally_statement(&mut self) -> NodeId {
        let start = self.current.range.start;
        self.error_current("'try' expected.");
        let block_start = self.current.full_start;
        let block_end = self.current.range.start;
        let try_block = self.alloc_node(
            SyntaxKind::Block,
            TextRange::new(block_start, block_end),
            NodeData::Block(Box::new(BlockData {
                flow_node: None,
                locals: SymbolTable,
                multi_line: false,
                next_container: None,
                statements: NodeList {
                    range: TextRange::new(block_start, block_end),
                    nodes: Vec::new(),
                    has_trailing_comma: false,
                },
                facts: 0,
            })),
            &[],
        );
        self.parse_try_statement_tail(start, try_block)
    }

    fn parse_try_statement_tail(&mut self, start: TextPos, try_block: NodeId) -> NodeId {
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
            let block = if self.current.kind == SyntaxKind::OpenBraceToken {
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
        let mut finally_block = if self.current.kind == SyntaxKind::FinallyKeyword {
            self.bump();
            Some(self.parse_block())
        } else {
            None
        };
        if catch_clause.is_none() && finally_block.is_none() {
            self.error_current("Expected 'catch' or 'finally'.");
            let start = self.node_end(try_block);
            let end = self.current.range.start;
            finally_block = Some(self.alloc_node(
                SyntaxKind::Block,
                TextRange::new(start, end),
                NodeData::Block(Box::new(BlockData {
                    flow_node: None,
                    locals: SymbolTable,
                    multi_line: false,
                    next_container: None,
                    statements: NodeList {
                        range: TextRange::new(start, end),
                        nodes: Vec::new(),
                        has_trailing_comma: false,
                    },
                    facts: 0,
                })),
                &[],
            ));
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
            self.parse_identifier_name("Expected a module name.")
        };
        let mut terminator_end = None;
        let body = if allows_dotted_name && self.current.kind == SyntaxKind::DotToken {
            self.bump();
            Some(self.parse_nested_module_declaration(keyword.kind))
        } else if self.current.kind == SyntaxKind::SemicolonToken {
            terminator_end = Some(self.consume().range.end);
            None
        } else {
            self.parse_module_block()
        };
        let declaration =
            self.alloc_module_declaration(keyword.range.start, keyword.kind, None, name, body);
        if let Some(end) = terminator_end {
            self.arena.get_mut(declaration).unwrap().range.end = end;
        }
        declaration
    }

    fn parse_nested_module_declaration(&mut self, keyword: SyntaxKind) -> NodeId {
        let start = self.current.range.start;
        let export_modifier = self.alloc_node_with_flags(
            SyntaxKind::ExportKeyword,
            NodeFlags::REPARSED,
            TextRange::new(start, start),
            NodeData::Token(Box::new(TokenData)),
            &[],
        );
        let modifiers = ModifierList {
            list: NodeList {
                range: TextRange::new(start, start),
                nodes: vec![export_modifier],
                has_trailing_comma: false,
            },
            flags: ts_ast::ModifierFlags::EXPORT,
        };
        let name = self.parse_identifier_name("Expected a module name.");
        let body = if self.current.kind == SyntaxKind::DotToken {
            self.bump();
            Some(self.parse_nested_module_declaration(keyword))
        } else {
            self.parse_module_block()
        };
        self.alloc_module_declaration(start, keyword, Some(modifiers), name, body)
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
        modifiers: Option<ModifierList>,
        name: NodeId,
        body: Option<NodeId>,
    ) -> NodeId {
        let end = body.map_or_else(|| self.node_end(name), |id| self.node_end(id));
        let mut children = modifiers
            .as_ref()
            .map_or_else(Vec::new, |modifiers| modifiers.list.nodes.clone());
        children.push(name);
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
                modifiers,
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
            SyntaxKind::DeclareKeyword
                | SyntaxKind::AbstractKeyword
                | SyntaxKind::AsyncKeyword
                | SyntaxKind::DefaultKeyword
        ) {
            modifiers.push(self.consume_token_node());
        }
        let parse_in_await_context = self.current.kind == SyntaxKind::FunctionKeyword
            && modifiers.iter().any(|modifier| {
                self.arena
                    .get(*modifier)
                    .is_some_and(|modifier| modifier.kind == SyntaxKind::AsyncKeyword)
            });
        let previous_next_function_is_async = self.next_function_is_async;
        self.next_function_is_async = parse_in_await_context;
        let declaration = self.parse_statement();
        self.next_function_is_async = previous_next_function_is_async;
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
                NodeData::ClassExpression(data) => data.modifiers.clone(),
                NodeData::FunctionDeclaration(data) => data.modifiers.clone(),
                NodeData::FunctionExpression(data) => data.modifiers.clone(),
                NodeData::InterfaceDeclaration(data) => data.modifiers.clone(),
                NodeData::TypeAliasDeclaration(data) => data.modifiers.clone(),
                NodeData::EnumDeclaration(data) => data.modifiers.clone(),
                NodeData::ImportDeclaration(data) => data.modifiers.clone(),
                NodeData::ImportEqualsDeclaration(data) => data.modifiers.clone(),
                NodeData::ExportDeclaration(data) => data.modifiers.clone(),
                NodeData::ExportAssignment(data) => data.modifiers.clone(),
                NodeData::NamespaceExportDeclaration(data) => data.modifiers.clone(),
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
                NodeData::ClassExpression(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::FunctionDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::FunctionExpression(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::InterfaceDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::TypeAliasDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::EnumDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::ImportDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::ImportEqualsDeclaration(data) => {
                    data.modifiers = Some(modifiers.clone());
                }
                NodeData::ExportDeclaration(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::ExportAssignment(data) => data.modifiers = Some(modifiers.clone()),
                NodeData::NamespaceExportDeclaration(data) => {
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
            let phase_modifier = self.import_phase_modifier();
            if phase_modifier.is_some() {
                self.bump();
            }
            let name = if self.token_is_identifier_in_current_context(self.current.kind) {
                Some(self.parse_identifier_name("Expected an import binding."))
            } else {
                None
            };
            if let Some(name) = name
                && !matches!(
                    self.current.kind,
                    SyntaxKind::CommaToken | SyntaxKind::FromKeyword
                )
                && phase_modifier != Some(SyntaxKind::DeferKeyword)
            {
                return self.parse_import_equals_declaration(
                    start,
                    name,
                    phase_modifier == Some(SyntaxKind::TypeKeyword),
                );
            }
            if name.is_none()
                && !matches!(
                    self.current.kind,
                    SyntaxKind::OpenBraceToken | SyntaxKind::AsteriskToken
                )
            {
                None
            } else {
                let parse_named_bindings = if name.is_none() {
                    true
                } else if self.current.kind == SyntaxKind::CommaToken {
                    self.bump();
                    true
                } else {
                    false
                };
                let named_bindings = parse_named_bindings.then(|| {
                    if self.current.kind == SyntaxKind::AsteriskToken {
                        self.parse_namespace_import()
                    } else {
                        self.parse_named_imports()
                    }
                });
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
                        phase_modifier,
                        symbol: None,
                        facts: 0,
                        name,
                    })),
                    &clause_children,
                ))
            }
        };
        if import_clause.is_some() {
            self.expect_and_bump(SyntaxKind::FromKeyword, "Expected 'from'.");
        }
        let module_specifier = self.parse_import_module_specifier();
        children.extend(import_clause);
        children.push(module_specifier);
        let attributes = self.parse_import_attributes(true);
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

    fn import_phase_modifier(&mut self) -> Option<SyntaxKind> {
        // `type` and `defer` are contextual: keep them as binding names at the
        // exact comma, equals, and `from "module"` ambiguity boundaries.
        if !self.token_is_identifier_in_current_context(self.current.kind) {
            return None;
        }
        let spelling = token_value(&self.current);
        let next = self.next_token_kind();
        if spelling == "type" {
            let next_is_identifier = self.token_is_identifier_in_current_context(next);
            let from_starts_phase_binding = if next == SyntaxKind::FromKeyword {
                next_is_identifier
                    && (self.next_tokens_are(SyntaxKind::FromKeyword, SyntaxKind::FromKeyword)
                        || self.next_tokens_are(SyntaxKind::FromKeyword, SyntaxKind::EqualsToken))
            } else {
                true
            };
            let next_starts_phase_clause = next_is_identifier
                || matches!(next, SyntaxKind::AsteriskToken | SyntaxKind::OpenBraceToken);
            let type_modifier_is_unambiguous =
                from_starts_phase_binding && next_starts_phase_clause;
            return type_modifier_is_unambiguous.then_some(SyntaxKind::TypeKeyword);
        }
        if spelling == "defer" {
            let defer_modifier_is_unambiguous = if next == SyntaxKind::FromKeyword {
                !self.next_tokens_are(SyntaxKind::FromKeyword, SyntaxKind::StringLiteral)
            } else {
                !matches!(next, SyntaxKind::CommaToken | SyntaxKind::EqualsToken)
            };
            return defer_modifier_is_unambiguous.then_some(SyntaxKind::DeferKeyword);
        }
        None
    }

    fn token_is_identifier_in_current_context(&self, kind: SyntaxKind) -> bool {
        // The pinned parser ignores strict-mode reserved words here and leaves
        // their grammar diagnostics to the checker.
        kind == SyntaxKind::Identifier
            || ((kind as u16) > (SyntaxKind::LAST_RESERVED_WORD as u16)
                && (kind as u16) <= (SyntaxKind::LAST_KEYWORD as u16)
                && !(kind == SyntaxKind::AwaitKeyword && self.await_context)
                && !(kind == SyntaxKind::YieldKeyword && self.yield_context))
    }

    fn parse_import_module_specifier(&mut self) -> NodeId {
        if self.current.kind == SyntaxKind::StringLiteral {
            return self.parse_string_literal();
        }
        // The grammar checker owns the string-literal restriction. Keeping the
        // complete expression here is important for parser recovery and mirrors
        // parseModuleSpecifier in the pinned parser.
        self.parse_binary_expression(0)
    }

    fn parse_import_attributes(&mut self, allow_with_preceding_line_break: bool) -> Option<NodeId> {
        let has_preceding_line_break = self
            .current
            .flags
            .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK);
        match self.current.kind {
            SyntaxKind::WithKeyword
                if allow_with_preceding_line_break || !has_preceding_line_break => {}
            SyntaxKind::AssertKeyword if !has_preceding_line_break => {
                self.error_code_at(self.current.range, 2880, []);
            }
            _ => return None,
        }

        let keyword = self.consume();
        let mut attributes = Vec::new();
        let mut has_trailing_comma = false;
        let mut multi_line = false;
        let list_start;
        let list_end;
        let end;

        if self.current.kind == SyntaxKind::OpenBraceToken {
            self.bump();
            list_start = self.current.range.start;
            multi_line = self
                .current
                .flags
                .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK);
            loop {
                if matches!(
                    self.current.kind,
                    SyntaxKind::CloseBraceToken | SyntaxKind::EndOfFile
                ) {
                    break;
                }
                if !(self.current.kind == SyntaxKind::Identifier
                    || self.current.kind.is_keyword()
                    || self.current.kind == SyntaxKind::StringLiteral)
                {
                    self.error_code_at(self.current.range, 1478, []);
                    break;
                }

                attributes.push(self.parse_import_attribute());

                if self.current.kind == SyntaxKind::CommaToken {
                    self.bump();
                    has_trailing_comma = self.current.kind == SyntaxKind::CloseBraceToken;
                    continue;
                }
                if matches!(
                    self.current.kind,
                    SyntaxKind::CloseBraceToken | SyntaxKind::EndOfFile
                ) {
                    break;
                }
                self.error_current("Expected ','.");
                if self.current.kind == SyntaxKind::SemicolonToken
                    && !self
                        .current
                        .flags
                        .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
                {
                    self.bump();
                }
            }
            list_end = self.current.range.start;
            end = if self.current.kind == SyntaxKind::CloseBraceToken {
                self.consume().range.end
            } else {
                self.error_current("Expected '}'.");
                self.current.range.start
            };
        } else {
            list_start = self.current.range.start;
            list_end = list_start;
            self.error_current("Expected '{'.");
            end = self.current.range.start;
        }

        Some(self.alloc_node(
            SyntaxKind::ImportAttributes,
            TextRange::new(keyword.range.start, end),
            NodeData::ImportAttributes(Box::new(ImportAttributesData {
                attributes: NodeList {
                    range: TextRange::new(list_start, list_end),
                    nodes: attributes.clone(),
                    has_trailing_comma,
                },
                multi_line,
                token: keyword.kind,
                facts: 0,
            })),
            &attributes,
        ))
    }

    fn parse_import_attribute(&mut self) -> NodeId {
        let start = self.current.range.start;
        let name = if self.current.kind == SyntaxKind::StringLiteral {
            self.parse_string_literal()
        } else {
            self.parse_identifier_name("Expected an import attribute name.")
        };
        self.expect_and_bump(SyntaxKind::ColonToken, "Expected ':'.");
        // Import-attribute values are parsed as assignment expressions; the
        // grammar checker reports non-string values.
        let value = self.parse_binary_expression(2);
        self.alloc_node(
            SyntaxKind::ImportAttribute,
            TextRange::new(start, self.node_end(value)),
            NodeData::ImportAttribute(Box::new(ImportAttributeData {
                value,
                facts: 0,
                name,
            })),
            &[name, value],
        )
    }

    fn parse_namespace_import(&mut self) -> NodeId {
        let start = self.consume().range.start;
        self.expect_and_bump(SyntaxKind::AsKeyword, "Expected 'as'.");
        let name = self.parse_identifier_in_current_context("Expected a namespace import name.");
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

    fn parse_import_equals_declaration(
        &mut self,
        start: TextPos,
        name: NodeId,
        is_type_only: bool,
    ) -> NodeId {
        self.expect_and_bump(SyntaxKind::EqualsToken, "Expected '='.");
        let module_reference = if self.current.kind == SyntaxKind::RequireKeyword
            && self.next_token_kind() == SyntaxKind::OpenParenToken
        {
            let reference_start = self.consume().range.start;
            self.expect_and_bump(SyntaxKind::OpenParenToken, "Expected '('.");
            let expression = self.parse_import_module_specifier();
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
            self.parse_entity_name(false)
        };
        let end = self.parse_semicolon(self.node_end(module_reference));
        self.alloc_node(
            SyntaxKind::ImportEqualsDeclaration,
            TextRange::new(start, end),
            NodeData::ImportEqualsDeclaration(Box::new(ImportEqualsDeclarationData {
                flow_node: None,
                is_type_only,
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

    fn parse_entity_name(&mut self, allow_reserved_words: bool) -> NodeId {
        let mut entity = if allow_reserved_words
            || self.token_is_identifier_in_current_context(self.current.kind)
        {
            self.parse_identifier_name("Expected a module reference.")
        } else {
            let position = self.current.range.start;
            self.error_current("Expected a module reference.");
            self.missing_identifier(position)
        };
        while self.current.kind == SyntaxKind::DotToken {
            self.bump();
            let right = self.parse_identifier_name("Expected an identifier after '.'.");
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
        let start = self.current.range.start;
        if self.current.kind != SyntaxKind::OpenBraceToken {
            self.error_current("Expected '{'.");
            return self.missing_named_imports(start);
        }
        self.bump();
        let mut elements = Vec::new();
        let mut has_trailing_comma = false;
        while self.current.kind != SyntaxKind::CloseBraceToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            if !can_parse_module_export_name(self.current.kind)
                || (self.current.kind == SyntaxKind::FromKeyword
                    && self.next_token_kind() == SyntaxKind::StringLiteral)
            {
                break;
            }
            let specifier_start = self.current.range.start;
            let is_type_only = self.current.kind == SyntaxKind::TypeKeyword
                && !matches!(
                    self.next_token_kind(),
                    SyntaxKind::AsKeyword | SyntaxKind::CommaToken | SyntaxKind::CloseBraceToken
                );
            if is_type_only {
                self.bump();
            }
            let first_kind = self.current.kind;
            let first = self.parse_module_export_name("Expected an import name.");
            let (property_name, name) = if self.current.kind == SyntaxKind::AsKeyword {
                self.bump();
                (
                    Some(first),
                    self.parse_import_binding_identifier("Expected a local import name."),
                )
            } else {
                if !self.token_is_identifier_in_current_context(first_kind) {
                    self.mark_invalid_import_binding(first, specifier_start);
                }
                (None, first)
            };
            let mut specifier_children = vec![name];
            specifier_children.extend(property_name);
            elements.push(self.alloc_node(
                SyntaxKind::ImportSpecifier,
                TextRange::new(specifier_start, self.node_end(name)),
                NodeData::ImportSpecifier(Box::new(ImportSpecifierData {
                    is_type_only,
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
            has_trailing_comma = self.current.kind == SyntaxKind::CloseBraceToken;
        }
        if !(matches!(
            self.current.kind,
            SyntaxKind::CloseBraceToken | SyntaxKind::EndOfFile
        ) || (self.current.kind == SyntaxKind::FromKeyword
            && self.next_token_kind() == SyntaxKind::StringLiteral))
        {
            // A malformed local binding can leave several scanner tokens behind.
            // Keep them inside the import clause so they do not become unrelated
            // top-level expression statements, while preserving missing-`}`
            // recovery immediately before a `from "module"` clause.
            while !matches!(
                self.current.kind,
                SyntaxKind::CloseBraceToken | SyntaxKind::EndOfFile
            ) {
                self.bump();
            }
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
                    has_trailing_comma,
                },
                facts: 0,
            })),
            &elements,
        )
    }

    fn mark_invalid_import_binding(&mut self, name: NodeId, position: TextPos) {
        let range = self
            .arena
            .get(name)
            .map_or(TextRange::new(position, position), |node| node.range);
        self.diagnostics
            .push(parser_diagnostic(range, "Expected a local import name."));
        if let Some(node) = self.arena.get_mut(name) {
            node.flags.0 |= NODE_FLAG_HAS_ERROR.0;
        }
    }

    fn missing_named_imports(&mut self, position: TextPos) -> NodeId {
        self.alloc_node(
            SyntaxKind::NamedImports,
            TextRange::new(position, position),
            NodeData::NamedImports(Box::new(NamedImportsData {
                elements: NodeList {
                    range: TextRange::new(position, position),
                    nodes: Vec::new(),
                    has_trailing_comma: false,
                },
                facts: 0,
            })),
            &[],
        )
    }

    #[allow(clippy::too_many_lines)]
    fn parse_export_declaration(&mut self) -> NodeId {
        let export_token = self.consume();
        let start = export_token.range.start;
        let next = self.next_token_kind();
        let invalid_contextual_declaration_name = match self.current.kind {
            SyntaxKind::InterfaceKeyword | SyntaxKind::NamespaceKeyword => {
                !is_module_name_token(next)
            }
            SyntaxKind::TypeKeyword => {
                !matches!(next, SyntaxKind::OpenBraceToken | SyntaxKind::AsteriskToken)
                    && !is_module_name_token(next)
            }
            SyntaxKind::ModuleKeyword => {
                next != SyntaxKind::StringLiteral && !is_module_name_token(next)
            }
            _ => false,
        };
        if invalid_contextual_declaration_name {
            let export_modifier =
                self.alloc_token_node(SyntaxKind::ExportKeyword, export_token.range);
            return self.alloc_node_with_flags(
                SyntaxKind::NotEmittedStatement,
                NODE_FLAG_HAS_ERROR,
                export_token.range,
                NodeData::NotEmittedStatement(Box::new(NotEmittedStatementData {
                    flow_node: None,
                })),
                &[export_modifier],
            );
        }
        let class_modifier_before_import = if matches!(
            self.current.kind,
            SyntaxKind::PublicKeyword
                | SyntaxKind::PrivateKeyword
                | SyntaxKind::ProtectedKeyword
                | SyntaxKind::StaticKeyword
                | SyntaxKind::ReadonlyKeyword
        ) {
            let checkpoint = self.scanner.mark();
            let mut kind = self.current.kind;
            while matches!(
                kind,
                SyntaxKind::PublicKeyword
                    | SyntaxKind::PrivateKeyword
                    | SyntaxKind::ProtectedKeyword
                    | SyntaxKind::StaticKeyword
                    | SyntaxKind::ReadonlyKeyword
            ) {
                kind = self.scanner.scan().kind;
            }
            self.scanner.rewind(checkpoint);
            kind == SyntaxKind::ImportKeyword
        } else {
            false
        };
        if class_modifier_before_import {
            let export_modifier =
                self.alloc_token_node(SyntaxKind::ExportKeyword, export_token.range);
            let mut import_modifiers = vec![export_modifier];
            while self.current.kind != SyntaxKind::ImportKeyword {
                import_modifiers.push(self.consume_token_node());
            }
            let declaration = self.parse_statement();
            self.attach_modifiers(declaration, import_modifiers, start);
            return declaration;
        }
        let is_type_only = self.current.kind == SyntaxKind::TypeKeyword
            && matches!(
                self.next_token_kind(),
                SyntaxKind::OpenBraceToken | SyntaxKind::AsteriskToken
            );
        if is_type_only {
            self.bump();
        }
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
                | SyntaxKind::AtToken
        ) {
            let declaration = self.parse_statement();
            let export_modifier =
                self.alloc_token_node(SyntaxKind::ExportKeyword, export_token.range);
            self.attach_modifiers(declaration, vec![export_modifier], start);
            return declaration;
        }
        if self.current.kind == SyntaxKind::ExportKeyword
            && self.next_token_kind() == SyntaxKind::EqualsToken
        {
            self.bump();
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
                    type_: None,
                    facts: 0,
                    modifiers: None,
                })),
                &[expression],
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
                    // The leading `export` is mandatory syntax, not a
                    // modifier. Pinned binder diagnostics reserve this slot
                    // for illegal decorators/modifiers preceding the
                    // declaration.
                    modifiers: None,
                    name,
                })),
                &[name],
            );
        }
        if self.current.kind == SyntaxKind::DefaultKeyword {
            let default_token = self.consume();
            if matches!(
                self.current.kind,
                SyntaxKind::FunctionKeyword
                    | SyntaxKind::ClassKeyword
                    | SyntaxKind::InterfaceKeyword
                    | SyntaxKind::AtToken
                    | SyntaxKind::AbstractKeyword
            ) || (self.current.kind == SyntaxKind::AsyncKeyword
                && self.next_token_kind() == SyntaxKind::FunctionKeyword)
            {
                let declaration = self.parse_statement();
                let export_modifier =
                    self.alloc_token_node(SyntaxKind::ExportKeyword, export_token.range);
                let default_modifier =
                    self.alloc_token_node(SyntaxKind::DefaultKeyword, default_token.range);
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
                    type_: None,
                    facts: 0,
                    modifiers: None,
                })),
                &[expression],
            );
        }
        let export_clause = if self.current.kind == SyntaxKind::OpenBraceToken {
            Some(self.parse_named_exports())
        } else if self.current.kind == SyntaxKind::AsteriskToken {
            let star_start = self.consume().range.start;
            if self.current.kind == SyntaxKind::AsKeyword {
                self.bump();
                let name = self.parse_module_export_name("Expected a namespace export name.");
                Some(self.alloc_node(
                    SyntaxKind::NamespaceExport,
                    TextRange::new(star_start, self.node_end(name)),
                    NodeData::NamespaceExport(Box::new(NamespaceExportData { symbol: None, name })),
                    &[name],
                ))
            } else {
                None
            }
        } else {
            self.error_current("Expected an export clause.");
            None
        };
        let module_specifier = if self.current.kind == SyntaxKind::FromKeyword {
            self.bump();
            if self.current.kind == SyntaxKind::StringLiteral {
                Some(self.parse_string_literal())
            } else if self.current.kind == SyntaxKind::Identifier || self.current.kind.is_keyword()
            {
                self.error_current("Expected a module specifier.");
                Some(self.parse_identifier_name("Expected a module specifier."))
            } else {
                self.error_current("Expected a module specifier.");
                None
            }
        } else {
            None
        };
        let attributes = module_specifier.and_then(|_| self.parse_import_attributes(false));
        let fallback = attributes
            .or(module_specifier)
            .or(export_clause)
            .map_or(start, |id| self.node_end(id));
        let end = self.parse_semicolon(fallback);
        let mut children = Vec::new();
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
                is_type_only,
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
        let mut has_trailing_comma = false;
        while self.current.kind != SyntaxKind::CloseBraceToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            // Recover a missing `}` before the `from` clause without turning
            // `from` into another exported name. A closed clause can still
            // legitimately export a binding named `from`.
            if self.current.kind == SyntaxKind::FromKeyword
                && self.next_token_kind() == SyntaxKind::StringLiteral
            {
                break;
            }
            let specifier_start = self.current.range.start;
            let is_type_only = self.current.kind == SyntaxKind::TypeKeyword
                && !matches!(
                    self.next_token_kind(),
                    SyntaxKind::AsKeyword | SyntaxKind::CommaToken | SyntaxKind::CloseBraceToken
                );
            if is_type_only {
                self.bump();
            }
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
                    is_type_only,
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
            has_trailing_comma = self.current.kind == SyntaxKind::CloseBraceToken;
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
                    has_trailing_comma,
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
        let end = if self.current.kind == SyntaxKind::ColonToken {
            self.error_current("Expected ';'.");
            self.bump();
            expression_end
        } else if self.current.kind == SyntaxKind::Unknown {
            // Match parseErrorForMissingSemicolonAfter: a scanner error at the next
            // token is sufficient and should not also produce a missing-semicolon error.
            expression_end
        } else {
            self.parse_semicolon(expression_end)
        };
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

    #[allow(clippy::too_many_lines)]
    fn parse_binary_expression(&mut self, minimum_precedence: u8) -> NodeId {
        let mut left = if minimum_precedence <= 2
            && self.current.kind == SyntaxKind::AsyncKeyword
            && self.is_async_arrow_function()
        {
            self.parse_async_arrow_function()
        } else if minimum_precedence <= 2
            && self.current.kind == SyntaxKind::LessThanToken
            && self.is_generic_arrow_function()
        {
            self.parse_generic_arrow_function()
        } else if minimum_precedence <= 2
            && self.current.kind == SyntaxKind::OpenParenToken
            && self.is_parenthesized_arrow()
        {
            self.parse_parenthesized_arrow_function()
        } else {
            self.parse_postfix_expression()
        };
        if minimum_precedence <= 2
            && self.current.kind == SyntaxKind::EqualsGreaterThanToken
            && self.arena.get(left).unwrap().kind == SyntaxKind::Identifier
            && !(self.await_identifier_context
                && matches!(
                    self.arena.get(left).map(|node| &node.data),
                    Some(NodeData::Identifier(identifier)) if identifier.text == "await"
                ))
        {
            left = self.parse_single_parameter_arrow_function(left);
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
            if self.current.kind.is_assignment_operator()
                && !self.expression_can_precede_assignment(left, self.current.kind)
            {
                break;
            }
            let operator = self.consume();
            let operator_node = self.alloc_node(
                operator.kind,
                operator.range,
                NodeData::Token(Box::new(TokenData)),
                &[],
            );
            let right_precedence = if right_associative {
                precedence
            } else {
                precedence + 1
            };
            let right = if (self
                .current
                .flags
                .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
                && matches!(
                    self.current.kind,
                    SyntaxKind::VarKeyword | SyntaxKind::LetKeyword | SyntaxKind::ConstKeyword
                ))
                || matches!(
                    self.current.kind,
                    SyntaxKind::CatchKeyword | SyntaxKind::FinallyKeyword
                ) {
                self.error_current("Expected an expression.");
                self.missing_identifier(self.current.range.start)
            } else {
                self.parse_binary_expression(right_precedence)
            };
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
        let block_bodied_arrow = matches!(
            self.arena.get(left).map(|node| &node.data),
            Some(NodeData::ArrowFunction(arrow))
                if matches!(
                    self.arena.get(arrow.body).map(|node| &node.data),
                    Some(NodeData::Block(_))
                )
        );
        if minimum_precedence <= 2
            && self.current.kind == SyntaxKind::QuestionToken
            && !block_bodied_arrow
        {
            let question_token = self.consume_token_node();
            let before_else = self.current.kind == SyntaxKind::ElseKeyword;
            let when_true = if before_else {
                self.error_current("Expected an expression.");
                self.missing_identifier(self.current.range.start)
            } else {
                self.parse_binary_expression(2)
            };
            let colon_token =
                self.parse_expected_token_node(SyntaxKind::ColonToken, "Expected ':'.");
            let when_false = if before_else && self.current.kind == SyntaxKind::ElseKeyword {
                self.error_current("Expected an expression.");
                self.missing_identifier(self.current.range.start)
            } else {
                self.parse_binary_expression(2)
            };
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
        while minimum_precedence <= 1 && self.current.kind == SyntaxKind::CommaToken {
            let operator = self.consume();
            let operator_node = self.alloc_node(
                operator.kind,
                operator.range,
                NodeData::Token(Box::new(TokenData)),
                &[],
            );
            let right = self.parse_binary_expression(2);
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

    fn expression_can_precede_assignment(&self, expression: NodeId, operator: SyntaxKind) -> bool {
        let Some(node) = self.arena.get(expression) else {
            return false;
        };
        match &node.data {
            NodeData::Identifier(_)
            | NodeData::MetaProperty(_)
            | NodeData::PropertyAccessExpression(_)
            | NodeData::ElementAccessExpression(_)
            | NodeData::CallExpression(_)
            | NodeData::NewExpression(_)
            | NodeData::NumericLiteral(_)
            | NodeData::BigIntLiteral(_)
            | NodeData::StringLiteral(_)
            | NodeData::KeywordExpression(_)
            | NodeData::ParenthesizedExpression(_)
            | NodeData::ExpressionWithTypeArguments(_)
            | NodeData::NonNullExpression(_) => true,
            NodeData::ArrayLiteralExpression(_) | NodeData::ObjectLiteralExpression(_) => {
                operator == SyntaxKind::EqualsToken
            }
            _ => false,
        }
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
            let mut previous_kind = SyntaxKind::OpenParenToken;
            let mut await_arrow_in_parameters = false;
            while token.kind != SyntaxKind::EndOfFile && depth > 0 {
                if previous_kind == SyntaxKind::AwaitKeyword
                    && token.kind == SyntaxKind::EqualsGreaterThanToken
                {
                    await_arrow_in_parameters = true;
                }
                match token.kind {
                    SyntaxKind::OpenParenToken => depth += 1,
                    SyntaxKind::CloseParenToken => depth -= 1,
                    _ => {}
                }
                if depth > 0 {
                    previous_kind = token.kind;
                    token = self.scanner.scan();
                }
            }
            if await_arrow_in_parameters {
                false
            } else {
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
            }
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
                    SyntaxKind::GreaterThanGreaterThanToken => delimiter_depth -= 2,
                    SyntaxKind::GreaterThanGreaterThanGreaterThanToken => delimiter_depth -= 3,
                    SyntaxKind::EqualsGreaterThanToken if delimiter_depth == 0 => break true,
                    SyntaxKind::EndOfFile => break false,
                    SyntaxKind::SemicolonToken if delimiter_depth == 0 => break false,
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
        let body = self.parse_arrow_function_body_in_await_context(false);
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
        let previous_await_context = self.await_context;
        self.await_context = true;
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
        self.await_context = previous_await_context;
        let return_type = self.parse_optional_type_annotation();
        let arrow =
            self.parse_expected_token_node(SyntaxKind::EqualsGreaterThanToken, "Expected '=>'.");
        let body = self.parse_arrow_function_body_in_await_context(true);
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

    fn parse_postfix_expression(&mut self) -> NodeId {
        self.parse_postfix_expression_worker(false)
    }

    fn parse_postfix_expression_in_decorator(&mut self) -> NodeId {
        self.parse_postfix_expression_worker(true)
    }

    #[allow(clippy::too_many_lines)]
    fn parse_postfix_expression_worker(&mut self, in_decorator_context: bool) -> NodeId {
        if self.current.kind == SyntaxKind::ImportKeyword
            && self.next_token_kind() == SyntaxKind::OpenBraceToken
        {
            let token = self.consume();
            self.error_code_at(token.range, 1128, std::iter::empty::<String>());
            while !matches!(
                self.current.kind,
                SyntaxKind::SemicolonToken | SyntaxKind::EndOfFile
            ) {
                self.bump();
            }
            return self.missing_identifier(token.range.end);
        }
        if self.current.kind == SyntaxKind::LessThanToken
            && self.language_variant != LanguageVariant::Jsx
        {
            return self.parse_type_assertion();
        }
        let async_function = self.current.kind == SyntaxKind::AsyncKeyword
            && !self.next_token_preceded_by_line_break()
            && self.next_token_kind() == SyntaxKind::FunctionKeyword;
        if self.current.kind == SyntaxKind::AwaitKeyword
            && (self.await_context
                || (!matches!(
                    self.next_token_kind(),
                    SyntaxKind::OpenParenToken | SyntaxKind::EqualsGreaterThanToken
                ) && !is_expression_terminator(self.next_token_kind())))
        {
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
        if self.current.kind == SyntaxKind::VoidKeyword {
            let start = self.consume().range.start;
            let expression = self.parse_postfix_expression();
            return self.alloc_node(
                SyntaxKind::VoidExpression,
                TextRange::new(start, self.node_end(expression)),
                NodeData::VoidExpression(Box::new(VoidExpressionData { expression })),
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
            let missing_before_await = self.await_context
                && matches!(
                    operator,
                    SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken
                )
                && self.current.kind == SyntaxKind::AwaitKeyword;
            let operand = if missing_before_await
                || (self
                    .current
                    .flags
                    .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
                    && matches!(
                        self.current.kind,
                        SyntaxKind::TryKeyword
                            | SyntaxKind::ReturnKeyword
                            | SyntaxKind::ThrowKeyword
                            | SyntaxKind::IfKeyword
                            | SyntaxKind::ForKeyword
                            | SyntaxKind::WhileKeyword
                            | SyntaxKind::SwitchKeyword
                            | SyntaxKind::VarKeyword
                            | SyntaxKind::ConstKeyword
                    )) {
                self.error_current("Expected an expression.");
                self.missing_identifier(self.current.range.start)
            } else {
                self.parse_postfix_expression()
            };
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
            if self.current.kind == SyntaxKind::LessThanLessThanToken {
                let checkpoint = self.scanner.mark();
                let shift_token = self.current.clone();
                self.current = self.scanner.rescan_less_than_token();
                if !self.is_type_argument_expression_suffix() {
                    self.scanner.rewind(checkpoint);
                    self.current = shift_token;
                }
            }
            match self.current.kind {
                SyntaxKind::DotToken => {
                    self.bump();
                    let name = self.parse_property_name_after_dot();
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
                    if self.current.kind == SyntaxKind::LessThanToken
                        && self.is_type_argument_expression_suffix()
                    {
                        let type_arguments = self
                            .parse_type_arguments()
                            .expect("type argument suffix starts with '<'");
                        let arguments = self.parse_argument_list();
                        let end = arguments.range.end;
                        let mut children = vec![expression, question_dot_token];
                        children.extend(type_arguments.nodes.iter().copied());
                        children.extend(arguments.nodes.iter().copied());
                        expression = self.alloc_node(
                            SyntaxKind::CallExpression,
                            TextRange::new(self.node_start(expression), end),
                            NodeData::CallExpression(Box::new(CallExpressionData {
                                arguments,
                                expression,
                                question_dot_token: Some(question_dot_token),
                                symbol: None,
                                type_arguments: Some(type_arguments),
                                facts: 0,
                            })),
                            &children,
                        );
                    } else if self.current.kind == SyntaxKind::OpenParenToken {
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
                SyntaxKind::NoSubstitutionTemplateLiteral | SyntaxKind::TemplateHead => {
                    let template = if self.current.kind == SyntaxKind::TemplateHead {
                        self.parse_template_expression()
                    } else {
                        self.parse_template_literal()
                    };
                    expression = self.alloc_node(
                        SyntaxKind::TaggedTemplateExpression,
                        TextRange::new(self.node_start(expression), self.node_end(template)),
                        NodeData::TaggedTemplateExpression(Box::new(
                            TaggedTemplateExpressionData {
                                question_dot_token: None,
                                tag: expression,
                                template,
                                type_arguments: None,
                                facts: 0,
                            },
                        )),
                        &[expression, template],
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
                    } else if matches!(
                        self.current.kind,
                        SyntaxKind::NoSubstitutionTemplateLiteral | SyntaxKind::TemplateHead
                    ) {
                        let template = if self.current.kind == SyntaxKind::TemplateHead {
                            self.parse_template_expression()
                        } else {
                            self.parse_template_literal()
                        };
                        let mut children = vec![expression];
                        children.extend(type_arguments.nodes.iter().copied());
                        children.push(template);
                        expression = self.alloc_node(
                            SyntaxKind::TaggedTemplateExpression,
                            TextRange::new(self.node_start(expression), self.node_end(template)),
                            NodeData::TaggedTemplateExpression(Box::new(
                                TaggedTemplateExpressionData {
                                    question_dot_token: None,
                                    tag: expression,
                                    template,
                                    type_arguments: Some(type_arguments),
                                    facts: 0,
                                },
                            )),
                            &children,
                        );
                    } else {
                        let start = self.node_start(expression);
                        let end = type_arguments.range.end;
                        let mut children = vec![expression];
                        children.extend(type_arguments.nodes.iter().copied());
                        expression = self.alloc_node(
                            SyntaxKind::ExpressionWithTypeArguments,
                            TextRange::new(start, end),
                            NodeData::ExpressionWithTypeArguments(Box::new(
                                ExpressionWithTypeArgumentsData {
                                    expression,
                                    type_arguments: Some(type_arguments),
                                    facts: 0,
                                },
                            )),
                            &children,
                        );
                    }
                }
                SyntaxKind::OpenBracketToken => {
                    // An ordinary element access is not consumed at the outer level of a
                    // decorator expression because it may instead begin the decorated
                    // class member's computed property name. Nested expressions (such as
                    // `@dec(value[key])`) are parsed through the context-free wrapper.
                    if in_decorator_context {
                        break;
                    }
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
                SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken
                    if !self
                        .current
                        .flags
                        .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK) =>
                {
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
                    let previous_context = self.type_parse_context;
                    self.type_parse_context = TypeParseContext::ExpressionCast;
                    let type_node = self.parse_type();
                    self.type_parse_context = previous_context;
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
        let mut delimiter_depth = 0_u32;
        let mut token = self.scanner.scan();
        while token.kind != SyntaxKind::EndOfFile {
            match token.kind {
                SyntaxKind::OpenParenToken
                | SyntaxKind::OpenBracketToken
                | SyntaxKind::OpenBraceToken => delimiter_depth += 1,
                SyntaxKind::CloseParenToken
                | SyntaxKind::CloseBracketToken
                | SyntaxKind::CloseBraceToken => {
                    if delimiter_depth == 0 {
                        break;
                    }
                    delimiter_depth -= 1;
                }
                SyntaxKind::SemicolonToken if delimiter_depth == 0 => break,
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
            && (token.kind == SyntaxKind::OpenParenToken
                || matches!(
                    token.kind,
                    SyntaxKind::NoSubstitutionTemplateLiteral | SyntaxKind::TemplateHead
                )
                || token.kind.is_assignment_operator()
                || (token.kind.is_binary_operator()
                    && !matches!(
                        token.kind,
                        SyntaxKind::LessThanToken
                            | SyntaxKind::GreaterThanToken
                            | SyntaxKind::PlusToken
                            | SyntaxKind::MinusToken
                    ))
                || matches!(
                    token.kind,
                    SyntaxKind::SemicolonToken
                        | SyntaxKind::EndOfFile
                        | SyntaxKind::CommaToken
                        | SyntaxKind::CloseParenToken
                        | SyntaxKind::CloseBracketToken
                        | SyntaxKind::DotToken
                        | SyntaxKind::QuestionDotToken
                        | SyntaxKind::OpenBracketToken
                        | SyntaxKind::AsKeyword
                        | SyntaxKind::SatisfiesKeyword
                        | SyntaxKind::ExclamationToken
                ))
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
        let expression = if is_expression_terminator(self.current.kind)
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
        let keyword = self.consume();
        let start = keyword.range.start;
        if self.current.kind == SyntaxKind::DotToken {
            return self.parse_new_meta_property(keyword.range);
        }
        let mut expression = self.parse_new_expression_target();
        loop {
            match self.current.kind {
                SyntaxKind::DotToken => {
                    self.bump();
                    let name = self.parse_property_name_after_dot();
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
                SyntaxKind::OpenBracketToken => {
                    if self.next_token_kind() == SyntaxKind::CloseBracketToken {
                        break;
                    }
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
                _ => break,
            }
        }
        let missing_expression = matches!(
            self.arena.get(expression).map(|node| &node.data),
            Some(NodeData::Identifier(identifier)) if identifier.text.is_empty()
        );
        let type_arguments = (!missing_expression
            && self.current.kind == SyntaxKind::LessThanToken
            && self.is_type_argument_expression_suffix())
        .then(|| self.parse_type_arguments())
        .flatten();
        if self.current.kind == SyntaxKind::QuestionDotToken {
            let expression_range = self.arena.get(expression).unwrap().range;
            let expression_text = self
                .arena
                .source_text()
                .and_then(|source| {
                    source.get(
                        expression_range.start.get() as usize..expression_range.end.get() as usize,
                    )
                })
                .unwrap_or_default()
                .to_owned();
            self.error_code_at(self.current.range, 1209, [expression_text]);
        }
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

    fn parse_new_expression_target(&mut self) -> NodeId {
        if self.current.kind == SyntaxKind::NewKeyword {
            self.parse_new_expression()
        } else {
            self.parse_primary_expression()
        }
    }

    fn parse_import_meta_property(&mut self) -> NodeId {
        let start = self.consume().range.start;
        self.expect_and_bump(SyntaxKind::DotToken, "Expected '.'.");
        let name = self.parse_identifier_name("Expected 'meta'.");
        self.alloc_node(
            SyntaxKind::MetaProperty,
            TextRange::new(start, self.node_end(name)),
            NodeData::MetaProperty(Box::new(MetaPropertyData {
                flow_node: None,
                keyword_token: SyntaxKind::ImportKeyword,
                facts: 0,
                name,
            })),
            &[name],
        )
    }

    fn parse_new_meta_property(&mut self, keyword_range: TextRange) -> NodeId {
        self.bump();
        let name = self.parse_property_name_after_dot();
        let text = match self.arena.get(name).map(|node| &node.data) {
            Some(NodeData::Identifier(identifier)) => identifier.text.clone(),
            _ => String::new(),
        };
        if text != "target" {
            let range = self
                .arena
                .get(name)
                .map_or(keyword_range, |name| name.range);
            self.error_code_at(range, 17012, [text, "new".to_owned(), "target".to_owned()]);
        }
        self.alloc_node(
            SyntaxKind::MetaProperty,
            TextRange::new(keyword_range.start, self.node_end(name)),
            NodeData::MetaProperty(Box::new(MetaPropertyData {
                flow_node: None,
                keyword_token: SyntaxKind::NewKeyword,
                facts: 0,
                name,
            })),
            &[name],
        )
    }

    fn parse_argument_list(&mut self) -> NodeList {
        let start = self.consume().range.start;
        let mut arguments = Vec::new();
        let mut trailing = false;
        while self.current.kind != SyntaxKind::CloseParenToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            if arguments.is_empty()
                && matches!(
                    self.current.kind,
                    SyntaxKind::WhileKeyword
                        | SyntaxKind::ForKeyword
                        | SyntaxKind::IfKeyword
                        | SyntaxKind::SwitchKeyword
                        | SyntaxKind::TryKeyword
                )
            {
                self.error_current("Expected ')'.");
                break;
            }
            let argument = self.parse_spread_element_or_expression();
            arguments.push(argument);
            if self.current.kind == SyntaxKind::Unknown
                && self.next_token_kind() == SyntaxKind::CloseParenToken
            {
                // An invalid identifier continuation belongs to the preceding
                // argument for recovery purposes; retain the valid argument and
                // let the scanner's invalid-character diagnostic stand alone.
                self.bump();
            }
            if self.current.kind == SyntaxKind::CloseBraceToken
                && self.next_token_kind() == SyntaxKind::CloseParenToken
                && matches!(
                    self.arena.get(argument).map(|node| &node.data),
                    Some(NodeData::ObjectLiteralExpression(_))
                )
            {
                self.bump();
            }
            if self.current.kind == SyntaxKind::EqualsGreaterThanToken {
                self.error_current("Expected ','.");
                self.bump();
                trailing = false;
                continue;
            }
            if self.current.kind == SyntaxKind::ColonToken {
                self.error_current("Expected ','.");
                self.bump();
                trailing = false;
                continue;
            }
            if self.current.kind != SyntaxKind::CommaToken {
                if token_starts_argument_expression(self.current.kind) {
                    self.error_current("Expected ','.");
                    trailing = false;
                    continue;
                }
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

    #[allow(clippy::too_many_lines)]
    fn is_parenthesized_arrow(&mut self) -> bool {
        if (self.await_context || self.await_identifier_context)
            && self.next_token_kind() == SyntaxKind::AwaitKeyword
        {
            return false;
        }
        let checkpoint = self.scanner.mark();
        let mut parenthesis_depth = 1_u32;
        let mut brace_depth = 0_u32;
        let mut bracket_depth = 0_u32;
        let mut angle_depth = 0_u32;
        let mut typed_parameter = false;
        let mut top_level_question = false;
        let mut at_parameter_start = true;
        let mut invalid_parameter_start = false;
        let mut invalid_parameter_expression = false;
        let mut previous_kind = SyntaxKind::OpenParenToken;
        let mut token = self.scanner.scan();
        while token.kind != SyntaxKind::EndOfFile {
            if invalid_arrow_parameter_expression(
                (parenthesis_depth, brace_depth, bracket_depth),
                previous_kind,
                token.kind,
            ) {
                invalid_parameter_expression = true;
            }
            if at_parameter_start
                && parenthesis_depth == 1
                && brace_depth == 0
                && bracket_depth == 0
                && angle_depth == 0
                && !matches!(
                    token.kind,
                    SyntaxKind::CommaToken | SyntaxKind::CloseParenToken
                )
            {
                invalid_parameter_start |= invalid_arrow_parameter_start(token.kind);
                at_parameter_start = false;
            }
            match token.kind {
                SyntaxKind::OpenParenToken => parenthesis_depth += 1,
                SyntaxKind::CloseParenToken => {
                    parenthesis_depth -= 1;
                    if parenthesis_depth == 0 {
                        token = self.scanner.scan();
                        let result = if invalid_parameter_start || invalid_parameter_expression {
                            false
                        } else if token.kind == SyntaxKind::ColonToken {
                            if previous_kind == SyntaxKind::OpenParenToken || typed_parameter {
                                self.scanner.rewind(checkpoint);
                                return true;
                            }
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
                                    SyntaxKind::EqualsGreaterThanToken if delimiter_depth == 0 => {
                                        break true;
                                    }
                                    SyntaxKind::EndOfFile | SyntaxKind::SemicolonToken => {
                                        break false;
                                    }
                                    _ => {}
                                }
                            }
                        } else {
                            matches!(
                                token.kind,
                                SyntaxKind::EqualsGreaterThanToken | SyntaxKind::OpenBraceToken
                            ) || typed_parameter
                        };
                        self.scanner.rewind(checkpoint);
                        return result;
                    }
                }
                SyntaxKind::OpenBraceToken => brace_depth += 1,
                SyntaxKind::CloseBraceToken => brace_depth = brace_depth.saturating_sub(1),
                SyntaxKind::OpenBracketToken => bracket_depth += 1,
                SyntaxKind::CloseBracketToken => bracket_depth = bracket_depth.saturating_sub(1),
                SyntaxKind::LessThanToken if typed_parameter => angle_depth += 1,
                SyntaxKind::GreaterThanToken if angle_depth != 0 => angle_depth -= 1,
                SyntaxKind::GreaterThanGreaterThanToken if angle_depth != 0 => {
                    angle_depth = angle_depth.saturating_sub(2);
                }
                SyntaxKind::GreaterThanGreaterThanGreaterThanToken if angle_depth != 0 => {
                    angle_depth = angle_depth.saturating_sub(3);
                }
                SyntaxKind::QuestionToken
                    if parenthesis_depth == 1
                        && brace_depth == 0
                        && bracket_depth == 0
                        && angle_depth == 0 =>
                {
                    top_level_question = true;
                }
                SyntaxKind::ColonToken
                    if parenthesis_depth == 1
                        && brace_depth == 0
                        && bracket_depth == 0
                        && angle_depth == 0 =>
                {
                    if previous_kind != SyntaxKind::CloseParenToken
                        && (previous_kind == SyntaxKind::QuestionToken || !top_level_question)
                    {
                        typed_parameter = true;
                    }
                    top_level_question = false;
                }
                SyntaxKind::CommaToken
                    if parenthesis_depth == 1
                        && brace_depth == 0
                        && bracket_depth == 0
                        && angle_depth == 0 =>
                {
                    at_parameter_start = true;
                }
                _ => {}
            }
            previous_kind = token.kind;
            token = self.scanner.scan();
        }
        self.scanner.rewind(checkpoint);
        false
    }

    fn is_parenthesized_function_type(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let mut depth = 1_u32;
        let mut token = self.scanner.scan();
        if token.kind == SyntaxKind::OpenParenToken {
            self.scanner.rewind(checkpoint);
            return false;
        }
        if matches!(
            token.kind,
            SyntaxKind::CloseParenToken | SyntaxKind::DotDotDotToken
        ) {
            self.scanner.rewind(checkpoint);
            return true;
        }
        if token.kind == SyntaxKind::Identifier
            || token.kind == SyntaxKind::ThisKeyword
            || token.kind.is_keyword()
        {
            token = self.scanner.scan();
            if matches!(
                token.kind,
                SyntaxKind::ColonToken
                    | SyntaxKind::CommaToken
                    | SyntaxKind::QuestionToken
                    | SyntaxKind::EqualsToken
            ) {
                self.scanner.rewind(checkpoint);
                return true;
            }
            if token.kind == SyntaxKind::CloseParenToken
                && self.scanner.scan().kind == SyntaxKind::EqualsGreaterThanToken
            {
                self.scanner.rewind(checkpoint);
                return true;
            }
        }
        self.scanner.rewind(checkpoint.clone());
        token = self.scanner.scan();
        while token.kind != SyntaxKind::EndOfFile {
            match token.kind {
                SyntaxKind::OpenParenToken => depth += 1,
                SyntaxKind::CloseParenToken => {
                    depth -= 1;
                    if depth == 0 {
                        let result = self.scanner.scan().kind == SyntaxKind::EqualsGreaterThanToken;
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
        let has_body_token = matches!(
            self.current.kind,
            SyntaxKind::EqualsGreaterThanToken | SyntaxKind::OpenBraceToken
        );
        let arrow =
            self.parse_expected_token_node(SyntaxKind::EqualsGreaterThanToken, "Expected '=>'.");
        let body = if has_body_token {
            self.parse_arrow_function_body_in_await_context(false)
        } else {
            self.missing_identifier(self.current.range.start)
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
        let previous_await_identifier_context = self.await_identifier_context;
        self.await_identifier_context |= self.arena.get(name).is_some_and(|node| {
            matches!(&node.data, NodeData::Identifier(identifier) if identifier.text == "await")
        });
        let body = self.parse_arrow_function_body_in_await_context(false);
        self.await_identifier_context = previous_await_identifier_context;
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

    fn parse_arrow_function_body_in_await_context(&mut self, await_context: bool) -> NodeId {
        let previous_await_context = self.await_context;
        let previous_yield_context = self.yield_context;
        self.await_context = await_context;
        self.yield_context = false;
        let body = self.parse_arrow_function_body();
        self.await_context = previous_await_context;
        self.yield_context = previous_yield_context;
        body
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
            SyntaxKind::ImportKeyword => {
                if self.import_meta_follows() {
                    self.parse_import_meta_property()
                } else {
                    self.parse_identifier_name("Expected an expression.")
                }
            }
            SyntaxKind::SlashToken | SyntaxKind::SlashEqualsToken => {
                self.parse_regular_expression_literal()
            }
            SyntaxKind::FunctionKeyword => self.parse_function_expression(),
            SyntaxKind::ClassKeyword => self.parse_class_expression(),
            SyntaxKind::AtToken => self.parse_decorated_class_expression(),
            SyntaxKind::NoSubstitutionTemplateLiteral => self.parse_template_literal(),
            SyntaxKind::NullKeyword
            | SyntaxKind::TrueKeyword
            | SyntaxKind::FalseKeyword
            | SyntaxKind::ThisKeyword
            | SyntaxKind::SuperKeyword => self.parse_keyword_expression(),
            kind if is_keyword_type(kind) => self.parse_identifier_name("Expected an expression."),
            kind if is_contextual_keyword(kind) => {
                self.parse_identifier_name("Expected an expression.")
            }
            SyntaxKind::ImplementsKeyword
            | SyntaxKind::InterfaceKeyword
            | SyntaxKind::LetKeyword
            | SyntaxKind::PackageKeyword
            | SyntaxKind::StaticKeyword => self.parse_identifier_name("Expected an expression."),
            SyntaxKind::OpenParenToken => self.parse_parenthesized_expression(),
            SyntaxKind::OpenBracketToken => self.parse_array_literal(),
            SyntaxKind::OpenBraceToken => self.parse_object_literal(),
            SyntaxKind::TemplateHead => self.parse_template_expression(),
            SyntaxKind::LessThanToken if self.language_variant == LanguageVariant::Jsx => {
                self.parse_jsx_element(false)
            }
            _ => {
                let position = if self.current.kind == SyntaxKind::EndOfFile {
                    let position = self.current.full_start;
                    self.error_code_at(TextRange::new(position, position), 1109, []);
                    position
                } else {
                    self.error_current("Expected an expression.");
                    self.current.range.start
                };
                if self.current.kind != SyntaxKind::Unknown
                    && self.current.kind != SyntaxKind::EqualsGreaterThanToken
                    && binary_precedence(self.current.kind).is_none()
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
        // A type assertion consumes a unary expression, but `yield` is not a
        // unary expression in this grammar. Leave it for the following
        // expression statement so recovery matches TypeScript's `; yield x;`
        // emit rather than incorrectly accepting `<T> yield x`.
        let expression = if self.current.kind == SyntaxKind::YieldKeyword {
            let position = self.current.range.start;
            self.error_current("Expected an expression.");
            self.missing_identifier(position)
        } else {
            self.parse_postfix_expression()
        };
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
            if self.current.kind == SyntaxKind::CommaToken {
                let position = self.current.range.start;
                elements.push(self.alloc_node(
                    SyntaxKind::OmittedExpression,
                    TextRange::new(position, position),
                    NodeData::OmittedExpression(Box::new(OmittedExpressionData)),
                    &[],
                ));
                self.bump();
                trailing = self.current.kind == SyntaxKind::CloseBracketToken;
                continue;
            }
            elements.push(self.parse_spread_element_or_expression());
            if self.current.kind == SyntaxKind::ColonToken {
                // Recover an object/type-like `name: value` fragment inside an array as two
                // elements. This is the same statement-level recovery used after a malformed
                // class member such as `{ [name: string]: T }`.
                self.error_current("Expected ','.");
                self.bump();
                trailing = false;
                continue;
            }
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
        let mut has_recovered_missing_colon = false;
        while self.current.kind != SyntaxKind::CloseBraceToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            if self.current.kind == SyntaxKind::CommaToken {
                self.error_current("Property assignment expected.");
                self.bump();
                trailing = self.current.kind == SyntaxKind::CloseBraceToken;
                continue;
            }
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
                    trailing = self.current.kind == SyntaxKind::CloseBraceToken;
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
            while self.current.kind.is_modifier() && !self.current_modifier_is_member_name() {
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
            if matches!(
                self.current.kind,
                SyntaxKind::GetKeyword | SyntaxKind::SetKeyword
            ) && self.is_accessor_signature()
            {
                properties.push(self.parse_class_accessor(
                    property_start,
                    modifiers,
                    modifier_nodes,
                    true,
                ));
                if self.current.kind != SyntaxKind::CommaToken {
                    break;
                }
                self.bump();
                trailing = self.current.kind == SyntaxKind::CloseBraceToken;
                continue;
            }
            let asterisk_token = if self.current.kind == SyntaxKind::AsteriskToken {
                Some(self.consume_token_node())
            } else {
                None
            };
            let is_async_method = modifier_nodes.iter().any(|modifier| {
                self.arena
                    .get(*modifier)
                    .is_some_and(|modifier| modifier.kind == SyntaxKind::AsyncKeyword)
            });
            let name = self.parse_property_name("Expected a property name.");
            let recovered_object_index_signature = self.current.kind == SyntaxKind::ColonToken
                && matches!(
                    self.arena.get(name).map(|node| &node.data),
                    Some(NodeData::ComputedPropertyName(computed))
                        if self.node_end(name) == self.node_end(computed.expression)
                );
            let postfix_token = if self.current.kind == SyntaxKind::QuestionToken {
                Some(self.consume_token_node())
            } else {
                None
            };
            if matches!(
                self.current.kind,
                SyntaxKind::LessThanToken | SyntaxKind::OpenParenToken
            ) {
                let previous_await_context = self.await_context;
                let previous_yield_context = self.yield_context;
                self.await_context = is_async_method;
                self.yield_context = asterisk_token.is_some();
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
                children.extend(postfix_token);
                extend_list_children(&mut children, type_parameters.as_ref());
                children.extend(parameters.nodes.iter().copied());
                children.extend(return_type);
                children.extend(body);
                self.await_context = previous_await_context;
                self.yield_context = previous_yield_context;
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
                        postfix_token,
                        symbol: None,
                        type_: return_type,
                        type_parameters,
                        facts: 0,
                        modifiers,
                        name,
                    })),
                    &children,
                ));
            } else if self.current.kind == SyntaxKind::ColonToken
                || self.current_token_starts_recovered_object_property_initializer()
                || !matches!(
                    self.arena.get(name).map(|node| &node.data),
                    Some(NodeData::Identifier(_))
                )
            {
                if self.current.kind == SyntaxKind::ColonToken {
                    self.bump();
                } else {
                    self.error_current("Expected ':'.");
                    has_recovered_missing_colon = true;
                }
                let initializer = self.parse_binary_expression(2);
                let mut children = modifier_nodes.clone();
                children.push(name);
                children.extend(postfix_token);
                children.push(initializer);
                properties.push(self.alloc_node(
                    SyntaxKind::PropertyAssignment,
                    TextRange::new(property_start, self.node_end(initializer)),
                    NodeData::PropertyAssignment(Box::new(PropertyAssignmentData {
                        initializer,
                        postfix_token,
                        symbol: None,
                        type_: None,
                        facts: 0,
                        modifiers,
                        name,
                    })),
                    &children,
                ));
            } else {
                let (equals_token, object_assignment_initializer, end, mut children) =
                    if self.current.kind == SyntaxKind::EqualsToken {
                        let equals = self.consume();
                        let equals_token = self.alloc_node(
                            equals.kind,
                            equals.range,
                            NodeData::Token(Box::new(TokenData)),
                            &[],
                        );
                        let initializer = self.parse_binary_expression(2);
                        (
                            Some(equals_token),
                            Some(initializer),
                            self.node_end(initializer),
                            {
                                let mut children = vec![name];
                                children.extend(postfix_token);
                                children.extend([equals_token, initializer]);
                                children
                            },
                        )
                    } else {
                        let mut children = vec![name];
                        children.extend(postfix_token);
                        (
                            None,
                            None,
                            postfix_token
                                .map_or_else(|| self.node_end(name), |token| self.node_end(token)),
                            children,
                        )
                    };
                children.splice(0..0, modifier_nodes.iter().copied());
                properties.push(self.alloc_node(
                    SyntaxKind::ShorthandPropertyAssignment,
                    TextRange::new(property_start, end),
                    NodeData::ShorthandPropertyAssignment(Box::new(
                        ShorthandPropertyAssignmentData {
                            equals_token,
                            object_assignment_initializer,
                            postfix_token,
                            symbol: None,
                            type_: None,
                            facts: 0,
                            modifiers,
                            name,
                        },
                    )),
                    &children,
                ));
            }
            if recovered_object_index_signature
                && self.current.kind == SyntaxKind::CloseBracketToken
            {
                self.bump();
                if self.current.kind == SyntaxKind::ColonToken {
                    self.bump();
                    let recovered_start = self.current.range.start;
                    let recovered_name = self.parse_property_name("Expected a property name.");
                    properties.push(self.alloc_node(
                        SyntaxKind::ShorthandPropertyAssignment,
                        TextRange::new(recovered_start, self.node_end(recovered_name)),
                        NodeData::ShorthandPropertyAssignment(Box::new(
                            ShorthandPropertyAssignmentData {
                                equals_token: None,
                                object_assignment_initializer: None,
                                postfix_token: None,
                                symbol: None,
                                type_: None,
                                facts: 0,
                                modifiers: None,
                                name: recovered_name,
                            },
                        )),
                        &[recovered_name],
                    ));
                }
            }
            if !matches!(
                self.current.kind,
                SyntaxKind::CommaToken | SyntaxKind::SemicolonToken
            ) {
                break;
            }
            let separator = self.current.kind;
            self.bump();
            trailing = separator == SyntaxKind::CommaToken
                && self.current.kind == SyntaxKind::CloseBraceToken;
        }
        let end =
            if self.current.kind == SyntaxKind::CloseBraceToken && !has_recovered_missing_colon {
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

    fn current_token_starts_recovered_object_property_initializer(&self) -> bool {
        matches!(
            self.current.kind,
            SyntaxKind::Identifier
                | SyntaxKind::PrivateIdentifier
                | SyntaxKind::NumericLiteral
                | SyntaxKind::BigIntLiteral
                | SyntaxKind::StringLiteral
                | SyntaxKind::NoSubstitutionTemplateLiteral
                | SyntaxKind::NullKeyword
                | SyntaxKind::TrueKeyword
                | SyntaxKind::FalseKeyword
                | SyntaxKind::UndefinedKeyword
                | SyntaxKind::ThisKeyword
                | SyntaxKind::SuperKeyword
                | SyntaxKind::NewKeyword
                | SyntaxKind::FunctionKeyword
                | SyntaxKind::ClassKeyword
                | SyntaxKind::OpenParenToken
                | SyntaxKind::OpenBracketToken
                | SyntaxKind::OpenBraceToken
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
        if self.current.kind == SyntaxKind::ColonToken {
            self.bump();
        }
        let type_arguments = if self.javascript_file {
            None
        } else {
            self.parse_type_arguments()
        };
        let recovered_attribute = if self.current.kind == SyntaxKind::EqualsToken {
            let attribute_start = self.current.range.start;
            self.current = self.scanner.scan_jsx_attribute_value();
            if self.current.kind == SyntaxKind::OpenBraceToken {
                self.bump();
                let expression = self.parse_binary_expression(0);
                let end = if self.current.kind == SyntaxKind::CloseBraceToken {
                    self.consume().range.end
                } else {
                    self.node_end(expression)
                };
                Some(self.alloc_node(
                    SyntaxKind::JsxSpreadAttribute,
                    TextRange::new(attribute_start, end),
                    NodeData::JsxSpreadAttribute(Box::new(JsxSpreadAttributeData { expression })),
                    &[expression],
                ))
            } else {
                None
            }
        } else {
            None
        };
        let attributes = self.parse_jsx_attributes(recovered_attribute);
        let mut element_children = vec![tag_name];
        extend_list_children(&mut element_children, type_arguments.as_ref());
        element_children.push(attributes);
        if self.current.kind != SyntaxKind::GreaterThanToken {
            self.expect_and_bump(SyntaxKind::SlashToken, "Expected '/'.");
            let end = self.finish_jsx_tag(resume_jsx);
            return self.alloc_node(
                SyntaxKind::JsxSelfClosingElement,
                TextRange::new(start, end),
                NodeData::JsxSelfClosingElement(Box::new(JsxSelfClosingElementData {
                    attributes,
                    tag_name,
                    type_arguments,
                    facts: 0,
                })),
                &element_children,
            );
        }
        let opening_end = self.finish_jsx_tag(true);
        let opening = self.alloc_node(
            SyntaxKind::JsxOpeningElement,
            TextRange::new(start, opening_end),
            NodeData::JsxOpeningElement(Box::new(JsxOpeningElementData {
                attributes,
                tag_name,
                type_arguments,
                facts: 0,
            })),
            &element_children,
        );
        let children = self.parse_jsx_children(opening);
        let closing_start = self.current.range.start;
        self.parse_jsx_closing_tag_start();
        let missing_closing_tag = self.current.kind == SyntaxKind::EndOfFile;
        let closing_name = if missing_closing_tag {
            self.missing_identifier(closing_start)
        } else {
            self.parse_jsx_tag_name("Expected a JSX closing tag name.")
        };
        let source_text = self.arena.source_text();
        let tag_text = |node: NodeId| {
            let range = self.arena.get(node)?.range;
            source_text?.get(range.start.get() as usize..range.end.get() as usize)
        };
        if !missing_closing_tag
            && tag_text(tag_name) != tag_text(closing_name)
            && let Some(opening_name) = tag_text(tag_name).map(str::to_owned)
        {
            let range = self.arena.get(closing_name).unwrap().range;
            self.error_code_at(range, 17002, [opening_name]);
        }
        let end = if missing_closing_tag {
            closing_start
        } else {
            self.finish_jsx_tag(resume_jsx)
        };
        let closing = self.alloc_node(
            SyntaxKind::JsxClosingElement,
            TextRange::new(closing_start, end),
            NodeData::JsxClosingElement(Box::new(JsxClosingElementData {
                tag_name: closing_name,
            })),
            &[closing_name],
        );
        if self.current.kind == SyntaxKind::ConflictMarkerTrivia {
            let checkpoint = self.scanner.mark();
            let next = if resume_jsx {
                self.scanner.scan_jsx_token()
            } else {
                self.scanner.scan()
            };
            if next.kind == SyntaxKind::EndOfFile {
                self.current = next;
            } else {
                self.scanner.rewind(checkpoint);
            }
        }
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

    fn parse_jsx_children(&mut self, opening: NodeId) -> Vec<NodeId> {
        let mut children = Vec::new();
        loop {
            self.current = self.scanner.rescan_jsx_token(true);
            if self.current.kind == SyntaxKind::EndOfFile {
                let diagnostic = match self.arena.get(opening).map(|node| &node.data) {
                    Some(NodeData::JsxOpeningElement(element)) => {
                        let range = self.arena.get(element.tag_name).unwrap().range;
                        let name = self
                            .arena
                            .source_text()
                            .and_then(|source| {
                                source.get(range.start.get() as usize..range.end.get() as usize)
                            })
                            .unwrap_or_default()
                            .to_owned();
                        Some((range, 17008, Some(name)))
                    }
                    Some(NodeData::JsxOpeningFragment(_)) => self
                        .arena
                        .get(opening)
                        .map(|node| (node.range, 17014, None)),
                    _ => None,
                };
                if let Some((range, code, name)) = diagnostic {
                    self.error_code_at(range, code, name);
                }
                break;
            }
            if matches!(
                self.current.kind,
                SyntaxKind::LessThanSlashToken | SyntaxKind::ConflictMarkerTrivia
            ) {
                break;
            }
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
        if self.current.kind == SyntaxKind::ConflictMarkerTrivia {
            while children.last().is_some_and(|child| {
                self.arena
                    .get(*child)
                    .is_some_and(|node| node.kind == SyntaxKind::JsxTextAllWhiteSpaces)
            }) {
                children.pop();
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
        let children = self.parse_jsx_children(opening);
        let closing_start = self.current.range.start;
        self.parse_jsx_closing_tag_start();
        let end = if self.current.kind == SyntaxKind::EndOfFile {
            closing_start
        } else {
            self.finish_jsx_tag(resume_jsx)
        };
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

    fn parse_jsx_closing_tag_start(&mut self) {
        if self.current.kind == SyntaxKind::LessThanSlashToken {
            self.current = self.scanner.scan();
            return;
        }
        if !self.diagnostics.iter().any(|diagnostic| {
            diagnostic.range.start == self.current.range.start
                && diagnostic.code == Some(1005)
                && diagnostic.message == "'</' expected."
        }) {
            self.error_current("Expected '</'.");
        }
    }

    fn parse_jsx_attributes(&mut self, recovered_attribute: Option<NodeId>) -> NodeId {
        let start = self.current.full_start;
        let mut attributes = recovered_attribute.into_iter().collect::<Vec<_>>();
        while matches!(
            self.current.kind,
            SyntaxKind::Identifier | SyntaxKind::OpenBraceToken
        ) || self.current.kind.is_keyword()
        {
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
            let name = self.parse_jsx_name("Expected a JSX attribute name.");
            let initializer = if self.current.kind == SyntaxKind::EqualsToken {
                self.current = self.scanner.scan_jsx_attribute_value();
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
        if self.current.kind == SyntaxKind::ColonToken {
            self.error_current("Expected a JSX attribute name.");
            self.bump();
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
        let mut expression = self.parse_jsx_name(message);
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

    fn parse_jsx_name(&mut self, message: &str) -> NodeId {
        self.current = self.scanner.scan_jsx_identifier();
        let namespace = self.parse_identifier_name(message);
        if self.current.kind != SyntaxKind::ColonToken {
            return namespace;
        }
        self.bump();
        self.current = self.scanner.scan_jsx_identifier();
        let name = self.parse_identifier_name(message);
        self.alloc_node(
            SyntaxKind::JsxNamespacedName,
            TextRange::new(self.node_start(namespace), self.node_end(name)),
            NodeData::JsxNamespacedName(Box::new(JsxNamespacedNameData {
                namespace,
                facts: 0,
                name,
            })),
            &[namespace, name],
        )
    }

    fn parse_identifier(&mut self, message: &str) -> NodeId {
        if !matches!(
            self.current.kind,
            SyntaxKind::Identifier | SyntaxKind::RequireKeyword
        ) {
            let position = self.current.range.start;
            self.error_current(message);
            return self.missing_identifier(position);
        }
        let token = self.consume();
        let text = token_value(&token);
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

    fn parse_identifier_in_current_context(&mut self, message: &str) -> NodeId {
        if self.token_is_identifier_in_current_context(self.current.kind) {
            return self.parse_identifier_name(message);
        }
        let position = self.current.range.start;
        self.error_current(message);
        self.missing_identifier(position)
    }

    fn parse_import_binding_identifier(&mut self, message: &str) -> NodeId {
        if self.token_is_identifier_in_current_context(self.current.kind) {
            return self.parse_identifier_name(message);
        }
        if self.current.kind.is_keyword() {
            self.error_current(message);
            let token = self.consume();
            return self.alloc_node_with_flags(
                SyntaxKind::Identifier,
                NODE_FLAG_HAS_ERROR,
                token.range,
                NodeData::Identifier(Box::new(IdentifierData {
                    flow_node: None,
                    text: token_value(&token),
                })),
                &[],
            );
        }
        if self.current.kind == SyntaxKind::StringLiteral {
            self.error_current(message);
            let name = self.parse_string_literal();
            if let Some(node) = self.arena.get_mut(name) {
                node.flags.0 |= NODE_FLAG_HAS_ERROR.0;
            }
            return name;
        }
        let position = self.current.range.start;
        self.error_current(message);
        self.missing_identifier(position)
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
            SyntaxKind::BigIntLiteral => self.parse_bigint_literal(),
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

    fn parse_property_name_after_dot(&mut self) -> NodeId {
        if self
            .current
            .flags
            .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
            && matches!(
                self.current.kind,
                SyntaxKind::VarKeyword
                    | SyntaxKind::LetKeyword
                    | SyntaxKind::ConstKeyword
                    | SyntaxKind::NamespaceKeyword
            )
        {
            let position = self.current.range.start;
            self.error_current("Expected a property name.");
            self.missing_identifier(position)
        } else {
            self.parse_property_name("Expected a property name.")
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
        let token_flags = TokenFlags(if token.flags.contains(ScannerTokenFlags::OCTAL) {
            1 << 5
        } else {
            0
        });
        self.alloc_node(
            SyntaxKind::NumericLiteral,
            token.range,
            NodeData::NumericLiteral(Box::new(NumericLiteralData {
                text: token_value(&token),
                token_flags,
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
                text: token_value(&token),
                token_flags: TokenFlags::default(),
            })),
            &[],
        )
    }

    fn parse_string_literal(&mut self) -> NodeId {
        let token = self.consume();
        let token_flags = TokenFlags(if token.flags.contains(ScannerTokenFlags::UNTERMINATED) {
            1 << 2
        } else {
            0
        });
        let text = token_value(&token);
        self.alloc_node(
            SyntaxKind::StringLiteral,
            token.range,
            NodeData::StringLiteral(Box::new(StringLiteralData { text, token_flags })),
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
        let is_async = self.next_function_is_async;
        self.next_function_is_async = false;
        let previous_await_context = self.await_context;
        let previous_yield_context = self.yield_context;
        self.await_context = is_async;
        let start = self.consume().range.start;
        let asterisk_token =
            (self.current.kind == SyntaxKind::AsteriskToken).then(|| self.consume_token_node());
        self.yield_context = asterisk_token.is_some();
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
        self.await_context = previous_await_context;
        self.yield_context = previous_yield_context;
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
        let previous_next_function_is_async = self.next_function_is_async;
        self.next_function_is_async = true;
        let expression = self.parse_function_expression();
        self.next_function_is_async = previous_next_function_is_async;
        self.attach_modifiers(expression, vec![async_modifier], start);
        expression
    }

    fn parse_template_literal(&mut self) -> NodeId {
        let token = self.consume();
        let text = token_value(&token);
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
        if self.current.kind != SyntaxKind::ExtendsKeyword
            || self.next_token_kind() == SyntaxKind::QuestionToken
        {
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

    #[allow(clippy::too_many_lines)] // Type operator grammar is one dispatch.
    fn parse_type_operator_or_postfix(&mut self) -> NodeId {
        if self.current.kind == SyntaxKind::ExclamationToken {
            let start = self.consume().range.start;
            let type_node = self.parse_type_operator_or_postfix();
            return self.alloc_non_nullable_type(
                type_node,
                TextRange::new(start, self.node_end(type_node)),
            );
        }
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
        loop {
            if self.current.kind == SyntaxKind::ExclamationToken
                && !self
                    .current
                    .flags
                    .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
            {
                let end = self.consume().range.end;
                type_node = self.alloc_non_nullable_type(
                    type_node,
                    TextRange::new(self.node_start(type_node), end),
                );
                continue;
            }
            if self.current.kind == SyntaxKind::QuestionToken
                && self.type_parse_context != TypeParseContext::ExpressionCast
                && !self
                    .current
                    .flags
                    .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
                && !self.next_token_starts_type()
                && !self.postfix_question_belongs_to_tuple()
            {
                let end = self.consume().range.end;
                type_node = self.alloc_node(
                    SyntaxKind::JsDocNullableType,
                    TextRange::new(self.node_start(type_node), end),
                    NodeData::JsDocNullableType(Box::new(JsDocNullableTypeData {
                        type_: type_node,
                    })),
                    &[type_node],
                );
                continue;
            }
            if self.current.kind != SyntaxKind::OpenBracketToken {
                break;
            }
            if self
                .current
                .flags
                .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
                && (self.is_index_signature() || self.line_broken_bracket_starts_method())
            {
                break;
            }
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
                continue;
            }
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
        type_node
    }

    fn postfix_question_belongs_to_tuple(&mut self) -> bool {
        self.type_parse_context == TypeParseContext::TupleElement
            && matches!(
                self.next_token_kind(),
                SyntaxKind::CommaToken | SyntaxKind::CloseBracketToken
            )
    }

    fn alloc_non_nullable_type(&mut self, type_node: NodeId, range: TextRange) -> NodeId {
        self.alloc_node(
            SyntaxKind::JsDocNonNullableType,
            range,
            NodeData::JsDocNonNullableType(Box::new(JsDocNonNullableTypeData { type_: type_node })),
            &[type_node],
        )
    }

    fn line_broken_bracket_starts_method(&mut self) -> bool {
        if self.current.kind != SyntaxKind::OpenBracketToken {
            return false;
        }
        let checkpoint = self.scanner.mark();
        let name = self.scanner.scan().kind;
        let close = self.scanner.scan().kind;
        let mut next = self.scanner.scan().kind;
        if matches!(
            next,
            SyntaxKind::QuestionToken | SyntaxKind::ExclamationToken
        ) {
            next = self.scanner.scan().kind;
        }
        self.scanner.rewind(checkpoint);
        matches!(
            name,
            SyntaxKind::Identifier
                | SyntaxKind::StringLiteral
                | SyntaxKind::NumericLiteral
                | SyntaxKind::BigIntLiteral
        ) && close == SyntaxKind::CloseBracketToken
            && matches!(next, SyntaxKind::OpenParenToken | SyntaxKind::LessThanToken)
    }

    fn next_token_starts_type(&mut self) -> bool {
        let checkpoint = self.scanner.mark();
        let kind = self.scanner.scan().kind;
        self.scanner.rewind(checkpoint);
        is_type_start_kind(kind)
    }

    fn parse_jsdoc_nullable_type(&mut self) -> NodeId {
        let start = self.consume().range.start;
        let type_node = self.parse_type_operator_or_postfix();
        self.alloc_node(
            SyntaxKind::JsDocNullableType,
            TextRange::new(start, self.node_end(type_node)),
            NodeData::JsDocNullableType(Box::new(JsDocNullableTypeData { type_: type_node })),
            &[type_node],
        )
    }

    #[allow(clippy::too_many_lines)]
    fn parse_primary_type(&mut self) -> NodeId {
        let parenthesized_function = self.current.kind == SyntaxKind::OpenParenToken
            && self.is_parenthesized_function_type();
        let mapped_type = self.current.kind == SyntaxKind::OpenBraceToken && self.is_mapped_type();
        let qualified_this = self.current.kind == SyntaxKind::ThisKeyword
            && self.next_token_kind() == SyntaxKind::DotToken;
        match self.current.kind {
            SyntaxKind::QuestionToken => self.parse_jsdoc_nullable_type(),
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
            SyntaxKind::ThisKeyword if qualified_this => self.parse_type_reference(),
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
            SyntaxKind::AsteriskToken => {
                let token = self.consume();
                self.alloc_node(
                    SyntaxKind::JsDocAllType,
                    token.range,
                    NodeData::JsDocAllType(Box::new(JsDocAllTypeData)),
                    &[],
                )
            }
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
        let mut type_name =
            if self.current.kind == SyntaxKind::Identifier || self.current.kind.is_keyword() {
                self.parse_identifier_name("Expected a type name.")
            } else {
                self.parse_identifier("Expected a type name.")
            };
        while self.current.kind == SyntaxKind::DotToken {
            self.bump();
            let right = self.parse_identifier_name("Expected an identifier after '.'.");
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
        let type_arguments = self.parse_type_arguments_of_type_reference();
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
        let return_type = if self.current.kind == SyntaxKind::ColonToken {
            self.error_current("Expected '=>'.");
            self.bump();
            self.missing_identifier(self.current.range.start)
        } else {
            self.expect_and_bump(SyntaxKind::EqualsGreaterThanToken, "Expected '=>'.");
            self.parse_type()
        };
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
        if self.current.kind == SyntaxKind::ImportKeyword {
            let import_type = self.parse_import_type();
            let node = self.arena.get_mut(import_type).unwrap();
            node.range.start = start;
            let NodeData::ImportTypeNode(import) = &mut node.data else {
                unreachable!("parse_import_type must return an import type node");
            };
            import.is_type_of = true;
            return import_type;
        }
        let expr_name = self.parse_entity_name(true);
        let type_arguments = self.parse_type_arguments_of_type_reference();
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
        let attributes = if self.current.kind == SyntaxKind::CommaToken {
            self.bump();
            self.parse_import_type_attributes()
        } else {
            None
        };
        self.expect_and_bump(SyntaxKind::CloseParenToken, "Expected ')'.");
        let qualifier = if self.current.kind == SyntaxKind::DotToken {
            self.bump();
            Some(self.parse_entity_name(true))
        } else {
            None
        };
        let type_arguments = self.parse_type_arguments_of_type_reference();
        let end = type_arguments.as_ref().map_or_else(
            || qualifier.map_or_else(|| self.node_end(argument), |node| self.node_end(node)),
            |arguments| arguments.range.end,
        );
        let mut children = vec![argument];
        children.extend(attributes);
        children.extend(qualifier);
        extend_list_children(&mut children, type_arguments.as_ref());
        self.alloc_node(
            SyntaxKind::ImportType,
            TextRange::new(start, end),
            NodeData::ImportTypeNode(Box::new(ImportTypeNodeData {
                argument,
                attributes,
                is_type_of: false,
                qualifier,
                type_arguments,
            })),
            &children,
        )
    }

    #[allow(clippy::too_many_lines)]
    fn parse_import_type_attributes(&mut self) -> Option<NodeId> {
        if self.current.kind != SyntaxKind::OpenBraceToken {
            self.error_current("Expected '{'.");
            return None;
        }
        self.bump();
        let keyword = if matches!(
            self.current.kind,
            SyntaxKind::WithKeyword | SyntaxKind::AssertKeyword
        ) {
            self.consume()
        } else {
            self.error_current("Expected 'with'.");
            return None;
        };
        self.expect_and_bump(SyntaxKind::ColonToken, "Expected ':'.");
        self.expect_and_bump(SyntaxKind::OpenBraceToken, "Expected '{'.");
        let list_start = self.current.range.start;
        let mut attributes = Vec::new();
        while !matches!(
            self.current.kind,
            SyntaxKind::CloseBraceToken | SyntaxKind::EndOfFile
        ) {
            if !matches!(
                self.current.kind,
                SyntaxKind::Identifier | SyntaxKind::StringLiteral
            ) && !self.current.kind.is_keyword()
            {
                self.error_current("Expected an import attribute name.");
                return Some(self.alloc_node(
                    SyntaxKind::ImportAttributes,
                    TextRange::new(keyword.range.start, list_start),
                    NodeData::ImportAttributes(Box::new(ImportAttributesData {
                        attributes: NodeList {
                            range: TextRange::new(list_start, list_start),
                            nodes: Vec::new(),
                            has_trailing_comma: false,
                        },
                        multi_line: false,
                        token: keyword.kind,
                        facts: 0,
                    })),
                    &[],
                ));
            }
            let attribute_start = self.current.range.start;
            let name = self.parse_property_name("Expected an import attribute name.");
            self.expect_and_bump(SyntaxKind::ColonToken, "Expected ':'.");
            let value = if self.current.kind == SyntaxKind::StringLiteral {
                self.parse_string_literal()
            } else {
                let value = self.parse_binary_expression(2);
                let range = self
                    .arena
                    .get(value)
                    .map_or(TextRange::new(attribute_start, attribute_start), |node| {
                        node.range
                    });
                self.error_code_at(range, 2858, []);
                value
            };
            attributes.push(self.alloc_node(
                SyntaxKind::ImportAttribute,
                TextRange::new(attribute_start, self.node_end(value)),
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
        let inner_end = if self.current.kind == SyntaxKind::CloseBraceToken {
            self.consume().range.end
        } else {
            self.error_current("Expected '}'.");
            attributes
                .last()
                .map_or(list_start, |attribute| self.node_end(*attribute))
        };
        let end = if self.current.kind == SyntaxKind::CloseBraceToken {
            self.consume().range.end
        } else {
            self.error_current("Expected '}'.");
            inner_end
        };
        Some(self.alloc_node(
            SyntaxKind::ImportAttributes,
            TextRange::new(keyword.range.start, end),
            NodeData::ImportAttributes(Box::new(ImportAttributesData {
                attributes: NodeList {
                    range: TextRange::new(list_start, inner_end),
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
        let constraint = if self.current.kind == SyntaxKind::ExtendsKeyword {
            self.bump();
            Some(self.parse_union_type())
        } else {
            None
        };
        let end = constraint.map_or_else(|| self.node_end(name), |node| self.node_end(node));
        let mut children = vec![name];
        children.extend(constraint);
        let type_parameter = self.alloc_node(
            SyntaxKind::TypeParameter,
            TextRange::new(self.node_start(name), end),
            NodeData::TypeParameterDeclaration(Box::new(TypeParameterDeclarationData {
                constraint,
                default_type: None,
                expression: None,
                symbol: None,
                modifiers: None,
                name,
            })),
            &children,
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
            let dot_dot_dot_token = (self.current.kind == SyntaxKind::DotDotDotToken)
                .then(|| self.consume_token_node());
            let named = self.current.kind == SyntaxKind::Identifier
                && (self.next_token_kind() == SyntaxKind::ColonToken
                    || self.next_tokens_are(SyntaxKind::QuestionToken, SyntaxKind::ColonToken));
            if named {
                let name = self.parse_identifier("Expected a tuple element name.");
                let question_token = (self.current.kind == SyntaxKind::QuestionToken)
                    .then(|| self.consume_token_node());
                self.expect_and_bump(SyntaxKind::ColonToken, "Expected ':'.");
                let type_node = self.parse_type();
                let member_start = dot_dot_dot_token
                    .map_or_else(|| self.node_start(name), |token| self.node_start(token));
                let mut children = Vec::new();
                children.extend(dot_dot_dot_token);
                children.push(name);
                children.extend(question_token);
                children.push(type_node);
                elements.push(self.alloc_node(
                    SyntaxKind::NamedTupleMember,
                    TextRange::new(member_start, self.node_end(type_node)),
                    NodeData::NamedTupleMember(Box::new(NamedTupleMemberData {
                        dot_dot_dot_token,
                        question_token,
                        symbol: None,
                        type_: type_node,
                        name,
                    })),
                    &children,
                ));
            } else if let Some(dot_dot_dot_token) = dot_dot_dot_token {
                let rest_start = self.node_start(dot_dot_dot_token);
                let type_node = self.parse_type();
                elements.push(self.alloc_node(
                    SyntaxKind::RestType,
                    TextRange::new(rest_start, self.node_end(type_node)),
                    NodeData::RestTypeNode(Box::new(RestTypeNodeData { type_: type_node })),
                    &[dot_dot_dot_token, type_node],
                ));
            } else {
                let previous_context = self.type_parse_context;
                self.type_parse_context = TypeParseContext::TupleElement;
                let type_node = self.parse_type();
                self.type_parse_context = previous_context;
                if self.current.kind == SyntaxKind::QuestionToken {
                    let end = self.consume().range.end;
                    elements.push(self.alloc_node(
                        SyntaxKind::OptionalType,
                        TextRange::new(self.node_start(type_node), end),
                        NodeData::OptionalTypeNode(Box::new(OptionalTypeNodeData {
                            type_: type_node,
                        })),
                        &[type_node],
                    ));
                } else {
                    elements.push(type_node);
                }
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
        let mut has_trailing_comma = false;
        while self.current.kind != SyntaxKind::GreaterThanToken
            && self.current.kind != SyntaxKind::EndOfFile
        {
            arguments.push(self.parse_type());
            if self.current.kind != SyntaxKind::CommaToken {
                break;
            }
            self.bump();
            has_trailing_comma = self.current.kind == SyntaxKind::GreaterThanToken;
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
            has_trailing_comma,
        })
    }

    fn parse_type_arguments_of_type_reference(&mut self) -> Option<NodeList> {
        if self
            .current
            .flags
            .contains(ScannerTokenFlags::PRECEDING_LINE_BREAK)
        {
            return None;
        }
        if self.current.kind == SyntaxKind::LessThanLessThanToken {
            self.current = self.scanner.rescan_less_than_token();
        }
        self.parse_type_arguments()
    }

    fn parse_type_member_terminator(&mut self, fallback_end: TextPos) -> TextPos {
        if self.current.kind == SyntaxKind::CommaToken {
            self.bump();
            fallback_end
        } else {
            self.parse_semicolon(fallback_end)
        }
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
        if self
            .diagnostics
            .last()
            .is_some_and(|diagnostic| diagnostic.range.start == self.current.range.start)
        {
            return;
        }
        self.diagnostics
            .push(parser_diagnostic(self.current.range, message));
    }

    fn error_code_at(
        &mut self,
        range: TextRange,
        code: u32,
        arguments: impl IntoIterator<Item = String>,
    ) {
        if self
            .diagnostics
            .last()
            .is_some_and(|diagnostic| diagnostic.range.start == range.start)
        {
            return;
        }
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
        self.alloc_token_node(token.kind, token.range)
    }

    fn alloc_token_node(&mut self, kind: SyntaxKind, range: TextRange) -> NodeId {
        self.alloc_node(kind, range, NodeData::Token(Box::new(TokenData)), &[])
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

impl Parser<'_> {
    fn parse_isolated_entity_name(mut self) -> Option<IsolatedEntityName> {
        let entity = self.parse_entity_name(true);

        if self.current.kind != SyntaxKind::EndOfFile
            || !self.diagnostics.is_empty()
            || !self.scanner.diagnostics().is_empty()
        {
            return None;
        }

        for index in 0..self.arena.len() {
            let index = u32::try_from(index).expect("AST node arena exceeds u32::MAX nodes");
            self.arena
                .get_mut(NodeId::new(index))
                .expect("allocated entity-name node exists")
                .flags = NodeFlags::JAVASCRIPT_FILE;
        }
        Some(IsolatedEntityName {
            arena: self.arena,
            root: entity,
        })
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
        .map_or_else(|| token.text.to_owned(), ts_ast::encode_js_string)
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
        "Expected an import attribute name." => Some((1478, Vec::new())),
        "Declaration or statement expected." => Some((1128, Vec::new())),
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
            | SyntaxKind::ColonToken
            | SyntaxKind::CloseParenToken
            | SyntaxKind::CloseBracketToken
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

fn is_import_binding_identifier_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Identifier | SyntaxKind::RequireKeyword | SyntaxKind::YieldKeyword
    ) || is_contextual_keyword(kind)
}

fn is_module_name_token(kind: SyntaxKind) -> bool {
    matches!(kind, SyntaxKind::Identifier | SyntaxKind::RequireKeyword)
        || is_contextual_keyword(kind)
}

fn can_parse_module_export_name(kind: SyntaxKind) -> bool {
    kind == SyntaxKind::Identifier || kind == SyntaxKind::StringLiteral || kind.is_keyword()
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

fn token_starts_argument_expression(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Identifier
            | SyntaxKind::PrivateIdentifier
            | SyntaxKind::NumericLiteral
            | SyntaxKind::BigIntLiteral
            | SyntaxKind::StringLiteral
            | SyntaxKind::ImportKeyword
            | SyntaxKind::FunctionKeyword
            | SyntaxKind::ClassKeyword
            | SyntaxKind::AtToken
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::NullKeyword
            | SyntaxKind::TrueKeyword
            | SyntaxKind::FalseKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::ThisKeyword
            | SyntaxKind::SuperKeyword
            | SyntaxKind::ImplementsKeyword
            | SyntaxKind::InterfaceKeyword
            | SyntaxKind::LetKeyword
            | SyntaxKind::PackageKeyword
            | SyntaxKind::StaticKeyword
            | SyntaxKind::OpenParenToken
            | SyntaxKind::OpenBracketToken
            | SyntaxKind::OpenBraceToken
            | SyntaxKind::TemplateHead
            | SyntaxKind::LessThanToken
            | SyntaxKind::SlashToken
            | SyntaxKind::SlashEqualsToken
            | SyntaxKind::AwaitKeyword
            | SyntaxKind::YieldKeyword
            | SyntaxKind::TypeOfKeyword
            | SyntaxKind::VoidKeyword
            | SyntaxKind::DeleteKeyword
            | SyntaxKind::NewKeyword
    ) || is_keyword_type(kind)
        || is_contextual_keyword(kind)
        || is_prefix_operator(kind)
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

fn is_type_start_kind(kind: SyntaxKind) -> bool {
    kind == SyntaxKind::Identifier
        || is_keyword_type(kind)
        || matches!(
            kind,
            SyntaxKind::ThisKeyword
                | SyntaxKind::TypeOfKeyword
                | SyntaxKind::ImportKeyword
                | SyntaxKind::NewKeyword
                | SyntaxKind::AbstractKeyword
                | SyntaxKind::InferKeyword
                | SyntaxKind::KeyOfKeyword
                | SyntaxKind::ReadonlyKeyword
                | SyntaxKind::UniqueKeyword
                | SyntaxKind::OpenBraceToken
                | SyntaxKind::OpenBracketToken
                | SyntaxKind::OpenParenToken
                | SyntaxKind::LessThanToken
                | SyntaxKind::TemplateHead
                | SyntaxKind::StringLiteral
                | SyntaxKind::NumericLiteral
                | SyntaxKind::BigIntLiteral
                | SyntaxKind::NoSubstitutionTemplateLiteral
                | SyntaxKind::TrueKeyword
                | SyntaxKind::FalseKeyword
                | SyntaxKind::NullKeyword
                | SyntaxKind::MinusToken
                | SyntaxKind::QuestionToken
        )
}

fn invalid_arrow_parameter_start(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::OpenParenToken
            | SyntaxKind::NumericLiteral
            | SyntaxKind::BigIntLiteral
            | SyntaxKind::StringLiteral
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::TrueKeyword
            | SyntaxKind::FalseKeyword
            | SyntaxKind::NullKeyword
    )
}

fn invalid_arrow_parameter_expression(
    depths: (u32, u32, u32),
    previous: SyntaxKind,
    current: SyntaxKind,
) -> bool {
    depths == (1, 0, 0) && previous.is_binary_operator() && current.is_assignment_operator()
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
        // `??` and `||` share the ShortCircuitExpression precedence. Keeping
        // them equal is also important for error recovery: invalid unparenthesized
        // mixtures are parsed left-associatively before the checker reports
        // TS5076.
        SyntaxKind::QuestionQuestionToken | SyntaxKind::BarBarToken => (4, false),
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
    use ts_ast::{ModifierFlags, NodeData, NodeFlags, NodeId, SyntaxKind};
    use ts_core::DiagnosticCategory;

    use super::{
        NODE_FLAG_AWAIT_USING, NODE_FLAG_HAS_ERROR, NODE_FLAG_USING, ParseResult,
        parse_isolated_entity_name, parse_javascript_source_file, parse_jsdoc_comment,
        parse_jsx_source_file, parse_source_file, text_range,
    };

    #[test]
    fn parses_exact_isolated_entity_names_in_javascript_context() {
        let parsed = parse_isolated_entity_name("default . Namespace.createElement").unwrap();
        assert_eq!(
            parsed.arena().source_text(),
            Some("default . Namespace.createElement")
        );
        assert_eq!(parsed.arena().len(), 5);
        for (_, node) in parsed.arena().iter() {
            assert_eq!(node.flags, NodeFlags::JAVASCRIPT_FILE);
        }

        let root = parsed.arena().get(parsed.root()).unwrap();
        assert_eq!(root.kind, SyntaxKind::QualifiedName);
        assert_eq!(root.parent, None);
        let NodeData::QualifiedName(root) = &root.data else {
            panic!("isolated dotted name must produce a QualifiedName")
        };
        let right_node = parsed.arena().get(root.right).unwrap();
        let NodeData::Identifier(right) = &right_node.data else {
            panic!("qualified-name right side must be an Identifier")
        };
        assert_eq!(right.text, "createElement");
        assert_eq!(right.flow_node, None);
        assert_eq!(right_node.parent, Some(parsed.root()));

        for valid in [
            "default",
            "default.class",
            "await.yield",
            "R\\u0065act.createElement",
            "/// <amd-module name='first'/>\n/// <amd-module name='second'/>\nReact.createElement",
        ] {
            assert!(
                parse_isolated_entity_name(valid).is_some(),
                "{valid:?} is an IdentifierName chain in isolated JS context"
            );
        }
    }

    #[test]
    fn isolated_entity_names_require_clean_complete_input() {
        for invalid in [
            "",
            " ",
            ".React",
            "React.",
            "React..factory",
            "React factory",
            "React.createElement()",
            "1React",
            "#private",
            "React.\\u{notHex}",
        ] {
            assert_eq!(
                parse_isolated_entity_name(invalid).map(|parsed| parsed.root()),
                None,
                "{invalid:?} must not produce a sealed entity name",
            );
        }
    }

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
    fn stores_canonical_numeric_and_bigint_values_with_original_source_ranges() {
        let source = concat!(
            "const values = [1_000, 0xCA_FE, 0b1010_0101, 0o7_7, 1e+2, ",
            "9007199254740993, 0b101n, 0o77n, 0xCAn, 12_34n];",
        );
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let numeric = result
            .arena
            .iter()
            .filter_map(|(_, node)| {
                let NodeData::NumericLiteral(literal) = &node.data else {
                    return None;
                };
                let start = usize::try_from(node.range.start.get()).unwrap();
                let end = usize::try_from(node.range.end.get()).unwrap();
                Some((literal.text.as_str(), &source[start..end]))
            })
            .collect::<Vec<_>>();
        assert_eq!(
            numeric,
            [
                ("1000", "1_000"),
                ("51966", "0xCA_FE"),
                ("165", "0b1010_0101"),
                ("63", "0o7_7"),
                ("100", "1e+2"),
                ("9007199254740992", "9007199254740993"),
            ]
        );

        let bigint = result
            .arena
            .iter()
            .filter_map(|(_, node)| {
                let NodeData::BigIntLiteral(literal) = &node.data else {
                    return None;
                };
                let start = usize::try_from(node.range.start.get()).unwrap();
                let end = usize::try_from(node.range.end.get()).unwrap();
                Some((literal.text.as_str(), &source[start..end]))
            })
            .collect::<Vec<_>>();
        assert_eq!(
            bigint,
            [
                ("5n", "0b101n"),
                ("63n", "0o77n"),
                ("0xcan", "0xCAn"),
                ("1234n", "12_34n"),
            ]
        );
    }

    #[test]
    fn preserves_lone_surrogates_in_string_and_template_literal_values() {
        let source = concat!(
            r#"type High = "\uD800"; type Low = "\uDC00";"#,
            r#"type Template = `\uD800${High}\uDC00`;"#,
            r#"const high = "\uD83D"; const low = "\uDE00";"#,
            r#"const plain = "ordinary 😀";"#,
        );
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let strings = result
            .arena
            .iter()
            .filter_map(|(_, node)| {
                let NodeData::StringLiteral(literal) = &node.data else {
                    return None;
                };
                Some((
                    literal.text.as_str(),
                    ts_ast::decode_js_string(&literal.text),
                ))
            })
            .collect::<Vec<_>>();
        assert_eq!(strings.len(), 5);
        assert_ne!(strings[0].0, strings[1].0);
        assert_eq!(strings[0].1.as_units(), &[0xd800]);
        assert_eq!(strings[1].1.as_units(), &[0xdc00]);
        assert_eq!(strings[2].1.as_units(), &[0xd83d]);
        assert_eq!(strings[3].1.as_units(), &[0xde00]);
        assert_eq!(strings[4].0, "ordinary 😀");

        let head = result
            .arena
            .iter()
            .find_map(|(_, node)| match &node.data {
                NodeData::TemplateHead(head) => Some(ts_ast::decode_js_string(&head.text)),
                _ => None,
            })
            .unwrap();
        let tail = result
            .arena
            .iter()
            .find_map(|(_, node)| match &node.data {
                NodeData::TemplateTail(tail) => Some(ts_ast::decode_js_string(&tail.text)),
                _ => None,
            })
            .unwrap();
        assert_eq!(head.as_units(), &[0xd800]);
        assert_eq!(tail.as_units(), &[0xdc00]);
    }

    #[test]
    fn parses_nullish_and_logical_or_with_shared_left_associative_precedence() {
        let result = parse_source_file(
            "const first: number = 1 ?? 2 || 3; const second: number = 1 || 2 ?? 3;",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        for (statement, root_operator, left_operator) in [
            (
                source_statements(&result)[0],
                SyntaxKind::BarBarToken,
                SyntaxKind::QuestionQuestionToken,
            ),
            (
                source_statements(&result)[1],
                SyntaxKind::QuestionQuestionToken,
                SyntaxKind::BarBarToken,
            ),
        ] {
            let (list, _) = variable_list(&result, statement);
            let declaration = declaration_nodes(&result, list)[0];
            let (_, initializer) = declaration_type_and_initializer(&result, declaration);
            let NodeData::BinaryExpression(root) = &result.arena.get(initializer).unwrap().data
            else {
                panic!("expected a mixed short-circuit expression");
            };
            assert_eq!(
                result.arena.get(root.operator_token).unwrap().kind,
                root_operator
            );
            let NodeData::BinaryExpression(left) = &result.arena.get(root.left).unwrap().data
            else {
                panic!("expected a left-associative mixed operand");
            };
            assert_eq!(
                result.arena.get(left.operator_token).unwrap().kind,
                left_operator
            );
        }
    }

    #[test]
    fn preserves_new_expressions_as_invalid_assignment_targets() {
        let result = parse_source_file("var x = new y = 5;");
        let (list, _) = variable_list(&result, source_statements(&result)[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let NodeData::BinaryExpression(assignment) = &result
            .arena
            .get(declaration.initializer.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected assignment expression");
        };
        assert_eq!(
            result.arena.get(assignment.left).unwrap().kind,
            SyntaxKind::NewExpression
        );
        assert_eq!(
            result.arena.get(assignment.operator_token).unwrap().kind,
            SyntaxKind::EqualsToken
        );

        let parenthesized = parse_source_file("(1, x) = 0;");
        let NodeData::ExpressionStatement(statement) = &parenthesized
            .arena
            .get(source_statements(&parenthesized)[0])
            .unwrap()
            .data
        else {
            panic!("expected expression statement");
        };
        let NodeData::BinaryExpression(assignment) =
            &parenthesized.arena.get(statement.expression).unwrap().data
        else {
            panic!("expected assignment expression");
        };
        assert_eq!(
            parenthesized.arena.get(assignment.left).unwrap().kind,
            SyntaxKind::ParenthesizedExpression
        );
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
    fn type_argument_lists_retain_empty_and_trailing_comma_grammar_shape() {
        let source = "type Trailing = Id<string,>; type Empty = Id<>;";
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let mut lists = result
            .arena
            .iter()
            .filter_map(|(_, node)| {
                let NodeData::TypeReferenceNode(reference) = &node.data else {
                    return None;
                };
                reference.type_arguments.as_ref()
            })
            .collect::<Vec<_>>();
        lists.sort_by_key(|list| list.range.start);

        assert_eq!(lists.len(), 2);
        assert_eq!(lists[0].nodes.len(), 1);
        assert!(lists[0].has_trailing_comma);
        assert_eq!(
            source.get(lists[0].range.start.get() as usize..lists[0].range.end.get() as usize),
            Some("<string,>")
        );
        assert!(lists[1].nodes.is_empty());
        assert!(!lists[1].has_trailing_comma);
        assert_eq!(
            source.get(lists[1].range.start.get() as usize..lists[1].range.end.get() as usize),
            Some("<>")
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
    fn accepts_require_as_a_contextual_declaration_name() {
        let result = parse_source_file(
            "namespace require {} enum require { A } import require = M.C; new require();",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let kinds = source_statements(&result)
            .iter()
            .map(|statement| result.arena.get(*statement).unwrap().kind)
            .collect::<Vec<_>>();
        assert_eq!(
            kinds,
            [
                SyntaxKind::ModuleDeclaration,
                SyntaxKind::EnumDeclaration,
                SyntaxKind::ImportEqualsDeclaration,
                SyntaxKind::ExpressionStatement,
            ]
        );
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
    fn unexpected_case_token_does_not_consume_the_next_declaration() {
        let result = parse_source_file("class Before {}\ncase\nfunction after() {}");
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [1128]
        );
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::FunctionDeclaration
        );
    }

    #[test]
    fn recovers_a_closed_for_header_as_a_continued_declaration_list() {
        let result = parse_source_file("for (let x: y) { z(x); }");
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [1005, 1005, 1109]
        );
        let NodeData::ForStatement(for_) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
        else {
            panic!("expected for statement");
        };
        let NodeData::VariableDeclarationList(list) =
            &result.arena.get(for_.initializer.unwrap()).unwrap().data
        else {
            panic!("expected variable declaration list");
        };
        assert_eq!(list.declarations.nodes.len(), 2);
        let NodeData::VariableDeclaration(second) =
            &result.arena.get(list.declarations.nodes[1]).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        assert_eq!(
            result.arena.get(second.name).unwrap().kind,
            SyntaxKind::ObjectBindingPattern
        );
        assert_eq!(
            result.arena.get(for_.statement).unwrap().kind,
            SyntaxKind::EmptyStatement
        );
    }

    #[test]
    fn preserves_semicolon_class_elements() {
        let result = parse_source_file("class C { ; value = 1; ; }");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let NodeData::ClassDeclaration(class) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
        else {
            panic!("expected class declaration");
        };
        assert_eq!(
            class
                .members
                .nodes
                .iter()
                .map(|member| result.arena.get(*member).unwrap().kind)
                .collect::<Vec<_>>(),
            [
                SyntaxKind::SemicolonClassElement,
                SyntaxKind::PropertyDeclaration,
                SyntaxKind::SemicolonClassElement,
            ]
        );
    }

    #[test]
    fn class_field_line_break_does_not_create_a_semicolon_member() {
        let result = parse_source_file(
            "class C { #x = 1\n constructor(x: number) { this.#x = x; } static { x(); } }",
        );
        let NodeData::ClassDeclaration(class) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
        else {
            panic!("expected class declaration");
        };
        assert_eq!(
            class
                .members
                .nodes
                .iter()
                .map(|member| result.arena.get(*member).unwrap().kind)
                .collect::<Vec<_>>(),
            [
                SyntaxKind::PropertyDeclaration,
                SyntaxKind::Constructor,
                SyntaxKind::ClassStaticBlockDeclaration,
            ],
            "{:?}",
            result.diagnostics,
        );
    }

    #[test]
    fn recovers_modifiers_before_class_static_blocks() {
        let result = parse_source_file(
            "class C { @dec static {} async static {} public static {} readonly private static {} }",
        );
        let NodeData::ClassDeclaration(class) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
        else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 4, "{:?}", result.diagnostics);
        assert!(class.members.nodes.iter().all(|member| {
            result.arena.get(*member).unwrap().kind == SyntaxKind::ClassStaticBlockDeclaration
        }));
    }

    #[test]
    fn recovers_await_label_inside_class_static_block() {
        let result = parse_source_file("class C { static { await: // illegal\n break await; } }");
        let kinds = result
            .arena
            .iter()
            .filter_map(|(_, node)| {
                matches!(
                    node.kind,
                    SyntaxKind::LabeledStatement
                        | SyntaxKind::ExpressionStatement
                        | SyntaxKind::BreakStatement
                )
                .then_some(node.kind)
            })
            .collect::<Vec<_>>();
        assert_eq!(
            kinds,
            [
                SyntaxKind::ExpressionStatement,
                SyntaxKind::BreakStatement,
                SyntaxKind::ExpressionStatement,
            ]
        );

        let arrows = parse_source_file(
            "class C { static { const ff = (await) => {}; const fff = await => {}; } }",
        );
        assert!(
            arrows
                .arena
                .iter()
                .all(|(_, node)| node.kind != SyntaxKind::ArrowFunction),
            "{:?}",
            arrows.diagnostics,
        );
    }

    #[test]
    fn parses_var_as_a_class_property_name() {
        let result = parse_source_file("class C { var; } class D { var\nvalue = 1; }");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        for statement in source_statements(&result) {
            let NodeData::ClassDeclaration(class) = &result.arena.get(*statement).unwrap().data
            else {
                panic!("expected class declaration");
            };
            assert_eq!(
                result.arena.get(class.members.nodes[0]).unwrap().kind,
                SyntaxKind::PropertyDeclaration
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One fixture walk.
    fn parses_arrow_postfix_aggregate_and_template_expressions() {
        let source = r"
            const f = (x: number): number => x + 1;
            f({value: [1, 2]}).value;
            const t = `a${f(1)}b${2}`;
            const tagged = f`value`;
            const genericTagged = f<number>``;
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
        let (list, _) = variable_list(&result, statements[3]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected tagged-template declaration");
        };
        assert_eq!(
            result
                .arena
                .get(declaration.initializer.unwrap())
                .unwrap()
                .kind,
            SyntaxKind::TaggedTemplateExpression
        );
        let (list, _) = variable_list(&result, statements[4]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected generic tagged-template declaration");
        };
        let NodeData::TaggedTemplateExpression(tagged) = &result
            .arena
            .get(declaration.initializer.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected generic tagged-template expression");
        };
        assert_eq!(tagged.type_arguments.as_ref().unwrap().nodes.len(), 1);
        assert_eq!(
            result.arena.get(tagged.tag).unwrap().kind,
            SyntaxKind::Identifier
        );
    }

    #[test]
    fn does_not_parse_postfix_increment_across_a_line_break() {
        let result = parse_source_file("\"use strict\"\n++eval;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        let NodeData::ExpressionStatement(statement) =
            &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected expression statement");
        };
        assert_eq!(
            result.arena.get(statement.expression).unwrap().kind,
            SyntaxKind::PrefixUnaryExpression
        );
    }

    #[test]
    fn parses_called_parenthesized_arrow_with_return_type() {
        let result = parse_source_file("const pair = ((): [number, number] => [0, 0])();");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let (list, _) = variable_list(&result, statements[0]);
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
            SyntaxKind::CallExpression
        );
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
    fn splits_shift_token_for_nested_generic_function_call_type_arguments() {
        let result = parse_source_file(
            "const value = foo<<T>(x: T) => number>(() => 1); const shifted = a << b;",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert!(result.arena.iter().any(|(_, node)| {
            matches!(
                &node.data,
                NodeData::CallExpression(call) if call.type_arguments.is_some()
            )
        }));
        assert!(result.arena.iter().any(|(_, node)| {
            let NodeData::BinaryExpression(binary) = &node.data else {
                return false;
            };
            result
                .arena
                .get(binary.operator_token)
                .is_some_and(|operator| operator.kind == SyntaxKind::LessThanLessThanToken)
        }));
    }

    #[test]
    fn recovers_type_assertion_after_new_as_relational_expression() {
        let result = parse_source_file(
            "const assertion = <T>value; const valid = new Value<T>(); const malformed = new <T> value;",
        );
        let statements = source_statements(&result);

        let initializer = |statement| {
            let (list, _) = variable_list(&result, statement);
            let declaration = declaration_nodes(&result, list)[0];
            let NodeData::VariableDeclaration(declaration) =
                &result.arena.get(declaration).unwrap().data
            else {
                panic!("expected variable declaration");
            };
            declaration.initializer.unwrap()
        };

        assert!(matches!(
            &result.arena.get(initializer(statements[0])).unwrap().data,
            NodeData::TypeAssertion(_)
        ));

        let NodeData::NewExpression(valid) =
            &result.arena.get(initializer(statements[1])).unwrap().data
        else {
            panic!("expected generic new expression");
        };
        assert_eq!(valid.type_arguments.as_ref().unwrap().nodes.len(), 1);

        let NodeData::BinaryExpression(greater) =
            &result.arena.get(initializer(statements[2])).unwrap().data
        else {
            panic!("expected outer relational expression");
        };
        assert_eq!(
            result.arena.get(greater.operator_token).unwrap().kind,
            SyntaxKind::GreaterThanToken
        );
        let NodeData::BinaryExpression(less) = &result.arena.get(greater.left).unwrap().data else {
            panic!("expected inner relational expression");
        };
        assert_eq!(
            result.arena.get(less.operator_token).unwrap().kind,
            SyntaxKind::LessThanToken
        );
        let NodeData::NewExpression(malformed) = &result.arena.get(less.left).unwrap().data else {
            panic!("expected recovered new expression");
        };
        assert!(malformed.type_arguments.is_none());
        assert!(matches!(
            &result.arena.get(malformed.expression).unwrap().data,
            NodeData::Identifier(identifier) if identifier.text.is_empty()
        ));
    }

    #[test]
    fn reports_optional_chain_from_bare_new_and_preserves_chain_shape() {
        let result = parse_source_file("new A?.b(); new A()?.b();");
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [1209]
        );
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        for (index, statement) in statements.iter().enumerate() {
            let NodeData::ExpressionStatement(statement) =
                &result.arena.get(*statement).unwrap().data
            else {
                panic!("expected expression statement");
            };
            let NodeData::CallExpression(call) =
                &result.arena.get(statement.expression).unwrap().data
            else {
                panic!("expected outer call");
            };
            assert!(call.question_dot_token.is_none());
            let NodeData::PropertyAccessExpression(access) =
                &result.arena.get(call.expression).unwrap().data
            else {
                panic!("expected optional property access");
            };
            assert!(access.question_dot_token.is_some());
            let NodeData::NewExpression(new_expression) =
                &result.arena.get(access.expression).unwrap().data
            else {
                panic!("expected new-expression receiver");
            };
            assert_eq!(new_expression.arguments.is_some(), index == 1);
        }
    }

    #[test]
    fn parses_optional_calls_with_type_arguments() {
        let result = parse_source_file("value?.<T>();");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let NodeData::ExpressionStatement(statement) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
        else {
            panic!("expected expression statement");
        };
        let NodeData::CallExpression(call) = &result.arena.get(statement.expression).unwrap().data
        else {
            panic!("expected call expression");
        };
        assert!(call.question_dot_token.is_some());
        assert_eq!(call.type_arguments.as_ref().unwrap().nodes.len(), 1);
        assert!(matches!(
            &result.arena.get(call.expression).unwrap().data,
            NodeData::Identifier(identifier) if identifier.text == "value"
        ));
    }

    #[test]
    fn recovers_comma_separated_function_declarations_with_missing_bodies() {
        let result = parse_source_file(concat!(
            "function f1(), function f1();\n",
            "function f2(), function f2() {}\n",
            "function f3() {}, function f3();\n",
            "class C { m1(), m1(); m2(), m2() {} m3() {}, m3(); }\n",
        ));
        let statements = source_statements(&result);
        let bodies = statements
            .iter()
            .filter_map(|statement| {
                let NodeData::FunctionDeclaration(function) = &result.arena.get(*statement)?.data
                else {
                    return None;
                };
                Some(function.body.is_some())
            })
            .collect::<Vec<_>>();
        assert_eq!(bodies, [true, false, true, true, true, false]);
        let NodeData::ClassDeclaration(class) =
            &result.arena.get(*statements.last().unwrap()).unwrap().data
        else {
            panic!("expected class declaration");
        };
        let method_bodies = class
            .members
            .nodes
            .iter()
            .map(|member| {
                let NodeData::MethodDeclaration(method) = &result.arena.get(*member).unwrap().data
                else {
                    panic!("expected method declaration");
                };
                method.body.is_some()
            })
            .collect::<Vec<_>>();
        assert_eq!(method_bodies, [true, false, true, true, true, false]);
    }

    #[test]
    fn preserves_computed_name_overload_implementation_bodies() {
        let result = parse_source_file(concat!(
            "class C {\n",
            "  [\"foo\"](): void\n",
            "  [\"bar\"](): void;\n",
            "  [\"foo\"]() { return 0; }\n",
            "}\n",
        ));
        let statements = source_statements(&result);
        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        let bodies = class
            .members
            .nodes
            .iter()
            .map(|member| {
                let NodeData::MethodDeclaration(method) = &result.arena.get(*member).unwrap().data
                else {
                    panic!("expected method declaration");
                };
                method.body.is_some()
            })
            .collect::<Vec<_>>();
        assert_eq!(bodies, [false, false, true]);
    }

    #[test]
    fn recovers_static_prefixed_calls_in_a_malformed_function_body() {
        let result = parse_source_file(concat!(
            "function boo {\n",
            "  static test()\n",
            "  static test(name: string)\n",
            "  static test(name?: any) { }\n",
            "}\n",
        ));
        let NodeData::FunctionDeclaration(function) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
        else {
            panic!("expected function declaration");
        };
        let NodeData::Block(body) = &result.arena.get(function.body.unwrap()).unwrap().data else {
            panic!("expected function body");
        };
        assert_eq!(body.statements.nodes.len(), 4);
        for statement in &body.statements.nodes[..3] {
            let NodeData::ExpressionStatement(statement) =
                &result.arena.get(*statement).unwrap().data
            else {
                panic!("expected recovered call statement");
            };
            assert!(matches!(
                &result.arena.get(statement.expression).unwrap().data,
                NodeData::CallExpression(_)
            ));
        }
        assert!(matches!(
            &result.arena.get(body.statements.nodes[3]).unwrap().data,
            NodeData::Block(_)
        ));
    }

    #[test]
    fn skips_recovery_only_entries_for_doubled_object_literal_commas() {
        let result = parse_source_file("Boolean({ x: 0,, });");
        let object = result.arena.iter().find_map(|(_, node)| {
            let NodeData::ObjectLiteralExpression(object) = &node.data else {
                return None;
            };
            Some(object)
        });
        let object = object.expect("expected object literal");
        assert_eq!(object.properties.nodes.len(), 1);
        assert!(object.properties.has_trailing_comma);
    }

    #[test]
    fn recovers_non_identifier_object_names_as_missing_property_assignments() {
        let result = parse_source_file("use({ 1234, next: \"value\" });");
        let object = result.arena.iter().find_map(|(_, node)| {
            let NodeData::ObjectLiteralExpression(object) = &node.data else {
                return None;
            };
            Some(object)
        });
        let object = object.expect("expected object literal");
        assert_eq!(object.properties.nodes.len(), 2);
        let NodeData::PropertyAssignment(property) =
            &result.arena.get(object.properties.nodes[0]).unwrap().data
        else {
            panic!("expected recovered property assignment");
        };
        assert!(matches!(
            &result.arena.get(property.initializer).unwrap().data,
            NodeData::Identifier(identifier) if identifier.text.is_empty()
        ));
    }

    #[test]
    fn parses_nested_new_expressions() {
        let result = parse_source_file("const value = new new Date;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let (list, _) = variable_list(&result, source_statements(&result)[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let NodeData::NewExpression(outer) = &result
            .arena
            .get(declaration.initializer.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected outer new expression");
        };
        assert!(matches!(
            result.arena.get(outer.expression).map(|node| &node.data),
            Some(NodeData::NewExpression(_))
        ));
    }

    #[test]
    fn parses_incomplete_constructor_type_arguments_as_comparisons() {
        let result = parse_source_file("new Date<A;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let NodeData::ExpressionStatement(statement) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
        else {
            panic!("expected expression statement");
        };
        let NodeData::BinaryExpression(comparison) =
            &result.arena.get(statement.expression).unwrap().data
        else {
            panic!("expected comparison expression");
        };
        assert_eq!(
            result.arena.get(comparison.operator_token).unwrap().kind,
            SyntaxKind::LessThanToken
        );
        assert!(matches!(
            result.arena.get(comparison.left).map(|node| &node.data),
            Some(NodeData::NewExpression(expression)) if expression.type_arguments.is_none()
        ));
    }

    #[test]
    fn type_argument_lookahead_stops_at_top_level_semicolon() {
        let result = parse_source_file("for (; i < len; i++) {} for (; j >= 0; j--) {}");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let expected = [
            SyntaxKind::LessThanToken,
            SyntaxKind::GreaterThanEqualsToken,
        ];
        for (statement, expected) in statements.iter().zip(expected) {
            let NodeData::ForStatement(for_statement) = &result.arena.get(*statement).unwrap().data
            else {
                panic!("expected for statement");
            };
            let NodeData::BinaryExpression(condition) = &result
                .arena
                .get(for_statement.condition.unwrap())
                .unwrap()
                .data
            else {
                panic!("expected binary condition");
            };
            assert_eq!(
                result.arena.get(condition.operator_token).unwrap().kind,
                expected
            );
        }
    }

    #[test]
    fn parses_generic_arrow_with_nested_generic_return_type() {
        let result = parse_source_file(
            "const build = <V extends string>(version: V): Output<{ value: Record<V, string>; }> => ({});",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let (list, _) = variable_list(&result, statements[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        assert!(matches!(
            result
                .arena
                .get(declaration.initializer.unwrap())
                .unwrap()
                .data,
            NodeData::ArrowFunction(_)
        ));
    }

    #[test]
    fn parses_parenthesized_arrow_parameters_with_nested_generic_arguments() {
        for (source, expected_parameters) in [
            ("const fn = (value: Omit<O, 'prop'>) => {};", 1),
            (
                "const fn = (value: Wrapper<Omit<O, 'prop'>, Record<string, O>>) => value;",
                1,
            ),
            (
                concat!(
                    "const fn = (value: O['prop'], omitted: Omit<O, 'prop'>, ",
                    "key: keyof O, nested: Omit<O, keyof I>) => {};",
                ),
                4,
            ),
        ] {
            let result = parse_source_file(source);
            assert!(
                result.diagnostics.is_empty(),
                "source: {source}; diagnostics: {:?}",
                result.diagnostics
            );
            let (list, _) = variable_list(&result, source_statements(&result)[0]);
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
            assert_eq!(arrow.parameters.nodes.len(), expected_parameters);
        }

        let comparison = parse_source_file("const value = (left < right, next > last);");
        assert!(
            comparison.diagnostics.is_empty(),
            "{:?}",
            comparison.diagnostics
        );
        assert!(
            comparison
                .arena
                .iter()
                .all(|(_, node)| !matches!(node.data, NodeData::ArrowFunction(_)))
        );
    }

    #[test]
    fn parses_generic_arrow_after_parenthesized_function_return_type() {
        let result = parse_source_file("const fn = <T>(): (() => T) => null as any;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let (list, _) = variable_list(&result, source_statements(&result)[0]);
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
        assert!(matches!(
            &result.arena.get(arrow.type_.unwrap()).unwrap().data,
            NodeData::ParenthesizedTypeNode(_)
        ));
        let NodeData::AsExpression(body) = &result.arena.get(arrow.body).unwrap().data else {
            panic!("expected asserted null body");
        };
        assert_eq!(
            result.arena.get(body.expression).unwrap().kind,
            SyntaxKind::NullKeyword
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

        let missing_after_return_type =
            parse_source_file("var b = (): void {}; var e = (x: number): void;");
        assert_eq!(
            missing_after_return_type
                .arena
                .iter()
                .filter(|(_, node)| matches!(node.data, NodeData::ArrowFunction(_)))
                .count(),
            2
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
    fn rejects_an_arrow_lookahead_with_an_unparsed_binary_operand() {
        let result = parse_source_file("x = (y = z ==== 'function') {");
        assert!(
            result
                .arena
                .iter()
                .all(|(_, node)| !matches!(node.data, NodeData::ArrowFunction(_)))
        );
        assert!(
            result
                .arena
                .iter()
                .any(|(_, node)| matches!(node.data, NodeData::Block(_)))
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
    fn parses_private_class_accessors() {
        let result =
            parse_source_file("class C { get #value() { return 1; } set #value(next: number) {} }");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected class");
        };
        assert!(matches!(
            &result.arena.get(class.members.nodes[0]).unwrap().data,
            NodeData::GetAccessorDeclaration(accessor)
                if matches!(
                    result.arena.get(accessor.name).map(|node| &node.data),
                    Some(NodeData::PrivateIdentifier(_))
                )
        ));
        assert!(matches!(
            &result.arena.get(class.members.nodes[1]).unwrap().data,
            NodeData::SetAccessorDeclaration(accessor)
                if matches!(
                    result.arena.get(accessor.name).map(|node| &node.data),
                    Some(NodeData::PrivateIdentifier(_))
                )
        ));
    }

    #[test]
    fn preserves_a_bare_hash_as_a_recovered_private_expression() {
        let result = parse_source_file("#\nclass C {}");
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        assert!(matches!(
            &result.arena.get(statements[0]).unwrap().data,
            NodeData::ExpressionStatement(statement)
                if matches!(
                    result.arena.get(statement.expression).map(|node| &node.data),
                    Some(NodeData::PrivateIdentifier(identifier)) if identifier.text == "#"
                )
        ));
    }

    #[test]
    fn preserves_a_private_identifier_as_a_recovered_variable_name() {
        let result = parse_source_file("const #foo = 3;");
        let statements = source_statements(&result);
        let NodeData::VariableStatement(statement) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected variable statement");
        };
        let NodeData::VariableDeclarationList(list) =
            &result.arena.get(statement.declaration_list).unwrap().data
        else {
            panic!("expected variable declaration list");
        };
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(list.declarations.nodes[0]).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        assert!(matches!(
            result.arena.get(declaration.name).map(|node| &node.data),
            Some(NodeData::PrivateIdentifier(identifier)) if identifier.text == "#foo"
        ));
    }

    #[test]
    fn preserves_a_private_identifier_as_a_recovered_parameter_name() {
        let result = parse_source_file("class A { setFoo(#foo: string) {} }");
        let statements = source_statements(&result);
        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 1);
        let NodeData::MethodDeclaration(method) =
            &result.arena.get(class.members.nodes[0]).unwrap().data
        else {
            panic!("expected method declaration");
        };
        let NodeData::ParameterDeclaration(parameter) =
            &result.arena.get(method.parameters.nodes[0]).unwrap().data
        else {
            panic!("expected parameter declaration");
        };
        assert!(matches!(
            result.arena.get(parameter.name).map(|node| &node.data),
            Some(NodeData::PrivateIdentifier(identifier)) if identifier.text == "#foo"
        ));
    }

    #[test]
    fn recovers_a_private_identifier_after_an_invalid_indexed_access_type() {
        let result = parse_source_file("const badForNow: C[#bar] = 3;");
        let statements = source_statements(&result);
        let NodeData::VariableStatement(statement) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected variable statement");
        };
        let NodeData::VariableDeclarationList(list) =
            &result.arena.get(statement.declaration_list).unwrap().data
        else {
            panic!("expected variable declaration list");
        };
        assert_eq!(list.declarations.nodes.len(), 2);
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(list.declarations.nodes[1]).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        assert!(matches!(
            result.arena.get(declaration.name).map(|node| &node.data),
            Some(NodeData::PrivateIdentifier(identifier)) if identifier.text == "#bar"
        ));
    }

    #[test]
    fn parses_private_type_members() {
        let result = parse_source_file(concat!(
            "type A = { #value: string; #read(): string; }; ",
            "interface B { #value: string; #read(): string; }",
        ));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert_eq!(source_statements(&result).len(), 2);
        assert_eq!(
            result
                .arena
                .iter()
                .filter(|(_, node)| matches!(node.data, NodeData::PrivateIdentifier(_)))
                .count(),
            4
        );
    }

    #[test]
    fn recovers_object_member_modifiers_and_question_marks() {
        let result =
            parse_source_file("const value = { public get foo() {}, bar?() {}, baz?: 1 };");
        let object = find_descendant_kind(
            &result,
            result.source_file,
            SyntaxKind::ObjectLiteralExpression,
        )
        .expect("object literal");
        let NodeData::ObjectLiteralExpression(object) = &result.arena.get(object).unwrap().data
        else {
            panic!("expected object literal");
        };
        assert_eq!(object.properties.nodes.len(), 3);
        assert!(matches!(
            &result.arena.get(object.properties.nodes[0]).unwrap().data,
            NodeData::GetAccessorDeclaration(accessor) if accessor.modifiers.is_some()
        ));
        assert!(matches!(
            &result.arena.get(object.properties.nodes[1]).unwrap().data,
            NodeData::MethodDeclaration(method) if method.postfix_token.is_some()
        ));
        assert!(matches!(
            &result.arena.get(object.properties.nodes[2]).unwrap().data,
            NodeData::PropertyAssignment(property) if property.postfix_token.is_some()
        ));
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
    fn incomplete_unicode_escape_preserves_following_identifier_statement() {
        let result = parse_source_file(r"a\u");
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2, "{:?}", result.diagnostics);
        let names = statements
            .iter()
            .map(|statement| {
                let NodeData::ExpressionStatement(statement) =
                    &result.arena.get(*statement).unwrap().data
                else {
                    panic!("expected expression statement");
                };
                let NodeData::Identifier(identifier) =
                    &result.arena.get(statement.expression).unwrap().data
                else {
                    panic!("expected identifier");
                };
                identifier.text.as_str()
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["a", "u"]);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [1127]
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
        let NodeData::ConstructorDeclaration(constructor) =
            &result.arena.get(class.members.nodes[0]).unwrap().data
        else {
            panic!("expected constructor declaration");
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
    fn parses_constructor_declarations_with_canonical_shape_and_parents() {
        let source = concat!(
            "class Example {\n",
            "  public constructor<T>(value: T): Example;\n",
            "  protected \"constructor\"(value: string) {}\n",
            r#"  "\x63onstructor"() {}"#,
            "\n}",
        );
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let class_id = source_statements(&result)[0];
        let NodeData::ClassDeclaration(class) = &result.arena.get(class_id).unwrap().data else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 3);
        for member in &class.members.nodes {
            let member_node = result.arena.get(*member).unwrap();
            assert_eq!(member_node.parent, Some(class_id));
            member_node.for_each_child(|child| {
                assert_eq!(result.arena.get(child).unwrap().parent, Some(*member));
            });
        }

        let overload_id = class.members.nodes[0];
        let overload_node = result.arena.get(overload_id).unwrap();
        assert_eq!(overload_node.kind, SyntaxKind::Constructor);
        let NodeData::ConstructorDeclaration(overload) = &overload_node.data else {
            panic!("expected constructor declaration");
        };
        assert!(overload.body.is_none());
        assert!(overload.asterisk_token.is_none());
        assert!(overload.full_signature.is_none());
        let modifier = overload.modifiers.as_ref().unwrap().list.nodes[0];
        let type_parameter = overload.type_parameters.as_ref().unwrap().nodes[0];
        let parameter = overload.parameters.nodes[0];
        let return_type = overload.type_.unwrap();
        let mut direct_children = Vec::new();
        overload_node.for_each_child(|child| direct_children.push(child));
        assert_eq!(
            direct_children,
            [modifier, type_parameter, parameter, return_type]
        );
        for child in direct_children {
            assert_eq!(result.arena.get(child).unwrap().parent, Some(overload_id));
        }
        assert_eq!(
            result.arena.get(modifier).unwrap().kind,
            SyntaxKind::PublicKeyword
        );
        let range = overload_node.range;
        assert_eq!(
            &source[range.start.get() as usize..range.end.get() as usize],
            "public constructor<T>(value: T): Example;"
        );

        let quoted_id = class.members.nodes[1];
        let quoted_node = result.arena.get(quoted_id).unwrap();
        let NodeData::ConstructorDeclaration(quoted) = &quoted_node.data else {
            panic!("expected quoted constructor declaration");
        };
        assert!(quoted.type_parameters.is_none());
        assert!(quoted.type_.is_none());
        let quoted_body = quoted.body.expect("constructor implementation body");
        assert_eq!(
            result.arena.get(quoted_body).unwrap().parent,
            Some(quoted_id)
        );
        assert_eq!(
            result
                .arena
                .get(quoted.modifiers.as_ref().unwrap().list.nodes[0])
                .unwrap()
                .kind,
            SyntaxKind::ProtectedKeyword
        );

        let escaped_id = class.members.nodes[2];
        assert!(matches!(
            &result.arena.get(escaped_id).unwrap().data,
            NodeData::ConstructorDeclaration(constructor) if constructor.body.is_some()
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One constructor-name classification matrix.
    fn constructor_promotion_excludes_other_constructor_named_members() {
        let result = parse_source_file(
            r#"
                class MemberKinds {
                    static constructor() {}
                    static() {}
                    get constructor() { return 1; }
                    set constructor(value: number) {}
                    *constructor() {}
                    ["constructor"]() {}
                    #constructor() {}
                    "constructor"<T>() {}
                    "constructor"?() {}
                    "constructor" = 1;
                }
            "#,
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let NodeData::ClassDeclaration(class) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
        else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 10);

        let NodeData::ConstructorDeclaration(static_constructor) =
            &result.arena.get(class.members.nodes[0]).unwrap().data
        else {
            panic!("expected static constructor syntax to retain constructor shape");
        };
        assert_eq!(
            result
                .arena
                .get(static_constructor.modifiers.as_ref().unwrap().list.nodes[0])
                .unwrap()
                .kind,
            SyntaxKind::StaticKeyword
        );

        let NodeData::MethodDeclaration(static_method) =
            &result.arena.get(class.members.nodes[1]).unwrap().data
        else {
            panic!("expected method named static");
        };
        assert!(matches!(
            &result.arena.get(static_method.name).unwrap().data,
            NodeData::Identifier(identifier) if identifier.text == "static"
        ));
        assert!(matches!(
            result
                .arena
                .get(class.members.nodes[2])
                .map(|node| &node.data),
            Some(NodeData::GetAccessorDeclaration(_))
        ));
        assert!(matches!(
            result
                .arena
                .get(class.members.nodes[3])
                .map(|node| &node.data),
            Some(NodeData::SetAccessorDeclaration(_))
        ));

        let NodeData::MethodDeclaration(generator) =
            &result.arena.get(class.members.nodes[4]).unwrap().data
        else {
            panic!("expected generator method");
        };
        assert!(generator.asterisk_token.is_some());
        let NodeData::MethodDeclaration(computed) =
            &result.arena.get(class.members.nodes[5]).unwrap().data
        else {
            panic!("expected computed method");
        };
        assert_eq!(
            result.arena.get(computed.name).unwrap().kind,
            SyntaxKind::ComputedPropertyName
        );
        let NodeData::MethodDeclaration(private) =
            &result.arena.get(class.members.nodes[6]).unwrap().data
        else {
            panic!("expected private method");
        };
        assert_eq!(
            result.arena.get(private.name).unwrap().kind,
            SyntaxKind::PrivateIdentifier
        );
        let NodeData::MethodDeclaration(quoted_generic) =
            &result.arena.get(class.members.nodes[7]).unwrap().data
        else {
            panic!("expected quoted generic method");
        };
        assert!(quoted_generic.type_parameters.is_some());
        assert_eq!(
            result.arena.get(quoted_generic.name).unwrap().kind,
            SyntaxKind::StringLiteral
        );
        let NodeData::MethodDeclaration(quoted_optional) =
            &result.arena.get(class.members.nodes[8]).unwrap().data
        else {
            panic!("expected quoted optional method");
        };
        assert!(quoted_optional.postfix_token.is_some());
        assert_eq!(
            result.arena.get(quoted_optional.name).unwrap().kind,
            SyntaxKind::StringLiteral
        );
        let NodeData::PropertyDeclaration(quoted_property) =
            &result.arena.get(class.members.nodes[9]).unwrap().data
        else {
            panic!("expected quoted property");
        };
        assert_eq!(
            result.arena.get(quoted_property.name).unwrap().kind,
            SyntaxKind::StringLiteral
        );
    }

    #[test]
    fn constructor_parameters_and_bodies_clear_outer_await_context() {
        let result = parse_source_file(
            "async function outer() { class C { constructor(value = await) { await; } } }",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let NodeData::FunctionDeclaration(outer) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
        else {
            panic!("expected outer function");
        };
        let NodeData::Block(outer_body) = &result.arena.get(outer.body.unwrap()).unwrap().data
        else {
            panic!("expected outer function body");
        };
        let NodeData::ClassDeclaration(class) = &result
            .arena
            .get(outer_body.statements.nodes[0])
            .unwrap()
            .data
        else {
            panic!("expected nested class");
        };
        let NodeData::ConstructorDeclaration(constructor) =
            &result.arena.get(class.members.nodes[0]).unwrap().data
        else {
            panic!("expected constructor declaration");
        };
        let NodeData::ParameterDeclaration(parameter) = &result
            .arena
            .get(constructor.parameters.nodes[0])
            .unwrap()
            .data
        else {
            panic!("expected constructor parameter");
        };
        assert!(matches!(
            &result.arena.get(parameter.initializer.unwrap()).unwrap().data,
            NodeData::Identifier(identifier) if identifier.text == "await"
        ));
        let NodeData::Block(body) = &result.arena.get(constructor.body.unwrap()).unwrap().data
        else {
            panic!("expected constructor body");
        };
        let NodeData::ExpressionStatement(statement) =
            &result.arena.get(body.statements.nodes[0]).unwrap().data
        else {
            panic!("expected expression statement");
        };
        assert!(matches!(
            &result.arena.get(statement.expression).unwrap().data,
            NodeData::Identifier(identifier) if identifier.text == "await"
        ));
    }

    #[test]
    fn invalid_parameter_modifiers_do_not_detach_constructor_bodies() {
        let result = parse_source_file(concat!(
            "class Static { constructor(static a: number) {} }\n",
            "class Mixed { constructor(public static a: number) {} }\n",
            "class Exported { constructor(export a: number) {} }",
        ));
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 3);
        for statement in statements {
            let NodeData::ClassDeclaration(class) = &result.arena.get(*statement).unwrap().data
            else {
                panic!("expected class declaration");
            };
            let NodeData::ConstructorDeclaration(constructor) =
                &result.arena.get(class.members.nodes[0]).unwrap().data
            else {
                panic!("expected constructor declaration");
            };
            assert!(constructor.body.is_some());
            let NodeData::ParameterDeclaration(parameter) = &result
                .arena
                .get(constructor.parameters.nodes[0])
                .unwrap()
                .data
            else {
                panic!("expected constructor parameter");
            };
            let NodeData::Identifier(name) = &result.arena.get(parameter.name).unwrap().data else {
                panic!("expected parameter name");
            };
            assert_eq!(name.text, "a");
        }
    }

    #[test]
    fn conflict_marker_recovery_keeps_selected_class_members() {
        let source = concat!(
            "class C {\n",
            "  foo() {\n",
            "<<<<<<< B\n",
            "    a();\n",
            "  }\n",
            "=======\n",
            "    b();\n",
            "  }\n",
            ">>>>>>> A\n",
            "  public bar() {}\n",
            "}\n",
        );
        let result = parse_source_file(source);
        let statements = source_statements(&result);
        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 2, "{:?}", result.diagnostics);
        let names = class
            .members
            .nodes
            .iter()
            .map(|member| {
                let NodeData::MethodDeclaration(method) = &result.arena.get(*member).unwrap().data
                else {
                    panic!("expected method declaration");
                };
                let NodeData::Identifier(name) = &result.arena.get(method.name).unwrap().data
                else {
                    panic!("expected method name");
                };
                name.text.as_str()
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["foo", "bar"]);
    }

    #[test]
    fn conflict_marker_terminates_unclosed_jsx_children() {
        let result = parse_jsx_source_file("const x = <div>\n<<<<<<< HEAD");
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1, "{:?}", result.diagnostics);
        let (list, _) = variable_list(&result, statements[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let NodeData::JsxElement(element) = &result
            .arena
            .get(declaration.initializer.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected JSX element");
        };
        let NodeData::JsxClosingElement(closing) =
            &result.arena.get(element.closing_element).unwrap().data
        else {
            panic!("expected synthetic JSX closing element");
        };
        let NodeData::Identifier(name) = &result.arena.get(closing.tag_name).unwrap().data else {
            panic!("expected synthetic closing tag name");
        };
        assert!(name.text.is_empty());
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
        assert!(namespace.modifiers.is_none());
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
    fn parses_quoted_type_only_module_names_without_runtime_bindings() {
        let result = parse_source_file(concat!(
            "export type * as \"<C>\" from \"m\";",
            "import { type \"<C>\" as type_c } from \"m\";",
        ));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let NodeData::ExportDeclaration(export) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected export declaration");
        };
        assert!(export.is_type_only);
        let NodeData::ImportDeclaration(import) = &result.arena.get(statements[1]).unwrap().data
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
        assert!(specifier.is_type_only);
    }

    #[test]
    fn preserves_default_export_declaration_forms() {
        let result = parse_source_file(concat!(
            "export default interface Shape {}\n",
            "export default class Model {}\n",
            "export default function make() {}\n",
            "export default @sealed class Decorated {}\n",
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
                SyntaxKind::ClassDeclaration,
            ]
        );
        for (index, statement) in statements.iter().enumerate() {
            let modifiers = match &result.arena.get(*statement).unwrap().data {
                NodeData::InterfaceDeclaration(declaration) => declaration.modifiers.as_ref(),
                NodeData::ClassDeclaration(declaration) => declaration.modifiers.as_ref(),
                NodeData::FunctionDeclaration(declaration) => declaration.modifiers.as_ref(),
                _ => None,
            }
            .unwrap();
            let actual = modifiers
                .list
                .nodes
                .iter()
                .map(|modifier| result.arena.get(*modifier).unwrap().kind)
                .collect::<Vec<_>>();
            if index == 3 {
                assert_eq!(
                    actual,
                    [
                        SyntaxKind::ExportKeyword,
                        SyntaxKind::DefaultKeyword,
                        SyntaxKind::Decorator,
                    ]
                );
            } else {
                assert_eq!(
                    actual,
                    [SyntaxKind::ExportKeyword, SyntaxKind::DefaultKeyword]
                );
            }
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
    fn malformed_escaped_import_binding_stays_inside_the_import() {
        let result = parse_source_file("import { value as \\uD800\\uDEA7 } from \"./mod.js\";");
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1);
        assert_eq!(
            result.arena.get(statements[0]).unwrap().kind,
            SyntaxKind::ImportDeclaration
        );
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter(|diagnostic| diagnostic.code == Some(1127))
                .count(),
            2
        );
    }

    #[test]
    fn recovers_missing_export_clause_brace_before_from() {
        let result = parse_source_file("export { value, from \"./mod\"");
        assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
        let NodeData::ExportDeclaration(declaration) = &result
            .arena
            .get(source_statements(&result)[0])
            .unwrap()
            .data
        else {
            panic!("expected export declaration");
        };
        assert!(declaration.module_specifier.is_some());
        let NodeData::NamedExports(exports) = &result
            .arena
            .get(declaration.export_clause.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected named exports");
        };
        assert_eq!(exports.elements.nodes.len(), 1);

        let valid = parse_source_file("export { from } from \"./mod\";");
        assert!(valid.diagnostics.is_empty(), "{:?}", valid.diagnostics);
        let NodeData::ExportDeclaration(declaration) =
            &valid.arena.get(source_statements(&valid)[0]).unwrap().data
        else {
            panic!("expected export declaration");
        };
        let NodeData::NamedExports(exports) = &valid
            .arena
            .get(declaration.export_clause.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected named exports");
        };
        assert_eq!(exports.elements.nodes.len(), 1);
    }

    #[test]
    fn parses_type_only_export_declarations_and_specifiers() {
        let result = parse_source_file(concat!(
            "export { type Foo, type as renamed, type };\n",
            "export type { Foo, Bar as Baz } from './mod';\n",
        ));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);

        let NodeData::ExportDeclaration(inline) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected export declaration");
        };
        assert!(!inline.is_type_only);
        let NodeData::NamedExports(inline_exports) = &result
            .arena
            .get(inline.export_clause.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected named exports");
        };
        let identifier = |id| {
            let NodeData::Identifier(identifier) = &result.arena.get(id).unwrap().data else {
                panic!("expected identifier");
            };
            identifier.text.clone()
        };
        let inline_specifiers = inline_exports
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
                    specifier.is_type_only,
                    specifier.property_name.map(&identifier),
                    identifier(specifier.name),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            inline_specifiers,
            [
                (true, None, "Foo".into()),
                (false, Some("type".into()), "renamed".into()),
                (false, None, "type".into()),
            ]
        );

        let NodeData::ExportDeclaration(declaration) =
            &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected export declaration");
        };
        assert!(declaration.is_type_only);
        let NodeData::NamedExports(exports) = &result
            .arena
            .get(declaration.export_clause.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected named exports");
        };
        assert!(exports.elements.nodes.iter().all(|specifier| {
            matches!(
                &result.arena.get(*specifier).unwrap().data,
                NodeData::ExportSpecifier(specifier) if !specifier.is_type_only
            )
        }));
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
        assert!(assignment.type_.is_none());
        let NodeData::Identifier(expression) =
            &result.arena.get(assignment.expression).unwrap().data
        else {
            panic!("expected identifier expression");
        };
        assert_eq!(expression.text, "runtimeValue");
    }

    #[test]
    fn export_grammar_tokens_are_not_modifiers_or_generated_children() {
        let result = parse_source_file(concat!(
            "export { value };\n",
            "export default value;\n",
            "export = value;\n",
            "declare export { value };\n",
            "@decorator export default value;\n",
            "declare export as namespace Global;\n",
        ));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 6);
        assert!(result.arena.iter().all(|(_, node)| {
            !matches!(
                node.kind,
                SyntaxKind::ExportKeyword | SyntaxKind::DefaultKeyword
            )
        }));

        for statement in &statements[..3] {
            let modifiers = match &result.arena.get(*statement).unwrap().data {
                NodeData::ExportDeclaration(export) => export.modifiers.as_ref(),
                NodeData::ExportAssignment(export) => export.modifiers.as_ref(),
                data => panic!("expected ordinary export node, got {data:?}"),
            };
            assert!(modifiers.is_none());

            let mut children = Vec::new();
            result
                .arena
                .get(*statement)
                .unwrap()
                .for_each_child(|child| children.push(child));
            assert!(children.iter().all(|child| {
                !matches!(
                    result.arena.get(*child).unwrap().kind,
                    SyntaxKind::ExportKeyword | SyntaxKind::DefaultKeyword
                )
            }));
        }

        let expected_modifiers = [
            SyntaxKind::DeclareKeyword,
            SyntaxKind::Decorator,
            SyntaxKind::DeclareKeyword,
        ];
        for (statement, expected) in statements[3..].iter().zip(expected_modifiers) {
            let modifiers = match &result.arena.get(*statement).unwrap().data {
                NodeData::ExportDeclaration(export) => export.modifiers.as_ref(),
                NodeData::ExportAssignment(export) => export.modifiers.as_ref(),
                NodeData::NamespaceExportDeclaration(export) => export.modifiers.as_ref(),
                data => panic!("expected modified export node, got {data:?}"),
            }
            .expect("preceding illegal modifier is retained");
            assert_eq!(modifiers.list.nodes.len(), 1);
            assert_eq!(
                result.arena.get(modifiers.list.nodes[0]).unwrap().kind,
                expected
            );
        }
    }

    #[test]
    fn import_export_payloads_form_one_generated_child_tree() {
        let result = parse_source_file(
            r#"
import defaultValue, { source as local, same } from "pkg" with { type: "json" };
import * as namespaceValue from "namespace-pkg";
import equalsValue = require("equals-pkg");
export { local as renamed, same };
export * from "star-pkg";
export * as namespaceExport from "namespace-export-pkg";
export default local;
export = equalsValue;
export as namespace GlobalName;
"#,
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let mut stack = vec![result.source_file];
        let mut reached = std::collections::HashSet::new();
        while let Some(node) = stack.pop() {
            assert!(reached.insert(node), "AST child is reused: {node:?}");
            result
                .arena
                .get(node)
                .unwrap()
                .for_each_child(|child| stack.push(child));
        }

        for kind in [
            SyntaxKind::ImportDeclaration,
            SyntaxKind::ImportClause,
            SyntaxKind::NamespaceImport,
            SyntaxKind::ImportEqualsDeclaration,
            SyntaxKind::ImportSpecifier,
            SyntaxKind::ExportDeclaration,
            SyntaxKind::ExportSpecifier,
            SyntaxKind::NamespaceExport,
            SyntaxKind::NamespaceExportDeclaration,
            SyntaxKind::ExportAssignment,
        ] {
            assert!(
                reached
                    .iter()
                    .any(|node| result.arena.get(*node).unwrap().kind == kind),
                "missing {kind:?}"
            );
        }
        assert!(reached.iter().all(|node| {
            !matches!(
                &result.arena.get(*node).unwrap().data,
                NodeData::ExportAssignment(assignment) if assignment.type_.is_some()
            )
        }));
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
        let inner_modifiers = inner.modifiers.as_ref().unwrap();
        assert_eq!(inner_modifiers.flags, ModifierFlags::EXPORT);
        assert_eq!(inner_modifiers.list.nodes.len(), 1);
        let inner_export = result.arena.get(inner_modifiers.list.nodes[0]).unwrap();
        assert_eq!(inner_export.kind, SyntaxKind::ExportKeyword);
        assert_eq!(inner_export.flags, NodeFlags::REPARSED);
        assert_eq!(inner_export.range.start, inner_export.range.end);
        assert_eq!(inner_export.range.start, inner_node.range.start);
        assert_eq!(inner_export.parent, Some(inner_id));
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
    fn synthesizes_reparsed_exports_for_each_dotted_namespace_segment() {
        for (source, has_declare_modifier) in [
            ("namespace A.B.C {}", false),
            ("declare namespace A.B.C {}", true),
        ] {
            let result = parse_source_file(source);
            assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
            let [outer_id] = source_statements(&result) else {
                panic!("expected one namespace declaration");
            };
            let outer_node = result.arena.get(*outer_id).unwrap();
            let NodeData::ModuleDeclaration(outer) = &outer_node.data else {
                panic!("expected outer namespace");
            };

            if has_declare_modifier {
                let outer_modifiers = outer.modifiers.as_ref().unwrap();
                let [declare_modifier] = outer_modifiers.list.nodes.as_slice() else {
                    panic!("expected only the source declare modifier");
                };
                let declare_node = result.arena.get(*declare_modifier).unwrap();
                assert_eq!(declare_node.kind, SyntaxKind::DeclareKeyword);
                assert_eq!(declare_node.flags, NodeFlags::default());
                assert_eq!(declare_node.parent, Some(*outer_id));
                assert_eq!(
                    &source[declare_node.range.start.get() as usize
                        ..declare_node.range.end.get() as usize],
                    "declare"
                );
            } else {
                assert!(outer.modifiers.is_none());
            }

            let mut nested_id = outer.body.unwrap();
            for nested_name in ["B", "C"] {
                let nested_position = u32::try_from(source.find(nested_name).unwrap()).unwrap();
                let nested_node = result.arena.get(nested_id).unwrap();
                let NodeData::ModuleDeclaration(nested) = &nested_node.data else {
                    panic!("expected nested namespace segment");
                };
                assert_eq!(nested_node.range.start.get(), nested_position);
                let modifiers = nested.modifiers.as_ref().unwrap();
                assert_eq!(modifiers.flags, ModifierFlags::EXPORT);
                assert_eq!(modifiers.list.range.start.get(), nested_position);
                assert_eq!(modifiers.list.range.end.get(), nested_position);
                assert_eq!(modifiers.list.nodes.len(), 1);
                let export_id = modifiers.list.nodes[0];
                let export = result.arena.get(export_id).unwrap();
                assert_eq!(export.kind, SyntaxKind::ExportKeyword);
                assert_eq!(export.flags, NodeFlags::REPARSED);
                assert_eq!(export.flags.0, 1 << 3);
                assert_eq!(export.range.start.get(), nested_position);
                assert_eq!(export.range.end.get(), nested_position);
                assert_eq!(export.parent, Some(nested_id));
                assert_eq!(
                    &source[export.range.start.get() as usize..export.range.end.get() as usize],
                    ""
                );
                assert_eq!(
                    result.arena.get(nested.name).unwrap().parent,
                    Some(nested_id)
                );
                nested_id = nested.body.unwrap();
            }
            assert!(matches!(
                result.arena.get(nested_id).map(|node| &node.data),
                Some(NodeData::ModuleBlock(_))
            ));
        }
    }

    #[test]
    fn bodyless_ambient_module_owns_its_semicolon() {
        let source = "declare module \"foo\";";
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let [statement] = source_statements(&result) else {
            panic!("expected one module declaration");
        };
        let node = result.arena.get(*statement).unwrap();
        assert_eq!(node.kind, SyntaxKind::ModuleDeclaration);
        assert_eq!(node.range.end.get() as usize, source.len());
    }

    #[test]
    fn recovers_declare_before_an_invalid_root_namespace_name() {
        let result = parse_source_file(concat!(
            "declare namespace test.class {}\n",
            "declare namespace debugger {}",
        ));
        let kinds = source_statements(&result)
            .iter()
            .map(|statement| result.arena.get(*statement).unwrap().kind)
            .collect::<Vec<_>>();
        assert_eq!(
            kinds,
            [
                SyntaxKind::ModuleDeclaration,
                SyntaxKind::ExpressionStatement,
                SyntaxKind::ExpressionStatement,
                SyntaxKind::DebuggerStatement,
                SyntaxKind::Block,
            ]
        );
    }

    #[test]
    fn retains_namespace_recovery_after_a_missing_dotted_name() {
        let source =
            "namespace Plain { const value = 1; } namespace Broken. { const recovered = 2; }";
        let result = parse_source_file(source);
        assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
        assert!(statements.iter().all(|statement| {
            result.arena.get(*statement).unwrap().kind == SyntaxKind::ModuleDeclaration
        }));

        let NodeData::ModuleDeclaration(broken) = &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected recovered outer namespace");
        };
        let recovered_id = broken.body.unwrap();
        let recovered_node = result.arena.get(recovered_id).unwrap();
        let NodeData::ModuleDeclaration(recovered) = &recovered_node.data else {
            panic!("expected recovered nested namespace");
        };
        let missing_position = u32::try_from(source.find("{ const recovered").unwrap()).unwrap();
        assert_eq!(recovered_node.range.start.get(), missing_position);
        let NodeData::Identifier(missing_name) = &result.arena.get(recovered.name).unwrap().data
        else {
            panic!("expected recovered missing identifier");
        };
        assert!(missing_name.text.is_empty());
        assert_eq!(
            result.arena.get(recovered.name).unwrap().range.start.get(),
            missing_position
        );
        let recovered_modifiers = recovered.modifiers.as_ref().unwrap();
        assert_eq!(recovered_modifiers.flags, ModifierFlags::EXPORT);
        let [export_id] = recovered_modifiers.list.nodes.as_slice() else {
            panic!("expected synthesized export modifier");
        };
        let export = result.arena.get(*export_id).unwrap();
        assert_eq!(export.kind, SyntaxKind::ExportKeyword);
        assert_eq!(export.flags, NodeFlags::REPARSED);
        assert_eq!(export.range.start.get(), missing_position);
        assert_eq!(export.range.end.get(), missing_position);
        assert_eq!(export.parent, Some(recovered_id));
        assert!(matches!(
            recovered
                .body
                .and_then(|body| result.arena.get(body))
                .map(|node| &node.data),
            Some(NodeData::ModuleBlock(_))
        ));
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
    fn recovers_static_class_field_from_a_malformed_method_body() {
        let result = parse_source_file("class foo { constructor() { static f = 3; } }");
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [Some(1128), Some(1128)]
        );
        let statements = source_statements(&result);
        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 2);
        let NodeData::ConstructorDeclaration(constructor) =
            &result.arena.get(class.members.nodes[0]).unwrap().data
        else {
            panic!("expected constructor");
        };
        let NodeData::Block(body) = &result
            .arena
            .get(constructor.body.expect("constructor body"))
            .unwrap()
            .data
        else {
            panic!("expected constructor block");
        };
        assert!(body.statements.nodes.is_empty());
        let NodeData::PropertyDeclaration(field) =
            &result.arena.get(class.members.nodes[1]).unwrap().data
        else {
            panic!("expected recovered class field");
        };
        assert_eq!(
            field
                .modifiers
                .as_ref()
                .expect("static modifier")
                .list
                .nodes
                .iter()
                .map(|modifier| result.arena.get(*modifier).unwrap().kind)
                .collect::<Vec<_>>(),
            [SyntaxKind::StaticKeyword]
        );
        assert!(field.initializer.is_some());
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
                    new?(): Inline;
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
        assert_eq!(literal.members.nodes.len(), 5);
        assert_eq!(
            result.arena.get(literal.members.nodes[2]).unwrap().kind,
            SyntaxKind::MethodSignature
        );
    }

    #[test]
    fn recovers_swapped_signature_and_function_return_tokens() {
        let result = parse_source_file(
            "type F1 = { (n: number) => string; } type F2 = (n: number): string;",
        );
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 3);

        let NodeData::TypeAliasDeclaration(first) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected first type alias");
        };
        let NodeData::TypeLiteralNode(literal) = &result.arena.get(first.type_).unwrap().data
        else {
            panic!("expected type literal");
        };
        let NodeData::CallSignatureDeclaration(signature) =
            &result.arena.get(literal.members.nodes[0]).unwrap().data
        else {
            panic!("expected recovered call signature");
        };
        assert!(signature.type_.is_some());

        let NodeData::TypeAliasDeclaration(second) = &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected second type alias");
        };
        assert!(matches!(
            &result.arena.get(second.type_).unwrap().data,
            NodeData::FunctionTypeNode(function) if function.type_.is_some()
        ));
        assert_eq!(
            result.arena.get(statements[2]).unwrap().kind,
            SyntaxKind::ExpressionStatement
        );
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
    fn consumes_invalid_prefix_and_postfix_non_nullable_types() {
        let result = parse_source_file(concat!(
            "function first(value: string!): !number {}\n",
            "const postfix = 1 as any!;\n",
            "const prefix: !number = 1;\n",
        ));
        assert_eq!(source_statements(&result).len(), 3);
        assert_eq!(
            result
                .arena
                .iter()
                .filter(|(_, node)| matches!(node.data, NodeData::JsDocNonNullableType(_)))
                .count(),
            4
        );
    }

    #[test]
    fn parses_this_qualified_type_queries_without_orphaned_tokens() {
        let result = parse_source_file("declare class C { get foo(): typeof this.foo; }");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1);
        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        let NodeData::GetAccessorDeclaration(accessor) =
            &result.arena.get(class.members.nodes[0]).unwrap().data
        else {
            panic!("expected getter");
        };
        let NodeData::TypeQueryNode(query) =
            &result.arena.get(accessor.type_.unwrap()).unwrap().data
        else {
            panic!("expected type query");
        };
        let NodeData::QualifiedName(name) = &result.arena.get(query.expr_name).unwrap().data else {
            panic!("expected qualified this name");
        };
        let NodeData::Identifier(left) = &result.arena.get(name.left).unwrap().data else {
            panic!("expected this identifier");
        };
        assert_eq!(left.text, "this");
    }

    #[test]
    fn parses_super_qualified_type_queries_without_orphaned_tokens() {
        let result = parse_source_file("class C { z: typeof super.foo; a: this.foo; }");
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1, "{:?}", result.diagnostics);
        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 2, "{:?}", result.diagnostics);
        let NodeData::PropertyDeclaration(property) =
            &result.arena.get(class.members.nodes[0]).unwrap().data
        else {
            panic!("expected property declaration");
        };
        let NodeData::TypeQueryNode(query) =
            &result.arena.get(property.type_.unwrap()).unwrap().data
        else {
            panic!("expected type query");
        };
        let NodeData::QualifiedName(name) = &result.arena.get(query.expr_name).unwrap().data else {
            panic!("expected qualified super name");
        };
        let NodeData::Identifier(left) = &result.arena.get(name.left).unwrap().data else {
            panic!("expected super identifier");
        };
        assert_eq!(left.text, "super");
    }

    #[test]
    fn separates_conditional_types_from_following_declaration_tokens() {
        let result = parse_source_file(
            r"
                interface Schema {
                    a?: number
                    extends?: string | string[]
                }
                function test<T>(x: unknown) {
                    const value: [T] extends [number]
                        ? ([T] extends [string] ? { y: number } : { a: number })
                        : ([T] extends [string] ? { y: number } : { b: number }) = x;
                }
            ",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let interface = result
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::InterfaceDeclaration(interface) = &node.data else {
                    return None;
                };
                Some(interface)
            })
            .unwrap();
        assert_eq!(interface.members.nodes.len(), 2);

        let value = result
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::VariableDeclaration(variable) = &node.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &result.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == "value").then_some(variable)
            })
            .unwrap();
        let initializer = value
            .initializer
            .expect("initializer after conditional type");
        assert!(matches!(
            result.arena.get(initializer).map(|node| &node.data),
            Some(NodeData::Identifier(identifier)) if identifier.text == "x"
        ));
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
    fn parses_and_recovers_import_type_attributes() {
        let valid =
            parse_source_file("type T = import(\"pkg\", { with: { type: \"json\" } }).Value;");
        assert!(valid.diagnostics.is_empty(), "{:?}", valid.diagnostics);
        let valid_import = valid.arena.iter().find_map(|(_, node)| {
            let NodeData::ImportTypeNode(import) = &node.data else {
                return None;
            };
            Some(import)
        });
        let attributes = valid_import
            .expect("expected import type")
            .attributes
            .expect("expected import attributes");
        let NodeData::ImportAttributes(attributes) = &valid.arena.get(attributes).unwrap().data
        else {
            panic!("expected import attributes");
        };
        assert_eq!(attributes.attributes.nodes.len(), 1);

        let invalid = parse_source_file(
            "type T = import(\"pkg\", { with: { 1234, type: \"json\" } }).Value;",
        );
        assert!(!invalid.diagnostics.is_empty());
        let invalid_import = invalid.arena.iter().find_map(|(_, node)| {
            let NodeData::ImportTypeNode(import) = &node.data else {
                return None;
            };
            Some(import)
        });
        let attributes = invalid_import
            .expect("expected recovered import type")
            .attributes
            .expect("expected recovered import attributes");
        let NodeData::ImportAttributes(attributes) = &invalid.arena.get(attributes).unwrap().data
        else {
            panic!("expected recovered import attributes");
        };
        assert!(attributes.attributes.nodes.is_empty());
        assert!(invalid.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == Some(1478)
                && diagnostic.message == "Identifier or string literal expected."
        }));
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
    fn import_phase_disambiguates_type_imports_and_type_only_import_equals() {
        let result = parse_source_file(
            r#"
                import type from "default-binding";
                import type = require("value-equals");
                import type Foo = require("type-equals");
                import type from from "type-default-named-from";
                import type from = require("type-equals-named-from");
            "#,
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 5);

        let default_import = import_declaration(&result, statements[0]);
        let default_clause = import_clause(&result, default_import.import_clause.unwrap());
        assert_eq!(default_clause.phase_modifier, None);
        assert_eq!(
            identifier_text(&result, default_clause.name.unwrap()),
            "type"
        );

        let value_equals = import_equals_declaration(&result, statements[1]);
        assert!(!value_equals.is_type_only);
        assert_eq!(identifier_text(&result, value_equals.name), "type");
        assert_eq!(
            result
                .arena
                .get(value_equals.module_reference)
                .unwrap()
                .kind,
            SyntaxKind::ExternalModuleReference
        );

        let type_equals = import_equals_declaration(&result, statements[2]);
        assert!(type_equals.is_type_only);
        assert_eq!(identifier_text(&result, type_equals.name), "Foo");
        assert_eq!(
            result.arena.get(type_equals.module_reference).unwrap().kind,
            SyntaxKind::ExternalModuleReference
        );

        let named_from = import_declaration(&result, statements[3]);
        let named_from_clause = import_clause(&result, named_from.import_clause.unwrap());
        assert_eq!(
            named_from_clause.phase_modifier,
            Some(SyntaxKind::TypeKeyword)
        );
        assert_eq!(
            identifier_text(&result, named_from_clause.name.unwrap()),
            "from"
        );

        let named_from_equals = import_equals_declaration(&result, statements[4]);
        assert!(named_from_equals.is_type_only);
        assert_eq!(identifier_text(&result, named_from_equals.name), "from");
    }

    #[test]
    fn import_phase_parses_deferred_namespace_import() {
        let result = parse_source_file("import defer * as ns from \"deferred\";");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let declaration = import_declaration(&result, source_statements(&result)[0]);
        let clause = import_clause(&result, declaration.import_clause.unwrap());
        assert_eq!(clause.phase_modifier, Some(SyntaxKind::DeferKeyword));
        assert!(clause.name.is_none());
        let namespace = clause.named_bindings.unwrap();
        let NodeData::NamespaceImport(namespace) = &result.arena.get(namespace).unwrap().data
        else {
            panic!("expected namespace import");
        };
        assert_eq!(identifier_text(&result, namespace.name), "ns");
    }

    #[test]
    fn import_phase_keeps_type_and_defer_binding_boundaries_out_of_the_phase_slot() {
        let result = parse_source_file(
            r#"
                import defer from "default-binding";
                import defer = require("value-equals");
                import defer, { value } from "default-and-named";
                import type Default from "type-default";
                import type * as ns from "type-namespace";
                import type { Value } from "type-named";
            "#,
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 6);

        let defer_default = import_declaration(&result, statements[0]);
        let defer_default_clause = import_clause(&result, defer_default.import_clause.unwrap());
        assert_eq!(defer_default_clause.phase_modifier, None);
        assert_eq!(
            identifier_text(&result, defer_default_clause.name.unwrap()),
            "defer"
        );

        let defer_equals = import_equals_declaration(&result, statements[1]);
        assert!(!defer_equals.is_type_only);
        assert_eq!(identifier_text(&result, defer_equals.name), "defer");

        let defer_comma = import_declaration(&result, statements[2]);
        let defer_comma_clause = import_clause(&result, defer_comma.import_clause.unwrap());
        assert_eq!(defer_comma_clause.phase_modifier, None);
        assert_eq!(
            identifier_text(&result, defer_comma_clause.name.unwrap()),
            "defer"
        );
        assert_eq!(
            result
                .arena
                .get(defer_comma_clause.named_bindings.unwrap())
                .unwrap()
                .kind,
            SyntaxKind::NamedImports
        );

        for statement in &statements[3..] {
            let declaration = import_declaration(&result, *statement);
            let clause = import_clause(&result, declaration.import_clause.unwrap());
            assert_eq!(clause.phase_modifier, Some(SyntaxKind::TypeKeyword));
        }
    }

    #[test]
    fn import_phase_preserves_invalid_deferred_imports_for_grammar_checking() {
        let default = parse_source_file("import defer value from \"default\";");
        assert!(default.diagnostics.is_empty(), "{:?}", default.diagnostics);
        let declaration = import_declaration(&default, source_statements(&default)[0]);
        let clause = import_clause(&default, declaration.import_clause.unwrap());
        assert_eq!(clause.phase_modifier, Some(SyntaxKind::DeferKeyword));
        assert_eq!(identifier_text(&default, clause.name.unwrap()), "value");

        let named = parse_source_file("import defer { value } from \"named\";");
        assert!(named.diagnostics.is_empty(), "{:?}", named.diagnostics);
        let declaration = import_declaration(&named, source_statements(&named)[0]);
        let clause = import_clause(&named, declaration.import_clause.unwrap());
        assert_eq!(clause.phase_modifier, Some(SyntaxKind::DeferKeyword));
        assert_eq!(
            named
                .arena
                .get(clause.named_bindings.unwrap())
                .unwrap()
                .kind,
            SyntaxKind::NamedImports
        );

        let named_from = parse_source_file("import defer from from \"named-from\";");
        assert!(
            named_from.diagnostics.is_empty(),
            "{:?}",
            named_from.diagnostics
        );
        let declaration = import_declaration(&named_from, source_statements(&named_from)[0]);
        let clause = import_clause(&named_from, declaration.import_clause.unwrap());
        assert_eq!(clause.phase_modifier, Some(SyntaxKind::DeferKeyword));
        assert_eq!(identifier_text(&named_from, clause.name.unwrap()), "from");

        let type_conflict = parse_source_file("import defer type * as ns from \"type-conflict\";");
        let declaration = import_declaration(&type_conflict, source_statements(&type_conflict)[0]);
        let clause = import_clause(&type_conflict, declaration.import_clause.unwrap());
        assert_eq!(clause.phase_modifier, Some(SyntaxKind::DeferKeyword));
        assert_eq!(
            identifier_text(&type_conflict, clause.name.unwrap()),
            "type"
        );
        assert!(clause.named_bindings.is_none());
        assert!(
            type_conflict
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message == "'from' expected."),
            "{:?}",
            type_conflict.diagnostics
        );

        let equals = parse_source_file("import defer value = require(\"equals\");");
        let declaration = import_declaration(&equals, source_statements(&equals)[0]);
        let clause = import_clause(&equals, declaration.import_clause.unwrap());
        assert_eq!(clause.phase_modifier, Some(SyntaxKind::DeferKeyword));
        assert_eq!(identifier_text(&equals, clause.name.unwrap()), "value");
        assert!(
            equals
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message == "'from' expected."),
            "{:?}",
            equals.diagnostics
        );
    }

    #[test]
    fn import_equals_distinguishes_require_entities_from_external_references() {
        let result = parse_source_file(concat!(
            "import qualified = require.member;",
            "import bare = require;",
            "import expression = require(moduleName);",
            "import literal = require(\"pkg\");",
        ));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 4);

        let qualified = import_equals_declaration(&result, statements[0]);
        let NodeData::QualifiedName(qualified_name) =
            &result.arena.get(qualified.module_reference).unwrap().data
        else {
            panic!("expected qualified require entity name");
        };
        assert_eq!(identifier_text(&result, qualified_name.left), "require");
        assert_eq!(identifier_text(&result, qualified_name.right), "member");

        let bare = import_equals_declaration(&result, statements[1]);
        assert_eq!(identifier_text(&result, bare.module_reference), "require");

        for (statement, expected) in [(statements[2], "moduleName"), (statements[3], "pkg")] {
            let declaration = import_equals_declaration(&result, statement);
            let NodeData::ExternalModuleReference(reference) =
                &result.arena.get(declaration.module_reference).unwrap().data
            else {
                panic!("expected external module reference");
            };
            let actual = match &result.arena.get(reference.expression).unwrap().data {
                NodeData::Identifier(identifier) => identifier.text.as_str(),
                NodeData::StringLiteral(literal) => literal.text.as_str(),
                data => panic!("unexpected module reference expression: {data:?}"),
            };
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn missing_named_import_brace_does_not_consume_the_from_clause_or_next_statement() {
        let result = parse_source_file("import value, from \"pkg\"; const survived = 1;");
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1005)
                    && diagnostic.message == "'{' expected."),
            "{:?}",
            result.diagnostics
        );
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2, "{:?}", result.diagnostics);
        let declaration = import_declaration(&result, statements[0]);
        let clause = import_clause(&result, declaration.import_clause.unwrap());
        let NodeData::NamedImports(imports) = &result
            .arena
            .get(clause.named_bindings.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected recovered named imports");
        };
        assert!(imports.elements.nodes.is_empty());
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::VariableStatement
        );
    }

    #[test]
    fn import_attributes_obey_assert_and_with_line_break_boundaries() {
        let inline_assert =
            parse_source_file("import value from \"pkg\" assert { type: \"json\" };");
        assert!(
            inline_assert
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2880)),
            "{:?}",
            inline_assert.diagnostics
        );
        let declaration = import_declaration(&inline_assert, source_statements(&inline_assert)[0]);
        let NodeData::ImportAttributes(attributes) = &inline_assert
            .arena
            .get(declaration.attributes.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected import assertions");
        };
        assert_eq!(attributes.token, SyntaxKind::AssertKeyword);

        let separated_assert =
            parse_source_file("import value from \"pkg\"\nassert { type: \"json\" };");
        let declaration =
            import_declaration(&separated_assert, source_statements(&separated_assert)[0]);
        assert!(declaration.attributes.is_none());

        let separated_with =
            parse_source_file("import value from \"pkg\"\nwith { type: \"json\" };");
        assert!(
            separated_with.diagnostics.is_empty(),
            "{:?}",
            separated_with.diagnostics
        );
        let declaration =
            import_declaration(&separated_with, source_statements(&separated_with)[0]);
        assert!(declaration.attributes.is_some());

        let export = parse_source_file("export { value } from \"pkg\"\nwith { type: \"json\" };");
        let NodeData::ExportDeclaration(declaration) = &export
            .arena
            .get(source_statements(&export)[0])
            .unwrap()
            .data
        else {
            panic!("expected export declaration");
        };
        assert!(declaration.attributes.is_none());
    }

    #[test]
    fn import_attributes_preserve_list_shape_and_defer_value_grammar_checks() {
        let result = parse_source_file(
            "import value from \"pkg\" with {\n type: \"json\",\n mode: runtimeValue,\n};",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let declaration = import_declaration(&result, source_statements(&result)[0]);
        let NodeData::ImportAttributes(attributes) = &result
            .arena
            .get(declaration.attributes.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected import attributes");
        };
        assert!(attributes.multi_line);
        assert!(attributes.attributes.has_trailing_comma);
        assert_eq!(attributes.attributes.nodes.len(), 2);
        let NodeData::ImportAttribute(mode) = &result
            .arena
            .get(attributes.attributes.nodes[1])
            .unwrap()
            .data
        else {
            panic!("expected mode import attribute");
        };
        assert_eq!(
            result.arena.get(mode.value).unwrap().kind,
            SyntaxKind::Identifier
        );

        let invalid = parse_source_file("import value from \"pkg\" with { 0: \"json\" };");
        assert!(
            invalid
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1478)),
            "{:?}",
            invalid.diagnostics
        );
        let declaration = import_declaration(&invalid, source_statements(&invalid)[0]);
        let NodeData::ImportAttributes(attributes) = &invalid
            .arena
            .get(declaration.attributes.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected recovered import attributes");
        };
        assert!(attributes.attributes.nodes.is_empty());
    }

    #[test]
    fn import_bindings_use_await_and_yield_identifier_contexts() {
        let generator = parse_source_file("function* g() { import type yield from \"pkg\"; }");
        assert!(!generator.diagnostics.is_empty());
        let declaration = generator.arena.iter().find_map(|(_, node)| {
            let NodeData::ImportEqualsDeclaration(declaration) = &node.data else {
                return None;
            };
            Some(declaration)
        });
        let declaration = declaration.expect("expected recovered import-equals declaration");
        assert!(!declaration.is_type_only);
        assert_eq!(identifier_text(&generator, declaration.name), "type");

        let namespace = parse_source_file("async function f() { import * as await from \"pkg\"; }");
        assert!(
            namespace
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1003)),
            "{:?}",
            namespace.diagnostics
        );
        let namespace_name = namespace.arena.iter().find_map(|(_, node)| {
            let NodeData::NamespaceImport(namespace) = &node.data else {
                return None;
            };
            Some(namespace.name)
        });
        assert_eq!(
            namespace.arena.get(namespace_name.unwrap()).unwrap().flags,
            NODE_FLAG_HAS_ERROR
        );

        let named =
            parse_source_file("async function f() { import { value as await } from \"pkg\"; }");
        assert!(
            named
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1003)),
            "{:?}",
            named.diagnostics
        );
        let local_name = named.arena.iter().find_map(|(_, node)| {
            let NodeData::ImportSpecifier(specifier) = &node.data else {
                return None;
            };
            Some(specifier.name)
        });
        assert_eq!(
            named.arena.get(local_name.unwrap()).unwrap().flags,
            NODE_FLAG_HAS_ERROR
        );
    }

    #[test]
    fn import_equals_entity_names_restrict_only_the_first_segment() {
        let valid = parse_source_file("function* g() { import Alias = namespace.yield; }");
        assert!(valid.diagnostics.is_empty(), "{:?}", valid.diagnostics);
        let declaration = valid.arena.iter().find_map(|(_, node)| {
            let NodeData::ImportEqualsDeclaration(declaration) = &node.data else {
                return None;
            };
            Some(declaration)
        });
        let declaration = declaration.expect("expected import-equals declaration");
        let NodeData::QualifiedName(name) =
            &valid.arena.get(declaration.module_reference).unwrap().data
        else {
            panic!("expected qualified entity name");
        };
        assert_eq!(identifier_text(&valid, name.left), "namespace");
        assert_eq!(identifier_text(&valid, name.right), "yield");

        let invalid = parse_source_file("import Alias = class.member;");
        assert!(
            invalid
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1003)),
            "{:?}",
            invalid.diagnostics
        );
        let declaration = import_equals_declaration(&invalid, source_statements(&invalid)[0]);
        let reference = invalid.arena.get(declaration.module_reference).unwrap();
        assert_eq!(reference.kind, SyntaxKind::Identifier);
        assert_eq!(reference.flags, NODE_FLAG_HAS_ERROR);
        assert_eq!(reference.range.start, reference.range.end);
    }

    #[test]
    fn import_module_specifier_preserves_non_string_expressions_for_grammar_checking() {
        let result = parse_source_file("import value from moduleName;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let declaration = import_declaration(&result, source_statements(&result)[0]);
        assert_eq!(
            result.arena.get(declaration.module_specifier).unwrap().kind,
            SyntaxKind::Identifier
        );
        assert_eq!(
            identifier_text(&result, declaration.module_specifier),
            "moduleName"
        );
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
    fn recovers_contextual_keyword_import_equals_entity_names() {
        let result = parse_source_file("import fs = module(\"fs\");");
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2);
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
        assert_eq!(reference.text, "module");
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::ExpressionStatement
        );
    }

    #[test]
    fn recovers_import_equals_when_equals_token_is_missing() {
        let result = parse_source_file("import Foo From './Foo';");
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message == "'=' expected."),
            "{:?}",
            result.diagnostics
        );
        let statements = source_statements(&result);
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
        assert_eq!(reference.text, "From");
        assert_eq!(
            result.arena.get(statements[1]).unwrap().kind,
            SyntaxKind::ExpressionStatement
        );
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
    fn parses_nested_dynamic_imports_in_async_generator_expressions() {
        let result = parse_source_file(concat!(
            "async function* foo() {\n",
            "    import((await import(yield \"foo\")).default);\n",
            "}",
        ));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let dynamic_imports = result
            .arena
            .iter()
            .filter(|(_, node)| {
                let NodeData::CallExpression(call) = &node.data else {
                    return false;
                };
                matches!(
                    result.arena.get(call.expression).map(|node| &node.data),
                    Some(NodeData::Identifier(identifier)) if identifier.text == "import"
                )
            })
            .count();
        assert_eq!(dynamic_imports, 2);
        assert_eq!(
            result
                .arena
                .iter()
                .filter(|(_, node)| node.kind == SyntaxKind::AwaitExpression)
                .count(),
            1
        );
        assert_eq!(
            result
                .arena
                .iter()
                .filter(|(_, node)| node.kind == SyntaxKind::YieldExpression)
                .count(),
            1
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
    fn recovers_keyword_type_parameters_and_keyword_class_names() {
        let result = parse_source_file(concat!(
            "function bigGeneric<implements, interface, let, private>(value: implements) {} ",
            "namespace Names { class implements {} class Derived implements Contract {} ",
            "class Fields { public var = 0; } }",
        ));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 2, "{:?}", result.diagnostics);

        let NodeData::FunctionDeclaration(function) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected recovered generic function");
        };
        let parameter_names = function
            .type_parameters
            .as_ref()
            .unwrap()
            .nodes
            .iter()
            .map(|parameter| {
                let NodeData::TypeParameterDeclaration(parameter) =
                    &result.arena.get(*parameter).unwrap().data
                else {
                    panic!("expected type parameter");
                };
                let NodeData::Identifier(name) = &result.arena.get(parameter.name).unwrap().data
                else {
                    panic!("expected type parameter name");
                };
                name.text.as_str()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            parameter_names,
            ["implements", "interface", "let", "private"]
        );
        assert_eq!(function.parameters.nodes.len(), 1);
        assert!(function.body.is_some());

        let NodeData::ModuleDeclaration(module) = &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected namespace");
        };
        let NodeData::ModuleBlock(block) = &result.arena.get(module.body.unwrap()).unwrap().data
        else {
            panic!("expected namespace body");
        };
        assert_eq!(block.statements.nodes.len(), 3, "{:?}", result.diagnostics);

        let NodeData::ClassDeclaration(keyword_name) =
            &result.arena.get(block.statements.nodes[0]).unwrap().data
        else {
            panic!("expected keyword-named class");
        };
        let NodeData::Identifier(keyword_name_text) =
            &result.arena.get(keyword_name.name.unwrap()).unwrap().data
        else {
            panic!("expected keyword class name");
        };
        assert_eq!(keyword_name_text.text, "implements");
        assert!(keyword_name.heritage_clauses.is_none());

        let NodeData::ClassDeclaration(derived) =
            &result.arena.get(block.statements.nodes[1]).unwrap().data
        else {
            panic!("expected derived class");
        };
        assert_eq!(derived.heritage_clauses.as_ref().unwrap().nodes.len(), 1);

        let NodeData::ClassDeclaration(fields) =
            &result.arena.get(block.statements.nodes[2]).unwrap().data
        else {
            panic!("expected fields class");
        };
        let NodeData::PropertyDeclaration(field) =
            &result.arena.get(fields.members.nodes[0]).unwrap().data
        else {
            panic!("expected recovered keyword field");
        };
        let NodeData::Identifier(field_name) = &result.arena.get(field.name).unwrap().data else {
            panic!("expected recovered field name");
        };
        assert_eq!(field_name.text, "var");
    }

    #[test]
    fn parses_decorated_class_expression() {
        let result = parse_source_file("const value = @first @factory(arg) class Inner {};");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statement = source_statements(&result)[0];
        let (list, _) = variable_list(&result, statement);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let class_id = declaration.initializer.unwrap();
        let class_node = result.arena.get(class_id).unwrap();
        let NodeData::ClassExpression(class) = &class_node.data else {
            panic!("expected class expression");
        };
        let modifiers = class.modifiers.as_ref().unwrap();
        assert_eq!(modifiers.list.nodes.len(), 2);
        assert_eq!(class_node.range.start.get(), 14);
        assert!(
            modifiers
                .list
                .nodes
                .iter()
                .all(|modifier| { result.arena.get(*modifier).unwrap().parent == Some(class_id) })
        );
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

        let generic_call = parse_source_file("class Derived<T> extends base<T>() {}");
        assert!(
            generic_call.diagnostics.is_empty(),
            "{:?}",
            generic_call.diagnostics
        );
        let generic_call_statement = source_statements(&generic_call)[0];
        let NodeData::ClassDeclaration(class) =
            &generic_call.arena.get(generic_call_statement).unwrap().data
        else {
            panic!("expected class declaration");
        };
        let clause_id = class.heritage_clauses.as_ref().unwrap().nodes[0];
        let NodeData::HeritageClause(clause) = &generic_call.arena.get(clause_id).unwrap().data
        else {
            panic!("expected heritage clause");
        };
        let NodeData::ExpressionWithTypeArguments(heritage) =
            &generic_call.arena.get(clause.types.nodes[0]).unwrap().data
        else {
            panic!("expected heritage expression");
        };
        assert!(heritage.type_arguments.is_none());
        let NodeData::CallExpression(call) =
            &generic_call.arena.get(heritage.expression).unwrap().data
        else {
            panic!("expected generic call expression");
        };
        assert_eq!(call.type_arguments.as_ref().unwrap().nodes.len(), 1);
        assert!(call.arguments.nodes.is_empty());
    }

    #[test]
    fn recovers_trailing_commas_in_heritage_clauses() {
        let source = "class Derived extends Base, { value = 1; }";
        let result = parse_source_file(source);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [1009]
        );
        let comma = source.find(',').unwrap();
        assert_eq!(result.diagnostics[0].range, text_range(comma, comma + 1));

        let statement = source_statements(&result)[0];
        let NodeData::ClassDeclaration(class) = &result.arena.get(statement).unwrap().data else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 1);
        let clause_id = class.heritage_clauses.as_ref().unwrap().nodes[0];
        let NodeData::HeritageClause(clause) = &result.arena.get(clause_id).unwrap().data else {
            panic!("expected heritage clause");
        };
        assert_eq!(clause.types.nodes.len(), 1);
        assert!(clause.types.has_trailing_comma);
        let NodeData::ExpressionWithTypeArguments(heritage) =
            &result.arena.get(clause.types.nodes[0]).unwrap().data
        else {
            panic!("expected heritage expression");
        };
        let NodeData::Identifier(base) = &result.arena.get(heritage.expression).unwrap().data
        else {
            panic!("expected heritage identifier");
        };
        assert_eq!(base.text, "Base");
    }

    #[test]
    fn consumes_primitive_implements_names_without_losing_class_bodies() {
        let result = parse_source_file(
            "class C implements number {} const D = class implements string {}; class E {}",
        );
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 3, "{:?}", result.diagnostics);
        for statement in [statements[0], statements[2]] {
            assert!(matches!(
                result.arena.get(statement).unwrap().data,
                NodeData::ClassDeclaration(_)
            ));
        }
        assert!(matches!(
            result.arena.get(statements[1]).unwrap().data,
            NodeData::VariableStatement(_)
        ));
    }

    #[test]
    fn recovers_optional_object_and_void_class_heritage() {
        let optional = parse_source_file("class C extends A?.B {}");
        let NodeData::ClassDeclaration(class) = &optional
            .arena
            .get(source_statements(&optional)[0])
            .unwrap()
            .data
        else {
            panic!("expected class declaration");
        };
        let clause = class.heritage_clauses.as_ref().unwrap().nodes[0];
        let NodeData::HeritageClause(clause) = &optional.arena.get(clause).unwrap().data else {
            panic!("expected heritage clause");
        };
        let NodeData::ExpressionWithTypeArguments(heritage) =
            &optional.arena.get(clause.types.nodes[0]).unwrap().data
        else {
            panic!("expected heritage expression");
        };
        assert!(matches!(
            optional.arena.get(heritage.expression).unwrap().data,
            NodeData::PropertyAccessExpression(ref access) if access.question_dot_token.is_some()
        ));

        let object = parse_source_file("class C extends { foo: string; } {}");
        let NodeData::ClassDeclaration(class) = &object
            .arena
            .get(source_statements(&object)[0])
            .unwrap()
            .data
        else {
            panic!("expected class declaration");
        };
        assert_eq!(class.members.nodes.len(), 0);

        let void = parse_source_file("class C extends void {}");
        assert!(
            source_statements(&void).len() >= 2,
            "{:?}",
            void.diagnostics
        );
    }

    #[test]
    fn leaves_void_after_an_anonymous_recovered_class() {
        let result = parse_source_file("class void {}");
        let statements = source_statements(&result);
        assert!(statements.len() >= 2, "{:?}", result.diagnostics);
        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        assert!(class.name.is_none());
        assert!(class.members.nodes.is_empty());
    }

    #[test]
    fn recovers_modifier_without_member_name_at_following_block() {
        let result = parse_source_file("class C { public {}; }");
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 3, "{:?}", result.diagnostics);
        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        assert!(class.members.nodes.is_empty());
        assert!(matches!(
            result.arena.get(statements[1]).unwrap().data,
            NodeData::Block(_)
        ));
        assert!(matches!(
            result.arena.get(statements[2]).unwrap().data,
            NodeData::EmptyStatement(_)
        ));
    }

    #[test]
    fn recovers_try_statement_from_inside_a_class() {
        let result = parse_source_file(
            "class C { try { public value = initialize(); } catch (error) {} method(); {} }",
        );
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 4, "{:?}", result.diagnostics);
        assert!(matches!(
            result.arena.get(statements[0]).unwrap().data,
            NodeData::ClassDeclaration(_)
        ));
        assert!(matches!(
            result.arena.get(statements[1]).unwrap().data,
            NodeData::TryStatement(_)
        ));
        assert!(matches!(
            result.arena.get(statements[2]).unwrap().data,
            NodeData::ExpressionStatement(_)
        ));
        assert!(matches!(
            result.arena.get(statements[3]).unwrap().data,
            NodeData::Block(_)
        ));
    }

    #[test]
    fn recovers_global_namespace_from_inside_a_class() {
        let result = parse_source_file("class C { global x }");
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 3, "{:?}", result.diagnostics);

        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        assert!(class.members.nodes.is_empty());

        let NodeData::ModuleDeclaration(global) = &result.arena.get(statements[1]).unwrap().data
        else {
            panic!("expected recovered global namespace");
        };
        assert_eq!(global.keyword, SyntaxKind::GlobalKeyword);
        assert!(global.body.is_none());

        let NodeData::ExpressionStatement(expression) =
            &result.arena.get(statements[2]).unwrap().data
        else {
            panic!("expected recovered expression");
        };
        let NodeData::Identifier(identifier) =
            &result.arena.get(expression.expression).unwrap().data
        else {
            panic!("expected identifier expression");
        };
        assert_eq!(identifier.text, "x");
    }

    #[test]
    fn preserves_keyword_types_used_as_recovery_expressions() {
        let result = parse_source_file("any; number; string;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 3);
        for (statement, expected) in statements.iter().zip(["any", "number", "string"]) {
            let NodeData::ExpressionStatement(statement) =
                &result.arena.get(*statement).unwrap().data
            else {
                panic!("expected expression statement");
            };
            let NodeData::Identifier(identifier) =
                &result.arena.get(statement.expression).unwrap().data
            else {
                panic!("expected identifier expression");
            };
            assert_eq!(identifier.text, expected);
        }
    }

    #[test]
    fn parses_undefined_as_an_identifier_expression_and_a_keyword_type() {
        let source = concat!(
            "declare function f(o: { y?: string }): void;\n",
            "f({ y: undefined });\n",
            "type U = undefined;",
        );
        let result = parse_source_file(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert!(
            result
                .arena
                .iter()
                .all(|(_, node)| node.data.matches_syntax_kind(node.kind))
        );

        let value = result
            .arena
            .iter()
            .find_map(|(_, node)| match &node.data {
                NodeData::PropertyAssignment(property) => Some(property.initializer),
                _ => None,
            })
            .expect("object property initializer");
        let value_node = result.arena.get(value).unwrap();
        let NodeData::Identifier(value_identifier) = &value_node.data else {
            panic!("expected undefined value identifier");
        };
        assert_eq!(value_node.kind, SyntaxKind::Identifier);
        assert_eq!(value_identifier.text, "undefined");
        assert_eq!(
            (value_node.range.start.get(), value_node.range.end.get()),
            (52, 61)
        );

        let statements = source_statements(&result);
        let NodeData::TypeAliasDeclaration(alias) = &result.arena.get(statements[2]).unwrap().data
        else {
            panic!("expected type alias");
        };
        let type_node = result.arena.get(alias.type_).unwrap();
        assert_eq!(type_node.kind, SyntaxKind::UndefinedKeyword);
        assert!(matches!(type_node.data, NodeData::KeywordTypeNode(_)));
        assert_eq!(
            (type_node.range.start.get(), type_node.range.end.get()),
            (75, 84)
        );
    }

    #[test]
    fn recovers_after_colons_in_expression_statements() {
        let result = parse_source_file("{ this.value: any; }");
        let statements = source_statements(&result);
        let NodeData::Block(block) = &result.arena.get(statements[0]).unwrap().data else {
            panic!("expected block");
        };
        assert_eq!(block.statements.nodes.len(), 2);
        let NodeData::ExpressionStatement(recovered) =
            &result.arena.get(block.statements.nodes[1]).unwrap().data
        else {
            panic!("expected recovered expression statement");
        };
        let NodeData::Identifier(identifier) =
            &result.arena.get(recovered.expression).unwrap().data
        else {
            panic!("expected identifier expression");
        };
        assert_eq!(identifier.text, "any");
        assert!(result.arena.iter().all(|(_, node)| {
            !matches!(&node.data, NodeData::Identifier(identifier) if identifier.text.is_empty())
        }));
    }

    #[test]
    fn keeps_empty_element_access_before_call_parentheses() {
        let result = parse_source_file("new Z[]();");
        let statements = source_statements(&result);
        let NodeData::ExpressionStatement(statement) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected expression statement");
        };
        let NodeData::CallExpression(call) = &result.arena.get(statement.expression).unwrap().data
        else {
            panic!("expected call expression");
        };
        assert!(call.arguments.nodes.is_empty());
        let NodeData::ElementAccessExpression(access) =
            &result.arena.get(call.expression).unwrap().data
        else {
            panic!("expected element access expression");
        };
        let NodeData::Identifier(argument) =
            &result.arena.get(access.argument_expression).unwrap().data
        else {
            panic!("expected missing identifier");
        };
        assert!(argument.text.is_empty());
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
    fn recovers_invalid_contextual_declaration_names_as_statements() {
        let result = parse_source_file(concat!(
            "namespace 100 {}\ninterface 100 {}\ntype 100 {}\n",
            "export namespace 100 {}\nexport interface 100 {}\nexport type 100 {}\n",
        ));
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 21);
        assert_eq!(
            statements
                .iter()
                .filter(|statement| {
                    matches!(
                        result.arena.get(**statement).map(|node| &node.data),
                        Some(NodeData::NotEmittedStatement(_))
                    )
                })
                .count(),
            3
        );
        let names = statements
            .iter()
            .filter_map(|statement| {
                let NodeData::ExpressionStatement(expression) = &result.arena.get(*statement)?.data
                else {
                    return None;
                };
                let NodeData::Identifier(identifier) =
                    &result.arena.get(expression.expression)?.data
                else {
                    return None;
                };
                (!identifier.text.is_empty()).then_some(identifier.text.as_str())
            })
            .collect::<Vec<_>>();
        assert_eq!(
            names,
            [
                "namespace",
                "interface",
                "type",
                "namespace",
                "interface",
                "type"
            ]
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
    fn reports_unclosed_jsx_elements_at_their_opening_tag_names() {
        let source = "let x = <    Foo.Bar >Hello\nlet y = <   Baz >Hello";
        let result = parse_jsx_source_file(source);
        let mut diagnostics = result
            .diagnostics
            .iter()
            .map(|diagnostic| {
                (
                    diagnostic.code,
                    diagnostic.range.start.get(),
                    diagnostic.message.as_str(),
                )
            })
            .collect::<Vec<_>>();
        diagnostics.sort_by_key(|diagnostic| diagnostic.1);

        assert_eq!(
            diagnostics,
            [
                (
                    Some(17008),
                    u32::try_from(source.find("Foo.Bar").unwrap()).unwrap(),
                    "JSX element 'Foo.Bar' has no corresponding closing tag.",
                ),
                (
                    Some(17008),
                    u32::try_from(source.find("Baz").unwrap()).unwrap(),
                    "JSX element 'Baz' has no corresponding closing tag.",
                ),
                (
                    Some(1005),
                    u32::try_from(source.len()).unwrap(),
                    "'</' expected.",
                ),
            ]
        );
    }

    #[test]
    fn reports_unclosed_jsx_fragments_at_their_opening_tags() {
        let source = "const value = <>content";
        let result = parse_jsx_source_file(source);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| {
                    (
                        diagnostic.code,
                        diagnostic.range.start.get(),
                        diagnostic.message.as_str(),
                    )
                })
                .collect::<Vec<_>>(),
            [
                (
                    Some(17014),
                    u32::try_from(source.find("<>").unwrap()).unwrap(),
                    "JSX fragment has no corresponding closing tag.",
                ),
                (
                    Some(1005),
                    u32::try_from(source.len()).unwrap(),
                    "'</' expected.",
                ),
            ]
        );
    }

    #[test]
    fn reports_rescanned_jsx_text_diagnostics_only_once() {
        let result = parse_jsx_source_file("const value = <div> > }</div>;");
        let jsx_diagnostics = result
            .diagnostics
            .iter()
            .filter_map(|diagnostic| {
                matches!(diagnostic.code, Some(1381 | 1382))
                    .then_some((diagnostic.code, diagnostic.range.start.get()))
            })
            .collect::<Vec<_>>();

        assert_eq!(jsx_diagnostics, [(Some(1382), 20), (Some(1381), 22)]);
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
    fn rescans_invalid_numeric_jsx_tag_as_child_text() {
        let result = parse_jsx_source_file(concat!(
            "const a = + <number> x;\n",
            "const b = + <> x;\n",
            "const c = + <1234> x;\n",
        ));
        assert!(result.arena.iter().any(|(_, node)| {
            matches!(
                &node.data,
                NodeData::JsxText(text) if text.text.contains("1234> x;")
            )
        }));
    }

    #[test]
    fn javascript_jsx_recovers_unary_elements_without_type_arguments() {
        let less_than = parse_javascript_source_file("~< <");
        let NodeData::ExpressionStatement(statement) = &less_than
            .arena
            .get(source_statements(&less_than)[0])
            .unwrap()
            .data
        else {
            panic!("expected expression statement");
        };
        let NodeData::BinaryExpression(binary) =
            &less_than.arena.get(statement.expression).unwrap().data
        else {
            panic!("expected binary expression");
        };
        let NodeData::PrefixUnaryExpression(prefix) =
            &less_than.arena.get(binary.left).unwrap().data
        else {
            panic!("expected prefix expression");
        };
        let NodeData::JsxSelfClosingElement(element) =
            &less_than.arena.get(prefix.operand).unwrap().data
        else {
            panic!("expected self-closing JSX element");
        };
        assert!(element.type_arguments.is_none());

        let spread = parse_javascript_source_file("!< {:>");
        let NodeData::ExpressionStatement(statement) = &spread
            .arena
            .get(source_statements(&spread)[0])
            .unwrap()
            .data
        else {
            panic!("expected expression statement");
        };
        let NodeData::PrefixUnaryExpression(prefix) =
            &spread.arena.get(statement.expression).unwrap().data
        else {
            panic!("expected prefix expression");
        };
        assert!(matches!(
            spread.arena.get(prefix.operand).map(|node| &node.data),
            Some(NodeData::JsxElement(_))
        ));
    }

    #[test]
    fn reports_trailing_jsx_comparison_expression_at_end_of_file() {
        for source in ["~<></> <", "~<></> <\n", "~<></> <\r\n"] {
            let result = parse_javascript_source_file(source);
            assert_eq!(
                result
                    .diagnostics
                    .iter()
                    .map(|diagnostic| {
                        (
                            diagnostic.code,
                            diagnostic.range.start.get(),
                            diagnostic.range.end.get(),
                            diagnostic.message.as_str(),
                        )
                    })
                    .collect::<Vec<_>>(),
                [(Some(1109), 8, 8, "Expression expected.")],
                "source: {source:?}"
            );
        }
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
    fn optional_tuple_annotation_stops_before_variable_initializer() {
        let result = parse_source_file(
            "let [value = { a: 1 }]: [{ a: number }?] = []; type Alias<T> = [T?];",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let (list, _) = variable_list(&result, source_statements(&result)[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        assert!(declaration.initializer.is_some());
        let NodeData::TupleTypeNode(tuple) =
            &result.arena.get(declaration.type_.unwrap()).unwrap().data
        else {
            panic!("expected tuple annotation");
        };
        assert_eq!(tuple.elements.nodes.len(), 1);
        assert_eq!(
            result.arena.get(tuple.elements.nodes[0]).unwrap().kind,
            SyntaxKind::OptionalType
        );
        let NodeData::TypeAliasDeclaration(alias) = &result
            .arena
            .get(source_statements(&result)[1])
            .unwrap()
            .data
        else {
            panic!("expected type alias");
        };
        let NodeData::TupleTypeNode(tuple) = &result.arena.get(alias.type_).unwrap().data else {
            panic!("expected tuple alias");
        };
        assert_eq!(
            result.arena.get(tuple.elements.nodes[0]).unwrap().kind,
            SyntaxKind::OptionalType
        );
    }

    #[test]
    fn parses_comma_separated_interface_members_without_empty_recovery_nodes() {
        let result = parse_source_file("interface Pair<T> { first: T, second: T, }");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        let NodeData::InterfaceDeclaration(interface) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected interface");
        };
        assert_eq!(interface.members.nodes.len(), 2);
        let names = interface
            .members
            .nodes
            .iter()
            .map(|member| {
                let NodeData::PropertyDeclaration(property) =
                    &result.arena.get(*member).unwrap().data
                else {
                    panic!("expected property");
                };
                let NodeData::Identifier(name) = &result.arena.get(property.name).unwrap().data
                else {
                    panic!("expected identifier name");
                };
                name.text.as_str()
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["first", "second"]);
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
    fn preserves_omitted_array_literal_elements() {
        let result = parse_source_file("const values = [, second, ,];");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let (list, _) = variable_list(&result, source_statements(&result)[0]);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let initializer = declaration.initializer.expect("initializer");
        let NodeData::ArrayLiteralExpression(array) = &result.arena.get(initializer).unwrap().data
        else {
            panic!("expected array literal");
        };
        assert_eq!(
            array
                .elements
                .nodes
                .iter()
                .map(|element| result.arena.get(*element).unwrap().kind)
                .collect::<Vec<_>>(),
            [
                SyntaxKind::OmittedExpression,
                SyntaxKind::Identifier,
                SyntaxKind::OmittedExpression,
            ]
        );
        assert!(array.elements.has_trailing_comma);
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
    fn parses_typeof_import_as_a_type_argument() {
        let result = parse_source_file("useRef<typeof import(\"pkg\")>(null);");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1);
        let NodeData::ExpressionStatement(statement) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected expression statement");
        };
        let NodeData::CallExpression(call) = &result.arena.get(statement.expression).unwrap().data
        else {
            panic!("expected call expression");
        };
        let type_argument = call.type_arguments.as_ref().unwrap().nodes[0];
        let NodeData::ImportTypeNode(import) = &result.arena.get(type_argument).unwrap().data
        else {
            panic!("expected import type");
        };
        assert!(import.is_type_of);
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
                SyntaxKind::ExpressionWithTypeArguments
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

    fn import_declaration(
        result: &ParseResult,
        statement: NodeId,
    ) -> &ts_ast::ImportDeclarationData {
        let NodeData::ImportDeclaration(declaration) = &result.arena.get(statement).unwrap().data
        else {
            panic!("expected import declaration");
        };
        declaration
    }

    fn import_clause(result: &ParseResult, clause: NodeId) -> &ts_ast::ImportClauseData {
        let NodeData::ImportClause(clause) = &result.arena.get(clause).unwrap().data else {
            panic!("expected import clause");
        };
        clause
    }

    fn import_equals_declaration(
        result: &ParseResult,
        statement: NodeId,
    ) -> &ts_ast::ImportEqualsDeclarationData {
        let NodeData::ImportEqualsDeclaration(declaration) =
            &result.arena.get(statement).unwrap().data
        else {
            panic!("expected import-equals declaration");
        };
        declaration
    }

    fn identifier_text(result: &ParseResult, identifier: NodeId) -> &str {
        let NodeData::Identifier(identifier) = &result.arena.get(identifier).unwrap().data else {
            panic!("expected identifier");
        };
        &identifier.text
    }

    #[test]
    fn preserves_unary_expression_after_invalid_variable_initializer_tokens() {
        let result = parse_source_file("const a =!@#!@$\nconst b = !@#!@#!@#!\n");
        let kinds = source_statements(&result)
            .iter()
            .map(|statement| result.arena.get(*statement).unwrap().kind)
            .collect::<Vec<_>>();
        assert_eq!(
            kinds,
            [
                SyntaxKind::VariableStatement,
                SyntaxKind::ExpressionStatement,
                SyntaxKind::VariableStatement,
                SyntaxKind::ExpressionStatement,
                SyntaxKind::ExpressionStatement,
                SyntaxKind::ExpressionStatement,
            ]
        );
    }

    #[test]
    fn recovers_expressions_after_invalid_identifier_continuations() {
        let result = parse_source_file("var a₁ = \"hello\"; alert(a₁)");
        assert_eq!(
            result
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [1134, 1134, 1127, 1127]
        );
        let kinds = source_statements(&result)
            .iter()
            .map(|statement| result.arena.get(*statement).unwrap().kind)
            .collect::<Vec<_>>();
        assert_eq!(
            kinds,
            [
                SyntaxKind::VariableStatement,
                SyntaxKind::ExpressionStatement,
                SyntaxKind::ExpressionStatement,
            ]
        );
    }

    #[test]
    fn parses_typed_async_arrows_and_assignment_for_initializers() {
        let result = parse_source_file(concat!(
            "const f = async (): Promise<void> => {};\n",
            "for (i = 1; i < limit; ++i) {}\n",
            "for (let x = 0, y = 1; x < y; ++x, --y) {}\n",
            "for (key in value) {}\n",
            "for (const property in value) {}\n",
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
        assert_eq!(for_statements.len(), 2);
        let initializer = for_statements[0].initializer.expect("initializer");
        assert_eq!(
            result.arena.get(initializer).unwrap().kind,
            SyntaxKind::BinaryExpression
        );
        let declaration_list = for_statements[1].initializer.expect("initializer");
        assert_eq!(declaration_nodes(&result, declaration_list).len(), 2);
        assert_eq!(
            result
                .arena
                .get(for_statements[1].incrementor.expect("incrementor"))
                .unwrap()
                .kind,
            SyntaxKind::BinaryExpression
        );
        assert!(
            result
                .arena
                .iter()
                .filter(|(_, node)| matches!(node.data, NodeData::ForInOrOfStatement(_)))
                .count()
                == 2
        );
    }

    #[test]
    fn untyped_optional_parameter_range_contains_its_question_token() {
        let result = parse_source_file("const f: () => void = (a?, ...b) => {};");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let (parameter_id, parameter_node) = result
            .arena
            .iter()
            .find(|(_, node)| {
                matches!(
                    &node.data,
                    NodeData::ParameterDeclaration(parameter)
                        if parameter.question_token.is_some()
                )
            })
            .expect("optional parameter");
        let NodeData::ParameterDeclaration(parameter) = &parameter_node.data else {
            unreachable!();
        };
        let question = result.arena.get(parameter.question_token.unwrap()).unwrap();

        assert_eq!(
            (
                parameter_node.range.start.get(),
                parameter_node.range.end.get()
            ),
            (23, 25)
        );
        assert_eq!(
            (question.range.start.get(), question.range.end.get()),
            (24, 25)
        );
        assert_eq!(question.parent, Some(parameter_id));
        assert!(parameter_node.range.start.get() <= question.range.start.get());
        assert!(question.range.end.get() <= parameter_node.range.end.get());
    }

    #[test]
    fn recovers_await_named_arrow_inside_async_call_parameters() {
        let result = parse_source_file("var foo = async (a = await => await): Promise<void> => {}");
        let arrows = result
            .arena
            .iter()
            .filter_map(|(id, node)| matches!(node.data, NodeData::ArrowFunction(_)).then_some(id))
            .collect::<Vec<_>>();
        assert_eq!(arrows.len(), 1);
        let NodeData::ArrowFunction(arrow) = &result.arena.get(arrows[0]).unwrap().data else {
            unreachable!();
        };
        let parameter = arrow.parameters.nodes[0];
        let NodeData::ParameterDeclaration(parameter) = &result.arena.get(parameter).unwrap().data
        else {
            unreachable!();
        };
        assert!(matches!(
            &result.arena.get(parameter.name).unwrap().data,
            NodeData::Identifier(identifier) if identifier.text == "await"
        ));
        assert!(matches!(
            &result.arena.get(arrow.body).unwrap().data,
            NodeData::Identifier(identifier) if identifier.text == "await"
        ));
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| {
                    (
                        diagnostic.code,
                        diagnostic.message.as_str(),
                        diagnostic.range.start.get(),
                    )
                })
                .collect::<Vec<_>>(),
            [
                (Some(1005), "',' expected.", 36),
                (Some(1005), "',' expected.", 45),
                (Some(1109), "Expression expected.", 52),
            ]
        );
    }

    #[test]
    fn recovers_await_arrow_in_async_function_parameters_as_comma_expression() {
        let result = parse_source_file("async function foo(a = await => await): Promise<void> {}");
        let statements = source_statements(&result);
        assert_eq!(
            statements
                .iter()
                .map(|statement| result.arena.get(*statement).unwrap().kind)
                .collect::<Vec<_>>(),
            [SyntaxKind::FunctionDeclaration]
        );
        let NodeData::FunctionDeclaration(function) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            unreachable!();
        };
        let NodeData::ParameterDeclaration(parameter) =
            &result.arena.get(function.parameters.nodes[0]).unwrap().data
        else {
            unreachable!();
        };
        assert!(matches!(
            parameter
                .initializer
                .and_then(|initializer| result.arena.get(initializer))
                .map(|node| &node.data),
            Some(NodeData::BinaryExpression(_))
        ));
    }

    #[test]
    fn separates_invalid_prefix_updates_from_await_expressions() {
        let result = parse_source_file("async function f() { ++await 1; --await 2; }");
        let statements = source_statements(&result);
        let NodeData::FunctionDeclaration(function) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            unreachable!();
        };
        let NodeData::Block(block) = &result.arena.get(function.body.unwrap()).unwrap().data else {
            unreachable!();
        };
        assert_eq!(block.statements.nodes.len(), 4);
        for (index, statement) in block.statements.nodes.iter().enumerate() {
            let NodeData::ExpressionStatement(statement) =
                &result.arena.get(*statement).unwrap().data
            else {
                unreachable!();
            };
            if index % 2 == 0 {
                let NodeData::PrefixUnaryExpression(prefix) =
                    &result.arena.get(statement.expression).unwrap().data
                else {
                    unreachable!();
                };
                assert!(matches!(
                    &result.arena.get(prefix.operand).unwrap().data,
                    NodeData::Identifier(identifier) if identifier.text.is_empty()
                ));
            } else {
                assert!(matches!(
                    result
                        .arena
                        .get(statement.expression)
                        .map(|node| &node.data),
                    Some(NodeData::AwaitExpression(_))
                ));
            }
        }
    }

    #[test]
    fn restores_await_context_for_nested_ordinary_functions() {
        let result = parse_source_file(
            "async function outer() { function inner() { await(value); } await(value); }",
        );
        let await_expressions = result
            .arena
            .iter()
            .filter(|(_, node)| matches!(node.data, NodeData::AwaitExpression(_)))
            .count();
        let await_calls = result
            .arena
            .iter()
            .filter(|(_, node)| {
                matches!(
                    &node.data,
                    NodeData::CallExpression(call)
                        if matches!(
                            result.arena.get(call.expression).map(|node| &node.data),
                            Some(NodeData::Identifier(identifier)) if identifier.text == "await"
                        )
                )
            })
            .count();
        assert_eq!(await_expressions, 1);
        assert_eq!(await_calls, 1);
    }

    #[test]
    fn parses_bare_await_before_expression_terminators_as_an_identifier() {
        let result = parse_source_file("var value = { [await]: 1 }; function f(await = await) {}");
        assert_eq!(
            result
                .arena
                .iter()
                .filter(|(_, node)| matches!(node.data, NodeData::AwaitExpression(_)))
                .count(),
            0
        );
        assert!(
            result
                .arena
                .iter()
                .filter(|(_, node)| {
                    matches!(&node.data, NodeData::Identifier(identifier) if identifier.text == "await")
                })
                .count()
                >= 3
        );
    }

    #[test]
    fn parses_async_arrow_parameters_in_await_context() {
        let result = parse_source_file("const fn = async (value = await) => {};");
        let arrow = result
            .arena
            .iter()
            .find_map(|(_, node)| match &node.data {
                NodeData::ArrowFunction(arrow) => Some(arrow),
                _ => None,
            })
            .unwrap();
        let NodeData::ParameterDeclaration(parameter) =
            &result.arena.get(arrow.parameters.nodes[0]).unwrap().data
        else {
            unreachable!();
        };
        assert!(matches!(
            parameter
                .initializer
                .and_then(|initializer| result.arena.get(initializer))
                .map(|node| &node.data),
            Some(NodeData::AwaitExpression(_))
        ));
    }

    #[test]
    fn parses_parenthesized_async_iife_variable_initializer() {
        let result = parse_source_file(
            "const test: Promise<[one: number, two: string]> = (async () => { return [1, 'two']; })();",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statement = source_statements(&result)[0];
        let (list, _) = variable_list(&result, statement);
        let declaration = declaration_nodes(&result, list)[0];
        let NodeData::VariableDeclaration(declaration) =
            &result.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let initializer = declaration.initializer.expect("initializer");
        assert!(matches!(
            result.arena.get(initializer).map(|node| &node.data),
            Some(NodeData::CallExpression(_))
        ));
    }

    #[test]
    fn parses_parenthesized_comma_expression_before_ternary_colon() {
        let result = parse_source_file("const result = flag ? (assert(value), value) : null;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert!(
            result
                .arena
                .iter()
                .any(|(_, node)| matches!(node.data, NodeData::ConditionalExpression(_)))
        );
        assert!(result.arena.iter().any(|(_, node)| {
            let NodeData::BinaryExpression(binary) = &node.data else {
                return false;
            };
            result
                .arena
                .get(binary.operator_token)
                .is_some_and(|token| token.kind == SyntaxKind::CommaToken)
        }));
        assert!(
            !result
                .arena
                .iter()
                .any(|(_, node)| matches!(node.data, NodeData::ArrowFunction(_)))
        );
    }

    #[test]
    fn attaches_decorators_to_class_members_and_parameters() {
        let result = parse_source_file(
            "class C { @field value: string; @method run(@parameter input: number) {} }",
        );
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let class = result
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::ClassDeclaration(class) = &node.data else {
                    return None;
                };
                Some(class)
            })
            .unwrap();
        assert!(class.members.nodes.iter().all(|member| {
            result
                .arena
                .get(*member)
                .and_then(|member| match &member.data {
                    NodeData::PropertyDeclaration(data) => data.modifiers.as_ref(),
                    NodeData::MethodDeclaration(data) => data.modifiers.as_ref(),
                    _ => None,
                })
                .is_some_and(|modifiers| {
                    modifiers.list.nodes.iter().any(|modifier| {
                        result
                            .arena
                            .get(*modifier)
                            .is_some_and(|modifier| modifier.kind == SyntaxKind::Decorator)
                    })
                })
        }));
        let parameter = result
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::ParameterDeclaration(parameter) = &node.data else {
                    return None;
                };
                Some(parameter)
            })
            .unwrap();
        assert!(parameter.modifiers.as_ref().is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|modifier| {
                result
                    .arena
                    .get(*modifier)
                    .is_some_and(|modifier| modifier.kind == SyntaxKind::Decorator)
            })
        }));
    }

    #[test]
    fn recovers_parameter_decorators_after_accessibility_names() {
        let result = parse_source_file("class C { constructor(public @dec value: number) {} }");
        assert!(!result.diagnostics.is_empty());
        let parameters = result
            .arena
            .iter()
            .filter_map(|(_, node)| {
                let NodeData::ParameterDeclaration(parameter) = &node.data else {
                    return None;
                };
                Some(parameter)
            })
            .collect::<Vec<_>>();
        assert_eq!(parameters.len(), 2);
        assert!(parameters[1].modifiers.as_ref().is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|modifier| {
                result
                    .arena
                    .get(*modifier)
                    .is_some_and(|modifier| modifier.kind == SyntaxKind::Decorator)
            })
        }));
    }

    #[test]
    fn stops_decorator_expression_before_computed_class_member_name() {
        let result =
            parse_source_file("class C { @dec [key]: any; @dec(value[key]) [other]: any; }");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let class = result
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::ClassDeclaration(class) = &node.data else {
                    return None;
                };
                Some(class)
            })
            .unwrap();
        assert_eq!(class.members.nodes.len(), 2);

        for member in &class.members.nodes {
            let NodeData::PropertyDeclaration(property) = &result.arena.get(*member).unwrap().data
            else {
                panic!("expected property declaration");
            };
            assert_eq!(
                result.arena.get(property.name).unwrap().kind,
                SyntaxKind::ComputedPropertyName
            );
        }

        let NodeData::PropertyDeclaration(first_property) =
            &result.arena.get(class.members.nodes[0]).unwrap().data
        else {
            unreachable!();
        };
        let first_decorator = first_property.modifiers.as_ref().unwrap().list.nodes[0];
        let NodeData::Decorator(first_decorator) = &result.arena.get(first_decorator).unwrap().data
        else {
            panic!("expected decorator");
        };
        assert_eq!(
            result.arena.get(first_decorator.expression).unwrap().kind,
            SyntaxKind::Identifier
        );

        let NodeData::PropertyDeclaration(second_property) =
            &result.arena.get(class.members.nodes[1]).unwrap().data
        else {
            unreachable!();
        };
        let second_decorator = second_property.modifiers.as_ref().unwrap().list.nodes[0];
        let NodeData::Decorator(second_decorator) =
            &result.arena.get(second_decorator).unwrap().data
        else {
            panic!("expected decorator");
        };
        let NodeData::CallExpression(call) =
            &result.arena.get(second_decorator.expression).unwrap().data
        else {
            panic!("expected decorator call");
        };
        assert_eq!(
            result.arena.get(call.arguments.nodes[0]).unwrap().kind,
            SyntaxKind::ElementAccessExpression
        );
    }

    #[test]
    fn recovers_invalid_member_modifiers_and_misspelled_new_meta_property() {
        let result = parse_source_file(concat!(
            "const value = { public field: 1 }; ",
            "interface Shape { public [key: string]: number; } ",
            "function f() { new.targ; }",
        ));
        let object = find_descendant_kind(
            &result,
            result.source_file,
            SyntaxKind::ObjectLiteralExpression,
        )
        .expect("object literal");
        let NodeData::ObjectLiteralExpression(object) = &result.arena.get(object).unwrap().data
        else {
            panic!("expected object literal");
        };
        let NodeData::PropertyAssignment(property) =
            &result.arena.get(object.properties.nodes[0]).unwrap().data
        else {
            panic!("expected property assignment");
        };
        assert_eq!(property.modifiers.as_ref().unwrap().list.nodes.len(), 1);

        let index = find_descendant_kind(&result, result.source_file, SyntaxKind::IndexSignature)
            .expect("index signature");
        let NodeData::IndexSignatureDeclaration(index) = &result.arena.get(index).unwrap().data
        else {
            panic!("expected index signature");
        };
        assert_eq!(index.modifiers.as_ref().unwrap().list.nodes.len(), 1);

        let meta = find_descendant_kind(&result, result.source_file, SyntaxKind::MetaProperty)
            .expect("meta property");
        let NodeData::MetaProperty(meta) = &result.arena.get(meta).unwrap().data else {
            panic!("expected meta property");
        };
        assert_eq!(meta.keyword_token, SyntaxKind::NewKeyword);
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Some(17012))
        );
    }

    #[test]
    fn object_literal_property_type_slots_are_nil_and_children_are_unique() {
        let result =
            parse_source_file("const shorthand = 2; const value = { property: 1, shorthand };");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let object = find_descendant_kind(
            &result,
            result.source_file,
            SyntaxKind::ObjectLiteralExpression,
        )
        .expect("object literal");
        let NodeData::ObjectLiteralExpression(object) = &result.arena.get(object).unwrap().data
        else {
            panic!("expected object literal");
        };
        assert_eq!(object.properties.nodes.len(), 2);

        let property_id = object.properties.nodes[0];
        let NodeData::PropertyAssignment(property) = &result.arena.get(property_id).unwrap().data
        else {
            panic!("expected property assignment");
        };
        assert_eq!(property.type_, None);
        let mut property_children = Vec::new();
        result
            .arena
            .get(property_id)
            .unwrap()
            .for_each_child(|child| property_children.push(child));
        assert_eq!(property_children, [property.name, property.initializer]);
        assert_eq!(
            result.arena.get(property.initializer).unwrap().parent,
            Some(property_id)
        );

        let shorthand_id = object.properties.nodes[1];
        let NodeData::ShorthandPropertyAssignment(shorthand) =
            &result.arena.get(shorthand_id).unwrap().data
        else {
            panic!("expected shorthand property assignment");
        };
        assert_eq!(shorthand.type_, None);
        let mut shorthand_children = Vec::new();
        result
            .arena
            .get(shorthand_id)
            .unwrap()
            .for_each_child(|child| shorthand_children.push(child));
        assert_eq!(shorthand_children, [shorthand.name]);
        assert_eq!(
            result.arena.get(shorthand.name).unwrap().parent,
            Some(shorthand_id)
        );
    }

    #[test]
    fn parses_import_meta_without_reclassifying_longer_properties() {
        let result = parse_source_file(
            "const meta = import.meta; import.meta = meta; const longer = import.metal;",
        );
        let import_meta = result
            .arena
            .iter()
            .filter(|(_, node)| {
                matches!(
                    &node.data,
                    NodeData::MetaProperty(meta)
                        if meta.keyword_token == SyntaxKind::ImportKeyword
                )
            })
            .count();
        assert_eq!(import_meta, 2);
        assert!(result.arena.iter().any(|(_, node)| {
            let NodeData::PropertyAccessExpression(access) = &node.data else {
                return false;
            };
            matches!(
                result.arena.get(access.name).map(|node| &node.data),
                Some(NodeData::Identifier(identifier)) if identifier.text == "metal"
            )
        }));
    }

    #[test]
    fn recovers_object_literal_index_signature_as_two_properties() {
        let result = parse_source_file("const value = { private [x: string]: string; };");
        let object = find_descendant_kind(
            &result,
            result.source_file,
            SyntaxKind::ObjectLiteralExpression,
        )
        .expect("object literal");
        let NodeData::ObjectLiteralExpression(object) = &result.arena.get(object).unwrap().data
        else {
            panic!("expected object literal");
        };
        assert_eq!(object.properties.nodes.len(), 2);
        assert!(matches!(
            result
                .arena
                .get(object.properties.nodes[0])
                .map(|node| &node.data),
            Some(NodeData::PropertyAssignment(_))
        ));
        let Some(NodeData::ShorthandPropertyAssignment(property)) = result
            .arena
            .get(object.properties.nodes[1])
            .map(|node| &node.data)
        else {
            panic!("expected recovered shorthand property");
        };
        assert!(matches!(
            result.arena.get(property.name).map(|node| &node.data),
            Some(NodeData::Identifier(identifier)) if identifier.text == "string"
        ));
    }

    #[test]
    fn recovers_identifier_after_trailing_decimal_as_variable_declarator() {
        let result = parse_source_file("var test2 = 2.toString();");
        let NodeData::SourceFile(source) = &result.arena.get(result.source_file).unwrap().data
        else {
            panic!("expected source file");
        };
        let NodeData::VariableStatement(statement) =
            &result.arena.get(source.statements.nodes[0]).unwrap().data
        else {
            panic!("expected variable statement");
        };
        let NodeData::VariableDeclarationList(list) =
            &result.arena.get(statement.declaration_list).unwrap().data
        else {
            panic!("expected variable declaration list");
        };
        assert_eq!(list.declarations.nodes.len(), 2);
        let NodeData::VariableDeclaration(second) =
            &result.arena.get(list.declarations.nodes[1]).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        assert!(matches!(
            &result.arena.get(second.name).unwrap().data,
            NodeData::Identifier(identifier) if identifier.text == "toString"
        ));

        let asi = parse_source_file("var value = other\nnext();");
        let NodeData::SourceFile(source) = &asi.arena.get(asi.source_file).unwrap().data else {
            panic!("expected source file");
        };
        assert_eq!(source.statements.nodes.len(), 2);
        let NodeData::VariableStatement(statement) =
            &asi.arena.get(source.statements.nodes[0]).unwrap().data
        else {
            panic!("expected variable statement");
        };
        let NodeData::VariableDeclarationList(list) =
            &asi.arena.get(statement.declaration_list).unwrap().data
        else {
            panic!("expected variable declaration list");
        };
        assert_eq!(list.declarations.nodes.len(), 1);
    }

    #[test]
    fn recovers_reserved_words_as_declaration_names() {
        let result = parse_source_file("let let = 1; interface implements {} enum package {}");
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 3, "{:?}", result.diagnostics);

        let (list, _) = variable_list(&result, statements[0]);
        let NodeData::VariableDeclaration(variable) = &result
            .arena
            .get(declaration_nodes(&result, list)[0])
            .unwrap()
            .data
        else {
            panic!("expected variable declaration");
        };
        assert!(matches!(
            &result.arena.get(variable.name).unwrap().data,
            NodeData::Identifier(identifier) if identifier.text == "let"
        ));
        assert!(matches!(
            &result.arena.get(statements[1]).unwrap().data,
            NodeData::InterfaceDeclaration(interface)
                if matches!(
                    &result.arena.get(interface.name).unwrap().data,
                    NodeData::Identifier(identifier) if identifier.text == "implements"
                )
        ));
        assert!(matches!(
            &result.arena.get(statements[2]).unwrap().data,
            NodeData::EnumDeclaration(enum_)
                if matches!(
                    &result.arena.get(enum_.name).unwrap().data,
                    NodeData::Identifier(identifier) if identifier.text == "package"
                )
        ));
    }

    #[test]
    fn recovers_reserved_words_in_imports_and_heritage_names() {
        let result = parse_source_file(
            r#"
                import public = require("1");
                import * as package from "./1";
                import { foo as private } from "./1";
                import public from "./1";
                class F implements public.private.implements {}
            "#,
        );
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 5, "{:?}", result.diagnostics);
        assert_eq!(
            result.arena.get(statements[0]).unwrap().kind,
            SyntaxKind::ImportEqualsDeclaration
        );
        for statement in &statements[1..4] {
            assert_eq!(
                result.arena.get(*statement).unwrap().kind,
                SyntaxKind::ImportDeclaration
            );
        }

        let NodeData::ClassDeclaration(class) = &result.arena.get(statements[4]).unwrap().data
        else {
            panic!("expected class declaration");
        };
        let clause = class.heritage_clauses.as_ref().unwrap().nodes[0];
        let NodeData::HeritageClause(clause) = &result.arena.get(clause).unwrap().data else {
            panic!("expected heritage clause");
        };
        let NodeData::ExpressionWithTypeArguments(heritage) =
            &result.arena.get(clause.types.nodes[0]).unwrap().data
        else {
            panic!("expected heritage expression");
        };
        assert_eq!(
            result.arena.get(heritage.expression).unwrap().kind,
            SyntaxKind::QualifiedName
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
