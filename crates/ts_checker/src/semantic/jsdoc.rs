//! Parsed `JSDoc` types for the canonical JavaScript checker.
//!
//! The source parser does not yet attach structured `JSDoc` nodes to source
//! declarations. This module uses its standalone comment scanner to identify
//! tags, then parses each type with the ordinary TypeScript type parser. The
//! resulting values never contain node identities from that temporary arena.

use std::fmt;

use ts_ast::{NodeArena, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_core::{Diagnostic, DiagnosticCategory, TextPos, TextRange};
use ts_diagnostics::{Category, message_by_code};
use ts_parser::{parse_jsdoc_comment, parse_source_file};

use super::{
    ArrayTypeError, CanonicalCheckerOptions, CanonicalGlobalTypes, CanonicalTypeMapperStore,
    IntrinsicBootstrapOptions, TypeId, bootstrap::UnionReduction,
};

const TYPE_PREFIX: &str = "type __JsDoc = ";

/// A `JSDoc` tag that can contribute a declaration or signature type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum JsDocTagKind {
    Type,
    Parameter,
    Return,
    Typedef,
}

/// Intrinsic types accepted by the pinned `JSDoc` type grammar.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum JsDocIntrinsicType {
    Any,
    Unknown,
    Never,
    Void,
    Undefined,
    Null,
    Boolean,
    True,
    False,
    Number,
    String,
    BigInt,
    Symbol,
    Object,
}

/// A parsed `JSDoc` type without identities from its temporary parser arena.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum JsDocType {
    Intrinsic(JsDocIntrinsicType),
    Named(String),
    Parenthesized(Box<Self>),
    Nullable(Box<Self>),
    NonNullable(Box<Self>),
    Optional(Box<Self>),
    Variadic(Box<Self>),
    Array(Box<Self>),
    Union(Vec<Self>),
    Unsupported(SyntaxKind),
}

/// The original source text and exact UTF-8 range of one parsed type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsDocTypeExpression<'source> {
    text: &'source str,
    range: TextRange,
    type_: JsDocType,
}

impl<'source> JsDocTypeExpression<'source> {
    #[must_use]
    pub const fn text(&self) -> &'source str {
        self.text
    }

    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }

    #[must_use]
    pub const fn type_(&self) -> &JsDocType {
        &self.type_
    }
}

/// The parameter or typedef name carried by one `JSDoc` tag.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct JsDocTagName<'source> {
    text: &'source str,
    range: TextRange,
}

impl<'source> JsDocTagName<'source> {
    #[must_use]
    pub const fn text(self) -> &'source str {
        self.text
    }

    #[must_use]
    pub const fn range(self) -> TextRange {
        self.range
    }
}

/// One supported `JSDoc` tag and its exact source-owned arguments.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsDocTag<'source> {
    kind: JsDocTagKind,
    range: TextRange,
    name: Option<JsDocTagName<'source>>,
    type_expression: Option<JsDocTypeExpression<'source>>,
    name_first: bool,
    optional: bool,
}

impl<'source> JsDocTag<'source> {
    #[must_use]
    pub const fn kind(&self) -> JsDocTagKind {
        self.kind
    }

    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }

    #[must_use]
    pub const fn name(&self) -> Option<JsDocTagName<'source>> {
        self.name
    }

    #[must_use]
    pub const fn type_expression(&self) -> Option<&JsDocTypeExpression<'source>> {
        self.type_expression.as_ref()
    }

    #[must_use]
    pub const fn is_name_first(&self) -> bool {
        self.name_first
    }

    #[must_use]
    pub const fn is_optional(&self) -> bool {
        self.optional
    }
}

/// Supported tags and parser diagnostics for one source-owned `JSDoc` comment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParsedJsDocComment<'source> {
    range: TextRange,
    tags: Vec<JsDocTag<'source>>,
    diagnostics: Vec<Diagnostic>,
}

impl<'source> ParsedJsDocComment<'source> {
    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }

    #[must_use]
    pub fn tags(&self) -> &[JsDocTag<'source>] {
        &self.tags
    }

    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    #[must_use]
    pub fn type_tag(&self) -> Option<&JsDocTag<'source>> {
        self.tags.iter().find(|tag| tag.kind == JsDocTagKind::Type)
    }

    #[must_use]
    pub fn return_tag(&self) -> Option<&JsDocTag<'source>> {
        self.tags
            .iter()
            .find(|tag| tag.kind == JsDocTagKind::Return)
    }

    #[must_use]
    pub fn parameter_tag(&self, name: &str) -> Option<&JsDocTag<'source>> {
        self.tags.iter().find(|tag| {
            tag.kind == JsDocTagKind::Parameter
                && tag.name.is_some_and(|parameter| parameter.text == name)
        })
    }
}

/// Invalid source provenance or an inconsistent standalone `JSDoc` parse.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum JsDocCommentError {
    InvalidCommentRange(TextRange),
    InvalidCommentSyntax(TextRange),
    InvalidParserTree(TextRange),
    InvalidSourceNode(NodeRef),
    MissingSourceText(NodeRef),
    SourcePositionOverflow,
}

impl fmt::Display for JsDocCommentError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCommentRange(range) => {
                write!(
                    formatter,
                    "JSDoc comment range {range:?} is outside its source"
                )
            }
            Self::InvalidCommentSyntax(range) => {
                write!(
                    formatter,
                    "range {range:?} does not contain a JSDoc comment"
                )
            }
            Self::InvalidParserTree(range) => {
                write!(
                    formatter,
                    "JSDoc parser returned an invalid tree for {range:?}"
                )
            }
            Self::InvalidSourceNode(node) => {
                write!(
                    formatter,
                    "JSDoc comment received an invalid source node {node:?}"
                )
            }
            Self::MissingSourceText(node) => {
                write!(
                    formatter,
                    "JSDoc comment source text is unavailable for {node:?}"
                )
            }
            Self::SourcePositionOverflow => {
                formatter.write_str("JSDoc comment position exceeds the source range")
            }
        }
    }
}

impl std::error::Error for JsDocCommentError {}

/// A `JSDoc` type that needs an unavailable checker capability or invalid state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum JsDocTypeResolutionError {
    MissingBootstrap,
    OptionsMismatch {
        initialized: IntrinsicBootstrapOptions,
        requested: IntrinsicBootstrapOptions,
    },
    UnresolvedTypeReference {
        name: String,
        range: TextRange,
    },
    UnsupportedType {
        kind: SyntaxKind,
        range: TextRange,
    },
    InvalidGlobalType(TypeId),
    UnionConstruction(TextRange),
    ArrayConstruction {
        range: TextRange,
        error: ArrayTypeError,
    },
}

impl fmt::Display for JsDocTypeResolutionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingBootstrap => {
                formatter.write_str("JSDoc type requires intrinsic bootstrap")
            }
            Self::OptionsMismatch { .. } => {
                formatter.write_str("JSDoc type options do not match intrinsic bootstrap")
            }
            Self::UnresolvedTypeReference { name, .. } => {
                write!(
                    formatter,
                    "JSDoc type reference '{name}' cannot be resolved"
                )
            }
            Self::UnsupportedType { kind, .. } => {
                write!(formatter, "JSDoc type syntax {kind:?} is not supported")
            }
            Self::InvalidGlobalType(type_) => {
                write!(
                    formatter,
                    "JSDoc type references invalid global type {type_:?}"
                )
            }
            Self::UnionConstruction(range) => {
                write!(
                    formatter,
                    "JSDoc union type could not be created at {range:?}"
                )
            }
            Self::ArrayConstruction { error, .. } => error.fmt(formatter),
        }
    }
}

impl std::error::Error for JsDocTypeResolutionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::ArrayConstruction { error, .. } => Some(error),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct ScannedTag<'source> {
    name: &'source str,
    start: usize,
    body_start: usize,
}

/// Parses a complete `/** ... */` comment at its exact source-owned range.
///
/// # Errors
///
/// Returns an error for invalid source ranges or an inconsistent parser tree.
/// Ordinary malformed `JSDoc` types remain source-positioned parser diagnostics.
pub fn parse_jsdoc_comment_at(
    source: &str,
    range: TextRange,
) -> Result<ParsedJsDocComment<'_>, JsDocCommentError> {
    let start = usize::try_from(range.start.get())
        .map_err(|_| JsDocCommentError::InvalidCommentRange(range))?;
    let end = usize::try_from(range.end.get())
        .map_err(|_| JsDocCommentError::InvalidCommentRange(range))?;
    let comment = source
        .get(start..end)
        .ok_or(JsDocCommentError::InvalidCommentRange(range))?;
    if !comment.starts_with("/**") || !comment.ends_with("*/") {
        return Err(JsDocCommentError::InvalidCommentSyntax(range));
    }

    let parsed = parse_jsdoc_comment(comment);
    let NodeData::JsDoc(root) = &parsed
        .arena
        .get(parsed.jsdoc)
        .ok_or(JsDocCommentError::InvalidParserTree(range))?
        .data
    else {
        return Err(JsDocCommentError::InvalidParserTree(range));
    };
    let mut scanned = Vec::new();
    if let Some(tags) = &root.tags {
        for tag_id in &tags.nodes {
            let tag = parsed
                .arena
                .get(*tag_id)
                .ok_or(JsDocCommentError::InvalidParserTree(range))?;
            let NodeData::JsDocUnknownTag(data) = &tag.data else {
                return Err(JsDocCommentError::InvalidParserTree(range));
            };
            let name = parsed
                .arena
                .get(data.tag_name)
                .ok_or(JsDocCommentError::InvalidParserTree(range))?;
            let NodeData::Identifier(identifier) = &name.data else {
                return Err(JsDocCommentError::InvalidParserTree(range));
            };
            let tag_start = usize::try_from(tag.range.start.get())
                .map_err(|_| JsDocCommentError::InvalidParserTree(range))?;
            let body_start = usize::try_from(name.range.end.get())
                .map_err(|_| JsDocCommentError::InvalidParserTree(range))?;
            if tag_start >= body_start || body_start > comment.len() {
                return Err(JsDocCommentError::InvalidParserTree(range));
            }
            if is_top_level_tag(comment, tag_start) {
                let name = comment
                    .get(tag_start + 1..body_start)
                    .filter(|name| *name == identifier.text)
                    .ok_or(JsDocCommentError::InvalidParserTree(range))?;
                scanned.push(ScannedTag {
                    name,
                    start: tag_start,
                    body_start,
                });
            }
        }
    }
    recover_keyword_tags(comment, &mut scanned);
    scanned.sort_unstable_by_key(|tag| tag.start);

    let mut diagnostics = parsed
        .diagnostics
        .into_iter()
        .map(|diagnostic| relocate_comment_diagnostic(diagnostic, start))
        .collect::<Result<Vec<_>, _>>()?;
    let mut tags = Vec::new();
    let comment_end = comment.len() - 2;
    for (index, tag) in scanned.iter().enumerate() {
        let Some(kind) = tag_kind(tag.name) else {
            continue;
        };
        let tag_end = scanned
            .get(index + 1)
            .map_or(comment_end, |next| next.start);
        tags.push(parse_supported_tag(
            source,
            start,
            *tag,
            tag_end,
            kind,
            &mut diagnostics,
        )?);
    }

    Ok(ParsedJsDocComment {
        range,
        tags,
        diagnostics,
    })
}

/// Finds and parses the immediately preceding `JSDoc` comment for a source node.
///
/// # Errors
///
/// Returns an error when the node does not belong to `arena`, its source text
/// is unavailable, or the comment parser returns inconsistent source ranges.
pub fn leading_jsdoc_comment(
    arena: &NodeArena,
    node: NodeRef,
) -> Result<Option<ParsedJsDocComment<'_>>, JsDocCommentError> {
    if node.arena != arena.id() {
        return Err(JsDocCommentError::InvalidSourceNode(node));
    }
    let record = arena
        .get(node.node)
        .ok_or(JsDocCommentError::InvalidSourceNode(node))?;
    let source = arena
        .source_text()
        .ok_or(JsDocCommentError::MissingSourceText(node))?;
    let node_start = usize::try_from(record.range.start.get())
        .map_err(|_| JsDocCommentError::InvalidSourceNode(node))?;
    let prefix = source
        .get(..node_start)
        .ok_or(JsDocCommentError::InvalidSourceNode(node))?
        .trim_end_matches(char::is_whitespace);
    if !prefix.ends_with("*/") {
        return Ok(None);
    }
    let Some(comment_start) = prefix.rfind("/**") else {
        return Ok(None);
    };
    let range = checked_range(comment_start, prefix.len())?;
    parse_jsdoc_comment_at(source, range).map(Some)
}

/// Resolves a primitive `JSDoc` annotation without mutating the checker store.
///
/// # Errors
///
/// Returns an error when the type requires name resolution, allocation, a
/// missing intrinsic bootstrap, or different compiler options.
pub fn resolve_intrinsic_jsdoc_type(
    store: &CanonicalTypeMapperStore,
    options: CanonicalCheckerOptions,
    annotation: &JsDocTypeExpression<'_>,
) -> Result<TypeId, JsDocTypeResolutionError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(JsDocTypeResolutionError::MissingBootstrap)?;
    if bootstrap.options != options.intrinsic {
        return Err(JsDocTypeResolutionError::OptionsMismatch {
            initialized: bootstrap.options,
            requested: options.intrinsic,
        });
    }
    resolve_intrinsic_type(store, options, annotation.type_(), annotation.range())
}

/// Resolves the complete installed `JSDoc` type subset in a canonical store.
///
/// The complete type is validated before the first union or array allocation.
/// Unknown references and unsupported syntax therefore cannot leave new
/// checker-owned records behind.
///
/// # Errors
///
/// Returns an error for unsupported type syntax, invalid global identities,
/// inconsistent compiler options, or failed canonical union/array allocation.
pub fn resolve_jsdoc_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    annotation: &JsDocTypeExpression<'_>,
) -> Result<TypeId, JsDocTypeResolutionError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(JsDocTypeResolutionError::MissingBootstrap)?;
    if bootstrap.options != options.intrinsic {
        return Err(JsDocTypeResolutionError::OptionsMismatch {
            initialized: bootstrap.options,
            requested: options.intrinsic,
        });
    }
    validate_resolvable_type(
        store,
        global_types,
        options,
        annotation.type_(),
        annotation.range(),
    )?;
    resolve_complete_type(
        store,
        global_types,
        options,
        annotation.type_(),
        annotation.range(),
    )
}

fn tag_kind(name: &str) -> Option<JsDocTagKind> {
    match name {
        "type" => Some(JsDocTagKind::Type),
        "param" | "arg" | "argument" => Some(JsDocTagKind::Parameter),
        "return" | "returns" => Some(JsDocTagKind::Return),
        "typedef" => Some(JsDocTagKind::Typedef),
        _ => None,
    }
}

fn recover_keyword_tags<'source>(comment: &'source str, tags: &mut Vec<ScannedTag<'source>>) {
    for (start, _) in comment.match_indices('@') {
        if start < 3
            || start + 1 >= comment.len().saturating_sub(2)
            || comment
                .get(..start)
                .and_then(|prefix| prefix.chars().next_back())
                .is_none_or(|character| !character.is_whitespace())
            || !is_top_level_tag(comment, start)
        {
            continue;
        }
        let rest = &comment[start + 1..];
        let name_length = rest
            .char_indices()
            .find_map(|(index, character)| {
                (!character.is_alphanumeric() && !matches!(character, '_' | '$' | '-'))
                    .then_some(index)
            })
            .unwrap_or(rest.len());
        let Some(name) = rest.get(..name_length) else {
            continue;
        };
        if !matches!(name, "type" | "return") || tags.iter().any(|existing| existing.start == start)
        {
            continue;
        }
        tags.push(ScannedTag {
            name,
            start,
            body_start: start + 1 + name_length,
        });
    }
}

fn is_top_level_tag(comment: &str, position: usize) -> bool {
    let mut depth = 0usize;
    let mut quote = None;
    let mut escaped = false;
    for byte in comment.as_bytes().get(3..position).unwrap_or_default() {
        if let Some(current) = quote {
            if escaped {
                escaped = false;
            } else if *byte == b'\\' {
                escaped = true;
            } else if *byte == current {
                quote = None;
            }
            continue;
        }
        match *byte {
            b'\'' | b'"' | b'`' if depth > 0 => quote = Some(*byte),
            b'{' => depth = depth.saturating_add(1),
            b'}' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    depth == 0
}

fn parse_supported_tag<'source>(
    source: &'source str,
    comment_start: usize,
    tag: ScannedTag<'_>,
    tag_end: usize,
    kind: JsDocTagKind,
    diagnostics: &mut Vec<Diagnostic>,
) -> Result<JsDocTag<'source>, JsDocCommentError> {
    let absolute_start = comment_start
        .checked_add(tag.start)
        .ok_or(JsDocCommentError::SourcePositionOverflow)?;
    let absolute_end = comment_start
        .checked_add(tag_end)
        .ok_or(JsDocCommentError::SourcePositionOverflow)?;
    let body_start = comment_start
        .checked_add(tag.body_start)
        .ok_or(JsDocCommentError::SourcePositionOverflow)?;
    let mut cursor = skip_doc_whitespace(source, body_start, absolute_end);
    let mut type_expression = None;
    let mut name = None;
    let mut name_first = false;
    let mut bracketed = false;

    if source.as_bytes().get(cursor) == Some(&b'{') {
        let (parsed, next) = parse_braced_type(source, cursor, absolute_end, diagnostics)?;
        type_expression = parsed;
        cursor = skip_doc_whitespace(source, next, absolute_end);
    } else if matches!(kind, JsDocTagKind::Parameter | JsDocTagKind::Typedef) {
        name_first = kind == JsDocTagKind::Parameter;
    } else if cursor < absolute_end {
        let type_end = unbraced_type_end(source, cursor, absolute_end);
        type_expression = parse_type_expression(source, cursor, type_end, diagnostics)?;
        cursor = skip_doc_whitespace(source, type_end, absolute_end);
    } else if kind == JsDocTagKind::Type {
        diagnostics.push(type_expected_diagnostic(source, cursor, absolute_end)?);
    }

    if matches!(kind, JsDocTagKind::Parameter | JsDocTagKind::Typedef) {
        let (parsed_name, next, optional) = parse_tag_name(source, cursor, absolute_end)?;
        name = parsed_name;
        bracketed = optional;
        cursor = skip_doc_whitespace(source, next, absolute_end);
        if name_first && source.as_bytes().get(cursor) == Some(&b'{') {
            let (parsed, _) = parse_braced_type(source, cursor, absolute_end, diagnostics)?;
            type_expression = parsed;
        }
    }

    let optional = bracketed
        || type_expression
            .as_ref()
            .is_some_and(|expression| matches!(expression.type_, JsDocType::Optional(_)));
    Ok(JsDocTag {
        kind,
        range: checked_range(absolute_start, absolute_end)?,
        name,
        type_expression,
        name_first,
        optional,
    })
}

fn parse_braced_type<'source>(
    source: &'source str,
    open: usize,
    end: usize,
    diagnostics: &mut Vec<Diagnostic>,
) -> Result<(Option<JsDocTypeExpression<'source>>, usize), JsDocCommentError> {
    let Some(close) = matching_brace(source, open, end) else {
        diagnostics.push(expected_token_diagnostic(source, end, end, "}")?);
        return Ok((None, end));
    };
    let (start, type_end) = trimmed_range(source, open + 1, close);
    if start == type_end {
        diagnostics.push(type_expected_diagnostic(source, close, end)?);
        return Ok((None, close + 1));
    }
    let expression = parse_type_expression(source, start, type_end, diagnostics)?;
    Ok((expression, close + 1))
}

fn matching_brace(source: &str, open: usize, end: usize) -> Option<usize> {
    let bytes = source.as_bytes();
    let mut depth = 0usize;
    let mut quote = None;
    let mut escaped = false;
    for (offset, byte) in bytes.get(open..end)?.iter().enumerate() {
        if let Some(current) = quote {
            if escaped {
                escaped = false;
            } else if *byte == b'\\' {
                escaped = true;
            } else if *byte == current {
                quote = None;
            }
            continue;
        }
        match *byte {
            b'\'' | b'"' | b'`' => quote = Some(*byte),
            b'{' => depth = depth.checked_add(1)?,
            b'}' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(open + offset);
                }
            }
            _ => {}
        }
    }
    None
}

fn parse_tag_name(
    source: &str,
    start: usize,
    end: usize,
) -> Result<(Option<JsDocTagName<'_>>, usize, bool), JsDocCommentError> {
    if start >= end {
        return Ok((None, start, false));
    }
    let bytes = source.as_bytes();
    let bracketed = bytes.get(start) == Some(&b'[');
    let name_start = if bracketed {
        skip_doc_whitespace(source, start + 1, end)
    } else {
        start
    };
    let mut name_end = name_start;
    while name_end < end
        && !bytes[name_end].is_ascii_whitespace()
        && !matches!(bytes[name_end], b'=' | b']' | b'{')
    {
        name_end += 1;
    }
    let name = if name_end == name_start {
        None
    } else {
        Some(JsDocTagName {
            text: source
                .get(name_start..name_end)
                .ok_or(JsDocCommentError::SourcePositionOverflow)?,
            range: checked_range(name_start, name_end)?,
        })
    };
    let next = if bracketed {
        source
            .get(name_end..end)
            .and_then(|remaining| remaining.find(']'))
            .map_or(name_end, |offset| name_end + offset + 1)
    } else {
        name_end
    };
    Ok((name, next, bracketed))
}

fn parse_type_expression<'source>(
    source: &'source str,
    start: usize,
    end: usize,
    diagnostics: &mut Vec<Diagnostic>,
) -> Result<Option<JsDocTypeExpression<'source>>, JsDocCommentError> {
    let range = checked_range(start, end)?;
    let text = source
        .get(start..end)
        .ok_or(JsDocCommentError::SourcePositionOverflow)?;
    let mut normalized = normalize_type_text(text);
    let variadic = normalized.starts_with("...");
    if variadic {
        normalized.replace_range(..3, "   ");
    }
    let trimmed_end = normalized.trim_end().len();
    let optional = normalized.as_bytes().get(trimmed_end.saturating_sub(1)) == Some(&b'=');
    if optional {
        let equals = trimmed_end - 1;
        normalized.replace_range(equals..=equals, " ");
    }
    let synthetic = format!("{TYPE_PREFIX}{normalized};");
    let parsed = parse_source_file(&synthetic);
    if let Some(diagnostic) = parsed.diagnostics.into_iter().next() {
        diagnostics.push(relocate_type_diagnostic(diagnostic, start, end)?);
        return Ok(None);
    }
    let NodeData::SourceFile(file) = &parsed
        .arena
        .get(parsed.source_file)
        .ok_or(JsDocCommentError::InvalidParserTree(range))?
        .data
    else {
        return Err(JsDocCommentError::InvalidParserTree(range));
    };
    let [declaration] = file.statements.nodes.as_slice() else {
        diagnostics.push(type_expected_diagnostic(source, start, end)?);
        return Ok(None);
    };
    let NodeData::TypeAliasDeclaration(alias) = &parsed
        .arena
        .get(*declaration)
        .ok_or(JsDocCommentError::InvalidParserTree(range))?
        .data
    else {
        return Err(JsDocCommentError::InvalidParserTree(range));
    };
    let mut type_ = project_type(&parsed.arena, alias.type_, range)?;
    if variadic {
        type_ = JsDocType::Variadic(Box::new(type_));
    }
    if optional {
        type_ = JsDocType::Optional(Box::new(type_));
    }
    Ok(Some(JsDocTypeExpression { text, range, type_ }))
}

fn project_type(
    arena: &NodeArena,
    node: NodeId,
    range: TextRange,
) -> Result<JsDocType, JsDocCommentError> {
    let record = arena
        .get(node)
        .ok_or(JsDocCommentError::InvalidParserTree(range))?;
    let type_ = match &record.data {
        NodeData::KeywordTypeNode(_) => keyword_intrinsic(record.kind)
            .map(JsDocType::Intrinsic)
            .unwrap_or(JsDocType::Unsupported(record.kind)),
        NodeData::JsDocAllType(_) => JsDocType::Intrinsic(JsDocIntrinsicType::Any),
        NodeData::JsDocNullableType(data) => {
            JsDocType::Nullable(Box::new(project_type(arena, data.type_, range)?))
        }
        NodeData::JsDocNonNullableType(data) => {
            JsDocType::NonNullable(Box::new(project_type(arena, data.type_, range)?))
        }
        NodeData::ParenthesizedTypeNode(data) => {
            JsDocType::Parenthesized(Box::new(project_type(arena, data.type_, range)?))
        }
        NodeData::ArrayTypeNode(data) => {
            JsDocType::Array(Box::new(project_type(arena, data.element_type, range)?))
        }
        NodeData::UnionTypeNode(data) => JsDocType::Union(
            data.types
                .nodes
                .iter()
                .map(|type_| project_type(arena, *type_, range))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        NodeData::TypeReferenceNode(data) => {
            let Some(name) = arena.get(data.type_name) else {
                return Err(JsDocCommentError::InvalidParserTree(range));
            };
            match (&name.data, &data.type_arguments) {
                (NodeData::Identifier(name), None) => boxed_intrinsic(&name.text)
                    .map_or_else(|| JsDocType::Named(name.text.clone()), JsDocType::Intrinsic),
                _ => JsDocType::Unsupported(record.kind),
            }
        }
        NodeData::LiteralTypeNode(data) => {
            let Some(literal) = arena.get(data.literal) else {
                return Err(JsDocCommentError::InvalidParserTree(range));
            };
            match literal.kind {
                SyntaxKind::NullKeyword => JsDocType::Intrinsic(JsDocIntrinsicType::Null),
                SyntaxKind::TrueKeyword => JsDocType::Intrinsic(JsDocIntrinsicType::True),
                SyntaxKind::FalseKeyword => JsDocType::Intrinsic(JsDocIntrinsicType::False),
                _ => JsDocType::Unsupported(record.kind),
            }
        }
        _ => JsDocType::Unsupported(record.kind),
    };
    Ok(type_)
}

const fn keyword_intrinsic(kind: SyntaxKind) -> Option<JsDocIntrinsicType> {
    match kind {
        SyntaxKind::AnyKeyword => Some(JsDocIntrinsicType::Any),
        SyntaxKind::UnknownKeyword => Some(JsDocIntrinsicType::Unknown),
        SyntaxKind::NeverKeyword => Some(JsDocIntrinsicType::Never),
        SyntaxKind::VoidKeyword => Some(JsDocIntrinsicType::Void),
        SyntaxKind::UndefinedKeyword => Some(JsDocIntrinsicType::Undefined),
        SyntaxKind::BooleanKeyword => Some(JsDocIntrinsicType::Boolean),
        SyntaxKind::NumberKeyword => Some(JsDocIntrinsicType::Number),
        SyntaxKind::StringKeyword => Some(JsDocIntrinsicType::String),
        SyntaxKind::BigIntKeyword => Some(JsDocIntrinsicType::BigInt),
        SyntaxKind::SymbolKeyword => Some(JsDocIntrinsicType::Symbol),
        SyntaxKind::ObjectKeyword => Some(JsDocIntrinsicType::Object),
        _ => None,
    }
}

fn boxed_intrinsic(name: &str) -> Option<JsDocIntrinsicType> {
    match name {
        "String" => Some(JsDocIntrinsicType::String),
        "Number" => Some(JsDocIntrinsicType::Number),
        "BigInt" => Some(JsDocIntrinsicType::BigInt),
        "Boolean" => Some(JsDocIntrinsicType::Boolean),
        "Void" => Some(JsDocIntrinsicType::Void),
        "Undefined" => Some(JsDocIntrinsicType::Undefined),
        "Null" => Some(JsDocIntrinsicType::Null),
        _ => None,
    }
}

fn resolve_intrinsic_type(
    store: &CanonicalTypeMapperStore,
    options: CanonicalCheckerOptions,
    type_: &JsDocType,
    range: TextRange,
) -> Result<TypeId, JsDocTypeResolutionError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(JsDocTypeResolutionError::MissingBootstrap)?;
    match type_ {
        JsDocType::Intrinsic(intrinsic) => Ok(match intrinsic {
            JsDocIntrinsicType::Any => bootstrap.any_type,
            JsDocIntrinsicType::Unknown => bootstrap.unknown_type,
            JsDocIntrinsicType::Never => bootstrap.never_type,
            JsDocIntrinsicType::Void => bootstrap.void_type,
            JsDocIntrinsicType::Undefined => bootstrap.undefined_type,
            JsDocIntrinsicType::Null => bootstrap.null_type,
            JsDocIntrinsicType::Boolean => bootstrap.boolean_type,
            JsDocIntrinsicType::True => bootstrap.regular_true_type,
            JsDocIntrinsicType::False => bootstrap.regular_false_type,
            JsDocIntrinsicType::Number => bootstrap.number_type,
            JsDocIntrinsicType::String => bootstrap.string_type,
            JsDocIntrinsicType::BigInt => bootstrap.bigint_type,
            JsDocIntrinsicType::Symbol => bootstrap.es_symbol_type,
            JsDocIntrinsicType::Object => bootstrap.non_primitive_type,
        }),
        JsDocType::Named(name) if name == "Object" && !options.no_implicit_any => {
            Ok(bootstrap.any_type)
        }
        JsDocType::Named(name) => Err(JsDocTypeResolutionError::UnresolvedTypeReference {
            name: name.clone(),
            range,
        }),
        JsDocType::Parenthesized(inner) | JsDocType::NonNullable(inner) => {
            resolve_intrinsic_type(store, options, inner, range)
        }
        JsDocType::Nullable(inner) | JsDocType::Optional(inner)
            if !options.intrinsic.strict_null_checks =>
        {
            resolve_intrinsic_type(store, options, inner, range)
        }
        JsDocType::Nullable(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::JsDocNullableType,
            range,
        }),
        JsDocType::Optional(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::JsDocOptionalType,
            range,
        }),
        JsDocType::Variadic(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::JsDocVariadicType,
            range,
        }),
        JsDocType::Array(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::ArrayType,
            range,
        }),
        JsDocType::Union(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::UnionType,
            range,
        }),
        JsDocType::Unsupported(kind) => {
            Err(JsDocTypeResolutionError::UnsupportedType { kind: *kind, range })
        }
    }
}

fn validate_resolvable_type(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    type_: &JsDocType,
    range: TextRange,
) -> Result<(), JsDocTypeResolutionError> {
    match type_ {
        JsDocType::Intrinsic(_) => Ok(()),
        JsDocType::Named(name) => {
            let type_ = match name.as_str() {
                "Object" if !options.no_implicit_any => return Ok(()),
                "Object" => global_types.object_type,
                "Function" | "function" => global_types.function_type,
                "array" if !options.no_implicit_any => global_types.any_array_type,
                _ => {
                    return Err(JsDocTypeResolutionError::UnresolvedTypeReference {
                        name: name.clone(),
                        range,
                    });
                }
            };
            if store.type_payload(type_).is_none() {
                return Err(JsDocTypeResolutionError::InvalidGlobalType(type_));
            }
            Ok(())
        }
        JsDocType::Parenthesized(inner)
        | JsDocType::Nullable(inner)
        | JsDocType::NonNullable(inner)
        | JsDocType::Optional(inner)
        | JsDocType::Variadic(inner)
        | JsDocType::Array(inner) => {
            validate_resolvable_type(store, global_types, options, inner, range)
        }
        JsDocType::Union(members) => members.iter().try_for_each(|member| {
            validate_resolvable_type(store, global_types, options, member, range)
        }),
        JsDocType::Unsupported(kind) => {
            Err(JsDocTypeResolutionError::UnsupportedType { kind: *kind, range })
        }
    }
}

fn resolve_complete_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    type_: &JsDocType,
    range: TextRange,
) -> Result<TypeId, JsDocTypeResolutionError> {
    match type_ {
        JsDocType::Intrinsic(_) => resolve_intrinsic_type(store, options, type_, range),
        JsDocType::Named(name) => match name.as_str() {
            "Object" if !options.no_implicit_any => {
                resolve_intrinsic_type(store, options, type_, range)
            }
            "Object" => Ok(global_types.object_type),
            "Function" | "function" => Ok(global_types.function_type),
            "array" if !options.no_implicit_any => Ok(global_types.any_array_type),
            _ => Err(JsDocTypeResolutionError::UnresolvedTypeReference {
                name: name.clone(),
                range,
            }),
        },
        JsDocType::Parenthesized(inner) | JsDocType::NonNullable(inner) => {
            resolve_complete_type(store, global_types, options, inner, range)
        }
        JsDocType::Nullable(inner) => {
            let inner = resolve_complete_type(store, global_types, options, inner, range)?;
            if !options.intrinsic.strict_null_checks {
                return Ok(inner);
            }
            let null = store
                .intrinsic_bootstrap()
                .ok_or(JsDocTypeResolutionError::MissingBootstrap)?
                .null_type;
            store
                .expression_union_type_with_global_types(
                    global_types,
                    &[inner, null],
                    UnionReduction::Literal,
                )
                .map_err(|_| JsDocTypeResolutionError::UnionConstruction(range))
        }
        JsDocType::Optional(inner) => {
            let inner = resolve_complete_type(store, global_types, options, inner, range)?;
            if !options.intrinsic.strict_null_checks {
                return Ok(inner);
            }
            let undefined = store
                .intrinsic_bootstrap()
                .ok_or(JsDocTypeResolutionError::MissingBootstrap)?
                .undefined_type;
            store
                .expression_union_type_with_global_types(
                    global_types,
                    &[inner, undefined],
                    UnionReduction::Literal,
                )
                .map_err(|_| JsDocTypeResolutionError::UnionConstruction(range))
        }
        JsDocType::Variadic(inner) | JsDocType::Array(inner) => {
            let inner = resolve_complete_type(store, global_types, options, inner, range)?;
            store
                .create_canonical_array_type(global_types, inner, false)
                .map_err(|error| JsDocTypeResolutionError::ArrayConstruction { range, error })
        }
        JsDocType::Union(members) => {
            let resolved_members = members
                .iter()
                .map(|member| resolve_complete_type(store, global_types, options, member, range))
                .collect::<Result<Vec<_>, _>>()?;
            store
                .expression_union_type_with_global_types(
                    global_types,
                    &resolved_members,
                    UnionReduction::Literal,
                )
                .map_err(|_| JsDocTypeResolutionError::UnionConstruction(range))
        }
        JsDocType::Unsupported(kind) => {
            Err(JsDocTypeResolutionError::UnsupportedType { kind: *kind, range })
        }
    }
}

fn skip_doc_whitespace(source: &str, mut index: usize, end: usize) -> usize {
    let bytes = source.as_bytes();
    while index < end {
        if bytes[index].is_ascii_whitespace() {
            index += 1;
            continue;
        }
        if bytes[index] == b'*'
            && source
                .get(..index)
                .and_then(|prefix| prefix.rsplit_once('\n'))
                .is_some_and(|(_, line)| {
                    line.bytes()
                        .all(|byte| matches!(byte, b' ' | b'\t' | b'\r'))
                })
        {
            index += 1;
            continue;
        }
        break;
    }
    index
}

fn unbraced_type_end(source: &str, start: usize, end: usize) -> usize {
    let bytes = source.as_bytes();
    let mut cursor = start;
    while cursor < end && !bytes[cursor].is_ascii_whitespace() {
        cursor += 1;
    }
    cursor
}

fn trimmed_range(source: &str, start: usize, end: usize) -> (usize, usize) {
    let bytes = source.as_bytes();
    let mut first = start;
    let mut last = end;
    while first < last && bytes[first].is_ascii_whitespace() {
        first += 1;
    }
    while last > first && bytes[last - 1].is_ascii_whitespace() {
        last -= 1;
    }
    (first, last)
}

fn normalize_type_text(text: &str) -> String {
    let mut normalized = String::with_capacity(text.len());
    let mut line_start = false;
    let mut leading_whitespace = true;
    for character in text.chars() {
        if character == '\n' {
            normalized.push(character);
            line_start = true;
            leading_whitespace = true;
            continue;
        }
        if line_start && leading_whitespace && matches!(character, ' ' | '\t' | '\r') {
            normalized.push(character);
            continue;
        }
        if line_start && leading_whitespace && character == '*' {
            normalized.push(' ');
            leading_whitespace = false;
            continue;
        }
        normalized.push(character);
        leading_whitespace = false;
    }
    normalized
}

fn checked_range(start: usize, end: usize) -> Result<TextRange, JsDocCommentError> {
    let start = u32::try_from(start).map_err(|_| JsDocCommentError::SourcePositionOverflow)?;
    let end = u32::try_from(end).map_err(|_| JsDocCommentError::SourcePositionOverflow)?;
    Ok(TextRange::new(TextPos::new(start), TextPos::new(end)))
}

fn relocate_comment_diagnostic(
    mut diagnostic: Diagnostic,
    offset: usize,
) -> Result<Diagnostic, JsDocCommentError> {
    let start = offset
        .checked_add(diagnostic.range.start.get() as usize)
        .ok_or(JsDocCommentError::SourcePositionOverflow)?;
    let end = offset
        .checked_add(diagnostic.range.end.get() as usize)
        .ok_or(JsDocCommentError::SourcePositionOverflow)?;
    diagnostic.range = checked_range(start, end)?;
    Ok(diagnostic)
}

fn relocate_type_diagnostic(
    mut diagnostic: Diagnostic,
    expression_start: usize,
    expression_end: usize,
) -> Result<Diagnostic, JsDocCommentError> {
    let start = expression_start
        .checked_add((diagnostic.range.start.get() as usize).saturating_sub(TYPE_PREFIX.len()))
        .ok_or(JsDocCommentError::SourcePositionOverflow)?
        .min(expression_end);
    let end = expression_start
        .checked_add((diagnostic.range.end.get() as usize).saturating_sub(TYPE_PREFIX.len()))
        .ok_or(JsDocCommentError::SourcePositionOverflow)?
        .min(expression_end);
    diagnostic.range = checked_range(start, end.max(start))?;
    Ok(diagnostic)
}

fn type_expected_diagnostic(
    source: &str,
    position: usize,
    end: usize,
) -> Result<Diagnostic, JsDocCommentError> {
    expected_diagnostic(source, position, end, 1110, &[])
}

fn expected_token_diagnostic(
    source: &str,
    position: usize,
    end: usize,
    token: &str,
) -> Result<Diagnostic, JsDocCommentError> {
    expected_diagnostic(source, position, end, 1005, &[token])
}

fn expected_diagnostic(
    source: &str,
    position: usize,
    end: usize,
    code: u32,
    arguments: &[&str],
) -> Result<Diagnostic, JsDocCommentError> {
    let start = position.min(end).min(source.len());
    let end = if start < source.len() {
        start + source[start..].chars().next().map_or(0, char::len_utf8)
    } else {
        start
    };
    let message = message_by_code(code).ok_or(JsDocCommentError::SourcePositionOverflow)?;
    let category = match message.category() {
        Category::Warning => DiagnosticCategory::Warning,
        Category::Error => DiagnosticCategory::Error,
        Category::Suggestion => DiagnosticCategory::Suggestion,
        Category::Message => DiagnosticCategory::Message,
    };
    let arguments = arguments
        .iter()
        .map(|argument| (*argument).to_owned())
        .collect::<Vec<_>>();
    let rendered = message
        .format(&arguments)
        .map_err(|_| JsDocCommentError::SourcePositionOverflow)?;
    Ok(Diagnostic::typescript(
        checked_range(start, end)?,
        code,
        category,
        rendered,
    ))
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{CanonicalCheckerContext, IntrinsicBootstrapOptions};

    fn context(
        parsed: &ParseResult,
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'_> {
        let file = FileId::new(0);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/input.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(binder.finish(), vec![(file, &parsed.arena)], options).unwrap()
    }

    fn type_tag(source: &str) -> ParsedJsDocComment<'_> {
        parse_jsdoc_comment_at(source, checked_range(0, source.len()).unwrap()).unwrap()
    }

    #[test]
    fn strict_nullable_optional_and_explicit_unions_use_canonical_types() {
        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = context(&parsed, options);
        for (source, expected) in [
            ("/** @type {?number} */", "number | null"),
            ("/** @type {number=} */", "number | undefined"),
            ("/** @type {string | number} */", "string | number"),
        ] {
            let comment = type_tag(source);
            assert!(
                comment.diagnostics().is_empty(),
                "{:?}",
                comment.diagnostics()
            );
            let annotation = comment.type_tag().unwrap().type_expression().unwrap();
            let globals = context.global_types().clone();
            let type_ =
                resolve_jsdoc_type(context.store_mut_for_test(), &globals, options, annotation)
                    .unwrap();
            assert_eq!(context.type_to_string(type_).unwrap(), expected);
        }
    }

    #[test]
    fn unresolved_union_member_fails_before_union_allocation() {
        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let comment = type_tag("/** @type {string | Missing} */");
        let annotation = comment.type_tag().unwrap().type_expression().unwrap();
        let globals = context.global_types().clone();
        let before = context.store().type_len();
        assert_eq!(
            resolve_jsdoc_type(context.store_mut_for_test(), &globals, options, annotation,),
            Err(JsDocTypeResolutionError::UnresolvedTypeReference {
                name: "Missing".to_owned(),
                range: annotation.range(),
            })
        );
        assert_eq!(context.store().type_len(), before);
    }

    #[test]
    fn jsdoc_object_and_function_names_follow_pinned_global_rules() {
        let parsed = parse_source_file("const marker = 1;");
        for implicit_any in [false, true] {
            let options = CanonicalCheckerOptions {
                no_implicit_any: implicit_any,
                ..CanonicalCheckerOptions::default()
            };
            let mut context = context(&parsed, options);
            let globals = context.global_types().clone();
            let comment = type_tag("/** @type {Object} */");
            let annotation = comment.type_tag().unwrap().type_expression().unwrap();
            let object =
                resolve_jsdoc_type(context.store_mut_for_test(), &globals, options, annotation)
                    .unwrap();
            let expected = if implicit_any {
                globals.object_type
            } else {
                context.store().intrinsic_bootstrap().unwrap().any_type
            };
            assert_eq!(object, expected);

            let comment = type_tag("/** @type {Function} */");
            let annotation = comment.type_tag().unwrap().type_expression().unwrap();
            let function =
                resolve_jsdoc_type(context.store_mut_for_test(), &globals, options, annotation)
                    .unwrap();
            assert_eq!(function, globals.function_type);
        }
    }
}
