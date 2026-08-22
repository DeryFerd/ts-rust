//! Parsed `JSDoc` types for the canonical JavaScript checker.
//!
//! The source parser does not yet attach structured `JSDoc` nodes to source
//! declarations. This module uses its standalone comment scanner to identify
//! tags, then parses each type with the ordinary TypeScript type parser. The
//! resulting values never contain node identities from that temporary arena.

use std::{
    collections::{HashMap, HashSet},
    fmt,
};

use ts_ast::{NodeArena, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_core::{Diagnostic, DiagnosticCategory, TextPos, TextRange};
use ts_diagnostics::{Category, Diagnostic as CheckerDiagnostic, message_by_code};
use ts_jsnum::{Number, PseudoBigInt};
use ts_parser::{parse_jsdoc_comment, parse_source_file};

use super::{
    ArrayTypeError, CanonicalCheckerDiagnostic, CanonicalCheckerDiagnosticRange,
    CanonicalCheckerOptions, CanonicalGlobalTypes, CanonicalTypeMapperStore,
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
    Callback,
    Property,
    Template,
    Satisfies,
    This,
    Augments,
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
    BoundTypeParameter(TypeId),
    GenericReference { name: String, arguments: Vec<Self> },
    Import(JsDocImportType),
    StringLiteral(String),
    NumberLiteral(String),
    BigIntLiteral(String),
    ObjectLiteral(Vec<JsDocObjectProperty>),
    Function(Box<JsDocFunctionType>),
    IndexedAccess { object: Box<Self>, index: Box<Self> },
    KeyOf(Box<Self>),
    Parenthesized(Box<Self>),
    Nullable(Box<Self>),
    NonNullable(Box<Self>),
    Optional(Box<Self>),
    Variadic(Box<Self>),
    Array(Box<Self>),
    ReadonlyArray(Box<Self>),
    Union(Vec<Self>),
    Unsupported(SyntaxKind),
}

/// One property in an inline `JSDoc` object type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsDocObjectProperty {
    name: String,
    type_: JsDocType,
    optional: bool,
    readonly: bool,
}

impl JsDocObjectProperty {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub const fn type_(&self) -> &JsDocType {
        &self.type_
    }

    #[must_use]
    pub const fn is_optional(&self) -> bool {
        self.optional
    }

    #[must_use]
    pub const fn is_readonly(&self) -> bool {
        self.readonly
    }
}

/// One parameter in a `JSDoc` function type expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsDocFunctionParameter {
    name: String,
    type_: Option<JsDocType>,
    optional: bool,
    rest: bool,
}

impl JsDocFunctionParameter {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub const fn type_(&self) -> Option<&JsDocType> {
        self.type_.as_ref()
    }

    #[must_use]
    pub const fn is_optional(&self) -> bool {
        self.optional
    }

    #[must_use]
    pub const fn is_rest(&self) -> bool {
        self.rest
    }
}

/// The structural contents of a `JSDoc` function type expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsDocFunctionType {
    parameters: Vec<JsDocFunctionParameter>,
    return_type: JsDocType,
}

impl JsDocFunctionType {
    #[must_use]
    pub fn parameters(&self) -> &[JsDocFunctionParameter] {
        &self.parameters
    }

    #[must_use]
    pub const fn return_type(&self) -> &JsDocType {
        &self.return_type
    }
}

/// One `import("module").Name` reference retained for later module resolution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsDocImportType {
    specifier: String,
    qualifier: Option<String>,
    type_arguments: Vec<JsDocType>,
    is_type_of: bool,
}

impl JsDocImportType {
    #[must_use]
    pub fn specifier(&self) -> &str {
        &self.specifier
    }

    #[must_use]
    pub fn qualifier(&self) -> Option<&str> {
        self.qualifier.as_deref()
    }

    #[must_use]
    pub fn type_arguments(&self) -> &[JsDocType] {
        &self.type_arguments
    }

    #[must_use]
    pub const fn is_type_of(&self) -> bool {
        self.is_type_of
    }
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

    #[must_use]
    pub fn planned(&self) -> PlannedJsDocType {
        PlannedJsDocType {
            range: self.range,
            type_: self.type_.clone(),
            resolved_type: None,
        }
    }
}

/// An owned annotation that can outlive its parsed source comment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedJsDocType {
    range: TextRange,
    type_: JsDocType,
    resolved_type: Option<Box<JsDocType>>,
}

/// A checked canonical type-parameter identity for one `@template` name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct JsDocTypeParameterBinding<'name> {
    name: &'name str,
    type_: TypeId,
}

impl<'name> JsDocTypeParameterBinding<'name> {
    #[must_use]
    pub const fn new(name: &'name str, type_: TypeId) -> Self {
        Self { name, type_ }
    }

    #[must_use]
    pub const fn name(self) -> &'name str {
        self.name
    }

    #[must_use]
    pub const fn type_(self) -> TypeId {
        self.type_
    }
}

impl PlannedJsDocType {
    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }

    #[must_use]
    pub const fn type_(&self) -> &JsDocType {
        &self.type_
    }

    fn resolution_type(&self) -> &JsDocType {
        self.resolved_type.as_deref().unwrap_or(&self.type_)
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

/// One parsed `@template` parameter and its optional constraint or default.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsDocTemplateParameter<'source> {
    name: JsDocTagName<'source>,
    constraint: Option<JsDocTypeExpression<'source>>,
    default_type: Option<JsDocTypeExpression<'source>>,
}

impl<'source> JsDocTemplateParameter<'source> {
    #[must_use]
    pub const fn name(&self) -> JsDocTagName<'source> {
        self.name
    }

    #[must_use]
    pub const fn constraint(&self) -> Option<&JsDocTypeExpression<'source>> {
        self.constraint.as_ref()
    }

    #[must_use]
    pub const fn default_type(&self) -> Option<&JsDocTypeExpression<'source>> {
        self.default_type.as_ref()
    }
}

/// One supported `JSDoc` tag and its exact source-owned arguments.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsDocTag<'source> {
    kind: JsDocTagKind,
    tag_name: &'source str,
    range: TextRange,
    name: Option<JsDocTagName<'source>>,
    type_expression: Option<JsDocTypeExpression<'source>>,
    template_parameters: Vec<JsDocTemplateParameter<'source>>,
    name_first: bool,
    optional: bool,
}

impl<'source> JsDocTag<'source> {
    #[must_use]
    pub const fn kind(&self) -> JsDocTagKind {
        self.kind
    }

    #[must_use]
    pub const fn tag_name(&self) -> &'source str {
        self.tag_name
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
    pub fn template_parameters(&self) -> &[JsDocTemplateParameter<'source>] {
        &self.template_parameters
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

    #[must_use]
    pub fn augments_tag(&self) -> Option<&JsDocTag<'source>> {
        self.tags
            .iter()
            .find(|tag| tag.kind == JsDocTagKind::Augments)
    }
}

/// One owned `JSDoc` parameter and its declaration name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedJsDocParameter {
    name: String,
    range: TextRange,
    type_: Option<PlannedJsDocType>,
    optional: bool,
    name_first: bool,
}

impl PlannedJsDocParameter {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }

    #[must_use]
    pub const fn type_(&self) -> Option<&PlannedJsDocType> {
        self.type_.as_ref()
    }

    #[must_use]
    pub const fn is_optional(&self) -> bool {
        self.optional
    }
}

/// One source-owned `@template` parameter.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedJsDocTemplateParameter {
    name: String,
    range: TextRange,
    constraint: Option<PlannedJsDocType>,
    default_type: Option<PlannedJsDocType>,
}

impl PlannedJsDocTemplateParameter {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }

    #[must_use]
    pub const fn constraint(&self) -> Option<&PlannedJsDocType> {
        self.constraint.as_ref()
    }

    #[must_use]
    pub const fn default_type(&self) -> Option<&PlannedJsDocType> {
        self.default_type.as_ref()
    }
}

/// One source-owned `@property` declaration in an object typedef.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedJsDocProperty {
    name: String,
    range: TextRange,
    type_: Option<PlannedJsDocType>,
    optional: bool,
}

impl PlannedJsDocProperty {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }

    #[must_use]
    pub const fn type_(&self) -> Option<&PlannedJsDocType> {
        self.type_.as_ref()
    }

    #[must_use]
    pub const fn is_optional(&self) -> bool {
        self.optional
    }
}

/// A source-owned `@satisfies` annotation and its exact diagnostic location.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedJsDocSatisfies {
    range: TextRange,
    type_: PlannedJsDocType,
}

impl PlannedJsDocSatisfies {
    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }

    #[must_use]
    pub const fn type_(&self) -> &PlannedJsDocType {
        &self.type_
    }
}

/// A `JSDoc` typedef retained before its synthetic binder declaration exists.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedJsDocTypedef {
    name: String,
    range: TextRange,
    type_: Option<PlannedJsDocType>,
    properties: Vec<PlannedJsDocProperty>,
    template_parameters: Vec<PlannedJsDocTemplateParameter>,
}

/// One synthetic `JSDoc` callback signature, separate from its host function.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedJsDocCallback {
    name: String,
    range: TextRange,
    parameters: Vec<PlannedJsDocParameter>,
    return_type: Option<PlannedJsDocType>,
    this_type: Option<PlannedJsDocType>,
    template_parameters: Vec<PlannedJsDocTemplateParameter>,
}

impl PlannedJsDocCallback {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }

    #[must_use]
    pub fn parameters(&self) -> &[PlannedJsDocParameter] {
        &self.parameters
    }

    #[must_use]
    pub const fn return_type(&self) -> Option<&PlannedJsDocType> {
        self.return_type.as_ref()
    }

    #[must_use]
    pub const fn this_type(&self) -> Option<&PlannedJsDocType> {
        self.this_type.as_ref()
    }

    #[must_use]
    pub fn template_parameters(&self) -> &[PlannedJsDocTemplateParameter] {
        &self.template_parameters
    }
}

impl PlannedJsDocTypedef {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }

    #[must_use]
    pub const fn type_(&self) -> Option<&PlannedJsDocType> {
        self.type_.as_ref()
    }

    #[must_use]
    pub fn properties(&self) -> &[PlannedJsDocProperty] {
        &self.properties
    }

    #[must_use]
    pub fn template_parameters(&self) -> &[PlannedJsDocTemplateParameter] {
        &self.template_parameters
    }
}

/// Source-owned `JSDoc` annotations for one JavaScript declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedJavaScriptDeclaration {
    node: NodeRef,
    type_: Option<PlannedJsDocType>,
    parameters: Vec<PlannedJsDocParameter>,
    return_type: Option<PlannedJsDocType>,
    typedefs: Vec<PlannedJsDocTypedef>,
    callbacks: Vec<PlannedJsDocCallback>,
    template_parameters: Vec<PlannedJsDocTemplateParameter>,
    satisfies: Option<PlannedJsDocSatisfies>,
    this_type: Option<PlannedJsDocType>,
    augments_type: Option<PlannedJsDocType>,
}

impl PlannedJavaScriptDeclaration {
    #[must_use]
    pub const fn node(&self) -> NodeRef {
        self.node
    }

    #[must_use]
    pub const fn type_(&self) -> Option<&PlannedJsDocType> {
        self.type_.as_ref()
    }

    #[must_use]
    pub fn parameters(&self) -> &[PlannedJsDocParameter] {
        &self.parameters
    }

    #[must_use]
    pub fn parameter(&self, name: &str) -> Option<&PlannedJsDocParameter> {
        self.parameters
            .iter()
            .find(|parameter| parameter.name == name)
    }

    #[must_use]
    pub const fn return_type(&self) -> Option<&PlannedJsDocType> {
        self.return_type.as_ref()
    }

    #[must_use]
    pub fn typedefs(&self) -> &[PlannedJsDocTypedef] {
        &self.typedefs
    }

    #[must_use]
    pub fn callbacks(&self) -> &[PlannedJsDocCallback] {
        &self.callbacks
    }

    #[must_use]
    pub fn template_parameters(&self) -> &[PlannedJsDocTemplateParameter] {
        &self.template_parameters
    }

    #[must_use]
    pub const fn satisfies(&self) -> Option<&PlannedJsDocSatisfies> {
        self.satisfies.as_ref()
    }

    #[must_use]
    pub const fn this_type(&self) -> Option<&PlannedJsDocType> {
        self.this_type.as_ref()
    }

    #[must_use]
    pub const fn augments_type(&self) -> Option<&PlannedJsDocType> {
        self.augments_type.as_ref()
    }
}

/// The complete owned `JSDoc` plan for one JavaScript source file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedJavaScriptJsDoc {
    declarations: Vec<PlannedJavaScriptDeclaration>,
    diagnostics: Vec<CanonicalCheckerDiagnostic>,
}

impl PlannedJavaScriptJsDoc {
    #[must_use]
    pub fn declarations(&self) -> &[PlannedJavaScriptDeclaration] {
        &self.declarations
    }

    #[must_use]
    pub fn declaration(&self, node: NodeRef) -> Option<&PlannedJavaScriptDeclaration> {
        self.declarations
            .iter()
            .find(|declaration| declaration.node == node)
    }

    /// Finds annotations on a callable or its declaring variable.
    #[must_use]
    pub fn callable_declaration(
        &self,
        arena: &NodeArena,
        callable: NodeRef,
    ) -> Option<&PlannedJavaScriptDeclaration> {
        self.declaration(callable).or_else(|| {
            let mut current = arena.get(callable.node)?.parent?;
            loop {
                let node = arena.get(current)?;
                match node.kind {
                    SyntaxKind::VariableDeclaration => {
                        return self.declaration(NodeRef::new(
                            callable.arena,
                            callable.file,
                            current,
                        ));
                    }
                    SyntaxKind::ParenthesizedExpression => current = node.parent?,
                    _ => return None,
                }
            }
        })
    }

    #[must_use]
    pub fn diagnostics(&self) -> &[CanonicalCheckerDiagnostic] {
        &self.diagnostics
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
    UnsupportedParserDiagnostic { code: Option<u32>, range: TextRange },
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
            Self::UnsupportedParserDiagnostic { code, range } => {
                write!(
                    formatter,
                    "JSDoc diagnostic {code:?} cannot be retained at {range:?}"
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
    LiteralConstruction(TextRange),
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
            Self::LiteralConstruction(range) => {
                write!(
                    formatter,
                    "JSDoc literal type could not be created at {range:?}"
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

/// Returns all adjacent leading `JSDoc` comments in source order.
///
/// # Errors
///
/// Returns an error when the node or any retained comment has invalid source
/// provenance.
pub fn leading_jsdoc_comments(
    arena: &NodeArena,
    node: NodeRef,
) -> Result<Vec<ParsedJsDocComment<'_>>, JsDocCommentError> {
    if node.arena != arena.id() {
        return Err(JsDocCommentError::InvalidSourceNode(node));
    }
    let record = arena
        .get(node.node)
        .ok_or(JsDocCommentError::InvalidSourceNode(node))?;
    let source = arena
        .source_text()
        .ok_or(JsDocCommentError::MissingSourceText(node))?;
    let mut end = usize::try_from(record.range.start.get())
        .map_err(|_| JsDocCommentError::InvalidSourceNode(node))?;
    let mut comments = Vec::new();
    loop {
        let prefix = source
            .get(..end)
            .ok_or(JsDocCommentError::InvalidSourceNode(node))?
            .trim_end_matches(char::is_whitespace);
        if !prefix.ends_with("*/") {
            break;
        }
        let Some(start) = prefix.rfind("/**") else {
            break;
        };
        comments.push(parse_jsdoc_comment_at(
            source,
            checked_range(start, prefix.len())?,
        )?);
        end = start;
    }
    comments.reverse();
    Ok(comments)
}

/// Collects source-owned `JSDoc` annotations for JavaScript declarations.
///
/// Parser and semantic diagnostics are anchored to the source root because
/// comment ranges precede the declaration nodes they annotate.
///
/// # Errors
///
/// Returns an error for invalid source identity, malformed parser trees, or
/// parser diagnostics whose catalog arguments cannot be reconstructed.
pub fn plan_javascript_source_jsdoc(
    arena: &NodeArena,
    source: NodeRef,
) -> Result<PlannedJavaScriptJsDoc, JsDocCommentError> {
    if source.arena != arena.id() {
        return Err(JsDocCommentError::InvalidSourceNode(source));
    }
    let root = arena
        .get(source.node)
        .ok_or(JsDocCommentError::InvalidSourceNode(source))?;
    if root.kind != SyntaxKind::SourceFile || !matches!(root.data, NodeData::SourceFile(_)) {
        return Err(JsDocCommentError::InvalidSourceNode(source));
    }
    if arena.source_text().is_none() {
        return Err(JsDocCommentError::MissingSourceText(source));
    }

    let mut pending = vec![source.node];
    let mut seen_comments = HashSet::new();
    let mut declarations = Vec::new();
    let mut diagnostics = Vec::new();

    while let Some(node) = pending.pop() {
        let record = arena
            .get(node)
            .ok_or(JsDocCommentError::InvalidSourceNode(source))?;
        let reference = NodeRef::new(arena.id(), source.file, node);
        if is_jsdoc_declaration_candidate(record.kind) {
            let comments = leading_jsdoc_comments(arena, reference)?
                .into_iter()
                .filter(|comment| {
                    seen_comments.insert((comment.range().start.get(), comment.range().end.get()))
                })
                .collect::<Vec<_>>();
            if !comments.is_empty() {
                let declaration = javascript_jsdoc_owner(arena, reference)?;
                let mut planned = PlannedJavaScriptDeclaration {
                    node: declaration,
                    type_: None,
                    parameters: Vec::new(),
                    return_type: None,
                    typedefs: Vec::new(),
                    callbacks: Vec::new(),
                    template_parameters: Vec::new(),
                    satisfies: None,
                    this_type: None,
                    augments_type: None,
                };
                for comment in comments {
                    for diagnostic in comment.diagnostics() {
                        diagnostics.push(canonical_parser_diagnostic(source, diagnostic)?);
                    }
                    apply_comment_tags(arena, source, &mut planned, &comment, &mut diagnostics)?;
                }
                append_unmatched_parameter_diagnostics(arena, source, &planned, &mut diagnostics)?;
                declarations.push(planned);
            }
        }
        let mut children = Vec::new();
        record.for_each_child(|child| children.push(child));
        pending.extend(children.into_iter().rev());
    }

    attach_local_typedef_resolutions(&mut declarations);

    Ok(PlannedJavaScriptJsDoc {
        declarations,
        diagnostics,
    })
}

/// Appends planned comment diagnostics with the source checker's retry rules.
pub fn append_javascript_jsdoc_diagnostics(
    plan: &PlannedJavaScriptJsDoc,
    diagnostics: &mut super::CanonicalCheckerDiagnostics,
) {
    for diagnostic in &plan.diagnostics {
        diagnostics.lookup_primary_or_issue(
            diagnostic.node,
            diagnostic.range_override,
            diagnostic.diagnostic.clone(),
        );
    }
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

/// Validates an owned `JSDoc` annotation before any semantic allocation.
///
/// # Errors
///
/// Returns the same unsupported-reference, option, and global-identity errors
/// as [`resolve_planned_jsdoc_type`].
pub fn preflight_planned_jsdoc_type(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    annotation: &PlannedJsDocType,
) -> Result<(), JsDocTypeResolutionError> {
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
        annotation.resolution_type(),
        annotation.range(),
    )
}

/// Resolves an owned annotation into the source checker's canonical store.
///
/// # Errors
///
/// Returns an error for unsupported syntax, invalid global identities,
/// inconsistent options, or failed union/array allocation.
pub fn resolve_planned_jsdoc_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    annotation: &PlannedJsDocType,
) -> Result<TypeId, JsDocTypeResolutionError> {
    preflight_planned_jsdoc_type(store, global_types, options, annotation)?;
    resolve_complete_type(
        store,
        global_types,
        options,
        annotation.resolution_type(),
        annotation.range(),
    )
}

fn attach_local_typedef_resolutions(declarations: &mut [PlannedJavaScriptDeclaration]) {
    let mut aliases = HashMap::new();
    let mut duplicates = HashSet::new();
    for declaration in declarations.iter() {
        for alias in &declaration.typedefs {
            let Some(annotation) = &alias.type_ else {
                continue;
            };
            if aliases
                .insert(alias.name.clone(), annotation.type_.clone())
                .is_some()
            {
                duplicates.insert(alias.name.clone());
            }
        }
    }
    for name in duplicates {
        aliases.remove(&name);
    }
    if aliases.is_empty() {
        return;
    }

    for declaration in declarations {
        if let Some(annotation) = &mut declaration.type_ {
            attach_local_typedef_resolution(annotation, &aliases);
        }
        if let Some(annotation) = &mut declaration.return_type {
            attach_local_typedef_resolution(annotation, &aliases);
        }
        for parameter in &mut declaration.parameters {
            if let Some(annotation) = &mut parameter.type_ {
                attach_local_typedef_resolution(annotation, &aliases);
            }
        }
        for alias in &mut declaration.typedefs {
            if let Some(annotation) = &mut alias.type_ {
                attach_local_typedef_resolution(annotation, &aliases);
            }
        }
        for callback in &mut declaration.callbacks {
            for parameter in &mut callback.parameters {
                if let Some(annotation) = &mut parameter.type_ {
                    attach_local_typedef_resolution(annotation, &aliases);
                }
            }
            if let Some(annotation) = &mut callback.return_type {
                attach_local_typedef_resolution(annotation, &aliases);
            }
        }
    }
}

fn attach_local_typedef_resolution(
    annotation: &mut PlannedJsDocType,
    aliases: &HashMap<String, JsDocType>,
) {
    if let Some(resolved) = substitute_local_typedefs(&annotation.type_, aliases) {
        annotation.resolved_type = Some(Box::new(resolved));
    }
}

fn substitute_local_typedefs(
    type_: &JsDocType,
    aliases: &HashMap<String, JsDocType>,
) -> Option<JsDocType> {
    match type_ {
        JsDocType::Named(name) => resolve_scalar_typedef(name, aliases, &mut HashSet::new()),
        JsDocType::Parenthesized(inner) => substitute_local_typedefs(inner, aliases)
            .map(Box::new)
            .map(JsDocType::Parenthesized),
        JsDocType::Nullable(inner) => substitute_local_typedefs(inner, aliases)
            .map(Box::new)
            .map(JsDocType::Nullable),
        JsDocType::NonNullable(inner) => substitute_local_typedefs(inner, aliases)
            .map(Box::new)
            .map(JsDocType::NonNullable),
        JsDocType::Optional(inner) => substitute_local_typedefs(inner, aliases)
            .map(Box::new)
            .map(JsDocType::Optional),
        JsDocType::Variadic(inner) => substitute_local_typedefs(inner, aliases)
            .map(Box::new)
            .map(JsDocType::Variadic),
        JsDocType::Array(inner) => substitute_local_typedefs(inner, aliases)
            .map(Box::new)
            .map(JsDocType::Array),
        JsDocType::ReadonlyArray(inner) => substitute_local_typedefs(inner, aliases)
            .map(Box::new)
            .map(JsDocType::ReadonlyArray),
        JsDocType::Union(members) => {
            let mut changed = false;
            let resolved = members
                .iter()
                .map(|member| {
                    substitute_local_typedefs(member, aliases).map_or_else(
                        || member.clone(),
                        |member| {
                            changed = true;
                            member
                        },
                    )
                })
                .collect::<Vec<_>>();
            changed.then_some(JsDocType::Union(resolved))
        }
        JsDocType::Intrinsic(_)
        | JsDocType::BoundTypeParameter(_)
        | JsDocType::GenericReference { .. }
        | JsDocType::Import(_)
        | JsDocType::StringLiteral(_)
        | JsDocType::NumberLiteral(_)
        | JsDocType::BigIntLiteral(_)
        | JsDocType::ObjectLiteral(_)
        | JsDocType::Function(_)
        | JsDocType::IndexedAccess { .. }
        | JsDocType::KeyOf(_)
        | JsDocType::Unsupported(_) => None,
    }
}

fn resolve_scalar_typedef(
    name: &str,
    aliases: &HashMap<String, JsDocType>,
    visiting: &mut HashSet<String>,
) -> Option<JsDocType> {
    if !visiting.insert(name.to_owned()) {
        return None;
    }
    let resolved = match aliases.get(name)? {
        scalar @ (JsDocType::Intrinsic(_)
        | JsDocType::StringLiteral(_)
        | JsDocType::NumberLiteral(_)
        | JsDocType::BigIntLiteral(_)) => Some(scalar.clone()),
        JsDocType::Named(next) => resolve_scalar_typedef(next, aliases, visiting),
        JsDocType::Parenthesized(inner) => match inner.as_ref() {
            scalar @ (JsDocType::Intrinsic(_)
            | JsDocType::StringLiteral(_)
            | JsDocType::NumberLiteral(_)
            | JsDocType::BigIntLiteral(_)) => Some(scalar.clone()),
            JsDocType::Named(next) => resolve_scalar_typedef(next, aliases, visiting),
            _ => None,
        },
        _ => None,
    };
    visiting.remove(name);
    resolved
}

fn is_jsdoc_declaration_candidate(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::VariableStatement
            | SyntaxKind::FunctionDeclaration
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ArrowFunction
            | SyntaxKind::ClassDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::MethodDeclaration
    )
}

fn javascript_jsdoc_owner(arena: &NodeArena, node: NodeRef) -> Result<NodeRef, JsDocCommentError> {
    let record = arena
        .get(node.node)
        .ok_or(JsDocCommentError::InvalidSourceNode(node))?;
    let NodeData::VariableStatement(statement) = &record.data else {
        return Ok(node);
    };
    let declaration_list = arena
        .get(statement.declaration_list)
        .ok_or(JsDocCommentError::InvalidSourceNode(node))?;
    let NodeData::VariableDeclarationList(declarations) = &declaration_list.data else {
        return Err(JsDocCommentError::InvalidSourceNode(node));
    };
    let first = declarations
        .declarations
        .nodes
        .first()
        .copied()
        .ok_or(JsDocCommentError::InvalidSourceNode(node))?;
    Ok(NodeRef::new(node.arena, node.file, first))
}

#[derive(Clone, Copy)]
enum ActiveJsDocDefinition {
    Typedef(usize),
    Callback(usize),
}

fn apply_comment_tags(
    arena: &NodeArena,
    source: NodeRef,
    declaration: &mut PlannedJavaScriptDeclaration,
    comment: &ParsedJsDocComment<'_>,
    diagnostics: &mut Vec<CanonicalCheckerDiagnostic>,
) -> Result<(), JsDocCommentError> {
    let has_unhosted_definition = comment
        .tags()
        .iter()
        .any(|tag| matches!(tag.kind(), JsDocTagKind::Typedef | JsDocTagKind::Callback));
    let mut pending_templates = Vec::new();
    let mut active = None;
    let mut saw_definition = false;

    for tag in comment.tags() {
        match (active, tag.kind()) {
            (_, JsDocTagKind::Template) => {
                if saw_definition {
                    diagnostics.push(canonical_jsdoc_diagnostic(
                        source,
                        jsdoc_tag_name_range(tag)?,
                        8039,
                        std::iter::empty::<String>(),
                    )?);
                } else if has_unhosted_definition {
                    pending_templates.extend(planned_template_parameters(tag));
                } else {
                    declaration
                        .template_parameters
                        .extend(planned_template_parameters(tag));
                }
            }
            (_, JsDocTagKind::Callback) => {
                let before = declaration.callbacks.len();
                apply_jsdoc_tag(arena, source, declaration, tag, diagnostics)?;
                if declaration.callbacks.len() != before {
                    let callback = &mut declaration.callbacks[before];
                    callback
                        .template_parameters
                        .extend(pending_templates.iter().cloned());
                    active = Some(ActiveJsDocDefinition::Callback(before));
                    saw_definition = true;
                }
            }
            (_, JsDocTagKind::Typedef) => {
                let before = declaration.typedefs.len();
                apply_jsdoc_tag(arena, source, declaration, tag, diagnostics)?;
                if declaration.typedefs.len() != before {
                    let alias = &mut declaration.typedefs[before];
                    alias
                        .template_parameters
                        .extend(pending_templates.iter().cloned());
                    active = Some(ActiveJsDocDefinition::Typedef(before));
                    saw_definition = true;
                }
            }
            (
                Some(ActiveJsDocDefinition::Callback(index)),
                JsDocTagKind::Parameter | JsDocTagKind::Return | JsDocTagKind::This,
            ) => {
                let is_return = tag.kind() == JsDocTagKind::Return;
                apply_callback_signature_tag(declaration, index, tag);
                if is_return {
                    active = None;
                }
            }
            (Some(ActiveJsDocDefinition::Typedef(index)), JsDocTagKind::Property) => {
                apply_typedef_property_tag(declaration, index, tag);
            }
            (Some(ActiveJsDocDefinition::Typedef(index)), JsDocTagKind::Type) => {
                let alias = &mut declaration.typedefs[index];
                if alias.type_.is_some() {
                    diagnostics.push(canonical_jsdoc_diagnostic(
                        source,
                        jsdoc_tag_name_range(tag)?,
                        8033,
                        std::iter::empty::<String>(),
                    )?);
                } else {
                    alias.type_ = tag.type_expression().map(JsDocTypeExpression::planned);
                }
            }
            _ => {
                active = None;
                apply_jsdoc_tag(arena, source, declaration, tag, diagnostics)?;
            }
        }
    }
    Ok(())
}

fn planned_template_parameters(tag: &JsDocTag<'_>) -> Vec<PlannedJsDocTemplateParameter> {
    tag.template_parameters()
        .iter()
        .map(|parameter| PlannedJsDocTemplateParameter {
            name: parameter.name().text().to_owned(),
            range: parameter.name().range(),
            constraint: parameter.constraint().map(JsDocTypeExpression::planned),
            default_type: parameter.default_type().map(JsDocTypeExpression::planned),
        })
        .collect()
}

fn jsdoc_tag_name_range(tag: &JsDocTag<'_>) -> Result<TextRange, JsDocCommentError> {
    let start = (tag.range().start.get() as usize)
        .checked_add(1)
        .ok_or(JsDocCommentError::SourcePositionOverflow)?;
    let end = start
        .checked_add(tag.tag_name().len())
        .ok_or(JsDocCommentError::SourcePositionOverflow)?;
    checked_range(start, end)
}

fn apply_jsdoc_tag(
    arena: &NodeArena,
    source: NodeRef,
    declaration: &mut PlannedJavaScriptDeclaration,
    tag: &JsDocTag<'_>,
    diagnostics: &mut Vec<CanonicalCheckerDiagnostic>,
) -> Result<(), JsDocCommentError> {
    match tag.kind() {
        JsDocTagKind::Type => {
            declaration.type_ = tag.type_expression().map(JsDocTypeExpression::planned);
        }
        JsDocTagKind::Parameter => {
            let identity = tag
                .name()
                .map(|name| (name.text().to_owned(), name.range()))
                .or_else(|| {
                    positional_jsdoc_parameter(
                        arena,
                        declaration.node,
                        declaration.parameters.len(),
                    )
                });
            if let Some((name, range)) = identity {
                declaration.parameters.push(PlannedJsDocParameter {
                    name,
                    range,
                    type_: tag.type_expression().map(JsDocTypeExpression::planned),
                    optional: tag.is_optional(),
                    name_first: tag.is_name_first(),
                });
            }
        }
        JsDocTagKind::Return => {
            declaration.return_type = tag.type_expression().map(JsDocTypeExpression::planned);
        }
        JsDocTagKind::Typedef => {
            if let Some(name) = tag.name() {
                declaration.typedefs.push(PlannedJsDocTypedef {
                    name: name.text().to_owned(),
                    range: name.range(),
                    type_: tag.type_expression().map(JsDocTypeExpression::planned),
                    properties: Vec::new(),
                    template_parameters: Vec::new(),
                });
            }
        }
        JsDocTagKind::Callback => {
            if let Some(name) = tag.name() {
                declaration.callbacks.push(PlannedJsDocCallback {
                    name: name.text().to_owned(),
                    range: name.range(),
                    parameters: Vec::new(),
                    return_type: None,
                    this_type: None,
                    template_parameters: Vec::new(),
                });
            }
        }
        JsDocTagKind::Property | JsDocTagKind::Template => {}
        JsDocTagKind::Satisfies => {
            if let Some(annotation) = tag.type_expression() {
                declaration.satisfies = Some(PlannedJsDocSatisfies {
                    range: jsdoc_tag_name_range(tag)?,
                    type_: annotation.planned(),
                });
            }
        }
        JsDocTagKind::This => {
            declaration.this_type = tag.type_expression().map(JsDocTypeExpression::planned);
        }
        JsDocTagKind::Augments => {
            if let Some(annotation) = tag.type_expression() {
                append_augments_diagnostic(arena, source, declaration.node, tag, diagnostics)?;
                declaration.augments_type = Some(annotation.planned());
            }
        }
    }
    Ok(())
}

fn apply_callback_signature_tag(
    declaration: &mut PlannedJavaScriptDeclaration,
    index: usize,
    tag: &JsDocTag<'_>,
) {
    let Some(callback) = declaration.callbacks.get_mut(index) else {
        return;
    };
    match tag.kind() {
        JsDocTagKind::Parameter => {
            if let Some(name) = tag.name() {
                callback.parameters.push(PlannedJsDocParameter {
                    name: name.text().to_owned(),
                    range: name.range(),
                    type_: tag.type_expression().map(JsDocTypeExpression::planned),
                    optional: tag.is_optional(),
                    name_first: tag.is_name_first(),
                });
            }
        }
        JsDocTagKind::Return => {
            callback.return_type = tag.type_expression().map(JsDocTypeExpression::planned);
        }
        JsDocTagKind::This => {
            callback.this_type = tag.type_expression().map(JsDocTypeExpression::planned);
        }
        _ => {}
    }
}

fn apply_typedef_property_tag(
    declaration: &mut PlannedJavaScriptDeclaration,
    index: usize,
    tag: &JsDocTag<'_>,
) {
    let Some(alias) = declaration.typedefs.get_mut(index) else {
        return;
    };
    let Some(name) = tag.name() else {
        return;
    };
    alias.properties.push(PlannedJsDocProperty {
        name: name.text().to_owned(),
        range: name.range(),
        type_: tag.type_expression().map(JsDocTypeExpression::planned),
        optional: tag.is_optional(),
    });
}

fn append_unmatched_parameter_diagnostics(
    arena: &NodeArena,
    source: NodeRef,
    declaration: &PlannedJavaScriptDeclaration,
    diagnostics: &mut Vec<CanonicalCheckerDiagnostic>,
) -> Result<(), JsDocCommentError> {
    let Some(parameters) = javascript_callable_parameters(arena, declaration.node)? else {
        return Ok(());
    };
    let mut names = HashSet::new();
    let mut excluded = HashSet::new();
    for (index, parameter) in parameters.nodes.iter().enumerate() {
        let Some(parameter) = arena.get(*parameter) else {
            return Err(JsDocCommentError::InvalidSourceNode(declaration.node));
        };
        let NodeData::ParameterDeclaration(parameter) = &parameter.data else {
            return Err(JsDocCommentError::InvalidSourceNode(declaration.node));
        };
        match arena.get(parameter.name).map(|name| &name.data) {
            Some(NodeData::Identifier(name)) => {
                names.insert(name.text.as_str());
            }
            Some(_) => {
                excluded.insert(index);
            }
            None => return Err(JsDocCommentError::InvalidSourceNode(declaration.node)),
        }
    }

    for (index, parameter) in declaration.parameters.iter().enumerate() {
        if excluded.contains(&index) || names.contains(parameter.name.as_str()) {
            continue;
        }
        if let Some((left, _)) = parameter.name.rsplit_once('.') {
            diagnostics.push(canonical_jsdoc_diagnostic(
                source,
                parameter.range,
                8032,
                [parameter.name.clone(), left.to_owned()],
            )?);
        } else if !parameter.name_first {
            diagnostics.push(canonical_jsdoc_diagnostic(
                source,
                parameter.range,
                8024,
                [parameter.name.clone()],
            )?);
        }
    }
    Ok(())
}

fn javascript_callable_parameters(
    arena: &NodeArena,
    declaration: NodeRef,
) -> Result<Option<&ts_ast::NodeList>, JsDocCommentError> {
    let record = arena
        .get(declaration.node)
        .ok_or(JsDocCommentError::InvalidSourceNode(declaration))?;
    let parameters = match &record.data {
        NodeData::FunctionDeclaration(function) => Some(&function.parameters),
        NodeData::FunctionExpression(function) => Some(&function.parameters),
        NodeData::ArrowFunction(function) => Some(&function.parameters),
        NodeData::MethodDeclaration(function) => Some(&function.parameters),
        NodeData::VariableDeclaration(variable) => {
            let Some(initializer) = variable.initializer else {
                return Ok(None);
            };
            return javascript_callable_parameters(
                arena,
                NodeRef::new(declaration.arena, declaration.file, initializer),
            );
        }
        _ => None,
    };
    Ok(parameters)
}

fn positional_jsdoc_parameter(
    arena: &NodeArena,
    declaration: NodeRef,
    index: usize,
) -> Option<(String, TextRange)> {
    let parameters = javascript_callable_parameters(arena, declaration).ok()??;
    let parameter = arena.get(*parameters.nodes.get(index)?)?;
    let NodeData::ParameterDeclaration(parameter) = &parameter.data else {
        return None;
    };
    let name = arena.get(parameter.name)?;
    let NodeData::Identifier(name_text) = &name.data else {
        return None;
    };
    Some((name_text.text.clone(), name.range))
}

fn append_augments_diagnostic(
    arena: &NodeArena,
    source: NodeRef,
    declaration: NodeRef,
    tag: &JsDocTag<'_>,
    diagnostics: &mut Vec<CanonicalCheckerDiagnostic>,
) -> Result<(), JsDocCommentError> {
    let Some(class) = arena.get(declaration.node) else {
        return Err(JsDocCommentError::InvalidSourceNode(declaration));
    };
    let NodeData::ClassDeclaration(class) = &class.data else {
        return Ok(());
    };
    let Some(annotation) = tag.type_expression() else {
        return Ok(());
    };
    let JsDocType::Named(expected) = annotation.type_() else {
        return Ok(());
    };
    let Some(actual) = class_extends_name(arena, class.heritage_clauses.as_ref()) else {
        return Ok(());
    };
    let expected_name = expected.rsplit('.').next().unwrap_or(expected);
    let actual_name = actual.rsplit('.').next().unwrap_or(&actual);
    if expected_name == actual_name {
        return Ok(());
    }
    let relative_start = annotation
        .text()
        .rfind(expected_name)
        .ok_or(JsDocCommentError::InvalidParserTree(annotation.range()))?;
    let start = (annotation.range().start.get() as usize)
        .checked_add(relative_start)
        .ok_or(JsDocCommentError::SourcePositionOverflow)?;
    let end = start
        .checked_add(expected_name.len())
        .ok_or(JsDocCommentError::SourcePositionOverflow)?;
    diagnostics.push(canonical_jsdoc_diagnostic(
        source,
        checked_range(start, end)?,
        8023,
        [
            tag.tag_name().to_owned(),
            expected_name.to_owned(),
            actual_name.to_owned(),
        ],
    )?);
    Ok(())
}

fn class_extends_name(arena: &NodeArena, clauses: Option<&ts_ast::NodeList>) -> Option<String> {
    let clauses = clauses?;
    for clause in &clauses.nodes {
        let NodeData::HeritageClause(clause) = &arena.get(*clause)?.data else {
            continue;
        };
        if clause.token != SyntaxKind::ExtendsKeyword {
            continue;
        }
        let [base] = clause.types.nodes.as_slice() else {
            return None;
        };
        let NodeData::ExpressionWithTypeArguments(base) = &arena.get(*base)?.data else {
            return None;
        };
        return property_expression_name(arena, base.expression);
    }
    None
}

fn property_expression_name(arena: &NodeArena, node: NodeId) -> Option<String> {
    match &arena.get(node)?.data {
        NodeData::Identifier(name) => Some(name.text.clone()),
        NodeData::QualifiedName(_) => qualified_type_name(arena, node),
        NodeData::PropertyAccessExpression(property) => {
            let owner = property_expression_name(arena, property.expression)?;
            let NodeData::Identifier(name) = &arena.get(property.name)?.data else {
                return None;
            };
            Some(format!("{owner}.{}", name.text))
        }
        _ => None,
    }
}

fn canonical_parser_diagnostic(
    source: NodeRef,
    diagnostic: &Diagnostic,
) -> Result<CanonicalCheckerDiagnostic, JsDocCommentError> {
    let Some(code) = diagnostic.code else {
        return Err(JsDocCommentError::UnsupportedParserDiagnostic {
            code: None,
            range: diagnostic.range,
        });
    };
    let message = message_by_code(code).ok_or(JsDocCommentError::UnsupportedParserDiagnostic {
        code: Some(code),
        range: diagnostic.range,
    })?;
    let arguments = if message
        .format(&[])
        .is_ok_and(|text| text == diagnostic.message)
    {
        Vec::new()
    } else if code == 1005 {
        let token = diagnostic
            .message
            .strip_prefix('\'')
            .and_then(|text| text.strip_suffix("' expected."))
            .ok_or(JsDocCommentError::UnsupportedParserDiagnostic {
                code: Some(code),
                range: diagnostic.range,
            })?;
        vec![token.to_owned()]
    } else {
        return Err(JsDocCommentError::UnsupportedParserDiagnostic {
            code: Some(code),
            range: diagnostic.range,
        });
    };
    canonical_jsdoc_diagnostic(source, diagnostic.range, code, arguments)
}

fn canonical_jsdoc_diagnostic(
    source: NodeRef,
    range: TextRange,
    code: u32,
    arguments: impl IntoIterator<Item = impl Into<String>>,
) -> Result<CanonicalCheckerDiagnostic, JsDocCommentError> {
    if range.is_empty() {
        return Err(JsDocCommentError::UnsupportedParserDiagnostic {
            code: Some(code),
            range,
        });
    }
    let message = message_by_code(code).ok_or(JsDocCommentError::UnsupportedParserDiagnostic {
        code: Some(code),
        range,
    })?;
    Ok(CanonicalCheckerDiagnostic {
        node: Some(source),
        range_override: Some(CanonicalCheckerDiagnosticRange::new(source, range)),
        diagnostic: CheckerDiagnostic::with_arguments(message, arguments),
        related_information: Vec::new(),
    })
}

fn tag_kind(name: &str) -> Option<JsDocTagKind> {
    match name {
        "type" => Some(JsDocTagKind::Type),
        "param" | "arg" | "argument" => Some(JsDocTagKind::Parameter),
        "property" | "prop" => Some(JsDocTagKind::Property),
        "return" | "returns" => Some(JsDocTagKind::Return),
        "typedef" => Some(JsDocTagKind::Typedef),
        "callback" => Some(JsDocTagKind::Callback),
        "template" => Some(JsDocTagKind::Template),
        "satisfies" => Some(JsDocTagKind::Satisfies),
        "this" => Some(JsDocTagKind::This),
        "extends" | "augments" => Some(JsDocTagKind::Augments),
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
        if !matches!(name, "type" | "return" | "extends" | "satisfies" | "this")
            || tags.iter().any(|existing| existing.start == start)
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
    tag: ScannedTag<'source>,
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
    let mut template_parameters = Vec::new();
    let mut name = None;
    let mut name_first = false;
    let mut bracketed = false;

    if source.as_bytes().get(cursor) == Some(&b'{') {
        let (parsed, next) = parse_braced_type(source, cursor, absolute_end, diagnostics)?;
        type_expression = parsed;
        cursor = skip_doc_whitespace(source, next, absolute_end);
    } else if matches!(
        kind,
        JsDocTagKind::Parameter
            | JsDocTagKind::Property
            | JsDocTagKind::Typedef
            | JsDocTagKind::Callback
            | JsDocTagKind::Template
    ) {
        name_first = matches!(kind, JsDocTagKind::Parameter | JsDocTagKind::Property);
    } else if cursor < absolute_end {
        let type_end = unbraced_type_end(source, cursor, absolute_end);
        type_expression = parse_type_expression(source, cursor, type_end, diagnostics)?;
        cursor = skip_doc_whitespace(source, type_end, absolute_end);
    } else if matches!(
        kind,
        JsDocTagKind::Type | JsDocTagKind::Augments | JsDocTagKind::Satisfies | JsDocTagKind::This
    ) {
        diagnostics.push(type_expected_diagnostic(source, cursor, absolute_end)?);
    }

    if kind == JsDocTagKind::Template {
        template_parameters = parse_template_parameters(
            source,
            cursor,
            absolute_end,
            type_expression.as_ref(),
            diagnostics,
        )?;
        name = template_parameters
            .first()
            .map(JsDocTemplateParameter::name);
    } else if matches!(
        kind,
        JsDocTagKind::Parameter
            | JsDocTagKind::Property
            | JsDocTagKind::Typedef
            | JsDocTagKind::Callback
    ) {
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
        tag_name: tag.name,
        range: checked_range(absolute_start, absolute_end)?,
        name,
        type_expression,
        template_parameters,
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

fn parse_template_parameters<'source>(
    source: &'source str,
    mut cursor: usize,
    end: usize,
    constraint: Option<&JsDocTypeExpression<'source>>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Result<Vec<JsDocTemplateParameter<'source>>, JsDocCommentError> {
    let mut parameters = Vec::new();
    loop {
        cursor = skip_doc_whitespace(source, cursor, end);
        if cursor >= end {
            break;
        }
        let bracketed = source.as_bytes().get(cursor) == Some(&b'[');
        let content_start = if bracketed {
            skip_doc_whitespace(source, cursor + 1, end)
        } else {
            cursor
        };
        let mut name_start = content_start;
        if source
            .get(name_start..end)
            .is_some_and(|remaining| remaining.starts_with("const "))
        {
            name_start = skip_doc_whitespace(source, name_start + "const".len(), end);
        }
        let name_end = template_name_end(source, name_start, end);
        if name_start == name_end {
            diagnostics.push(expected_diagnostic(source, name_start, end, 1003, &[])?);
            break;
        }
        let name = JsDocTagName {
            text: source
                .get(name_start..name_end)
                .ok_or(JsDocCommentError::SourcePositionOverflow)?,
            range: checked_range(name_start, name_end)?,
        };
        let mut default_type = None;
        cursor = name_end;
        if bracketed {
            cursor = skip_doc_whitespace(source, cursor, end);
            if source.as_bytes().get(cursor) != Some(&b'=') {
                diagnostics.push(expected_token_diagnostic(source, cursor, end, "=")?);
                break;
            }
            let default_start = skip_doc_whitespace(source, cursor + 1, end);
            let Some(close) =
                matching_template_bracket(source, content_start.saturating_sub(1), end)
            else {
                diagnostics.push(expected_token_diagnostic(source, end, end, "]")?);
                break;
            };
            let (default_start, default_end) = trimmed_range(source, default_start, close);
            if default_start == default_end {
                diagnostics.push(type_expected_diagnostic(source, close, end)?);
                break;
            }
            default_type = parse_type_expression(source, default_start, default_end, diagnostics)?;
            cursor = close + 1;
        }
        parameters.push(JsDocTemplateParameter {
            name,
            constraint: (parameters.is_empty())
                .then(|| constraint.cloned())
                .flatten(),
            default_type,
        });
        let next = skip_doc_whitespace(source, cursor, end);
        if source.as_bytes().get(next) != Some(&b',') {
            break;
        }
        cursor = next + 1;
    }
    Ok(parameters)
}

fn template_name_end(source: &str, start: usize, end: usize) -> usize {
    let Some(remaining) = source.get(start..end) else {
        return start;
    };
    let mut result = start;
    for character in remaining.chars() {
        if !character.is_alphanumeric() && !matches!(character, '_' | '$') {
            break;
        }
        result += character.len_utf8();
    }
    result
}

fn matching_template_bracket(source: &str, open: usize, end: usize) -> Option<usize> {
    let bytes = source.as_bytes();
    if bytes.get(open) != Some(&b'[') {
        return None;
    }
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
            b'[' => depth = depth.checked_add(1)?,
            b']' => {
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
                (NodeData::Identifier(name), Some(arguments))
                    if matches!(name.text.as_str(), "Array" | "ReadonlyArray")
                        && arguments.nodes.len() == 1 =>
                {
                    let element = project_type(arena, arguments.nodes[0], range)?;
                    if name.text == "ReadonlyArray" {
                        JsDocType::ReadonlyArray(Box::new(element))
                    } else {
                        JsDocType::Array(Box::new(element))
                    }
                }
                (NodeData::QualifiedName(_), None) => qualified_type_name(arena, data.type_name)
                    .map(JsDocType::Named)
                    .ok_or(JsDocCommentError::InvalidParserTree(range))?,
                _ => JsDocType::Unsupported(record.kind),
            }
        }
        NodeData::LiteralTypeNode(data) => {
            let Some(literal) = arena.get(data.literal) else {
                return Err(JsDocCommentError::InvalidParserTree(range));
            };
            match &literal.data {
                NodeData::KeywordExpression(_) if literal.kind == SyntaxKind::NullKeyword => {
                    JsDocType::Intrinsic(JsDocIntrinsicType::Null)
                }
                NodeData::KeywordExpression(_) if literal.kind == SyntaxKind::TrueKeyword => {
                    JsDocType::Intrinsic(JsDocIntrinsicType::True)
                }
                NodeData::KeywordExpression(_) if literal.kind == SyntaxKind::FalseKeyword => {
                    JsDocType::Intrinsic(JsDocIntrinsicType::False)
                }
                NodeData::StringLiteral(value) => JsDocType::StringLiteral(value.text.clone()),
                NodeData::NumericLiteral(value) => JsDocType::NumberLiteral(value.text.clone()),
                NodeData::BigIntLiteral(value) => JsDocType::BigIntLiteral(value.text.clone()),
                NodeData::PrefixUnaryExpression(prefix)
                    if prefix.operator == SyntaxKind::MinusToken =>
                {
                    let Some(operand) = arena.get(prefix.operand) else {
                        return Err(JsDocCommentError::InvalidParserTree(range));
                    };
                    match &operand.data {
                        NodeData::NumericLiteral(value) => {
                            JsDocType::NumberLiteral(format!("-{}", value.text))
                        }
                        NodeData::BigIntLiteral(value) => {
                            JsDocType::BigIntLiteral(format!("-{}", value.text))
                        }
                        _ => JsDocType::Unsupported(record.kind),
                    }
                }
                _ => JsDocType::Unsupported(record.kind),
            }
        }
        _ => JsDocType::Unsupported(record.kind),
    };
    Ok(type_)
}

fn qualified_type_name(arena: &NodeArena, node: NodeId) -> Option<String> {
    match &arena.get(node)?.data {
        NodeData::Identifier(name) => Some(name.text.clone()),
        NodeData::QualifiedName(qualified) => {
            let left = qualified_type_name(arena, qualified.left)?;
            let NodeData::Identifier(right) = &arena.get(qualified.right)?.data else {
                return None;
            };
            Some(format!("{left}.{}", right.text))
        }
        _ => None,
    }
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
        JsDocType::BoundTypeParameter(type_) => Ok(*type_),
        JsDocType::GenericReference { .. } => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::TypeReference,
            range,
        }),
        JsDocType::Import(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::ImportType,
            range,
        }),
        JsDocType::ObjectLiteral(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::TypeLiteral,
            range,
        }),
        JsDocType::Function(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::FunctionType,
            range,
        }),
        JsDocType::IndexedAccess { .. } => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::IndexedAccessType,
            range,
        }),
        JsDocType::KeyOf(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::TypeOperator,
            range,
        }),
        JsDocType::StringLiteral(_) | JsDocType::NumberLiteral(_) | JsDocType::BigIntLiteral(_) => {
            Err(JsDocTypeResolutionError::UnsupportedType {
                kind: SyntaxKind::LiteralType,
                range,
            })
        }
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
        JsDocType::Array(_) | JsDocType::ReadonlyArray(_) => {
            Err(JsDocTypeResolutionError::UnsupportedType {
                kind: SyntaxKind::ArrayType,
                range,
            })
        }
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
        JsDocType::Intrinsic(_) | JsDocType::StringLiteral(_) => Ok(()),
        JsDocType::BoundTypeParameter(type_) => {
            if store.type_payload(*type_).is_some_and(|record| {
                record
                    .flags()
                    .contains(super::types::TypeFlags::TYPE_PARAMETER)
            }) {
                Ok(())
            } else {
                Err(JsDocTypeResolutionError::InvalidGlobalType(*type_))
            }
        }
        JsDocType::GenericReference { .. } => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::TypeReference,
            range,
        }),
        JsDocType::Import(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::ImportType,
            range,
        }),
        JsDocType::ObjectLiteral(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::TypeLiteral,
            range,
        }),
        JsDocType::Function(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::FunctionType,
            range,
        }),
        JsDocType::IndexedAccess { .. } => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::IndexedAccessType,
            range,
        }),
        JsDocType::KeyOf(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::TypeOperator,
            range,
        }),
        JsDocType::NumberLiteral(value) => {
            let number = ts_jsnum::from_string(value);
            if number.is_nan() {
                Err(JsDocTypeResolutionError::LiteralConstruction(range))
            } else {
                Ok(())
            }
        }
        JsDocType::BigIntLiteral(value) => {
            let body = value.strip_prefix('-').unwrap_or(value);
            if super::type_nodes::normalize_bigint_literal(body).is_none() {
                Err(JsDocTypeResolutionError::LiteralConstruction(range))
            } else {
                Ok(())
            }
        }
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
        | JsDocType::Array(inner)
        | JsDocType::ReadonlyArray(inner) => {
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
        JsDocType::BoundTypeParameter(type_) => Ok(*type_),
        JsDocType::GenericReference { .. } => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::TypeReference,
            range,
        }),
        JsDocType::Import(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::ImportType,
            range,
        }),
        JsDocType::ObjectLiteral(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::TypeLiteral,
            range,
        }),
        JsDocType::Function(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::FunctionType,
            range,
        }),
        JsDocType::IndexedAccess { .. } => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::IndexedAccessType,
            range,
        }),
        JsDocType::KeyOf(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::TypeOperator,
            range,
        }),
        JsDocType::StringLiteral(value) => store
            .regular_string_literal_type(value.clone())
            .map_err(|_| JsDocTypeResolutionError::LiteralConstruction(range)),
        JsDocType::NumberLiteral(value) => store
            .regular_number_literal_type(Number::from_string(value))
            .map_err(|_| JsDocTypeResolutionError::LiteralConstruction(range)),
        JsDocType::BigIntLiteral(value) => store
            .regular_bigint_literal_type(PseudoBigInt::parse_valid(value))
            .map_err(|_| JsDocTypeResolutionError::LiteralConstruction(range)),
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
        JsDocType::ReadonlyArray(inner) => {
            let inner = resolve_complete_type(store, global_types, options, inner, range)?;
            store
                .create_canonical_array_type(global_types, inner, true)
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
    use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

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

    #[test]
    fn local_scalar_typedef_aliases_preserve_spelling_and_resolve_canonical_types() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @typedef {number} NS.Base */\n",
            "/** @typedef {NS.Base} NS.Count */\n",
            "/** @type {NS.Count | string} */\n",
            "const value = 1;",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let source = NodeRef::new(
            javascript.arena.id(),
            FileId::new(81),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, source).unwrap();
        let [declaration] = plan.declarations() else {
            panic!("expected one annotated declaration")
        };
        let annotation = declaration.type_().unwrap();
        assert_eq!(
            annotation.type_(),
            &JsDocType::Union(vec![
                JsDocType::Named("NS.Count".to_owned()),
                JsDocType::Intrinsic(JsDocIntrinsicType::String),
            ])
        );

        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        let cold = context.store().type_len();
        preflight_planned_jsdoc_type(context.store(), &globals, options, annotation).unwrap();
        assert_eq!(context.store().type_len(), cold);

        let resolved =
            resolve_planned_jsdoc_type(context.store_mut_for_test(), &globals, options, annotation)
                .unwrap();
        assert_eq!(context.type_to_string(resolved).unwrap(), "string | number");
    }

    #[test]
    fn duplicate_cyclic_and_non_scalar_typedefs_remain_typed_boundaries() {
        for source in [
            concat!(
                "/** @typedef {number} Value */\n",
                "/** @typedef {string} Value */\n",
                "/** @type {Value} */\n",
                "const value = 1;",
            ),
            concat!(
                "/** @typedef {Next} Value */\n",
                "/** @typedef {Value} Next */\n",
                "/** @type {Value} */\n",
                "const value = 1;",
            ),
            concat!(
                "/** @typedef {string | number} Value */\n",
                "/** @type {Value} */\n",
                "const value = 1;",
            ),
        ] {
            let javascript = parse_javascript_source_file(source);
            assert!(
                javascript.diagnostics.is_empty(),
                "{:?}",
                javascript.diagnostics
            );
            let root = NodeRef::new(
                javascript.arena.id(),
                FileId::new(82),
                javascript.source_file,
            );
            let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
            let annotation = plan.declarations()[0].type_().unwrap();
            let parsed = parse_source_file("const marker = 1;");
            let options = CanonicalCheckerOptions::default();
            let context = context(&parsed, options);
            let cold = context.store().type_len();
            assert_eq!(
                preflight_planned_jsdoc_type(
                    context.store(),
                    context.global_types(),
                    options,
                    annotation,
                ),
                Err(JsDocTypeResolutionError::UnresolvedTypeReference {
                    name: "Value".to_owned(),
                    range: annotation.range(),
                })
            );
            assert_eq!(context.store().type_len(), cold);
        }
    }

    #[test]
    fn jsdoc_string_number_and_bigint_literals_use_exact_canonical_identities() {
        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        for (source, expected) in [
            ("/** @type {'ready'} */", "\"ready\""),
            ("/** @type {42} */", "42"),
            ("/** @type {-2} */", "-2"),
            ("/** @type {3n} */", "3n"),
            ("/** @type {-4n} */", "-4n"),
        ] {
            let comment = type_tag(source);
            assert!(
                comment.diagnostics().is_empty(),
                "{:?}",
                comment.diagnostics()
            );
            let annotation = comment.type_tag().unwrap().type_expression().unwrap();
            let resolved =
                resolve_jsdoc_type(context.store_mut_for_test(), &globals, options, annotation)
                    .unwrap();
            assert_eq!(context.type_to_string(resolved).unwrap(), expected);
        }
    }

    #[test]
    fn generic_jsdoc_array_spellings_use_exact_mutable_and_readonly_targets() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> { length: number; } ",
            "interface ReadonlyArray<T> { readonly length: number; } ",
            "const marker = 1;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        for (source, expected_target) in [
            ("/** @type {Array<string>} */", globals.array_type),
            (
                "/** @type {ReadonlyArray<number>} */",
                globals.readonly_array_type,
            ),
        ] {
            let comment = type_tag(source);
            assert!(
                comment.diagnostics().is_empty(),
                "{:?}",
                comment.diagnostics()
            );
            let annotation = comment.type_tag().unwrap().type_expression().unwrap();
            let resolved =
                resolve_jsdoc_type(context.store_mut_for_test(), &globals, options, annotation)
                    .unwrap();
            let payload = context.store().type_payload(resolved).unwrap();
            let super::super::TypeData::TypeReference(reference) = payload.data() else {
                panic!("expected an exact global array reference")
            };
            assert_eq!(reference.object.target, Some(expected_target));
        }
    }

    #[test]
    fn nameless_jsdoc_parameters_bind_to_the_matching_callable_position() {
        for (source, expected) in [
            (
                "/** @param {string} */ function read(value) {}",
                JsDocIntrinsicType::String,
            ),
            (
                "/** @param {number} */ const read = value => value;",
                JsDocIntrinsicType::Number,
            ),
        ] {
            let javascript = parse_javascript_source_file(source);
            assert!(
                javascript.diagnostics.is_empty(),
                "{:?}",
                javascript.diagnostics
            );
            let root = NodeRef::new(
                javascript.arena.id(),
                FileId::new(83),
                javascript.source_file,
            );
            let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
            assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
            let declaration = &plan.declarations()[0];
            let parameter = declaration.parameter("value").unwrap();
            assert_eq!(
                parameter.type_().unwrap().type_(),
                &JsDocType::Intrinsic(expected)
            );
            if let Some((node, _)) = javascript
                .arena
                .iter()
                .find(|(_, record)| record.kind == SyntaxKind::ArrowFunction)
            {
                let callable = NodeRef::new(javascript.arena.id(), root.file, node);
                assert_eq!(
                    plan.callable_declaration(&javascript.arena, callable)
                        .map(PlannedJavaScriptDeclaration::node),
                    Some(declaration.node())
                );
            }
        }
    }

    #[test]
    fn callback_signature_tags_do_not_become_host_function_parameters() {
        for declaration in ["function f1() {}", "export function f1() {}"] {
            let source = format!(
                "/**\n * @callback Foo\n * @param {{string}} x\n * @returns {{number}}\n */\n{declaration}"
            );
            let javascript = parse_javascript_source_file(&source);
            assert!(
                javascript.diagnostics.is_empty(),
                "{:?}",
                javascript.diagnostics
            );
            let root = NodeRef::new(
                javascript.arena.id(),
                FileId::new(84),
                javascript.source_file,
            );
            let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
            assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
            let [host] = plan.declarations() else {
                panic!("expected one callback-hosting declaration")
            };
            assert!(host.parameters().is_empty());
            assert!(host.return_type().is_none());
            let [callback] = host.callbacks() else {
                panic!("expected one independently owned callback signature")
            };
            assert_eq!(callback.name(), "Foo");
            let [parameter] = callback.parameters() else {
                panic!("expected one callback parameter")
            };
            assert_eq!(parameter.name(), "x");
            assert_eq!(
                parameter.type_().unwrap().type_(),
                &JsDocType::Intrinsic(JsDocIntrinsicType::String)
            );
            assert_eq!(
                callback.return_type().unwrap().type_(),
                &JsDocType::Intrinsic(JsDocIntrinsicType::Number)
            );
        }
    }
}
