//! Parsed `JSDoc` types for the canonical JavaScript checker.
//!
//! The source parser exposes supported top-level typedefs as reparsed source
//! declarations but does not attach structured `JSDoc` tags to their hosts.
//! This module scans those comments and parses each type with the ordinary
//! TypeScript type parser. Its values never retain temporary parser identities.

use std::{
    collections::{HashMap, HashSet},
    fmt,
};

use ts_ast::{NodeArena, NodeData, NodeFlags, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags, semantic::PreparedSymbolTable,
};
use ts_core::{Diagnostic, DiagnosticCategory, TextPos, TextRange};
use ts_diagnostics::{Category, Diagnostic as CheckerDiagnostic, message_by_code};
use ts_jsnum::{Number, PseudoBigInt};
use ts_parser::{parse_jsdoc_comment, parse_source_file};
use ts_scanner::{Scanner, TokenFlags};

use super::{
    ArrayTypeError, CanonicalCheckerDiagnostic, CanonicalCheckerDiagnosticRange,
    CanonicalCheckerOptions, CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost,
    IntrinsicBootstrapOptions, ResolvedSignatureState, SignatureId, SignatureLinks, TypeAliasId,
    TypeId, TypeNodeLinks, ValueSymbolLinks,
    bootstrap::UnionReduction,
    functions::{StoredFunctionTypeValidation, validate_stored_function_type},
    signatures::SignatureFlags,
    store::SourceNodeParent,
    type_records::{ConstrainedTypeData, ObjectTypeData, TypeCacheState, TypeData},
    types::{ObjectFlags, TypeFlags},
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
    Overload,
    Property,
    Template,
    Satisfies,
    This,
    Augments,
    Implements,
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
    Callback(Box<PlannedJsDocCallback>),
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

/// One canonical parameter resolved from a `JSDoc` callable signature.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedJsDocParameter {
    name: String,
    range: TextRange,
    type_: Option<TypeId>,
    optional: bool,
}

impl ResolvedJsDocParameter {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }

    #[must_use]
    pub const fn type_(&self) -> Option<TypeId> {
        self.type_
    }

    #[must_use]
    pub const fn is_optional(&self) -> bool {
        self.optional
    }
}

/// Canonical parameter, return, and receiver identities for a `JSDoc` callable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedJsDocSignature {
    parameters: Vec<ResolvedJsDocParameter>,
    return_type: Option<TypeId>,
    this_type: Option<TypeId>,
}

impl ResolvedJsDocSignature {
    #[must_use]
    pub fn parameters(&self) -> &[ResolvedJsDocParameter] {
        &self.parameters
    }

    #[must_use]
    pub const fn return_type(&self) -> Option<TypeId> {
        self.return_type
    }

    #[must_use]
    pub const fn this_type(&self) -> Option<TypeId> {
        self.this_type
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

    /// Returns the original name of a locally resolved supported typedef.
    #[must_use]
    pub fn resolved_alias_name(&self) -> Option<&str> {
        match (&self.type_, self.resolved_type.as_deref()) {
            (
                JsDocType::Named(name) | JsDocType::GenericReference { name, .. },
                Some(
                    JsDocType::Intrinsic(_)
                    | JsDocType::StringLiteral(_)
                    | JsDocType::NumberLiteral(_)
                    | JsDocType::BigIntLiteral(_)
                    | JsDocType::Parenthesized(_)
                    | JsDocType::Nullable(_)
                    | JsDocType::NonNullable(_)
                    | JsDocType::Optional(_)
                    | JsDocType::Array(_)
                    | JsDocType::ReadonlyArray(_)
                    | JsDocType::Union(_)
                    | JsDocType::ObjectLiteral(_)
                    | JsDocType::Callback(_),
                ),
            ) => Some(name),
            _ => None,
        }
    }

    /// Returns the independently owned signature behind a local callback alias.
    #[must_use]
    pub fn resolved_callback(&self) -> Option<&PlannedJsDocCallback> {
        match self.resolution_type() {
            JsDocType::Callback(callback) => Some(callback),
            _ => None,
        }
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
    overload_tags: Vec<JsDocTag<'source>>,
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

    /// Returns the tags owned by this overload, separate from its host signature.
    #[must_use]
    pub fn overload_tags(&self) -> &[JsDocTag<'source>] {
        &self.overload_tags
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

    #[must_use]
    pub fn satisfies_tag(&self) -> Option<&JsDocTag<'source>> {
        self.tags
            .iter()
            .find(|tag| tag.kind == JsDocTagKind::Satisfies)
    }

    #[must_use]
    pub fn this_tag(&self) -> Option<&JsDocTag<'source>> {
        self.tags.iter().find(|tag| tag.kind == JsDocTagKind::This)
    }

    pub fn template_tags(&self) -> impl Iterator<Item = &JsDocTag<'source>> {
        self.tags
            .iter()
            .filter(|tag| tag.kind == JsDocTagKind::Template)
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

/// A `JSDoc` typedef and its optional source-owned reparsed declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedJsDocTypedef {
    name: String,
    range: TextRange,
    type_: Option<PlannedJsDocType>,
    properties: Vec<PlannedJsDocProperty>,
    template_parameters: Vec<PlannedJsDocTemplateParameter>,
    source_declaration: Option<NodeRef>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceJsDocTypedefIdentity {
    pub(super) owner: NodeRef,
    pub(super) definition: PlannedJsDocTypedef,
    shape: SourceJsDocTypedefShape,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceJsDocCallbackIdentity {
    pub(super) owner: NodeRef,
    pub(super) definition: PlannedJsDocCallback,
    pub(super) signature: SignatureId,
    object: ObjectTypeData,
    parameters: Vec<SourceJsDocTypedefProperty>,
    return_type: TypeId,
}

impl SourceJsDocCallbackIdentity {
    pub(super) fn has_parameter(&self, symbol: SemanticSymbolId) -> bool {
        self.parameters
            .iter()
            .any(|parameter| parameter.symbol == symbol)
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct SourceJsDocTypedefShape {
    objects: Vec<SourceJsDocTypedefObject>,
    unions: Vec<(TypeId, Vec<TypeId>)>,
    references: Vec<SourceJsDocTypedefReference>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceJsDocTypedefReference {
    type_: TypeId,
    target: Option<TypeId>,
    arguments: Option<Vec<TypeId>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceJsDocTypedefObject {
    type_: TypeId,
    flags: TypeFlags,
    object_flags: ObjectFlags,
    symbol: Option<SemanticSymbolId>,
    alias: Option<TypeAliasId>,
    object: ObjectTypeData,
    members: Option<ts_binder::semantic::SymbolTable>,
    properties: Vec<SourceJsDocTypedefProperty>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceJsDocTypedefProperty {
    symbol: SemanticSymbolId,
    record: ts_binder::semantic::Symbol,
    links: ValueSymbolLinks,
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

    /// Returns the authenticated source declaration for a reparsed typedef.
    #[must_use]
    pub const fn source_declaration(&self) -> Option<NodeRef> {
        self.source_declaration
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
    implements_types: Vec<PlannedJsDocType>,
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

    #[must_use]
    pub fn implements_types(&self) -> &[PlannedJsDocType] {
        &self.implements_types
    }
}

/// The complete owned `JSDoc` plan for one JavaScript source file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedJavaScriptJsDoc {
    declarations: Vec<PlannedJavaScriptDeclaration>,
    expressions: Vec<PlannedJsDocArrowExpression>,
    diagnostics: Vec<CanonicalCheckerDiagnostic>,
}

/// One inline `@type` assertion on a source-owned parenthesized arrow body.
#[derive(Clone, Debug, Eq, PartialEq)]
struct PlannedJsDocArrowExpression {
    node: NodeRef,
    callable: NodeRef,
    declaration: NodeRef,
    type_: PlannedJsDocType,
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

    /// Finds the inline `@type` assertion owned by one arrow-body expression.
    #[must_use]
    pub fn expression_type(&self, node: NodeRef) -> Option<&PlannedJsDocType> {
        self.expressions
            .iter()
            .find(|expression| expression.node == node)
            .map(|expression| &expression.type_)
    }

    pub(super) fn expression_annotations(
        &self,
    ) -> impl Iterator<Item = (NodeRef, NodeRef, NodeRef, &PlannedJsDocType)> {
        self.expressions.iter().map(|expression| {
            (
                expression.node,
                expression.callable,
                expression.declaration,
                &expression.type_,
            )
        })
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

/// Invalid source provenance, an inconsistent parse, or an unsupported declaration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum JsDocCommentError {
    InvalidCommentRange(TextRange),
    InvalidCommentSyntax(TextRange),
    InvalidParserTree(TextRange),
    InvalidSourceNode(NodeRef),
    MissingSourceText(NodeRef),
    UnsupportedOverloadDeclaration(NodeRef),
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
            Self::UnsupportedOverloadDeclaration(node) => {
                write!(
                    formatter,
                    "JSDoc overload declarations are not supported for {node:?}"
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
    InvalidTypeParameterBinding {
        name: String,
        type_: TypeId,
    },
    DuplicateTypeParameterBinding(String),
    UnsupportedType {
        kind: SyntaxKind,
        range: TextRange,
    },
    InvalidGlobalType(TypeId),
    LiteralConstruction(TextRange),
    ObjectConstruction(TextRange),
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
            Self::InvalidTypeParameterBinding { name, type_ } => {
                write!(
                    formatter,
                    "JSDoc template parameter '{name}' has invalid type {type_:?}"
                )
            }
            Self::DuplicateTypeParameterBinding(name) => {
                write!(formatter, "JSDoc template parameter '{name}' is duplicated")
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
            Self::ObjectConstruction(range) => {
                write!(
                    formatter,
                    "JSDoc object type could not be created at {range:?}"
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
    let mut comment_lexer = Scanner::new(comment);
    comment_lexer.set_skip_trivia(false);
    let token = comment_lexer.scan();
    if token.kind != SyntaxKind::MultiLineCommentTrivia
        || token.text != comment
        || token.flags.contains(TokenFlags::UNTERMINATED)
    {
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
    let mut overload_children = 0;
    for (index, tag) in scanned.iter().enumerate() {
        if overload_children > 0 {
            overload_children -= 1;
            continue;
        }
        let Some(kind) = tag_kind(tag.name) else {
            continue;
        };
        let tag_end = scanned
            .get(index + 1)
            .map_or(comment_end, |next| next.start);
        let mut parsed_tag =
            parse_supported_tag(source, start, *tag, tag_end, kind, &mut diagnostics)?;
        if kind == JsDocTagKind::Overload {
            parsed_tag.overload_tags = parse_overload_signature_tags(
                source,
                start,
                &scanned[index + 1..],
                comment_end,
                &mut diagnostics,
            )?;
            overload_children = parsed_tag.overload_tags.len();
            if let Some(last) = parsed_tag.overload_tags.last() {
                parsed_tag.range.end = last.range.end;
            }
        }
        tags.push(parsed_tag);
    }

    Ok(ParsedJsDocComment {
        range,
        tags,
        diagnostics,
    })
}

fn parse_overload_signature_tags<'source>(
    source: &'source str,
    comment_start: usize,
    scanned: &[ScannedTag<'source>],
    comment_end: usize,
    diagnostics: &mut Vec<Diagnostic>,
) -> Result<Vec<JsDocTag<'source>>, JsDocCommentError> {
    let mut tags = Vec::new();
    for (index, tag) in scanned.iter().copied().enumerate() {
        let Some(
            kind @ (JsDocTagKind::Parameter
            | JsDocTagKind::This
            | JsDocTagKind::Template
            | JsDocTagKind::Return),
        ) = tag_kind(tag.name)
        else {
            break;
        };
        let end = scanned
            .get(index + 1)
            .map_or(comment_end, |next| next.start);
        let parsed = parse_supported_tag(source, comment_start, tag, end, kind, diagnostics)?;
        if kind == JsDocTagKind::Template {
            let range = jsdoc_tag_name_range(&parsed)?;
            let mut diagnostic = expected_diagnostic(
                source,
                range.start.get() as usize,
                range.end.get() as usize,
                8039,
                &[],
            )?;
            diagnostic.range = range;
            diagnostics.push(diagnostic);
        }
        tags.push(parsed);
        // The pinned parseJSDocSignature consumes at most one return tag.
        if kind == JsDocTagKind::Return {
            break;
        }
    }
    Ok(tags)
}

/// Finds and parses the last `JSDoc` comment in a source node's leading trivia.
///
/// # Errors
///
/// Returns an error when the node does not belong to `arena`, its source text
/// is unavailable, or the comment parser returns inconsistent source ranges.
pub fn leading_jsdoc_comment(
    arena: &NodeArena,
    node: NodeRef,
) -> Result<Option<ParsedJsDocComment<'_>>, JsDocCommentError> {
    let comments = LeadingJsDocComments::new(arena, node)?;
    comments.last(node)
}

/// Returns all `JSDoc` comments in a source node's leading trivia in source order.
///
/// # Errors
///
/// Returns an error when the node or any retained comment has invalid source
/// provenance.
pub fn leading_jsdoc_comments(
    arena: &NodeArena,
    node: NodeRef,
) -> Result<Vec<ParsedJsDocComment<'_>>, JsDocCommentError> {
    let comments = LeadingJsDocComments::new(arena, node)?;
    comments.all(node)
}

struct LeadingJsDocComments<'arena> {
    arena: &'arena NodeArena,
    source: &'arena str,
    source_node_ends: Vec<TextPos>,
}

impl<'arena> LeadingJsDocComments<'arena> {
    fn new(arena: &'arena NodeArena, node: NodeRef) -> Result<Self, JsDocCommentError> {
        let invalid = || JsDocCommentError::InvalidSourceNode(node);
        if node.arena != arena.id() {
            return Err(invalid());
        }
        let source = arena
            .source_text()
            .ok_or(JsDocCommentError::MissingSourceText(node))?;
        let mut root = node.node;
        let mut remaining = arena.len();
        while let Some(parent) = arena.get(root).ok_or_else(invalid)?.parent {
            remaining = remaining.checked_sub(1).ok_or_else(invalid)?;
            root = parent;
        }

        let mut source_node_ends = Vec::new();
        let mut pending = vec![root];
        let mut remaining = arena.len();
        while let Some(current) = pending.pop() {
            remaining = remaining.checked_sub(1).ok_or_else(invalid)?;
            let record = arena.get(current).ok_or_else(invalid)?;
            // Reparsed annotations and their children are inside comments, not source code.
            if record.flags.0 & NodeFlags::REPARSED.0 != 0 {
                continue;
            }
            if record.range.start < record.range.end {
                source_node_ends.push(record.range.end);
            }
            record.for_each_child(|child| pending.push(child));
        }
        source_node_ends.sort_unstable();
        source_node_ends.dedup();
        Ok(Self {
            arena,
            source,
            source_node_ends,
        })
    }

    fn ranges(&self, node: NodeRef) -> Result<Vec<TextRange>, JsDocCommentError> {
        let invalid = || JsDocCommentError::InvalidSourceNode(node);
        if node.arena != self.arena.id() {
            return Err(invalid());
        }
        let record = self.arena.get(node.node).ok_or_else(invalid)?;
        let end = usize::try_from(record.range.start.get()).map_err(|_| invalid())?;
        let index = self
            .source_node_ends
            .partition_point(|end| *end <= record.range.start);
        let start = index
            .checked_sub(1)
            .map_or(TextPos::new(0), |index| self.source_node_ends[index]);
        let start = usize::try_from(start.get()).map_err(|_| invalid())?;
        let prefix = self.source.get(..end).ok_or_else(invalid)?;
        if !prefix.is_char_boundary(start) {
            return Err(invalid());
        }

        // The previous source node excludes strings, regular expressions, and template text.
        // Scan the remaining punctuation and trivia without crossing the requested node.
        let mut scanner = Scanner::new(prefix);
        scanner.reset_pos(start);
        scanner.set_skip_trivia(false);
        let mut comments = Vec::new();
        loop {
            let token = scanner.scan();
            match token.kind {
                SyntaxKind::EndOfFile => break,
                SyntaxKind::MultiLineCommentTrivia => {
                    if token.flags.contains(TokenFlags::PRECEDING_JSDOC_COMMENT)
                        && !token.flags.contains(TokenFlags::UNTERMINATED)
                    {
                        comments.push(token.range);
                    }
                }
                SyntaxKind::WhitespaceTrivia
                | SyntaxKind::NewLineTrivia
                | SyntaxKind::SingleLineCommentTrivia => {}
                _ => comments.clear(),
            }
        }
        Ok(comments)
    }

    fn last(&self, node: NodeRef) -> Result<Option<ParsedJsDocComment<'arena>>, JsDocCommentError> {
        self.ranges(node)?
            .last()
            .map(|range| parse_jsdoc_comment_at(self.source, *range))
            .transpose()
    }

    fn all(&self, node: NodeRef) -> Result<Vec<ParsedJsDocComment<'arena>>, JsDocCommentError> {
        self.ranges(node)?
            .into_iter()
            .map(|range| parse_jsdoc_comment_at(self.source, range))
            .collect()
    }
}

/// Collects source-owned `JSDoc` annotations for JavaScript declarations.
///
/// Parser and semantic diagnostics are anchored to the source root because
/// comment ranges precede the declaration nodes they annotate.
///
/// # Errors
///
/// Returns an error for invalid source identity, malformed parser trees,
/// unsupported overload declarations, or parser diagnostics whose catalog
/// arguments cannot be reconstructed.
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
    let NodeData::SourceFile(root_data) = &root.data else {
        return Err(JsDocCommentError::InvalidSourceNode(source));
    };
    if root.kind != SyntaxKind::SourceFile {
        return Err(JsDocCommentError::InvalidSourceNode(source));
    }
    if arena.source_text().is_none() {
        return Err(JsDocCommentError::MissingSourceText(source));
    }

    let mut source_typedefs = HashMap::new();
    for node in &root_data.statements.nodes {
        let record = arena
            .get(*node)
            .ok_or(JsDocCommentError::InvalidSourceNode(source))?;
        if record.kind != SyntaxKind::JsTypeAliasDeclaration {
            continue;
        }
        let declaration = NodeRef::new(arena.id(), source.file, *node);
        let name = authenticate_reparsed_jsdoc_typedef(arena, source, declaration)?;
        if source_typedefs
            .insert((name.start.get(), name.end.get()), declaration)
            .is_some()
        {
            return Err(JsDocCommentError::InvalidSourceNode(declaration));
        }
    }

    let mut pending = vec![source.node];
    let leading_comments = LeadingJsDocComments::new(arena, source)?;
    let mut seen_comments = HashSet::new();
    let mut declarations = Vec::new();
    let mut expressions = Vec::new();
    let mut diagnostics = Vec::new();

    while let Some(node) = pending.pop() {
        let record = arena
            .get(node)
            .ok_or(JsDocCommentError::InvalidSourceNode(source))?;
        let reference = NodeRef::new(arena.id(), source.file, node);
        if record.kind == SyntaxKind::JsTypeAliasDeclaration {
            let name = authenticate_reparsed_jsdoc_typedef(arena, source, reference)?;
            if source_typedefs.get(&(name.start.get(), name.end.get())) != Some(&reference) {
                return Err(JsDocCommentError::InvalidSourceNode(reference));
            }
            continue;
        }
        if is_jsdoc_declaration_candidate(record.kind) {
            let comments = leading_comments
                .all(reference)?
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
                    implements_types: Vec::new(),
                };
                for comment in comments {
                    for diagnostic in comment.diagnostics() {
                        diagnostics.push(canonical_parser_diagnostic(source, diagnostic)?);
                    }
                    apply_comment_tags(arena, source, &mut planned, &comment, &mut diagnostics)?;
                }
                for alias in &mut planned.typedefs {
                    alias.source_declaration = source_typedefs
                        .get(&(alias.range.start.get(), alias.range.end.get()))
                        .copied();
                }
                append_unmatched_parameter_diagnostics(arena, source, &planned, &mut diagnostics)?;
                declarations.push(planned);
            }
        }
        if record.kind == SyntaxKind::ParenthesizedExpression
            && let Some((callable, declaration)) =
                javascript_jsdoc_arrow_expression_owner(arena, reference)?
            && let Some(comment) = leading_comments.last(reference)?
            && let [tag] = comment.tags()
            && tag.kind() == JsDocTagKind::Type
            && let Some(annotation) = tag.type_expression()
            && seen_comments.insert((comment.range().start.get(), comment.range().end.get()))
        {
            for diagnostic in comment.diagnostics() {
                diagnostics.push(canonical_parser_diagnostic(source, diagnostic)?);
            }
            expressions.push(PlannedJsDocArrowExpression {
                node: reference,
                callable,
                declaration,
                type_: annotation.planned(),
            });
        }
        let mut children = Vec::new();
        record.for_each_child(|child| children.push(child));
        pending.extend(children.into_iter().rev());
    }

    attach_local_typedef_resolutions(&mut declarations, &mut expressions);

    Ok(PlannedJavaScriptJsDoc {
        declarations,
        expressions,
        diagnostics,
    })
}

fn javascript_jsdoc_arrow_expression_owner(
    arena: &NodeArena,
    expression: NodeRef,
) -> Result<Option<(NodeRef, NodeRef)>, JsDocCommentError> {
    let invalid = || JsDocCommentError::InvalidSourceNode(expression);
    let mut current = expression;
    loop {
        let record = arena.get(current.node).ok_or_else(invalid)?;
        let Some(parent) = record.parent else {
            return Ok(None);
        };
        let parent = NodeRef::new(expression.arena, expression.file, parent);
        let parent_record = arena.get(parent.node).ok_or_else(invalid)?;
        match &parent_record.data {
            NodeData::ParenthesizedExpression(parenthesized)
                if parent_record.kind == SyntaxKind::ParenthesizedExpression
                    && parenthesized.expression == current.node =>
            {
                current = parent;
            }
            NodeData::ArrowFunction(arrow)
                if parent_record.kind == SyntaxKind::ArrowFunction
                    && arrow.body == current.node =>
            {
                let Some(declaration) = parent_record.parent else {
                    return Ok(None);
                };
                let declaration = NodeRef::new(expression.arena, expression.file, declaration);
                let declaration_record = arena.get(declaration.node).ok_or_else(invalid)?;
                let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
                    return Ok(None);
                };
                if declaration_record.kind != SyntaxKind::VariableDeclaration
                    || variable.initializer != Some(parent.node)
                {
                    return Ok(None);
                }
                return Ok(Some((parent, declaration)));
            }
            _ => return Ok(None),
        }
    }
}

fn authenticate_reparsed_jsdoc_typedef(
    arena: &NodeArena,
    source: NodeRef,
    declaration: NodeRef,
) -> Result<TextRange, JsDocCommentError> {
    let invalid = || JsDocCommentError::InvalidSourceNode(declaration);
    let record = arena.get(declaration.node).ok_or_else(invalid)?;
    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
        return Err(invalid());
    };
    if !declaration.is_for(arena.id(), source.file)
        || record.kind != SyntaxKind::JsTypeAliasDeclaration
        || record.flags != NodeFlags::REPARSED
        || record.parent != Some(source.node)
        || alias.flow_node.is_some()
        || alias.local_symbol.is_some()
        || alias.symbol.is_some()
        || alias.type_parameters.is_some()
        || alias.modifiers.is_some()
    {
        return Err(invalid());
    }

    let name = arena.get(alias.name).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &name.data else {
        return Err(invalid());
    };
    let type_ = arena.get(alias.type_).ok_or_else(invalid)?;
    let structural = match &type_.data {
        NodeData::TypeLiteralNode(literal)
            if type_.kind == SyntaxKind::TypeLiteral && type_.flags == NodeFlags::REPARSED =>
        {
            Some(literal)
        }
        _ => None,
    };
    if name.kind != SyntaxKind::Identifier
        || name.flags != NodeFlags::default()
        || name.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || type_.parent != Some(declaration.node)
        || record.range.end
            != if structural.is_some() {
                type_.range.end
            } else {
                name.range.end
            }
    {
        return Err(invalid());
    }

    let text = arena.source_text().ok_or_else(invalid)?;
    let start = usize::try_from(record.range.start.get()).map_err(|_| invalid())?;
    let comment_start = text
        .get(..start)
        .and_then(|prefix| prefix.rfind("/**"))
        .ok_or_else(invalid)?;
    let comment_end = text
        .get(start..)
        .and_then(|suffix| suffix.find("*/"))
        .and_then(|end| start.checked_add(end))
        .and_then(|end| end.checked_add(2))
        .ok_or_else(invalid)?;
    if text
        .get(comment_start..start)
        .is_none_or(|prefix| prefix.contains("*/"))
    {
        return Err(invalid());
    }
    let range = checked_range(comment_start, comment_end).map_err(|_| invalid())?;
    let comment = parse_jsdoc_comment_at(text, range).map_err(|_| invalid())?;
    let Some((index, tag)) = comment.tags().iter().enumerate().find(|(_, tag)| {
        tag.kind() == JsDocTagKind::Typedef
            && tag.range().start == record.range.start
            && tag.name().is_some_and(|tag_name| {
                tag_name.range() == name.range && tag_name.text() == identifier.text
            })
    }) else {
        return Err(invalid());
    };
    let annotation = tag.type_expression().ok_or_else(invalid)?;
    if let Some(literal) = structural {
        if !matches!(
            annotation.type_(),
            JsDocType::Intrinsic(JsDocIntrinsicType::Object)
        ) && !matches!(annotation.type_(), JsDocType::Named(name) if name == "Object")
            || literal.symbol.is_some()
            || literal.members.nodes.is_empty()
            || literal.members.has_trailing_comma
            || literal.members.range != type_.range
        {
            return Err(invalid());
        }
        let properties = comment
            .tags()
            .iter()
            .skip(index + 1)
            .take_while(|tag| tag.kind() == JsDocTagKind::Property)
            .collect::<Vec<_>>();
        if properties.len() != literal.members.nodes.len() {
            return Err(invalid());
        }
        for (member, tag) in literal.members.nodes.iter().zip(properties) {
            let member_record = arena.get(*member).ok_or_else(invalid)?;
            let NodeData::PropertyDeclaration(property) = &member_record.data else {
                return Err(invalid());
            };
            let property_name = arena.get(property.name).ok_or_else(invalid)?;
            let actual_name = match &property_name.data {
                NodeData::Identifier(name) => name.text.as_str(),
                NodeData::StringLiteral(name) => name.text.as_str(),
                _ => return Err(invalid()),
            };
            let tag_name = tag.name().ok_or_else(invalid)?;
            let property_type = property
                .type_
                .and_then(|type_| arena.get(type_))
                .ok_or_else(invalid)?;
            let tag_type = tag.type_expression().ok_or_else(invalid)?;
            if member_record.kind != SyntaxKind::PropertyDeclaration
                || member_record.flags != NodeFlags::REPARSED
                || member_record.parent != Some(alias.type_)
                || member_record.range.start != tag.range().start
                || property_name.parent != Some(*member)
                || property_name.range != tag_name.range()
                || actual_name != tag_name.text()
                || property_type.parent != Some(*member)
                || property_type.range != tag_type.range()
                || property.postfix_token.is_some() != tag.is_optional()
                || property.initializer.is_some()
                || property.symbol.is_some()
                || property.modifiers.is_some()
                || property.facts != 0
            {
                return Err(invalid());
            }
        }
    } else if annotation.range() != type_.range {
        return Err(invalid());
    }
    Ok(name.range)
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
/// as [`resolve_planned_jsdoc_type`]. Callback aliases retain a separate
/// signature and are resolved with [`resolve_planned_jsdoc_callback_signature`].
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

/// Keeps the source identity of an object typedef that has no reparsed alias node.
pub(super) fn resolve_source_jsdoc_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    owner: NodeRef,
    annotation: &PlannedJsDocType,
) -> Result<TypeId, JsDocTypeResolutionError> {
    let fallback = |store: &mut CanonicalTypeMapperStore| {
        resolve_planned_jsdoc_type(store, global_types, options, annotation)
    };
    let Some(name) = annotation.resolved_alias_name() else {
        return fallback(store);
    };
    if !matches!(annotation.type_(), JsDocType::Named(_)) {
        return fallback(store);
    }
    let invalid = || JsDocTypeResolutionError::ObjectConstruction(annotation.range());
    let (arena, bound) = host.source(owner).ok_or_else(invalid)?;
    if bound
        .source_facts()
        .is_none_or(|facts| !facts.is_javascript_file())
    {
        return Err(invalid());
    }
    let plan = plan_javascript_source_jsdoc(arena, bound.source_file()).map_err(|_| invalid())?;
    if plan
        .declaration(owner)
        .and_then(PlannedJavaScriptDeclaration::type_)
        != Some(annotation)
    {
        return fallback(store);
    }
    let Some((definition_owner, definition)) = source_object_typedef(&plan, name) else {
        return fallback(store);
    };
    if let Some(type_) = store.source_jsdoc_typedef_type(definition_owner, definition.range()) {
        validate_source_jsdoc_typedef_name(store, host, Some(global_types), type_)
            .map_err(|()| invalid())?;
        return Ok(type_);
    }
    let Some(definition_type) = definition.type_() else {
        return Err(invalid());
    };
    let JsDocType::ObjectLiteral(properties) =
        unparenthesized_jsdoc_type(definition_type.resolution_type())
    else {
        return Err(invalid());
    };
    preflight_planned_jsdoc_type(store, global_types, options, definition_type)?;
    if !store.try_reserve_source_jsdoc_typedefs(1) {
        return Err(invalid());
    }
    let type_ = resolve_object_type(
        store,
        global_types,
        options,
        properties,
        definition_type.range(),
    )?;
    let identity = SourceJsDocTypedefIdentity {
        owner: definition_owner,
        definition: definition.clone(),
        shape: source_jsdoc_typedef_shape(store, host, Some(global_types), type_)
            .ok_or_else(invalid)?,
    };
    if !store.publish_source_jsdoc_typedef(type_, identity) {
        return Err(invalid());
    }
    Ok(type_)
}

fn source_object_typedef<'a>(
    plan: &'a PlannedJavaScriptJsDoc,
    name: &str,
) -> Option<(NodeRef, &'a PlannedJsDocTypedef)> {
    let mut name = name;
    let mut visited = HashSet::new();
    while visited.insert(name) {
        let mut definitions = plan.declarations().iter().flat_map(|declaration| {
            declaration
                .typedefs()
                .iter()
                .filter(move |definition| definition.name() == name)
                .map(move |definition| (declaration.node(), definition))
        });
        let (owner, definition) = definitions.next()?;
        if definitions.next().is_some() || !definition.template_parameters().is_empty() {
            return None;
        }
        match unparenthesized_jsdoc_type(definition.type_()?.type_()) {
            JsDocType::Named(target) => name = target,
            JsDocType::ObjectLiteral(_) if definition.source_declaration().is_none() => {
                return Some((owner, definition));
            }
            _ => return None,
        }
    }
    None
}

/// Resolves the declared callback independently of its contextual arrow.
pub(super) fn resolve_source_jsdoc_callback_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    owner: NodeRef,
) -> Result<TypeId, JsDocTypeResolutionError> {
    let invalid = || JsDocTypeResolutionError::ObjectConstruction(TextRange::default());
    let (arena, bound) = host.source(owner).ok_or_else(invalid)?;
    if bound
        .source_facts()
        .is_none_or(|facts| !facts.is_javascript_file())
    {
        return Err(invalid());
    }
    let plan = plan_javascript_source_jsdoc(arena, bound.source_file()).map_err(|_| invalid())?;
    let annotation = plan
        .declaration(owner)
        .and_then(PlannedJavaScriptDeclaration::type_)
        .ok_or_else(invalid)?;
    let callback = annotation.resolved_callback().ok_or_else(invalid)?;
    let invalid = || JsDocTypeResolutionError::ObjectConstruction(annotation.range());
    let (definition_owner, definition) =
        source_callback_definition(&plan, callback.name()).ok_or_else(invalid)?;
    if !matches!(annotation.type_(), JsDocType::Named(name) if name == callback.name())
        || definition != callback
        || !definition.template_parameters().is_empty()
        || definition.this_type().is_some()
        || definition
            .parameters()
            .iter()
            .any(PlannedJsDocParameter::is_optional)
    {
        return Err(invalid());
    }
    if let Some(type_) = store.source_jsdoc_callback_type(definition_owner, definition.range()) {
        validate_source_jsdoc_callback_name(store, host, Some(global_types), type_)
            .map_err(|()| invalid())?;
        return Ok(type_);
    }
    let resolved =
        resolve_planned_jsdoc_callback_signature(store, global_types, options, callback, &[])?;
    let return_type = resolved.return_type().ok_or_else(invalid)?;
    let parameter_types = resolved
        .parameters()
        .iter()
        .map(|parameter| parameter.type_().ok_or_else(invalid))
        .collect::<Result<Vec<_>, _>>()?;
    let minimum = i32::try_from(parameter_types.len()).map_err(|_| invalid())?;
    if !store.try_reserve_source_jsdoc_callbacks(1)
        || !store.try_reserve_types(1)
        || !store.try_reserve_signatures(1)
        || !store.try_reserve_function_type_provenance(1)
        || !store.try_reserve_checker_symbol_allocations(parameter_types.len(), 0)
        || !store.try_reserve_value_symbol_links(parameter_types.len())
        || !store.try_reserve_callable_signature_parameter_types(1)
    {
        return Err(invalid());
    }
    let mut parameters = Vec::with_capacity(parameter_types.len());
    for (parameter, type_) in resolved.parameters().iter().zip(&parameter_types) {
        let symbol = store.alloc_transient_symbol(
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            EscapedName::source(parameter.name()),
            CheckFlags::NONE,
        );
        let links = ValueSymbolLinks {
            resolved_type: Some(*type_),
            ..ValueSymbolLinks::default()
        };
        assert!(store.set_value_symbol_links(symbol, links.clone()));
        parameters.push(SourceJsDocTypedefProperty {
            symbol,
            record: store
                .symbol(symbol)
                .expect("the callback parameter was allocated")
                .clone(),
            links,
        });
    }
    let signature = store
        .alloc_signature(
            SignatureFlags::NONE,
            None,
            Vec::new(),
            None,
            parameters
                .iter()
                .map(|parameter| parameter.symbol)
                .collect(),
            Some(return_type),
            None,
            minimum,
        )
        .ok_or_else(invalid)?;
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
        .ok_or_else(invalid)?;
    assert!(store.set_function_type_provenance(type_));
    assert!(store.set_structured_type_members(
        type_,
        None,
        None,
        Some(vec![signature]),
        None,
        None
    ));
    let TypeData::Object(object) = store.type_payload(type_).ok_or_else(invalid)?.data() else {
        return Err(invalid());
    };
    let identity = SourceJsDocCallbackIdentity {
        owner: definition_owner,
        definition: definition.clone(),
        signature,
        object: object.clone(),
        parameters,
        return_type,
    };
    assert!(store.publish_source_jsdoc_callback(type_, identity));
    assert!(source_jsdoc_callback_signature_types(store, type_).is_some());
    assert!(store.set_callable_signature_parameter_types_batch(vec![(signature, parameter_types)]));
    Ok(type_)
}

fn source_callback_definition<'a>(
    plan: &'a PlannedJavaScriptJsDoc,
    name: &str,
) -> Option<(NodeRef, &'a PlannedJsDocCallback)> {
    let mut definitions = plan.declarations().iter().flat_map(|declaration| {
        declaration
            .callbacks()
            .iter()
            .filter(move |definition| definition.name() == name)
            .map(move |definition| (declaration.node(), definition))
    });
    let definition = definitions.next()?;
    definitions.next().is_none().then_some(definition)
}

pub(super) fn validate_source_jsdoc_callback_name<'store>(
    store: &'store CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
) -> Result<&'store str, ()> {
    let identity = store.source_jsdoc_callback_identity(type_).ok_or(())?;
    let (arena, bound) = host.source(identity.owner).ok_or(())?;
    if bound
        .source_facts()
        .is_none_or(|facts| !facts.is_javascript_file())
    {
        return Err(());
    }
    let plan = plan_javascript_source_jsdoc(arena, bound.source_file()).map_err(|_| ())?;
    let (owner, definition) =
        source_callback_definition(&plan, identity.definition.name()).ok_or(())?;
    if owner != identity.owner || definition != &identity.definition {
        return Err(());
    }
    for edge in validate_stored_source_jsdoc_callback_type(store, type_).ok_or(())? {
        validate_source_jsdoc_leaf(store, global_types, edge).ok_or(())?;
    }
    Ok(identity.definition.name())
}

pub(super) fn validate_stored_source_jsdoc_callback_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<TypeId>> {
    let edges = source_jsdoc_callback_signature_types(store, type_)?;
    let signature = store.source_jsdoc_callback_identity(type_)?.signature;
    let (_, parameters) = edges.split_last()?;
    (store.callable_signature_parameter_types(signature) == Some(parameters)).then_some(edges)
}

/// Checks the callback owner and signature before publishing parameter-cache entries.
fn source_jsdoc_callback_signature_types(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<TypeId>> {
    let identity = store.source_jsdoc_callback_identity(type_)?;
    let record = store.type_payload(type_)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    let signature = store.signature(identity.signature)?;
    if !store.type_has_function_type_provenance(type_)
        || store.source_node_kind(identity.owner) != Some(SyntaxKind::VariableDeclaration)
        || record.flags() != TypeFlags::OBJECT
        || record.object_flags()
            & !(ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
                | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES)
            != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.symbol().is_some()
        || record.alias().is_some()
        || object != &identity.object
        || !identity.definition.template_parameters().is_empty()
        || identity.definition.this_type().is_some()
        || signature.flags() != SignatureFlags::NONE
        || signature.declaration().is_some()
        || !signature.type_parameters().is_empty()
        || signature.this_parameter().is_some()
        || signature.resolved_return_type() != Some(identity.return_type)
        || signature.resolved_type_predicate().is_some()
        || signature.target().is_some()
        || signature.mapper().is_some()
        || signature.isolated_signature_type().is_some()
        || signature.composite().is_some()
        || signature.resolved_min_argument_count() != -1
        || usize::try_from(signature.min_argument_count()).ok() != Some(identity.parameters.len())
        || signature.parameters().len() != identity.parameters.len()
    {
        return None;
    }
    let mut edges = Vec::with_capacity(identity.parameters.len() + 1);
    for (symbol, expected) in signature.parameters().iter().zip(&identity.parameters) {
        if *symbol != expected.symbol
            || store.symbol(*symbol) != Some(&expected.record)
            || store.value_symbol_links(*symbol) != Some(&expected.links)
            || store.get_merged_symbol(*symbol) != Some(*symbol)
        {
            return None;
        }
        let type_ = expected.links.resolved_type?;
        store.type_payload(type_)?;
        edges.push(type_);
    }
    store.type_payload(identity.return_type)?;
    edges.push(identity.return_type);
    Some(edges)
}

fn unparenthesized_jsdoc_type(mut type_: &JsDocType) -> &JsDocType {
    while let JsDocType::Parenthesized(inner) = type_ {
        type_ = inner;
    }
    type_
}

/// Rechecks the source definition and stored property identities before displaying its name.
pub(super) fn validate_source_jsdoc_typedef_name<'store>(
    store: &'store CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
) -> Result<&'store str, ()> {
    let identity = store.source_jsdoc_typedef_identity(type_).ok_or(())?;
    let (arena, bound) = host.source(identity.owner).ok_or(())?;
    if bound
        .source_facts()
        .is_none_or(|facts| !facts.is_javascript_file())
    {
        return Err(());
    }
    let plan = plan_javascript_source_jsdoc(arena, bound.source_file()).map_err(|_| ())?;
    let (owner, definition) = source_object_typedef(&plan, identity.definition.name()).ok_or(())?;
    if owner != identity.owner
        || definition != &identity.definition
        || source_jsdoc_typedef_shape(store, host, global_types, type_).as_ref()
            != Some(&identity.shape)
    {
        return Err(());
    }
    Ok(identity.definition.name())
}

fn source_jsdoc_typedef_shape(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
) -> Option<SourceJsDocTypedefShape> {
    let mut shape = SourceJsDocTypedefShape::default();
    let mut pending = vec![type_];
    let mut visited = HashSet::new();
    while let Some(type_) = pending.pop() {
        if !visited.insert(type_) {
            continue;
        }
        let record = store.type_payload(type_)?;
        match record.data() {
            TypeData::Object(object) => {
                super::formatter::validate_source_jsdoc_object(store, host, global_types, type_)
                    .ok()?;
                let mut properties = Vec::new();
                for property in object.structured.properties.as_deref().unwrap_or_default() {
                    let symbol = store.symbol(*property)?;
                    let links = store.value_symbol_links(*property)?;
                    let property_type = links.resolved_type?;
                    properties.push(SourceJsDocTypedefProperty {
                        symbol: *property,
                        record: symbol.clone(),
                        links: links.clone(),
                    });
                    pending.push(property_type);
                }
                shape.objects.push(SourceJsDocTypedefObject {
                    type_,
                    flags: record.flags(),
                    object_flags: record.object_flags()
                        & !(ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
                            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES),
                    symbol: record.symbol(),
                    alias: record.alias(),
                    object: object.clone(),
                    members: match object.structured.members {
                        Some(members) => Some(store.symbol_table(members)?.clone()),
                        None => None,
                    },
                    properties,
                });
            }
            TypeData::Union(union) => {
                validate_source_jsdoc_leaf(store, global_types, type_)?;
                shape.unions.push((type_, union.union.types.clone()));
                pending.extend(union.union.types.iter().copied());
                pending.extend(union.origin);
            }
            TypeData::TypeReference(reference) => {
                let array = store
                    .canonical_array_reference(global_types?, type_)
                    .ok()??;
                shape.references.push(SourceJsDocTypedefReference {
                    type_,
                    target: reference.object.target,
                    arguments: reference.resolved_type_arguments.clone(),
                });
                pending.push(array.element_type);
            }
            TypeData::Interface(_) => {
                validate_source_jsdoc_leaf(store, global_types, type_)?;
                if let super::object_members::DeclaredPropertyTypeGraphValidation::Traversable(
                    properties,
                ) = super::object_members::validate_resolved_declared_property_type_graph(
                    store, type_,
                ) {
                    pending.extend(properties);
                }
            }
            _ => validate_source_jsdoc_leaf(store, global_types, type_)?,
        }
    }
    Some(shape)
}

fn validate_source_jsdoc_leaf(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
) -> Option<()> {
    match global_types {
        Some(globals) => store.validate_union_constituent_with_global_types(globals, type_),
        None => store.validate_union_constituent(type_),
    }
    .ok()
}

/// Validates a nongeneric source-owned `JSDoc` function annotation without publishing a type.
pub(super) fn preflight_source_jsdoc_function_type(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    annotation: &PlannedJsDocType,
) -> Result<(), JsDocTypeResolutionError> {
    source_jsdoc_function_signature_types(store, global_types, options, annotation).map(|_| ())
}

/// Validates the structural target of a source-owned `@satisfies` function.
pub(super) fn preflight_source_jsdoc_satisfies_type(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    annotation: &PlannedJsDocType,
) -> Result<(), JsDocTypeResolutionError> {
    let JsDocType::Function(function) = annotation.resolution_type() else {
        return preflight_planned_jsdoc_type(store, global_types, options, annotation);
    };
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(JsDocTypeResolutionError::MissingBootstrap)?;
    if bootstrap.options != options.intrinsic {
        return Err(JsDocTypeResolutionError::OptionsMismatch {
            initialized: bootstrap.options,
            requested: options.intrinsic,
        });
    }
    let invalid = || JsDocTypeResolutionError::UnsupportedType {
        kind: SyntaxKind::FunctionType,
        range: annotation.range(),
    };
    let mut names = HashSet::with_capacity(function.parameters.len());
    let mut optional = false;
    for (index, parameter) in function.parameters.iter().enumerate() {
        let Some(type_) = parameter.type_.as_ref() else {
            return Err(invalid());
        };
        if parameter.name.is_empty()
            || !names.insert(parameter.name.as_str())
            || parameter.rest && (parameter.optional || index + 1 != function.parameters.len())
            || !parameter.rest && !parameter.optional && optional
        {
            return Err(invalid());
        }
        if parameter.rest
            && !matches!(
                type_,
                JsDocType::Array(_)
                    | JsDocType::Variadic(_)
                    | JsDocType::Intrinsic(JsDocIntrinsicType::Never)
            )
        {
            return Err(invalid());
        }
        optional |= parameter.optional;
        validate_resolvable_type(store, global_types, options, type_, annotation.range())?;
    }
    validate_resolvable_type(
        store,
        global_types,
        options,
        &function.return_type,
        annotation.range(),
    )
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResolvedJsDocSatisfiesParameter {
    pub(super) name: String,
    pub(super) type_: TypeId,
    pub(super) optional: bool,
    pub(super) rest: bool,
    pub(super) array_rest: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResolvedJsDocSatisfiesSignature {
    pub(super) parameters: Vec<ResolvedJsDocSatisfiesParameter>,
    pub(super) return_type: TypeId,
}

/// Resolves a `@satisfies` function without creating a synthetic callable.
///
/// Rest parameters retain their element type so contravariant positional
/// checks do not need to publish an unrelated array or signature identity.
pub(super) fn resolve_source_jsdoc_satisfies_signature(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    annotation: &PlannedJsDocType,
) -> Result<ResolvedJsDocSatisfiesSignature, JsDocTypeResolutionError> {
    preflight_source_jsdoc_satisfies_type(store, global_types, options, annotation)?;
    let invalid = || JsDocTypeResolutionError::UnsupportedType {
        kind: SyntaxKind::FunctionType,
        range: annotation.range(),
    };
    let JsDocType::Function(function) = annotation.resolution_type() else {
        return Err(invalid());
    };
    let mut parameters = Vec::with_capacity(function.parameters.len());
    for parameter in &function.parameters {
        let type_ = parameter.type_.as_ref().ok_or_else(invalid)?;
        let array_rest =
            parameter.rest && matches!(type_, JsDocType::Array(_) | JsDocType::Variadic(_));
        let type_ = if array_rest {
            match type_ {
                JsDocType::Array(element) | JsDocType::Variadic(element) => element.as_ref(),
                _ => return Err(invalid()),
            }
        } else {
            type_
        };
        parameters.push(ResolvedJsDocSatisfiesParameter {
            name: parameter.name.clone(),
            type_: resolve_complete_type(store, global_types, options, type_, annotation.range())?,
            optional: parameter.optional,
            rest: parameter.rest,
            array_rest,
        });
    }
    let return_type = resolve_complete_type(
        store,
        global_types,
        options,
        &function.return_type,
        annotation.range(),
    )?;
    Ok(ResolvedJsDocSatisfiesSignature {
        parameters,
        return_type,
    })
}

/// Publishes a comment-defined callable on its real JavaScript parameter declaration.
pub(super) fn resolve_source_jsdoc_function_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    annotation: &PlannedJsDocType,
) -> Result<TypeId, JsDocTypeResolutionError> {
    let invalid = || JsDocTypeResolutionError::UnsupportedType {
        kind: SyntaxKind::FunctionType,
        range: annotation.range(),
    };
    let (parameter_types, return_type) =
        source_jsdoc_function_signature_types(store, global_types, options, annotation)?;
    let (arena, bound) = host.source(declaration).ok_or_else(invalid)?;
    let record = host.node(declaration).ok_or_else(invalid)?;
    let NodeData::ParameterDeclaration(parameter) = &record.data else {
        return Err(invalid());
    };
    let Some(callable) = record
        .parent
        .map(|parent| NodeRef::new(declaration.arena, declaration.file, parent))
    else {
        return Err(invalid());
    };
    let name = NodeRef::new(declaration.arena, declaration.file, parameter.name);
    let Some(NodeData::Identifier(identifier)) = host.node(name).map(|node| &node.data) else {
        return Err(invalid());
    };
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    if record.kind != SyntaxKind::Parameter
        || parameter.type_.is_some()
        || parameter.initializer.is_some()
        || parameter.question_token.is_some()
        || parameter.dot_dot_dot_token.is_some()
        || bound
            .source_facts()
            .is_none_or(|facts| !facts.is_javascript_file())
        || store.source_node_kind(callable) != Some(SyntaxKind::FunctionDeclaration)
        || bound.symbol(declaration) != Some(owner)
        || store.get_merged_symbol(owner) != Some(owner)
        || owner_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some(identifier.text.as_str())
        || owner_record.declarations() != Some(&[declaration])
        || owner_record.value_declaration() != Some(declaration)
        || owner_record.members().is_some()
        || owner_record.exports().is_some()
        || owner_record.parent().is_some()
        || owner_record.export_symbol().is_some()
    {
        return Err(invalid());
    }

    let comments =
        plan_javascript_source_jsdoc(arena, bound.source_file()).map_err(|_| invalid())?;
    if comments
        .callable_declaration(arena, callable)
        .and_then(|callable| callable.parameter(&identifier.text))
        .and_then(PlannedJsDocParameter::type_)
        != Some(annotation)
    {
        return Err(invalid());
    }

    if let Some(links) = store.type_node_links(declaration) {
        let Some(cached) = links.resolved_type else {
            return Err(invalid());
        };
        if links.outer_type_parameters.is_some()
            || !matches!(
                validate_stored_function_type(store, cached),
                StoredFunctionTypeValidation::Valid(_)
            )
            || !source_jsdoc_function_signature_matches(
                store,
                declaration,
                owner,
                cached,
                &parameter_types,
                return_type,
            )
        {
            return Err(invalid());
        }
        return Ok(cached);
    }
    if store
        .signature_links(declaration)
        .is_some_and(|links| links != &SignatureLinks::default())
        || store
            .value_symbol_links(owner)
            .is_some_and(|links| links != &ValueSymbolLinks::default())
        || !store.try_reserve_types(1)
        || !store.try_reserve_signatures(1)
        || !store.try_reserve_function_type_provenance(1)
        || !store.try_reserve_checker_symbol_allocations(parameter_types.len(), 0)
        || !store.try_reserve_value_symbol_links(parameter_types.len())
        || !store.try_reserve_type_node_links(1)
        || !store.try_reserve_signature_links(1)
        || !store.try_reserve_callable_signature_parameter_types(1)
    {
        return Err(JsDocTypeResolutionError::ObjectConstruction(
            annotation.range(),
        ));
    }

    let parameters = parameter_types
        .iter()
        .map(|(name, type_)| {
            let parameter = store.alloc_transient_symbol(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source(name),
                CheckFlags::NONE,
            );
            assert!(store.set_value_symbol_links(
                parameter,
                ValueSymbolLinks {
                    resolved_type: Some(*type_),
                    ..ValueSymbolLinks::default()
                },
            ));
            parameter
        })
        .collect::<Vec<_>>();
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(owner))
        .ok_or_else(invalid)?;
    assert!(store.set_function_type_provenance(type_));
    assert!(store.set_type_node_links(
        declaration,
        TypeNodeLinks {
            resolved_type: Some(type_),
            ..TypeNodeLinks::default()
        },
    ));
    let minimum = i32::try_from(parameters.len()).map_err(|_| invalid())?;
    let signature = store
        .alloc_signature(
            SignatureFlags::NONE,
            Some(declaration),
            Vec::new(),
            None,
            parameters,
            Some(return_type),
            None,
            minimum,
        )
        .ok_or_else(invalid)?;
    assert!(store.set_signature_links(
        declaration,
        SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        },
    ));
    assert!(store.set_structured_type_members(
        type_,
        None,
        None,
        Some(vec![signature]),
        None,
        None,
    ));
    assert!(store.set_callable_signature_parameter_types_batch(vec![(
        signature,
        parameter_types.iter().map(|(_, type_)| *type_).collect(),
    )]));
    if !source_jsdoc_function_signature_matches(
        store,
        declaration,
        owner,
        type_,
        &parameter_types,
        return_type,
    ) {
        return Err(invalid());
    }
    Ok(type_)
}

fn source_jsdoc_function_signature_types(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    annotation: &PlannedJsDocType,
) -> Result<(Vec<(String, TypeId)>, TypeId), JsDocTypeResolutionError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(JsDocTypeResolutionError::MissingBootstrap)?;
    if bootstrap.options != options.intrinsic {
        return Err(JsDocTypeResolutionError::OptionsMismatch {
            initialized: bootstrap.options,
            requested: options.intrinsic,
        });
    }
    let invalid = || JsDocTypeResolutionError::UnsupportedType {
        kind: SyntaxKind::FunctionType,
        range: annotation.range(),
    };
    let JsDocType::Function(function) = annotation.resolution_type() else {
        return Err(invalid());
    };
    let mut names = HashSet::with_capacity(function.parameters.len());
    let mut parameters = Vec::with_capacity(function.parameters.len());
    for parameter in &function.parameters {
        let Some(type_) = parameter.type_.as_ref() else {
            return Err(invalid());
        };
        if parameter.name.is_empty()
            || !names.insert(parameter.name.as_str())
            || parameter.optional
            || parameter.rest
            || !matches!(type_, JsDocType::Intrinsic(_))
        {
            return Err(invalid());
        }
        validate_resolvable_type(store, global_types, options, type_, annotation.range())?;
        parameters.push((
            parameter.name.clone(),
            resolve_intrinsic_type(store, options, type_, annotation.range())?,
        ));
    }
    if !matches!(&function.return_type, JsDocType::Intrinsic(_)) {
        return Err(invalid());
    }
    validate_resolvable_type(
        store,
        global_types,
        options,
        &function.return_type,
        annotation.range(),
    )?;
    let return_type =
        resolve_intrinsic_type(store, options, &function.return_type, annotation.range())?;
    Ok((parameters, return_type))
}

fn source_jsdoc_function_signature_matches(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    type_: TypeId,
    parameters: &[(String, TypeId)],
    return_type: TypeId,
) -> bool {
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    let Some(signature) = store
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .and_then(|signature| store.signature(signature))
    else {
        return false;
    };
    record.symbol() == Some(owner)
        && signature.declaration() == Some(declaration)
        && signature.resolved_return_type() == Some(return_type)
        && signature.parameters().len() == parameters.len()
        && signature
            .parameters()
            .iter()
            .zip(parameters)
            .all(|(symbol, (name, type_))| {
                store
                    .symbol(*symbol)
                    .is_some_and(|parameter| parameter.name().as_utf8() == Some(name.as_str()))
                    && store.value_symbol_links(*symbol)
                        == Some(&ValueSymbolLinks {
                            resolved_type: Some(*type_),
                            ..ValueSymbolLinks::default()
                        })
            })
}

/// Validates the source-parameter-anchored callable family without an AST host.
pub(super) fn validate_stored_source_jsdoc_function_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<TypeId>> {
    let record = store.type_payload(type_)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    let owner = record.symbol()?;
    let owner_record = store.symbol(owner)?;
    let [declaration] = owner_record.declarations()? else {
        return None;
    };
    let declaration = *declaration;
    let SourceNodeParent::Parent(callable) = store.source_node_parent(declaration)? else {
        return None;
    };
    let links = store.signature_links(declaration)?;
    let ResolvedSignatureState::Resolved(signature) = links.resolved_signature else {
        return None;
    };
    let signature_record = store.signature(signature)?;
    let parameter_types = store.callable_signature_parameter_types(signature)?;
    if !store.type_has_function_type_provenance(type_)
        || record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.alias().is_some()
        || owner_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.value_declaration() != Some(declaration)
        || owner_record.members().is_some()
        || owner_record.exports().is_some()
        || owner_record.parent().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store.source_node_kind(declaration) != Some(SyntaxKind::Parameter)
        || store.source_node_kind(callable) != Some(SyntaxKind::FunctionDeclaration)
        || store.type_node_links(declaration)
            != Some(&TypeNodeLinks {
                resolved_type: Some(type_),
                ..TypeNodeLinks::default()
            })
        || links
            != &(SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            })
        || signature_record.flags() != SignatureFlags::NONE
        || signature_record.declaration() != Some(declaration)
        || !signature_record.type_parameters().is_empty()
        || signature_record.this_parameter().is_some()
        || signature_record.resolved_type_predicate().is_some()
        || signature_record.target().is_some()
        || signature_record.mapper().is_some()
        || signature_record.isolated_signature_type().is_some()
        || signature_record.composite().is_some()
        || signature_record.resolved_min_argument_count() != -1
        || usize::try_from(signature_record.min_argument_count()).ok()
            != Some(signature_record.parameters().len())
        || parameter_types.len() != signature_record.parameters().len()
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.members.is_some()
        || object.structured.properties.is_some()
        || object.structured.signatures.as_deref() != Some(&[signature])
        || object.structured.call_signature_count != 1
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || store.value_symbol_links(owner).is_some_and(|links| {
            links != &ValueSymbolLinks::default()
                && links
                    != &(ValueSymbolLinks {
                        resolved_type: Some(type_),
                        ..ValueSymbolLinks::default()
                    })
        })
    {
        return None;
    }

    let mut names = HashSet::with_capacity(parameter_types.len());
    let mut symbols = HashSet::with_capacity(parameter_types.len());
    for (parameter, type_) in signature_record.parameters().iter().zip(parameter_types) {
        let parameter_record = store.symbol(*parameter)?;
        let name = parameter_record.name().as_utf8()?;
        if !symbols.insert(*parameter)
            || !names.insert(name)
            || parameter_record.flags()
                != SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT
            || parameter_record.check_flags() != CheckFlags::NONE
            || parameter_record.declarations().is_some()
            || parameter_record.value_declaration().is_some()
            || parameter_record.members().is_some()
            || parameter_record.exports().is_some()
            || parameter_record.parent().is_some()
            || parameter_record.export_symbol().is_some()
            || store.get_merged_symbol(*parameter) != Some(*parameter)
            || store.value_symbol_links(*parameter)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(*type_),
                    ..ValueSymbolLinks::default()
                })
            || store.type_payload(*type_).is_none()
        {
            return None;
        }
    }
    let return_type = signature_record.resolved_return_type()?;
    store.type_payload(return_type)?;
    let mut edges = parameter_types.to_vec();
    edges.push(return_type);
    Some(edges)
}

/// Binds source `@template` names to canonical checker-owned type parameters.
///
/// # Errors
///
/// Rejects duplicate names, foreign identities, and bindings that do not
/// refer to canonical type-parameter records.
pub fn bind_planned_jsdoc_type_parameters(
    store: &CanonicalTypeMapperStore,
    annotation: &PlannedJsDocType,
    bindings: &[JsDocTypeParameterBinding<'_>],
) -> Result<PlannedJsDocType, JsDocTypeResolutionError> {
    let mut validated = HashMap::with_capacity(bindings.len());
    for binding in bindings {
        let valid = store.type_payload(binding.type_()).is_some_and(|record| {
            record
                .flags()
                .contains(super::types::TypeFlags::TYPE_PARAMETER)
        });
        if !valid {
            return Err(JsDocTypeResolutionError::InvalidTypeParameterBinding {
                name: binding.name().to_owned(),
                type_: binding.type_(),
            });
        }
        if validated
            .insert(binding.name().to_owned(), binding.type_())
            .is_some()
        {
            return Err(JsDocTypeResolutionError::DuplicateTypeParameterBinding(
                binding.name().to_owned(),
            ));
        }
    }
    let mut bound = annotation.clone();
    if let Some(resolved) = bind_jsdoc_type(annotation.resolution_type(), &validated) {
        bound.resolved_type = Some(Box::new(resolved));
    }
    Ok(bound)
}

/// Resolves a hosted `JSDoc` signature without inventing unannotated types.
///
/// # Errors
///
/// Returns an error if a template binding is invalid or any annotated
/// parameter, return, or receiver type cannot be resolved exactly.
pub fn resolve_planned_jsdoc_signature(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    declaration: &PlannedJavaScriptDeclaration,
    bindings: &[JsDocTypeParameterBinding<'_>],
) -> Result<ResolvedJsDocSignature, JsDocTypeResolutionError> {
    resolve_jsdoc_signature_parts(
        store,
        global_types,
        options,
        &declaration.parameters,
        declaration.return_type.as_ref(),
        declaration.this_type.as_ref(),
        bindings,
    )
}

/// Resolves a synthetic callback signature separately from its host callable.
///
/// # Errors
///
/// Returns the same validation and resolution errors as
/// [`resolve_planned_jsdoc_signature`].
pub fn resolve_planned_jsdoc_callback_signature(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    callback: &PlannedJsDocCallback,
    bindings: &[JsDocTypeParameterBinding<'_>],
) -> Result<ResolvedJsDocSignature, JsDocTypeResolutionError> {
    resolve_jsdoc_signature_parts(
        store,
        global_types,
        options,
        &callback.parameters,
        callback.return_type.as_ref(),
        callback.this_type.as_ref(),
        bindings,
    )
}

#[allow(clippy::too_many_arguments)] // A signature retains separate return and receiver slots.
fn resolve_jsdoc_signature_parts(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    parameters: &[PlannedJsDocParameter],
    return_type: Option<&PlannedJsDocType>,
    this_type: Option<&PlannedJsDocType>,
    bindings: &[JsDocTypeParameterBinding<'_>],
) -> Result<ResolvedJsDocSignature, JsDocTypeResolutionError> {
    let parameter_types = parameters
        .iter()
        .map(|parameter| {
            parameter
                .type_()
                .map(|annotation| bind_planned_jsdoc_type_parameters(store, annotation, bindings))
                .transpose()
        })
        .collect::<Result<Vec<_>, _>>()?;
    let return_type = return_type
        .map(|annotation| bind_planned_jsdoc_type_parameters(store, annotation, bindings))
        .transpose()?;
    let this_type = this_type
        .map(|annotation| bind_planned_jsdoc_type_parameters(store, annotation, bindings))
        .transpose()?;

    for annotation in parameter_types
        .iter()
        .flatten()
        .chain(return_type.iter())
        .chain(this_type.iter())
    {
        preflight_planned_jsdoc_type(store, global_types, options, annotation)?;
    }

    let mut resolved_parameters = Vec::with_capacity(parameters.len());
    for (parameter, annotation) in parameters.iter().zip(parameter_types) {
        let type_ = annotation
            .as_ref()
            .map(|annotation| resolve_planned_jsdoc_type(store, global_types, options, annotation))
            .transpose()?;
        resolved_parameters.push(ResolvedJsDocParameter {
            name: parameter.name.clone(),
            range: parameter.range,
            type_,
            optional: parameter.optional,
        });
    }
    let return_type = return_type
        .as_ref()
        .map(|annotation| resolve_planned_jsdoc_type(store, global_types, options, annotation))
        .transpose()?;
    let this_type = this_type
        .as_ref()
        .map(|annotation| resolve_planned_jsdoc_type(store, global_types, options, annotation))
        .transpose()?;

    Ok(ResolvedJsDocSignature {
        parameters: resolved_parameters,
        return_type,
        this_type,
    })
}

fn bind_jsdoc_type(type_: &JsDocType, bindings: &HashMap<String, TypeId>) -> Option<JsDocType> {
    match type_ {
        JsDocType::Named(name) => bindings
            .get(name)
            .copied()
            .map(JsDocType::BoundTypeParameter),
        JsDocType::Parenthesized(inner) => bind_jsdoc_type(inner, bindings)
            .map(Box::new)
            .map(JsDocType::Parenthesized),
        JsDocType::Nullable(inner) => bind_jsdoc_type(inner, bindings)
            .map(Box::new)
            .map(JsDocType::Nullable),
        JsDocType::NonNullable(inner) => bind_jsdoc_type(inner, bindings)
            .map(Box::new)
            .map(JsDocType::NonNullable),
        JsDocType::Optional(inner) => bind_jsdoc_type(inner, bindings)
            .map(Box::new)
            .map(JsDocType::Optional),
        JsDocType::Variadic(inner) => bind_jsdoc_type(inner, bindings)
            .map(Box::new)
            .map(JsDocType::Variadic),
        JsDocType::Array(inner) => bind_jsdoc_type(inner, bindings)
            .map(Box::new)
            .map(JsDocType::Array),
        JsDocType::ReadonlyArray(inner) => bind_jsdoc_type(inner, bindings)
            .map(Box::new)
            .map(JsDocType::ReadonlyArray),
        JsDocType::KeyOf(inner) => bind_jsdoc_type(inner, bindings)
            .map(Box::new)
            .map(JsDocType::KeyOf),
        JsDocType::Union(members) => bind_jsdoc_type_list(members, bindings).map(JsDocType::Union),
        JsDocType::GenericReference { name, arguments } => {
            bind_jsdoc_type_list(arguments, bindings).map(|arguments| JsDocType::GenericReference {
                name: name.clone(),
                arguments,
            })
        }
        JsDocType::Import(import) => {
            bind_jsdoc_type_list(&import.type_arguments, bindings).map(|type_arguments| {
                JsDocType::Import(JsDocImportType {
                    specifier: import.specifier.clone(),
                    qualifier: import.qualifier.clone(),
                    type_arguments,
                    is_type_of: import.is_type_of,
                })
            })
        }
        JsDocType::ObjectLiteral(properties) => bind_jsdoc_object_properties(properties, bindings),
        JsDocType::Function(function) => bind_jsdoc_function_type(function, bindings),
        JsDocType::IndexedAccess { object, index } => {
            let object_binding = bind_jsdoc_type(object, bindings);
            let index_binding = bind_jsdoc_type(index, bindings);
            if object_binding.is_none() && index_binding.is_none() {
                None
            } else {
                Some(JsDocType::IndexedAccess {
                    object: Box::new(object_binding.unwrap_or_else(|| (**object).clone())),
                    index: Box::new(index_binding.unwrap_or_else(|| (**index).clone())),
                })
            }
        }
        JsDocType::Intrinsic(_)
        | JsDocType::BoundTypeParameter(_)
        | JsDocType::Callback(_)
        | JsDocType::StringLiteral(_)
        | JsDocType::NumberLiteral(_)
        | JsDocType::BigIntLiteral(_)
        | JsDocType::Unsupported(_) => None,
    }
}

fn bind_jsdoc_type_list(
    members: &[JsDocType],
    bindings: &HashMap<String, TypeId>,
) -> Option<Vec<JsDocType>> {
    let mut changed = false;
    let resolved = members
        .iter()
        .map(|member| {
            bind_jsdoc_type(member, bindings).map_or_else(
                || member.clone(),
                |member| {
                    changed = true;
                    member
                },
            )
        })
        .collect::<Vec<_>>();
    changed.then_some(resolved)
}

fn bind_jsdoc_object_properties(
    properties: &[JsDocObjectProperty],
    bindings: &HashMap<String, TypeId>,
) -> Option<JsDocType> {
    let mut changed = false;
    let resolved = properties
        .iter()
        .map(|property| {
            let type_ = bind_jsdoc_type(&property.type_, bindings).map_or_else(
                || property.type_.clone(),
                |type_| {
                    changed = true;
                    type_
                },
            );
            JsDocObjectProperty {
                name: property.name.clone(),
                type_,
                optional: property.optional,
                readonly: property.readonly,
            }
        })
        .collect::<Vec<_>>();
    changed.then_some(JsDocType::ObjectLiteral(resolved))
}

fn bind_jsdoc_function_type(
    function: &JsDocFunctionType,
    bindings: &HashMap<String, TypeId>,
) -> Option<JsDocType> {
    let mut changed = false;
    let parameters = function
        .parameters
        .iter()
        .map(|parameter| {
            let type_ = parameter.type_.as_ref().map(|type_| {
                bind_jsdoc_type(type_, bindings).map_or_else(
                    || type_.clone(),
                    |type_| {
                        changed = true;
                        type_
                    },
                )
            });
            JsDocFunctionParameter {
                name: parameter.name.clone(),
                type_,
                optional: parameter.optional,
                rest: parameter.rest,
            }
        })
        .collect::<Vec<_>>();
    let return_type = bind_jsdoc_type(&function.return_type, bindings).map_or_else(
        || function.return_type.clone(),
        |type_| {
            changed = true;
            type_
        },
    );
    changed.then_some(JsDocType::Function(Box::new(JsDocFunctionType {
        parameters,
        return_type,
    })))
}

#[derive(Clone, Debug)]
struct LocalGenericJsDocDefinition {
    parameters: Vec<PlannedJsDocTemplateParameter>,
    type_: JsDocType,
}

#[allow(clippy::too_many_lines)] // Keep typedef, callback, and declaration ownership synchronized.
fn attach_local_typedef_resolutions(
    declarations: &mut [PlannedJavaScriptDeclaration],
    expressions: &mut [PlannedJsDocArrowExpression],
) {
    let mut aliases = HashMap::new();
    let mut generic_aliases = HashMap::new();
    let mut duplicates = HashSet::new();
    for declaration in declarations.iter() {
        for alias in &declaration.typedefs {
            let Some(annotation) = &alias.type_ else {
                continue;
            };
            let duplicate = if alias.template_parameters.is_empty() {
                aliases
                    .insert(alias.name.clone(), annotation.type_.clone())
                    .is_some()
                    || generic_aliases.contains_key(&alias.name)
            } else {
                generic_aliases
                    .insert(
                        alias.name.clone(),
                        LocalGenericJsDocDefinition {
                            parameters: alias.template_parameters.clone(),
                            type_: annotation.type_.clone(),
                        },
                    )
                    .is_some()
                    || aliases.contains_key(&alias.name)
            };
            if duplicate {
                duplicates.insert(alias.name.clone());
            }
        }
    }

    for declaration in declarations.iter() {
        for callback in &declaration.callbacks {
            if callback.template_parameters.is_empty() || !supports_local_callback_alias(callback) {
                continue;
            }
            if generic_aliases
                .insert(
                    callback.name.clone(),
                    LocalGenericJsDocDefinition {
                        parameters: callback.template_parameters.clone(),
                        type_: JsDocType::Callback(Box::new(callback.clone())),
                    },
                )
                .is_some()
                || aliases.contains_key(&callback.name)
            {
                duplicates.insert(callback.name.clone());
            }
        }
    }

    for name in &duplicates {
        aliases.remove(name);
        generic_aliases.remove(name);
    }

    for declaration in declarations.iter() {
        for callback in &declaration.callbacks {
            if !callback.template_parameters.is_empty() || !supports_local_callback_alias(callback)
            {
                continue;
            }
            let mut resolved = callback.clone();
            let shadowed = HashSet::new();
            for parameter in &mut resolved.parameters {
                if let Some(annotation) = &mut parameter.type_ {
                    attach_local_typedef_resolution(
                        annotation,
                        &aliases,
                        &generic_aliases,
                        &shadowed,
                    );
                }
            }
            if let Some(annotation) = &mut resolved.return_type {
                attach_local_typedef_resolution(annotation, &aliases, &generic_aliases, &shadowed);
            }
            if aliases
                .insert(
                    callback.name.clone(),
                    JsDocType::Callback(Box::new(resolved)),
                )
                .is_some()
                || generic_aliases.contains_key(&callback.name)
            {
                duplicates.insert(callback.name.clone());
            }
        }
    }
    for name in duplicates {
        aliases.remove(&name);
        generic_aliases.remove(&name);
    }
    if aliases.is_empty() && generic_aliases.is_empty() {
        return;
    }

    for declaration in declarations.iter_mut() {
        let declaration_templates = shadowed_type_parameters(&declaration.template_parameters);
        if let Some(annotation) = &mut declaration.type_ {
            attach_local_typedef_resolution(
                annotation,
                &aliases,
                &generic_aliases,
                &declaration_templates,
            );
        }
        if let Some(annotation) = &mut declaration.return_type {
            attach_local_typedef_resolution(
                annotation,
                &aliases,
                &generic_aliases,
                &declaration_templates,
            );
        }
        if let Some(annotation) = &mut declaration.this_type {
            attach_local_typedef_resolution(
                annotation,
                &aliases,
                &generic_aliases,
                &declaration_templates,
            );
        }
        if let Some(satisfies) = &mut declaration.satisfies {
            attach_local_typedef_resolution(
                &mut satisfies.type_,
                &aliases,
                &generic_aliases,
                &declaration_templates,
            );
        }
        attach_template_typedef_resolutions(
            &mut declaration.template_parameters,
            &aliases,
            &generic_aliases,
            &declaration_templates,
        );
        for parameter in &mut declaration.parameters {
            if let Some(annotation) = &mut parameter.type_ {
                attach_local_typedef_resolution(
                    annotation,
                    &aliases,
                    &generic_aliases,
                    &declaration_templates,
                );
            }
        }
        for alias in &mut declaration.typedefs {
            let alias_templates = shadowed_type_parameters(&alias.template_parameters);
            if let Some(annotation) = &mut alias.type_ {
                attach_local_typedef_resolution(
                    annotation,
                    &aliases,
                    &generic_aliases,
                    &alias_templates,
                );
            }
            for property in &mut alias.properties {
                if let Some(annotation) = &mut property.type_ {
                    attach_local_typedef_resolution(
                        annotation,
                        &aliases,
                        &generic_aliases,
                        &alias_templates,
                    );
                }
            }
            attach_template_typedef_resolutions(
                &mut alias.template_parameters,
                &aliases,
                &generic_aliases,
                &alias_templates,
            );
        }
        for callback in &mut declaration.callbacks {
            let callback_templates = shadowed_type_parameters(&callback.template_parameters);
            for parameter in &mut callback.parameters {
                if let Some(annotation) = &mut parameter.type_ {
                    attach_local_typedef_resolution(
                        annotation,
                        &aliases,
                        &generic_aliases,
                        &callback_templates,
                    );
                }
            }
            if let Some(annotation) = &mut callback.return_type {
                attach_local_typedef_resolution(
                    annotation,
                    &aliases,
                    &generic_aliases,
                    &callback_templates,
                );
            }
            if let Some(annotation) = &mut callback.this_type {
                attach_local_typedef_resolution(
                    annotation,
                    &aliases,
                    &generic_aliases,
                    &callback_templates,
                );
            }
            attach_template_typedef_resolutions(
                &mut callback.template_parameters,
                &aliases,
                &generic_aliases,
                &callback_templates,
            );
        }
    }

    for expression in expressions {
        let shadowed = declarations
            .iter()
            .find(|declaration| declaration.node == expression.declaration)
            .map(|declaration| shadowed_type_parameters(&declaration.template_parameters))
            .unwrap_or_default();
        attach_local_typedef_resolution(
            &mut expression.type_,
            &aliases,
            &generic_aliases,
            &shadowed,
        );
    }
}

fn supports_local_callback_alias(callback: &PlannedJsDocCallback) -> bool {
    callback.this_type.is_none()
        && callback.return_type.is_some()
        && callback
            .parameters
            .iter()
            .all(|parameter| parameter.type_.is_some())
}

fn shadowed_type_parameters(parameters: &[PlannedJsDocTemplateParameter]) -> HashSet<String> {
    parameters
        .iter()
        .map(|parameter| parameter.name.clone())
        .collect()
}

fn attach_template_typedef_resolutions(
    parameters: &mut [PlannedJsDocTemplateParameter],
    aliases: &HashMap<String, JsDocType>,
    generic_aliases: &HashMap<String, LocalGenericJsDocDefinition>,
    shadowed: &HashSet<String>,
) {
    for parameter in parameters {
        if let Some(constraint) = &mut parameter.constraint {
            attach_local_typedef_resolution(constraint, aliases, generic_aliases, shadowed);
        }
        if let Some(default_type) = &mut parameter.default_type {
            attach_local_typedef_resolution(default_type, aliases, generic_aliases, shadowed);
        }
    }
}

fn attach_local_typedef_resolution(
    annotation: &mut PlannedJsDocType,
    aliases: &HashMap<String, JsDocType>,
    generic_aliases: &HashMap<String, LocalGenericJsDocDefinition>,
    shadowed: &HashSet<String>,
) {
    let expanded = expand_local_generic_typedefs(
        &annotation.type_,
        aliases,
        generic_aliases,
        shadowed,
        &mut HashSet::new(),
    );
    let resolved = substitute_local_typedefs(
        expanded.as_ref().unwrap_or(&annotation.type_),
        aliases,
        shadowed,
    )
    .or(expanded);
    if let Some(resolved) = resolved {
        annotation.resolved_type = Some(Box::new(resolved));
    }
}

#[allow(clippy::too_many_lines)] // Generic arguments and nested type shapes share one cycle guard.
fn expand_local_generic_typedefs(
    type_: &JsDocType,
    aliases: &HashMap<String, JsDocType>,
    generic_aliases: &HashMap<String, LocalGenericJsDocDefinition>,
    shadowed: &HashSet<String>,
    visiting: &mut HashSet<String>,
) -> Option<JsDocType> {
    match type_ {
        JsDocType::GenericReference { name, arguments } => {
            let alias = generic_aliases.get(name)?;
            if shadowed.contains(name)
                || arguments.len() > alias.parameters.len()
                || !visiting.insert(name.clone())
            {
                return None;
            }

            let resolved = (|| {
                let mut bindings = HashMap::with_capacity(alias.parameters.len());
                for (index, parameter) in alias.parameters.iter().enumerate() {
                    let argument = arguments.get(index).or_else(|| {
                        parameter
                            .default_type
                            .as_ref()
                            .map(PlannedJsDocType::resolution_type)
                    })?;
                    let argument = substitute_jsdoc_template_names(argument, &bindings);
                    let argument = expand_local_generic_typedefs(
                        &argument,
                        aliases,
                        generic_aliases,
                        shadowed,
                        visiting,
                    )
                    .unwrap_or(argument);
                    let argument =
                        substitute_local_typedefs(&argument, aliases, shadowed).unwrap_or(argument);
                    if let Some(constraint) = &parameter.constraint {
                        let constraint = substitute_jsdoc_template_names(
                            constraint.resolution_type(),
                            &bindings,
                        );
                        let constraint = expand_local_generic_typedefs(
                            &constraint,
                            aliases,
                            generic_aliases,
                            shadowed,
                            visiting,
                        )
                        .unwrap_or(constraint);
                        let constraint = substitute_local_typedefs(&constraint, aliases, shadowed)
                            .unwrap_or(constraint);
                        if !jsdoc_template_constraint_accepts(&argument, &constraint) {
                            return None;
                        }
                    }
                    if bindings.insert(parameter.name.clone(), argument).is_some() {
                        return None;
                    }
                }

                if let JsDocType::Callback(callback) = &alias.type_ {
                    return instantiate_local_generic_callback(
                        callback,
                        &bindings,
                        aliases,
                        generic_aliases,
                        shadowed,
                        visiting,
                    );
                }

                let resolved = substitute_jsdoc_template_names(&alias.type_, &bindings);
                let resolved = expand_local_generic_typedefs(
                    &resolved,
                    aliases,
                    generic_aliases,
                    shadowed,
                    visiting,
                )
                .unwrap_or(resolved);
                Some(substitute_local_typedefs(&resolved, aliases, shadowed).unwrap_or(resolved))
            })();
            visiting.remove(name);
            resolved
        }
        JsDocType::Parenthesized(inner) => {
            expand_local_generic_typedefs(inner, aliases, generic_aliases, shadowed, visiting)
                .map(Box::new)
                .map(JsDocType::Parenthesized)
        }
        JsDocType::Nullable(inner) => {
            expand_local_generic_typedefs(inner, aliases, generic_aliases, shadowed, visiting)
                .map(Box::new)
                .map(JsDocType::Nullable)
        }
        JsDocType::NonNullable(inner) => {
            expand_local_generic_typedefs(inner, aliases, generic_aliases, shadowed, visiting)
                .map(Box::new)
                .map(JsDocType::NonNullable)
        }
        JsDocType::Optional(inner) => {
            expand_local_generic_typedefs(inner, aliases, generic_aliases, shadowed, visiting)
                .map(Box::new)
                .map(JsDocType::Optional)
        }
        JsDocType::Variadic(inner) => {
            expand_local_generic_typedefs(inner, aliases, generic_aliases, shadowed, visiting)
                .map(Box::new)
                .map(JsDocType::Variadic)
        }
        JsDocType::Array(inner) => {
            expand_local_generic_typedefs(inner, aliases, generic_aliases, shadowed, visiting)
                .map(Box::new)
                .map(JsDocType::Array)
        }
        JsDocType::ReadonlyArray(inner) => {
            expand_local_generic_typedefs(inner, aliases, generic_aliases, shadowed, visiting)
                .map(Box::new)
                .map(JsDocType::ReadonlyArray)
        }
        JsDocType::Union(members) => {
            let mut changed = false;
            let members = members
                .iter()
                .map(|member| {
                    expand_local_generic_typedefs(
                        member,
                        aliases,
                        generic_aliases,
                        shadowed,
                        visiting,
                    )
                    .map_or_else(
                        || member.clone(),
                        |member| {
                            changed = true;
                            member
                        },
                    )
                })
                .collect();
            changed.then_some(JsDocType::Union(members))
        }
        JsDocType::ObjectLiteral(properties) => {
            let mut changed = false;
            let properties = properties
                .iter()
                .map(|property| {
                    let type_ = expand_local_generic_typedefs(
                        &property.type_,
                        aliases,
                        generic_aliases,
                        shadowed,
                        visiting,
                    )
                    .map_or_else(
                        || property.type_.clone(),
                        |type_| {
                            changed = true;
                            type_
                        },
                    );
                    JsDocObjectProperty {
                        name: property.name.clone(),
                        type_,
                        optional: property.optional,
                        readonly: property.readonly,
                    }
                })
                .collect();
            changed.then_some(JsDocType::ObjectLiteral(properties))
        }
        _ => None,
    }
}

fn instantiate_local_generic_callback(
    callback: &PlannedJsDocCallback,
    bindings: &HashMap<String, JsDocType>,
    aliases: &HashMap<String, JsDocType>,
    generic_aliases: &HashMap<String, LocalGenericJsDocDefinition>,
    shadowed: &HashSet<String>,
    visiting: &mut HashSet<String>,
) -> Option<JsDocType> {
    let mut resolved = callback.clone();
    resolved.template_parameters.clear();

    for parameter in &mut resolved.parameters {
        instantiate_local_generic_callback_annotation(
            parameter.type_.as_mut()?,
            bindings,
            aliases,
            generic_aliases,
            shadowed,
            visiting,
        )?;
    }
    instantiate_local_generic_callback_annotation(
        resolved.return_type.as_mut()?,
        bindings,
        aliases,
        generic_aliases,
        shadowed,
        visiting,
    )?;

    Some(JsDocType::Callback(Box::new(resolved)))
}

fn instantiate_local_generic_callback_annotation(
    annotation: &mut PlannedJsDocType,
    bindings: &HashMap<String, JsDocType>,
    aliases: &HashMap<String, JsDocType>,
    generic_aliases: &HashMap<String, LocalGenericJsDocDefinition>,
    shadowed: &HashSet<String>,
    visiting: &mut HashSet<String>,
) -> Option<()> {
    let substituted = substitute_jsdoc_template_names(annotation.resolution_type(), bindings);
    let expanded =
        expand_local_generic_typedefs(&substituted, aliases, generic_aliases, shadowed, visiting);
    if expanded.is_none()
        && matches!(
            &substituted,
            JsDocType::GenericReference { name, .. } if generic_aliases.contains_key(name)
        )
    {
        return None;
    }

    let resolved = expanded.unwrap_or(substituted);
    let resolved = substitute_local_typedefs(&resolved, aliases, shadowed).unwrap_or(resolved);
    annotation.resolved_type = Some(Box::new(resolved));
    Some(())
}

fn substitute_jsdoc_template_names(
    type_: &JsDocType,
    bindings: &HashMap<String, JsDocType>,
) -> JsDocType {
    match type_ {
        JsDocType::Named(name) => bindings.get(name).cloned().unwrap_or_else(|| type_.clone()),
        JsDocType::Parenthesized(inner) => {
            JsDocType::Parenthesized(Box::new(substitute_jsdoc_template_names(inner, bindings)))
        }
        JsDocType::Nullable(inner) => {
            JsDocType::Nullable(Box::new(substitute_jsdoc_template_names(inner, bindings)))
        }
        JsDocType::NonNullable(inner) => {
            JsDocType::NonNullable(Box::new(substitute_jsdoc_template_names(inner, bindings)))
        }
        JsDocType::Optional(inner) => {
            JsDocType::Optional(Box::new(substitute_jsdoc_template_names(inner, bindings)))
        }
        JsDocType::Variadic(inner) => {
            JsDocType::Variadic(Box::new(substitute_jsdoc_template_names(inner, bindings)))
        }
        JsDocType::Array(inner) => {
            JsDocType::Array(Box::new(substitute_jsdoc_template_names(inner, bindings)))
        }
        JsDocType::ReadonlyArray(inner) => {
            JsDocType::ReadonlyArray(Box::new(substitute_jsdoc_template_names(inner, bindings)))
        }
        JsDocType::Union(members) => JsDocType::Union(
            members
                .iter()
                .map(|member| substitute_jsdoc_template_names(member, bindings))
                .collect(),
        ),
        JsDocType::ObjectLiteral(properties) => JsDocType::ObjectLiteral(
            properties
                .iter()
                .map(|property| JsDocObjectProperty {
                    name: property.name.clone(),
                    type_: substitute_jsdoc_template_names(&property.type_, bindings),
                    optional: property.optional,
                    readonly: property.readonly,
                })
                .collect(),
        ),
        JsDocType::GenericReference { name, arguments } => JsDocType::GenericReference {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_jsdoc_template_names(argument, bindings))
                .collect(),
        },
        JsDocType::IndexedAccess { object, index } => JsDocType::IndexedAccess {
            object: Box::new(substitute_jsdoc_template_names(object, bindings)),
            index: Box::new(substitute_jsdoc_template_names(index, bindings)),
        },
        JsDocType::KeyOf(inner) => {
            JsDocType::KeyOf(Box::new(substitute_jsdoc_template_names(inner, bindings)))
        }
        JsDocType::Function(function) => JsDocType::Function(Box::new(JsDocFunctionType {
            parameters: function
                .parameters
                .iter()
                .map(|parameter| JsDocFunctionParameter {
                    name: parameter.name.clone(),
                    type_: parameter
                        .type_
                        .as_ref()
                        .map(|type_| substitute_jsdoc_template_names(type_, bindings)),
                    optional: parameter.optional,
                    rest: parameter.rest,
                })
                .collect(),
            return_type: substitute_jsdoc_template_names(&function.return_type, bindings),
        })),
        _ => type_.clone(),
    }
}

fn jsdoc_template_constraint_accepts(argument: &JsDocType, constraint: &JsDocType) -> bool {
    if argument == constraint {
        return true;
    }
    if let JsDocType::Union(arguments) = argument {
        return arguments
            .iter()
            .all(|argument| jsdoc_template_constraint_accepts(argument, constraint));
    }
    match constraint {
        JsDocType::Intrinsic(JsDocIntrinsicType::Any | JsDocIntrinsicType::Unknown) => true,
        JsDocType::Intrinsic(JsDocIntrinsicType::String) => {
            matches!(argument, JsDocType::StringLiteral(_))
        }
        JsDocType::Intrinsic(JsDocIntrinsicType::Number) => {
            matches!(argument, JsDocType::NumberLiteral(_))
        }
        JsDocType::Intrinsic(JsDocIntrinsicType::BigInt) => {
            matches!(argument, JsDocType::BigIntLiteral(_))
        }
        JsDocType::Intrinsic(JsDocIntrinsicType::Boolean) => matches!(
            argument,
            JsDocType::Intrinsic(JsDocIntrinsicType::True | JsDocIntrinsicType::False)
        ),
        JsDocType::Intrinsic(JsDocIntrinsicType::Object) => matches!(
            argument,
            JsDocType::ObjectLiteral(_)
                | JsDocType::Array(_)
                | JsDocType::ReadonlyArray(_)
                | JsDocType::Function(_)
                | JsDocType::Callback(_)
        ),
        JsDocType::Parenthesized(inner) | JsDocType::NonNullable(inner) => {
            jsdoc_template_constraint_accepts(argument, inner)
        }
        JsDocType::Union(members) => members
            .iter()
            .any(|member| jsdoc_template_constraint_accepts(argument, member)),
        _ => false,
    }
}

fn substitute_local_typedefs(
    type_: &JsDocType,
    aliases: &HashMap<String, JsDocType>,
    shadowed: &HashSet<String>,
) -> Option<JsDocType> {
    match type_ {
        JsDocType::Named(name) if shadowed.contains(name) => None,
        JsDocType::Named(name) => resolve_local_typedef(name, aliases, &mut HashSet::new()),
        JsDocType::Parenthesized(inner) => substitute_local_typedefs(inner, aliases, shadowed)
            .map(Box::new)
            .map(JsDocType::Parenthesized),
        JsDocType::Nullable(inner) => substitute_local_typedefs(inner, aliases, shadowed)
            .map(Box::new)
            .map(JsDocType::Nullable),
        JsDocType::NonNullable(inner) => substitute_local_typedefs(inner, aliases, shadowed)
            .map(Box::new)
            .map(JsDocType::NonNullable),
        JsDocType::Optional(inner) => substitute_local_typedefs(inner, aliases, shadowed)
            .map(Box::new)
            .map(JsDocType::Optional),
        JsDocType::Variadic(inner) => substitute_local_typedefs(inner, aliases, shadowed)
            .map(Box::new)
            .map(JsDocType::Variadic),
        JsDocType::Array(inner) => substitute_local_typedefs(inner, aliases, shadowed)
            .map(Box::new)
            .map(JsDocType::Array),
        JsDocType::ReadonlyArray(inner) => substitute_local_typedefs(inner, aliases, shadowed)
            .map(Box::new)
            .map(JsDocType::ReadonlyArray),
        JsDocType::Union(members) => {
            let mut changed = false;
            let resolved = members
                .iter()
                .map(|member| {
                    substitute_local_typedefs(member, aliases, shadowed).map_or_else(
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
        JsDocType::ObjectLiteral(properties) => {
            let mut changed = false;
            let resolved = properties
                .iter()
                .map(|property| {
                    let type_ = substitute_local_typedefs(&property.type_, aliases, shadowed)
                        .map_or_else(
                            || property.type_.clone(),
                            |type_| {
                                changed = true;
                                type_
                            },
                        );
                    JsDocObjectProperty {
                        name: property.name.clone(),
                        type_,
                        optional: property.optional,
                        readonly: property.readonly,
                    }
                })
                .collect::<Vec<_>>();
            changed.then_some(JsDocType::ObjectLiteral(resolved))
        }
        JsDocType::Intrinsic(_)
        | JsDocType::BoundTypeParameter(_)
        | JsDocType::GenericReference { .. }
        | JsDocType::Import(_)
        | JsDocType::StringLiteral(_)
        | JsDocType::NumberLiteral(_)
        | JsDocType::BigIntLiteral(_)
        | JsDocType::Function(_)
        | JsDocType::Callback(_)
        | JsDocType::IndexedAccess { .. }
        | JsDocType::KeyOf(_)
        | JsDocType::Unsupported(_) => None,
    }
}

fn resolve_local_typedef(
    name: &str,
    aliases: &HashMap<String, JsDocType>,
    visiting: &mut HashSet<String>,
) -> Option<JsDocType> {
    if !visiting.insert(name.to_owned()) {
        return None;
    }
    let resolved = aliases
        .get(name)
        .and_then(|type_| resolve_local_typedef_target(type_, aliases, visiting));
    visiting.remove(name);
    resolved
}

fn resolve_local_typedef_target(
    type_: &JsDocType,
    aliases: &HashMap<String, JsDocType>,
    visiting: &mut HashSet<String>,
) -> Option<JsDocType> {
    match type_ {
        scalar @ (JsDocType::Intrinsic(_)
        | JsDocType::StringLiteral(_)
        | JsDocType::NumberLiteral(_)
        | JsDocType::BigIntLiteral(_)
        | JsDocType::Callback(_)) => Some(scalar.clone()),
        JsDocType::Named(next) => resolve_local_typedef(next, aliases, visiting),
        JsDocType::Parenthesized(inner) => resolve_local_typedef_target(inner, aliases, visiting)
            .map(Box::new)
            .map(JsDocType::Parenthesized),
        JsDocType::Nullable(inner) => resolve_local_typedef_target(inner, aliases, visiting)
            .map(Box::new)
            .map(JsDocType::Nullable),
        JsDocType::NonNullable(inner) => resolve_local_typedef_target(inner, aliases, visiting)
            .map(Box::new)
            .map(JsDocType::NonNullable),
        JsDocType::Optional(inner) => resolve_local_typedef_target(inner, aliases, visiting)
            .map(Box::new)
            .map(JsDocType::Optional),
        JsDocType::Array(inner) => resolve_local_typedef_target(inner, aliases, visiting)
            .map(Box::new)
            .map(JsDocType::Array),
        JsDocType::ReadonlyArray(inner) => resolve_local_typedef_target(inner, aliases, visiting)
            .map(Box::new)
            .map(JsDocType::ReadonlyArray),
        JsDocType::Union(members) => members
            .iter()
            .map(|member| resolve_local_typedef_target(member, aliases, visiting))
            .collect::<Option<Vec<_>>>()
            .map(JsDocType::Union),
        JsDocType::ObjectLiteral(properties) => properties
            .iter()
            .map(|property| {
                resolve_local_typedef_target(&property.type_, aliases, visiting).map(|type_| {
                    JsDocObjectProperty {
                        name: property.name.clone(),
                        type_,
                        optional: property.optional,
                        readonly: property.readonly,
                    }
                })
            })
            .collect::<Option<Vec<_>>>()
            .map(JsDocType::ObjectLiteral),
        _ => None,
    }
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
            | SyntaxKind::Constructor
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
                    source_declaration: None,
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
        JsDocTagKind::Overload => {
            if jsdoc_overload_creates_declaration(arena, declaration.node)? {
                return Err(JsDocCommentError::UnsupportedOverloadDeclaration(
                    declaration.node,
                ));
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
        JsDocTagKind::Implements => {
            if let Some(annotation) = tag.type_expression() {
                declaration.implements_types.push(annotation.planned());
            }
        }
    }
    Ok(())
}

fn jsdoc_overload_creates_declaration(
    arena: &NodeArena,
    declaration: NodeRef,
) -> Result<bool, JsDocCommentError> {
    let invalid = || JsDocCommentError::InvalidSourceNode(declaration);
    let record = arena.get(declaration.node).ok_or_else(invalid)?;
    if !matches!(
        record.kind,
        SyntaxKind::FunctionDeclaration | SyntaxKind::MethodDeclaration | SyntaxKind::Constructor
    ) {
        return Ok(false);
    }
    // PCObjectLiteralMembers remains set while nested declarations are parsed.
    let mut parent = record.parent;
    let mut visited = HashSet::new();
    while let Some(node) = parent {
        if !visited.insert(node) {
            return Err(invalid());
        }
        let record = arena.get(node).ok_or_else(invalid)?;
        if record.kind == SyntaxKind::ObjectLiteralExpression {
            return Ok(false);
        }
        parent = record.parent;
    }
    Ok(true)
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
    let Some(expected) = jsdoc_heritage_base_name(annotation.type_()) else {
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
    let base_text = annotation
        .text()
        .split_once('<')
        .map_or(annotation.text(), |(base, _)| base);
    let relative_start = base_text
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

fn jsdoc_heritage_base_name(type_: &JsDocType) -> Option<&str> {
    match type_ {
        JsDocType::Named(name) | JsDocType::GenericReference { name, .. } => Some(name),
        JsDocType::Parenthesized(inner) => jsdoc_heritage_base_name(inner),
        _ => None,
    }
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
        "overload" => Some(JsDocTagKind::Overload),
        "template" => Some(JsDocTagKind::Template),
        "satisfies" => Some(JsDocTagKind::Satisfies),
        "this" => Some(JsDocTagKind::This),
        "extends" | "augments" => Some(JsDocTagKind::Augments),
        "implements" => Some(JsDocTagKind::Implements),
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
        let mut scanner = Scanner::new(comment);
        scanner.reset_pos(start + 1);
        let token = scanner.scan_jsdoc_token();
        let Ok(body_start) = usize::try_from(token.range.end.get()) else {
            continue;
        };
        if !token.kind.is_keyword() || tags.iter().any(|existing| existing.start == start) {
            continue;
        }
        tags.push(ScannedTag {
            name: token.text,
            start,
            body_start,
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

    if kind != JsDocTagKind::Overload && source.as_bytes().get(cursor) == Some(&b'{') {
        let (parsed, next) = parse_braced_type(source, cursor, absolute_end, diagnostics)?;
        type_expression = parsed;
        cursor = skip_doc_whitespace(source, next, absolute_end);
    } else if matches!(
        kind,
        JsDocTagKind::Parameter
            | JsDocTagKind::Property
            | JsDocTagKind::Typedef
            | JsDocTagKind::Callback
            | JsDocTagKind::Overload
            | JsDocTagKind::Template
    ) {
        name_first = matches!(kind, JsDocTagKind::Parameter | JsDocTagKind::Property);
    } else if cursor < absolute_end {
        let type_end = unbraced_type_end(source, cursor, absolute_end);
        type_expression = parse_type_expression(source, cursor, type_end, diagnostics)?;
        cursor = skip_doc_whitespace(source, type_end, absolute_end);
    } else if matches!(
        kind,
        JsDocTagKind::Type
            | JsDocTagKind::Augments
            | JsDocTagKind::Implements
            | JsDocTagKind::Satisfies
            | JsDocTagKind::This
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
        overload_tags: Vec::new(),
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
        let bracket_start = cursor;
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
            let Some(close) = matching_template_bracket(source, bracket_start, end) else {
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
            constraint: if parameters.is_empty() {
                constraint.cloned()
            } else {
                None
            },
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
        NodeData::TypeLiteralNode(data) => project_object_type(arena, &data.members, range)?,
        NodeData::FunctionTypeNode(data) => project_function_type(arena, data, range)?,
        NodeData::IndexedAccessTypeNode(data) => JsDocType::IndexedAccess {
            object: Box::new(project_type(arena, data.object_type, range)?),
            index: Box::new(project_type(arena, data.index_type, range)?),
        },
        NodeData::TypeOperatorNode(data) if data.operator == SyntaxKind::KeyOfKeyword => {
            JsDocType::KeyOf(Box::new(project_type(arena, data.type_, range)?))
        }
        NodeData::TypeOperatorNode(data) if data.operator == SyntaxKind::ReadonlyKeyword => {
            match project_type(arena, data.type_, range)? {
                JsDocType::Array(element) => JsDocType::ReadonlyArray(element),
                _ => JsDocType::Unsupported(record.kind),
            }
        }
        NodeData::ImportTypeNode(data) => project_import_type(arena, data, range)?,
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
                (NodeData::Identifier(_) | NodeData::QualifiedName(_), Some(arguments)) => {
                    let name = qualified_type_name(arena, data.type_name)
                        .ok_or(JsDocCommentError::InvalidParserTree(range))?;
                    JsDocType::GenericReference {
                        name,
                        arguments: arguments
                            .nodes
                            .iter()
                            .map(|argument| project_type(arena, *argument, range))
                            .collect::<Result<Vec<_>, _>>()?,
                    }
                }
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

fn project_object_type(
    arena: &NodeArena,
    members: &ts_ast::NodeList,
    range: TextRange,
) -> Result<JsDocType, JsDocCommentError> {
    let mut properties = Vec::with_capacity(members.nodes.len());
    let mut names = HashSet::new();
    for member in &members.nodes {
        let record = arena
            .get(*member)
            .ok_or(JsDocCommentError::InvalidParserTree(range))?;
        let (name, type_, postfix, modifiers) = match &record.data {
            NodeData::PropertyDeclaration(property) => (
                property.name,
                property.type_,
                property.postfix_token,
                property.modifiers.as_ref(),
            ),
            NodeData::PropertySignatureDeclaration(property) => (
                property.name,
                Some(property.type_),
                property.postfix_token,
                property.modifiers.as_ref(),
            ),
            _ => return Ok(JsDocType::Unsupported(SyntaxKind::TypeLiteral)),
        };
        let Some(type_) = type_ else {
            return Ok(JsDocType::Unsupported(SyntaxKind::TypeLiteral));
        };
        let name = match arena.get(name).map(|node| &node.data) {
            Some(NodeData::Identifier(name)) => name.text.clone(),
            Some(NodeData::StringLiteral(name)) => name.text.clone(),
            Some(NodeData::NumericLiteral(name)) => name.text.clone(),
            Some(_) => return Ok(JsDocType::Unsupported(SyntaxKind::TypeLiteral)),
            None => return Err(JsDocCommentError::InvalidParserTree(range)),
        };
        if !names.insert(name.clone()) {
            return Ok(JsDocType::Unsupported(SyntaxKind::TypeLiteral));
        }
        let optional = if let Some(postfix) = postfix {
            let token = arena
                .get(postfix)
                .ok_or(JsDocCommentError::InvalidParserTree(range))?;
            if token.kind != SyntaxKind::QuestionToken {
                return Ok(JsDocType::Unsupported(SyntaxKind::TypeLiteral));
            }
            true
        } else {
            false
        };
        let readonly = modifiers.is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|modifier| {
                arena
                    .get(*modifier)
                    .is_some_and(|modifier| modifier.kind == SyntaxKind::ReadonlyKeyword)
            })
        });
        properties.push(JsDocObjectProperty {
            name,
            type_: project_type(arena, type_, range)?,
            optional,
            readonly,
        });
    }
    Ok(JsDocType::ObjectLiteral(properties))
}

fn project_function_type(
    arena: &NodeArena,
    function: &ts_ast::FunctionTypeNodeData,
    range: TextRange,
) -> Result<JsDocType, JsDocCommentError> {
    if function.type_parameters.is_some() || function.modifiers.is_some() {
        return Ok(JsDocType::Unsupported(SyntaxKind::FunctionType));
    }
    let Some(return_type) = function.type_ else {
        return Ok(JsDocType::Unsupported(SyntaxKind::FunctionType));
    };
    let mut parameters = Vec::with_capacity(function.parameters.nodes.len());
    for (index, parameter) in function.parameters.nodes.iter().enumerate() {
        let parameter = arena
            .get(*parameter)
            .ok_or(JsDocCommentError::InvalidParserTree(range))?;
        let NodeData::ParameterDeclaration(parameter) = &parameter.data else {
            return Ok(JsDocType::Unsupported(SyntaxKind::FunctionType));
        };
        let name = match arena.get(parameter.name).map(|node| &node.data) {
            Some(NodeData::Identifier(name)) => name.text.clone(),
            Some(_) => return Ok(JsDocType::Unsupported(SyntaxKind::FunctionType)),
            None => return Err(JsDocCommentError::InvalidParserTree(range)),
        };
        let rest = parameter.dot_dot_dot_token.is_some();
        if rest && index + 1 != function.parameters.nodes.len() {
            return Ok(JsDocType::Unsupported(SyntaxKind::FunctionType));
        }
        parameters.push(JsDocFunctionParameter {
            name,
            type_: parameter
                .type_
                .map(|type_| project_type(arena, type_, range))
                .transpose()?,
            optional: parameter.question_token.is_some() || parameter.initializer.is_some(),
            rest,
        });
    }
    Ok(JsDocType::Function(Box::new(JsDocFunctionType {
        parameters,
        return_type: project_type(arena, return_type, range)?,
    })))
}

fn project_import_type(
    arena: &NodeArena,
    import: &ts_ast::ImportTypeNodeData,
    range: TextRange,
) -> Result<JsDocType, JsDocCommentError> {
    if import.attributes.is_some() {
        return Ok(JsDocType::Unsupported(SyntaxKind::ImportType));
    }
    let argument = arena
        .get(import.argument)
        .ok_or(JsDocCommentError::InvalidParserTree(range))?;
    let NodeData::LiteralTypeNode(argument) = &argument.data else {
        return Ok(JsDocType::Unsupported(SyntaxKind::ImportType));
    };
    let literal = arena
        .get(argument.literal)
        .ok_or(JsDocCommentError::InvalidParserTree(range))?;
    let NodeData::StringLiteral(specifier) = &literal.data else {
        return Ok(JsDocType::Unsupported(SyntaxKind::ImportType));
    };
    let qualifier = import
        .qualifier
        .map(|qualifier| {
            qualified_type_name(arena, qualifier).ok_or(JsDocCommentError::InvalidParserTree(range))
        })
        .transpose()?;
    let type_arguments = import
        .type_arguments
        .as_ref()
        .map(|arguments| {
            arguments
                .nodes
                .iter()
                .map(|argument| project_type(arena, *argument, range))
                .collect::<Result<Vec<_>, _>>()
        })
        .transpose()?
        .unwrap_or_default();
    Ok(JsDocType::Import(JsDocImportType {
        specifier: specifier.text.clone(),
        qualifier,
        type_arguments,
        is_type_of: import.is_type_of,
    }))
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
        JsDocType::ObjectLiteral(properties) if properties.is_empty() => {
            Ok(bootstrap.empty_type_literal_type)
        }
        JsDocType::ObjectLiteral(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::TypeLiteral,
            range,
        }),
        JsDocType::Function(_) | JsDocType::Callback(_) => {
            Err(JsDocTypeResolutionError::UnsupportedType {
                kind: SyntaxKind::FunctionType,
                range,
            })
        }
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
        JsDocType::ObjectLiteral(properties) => properties.iter().try_for_each(|property| {
            validate_resolvable_type(store, global_types, options, &property.type_, range)
        }),
        JsDocType::Function(_) => Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::FunctionType,
            range,
        }),
        JsDocType::Callback(callback) => {
            validate_resolvable_callback(store, global_types, options, callback, range)
        }
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
        JsDocType::ObjectLiteral(properties) if properties.is_empty() => Ok(store
            .intrinsic_bootstrap()
            .ok_or(JsDocTypeResolutionError::MissingBootstrap)?
            .empty_type_literal_type),
        JsDocType::ObjectLiteral(properties) => {
            resolve_object_type(store, global_types, options, properties, range)
        }
        JsDocType::Function(_) | JsDocType::Callback(_) => {
            Err(JsDocTypeResolutionError::UnsupportedType {
                kind: SyntaxKind::FunctionType,
                range,
            })
        }
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

fn validate_resolvable_callback(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    callback: &PlannedJsDocCallback,
    range: TextRange,
) -> Result<(), JsDocTypeResolutionError> {
    let unsupported = || JsDocTypeResolutionError::UnsupportedType {
        kind: SyntaxKind::FunctionType,
        range,
    };
    if !callback.template_parameters.is_empty() || callback.this_type.is_some() {
        return Err(unsupported());
    }
    let mut names = HashSet::with_capacity(callback.parameters.len());
    let mut optional_seen = false;
    for parameter in &callback.parameters {
        let Some(annotation) = &parameter.type_ else {
            return Err(unsupported());
        };
        if parameter.name.is_empty()
            || !names.insert(parameter.name.as_str())
            || optional_seen && !parameter.optional
            || matches!(annotation.resolution_type(), JsDocType::Variadic(_))
        {
            return Err(unsupported());
        }
        optional_seen |= parameter.optional;
        validate_resolvable_type(
            store,
            global_types,
            options,
            annotation.resolution_type(),
            annotation.range(),
        )?;
    }
    let Some(return_type) = &callback.return_type else {
        return Err(unsupported());
    };
    validate_resolvable_type(
        store,
        global_types,
        options,
        return_type.resolution_type(),
        return_type.range(),
    )
}

fn resolve_object_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    properties: &[JsDocObjectProperty],
    range: TextRange,
) -> Result<TypeId, JsDocTypeResolutionError> {
    let property_types = properties
        .iter()
        .map(|property| {
            let type_ =
                resolve_complete_type(store, global_types, options, &property.type_, range)?;
            if !property.optional || !options.intrinsic.strict_null_checks {
                return Ok(type_);
            }
            let optional = store
                .intrinsic_bootstrap()
                .ok_or(JsDocTypeResolutionError::MissingBootstrap)?
                .undefined_or_missing_type;
            store
                .expression_union_type_with_global_types(
                    global_types,
                    &[type_, optional],
                    UnionReduction::Literal,
                )
                .map_err(|_| JsDocTypeResolutionError::UnionConstruction(range))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let members = PreparedSymbolTable::new(properties.len())
        .ok_or(JsDocTypeResolutionError::ObjectConstruction(range))?;
    let mut property_symbols = Vec::new();
    property_symbols
        .try_reserve_exact(properties.len())
        .map_err(|_| JsDocTypeResolutionError::ObjectConstruction(range))?;
    if !store.try_reserve_types(1)
        || !store.try_reserve_checker_symbol_allocations(properties.len(), 1)
        || !store.try_reserve_value_symbol_links(properties.len())
    {
        return Err(JsDocTypeResolutionError::ObjectConstruction(range));
    }

    let members = store.alloc_prepared_symbol_table(members);
    for (property, property_type) in properties.iter().zip(property_types) {
        let mut flags = SymbolFlags::PROPERTY;
        if property.optional {
            flags |= SymbolFlags::OPTIONAL;
        }
        let checks = if property.readonly {
            CheckFlags::READONLY
        } else {
            CheckFlags::NONE
        };
        let name = EscapedName::source(&property.name);
        let symbol = store.alloc_transient_symbol(flags, name.clone(), checks);
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(property_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(store.insert_symbol(members, name, symbol), Some(None));
        property_symbols.push(symbol);
    }
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
        .expect("a prepared JSDoc object type has valid synthetic ownership");
    assert!(store.set_structured_type_members(
        type_,
        Some(members),
        Some(property_symbols),
        None,
        None,
        None,
    ));
    Ok(type_)
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
    use crate::semantic::{
        CanonicalCheckerContext, IntrinsicBootstrapOptions, SourceCheckError, TypeData,
        UnsupportedSourceSyntax,
    };

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

    fn javascript_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/overloads.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    const GENERIC_OVERLOAD_COMMENT: &str = concat!(
        "/**\n",
        " * @template T\n",
        " * @param {T} value\n",
        " * @param {number=} count\n",
        " * @overload one value\n",
        " * @param {T} value\n",
        " * @return {T}\n",
        " * @overload with count\n",
        " * @param {T} value\n",
        " * @param {number} count\n",
        " * @returns {T}\n",
        " */",
    );

    #[test]
    fn jsdoc_overload_blocks_keep_signature_tags_separate() {
        let comment = type_tag(GENERIC_OVERLOAD_COMMENT);
        assert!(
            comment.diagnostics().is_empty(),
            "{:?}",
            comment.diagnostics()
        );
        assert_eq!(comment.template_tags().count(), 1);
        assert!(comment.return_tag().is_none());
        assert!(comment.parameter_tag("count").unwrap().is_optional());
        let kinds = comment
            .tags()
            .iter()
            .map(JsDocTag::kind)
            .collect::<Vec<_>>();
        assert_eq!(
            kinds,
            [
                JsDocTagKind::Template,
                JsDocTagKind::Parameter,
                JsDocTagKind::Parameter,
                JsDocTagKind::Overload,
                JsDocTagKind::Overload,
            ]
        );
        for (overload, parameter_count) in comment.tags()[3..].iter().zip([1, 2]) {
            assert!(overload.type_expression().is_none());
            let children = overload.overload_tags();
            assert_eq!(children.len(), parameter_count + 1);
            assert!(
                children[..parameter_count]
                    .iter()
                    .all(|tag| tag.kind() == JsDocTagKind::Parameter)
            );
            let result = children.last().unwrap();
            assert_eq!(result.kind(), JsDocTagKind::Return);
            assert_eq!(
                result.type_expression().unwrap().type_(),
                &JsDocType::Named("T".to_owned())
            );
            assert_eq!(overload.range().end, result.range().end);
            assert!(children.iter().all(|tag| {
                overload.range().start < tag.range().start
                    && tag.range().end <= overload.range().end
            }));
        }
    }

    #[test]
    fn jsdoc_overload_blocks_do_not_change_arrow_or_function_expression_signatures() {
        for initializer in [
            "(value, count) => value",
            "function (value, count) { return value; }",
        ] {
            for inline in [false, true] {
                let source = if inline {
                    format!("const read = {GENERIC_OVERLOAD_COMMENT}{initializer};")
                } else {
                    format!("{GENERIC_OVERLOAD_COMMENT}\nconst read = {initializer};")
                };
                let javascript = parse_javascript_source_file(&source);
                assert!(
                    javascript.diagnostics.is_empty(),
                    "{:?}",
                    javascript.diagnostics
                );
                let root = NodeRef::new(
                    javascript.arena.id(),
                    FileId::new(109),
                    javascript.source_file,
                );
                let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
                assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
                let [declaration] = plan.declarations() else {
                    panic!("expected one source-owned callable annotation")
                };
                let [template] = declaration.template_parameters() else {
                    panic!("expected only the host template")
                };
                assert_eq!(template.name(), "T");
                let [value, count] = declaration.parameters() else {
                    panic!("overload parameters must not enter the host signature")
                };
                assert_eq!(value.name(), "value");
                assert_eq!(
                    value.type_().unwrap().type_(),
                    &JsDocType::Named("T".to_owned())
                );
                assert_eq!(count.name(), "count");
                assert!(count.is_optional());
                assert!(declaration.return_type().is_none());
            }
        }
    }

    #[test]
    fn jsdoc_overload_blocks_preserve_host_tags_after_the_signature_ends() {
        for boundary in [
            "@returns {number}",
            "@deprecated end of overload",
            "@private",
        ] {
            let source = format!(
                "/**\n * @template T\n * @param {{T}} before\n * @overload\n \
                 * @param {{number}} nested\n * {boundary}\n * @template U\n \
                 * @param {{U}} after\n * @return {{U}}\n */\n \
                 const read = (before, after) => after;"
            );
            let javascript = parse_javascript_source_file(&source);
            let root = NodeRef::new(
                javascript.arena.id(),
                FileId::new(110),
                javascript.source_file,
            );
            let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
            assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
            let [declaration] = plan.declarations() else {
                panic!("expected one arrow annotation")
            };
            assert_eq!(
                declaration
                    .template_parameters()
                    .iter()
                    .map(PlannedJsDocTemplateParameter::name)
                    .collect::<Vec<_>>(),
                ["T", "U"]
            );
            assert_eq!(
                declaration
                    .parameters()
                    .iter()
                    .map(PlannedJsDocParameter::name)
                    .collect::<Vec<_>>(),
                ["before", "after"]
            );
            assert_eq!(
                declaration.return_type().unwrap().type_(),
                &JsDocType::Named("U".to_owned())
            );
        }

        let source = concat!(
            "/** @overload @param {number} nested */\n",
            "/** @param {string} value @returns {string} */\n",
            "const read = value => value;",
        );
        let javascript = parse_javascript_source_file(source);
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(111),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [declaration] = plan.declarations() else {
            panic!("adjacent comments must retain one host")
        };
        assert_eq!(declaration.parameters().len(), 1);
        assert_eq!(declaration.parameters()[0].name(), "value");
        assert_eq!(
            declaration.return_type().unwrap().type_(),
            &JsDocType::Intrinsic(JsDocIntrinsicType::String)
        );
    }

    #[test]
    fn jsdoc_overload_blocks_leave_declaration_overloads_unsupported() {
        let comment = "/** @overload @param {number} value @returns {number} */";
        for (source, kind) in [
            (
                format!("{comment}\nfunction read(value) {{ return value; }}"),
                SyntaxKind::FunctionDeclaration,
            ),
            (
                format!("class Box {{\n{comment}\nread(value) {{ return value; }} }}"),
                SyntaxKind::MethodDeclaration,
            ),
            (
                format!("class Box {{\n{comment}\nconstructor(value) {{}} }}"),
                SyntaxKind::Constructor,
            ),
        ] {
            let javascript = parse_javascript_source_file(&source);
            assert!(
                javascript.diagnostics.is_empty(),
                "{:?}",
                javascript.diagnostics
            );
            let file = FileId::new(112);
            let root = NodeRef::new(javascript.arena.id(), file, javascript.source_file);
            let error = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap_err();
            let JsDocCommentError::UnsupportedOverloadDeclaration(node) = error else {
                panic!("expected an explicit unsupported declaration, got {error:?}")
            };
            assert_eq!(node.arena, javascript.arena.id());
            assert_eq!(node.file, file);
            assert_eq!(javascript.arena.get(node.node).unwrap().kind, kind);
        }
    }

    #[test]
    fn jsdoc_overload_blocks_are_ignored_on_object_methods() {
        let source = concat!(
            "const object = {\n",
            "/**\n * @param {string} value\n * @overload\n",
            " * @this {number}\n * @param {number} nested\n * @returns {number}\n */\n",
            "read(value) { return value; }\n};",
        );
        let javascript = parse_javascript_source_file(source);
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(113),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [declaration] = plan.declarations() else {
            panic!("expected one object method annotation")
        };
        assert_eq!(declaration.parameters().len(), 1);
        assert_eq!(declaration.parameters()[0].name(), "value");
        assert!(declaration.this_type().is_none());
        assert!(declaration.return_type().is_none());
    }

    #[test]
    fn jsdoc_overload_blocks_are_ignored_in_nested_object_member_declarations() {
        let comment = "/** @overload @param {number} value @returns {number} */";
        for (nested, kind) in [
            (
                format!("{comment}\nfunction nested(value) {{ return value; }}"),
                SyntaxKind::FunctionDeclaration,
            ),
            (
                format!("class Nested {{\n{comment}\nconstructor(value) {{}} }}"),
                SyntaxKind::Constructor,
            ),
            (
                format!("class Nested {{\n{comment}\nread(value) {{ return value; }} }}"),
                SyntaxKind::MethodDeclaration,
            ),
        ] {
            let source = format!("const object = {{ read() {{ {nested} }} }};");
            let javascript = parse_javascript_source_file(&source);
            assert!(
                javascript.diagnostics.is_empty(),
                "{:?}",
                javascript.diagnostics
            );
            let root = NodeRef::new(
                javascript.arena.id(),
                FileId::new(115),
                javascript.source_file,
            );
            let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
            assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
            let [declaration] = plan.declarations() else {
                panic!("expected one nested annotation")
            };
            assert_eq!(
                javascript.arena.get(declaration.node().node).unwrap().kind,
                kind
            );
            assert!(declaration.parameters().is_empty());
            assert!(declaration.return_type().is_none());

            let outside = parse_javascript_source_file(&format!("{source}\n{nested}"));
            let root = NodeRef::new(outside.arena.id(), FileId::new(116), outside.source_file);
            assert!(matches!(
                plan_javascript_source_jsdoc(&outside.arena, root),
                Err(JsDocCommentError::UnsupportedOverloadDeclaration(_))
            ));
        }
    }

    #[test]
    fn jsdoc_overload_blocks_single_group_does_not_publish_an_overload_arrow_signature() {
        let source = concat!(
            "/** @template T @overload @param {T} value @returns {T} */\n",
            "const read = value => value;",
        );
        let javascript = parse_javascript_source_file(source);
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let file = FileId::new(117);
        let (arrow, function) = javascript
            .arena
            .iter()
            .find_map(|(node, record)| match &record.data {
                NodeData::ArrowFunction(function) => {
                    Some((NodeRef::new(javascript.arena.id(), file, node), function))
                }
                _ => None,
            })
            .unwrap();
        assert!(function.type_parameters.is_none());
        assert!(function.type_.is_none());
        let mut context = javascript_context(&javascript, file);
        // Template-only arrows need their own implementation, not an overload's signature.
        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::JsDoc(_)
            ))
        ));
        assert!(context.store().signature_links(arrow).is_none());
    }

    #[test]
    fn jsdoc_overload_blocks_single_group_keeps_the_primary_checker_signature() {
        let source = concat!(
            "/** @template T @param {T} value @returns {T}\n",
            " * @overload @param {number} value @return {number} */\n",
            "const read = value => value;",
        );
        let javascript = parse_javascript_source_file(source);
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let file = FileId::new(118);
        let name = javascript
            .arena
            .iter()
            .find_map(|(_, record)| match &record.data {
                NodeData::VariableDeclaration(variable) => {
                    Some(NodeRef::new(javascript.arena.id(), file, variable.name))
                }
                _ => None,
            })
            .unwrap();
        let mut context = javascript_context(&javascript, file);
        context.check_source_file(file).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let callable = context.get_type_at_location(name).unwrap();
        assert_eq!(
            context.type_to_string(callable).unwrap(),
            "<T>(value: T) => T"
        );
        let before = (context.store().type_len(), context.store().signature_len());
        context.recheck_source_file(file).unwrap();
        assert_eq!(context.get_type_at_location(name).unwrap(), callable);
        assert_eq!(
            (context.store().type_len(), context.store().signature_len()),
            before
        );
    }

    #[test]
    fn jsdoc_overload_blocks_report_nested_templates_without_binding_them_to_the_host() {
        let source = concat!(
            "/**\n * @overload\n * @template Bad\n * @param {Bad} nested\n",
            " * @returns {Bad}\n * @template Good\n * @param {Good} value\n */\n",
            "const read = value => value;",
        );
        let javascript = parse_javascript_source_file(source);
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(114),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let [diagnostic] = plan.diagnostics() else {
            panic!("expected one nested-template diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 8039);
        let start = source.find("@template").unwrap() + 1;
        assert_eq!(
            diagnostic.range_override.unwrap().range(),
            checked_range(start, start + "template".len()).unwrap()
        );
        let [declaration] = plan.declarations() else {
            panic!("expected one arrow annotation")
        };
        let [template] = declaration.template_parameters() else {
            panic!("the nested template must remain inside its overload")
        };
        assert_eq!(template.name(), "Good");
        assert_eq!(declaration.parameters().len(), 1);
        assert_eq!(declaration.parameters()[0].name(), "value");
        assert!(declaration.return_type().is_none());
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
    fn reparsed_typedefs_keep_comments_on_the_real_host_exactly_once() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @typedef {number} Value */\n",
            "/** @type {Value} */\n",
            "const first = 1;\n",
            "/** @typedef {{ label: string }} Shape */\n",
            "/** @type {Shape} */\n",
            "var second;",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let file = FileId::new(95);
        let root = NodeRef::new(javascript.arena.id(), file, javascript.source_file);
        let NodeData::SourceFile(source) = &javascript.arena.get(root.node).unwrap().data else {
            panic!("expected a JavaScript source root")
        };
        let [first_alias, _, second_alias, _] = source.statements.nodes.as_slice() else {
            panic!("expected two reparsed aliases and their host statements")
        };
        let aliases = [
            NodeRef::new(javascript.arena.id(), file, *first_alias),
            NodeRef::new(javascript.arena.id(), file, *second_alias),
        ];

        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        assert_eq!(plan.declarations().len(), 2);
        for (declaration, (name, alias)) in plan
            .declarations()
            .iter()
            .zip([("Value", aliases[0]), ("Shape", aliases[1])])
        {
            assert_eq!(
                javascript.arena.get(declaration.node().node).unwrap().kind,
                SyntaxKind::VariableDeclaration
            );
            let [typedef] = declaration.typedefs() else {
                panic!("expected one typedef on its real JavaScript host")
            };
            assert_eq!(typedef.name(), name);
            assert_eq!(typedef.source_declaration(), Some(alias));
            assert_eq!(
                declaration.type_().unwrap().type_(),
                &JsDocType::Named(name.to_owned())
            );
            assert_eq!(
                declaration.type_().unwrap().resolved_alias_name(),
                Some(name)
            );
        }
    }

    #[test]
    fn reparsed_import_typedefs_keep_their_unsupported_resolution_boundary() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @typedef {{ a: 1, m: 1 }} Shape */\n",
            "/** @typedef {import('./types').Shape} Imported */\n",
            "/** @type {Imported} */\n",
            "var value;",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let file = FileId::new(96);
        let root = NodeRef::new(javascript.arena.id(), file, javascript.source_file);
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let [declaration] = plan.declarations() else {
            panic!("expected one real JavaScript declaration")
        };
        let [shape, imported] = declaration.typedefs() else {
            panic!("expected both ordered typedefs on their real host")
        };
        assert_eq!(shape.name(), "Shape");
        assert_eq!(imported.name(), "Imported");
        assert!(shape.source_declaration().is_some());
        assert!(imported.source_declaration().is_some());

        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let context = context(&parsed, options);
        let globals = context.global_types();
        preflight_planned_jsdoc_type(context.store(), globals, options, shape.type_().unwrap())
            .unwrap();
        let import_annotation = imported.type_().unwrap();
        assert_eq!(
            preflight_planned_jsdoc_type(context.store(), globals, options, import_annotation),
            Err(JsDocTypeResolutionError::UnsupportedType {
                kind: SyntaxKind::ImportType,
                range: import_annotation.range(),
            })
        );
        let annotation = declaration.type_().unwrap();
        assert_eq!(annotation.resolved_alias_name(), None);
        assert_eq!(
            preflight_planned_jsdoc_type(context.store(), globals, options, annotation),
            Err(JsDocTypeResolutionError::UnresolvedTypeReference {
                name: "Imported".to_owned(),
                range: annotation.range(),
            })
        );
    }

    #[test]
    fn forged_reparsed_typedefs_fail_before_comment_ownership_changes() {
        for corruption in 0..3 {
            let mut javascript = parse_javascript_source_file(concat!(
                "/** @typedef {number} Value */\n",
                "/** @type {Value} */\n",
                "const value = 1;",
            ));
            let NodeData::SourceFile(source) =
                &javascript.arena.get(javascript.source_file).unwrap().data
            else {
                panic!("expected a JavaScript source root")
            };
            let [alias, _] = source.statements.nodes.as_slice() else {
                panic!("expected one reparsed typedef and its host")
            };
            let alias = *alias;
            let name = match &javascript.arena.get(alias).unwrap().data {
                NodeData::TypeAliasDeclaration(alias) => alias.name,
                _ => panic!("expected a reparsed typedef payload"),
            };
            match corruption {
                0 => javascript.arena.get_mut(alias).unwrap().flags = NodeFlags::default(),
                1 => javascript.arena.get_mut(alias).unwrap().parent = None,
                2 => {
                    let NodeData::Identifier(identifier) =
                        &mut javascript.arena.get_mut(name).unwrap().data
                    else {
                        panic!("expected the typedef identifier")
                    };
                    identifier.text = "Different".to_owned();
                }
                _ => unreachable!(),
            }
            let file = FileId::new(97 + corruption);
            let root = NodeRef::new(javascript.arena.id(), file, javascript.source_file);
            let alias = NodeRef::new(javascript.arena.id(), file, alias);
            assert_eq!(
                plan_javascript_source_jsdoc(&javascript.arena, root),
                Err(JsDocCommentError::InvalidSourceNode(alias)),
                "corruption case {corruption}"
            );
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
    fn local_composite_typedef_aliases_preserve_names_and_canonical_identity() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @typedef {number} NS.Base */\n",
            "/** @typedef {NS.Base | string} NS.Scalar */\n",
            "/** @typedef {NS.Scalar[]} NS.Mutable */\n",
            "/** @typedef {ReadonlyArray<NS.Mutable>} NS.Readonly */\n",
            "/** @typedef {?NS.Readonly} NS.Nullable */\n",
            "/** @typedef {NS.Scalar=} NS.Optional */\n",
            "/** @type {NS.Scalar} */ const scalar = 1;\n",
            "/** @type {NS.Mutable} */ const mutable = [];\n",
            "/** @type {NS.Readonly} */ const view = [];\n",
            "/** @type {NS.Nullable} */ const nullable = null;\n",
            "/** @type {NS.Optional} */ const optional = undefined;",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(93),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());

        let parsed = parse_source_file(concat!(
            "interface Array<T> { length: number; } ",
            "interface ReadonlyArray<T> { readonly length: number; } ",
            "const marker = 1;",
        ));
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        let expected = [
            ("NS.Scalar", "/** @type {number | string} */"),
            ("NS.Mutable", "/** @type {(number | string)[]} */"),
            (
                "NS.Readonly",
                "/** @type {ReadonlyArray<(number | string)[]>} */",
            ),
            (
                "NS.Nullable",
                "/** @type {?ReadonlyArray<(number | string)[]>} */",
            ),
            ("NS.Optional", "/** @type {(number | string)=} */"),
        ];
        assert_eq!(plan.declarations().len(), expected.len());

        for (declaration, (name, direct)) in plan.declarations().iter().zip(expected) {
            let annotation = declaration.type_().unwrap();
            assert_eq!(annotation.type_(), &JsDocType::Named(name.to_owned()));
            assert_eq!(annotation.resolved_alias_name(), Some(name));

            let cold = context.store().type_len();
            preflight_planned_jsdoc_type(context.store(), &globals, options, annotation).unwrap();
            assert_eq!(context.store().type_len(), cold);

            let resolved = resolve_planned_jsdoc_type(
                context.store_mut_for_test(),
                &globals,
                options,
                annotation,
            )
            .unwrap();
            let direct = type_tag(direct);
            let direct_annotation = direct.type_tag().unwrap().type_expression().unwrap();
            let canonical = resolve_jsdoc_type(
                context.store_mut_for_test(),
                &globals,
                options,
                direct_annotation,
            )
            .unwrap();
            assert_eq!(resolved, canonical);

            let warm = context.store().type_len();
            assert_eq!(
                resolve_planned_jsdoc_type(
                    context.store_mut_for_test(),
                    &globals,
                    options,
                    annotation,
                ),
                Ok(resolved)
            );
            assert_eq!(context.store().type_len(), warm);
        }
    }

    #[test]
    fn local_structural_typedefs_resolve_nested_aliases_and_exact_property_shapes() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @typedef {1} NS.Value */\n",
            "/** @typedef {{ readonly id: NS.Value, nested: { value: NS.Value }, label?: string }} NS.Box */\n",
            "/** @type {NS.Box} */\n",
            "var box;",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(94),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let [declaration] = plan.declarations() else {
            panic!("expected one structural typedef declaration")
        };
        let annotation = declaration.type_().unwrap();
        assert_eq!(annotation.type_(), &JsDocType::Named("NS.Box".to_owned()));
        assert_eq!(annotation.resolved_alias_name(), Some("NS.Box"));

        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        );
        preflight_planned_jsdoc_type(context.store(), &globals, options, annotation).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            before
        );

        let resolved =
            resolve_planned_jsdoc_type(context.store_mut_for_test(), &globals, options, annotation)
                .unwrap();
        assert_eq!(
            context.type_to_string(resolved).unwrap(),
            "{ readonly id: 1; nested: { value: 1; }; label?: string; }"
        );

        let record = context.store().type_payload(resolved).unwrap();
        assert_eq!(
            record.object_flags(),
            ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        );
        assert!(record.symbol().is_none());
        let TypeData::Object(object) = record.data() else {
            panic!("expected one structural object type")
        };
        let properties = object.structured.properties.as_deref().unwrap();
        let members = context
            .store()
            .symbol_table(object.structured.members.unwrap())
            .unwrap();
        assert_eq!(properties.len(), 3);
        for (symbol, (name, optional, readonly)) in properties.iter().zip([
            ("id", false, true),
            ("nested", false, false),
            ("label", true, false),
        ]) {
            let property = context.store().symbol(*symbol).unwrap();
            assert_eq!(property.name().as_utf8(), Some(name));
            assert_eq!(
                property.flags(),
                SymbolFlags::PROPERTY
                    | SymbolFlags::TRANSIENT
                    | if optional {
                        SymbolFlags::OPTIONAL
                    } else {
                        SymbolFlags::NONE
                    }
            );
            assert_eq!(
                property.check_flags().contains(CheckFlags::READONLY),
                readonly
            );
            assert_eq!(members.get_source(name), Some(*symbol));
            assert!(
                context
                    .store()
                    .value_symbol_links(*symbol)
                    .and_then(|links| links.resolved_type)
                    .is_some()
            );
        }
    }

    #[test]
    fn generic_local_typedefs_apply_constraints_defaults_and_canonical_array_caches() {
        let javascript = parse_javascript_source_file(concat!(
            "/**\n",
            " * @template {string | number} T\n",
            " * @template [U=T]\n",
            " * @typedef {(T | U)[]} NS.List\n",
            " */\n",
            "/** @type {NS.List<string>} */\n",
            "const first = [];\n",
            "/** @type {NS.List<number, string>} */\n",
            "const second = [];",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(102),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [first, second] = plan.declarations() else {
            panic!("expected both generic typedef consumers")
        };
        let [definition] = first.typedefs() else {
            panic!("expected the source-owned generic typedef")
        };
        let [constrained, defaulted] = definition.template_parameters() else {
            panic!("expected the constrained and defaulted template parameters")
        };
        assert!(constrained.constraint().is_some());
        assert_eq!(
            defaulted.default_type().unwrap().type_(),
            &JsDocType::Named("T".to_owned()),
        );

        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "const marker = 1;",
        ));
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        for (declaration, direct) in [
            (first, "/** @type {Array<string>} */"),
            (second, "/** @type {Array<string | number>} */"),
        ] {
            let annotation = declaration.type_().unwrap();
            assert_eq!(annotation.resolved_alias_name(), Some("NS.List"));
            let before = context.store().type_len();
            preflight_planned_jsdoc_type(context.store(), &globals, options, annotation).unwrap();
            assert_eq!(context.store().type_len(), before);

            let resolved = resolve_planned_jsdoc_type(
                context.store_mut_for_test(),
                &globals,
                options,
                annotation,
            )
            .unwrap();
            let direct = type_tag(direct);
            let direct = direct.type_tag().unwrap().type_expression().unwrap();
            assert_eq!(
                resolve_jsdoc_type(context.store_mut_for_test(), &globals, options, direct),
                Ok(resolved),
            );

            let warm = context.store().type_len();
            assert_eq!(
                resolve_planned_jsdoc_type(
                    context.store_mut_for_test(),
                    &globals,
                    options,
                    annotation,
                ),
                Ok(resolved),
            );
            assert_eq!(context.store().type_len(), warm);
        }
    }

    #[test]
    fn nested_generic_typedefs_preserve_structural_members_and_dependent_defaults() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @template T @typedef {{ readonly value: T }} NS.Box */\n",
            "/** @template [T=number] @typedef {NS.Box<T>} NS.Holder */\n",
            "/** @type {NS.Holder<string>} */\n",
            "var text;\n",
            "/** @type {NS.Holder<number>} */\n",
            "var count;",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(103),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();

        for (declaration, expected) in plan
            .declarations()
            .iter()
            .zip(["{ readonly value: string; }", "{ readonly value: number; }"])
        {
            let annotation = declaration.type_().unwrap();
            assert_eq!(annotation.resolved_alias_name(), Some("NS.Holder"));
            let resolved = resolve_planned_jsdoc_type(
                context.store_mut_for_test(),
                &globals,
                options,
                annotation,
            )
            .unwrap();
            assert_eq!(context.type_to_string(resolved).unwrap(), expected);
        }
    }

    #[test]
    fn generic_typedef_arguments_keep_host_template_parameters_shadowed() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @template T @typedef {T[]} Box */\n",
            "/**\n",
            " * @template T\n",
            " * @param {Box<T>} values\n",
            " * @returns {T}\n",
            " */\n",
            "function first(values) {}",
        ));
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(104),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let [declaration] = plan.declarations() else {
            panic!("expected one template-annotated JavaScript function")
        };
        let annotation = declaration.parameter("values").unwrap().type_().unwrap();
        assert_eq!(annotation.resolved_alias_name(), Some("Box"));

        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface Carrier<T> {}",
        ));
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let parameter = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                if record.kind != SyntaxKind::InterfaceDeclaration {
                    return None;
                }
                let NodeData::InterfaceDeclaration(interface) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                    return None;
                };
                (name.text == "Carrier").then(|| {
                    NodeRef::new(
                        parsed.arena.id(),
                        FileId::new(0),
                        interface.type_parameters.as_ref().unwrap().nodes[0],
                    )
                })
            })
            .unwrap();
        let symbol = context
            .file(FileId::new(0))
            .unwrap()
            .1
            .symbol(parameter)
            .unwrap();
        let template = context.get_declared_type_of_symbol(symbol).unwrap();
        let globals = context.global_types().clone();
        let signature = resolve_planned_jsdoc_signature(
            context.store_mut_for_test(),
            &globals,
            options,
            declaration,
            &[JsDocTypeParameterBinding::new("T", template)],
        )
        .unwrap();
        let array = context
            .store_mut_for_test()
            .create_canonical_array_type(&globals, template, false)
            .unwrap();
        assert_eq!(signature.parameters()[0].type_(), Some(array));
        assert_eq!(signature.return_type(), Some(template));
    }

    #[test]
    fn invalid_generic_typedef_constraints_arity_and_cycles_fail_without_allocations() {
        for source in [
            concat!(
                "/** @template {string} T @typedef {T[]} Box */\n",
                "/** @type {Box<number>} */ var value;",
            ),
            concat!(
                "/** @template T @typedef {T[]} Box */\n",
                "/** @type {Box<string, number>} */ var value;",
            ),
            concat!(
                "/** @template T @typedef {Loop<T>} Loop */\n",
                "/** @type {Loop<string>} */ var value;",
            ),
            concat!(
                "/** @template T @typedef {T[]} Box */\n",
                "/** @template T @typedef {T} Box */\n",
                "/** @type {Box<string>} */ var value;",
            ),
        ] {
            let javascript = parse_javascript_source_file(source);
            assert!(
                javascript.diagnostics.is_empty(),
                "{source}: {:?}",
                javascript.diagnostics
            );
            let root = NodeRef::new(
                javascript.arena.id(),
                FileId::new(105),
                javascript.source_file,
            );
            let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
            let annotation = plan
                .declarations()
                .iter()
                .find_map(PlannedJavaScriptDeclaration::type_)
                .unwrap();
            let parsed = parse_source_file(concat!(
                "interface Array<T> {} ",
                "interface ReadonlyArray<T> {}",
            ));
            let options = CanonicalCheckerOptions::default();
            let mut context = context(&parsed, options);
            let globals = context.global_types().clone();
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
            );
            let expected = JsDocTypeResolutionError::UnsupportedType {
                kind: SyntaxKind::TypeReference,
                range: annotation.range(),
            };

            assert_eq!(
                preflight_planned_jsdoc_type(context.store(), &globals, options, annotation),
                Err(expected.clone()),
                "{source}",
            );
            assert_eq!(
                resolve_planned_jsdoc_type(
                    context.store_mut_for_test(),
                    &globals,
                    options,
                    annotation,
                ),
                Err(expected),
                "{source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().symbol_store().symbol_table_len(),
                ),
                before,
                "{source}",
            );
        }
    }

    #[test]
    fn optional_structural_properties_use_the_configured_missing_type() {
        for exact_optional_property_types in [false, true] {
            let parsed = parse_source_file("const marker = 1;");
            let options = CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types,
                },
                ..CanonicalCheckerOptions::default()
            };
            let mut context = context(&parsed, options);
            let globals = context.global_types().clone();
            let comment = type_tag("/** @type {{ value?: number }} */");
            let annotation = comment.type_tag().unwrap().type_expression().unwrap();
            let resolved =
                resolve_jsdoc_type(context.store_mut_for_test(), &globals, options, annotation)
                    .unwrap();
            let record = context.store().type_payload(resolved).unwrap();
            let TypeData::Object(object) = record.data() else {
                panic!("expected one structural object type")
            };
            let [property] = object.structured.properties.as_deref().unwrap() else {
                panic!("expected one optional property")
            };
            let property_type = context
                .store()
                .value_symbol_links(*property)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let TypeData::Union(union) =
                context.store().type_payload(property_type).unwrap().data()
            else {
                panic!("expected the optional property to include its missing type")
            };
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            assert!(union.union.types.contains(&bootstrap.number_type));
            assert!(
                union
                    .union
                    .types
                    .contains(&bootstrap.undefined_or_missing_type)
            );
            let expected = if exact_optional_property_types {
                "{ value?: number; }"
            } else {
                "{ value?: number | undefined; }"
            };
            assert_eq!(context.type_to_string(resolved).unwrap(), expected);
        }
    }

    #[test]
    fn unresolved_structural_properties_fail_before_semantic_allocation() {
        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        let comment = type_tag("/** @type {{ first: 1, nested: { value: Missing } }} */");
        let annotation = comment.type_tag().unwrap().type_expression().unwrap();
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        );

        assert_eq!(
            resolve_jsdoc_type(context.store_mut_for_test(), &globals, options, annotation),
            Err(JsDocTypeResolutionError::UnresolvedTypeReference {
                name: "Missing".to_owned(),
                range: annotation.range(),
            })
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            before
        );
    }

    #[test]
    fn object_typedef_properties_retain_alias_names_after_canonical_resolution() {
        let javascript = parse_javascript_source_file(concat!(
            "/**\n",
            " * @typedef {object} T\n",
            " * @property {boolean} await\n",
            " */\n",
            "/** @type {T} */\n",
            "const a = 1;\n",
            "/** @type {T} */\n",
            "const b = { await: false };\n",
            "/** @param {boolean} await */\n",
            "function c(await) {}",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(91),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [first, second, callable] = plan.declarations() else {
            panic!("expected two annotated variables and one annotated function")
        };
        let [alias] = first.typedefs() else {
            panic!("expected one object typedef")
        };
        let [property] = alias.properties() else {
            panic!("expected one object typedef property")
        };
        assert_eq!(alias.name(), "T");
        assert_eq!(property.name(), "await");
        assert_eq!(
            property.type_().unwrap().type_(),
            &JsDocType::Intrinsic(JsDocIntrinsicType::Boolean)
        );
        assert_eq!(callable.parameters()[0].name(), "await");

        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        let object = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .non_primitive_type;
        for annotation in [first.type_().unwrap(), second.type_().unwrap()] {
            assert_eq!(annotation.type_(), &JsDocType::Named("T".to_owned()));
            assert_eq!(annotation.resolved_alias_name(), Some("T"));
            assert_eq!(
                resolve_planned_jsdoc_type(
                    context.store_mut_for_test(),
                    &globals,
                    options,
                    annotation,
                ),
                Ok(object)
            );
        }
        assert_eq!(context.type_to_string(object).unwrap(), "object");
    }

    #[test]
    fn duplicate_cyclic_and_unsupported_typedefs_remain_typed_boundaries() {
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
                "/** @typedef {Next[]} Value */\n",
                "/** @typedef {?Value} Next */\n",
                "/** @type {Value} */\n",
                "const value = 1;",
            ),
            concat!(
                "/** @typedef {number} NS.Base */\n",
                "/** @typedef {string} NS.Base */\n",
                "/** @typedef {NS.Base | boolean} Value */\n",
                "/** @type {Value} */\n",
                "const value = 1;",
            ),
            concat!(
                "/** @typedef {Missing | number} Value */\n",
                "/** @type {Value} */\n",
                "const value = 1;",
            ),
            concat!(
                "/** @typedef {{ value: Value }} Value */\n",
                "/** @type {Value} */\n",
                "const value = 1;",
            ),
            concat!(
                "/** @typedef {(value: number) => number} Value */\n",
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
            let mut context = context(&parsed, options);
            let globals = context.global_types().clone();
            let cold = context.store().type_len();
            let expected = JsDocTypeResolutionError::UnresolvedTypeReference {
                name: "Value".to_owned(),
                range: annotation.range(),
            };
            assert_eq!(
                preflight_planned_jsdoc_type(context.store(), &globals, options, annotation,),
                Err(expected.clone())
            );
            assert_eq!(
                resolve_planned_jsdoc_type(
                    context.store_mut_for_test(),
                    &globals,
                    options,
                    annotation,
                ),
                Err(expected)
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
    fn nameless_jsdoc_callable_parameter_preserves_its_complete_function_signature() {
        let source = concat!(
            "/** @param {(x: string) => string} */\n",
            "function invoke(callback) { return callback(123); }",
        );
        let javascript = parse_javascript_source_file(source);
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(102),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let [declaration] = plan.declarations() else {
            panic!("expected one callable-owning function declaration")
        };
        let parameter = declaration.parameter("callback").unwrap();
        let annotation = parameter.type_().unwrap();
        let JsDocType::Function(function) = annotation.type_() else {
            panic!("expected the complete JSDoc callable annotation")
        };
        let [argument] = function.parameters() else {
            panic!("expected one callable parameter")
        };
        assert_eq!(argument.name(), "x");
        assert_eq!(
            argument.type_(),
            Some(&JsDocType::Intrinsic(JsDocIntrinsicType::String)),
        );
        assert_eq!(
            function.return_type(),
            &JsDocType::Intrinsic(JsDocIntrinsicType::String),
        );
        let start = source.find("callback)").unwrap();
        assert_eq!(parameter.range().start.get() as usize, start);
        assert_eq!(
            parameter.range().end.get() as usize,
            start + "callback".len(),
        );
    }

    #[test]
    fn nested_arrow_body_type_comments_keep_their_source_and_template_owners() {
        let source = concat!(
            "/** @typedef {number} T */\n",
            "/**\n",
            " * @template T\n",
            " * @param {T | undefined} value\n",
            " * @returns {T}\n",
            " */\n",
            "const read = value => /** @type {string} */ ",
            "(/** @type {T} */ ({ ...value }));",
        );
        let javascript = parse_javascript_source_file(source);
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(104),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [declaration] = plan.declarations() else {
            panic!("expected one source-owned generic arrow declaration")
        };
        let [outer, inner] = plan.expressions.as_slice() else {
            panic!("expected both nested arrow-body type comments")
        };
        assert_eq!(outer.declaration, declaration.node());
        assert_eq!(inner.declaration, declaration.node());
        assert_eq!(outer.callable, inner.callable);
        assert_eq!(
            javascript.arena.get(outer.callable.node).unwrap().kind,
            SyntaxKind::ArrowFunction,
        );
        assert_eq!(
            plan.expression_type(outer.node).unwrap().type_(),
            &JsDocType::Intrinsic(JsDocIntrinsicType::String),
        );
        let generic = plan.expression_type(inner.node).unwrap();
        assert_eq!(generic.type_(), &JsDocType::Named("T".to_owned()));
        assert_eq!(generic.resolved_alias_name(), None);
    }

    #[test]
    fn arrow_body_type_comments_resolve_unshadowed_local_typedefs() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @typedef {number} Value */\n",
            "const read = value => /** @type {Value} */ (value);",
        ));
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(105),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let [expression] = plan.expressions.as_slice() else {
            panic!("expected one source-owned arrow-body type comment")
        };
        assert_eq!(expression.type_.resolved_alias_name(), Some("Value"));
    }

    #[test]
    fn arrow_body_type_comments_expand_generic_typedefs_without_losing_template_ownership() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @template T @typedef {T[]} Box */\n",
            "/**\n",
            " * @template T\n",
            " * @param {T} value\n",
            " * @returns {T}\n",
            " */\n",
            "const read = value => /** @type {Box<T>} */ (value);",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics,
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(113),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [declaration] = plan.declarations() else {
            panic!("expected one source-owned generic arrow declaration")
        };
        let [expression] = plan.expressions.as_slice() else {
            panic!("expected one generic arrow-body type comment")
        };
        assert_eq!(expression.declaration, declaration.node());
        assert_eq!(expression.type_.resolved_alias_name(), Some("Box"));
        assert_eq!(
            expression.type_.resolution_type(),
            &JsDocType::Array(Box::new(JsDocType::Named("T".to_owned()))),
        );
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

    #[test]
    fn namespaced_callback_aliases_resolve_contextual_arrow_signatures() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @callback NS.MyCallback\n",
            " * @param {string} name\n",
            " * @returns {void}\n",
            " */\n",
            "/** @type {NS.MyCallback} */\n",
            "const f = (name) => {};",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(98),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [declaration] = plan.declarations() else {
            panic!("expected one callback-annotated arrow declaration")
        };
        assert!(declaration.parameters().is_empty());
        assert!(declaration.return_type().is_none());
        let [defined] = declaration.callbacks() else {
            panic!("expected one independently owned callback definition")
        };
        let annotation = declaration.type_().unwrap();
        assert_eq!(
            annotation.type_(),
            &JsDocType::Named("NS.MyCallback".to_owned())
        );
        assert_eq!(annotation.resolved_alias_name(), Some("NS.MyCallback"));
        let callback = annotation.resolved_callback().unwrap();
        assert_eq!(callback, defined);

        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
        );
        preflight_planned_jsdoc_type(context.store(), &globals, options, annotation).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
            ),
            before
        );

        let resolved = resolve_planned_jsdoc_callback_signature(
            context.store_mut_for_test(),
            &globals,
            options,
            callback,
            &[],
        )
        .unwrap();
        let [parameter] = resolved.parameters() else {
            panic!("expected the callback's single typed parameter")
        };
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(parameter.name(), "name");
        assert_eq!(parameter.type_(), Some(bootstrap.string_type));
        assert_eq!(resolved.return_type(), Some(bootstrap.void_type));
    }

    #[test]
    fn callback_aliases_keep_local_typedefs_but_reject_generic_and_imported_signatures() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @typedef {string} Input */\n",
            "/** @callback Handler\n",
            " * @param {Input} value\n",
            " * @returns {void}\n",
            " */\n",
            "/** @type {Handler} */\n",
            "const handler = (value) => {};",
        ));
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(99),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let [declaration] = plan.declarations() else {
            panic!("expected one callback and its local typedef")
        };
        let callback = declaration.type_().unwrap().resolved_callback().unwrap();
        assert_eq!(
            callback.parameters()[0]
                .type_()
                .unwrap()
                .resolved_alias_name(),
            Some("Input")
        );

        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        let signature = resolve_planned_jsdoc_callback_signature(
            context.store_mut_for_test(),
            &globals,
            options,
            callback,
            &[],
        )
        .unwrap();
        assert_eq!(
            signature.parameters()[0].type_(),
            Some(context.store().intrinsic_bootstrap().unwrap().string_type)
        );

        let generic = parse_javascript_source_file(concat!(
            "/** @template T\n",
            " * @callback Generic\n",
            " * @param {T} value\n",
            " * @returns {T}\n",
            " */\n",
            "/** @type {Generic} */\n",
            "const generic = (value) => {};",
        ));
        let root = NodeRef::new(generic.arena.id(), FileId::new(100), generic.source_file);
        let generic_plan = plan_javascript_source_jsdoc(&generic.arena, root).unwrap();
        let generic = generic_plan.declarations()[0].type_().unwrap();
        assert!(generic.resolved_callback().is_none());
        assert_eq!(
            preflight_planned_jsdoc_type(context.store(), &globals, options, generic),
            Err(JsDocTypeResolutionError::UnresolvedTypeReference {
                name: "Generic".to_owned(),
                range: generic.range(),
            })
        );

        let imported = parse_javascript_source_file(concat!(
            "/** @callback Imported\n",
            " * @param {import('./types').Value} value\n",
            " * @returns {void}\n",
            " */\n",
            "/** @type {Imported} */\n",
            "const imported = (value) => {};",
        ));
        let root = NodeRef::new(imported.arena.id(), FileId::new(101), imported.source_file);
        let imported_plan = plan_javascript_source_jsdoc(&imported.arena, root).unwrap();
        let imported = imported_plan.declarations()[0].type_().unwrap();
        let parameter = imported.resolved_callback().unwrap().parameters()[0]
            .type_()
            .unwrap();
        assert_eq!(
            preflight_planned_jsdoc_type(context.store(), &globals, options, imported),
            Err(JsDocTypeResolutionError::UnsupportedType {
                kind: SyntaxKind::ImportType,
                range: parameter.range(),
            })
        );
    }

    #[test]
    fn generic_callback_aliases_apply_constraints_defaults_and_preserve_source_ranges() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @typedef {boolean} T */\n",
            "/**\n",
            " * @template {string | number} T\n",
            " * @template [U=T]\n",
            " * @callback NS.Mapper\n",
            " * @param {T} value\n",
            " * @returns {U}\n",
            " */\n",
            "/** @type {NS.Mapper<string>} */\n",
            "const first = value => value;\n",
            "/** @type {NS.Mapper<number, string>} */\n",
            "const second = value => value;",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(106),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [first, second] = plan.declarations() else {
            panic!("expected both generic callback consumers")
        };
        let [definition] = first.callbacks() else {
            panic!("expected one source-owned generic callback")
        };
        assert_eq!(definition.template_parameters().len(), 2);
        assert!(
            definition.parameters()[0]
                .type_()
                .unwrap()
                .resolved_alias_name()
                .is_none()
        );

        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;

        for (declaration, expected_parameter, expected_return) in
            [(first, string, string), (second, number, string)]
        {
            let annotation = declaration.type_().unwrap();
            assert_eq!(annotation.resolved_alias_name(), Some("NS.Mapper"));
            let callback = annotation.resolved_callback().unwrap();
            assert_eq!(callback.name(), definition.name());
            assert_eq!(callback.range(), definition.range());
            assert!(callback.template_parameters().is_empty());
            assert_eq!(callback.parameters()[0].name(), "value");
            assert_eq!(
                callback.parameters()[0].range(),
                definition.parameters()[0].range(),
            );
            assert_eq!(
                callback.parameters()[0].type_().unwrap().range(),
                definition.parameters()[0].type_().unwrap().range(),
            );
            assert_eq!(
                callback.return_type().unwrap().range(),
                definition.return_type().unwrap().range(),
            );

            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
            );
            preflight_planned_jsdoc_type(context.store(), &globals, options, annotation).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                ),
                before,
            );

            let signature = resolve_planned_jsdoc_callback_signature(
                context.store_mut_for_test(),
                &globals,
                options,
                callback,
                &[],
            )
            .unwrap();
            assert_eq!(signature.parameters()[0].type_(), Some(expected_parameter));
            assert_eq!(signature.return_type(), Some(expected_return));
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                ),
                before,
            );
        }
    }

    #[test]
    fn generic_callback_arguments_expand_nested_generic_typedefs() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @template T @typedef {T[]} NS.List */\n",
            "/**\n",
            " * @template T\n",
            " * @callback NS.Mapper\n",
            " * @param {T} value\n",
            " * @returns {NS.List<T>}\n",
            " */\n",
            "/** @type {NS.Mapper<NS.List<string>>} */\n",
            "const mapper = value => [value];",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(107),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [declaration] = plan.declarations() else {
            panic!("expected one generic callback and typedef consumer")
        };
        let annotation = declaration.type_().unwrap();
        assert_eq!(annotation.resolved_alias_name(), Some("NS.Mapper"));
        let callback = annotation.resolved_callback().unwrap();

        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "const marker = 1;",
        ));
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        let before = context.store().type_len();
        preflight_planned_jsdoc_type(context.store(), &globals, options, annotation).unwrap();
        assert_eq!(context.store().type_len(), before);

        let signature = resolve_planned_jsdoc_callback_signature(
            context.store_mut_for_test(),
            &globals,
            options,
            callback,
            &[],
        )
        .unwrap();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let strings = context
            .store_mut_for_test()
            .create_canonical_array_type(&globals, string, false)
            .unwrap();
        let nested = context
            .store_mut_for_test()
            .create_canonical_array_type(&globals, strings, false)
            .unwrap();
        assert_eq!(signature.parameters()[0].type_(), Some(strings));
        assert_eq!(signature.return_type(), Some(nested));

        let warm = context.store().type_len();
        assert_eq!(
            resolve_planned_jsdoc_callback_signature(
                context.store_mut_for_test(),
                &globals,
                options,
                callback,
                &[],
            ),
            Ok(signature),
        );
        assert_eq!(context.store().type_len(), warm);
    }

    #[test]
    fn invalid_generic_callback_definitions_fail_before_checker_allocations() {
        for source in [
            concat!(
                "/** @template {string} T\n",
                " * @callback Mapper\n",
                " * @param {T} value\n",
                " * @returns {T}\n",
                " */\n",
                "/** @type {Mapper<number>} */ var value;",
            ),
            concat!(
                "/** @template T\n",
                " * @callback Mapper\n",
                " * @param {T} value\n",
                " * @returns {T}\n",
                " */\n",
                "/** @type {Mapper<string, number>} */ var value;",
            ),
            concat!(
                "/** @template T, U\n",
                " * @callback Mapper\n",
                " * @param {T} value\n",
                " * @returns {U}\n",
                " */\n",
                "/** @type {Mapper<string>} */ var value;",
            ),
            concat!(
                "/** @template T, T\n",
                " * @callback Mapper\n",
                " * @param {T} value\n",
                " * @returns {T}\n",
                " */\n",
                "/** @type {Mapper<string, string>} */ var value;",
            ),
            concat!(
                "/** @template T\n",
                " * @callback Mapper\n",
                " * @param {Mapper<T>} value\n",
                " * @returns {T}\n",
                " */\n",
                "/** @type {Mapper<string>} */ var value;",
            ),
            concat!(
                "/** @template T\n",
                " * @callback Mapper\n",
                " * @this {object}\n",
                " * @param {T} value\n",
                " * @returns {T}\n",
                " */\n",
                "/** @type {Mapper<string>} */ var value;",
            ),
            concat!(
                "/** @template T @typedef {T} Mapper */\n",
                "/** @template T\n",
                " * @callback Mapper\n",
                " * @param {T} value\n",
                " * @returns {T}\n",
                " */\n",
                "/** @type {Mapper<string>} */ var value;",
            ),
            concat!(
                "/** @template T\n",
                " * @callback Mapper\n",
                " * @param {T} value\n",
                " * @returns {T}\n",
                " */\n",
                "/** @template U\n",
                " * @callback Mapper\n",
                " * @param {U} value\n",
                " * @returns {U}\n",
                " */\n",
                "/** @type {Mapper<string>} */ var value;",
            ),
        ] {
            let javascript = parse_javascript_source_file(source);
            assert!(
                javascript.diagnostics.is_empty(),
                "{source}: {:?}",
                javascript.diagnostics,
            );
            let root = NodeRef::new(
                javascript.arena.id(),
                FileId::new(108),
                javascript.source_file,
            );
            let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
            let annotation = plan
                .declarations()
                .iter()
                .find_map(PlannedJavaScriptDeclaration::type_)
                .unwrap();
            assert!(annotation.resolved_callback().is_none(), "{source}");

            let parsed = parse_source_file("const marker = 1;");
            let options = CanonicalCheckerOptions::default();
            let mut context = context(&parsed, options);
            let globals = context.global_types().clone();
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
            );
            let expected = JsDocTypeResolutionError::UnsupportedType {
                kind: SyntaxKind::TypeReference,
                range: annotation.range(),
            };
            assert_eq!(
                preflight_planned_jsdoc_type(context.store(), &globals, options, annotation),
                Err(expected.clone()),
                "{source}",
            );
            assert_eq!(
                resolve_planned_jsdoc_type(
                    context.store_mut_for_test(),
                    &globals,
                    options,
                    annotation,
                ),
                Err(expected),
                "{source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                ),
                before,
                "{source}",
            );
        }
    }

    #[test]
    fn forged_generic_callback_signatures_stay_rejected_without_allocations() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @template T\n",
            " * @callback Mapper\n",
            " * @param {T} value\n",
            " * @returns {T}\n",
            " */\n",
            "/** @type {Mapper<string>} */ var value;",
        ));
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(109),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let [declaration] = plan.declarations() else {
            panic!("expected one generic callback consumer")
        };
        let annotation = declaration.type_().unwrap();
        let definition = &declaration.callbacks()[0];

        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        for corruption in 0..2 {
            let mut forged = annotation.clone();
            let Some(JsDocType::Callback(callback)) = forged.resolved_type.as_deref_mut() else {
                panic!("expected one instantiated callback signature")
            };
            match corruption {
                0 => callback.template_parameters = definition.template_parameters.clone(),
                1 => callback.this_type = callback.return_type.clone(),
                _ => unreachable!(),
            }
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
            );
            let expected = JsDocTypeResolutionError::UnsupportedType {
                kind: SyntaxKind::FunctionType,
                range: forged.range(),
            };
            assert_eq!(
                preflight_planned_jsdoc_type(context.store(), &globals, options, &forged),
                Err(expected.clone()),
            );
            assert_eq!(
                resolve_planned_jsdoc_type(
                    context.store_mut_for_test(),
                    &globals,
                    options,
                    &forged,
                ),
                Err(expected),
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                ),
                before,
            );
        }
    }

    #[test]
    fn template_tags_preserve_constraints_defaults_and_host_ownership() {
        let javascript = parse_javascript_source_file(concat!(
            "/**\n",
            " * @template {string | number} T, U\n",
            " * @template [V=boolean]\n",
            " * @param {T} value\n",
            " * @returns {U}\n",
            " */\n",
            "function read(value) {}",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(85),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [declaration] = plan.declarations() else {
            panic!("expected one generic JavaScript function")
        };
        let [first, second, third] = declaration.template_parameters() else {
            panic!("expected three ordered template parameters")
        };
        assert_eq!(first.name(), "T");
        assert_eq!(
            first.constraint().unwrap().type_(),
            &JsDocType::Union(vec![
                JsDocType::Intrinsic(JsDocIntrinsicType::String),
                JsDocType::Intrinsic(JsDocIntrinsicType::Number),
            ])
        );
        assert_eq!(second.name(), "U");
        assert!(second.constraint().is_none());
        assert_eq!(third.name(), "V");
        assert_eq!(
            third.default_type().unwrap().type_(),
            &JsDocType::Intrinsic(JsDocIntrinsicType::Boolean)
        );
        assert_eq!(
            declaration
                .parameter("value")
                .unwrap()
                .type_()
                .unwrap()
                .type_(),
            &JsDocType::Named("T".to_owned())
        );
    }

    #[test]
    fn typedef_properties_and_templates_stay_separate_from_the_host_function() {
        let javascript = parse_javascript_source_file(concat!(
            "/**\n",
            " * @template T\n",
            " * @typedef {Object} NS.Box\n",
            " * @property {T} value\n",
            " * @property {string | null} [label]\n",
            " */\n",
            "function host() {}",
        ));
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(86),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [host] = plan.declarations() else {
            panic!("expected one typedef host")
        };
        assert!(host.parameters().is_empty());
        assert!(host.template_parameters().is_empty());
        let [alias] = host.typedefs() else {
            panic!("expected one namespaced object typedef")
        };
        assert_eq!(alias.name(), "NS.Box");
        assert_eq!(alias.template_parameters()[0].name(), "T");
        let [value, label] = alias.properties() else {
            panic!("expected two ordered typedef properties")
        };
        assert_eq!(value.name(), "value");
        assert!(!value.is_optional());
        assert_eq!(
            value.type_().unwrap().type_(),
            &JsDocType::Named("T".to_owned())
        );
        assert_eq!(label.name(), "label");
        assert!(label.is_optional());
    }

    #[test]
    fn callback_templates_and_receiver_keep_their_own_signature() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @typedef {number | string} T */\n",
            "/**\n",
            " * @template T\n",
            " * @callback NS.Handler\n",
            " * @this {object}\n",
            " * @param {T} value\n",
            " * @returns {T}\n",
            " */\n",
            "function host() {}",
        ));
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(87),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [host] = plan.declarations() else {
            panic!("expected one callback host")
        };
        assert!(host.parameters().is_empty());
        assert!(host.template_parameters().is_empty());
        assert!(host.this_type().is_none());
        let [callback] = host.callbacks() else {
            panic!("expected one independently owned callback")
        };
        assert_eq!(callback.name(), "NS.Handler");
        assert_eq!(callback.template_parameters()[0].name(), "T");
        assert_eq!(
            callback.this_type().unwrap().type_(),
            &JsDocType::Intrinsic(JsDocIntrinsicType::Object)
        );
        assert_eq!(callback.parameters()[0].name(), "value");
        assert!(
            callback.parameters()[0]
                .type_()
                .unwrap()
                .resolved_alias_name()
                .is_none()
        );
        assert_eq!(
            callback.return_type().unwrap().type_(),
            &JsDocType::Named("T".to_owned())
        );
    }

    #[test]
    fn namespaced_typedef_aliases_resolve_inside_callback_signatures() {
        let javascript = parse_javascript_source_file(concat!(
            "/** @typedef {number} NS.Input */\n",
            "/** @typedef {string} NS.Output */\n",
            "/**\n",
            " * @callback NS.Mapper\n",
            " * @param {NS.Input} value\n",
            " * @returns {NS.Output}\n",
            " */\n",
            "function host() {}",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(92),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [host] = plan.declarations() else {
            panic!("expected one callback-hosting declaration")
        };
        let [callback] = host.callbacks() else {
            panic!("expected one namespaced callback")
        };
        assert_eq!(callback.name(), "NS.Mapper");
        assert_eq!(
            callback.parameters()[0]
                .type_()
                .unwrap()
                .resolved_alias_name(),
            Some("NS.Input")
        );
        assert_eq!(
            callback.return_type().unwrap().resolved_alias_name(),
            Some("NS.Output")
        );

        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        let signature = resolve_planned_jsdoc_callback_signature(
            context.store_mut_for_test(),
            &globals,
            options,
            callback,
            &[],
        )
        .unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            signature.parameters()[0].type_(),
            Some(bootstrap.number_type)
        );
        assert_eq!(signature.return_type(), Some(bootstrap.string_type));
    }

    #[test]
    fn misplaced_template_tags_report_the_pinned_ts8039_location() {
        let source = concat!(
            "/**\n",
            " * @typedef {number} Value\n",
            " * @template T\n",
            " */\n",
            "const marker = 1;",
        );
        let javascript = parse_javascript_source_file(source);
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(88),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let [diagnostic] = plan.diagnostics() else {
            panic!("expected one misplaced-template diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 8039);
        let range = diagnostic.range_override.unwrap().range();
        let start = source.find("@template").unwrap() + 1;
        assert_eq!(range.start.get() as usize, start);
        assert_eq!(range.end.get() as usize, start + "template".len());
    }

    #[test]
    fn structured_jsdoc_types_preserve_object_function_import_and_generic_shapes() {
        let object = type_tag("/** @type {{ readonly id: string; label?: number }} */");
        let JsDocType::ObjectLiteral(properties) = object
            .type_tag()
            .unwrap()
            .type_expression()
            .unwrap()
            .type_()
        else {
            panic!("expected a structured object annotation")
        };
        assert_eq!(properties.len(), 2);
        assert_eq!(properties[0].name(), "id");
        assert!(properties[0].is_readonly());
        assert_eq!(properties[1].name(), "label");
        assert!(properties[1].is_optional());

        let function = type_tag("/** @type {(value: string, ...rest: number[]) => boolean} */");
        let JsDocType::Function(signature) = function
            .type_tag()
            .unwrap()
            .type_expression()
            .unwrap()
            .type_()
        else {
            panic!("expected a structured function annotation")
        };
        assert_eq!(signature.parameters()[0].name(), "value");
        assert!(signature.parameters()[1].is_rest());
        assert_eq!(
            signature.return_type(),
            &JsDocType::Intrinsic(JsDocIntrinsicType::Boolean)
        );

        let import = type_tag("/** @type {typeof import('./models').NS.Box<string>} */");
        let JsDocType::Import(reference) = import
            .type_tag()
            .unwrap()
            .type_expression()
            .unwrap()
            .type_()
        else {
            panic!("expected a structured import annotation")
        };
        assert_eq!(reference.specifier(), "./models");
        assert_eq!(reference.qualifier(), Some("NS.Box"));
        assert!(reference.is_type_of());
        assert_eq!(
            reference.type_arguments(),
            [JsDocType::Intrinsic(JsDocIntrinsicType::String)]
        );

        let generic = type_tag("/** @type {Promise<number>} */");
        assert_eq!(
            generic
                .type_tag()
                .unwrap()
                .type_expression()
                .unwrap()
                .type_(),
            &JsDocType::GenericReference {
                name: "Promise".to_owned(),
                arguments: vec![JsDocType::Intrinsic(JsDocIntrinsicType::Number)],
            }
        );
    }

    #[test]
    fn empty_jsdoc_object_uses_the_canonical_empty_type_literal_identity() {
        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        let comment = type_tag("/** @type {{}} */");
        let annotation = comment.type_tag().unwrap().type_expression().unwrap();
        let expected = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .empty_type_literal_type;
        assert_eq!(
            resolve_jsdoc_type(context.store_mut_for_test(), &globals, options, annotation),
            Ok(expected)
        );
    }

    #[test]
    fn source_owned_template_bindings_resolve_generic_callable_signatures() {
        let parsed = parse_source_file("interface Box<T> { value: T; }");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let parameter = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeParameter).then_some(NodeRef::new(
                    parsed.arena.id(),
                    FileId::new(0),
                    node,
                ))
            })
            .unwrap();
        let symbol = context
            .file(FileId::new(0))
            .unwrap()
            .1
            .symbol(parameter)
            .unwrap();
        let type_parameter = context.get_declared_type_of_symbol(symbol).unwrap();

        let javascript = parse_javascript_source_file(concat!(
            "/** @typedef {number} T */\n",
            "/**\n",
            " * @template T\n",
            " * @this {object}\n",
            " * @param {T} value\n",
            " * @returns {T}\n",
            " */\n",
            "function read(value) {}",
        ));
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(89),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let [declaration] = plan.declarations() else {
            panic!("expected one generic JavaScript callable")
        };
        let globals = context.global_types().clone();
        let signature = resolve_planned_jsdoc_signature(
            context.store_mut_for_test(),
            &globals,
            options,
            declaration,
            &[JsDocTypeParameterBinding::new("T", type_parameter)],
        )
        .unwrap();
        assert_eq!(signature.parameters()[0].type_(), Some(type_parameter));
        assert_eq!(signature.return_type(), Some(type_parameter));
        assert_eq!(
            signature.this_type(),
            Some(
                context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .non_primitive_type
            )
        );
    }

    #[test]
    fn arrow_body_template_casts_bind_to_the_same_canonical_signature_type_parameter() {
        let parsed = parse_source_file("interface Box<T> { value: T; }");
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = context(&parsed, options);
        let parameter = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeParameter).then_some(NodeRef::new(
                    parsed.arena.id(),
                    FileId::new(0),
                    node,
                ))
            })
            .unwrap();
        let symbol = context
            .file(FileId::new(0))
            .unwrap()
            .1
            .symbol(parameter)
            .unwrap();
        let type_parameter = context.get_declared_type_of_symbol(symbol).unwrap();
        let javascript = parse_javascript_source_file(concat!(
            "/**\n",
            " * @template T\n",
            " * @param {T|undefined} value value or not\n",
            " * @returns {T} result value\n",
            " */\n",
            "const cloneObjectGood = value => /** @type {T} */({ ...value });",
        ));
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(107),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let [declaration] = plan.declarations() else {
            panic!("expected one generic arrow declaration")
        };
        let [expression] = plan.expressions.as_slice() else {
            panic!("expected one generic arrow-body type assertion")
        };
        let globals = context.global_types().clone();
        let bindings = [JsDocTypeParameterBinding::new("T", type_parameter)];
        let signature = resolve_planned_jsdoc_signature(
            context.store_mut_for_test(),
            &globals,
            options,
            declaration,
            &bindings,
        )
        .unwrap();
        let bound =
            bind_planned_jsdoc_type_parameters(context.store(), &expression.type_, &bindings)
                .unwrap();
        let cast =
            resolve_planned_jsdoc_type(context.store_mut_for_test(), &globals, options, &bound)
                .unwrap();

        assert_eq!(signature.return_type(), Some(type_parameter));
        assert_eq!(cast, type_parameter);
        assert_eq!(
            context
                .type_to_string(signature.parameters()[0].type_().unwrap())
                .unwrap(),
            "T | undefined",
        );
    }

    #[test]
    fn satisfies_tags_preserve_the_function_shape_and_exact_tag_name_range() {
        let source = concat!(
            "/**\n",
            " * @satisfies {(value: string, ...rest: number[]) => void}\n",
            " * @param {string} value\n",
            " * @param {string | number} next\n",
            " */\n",
            "const read = (value, next) => {};",
        );
        let javascript = parse_javascript_source_file(source);
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(90),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        let [declaration] = plan.declarations() else {
            panic!("expected one satisfies-annotated callable")
        };
        assert!(declaration.type_().is_none());
        let satisfies = declaration.satisfies().unwrap();
        let JsDocType::Function(function) = satisfies.type_().type_() else {
            panic!("expected a complete @satisfies function target")
        };
        let [value, rest] = function.parameters() else {
            panic!("expected the required parameter and number-array rest tail")
        };
        assert_eq!(value.name(), "value");
        assert_eq!(
            value.type_(),
            Some(&JsDocType::Intrinsic(JsDocIntrinsicType::String)),
        );
        assert_eq!(rest.name(), "rest");
        assert!(rest.is_rest());
        assert_eq!(
            rest.type_(),
            Some(&JsDocType::Array(Box::new(JsDocType::Intrinsic(
                JsDocIntrinsicType::Number,
            )))),
        );
        assert_eq!(declaration.parameters().len(), 2);
        assert_eq!(declaration.parameters()[1].name(), "next");
        let start = source.find("@satisfies").unwrap() + 1;
        assert_eq!(satisfies.range().start.get() as usize, start);
        assert_eq!(
            satisfies.range().end.get() as usize,
            start + "satisfies".len()
        );
    }

    #[test]
    fn satisfies_function_rest_parameters_resolve_to_their_canonical_element_type() {
        let parsed = parse_source_file("const marker = 1;");
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&parsed, options);
        let globals = context.global_types().clone();
        for (index, (tail, array_rest)) in [("number[]", true), ("never", false)]
            .into_iter()
            .enumerate()
        {
            let source = format!(
                "/**\n * @satisfies {{(value: string, ...rest: {tail}) => void}}\n \
                 * @param {{string}} value\n * @param {{number}} next\n */\n \
                 const read = (value, next) => {{}};",
            );
            let javascript = parse_javascript_source_file(&source);
            let root = NodeRef::new(
                javascript.arena.id(),
                FileId::new(106 + u32::try_from(index).unwrap()),
                javascript.source_file,
            );
            let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
            let satisfies = plan.declarations()[0].satisfies().unwrap();
            preflight_source_jsdoc_satisfies_type(
                context.store(),
                &globals,
                options,
                satisfies.type_(),
            )
            .unwrap();
            let resolved = resolve_source_jsdoc_satisfies_signature(
                context.store_mut_for_test(),
                &globals,
                options,
                satisfies.type_(),
            )
            .unwrap();
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let expected = if array_rest {
                bootstrap.number_type
            } else {
                bootstrap.never_type
            };
            assert_eq!(resolved.parameters[0].type_, bootstrap.string_type);
            assert_eq!(resolved.parameters[1].type_, expected);
            assert!(resolved.parameters[1].rest);
            assert_eq!(resolved.parameters[1].array_rest, array_rest);
            assert_eq!(resolved.return_type, bootstrap.void_type);
        }
    }

    #[test]
    fn generic_jsdoc_heritage_preserves_exact_ts8023_ranges_and_matching_bases() {
        let source = concat!(
            "/** @extends {React.Component<React.Component>} */\n",
            "class First extends React.PureComponent {}\n",
            "/** @augments {(React.Component<string>)} */\n",
            "class Second extends React.PureComponent {}\n",
            "/** @extends {React.Component<string>} */\n",
            "class Third extends React.Component {}\n",
            "/** @augments {(React.Component<number>)} */\n",
            "class Fourth extends React.Component {}",
        );
        let javascript = parse_javascript_source_file(source);
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(110),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert_eq!(plan.declarations().len(), 4);
        let [first, second] = plan.diagnostics() else {
            panic!("expected only two mismatched generic superclass diagnostics")
        };

        let first_start = source.find("React.Component<React.Component>").unwrap() + "React.".len();
        let second_start =
            source.find("(React.Component<string>)").unwrap() + "(".len() + "React.".len();
        for (diagnostic, tag, start) in [
            (first, "extends", first_start),
            (second, "augments", second_start),
        ] {
            assert_eq!(diagnostic.diagnostic.code(), 8023);
            assert_eq!(
                diagnostic.diagnostic.arguments,
                [tag, "Component", "PureComponent"],
            );
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!(
                    "JSDoc '@{tag} Component' does not match the 'extends PureComponent' clause."
                ),
            );
            let range = diagnostic.range_override.unwrap().range();
            assert_eq!(range.start.get() as usize, start);
            assert_eq!(range.end.get() as usize, start + "Component".len());
        }
    }

    #[test]
    fn implements_tags_stay_separate_from_generic_superclass_annotations() {
        let source = concat!(
            "/**\n",
            " * @implements {Contracts.Readable<string>}\n",
            " * @extends {React.Component<string>}\n",
            " * @implements Contracts.Writable\n",
            " */\n",
            "class Reader extends React.Component {}",
        );
        let javascript = parse_javascript_source_file(source);
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(111),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        let [declaration] = plan.declarations() else {
            panic!("expected one class with separate heritage annotations")
        };
        assert_eq!(
            declaration.augments_type().unwrap().type_(),
            &JsDocType::GenericReference {
                name: "React.Component".to_owned(),
                arguments: vec![JsDocType::Intrinsic(JsDocIntrinsicType::String)],
            },
        );
        let [readable, writable] = declaration.implements_types() else {
            panic!("expected both ordered interface annotations")
        };
        assert_eq!(
            readable.type_(),
            &JsDocType::GenericReference {
                name: "Contracts.Readable".to_owned(),
                arguments: vec![JsDocType::Intrinsic(JsDocIntrinsicType::String)],
            },
        );
        assert_eq!(
            writable.type_(),
            &JsDocType::Named("Contracts.Writable".to_owned()),
        );
    }

    #[test]
    fn empty_jsdoc_class_heritage_does_not_fabricate_superclass_mismatches() {
        let source = concat!(
            "/** @augments X */\nclass First extends {}\n",
            "/** @extends X */\nclass Second extends {}",
        );
        let javascript = parse_javascript_source_file(source);
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let root = NodeRef::new(
            javascript.arena.id(),
            FileId::new(112),
            javascript.source_file,
        );
        let plan = plan_javascript_source_jsdoc(&javascript.arena, root).unwrap();
        assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
        assert_eq!(plan.declarations().len(), 2);
        for declaration in plan.declarations() {
            assert_eq!(
                declaration.augments_type().unwrap().type_(),
                &JsDocType::Named("X".to_owned()),
            );
        }
    }
}
