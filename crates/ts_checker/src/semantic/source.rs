//! Atomic canonical checking for the first source-statement slice.
//!
//! This module deliberately supports only unmodified type aliases and simple
//! interfaces, top-level nongeneric classes with primitive annotated fields
//! and at most one exact direct preceding local nongeneric base,
//! exact zero-argument construction of one preceding admitted no-base local
//! class,
//! top-level literal enums, empty external-module markers, exact
//! named ESM reexports,
//! leading direct named ESM value imports, clause-level type-only named ESM
//! imports in exact direct or union/parenthesized/array top-level variable
//! annotations,
//! annotated top-level function declarations, exact direct non-exported
//! ambient function declarations (including the existing generic callable
//! closure), initialized identifier-named top-level variables (optionally
//! exported), annotated uninitialized non-exported mutable top-level variables,
//! ordinary direct identifier
//! calls (including strict top-level call expression statements), atomic
//! primitive/literal scalar binary operators, direct top-level conditional
//! initializers, required own-property reads (including exact
//! two-constituent declared unions), direct indexed reads over supported
//! objects, arrays, and strings, strict direct-identifier `typeof` flow checks,
//! and direct assignments back to supported mutable declarations.
//! The complete source tree and complete supported-statement plan are validated
//! before semantic execution begins. Execution may retain safe canonical memo
//! caches while discovering a type-dependent capability boundary.
//! Unsupported syntax is therefore
//! a typed boundary, never a request to fall back to the legacy checker or to
//! synthesize `any`. Canonical memo caches are not rolled back after a later
//! semantic failure; diagnostics coupled to those caches remain in private
//! source staging until a retry completes and publishes them atomically.

use std::collections::{HashMap, HashSet};

use ts_ast::{FileId, ModifierList, Node, NodeArena, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalNameResolver, CanonicalResolutionLocation, SemanticSymbolId, SymbolFlags,
};
use ts_core::TextRange;
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_jsnum::{Number, PseudoBigInt};

use super::{
    ArrayTypeError, AssertionLinks, AssignmentInvariant, AssignmentUnsupported,
    CanonicalCheckerDiagnostic, CanonicalCheckerDiagnosticRange, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeError,
    DeclaredTypeHost, DerivedTypeError, ProductionAliasTargetHost, RelationUnavailable,
    SignatureId, SourceFileLinks, SourceFileRef, SymbolNodeLinks, TypeDisplayUnavailable, TypeId,
    TypeNodeLinks, ValueSymbolLinks, VariableInvariant, VariableUnsupported,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, UnionReduction},
    callables::{
        StoredSingleCallableValidation, ValidatedSingleCallable, validate_stored_single_callable,
    },
    classes::{
        ClassMemberPlan, ClassMemberQueryPlan, execute_nongeneric_class_member_query,
        plan_nongeneric_class_member_query, preflight_nongeneric_class_member_query,
    },
    contextual::{
        LiteralTreatment, PreparedExpression, prepare_expression_context_with_global_types,
        prepare_expression_without_context_with_global_types,
    },
    formatter::{
        CanonicalTypeFormatFlags,
        get_type_names_for_assignability_error_with_host_global_types_and_flags,
    },
    instantiate::InstantiationSession,
    jsdoc::{
        PlannedJavaScriptJsDoc, PlannedJsDocType, append_javascript_jsdoc_diagnostics,
        plan_javascript_source_jsdoc, preflight_planned_jsdoc_type, resolve_planned_jsdoc_type,
    },
    logical_operators::{
        LogicalBinaryError, LogicalBinaryInvariant, LogicalBinaryRequest, LogicalBinaryUnsupported,
        check_logical_binary, narrow_logical_right_operand,
    },
    object_members::{
        DeclaredPropertyObjectValidation, validate_resolved_declared_property_object,
    },
    primitive_operators::{
        PrimitiveBigIntExponentiationTarget, PrimitiveBinaryError, PrimitiveBinaryRecovery,
        PrimitiveBinaryRequest, PrimitiveBinaryUnsupported, check_primitive_binary,
    },
    source_arrows::{
        ResolvedSourceContextualArrowPlan, SourceArrowBodyPlan, SourceArrowError, SourceArrowPlan,
        SourceContextualArrowError, SourceContextualArrowPlan, SourceContextualParameterOrigin,
        SourceContextualSignatureShape, plan_contextual_source_arrow, plan_source_arrow,
        resolve_contextual_arrow_parameter_origins,
    },
    source_callables::{
        ContextualSourceCallableParameter, PreparedContextualSourceCallable,
        SourceCallableBodyMode, SourceCallableError, SourceCallableFamily,
        SourceCallableParameterPlan, SourceCallablePlan, SourceCallableReturnPlan,
        StoredSourceCallableValidation, plan_source_callable, publish_contextual_source_callable,
        publish_inferred_source_callable_return, validate_stored_source_callable,
    },
    source_calls::{
        SourceCallCalleeForm, SourceCallPlan, check_direct_source_call,
        emit_call_type_argument_grammar_diagnostics, finish_direct_source_call_plan,
        plan_direct_source_call_syntax, source_call_argument_contextual_type,
    },
    source_elements::{
        SourceElementError, SourceElementPlan, SourceElementUnsupported,
        check_direct_source_element, finish_direct_source_element_plan,
        plan_direct_source_element_syntax,
    },
    source_enums::{SourceEnumError, SourceEnumPlan, execute_top_level_enum, plan_top_level_enum},
    source_flow::{
        SourceFlowAssignment, SourceFlowCondition, SourceFlowError, SourceFlowFrame,
        SourceFlowPlan, SourceTruthinessCondition, SourceTypeofComparison, SourceTypeofCondition,
        SourceTypeofTag, source_typeof_narrowing_type_is_supported,
    },
    source_functions::{
        PlannedFunctionRead, SourceFunctionInvariant, SourceFunctionPlanError,
        SourceFunctionUnsupported, plan_function_identifier_read, plan_top_level_function,
    },
    source_imports::{
        PlannedSourceImportRead, PreparedSourceImportPublication, PreparedSourceImportValue,
        ResolvedSourceImportBinding, ResolvedSourceTypeImportBinding, SourceImportBindingPlan,
        SourceImportError, SourceImportPlan, SourceImportUnsupported, SourceNamedReexportPlan,
        plan_source_import_identifier_read, plan_source_type_import_reference,
        plan_top_level_named_reexport, plan_top_level_named_type_import,
        plan_top_level_named_value_import, preflight_prepared_source_import_publications,
        prepare_source_import_value, reject_source_type_import_value_use,
        resolve_source_import_binding, resolve_source_named_reexport_binding,
        resolve_source_type_import_binding,
    },
    source_namespaces::{
        SourceNamespaceMemberPlan, SourceNamespacePlan, execute_source_namespace,
        plan_source_namespace,
    },
    source_new::{
        SourceDefaultNewPlan, SourceNewError, SourceNewInvariant, SourceNewUnsupported,
        check_direct_default_new, plan_direct_default_new, preflight_direct_default_new,
        prepare_direct_default_news,
    },
    source_overloads::{
        MaterializedSourceOverload, ResolvedSourceOverloadSignature, SourceOverloadError,
        SourceOverloadPlan, plan_source_ambient_overload_group,
        prepare_source_overload_publication, publish_source_overload_batch,
    },
    source_properties::{
        SourcePropertyDiagnostic, SourcePropertyError, SourcePropertyPlan,
        SourcePropertyUnsupported, check_direct_source_property,
        finish_direct_source_property_plan, plan_direct_source_property_call_syntax,
        plan_direct_source_property_syntax, prepare_source_property_diagnostic,
    },
    source_statements::{
        SourceFallthroughBranchSyntax, SourceFunctionStatementsError,
        SourceFunctionStatementsInvariant, SourceFunctionStatementsSyntax,
        SourceJoinedFunctionStatementsError, SourceJoinedFunctionStatementsInvariant,
        SourceJoinedFunctionStatementsSyntax, SourceLinearFunctionStatementsSyntax,
        SourceLocalDeclarationSyntax, SourceReturnBranchSyntax, SourceTypeofConditionSyntax,
        plan_source_function_statements_syntax, plan_source_joined_function_statements_syntax,
        plan_source_linear_function_statements_syntax,
    },
    type_nodes::{
        CanonicalTypeQuery, CanonicalTypeReferenceAliasTarget, normalize_bigint_literal,
        normalize_numeric_separators,
    },
    type_records::{TypeData, TypeRecord},
    types::TypeFlags,
    variables::{
        PlannedIdentifierRead as PlannedVariableRead, VariableBindingKind, VariablePlanError,
        plan_identifier_read, plan_top_level_variable,
    },
};

const NODE_FLAG_JSDOC: u32 = 1 << 22;
const NODE_FLAG_LET: u32 = 1 << 0;
const NODE_FLAG_CONST: u32 = 1 << 1;

/// The syntactic position whose dependency-closed source-check support ended.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceSyntaxRole {
    SourceFile,
    Statement,
    TypeAliasDeclaration,
    InterfaceDeclaration,
    FunctionDeclaration,
    FunctionModifier,
    FunctionName,
    FunctionBody,
    ReturnStatement,
    ExportDeclaration,
    ExportClause,
    VariableStatement,
    VariableModifier,
    VariableDeclarationList,
    VariableDeclaration,
    VariableName,
    VariableType,
    VariableInitializer,
    PrefixUnaryOperand,
    AssertionType,
    AssertionOperand,
    ArrayLiteral,
    ArrayElement,
    ObjectLiteral,
    ObjectProperty,
    BinaryExpression,
    BinaryOperator,
    BinaryOperand,
}

/// Syntax that cannot be checked exactly by the installed source slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnsupportedSourceSyntax {
    Syntax {
        node: NodeRef,
        kind: SyntaxKind,
        role: SourceSyntaxRole,
    },
    MissingExternalModuleFact {
        node: NodeRef,
        role: SourceSyntaxRole,
    },
    JsDoc(NodeRef),
    JavaScriptSource(SourceFileRef),
    MissingVariableType(NodeRef),
    MissingVariableInitializer(NodeRef),
    EmptyVariableDeclarationList(NodeRef),
    InvalidLiteralSpelling(NodeRef),
    InvalidLiteralFlags(NodeRef),
    InvalidPrefixUnaryOperator {
        node: NodeRef,
        operator: SyntaxKind,
    },
    BigIntExponentiationTarget(NodeRef),
    ConstAssertion(NodeRef),
    NestedAssertion(NodeRef),
    Assignment(AssignmentUnsupported),
    Arrow(NodeRef),
    Function(SourceFunctionUnsupported),
    Variable(VariableUnsupported),
    Call(NodeRef),
    Enum(NodeRef),
    Import(NodeRef),
    Class(NodeRef),
    Property(NodeRef),
    Element(NodeRef),
    New(NodeRef),
}

/// Source and AST identity rejected before semantic execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceCheckProvenanceError {
    MissingFile(FileId),
    StoreSourceMismatch(SourceFileRef),
    BoundSourceMismatch {
        expected: NodeRef,
        actual: SourceFileRef,
    },
    MissingSourceFacts(FileId),
    MissingNode(NodeRef),
    NodeNotBound(NodeRef),
    MismatchedNodeData {
        node: NodeRef,
        kind: SyntaxKind,
    },
    RepeatedNode(NodeRef),
    InvalidParent {
        node: NodeRef,
        expected: Option<NodeId>,
        actual: Option<NodeId>,
    },
    InvalidRange {
        node: NodeRef,
        range: TextRange,
        parent: Option<TextRange>,
    },
    MissingDeclarationSymbol(NodeRef),
    InvalidDiagnosticNode(NodeRef),
    InvalidDiagnosticRange {
        node: Option<NodeRef>,
        range_override: CanonicalCheckerDiagnosticRange,
    },
    SourceLinkPublication(SourceFileRef),
}

/// Public mirror of the store-private literal cache failure domain.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceLiteralCacheError {
    BootstrapUninitialized,
    InvalidValue,
    InvalidCachedLiteral(TypeId),
    InvalidCachedUnion(TypeId),
    UnsupportedUnionConstituent(TypeId),
    ArrayType(ArrayTypeError),
    InvalidUnionAlias(SemanticSymbolId),
    InvalidPreparedQuery,
    Capacity,
}

/// Source-level object-literal construction or cache validation failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceObjectLiteralError {
    InvalidCache {
        node: NodeRef,
        type_: Option<TypeId>,
    },
    Capacity(NodeRef),
}

/// Assertion-expression cache or deferred-queue state rejected atomically.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceAssertionError {
    InvalidOperandCache {
        node: NodeRef,
        cached: Option<TypeId>,
        expected: TypeId,
    },
    InvalidExpressionCache {
        node: NodeRef,
        cached: Option<TypeId>,
        expected: TypeId,
    },
    InvalidDeferredNodes(SourceFileRef),
}

impl From<LiteralTypeCacheError> for SourceLiteralCacheError {
    fn from(error: LiteralTypeCacheError) -> Self {
        match error {
            LiteralTypeCacheError::BootstrapUninitialized => Self::BootstrapUninitialized,
            LiteralTypeCacheError::InvalidValue => Self::InvalidValue,
            LiteralTypeCacheError::InvalidCachedLiteral(type_id) => {
                Self::InvalidCachedLiteral(type_id)
            }
            LiteralTypeCacheError::InvalidCachedUnion(type_id) => Self::InvalidCachedUnion(type_id),
            LiteralTypeCacheError::UnsupportedUnionConstituent(type_id) => {
                Self::UnsupportedUnionConstituent(type_id)
            }
            LiteralTypeCacheError::ArrayType { error, .. } => Self::ArrayType(error),
            LiteralTypeCacheError::InvalidUnionAlias(symbol) => Self::InvalidUnionAlias(symbol),
            LiteralTypeCacheError::InvalidPreparedQuery => Self::InvalidPreparedQuery,
            LiteralTypeCacheError::Capacity => Self::Capacity,
        }
    }
}

/// Exact failure domain for [`crate::semantic::CanonicalCheckerContext::check_source_file`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceCheckError {
    Provenance(SourceCheckProvenanceError),
    Unsupported(UnsupportedSourceSyntax),
    DeclaredType(DeclaredTypeError),
    RelationUnavailable(RelationUnavailable),
    TypeDisplayUnavailable(TypeDisplayUnavailable),
    LiteralCache(SourceLiteralCacheError),
    ObjectLiteral(SourceObjectLiteralError),
    ArrayType(ArrayTypeError),
    DerivedType(DerivedTypeError),
    Assertion(SourceAssertionError),
    Assignment(AssignmentInvariant),
    Arrow(NodeRef),
    Function(SourceFunctionInvariant),
    Variable(VariableInvariant),
    Call(NodeRef),
    Enum(NodeRef),
    Import(NodeRef),
    Class(NodeRef),
    Property(NodeRef),
    Element(NodeRef),
    PrimitiveOperator(NodeRef),
    LogicalOperator(NodeRef),
    Conditional(NodeRef),
    MissingDiagnostic(u32),
}

impl std::fmt::Display for SourceCheckError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Provenance(error) => write!(formatter, "source provenance failed: {error:?}"),
            Self::Unsupported(error) => {
                write!(formatter, "source syntax is unsupported: {error:?}")
            }
            Self::DeclaredType(error) => write!(formatter, "{error}"),
            Self::RelationUnavailable(error) => write!(formatter, "{error}"),
            Self::TypeDisplayUnavailable(error) => write!(formatter, "{error}"),
            Self::LiteralCache(error) => write!(formatter, "literal cache failed: {error:?}"),
            Self::ObjectLiteral(error) => write!(formatter, "object literal failed: {error:?}"),
            Self::ArrayType(error) => write!(formatter, "array type failed: {error}"),
            Self::DerivedType(error) => write!(formatter, "{error}"),
            Self::Assertion(error) => write!(formatter, "assertion checking failed: {error:?}"),
            Self::Assignment(error) => write!(formatter, "assignment planning failed: {error:?}"),
            Self::Arrow(node) => write!(formatter, "arrow checking failed at {node:?}"),
            Self::Function(error) => write!(formatter, "function checking failed: {error:?}"),
            Self::Variable(error) => write!(formatter, "variable checking failed: {error:?}"),
            Self::Call(node) => write!(formatter, "call checking failed at {node:?}"),
            Self::Enum(node) => write!(formatter, "enum checking failed at {node:?}"),
            Self::Import(node) => write!(formatter, "import checking failed at {node:?}"),
            Self::Class(node) => write!(formatter, "class checking failed at {node:?}"),
            Self::Property(node) => write!(formatter, "property checking failed at {node:?}"),
            Self::Element(node) => write!(formatter, "element checking failed at {node:?}"),
            Self::PrimitiveOperator(node) => {
                write!(formatter, "primitive operator checking failed at {node:?}")
            }
            Self::LogicalOperator(node) => {
                write!(formatter, "logical operator checking failed at {node:?}")
            }
            Self::Conditional(node) => {
                write!(
                    formatter,
                    "conditional expression checking failed at {node:?}"
                )
            }
            Self::MissingDiagnostic(code) => {
                write!(formatter, "diagnostic TS{code} is absent from the catalog")
            }
        }
    }
}

impl std::error::Error for SourceCheckError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::DeclaredType(error) => Some(error),
            Self::RelationUnavailable(error) => Some(error),
            Self::TypeDisplayUnavailable(error) => Some(error),
            Self::LiteralCache(SourceLiteralCacheError::ArrayType(error))
            | Self::ArrayType(error) => Some(error),
            Self::DerivedType(error) => Some(error),
            Self::Provenance(_)
            | Self::Unsupported(_)
            | Self::LiteralCache(_)
            | Self::ObjectLiteral(_)
            | Self::Assertion(_)
            | Self::Assignment(_)
            | Self::Arrow(_)
            | Self::Function(_)
            | Self::Variable(_)
            | Self::Call(_)
            | Self::Enum(_)
            | Self::Import(_)
            | Self::Class(_)
            | Self::Property(_)
            | Self::Element(_)
            | Self::PrimitiveOperator(_)
            | Self::LogicalOperator(_)
            | Self::Conditional(_)
            | Self::MissingDiagnostic(_) => None,
        }
    }
}

impl From<DeclaredTypeError> for SourceCheckError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<RelationUnavailable> for SourceCheckError {
    fn from(error: RelationUnavailable) -> Self {
        Self::RelationUnavailable(error)
    }
}

impl From<TypeDisplayUnavailable> for SourceCheckError {
    fn from(error: TypeDisplayUnavailable) -> Self {
        Self::TypeDisplayUnavailable(error)
    }
}

impl From<LiteralTypeCacheError> for SourceCheckError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::LiteralCache(error.into())
    }
}

impl From<DerivedTypeError> for SourceCheckError {
    fn from(error: DerivedTypeError) -> Self {
        Self::DerivedType(error)
    }
}

impl From<ArrayTypeError> for SourceCheckError {
    fn from(error: ArrayTypeError) -> Self {
        Self::ArrayType(error)
    }
}

#[derive(Clone, Debug)]
pub(super) struct PlannedExpression {
    pub(super) node: NodeRef,
    pub(super) kind: PlannedExpressionKind,
    used_before_assignment: bool,
}

impl PlannedExpression {
    pub(super) fn new(node: NodeRef, kind: PlannedExpressionKind) -> Self {
        Self {
            node,
            kind,
            used_before_assignment: false,
        }
    }

    fn with_used_before_assignment(mut self, used_before_assignment: bool) -> Self {
        self.used_before_assignment = used_before_assignment;
        self
    }

    pub(super) fn unparenthesized(&self) -> &Self {
        let mut expression = self;
        while let PlannedExpressionKind::Parenthesized(inner) = &expression.kind {
            expression = inner;
        }
        expression
    }
}

/// Fully preflighted scalar-binary source shape with recursive operands.
#[derive(Clone, Debug)]
pub(super) struct PrimitiveBinaryPlan {
    node: NodeRef,
    left: PlannedExpression,
    operator: SyntaxKind,
    right: PlannedExpression,
}

/// Fully preflighted logical/coalescing source shape with recursive operands.
#[derive(Clone, Debug)]
pub(super) struct LogicalBinaryPlan {
    node: NodeRef,
    left: PlannedExpression,
    operator: SyntaxKind,
    right: PlannedExpression,
    parent: Option<DirectBinaryParent>,
}

/// Fully preflighted direct top-level conditional initializer.
#[derive(Clone, Debug)]
pub(super) struct ConditionalExpressionPlan {
    node: NodeRef,
    condition: PlannedExpression,
    condition_expectation: ConditionalScalarExpectation,
    when_true: PlannedExpression,
    when_true_expectation: ConditionalScalarExpectation,
    when_false: PlannedExpression,
    when_false_expectation: ConditionalScalarExpectation,
    expected_result: TypeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConditionalScalarFamily {
    String,
    Number,
    BigInt,
    Boolean,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConditionalScalarExpectation {
    Exact {
        family: ConditionalScalarFamily,
        type_: TypeId,
    },
    Literal(ConditionalScalarFamily),
    Error,
}

#[derive(Clone, Copy, Debug)]
struct LogicalGrammarDiagnostic {
    node: NodeRef,
    first: SyntaxKind,
    second: SyntaxKind,
}

/// The direct, unparenthesized binary parent of one planned logical
/// expression. TypeScript owns TS5076 on the `??` node, but selecting its
/// diagnostic requires the surrounding binary operator and left operand.
#[derive(Clone, Copy, Debug)]
struct DirectBinaryParent {
    left: NodeRef,
    left_is_binary: bool,
    operator: SyntaxKind,
}

impl PrimitiveBinaryPlan {
    pub(super) const fn node(&self) -> NodeRef {
        self.node
    }

    pub(super) const fn operator(&self) -> SyntaxKind {
        self.operator
    }

    pub(super) const fn operands(&self) -> (&PlannedExpression, &PlannedExpression) {
        (&self.left, &self.right)
    }
}

impl LogicalBinaryPlan {
    pub(super) const fn node(&self) -> NodeRef {
        self.node
    }

    pub(super) const fn operator(&self) -> SyntaxKind {
        self.operator
    }

    pub(super) const fn operands(&self) -> (&PlannedExpression, &PlannedExpression) {
        (&self.left, &self.right)
    }
}

#[derive(Clone, Debug)]
pub(super) enum PlannedExpressionKind {
    Null,
    String(String),
    Number {
        value: Number,
        unary_operand: Option<Number>,
    },
    BigInt {
        value: PseudoBigInt,
        unary_operand: Option<PseudoBigInt>,
    },
    Boolean(bool),
    GlobalUndefined,
    Identifier(PlannedIdentifierRead),
    TypeImportValueUse(PlannedSourceTypeImportValueUse),
    Parenthesized(Box<PlannedExpression>),
    Assertion {
        type_node: NodeRef,
        operand: Box<PlannedExpression>,
    },
    Array(Vec<PlannedExpression>),
    Object {
        plan: super::object_members::PropertyObjectPlan,
        properties: Vec<PlannedExpression>,
    },
    Property(Box<SourcePropertyPlan>),
    Element(Box<SourceElementPlan>),
    Call(Box<SourceCallPlan>),
    New(Box<SourceDefaultNewPlan>),
    Binary(Box<PrimitiveBinaryPlan>),
    Logical(Box<LogicalBinaryPlan>),
    Conditional(Box<ConditionalExpressionPlan>),
}

/// A direct expression read of one clause-level type-only import. It remains
/// separate from value-family identifier reads so execution cannot consult or
/// populate the alias's current-flow or value-symbol state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PlannedSourceTypeImportValueUse {
    node: NodeRef,
    alias_symbol: SemanticSymbolId,
    name: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PreparedSourceTypeImportValueUse {
    diagnostic: CanonicalCheckerDiagnostic,
    error_type: TypeId,
    prior_links: Option<TypeNodeLinks>,
    publication: TypeNodeLinks,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PlannedSourceTypeImportReference {
    root: NodeRef,
    node: NodeRef,
    alias_symbol: SemanticSymbolId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PlannedIdentifierReadKind {
    Variable,
    Function,
    Import,
    Unresolved,
}

/// A source expression read with an explicit value-family route.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedIdentifierRead {
    pub(super) resolved_symbol: SemanticSymbolId,
    pub(super) value_symbol: SemanticSymbolId,
    pub(super) kind: PlannedIdentifierReadKind,
}

impl PlannedIdentifierRead {
    const fn variable(read: PlannedVariableRead) -> Self {
        Self {
            resolved_symbol: read.resolved_symbol,
            value_symbol: read.value_symbol,
            kind: PlannedIdentifierReadKind::Variable,
        }
    }

    const fn function(read: PlannedFunctionRead) -> Self {
        Self {
            resolved_symbol: read.resolved_symbol,
            value_symbol: read.value_symbol,
            kind: PlannedIdentifierReadKind::Function,
        }
    }

    const fn import(read: PlannedSourceImportRead) -> Self {
        Self {
            resolved_symbol: read.resolved_symbol,
            value_symbol: read.value_symbol,
            kind: PlannedIdentifierReadKind::Import,
        }
    }

    const fn unresolved(unknown_symbol: SemanticSymbolId) -> Self {
        Self {
            resolved_symbol: unknown_symbol,
            value_symbol: unknown_symbol,
            kind: PlannedIdentifierReadKind::Unresolved,
        }
    }
}

#[derive(Clone, Debug)]
struct PlannedVariable {
    declaration: NodeRef,
    name: NodeRef,
    symbol: SemanticSymbolId,
    binding: VariableBindingKind,
    type_node: Option<NodeRef>,
    jsdoc_type: Option<PlannedJsDocType>,
    initializer: PlannedVariableInitializer,
}

#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)] // Keeps ordinary variable expressions inline.
enum PlannedVariableInitializer {
    Expression(PlannedExpression),
    Jsx(NodeRef),
    AbsentAnnotated,
    AbsentJavaScript,
}

#[derive(Clone, Copy, Debug)]
struct PlannedAmbientVariable {
    symbol: SemanticSymbolId,
    binding: VariableBindingKind,
    type_node: NodeRef,
}

#[derive(Clone, Debug)]
struct PlannedFunction {
    callable: SourceCallablePlan,
    parameter_initializers: Vec<PlannedParameterInitializer>,
    body: PlannedFunctionBody,
}

#[derive(Clone, Debug)]
struct PlannedFunctionHeader {
    name: NodeRef,
    name_text: String,
    modifier_mode: PlannedFunctionModifierMode,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PlannedFunctionModifierMode {
    None,
    Export(NodeRef),
    Declare,
    ExportDeclare(NodeRef),
}

#[derive(Clone, Debug)]
struct PlannedArrow {
    source: SourceArrowPlan,
    parameter_initializers: Vec<PlannedParameterInitializer>,
    body: PlannedArrowBody,
}

#[derive(Clone, Debug)]
struct PlannedParameterInitializer {
    parameter: SourceCallableParameterPlan,
    expression: PlannedExpression,
}

#[derive(Clone, Debug)]
struct PlannedContextualArrow {
    source: SourceContextualArrowPlan,
}

#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)] // Keeps ordinary arrow return expressions inline.
enum PlannedArrowBody {
    Empty,
    Return {
        diagnostic_node: NodeRef,
        expression: PlannedExpression,
    },
}

#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)] // Keeps ordinary function return expressions inline.
enum PlannedFunctionBody {
    Ambient,
    Empty,
    Return {
        statement: NodeRef,
        expression: PlannedExpression,
    },
    Linear(Box<PlannedLinearFunctionStatements>),
    Statements(Box<PlannedFunctionStatements>),
    JoinedStatements(Box<PlannedJoinedFunctionStatements>),
}

#[derive(Clone, Debug)]
struct PlannedLinearFunctionStatements {
    locals: Vec<PlannedVariable>,
    return_statement: Option<NodeRef>,
    return_expression: Option<PlannedExpression>,
    flow: SourceFlowPlan,
}

#[derive(Clone, Debug)]
struct PlannedFunctionStatements {
    leading: Vec<PlannedVariable>,
    condition: PlannedSourceCondition,
    then_branch: PlannedReturnBranch,
    else_branch: PlannedReturnBranch,
    flow: SourceFlowPlan,
}

#[derive(Clone, Debug)]
struct PlannedReturnBranch {
    locals: Vec<PlannedVariable>,
    return_statement: NodeRef,
    return_expression: PlannedExpression,
}

#[derive(Clone, Debug)]
struct PlannedJoinedFunctionStatements {
    leading: Vec<PlannedVariable>,
    condition: PlannedSourceCondition,
    then_branch: PlannedFallthroughBranch,
    else_branch: PlannedFallthroughBranch,
    trailing: Vec<PlannedVariable>,
    return_statement: NodeRef,
    return_expression: PlannedExpression,
    flow: SourceFlowPlan,
}

#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)] // Keeps ordinary truthiness expressions inline.
enum PlannedSourceCondition {
    Truthiness {
        expression: PlannedExpression,
        symbol: SemanticSymbolId,
    },
    Typeof(Box<PlannedTypeofCondition>),
}

#[derive(Clone, Debug)]
struct PlannedTypeofCondition {
    expression: NodeRef,
    type_of_expression: NodeRef,
    identifier: PlannedExpression,
    literal: PlannedExpression,
    tag: SourceTypeofTag,
    comparison: SourceTypeofComparison,
    type_of_on_left: bool,
    symbol: SemanticSymbolId,
}

impl PlannedSourceCondition {
    fn flow_point(&self) -> NodeRef {
        match self {
            Self::Truthiness { expression, .. } => expression.unparenthesized().node,
            Self::Typeof(condition) => condition.identifier.node,
        }
    }

    fn flow_condition(&self) -> SourceFlowCondition {
        match self {
            Self::Truthiness { expression, symbol } => {
                SourceFlowCondition::Truthiness(SourceTruthinessCondition {
                    expression: expression.node,
                    symbol: *symbol,
                })
            }
            Self::Typeof(condition) => SourceFlowCondition::Typeof(SourceTypeofCondition {
                expression: condition.expression,
                symbol: condition.symbol,
                tag: condition.tag,
                comparison: condition.comparison,
            }),
        }
    }
}

#[derive(Clone, Debug)]
struct PlannedFallthroughBranch {
    locals: Vec<PlannedVariable>,
}

#[derive(Clone, Debug)]
struct PlannedAssignment {
    expression: NodeRef,
    left: NodeRef,
    target_symbol: SemanticSymbolId,
    target_type_node: Option<NodeRef>,
    right: PlannedExpression,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DeferredAssertion {
    node: NodeRef,
    operand_type: TypeId,
    target_type: TypeId,
}

#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)] // Keeps source class and expression plans inline.
enum PlannedStatement {
    TypeAlias(SemanticSymbolId),
    Interface(SemanticSymbolId),
    GenericInterface(super::object_members::PropertyObjectPlan),
    Namespace(Box<SourceNamespacePlan>),
    Class(ClassMemberQueryPlan),
    Enum(SourceEnumPlan),
    ExternalModuleMarker,
    NamedReexport,
    AmbientVariables,
    AmbientOverload,
    Function(usize),
    Arrow(usize),
    ContextualArrow(usize),
    Variables(Vec<PlannedVariable>),
    Assignment(PlannedAssignment),
    ExpressionCall(PlannedExpression),
}

#[derive(Debug)]
struct SourceCheckPlan {
    statements: Vec<PlannedStatement>,
    value_imports: Vec<SourceImportPlan>,
    type_imports: Vec<SourceImportPlan>,
    named_reexports: Vec<SourceNamedReexportPlan>,
    import_reads: Vec<PlannedSourceImportRead>,
    type_import_references: Vec<PlannedSourceTypeImportReference>,
    type_import_value_uses: Vec<PlannedSourceTypeImportValueUse>,
    ambient_variables: Vec<PlannedAmbientVariable>,
    overloads: Vec<SourceOverloadPlan>,
    functions: Vec<PlannedFunction>,
    arrows: Vec<PlannedArrow>,
    contextual_arrows: Vec<PlannedContextualArrow>,
    identifier_reads: Vec<(NodeRef, SemanticSymbolId)>,
    default_news: Vec<SourceDefaultNewPlan>,
    javascript_jsdoc: Option<PlannedJavaScriptJsDoc>,
    strings: Vec<String>,
    numbers: Vec<Number>,
    bigints: Vec<PseudoBigInt>,
}

enum PlannedVariableStatement {
    Arrow(Box<SourceArrowPlan>),
    ContextualArrow(Box<SourceContextualArrowPlan>),
    Variables(Vec<PlannedVariable>),
}

struct SourcePlanner<'arena, 'semantic, 'sources> {
    arena: &'arena NodeArena,
    bound: &'arena BoundFile,
    source: SourceFileRef,
    strings: Vec<String>,
    numbers: Vec<Number>,
    bigints: Vec<PseudoBigInt>,
    identifier_reads: Vec<(NodeRef, SemanticSymbolId)>,
    default_news: Vec<SourceDefaultNewPlan>,
    javascript_jsdoc: Option<PlannedJavaScriptJsDoc>,
    value_import_bindings: HashMap<SemanticSymbolId, SourceImportBindingPlan>,
    type_import_bindings: HashMap<SemanticSymbolId, SourceImportBindingPlan>,
    import_reads: Vec<PlannedSourceImportRead>,
    type_import_references: Vec<PlannedSourceTypeImportReference>,
    type_import_value_uses: Vec<PlannedSourceTypeImportValueUse>,
    semantic: Option<(
        &'semantic CanonicalTypeMapperStore,
        &'semantic DeclaredTypeHost<'sources>,
    )>,
    array_targets: Option<CanonicalArrayTargets>,
    hoisted_functions: HashSet<SemanticSymbolId>,
    prior_variables: HashSet<SemanticSymbolId>,
    readable_variables: HashSet<SemanticSymbolId>,
    assignable_ambient_variables: HashSet<SemanticSymbolId>,
    assignable_uninitialized_variables: HashSet<SemanticSymbolId>,
    assignable_mutable_variables: HashSet<SemanticSymbolId>,
    planned_classes: HashSet<SemanticSymbolId>,
    prior_classes: HashMap<SemanticSymbolId, ClassMemberPlan>,
    assigned_variables: HashSet<SemanticSymbolId>,
    /// Exact roots minted only by assignment and direct-call syntax owners.
    primitive_binary_position_roots: HashSet<NodeRef>,
}

impl<'arena, 'semantic, 'sources> SourcePlanner<'arena, 'semantic, 'sources> {
    #[cfg(test)]
    fn new(arena: &'arena NodeArena, bound: &'arena BoundFile, source: SourceFileRef) -> Self {
        Self {
            arena,
            bound,
            source,
            strings: Vec::new(),
            numbers: Vec::new(),
            bigints: Vec::new(),
            identifier_reads: Vec::new(),
            default_news: Vec::new(),
            javascript_jsdoc: None,
            value_import_bindings: HashMap::new(),
            type_import_bindings: HashMap::new(),
            import_reads: Vec::new(),
            type_import_references: Vec::new(),
            type_import_value_uses: Vec::new(),
            semantic: None,
            array_targets: None,
            hoisted_functions: HashSet::new(),
            prior_variables: HashSet::new(),
            readable_variables: HashSet::new(),
            assignable_ambient_variables: HashSet::new(),
            assignable_uninitialized_variables: HashSet::new(),
            assignable_mutable_variables: HashSet::new(),
            planned_classes: HashSet::new(),
            prior_classes: HashMap::new(),
            assigned_variables: HashSet::new(),
            primitive_binary_position_roots: HashSet::new(),
        }
    }

    fn new_semantic(
        arena: &'arena NodeArena,
        bound: &'arena BoundFile,
        source: SourceFileRef,
        store: &'semantic CanonicalTypeMapperStore,
        host: &'semantic DeclaredTypeHost<'sources>,
    ) -> Self {
        Self {
            arena,
            bound,
            source,
            strings: Vec::new(),
            numbers: Vec::new(),
            bigints: Vec::new(),
            identifier_reads: Vec::new(),
            default_news: Vec::new(),
            javascript_jsdoc: None,
            value_import_bindings: HashMap::new(),
            type_import_bindings: HashMap::new(),
            import_reads: Vec::new(),
            type_import_references: Vec::new(),
            type_import_value_uses: Vec::new(),
            semantic: Some((store, host)),
            array_targets: None,
            hoisted_functions: HashSet::new(),
            prior_variables: HashSet::new(),
            readable_variables: HashSet::new(),
            assignable_ambient_variables: HashSet::new(),
            assignable_uninitialized_variables: HashSet::new(),
            assignable_mutable_variables: HashSet::new(),
            planned_classes: HashSet::new(),
            prior_classes: HashMap::new(),
            assigned_variables: HashSet::new(),
            primitive_binary_position_roots: HashSet::new(),
        }
    }

    fn new_semantic_with_global_types(
        arena: &'arena NodeArena,
        bound: &'arena BoundFile,
        source: SourceFileRef,
        store: &'semantic CanonicalTypeMapperStore,
        host: &'semantic DeclaredTypeHost<'sources>,
        global_types: &CanonicalGlobalTypes,
    ) -> Self {
        let mut planner = Self::new_semantic(arena, bound, source, store, host);
        planner.array_targets = Some(CanonicalArrayTargets::from_global_types(global_types));
        planner
    }

    fn finish(mut self) -> Result<SourceCheckPlan, SourceCheckError> {
        self.validate_complete_tree()?;
        let source_node = self.node(self.source.node_ref())?;
        let NodeData::SourceFile(source_data) = &source_node.data else {
            return Err(self.unsupported(
                self.source.node_ref(),
                source_node.kind,
                SourceSyntaxRole::SourceFile,
            ));
        };
        let source_statements = source_data.statements.nodes.clone();
        let facts = self
            .bound
            .source_facts()
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingSourceFacts(self.source.file()),
            ))?;
        let is_javascript_file = facts.is_javascript_file();
        let is_external_module = facts.is_external_module();
        if is_javascript_file {
            self.javascript_jsdoc = Some(
                plan_javascript_source_jsdoc(self.arena, self.source.node_ref()).map_err(|_| {
                    SourceCheckError::Unsupported(UnsupportedSourceSyntax::JsDoc(
                        self.source.node_ref(),
                    ))
                })?,
            );
        }

        let mut value_imports = Vec::new();
        let mut type_imports = Vec::new();
        let mut leading_import_prefix = true;
        for statement in &source_statements {
            let statement = self.reference(*statement);
            match self.node(statement)?.kind {
                SyntaxKind::ImportDeclaration if leading_import_prefix => {
                    let Some((store, _)) = self.semantic else {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Import(statement),
                        ));
                    };
                    let type_only = self.import_is_type_only(statement)?;
                    let import = if type_only {
                        plan_top_level_named_type_import(self.arena, self.bound, store, statement)
                    } else {
                        plan_top_level_named_value_import(self.arena, self.bound, store, statement)
                    }
                    .map_err(|error| Self::import_plan_error(statement, &error))?;
                    for binding in &import.bindings {
                        let duplicate = if type_only {
                            self.value_import_bindings
                                .contains_key(&binding.alias_symbol)
                                || self
                                    .type_import_bindings
                                    .insert(binding.alias_symbol, binding.clone())
                                    .is_some()
                        } else {
                            self.type_import_bindings
                                .contains_key(&binding.alias_symbol)
                                || self
                                    .value_import_bindings
                                    .insert(binding.alias_symbol, binding.clone())
                                    .is_some()
                        };
                        if duplicate {
                            return Err(SourceCheckError::Import(binding.declaration));
                        }
                    }
                    if type_only {
                        type_imports.push(import);
                    } else {
                        value_imports.push(import);
                    }
                }
                SyntaxKind::ImportDeclaration => {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Import(statement),
                    ));
                }
                SyntaxKind::EmptyStatement => {}
                _ => leading_import_prefix = false,
            }
        }
        let mut function_declarations_by_owner = HashMap::<SemanticSymbolId, Vec<NodeRef>>::new();
        for statement in &source_statements {
            let statement = self.reference(*statement);
            if self.node(statement)?.kind != SyntaxKind::FunctionDeclaration {
                continue;
            }
            let owner = self
                .bound
                .symbol(statement)
                .ok_or(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MissingDeclarationSymbol(statement),
                ))?;
            function_declarations_by_owner
                .entry(owner)
                .or_default()
                .push(statement);
        }
        let mut preplanned_functions = HashMap::new();
        let mut preplanned_overload_declarations = HashSet::new();
        let mut preplanned_overload_owners = HashSet::new();
        let mut overloads = Vec::new();
        for statement in &source_statements {
            let statement = self.reference(*statement);
            if self.node(statement)?.kind != SyntaxKind::FunctionDeclaration {
                continue;
            }
            let owner = self
                .bound
                .symbol(statement)
                .ok_or(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MissingDeclarationSymbol(statement),
                ))?;
            if !preplanned_overload_owners.insert(owner) {
                continue;
            }
            let declarations =
                function_declarations_by_owner
                    .get(&owner)
                    .ok_or(SourceCheckError::Function(
                        SourceFunctionInvariant::MissingDeclaration(statement),
                    ))?;
            if declarations.len() == 1 {
                let callable = self.preplan_function_declaration(
                    statement,
                    is_external_module,
                    facts.is_declaration_file(),
                )?;
                if preplanned_functions.insert(statement, callable).is_some() {
                    return Err(SourceCheckError::Function(
                        SourceFunctionInvariant::DuplicateDeclaration(statement),
                    ));
                }
                continue;
            }
            let overload = self.preplan_function_overload_group(
                declarations,
                is_external_module,
                facts.is_declaration_file(),
            )?;
            if declarations
                .iter()
                .any(|declaration| !preplanned_overload_declarations.insert(*declaration))
            {
                return Err(SourceCheckError::Function(
                    SourceFunctionInvariant::DuplicateDeclaration(statement),
                ));
            }
            overloads.push(overload);
        }
        let mut preplanned_ambient_variables = HashMap::new();
        for statement in &source_statements {
            let statement = self.reference(*statement);
            if self.node(statement)?.kind != SyntaxKind::VariableStatement {
                continue;
            }
            let Some(variables) = self.preplan_ambient_variable_statement(
                statement,
                is_external_module,
                facts.is_declaration_file(),
            )?
            else {
                continue;
            };
            if preplanned_ambient_variables
                .insert(statement, variables)
                .is_some()
            {
                return Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::RepeatedNode(statement),
                ));
            }
        }

        let mut statements = Vec::with_capacity(source_statements.len());
        let mut named_reexports = Vec::new();
        let mut ambient_variables = Vec::new();
        let mut functions = Vec::with_capacity(preplanned_functions.len());
        let mut arrows = Vec::new();
        let mut contextual_arrows = Vec::new();
        for statement in source_statements {
            let statement = self.reference(statement);
            match self.node(statement)?.kind {
                SyntaxKind::ImportDeclaration => {}
                SyntaxKind::EmptyStatement => {
                    let node = self.node(statement)?;
                    let NodeData::EmptyStatement(empty) = &node.data else {
                        return Err(SourceCheckError::Provenance(
                            SourceCheckProvenanceError::MismatchedNodeData {
                                node: statement,
                                kind: node.kind,
                            },
                        ));
                    };
                    if node.flags.0 != 0
                        || empty.flow_node.is_some()
                        || !self.source_spelling_matches(statement, ";")
                    {
                        return Err(self.unsupported(
                            statement,
                            node.kind,
                            SourceSyntaxRole::Statement,
                        ));
                    }
                }
                SyntaxKind::ModuleDeclaration => {
                    let Some((store, _)) = self.semantic else {
                        return Err(self.unsupported(
                            statement,
                            SyntaxKind::ModuleDeclaration,
                            SourceSyntaxRole::Statement,
                        ));
                    };
                    let namespace =
                        plan_source_namespace(self.arena, self.bound, store, statement)?;
                    statements.push(PlannedStatement::Namespace(Box::new(namespace)));
                }
                SyntaxKind::TypeAliasDeclaration => {
                    let node = self.node(statement)?;
                    let NodeData::TypeAliasDeclaration(alias) = &node.data else {
                        return Err(SourceCheckError::Provenance(
                            SourceCheckProvenanceError::MismatchedNodeData {
                                node: statement,
                                kind: node.kind,
                            },
                        ));
                    };
                    if node.flags.0 != 0 {
                        return Err(self.unsupported(
                            statement,
                            node.kind,
                            SourceSyntaxRole::TypeAliasDeclaration,
                        ));
                    }
                    let export_modifier = self.validate_named_type_modifiers(
                        statement,
                        node.range,
                        alias.name,
                        alias.modifiers.as_ref(),
                        SyntaxKind::TypeAliasDeclaration,
                        SourceSyntaxRole::TypeAliasDeclaration,
                    )?;
                    if let Some(export_modifier) = export_modifier
                        && !is_external_module
                    {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::MissingExternalModuleFact {
                                node: export_modifier,
                                role: SourceSyntaxRole::TypeAliasDeclaration,
                            },
                        ));
                    }
                    let symbol =
                        self.bound
                            .symbol(statement)
                            .ok_or(SourceCheckError::Provenance(
                                SourceCheckProvenanceError::MissingDeclarationSymbol(statement),
                            ))?;
                    statements.push(PlannedStatement::TypeAlias(symbol));
                }
                SyntaxKind::InterfaceDeclaration => {
                    let node = self.node(statement)?;
                    let NodeData::InterfaceDeclaration(interface) = &node.data else {
                        return Err(SourceCheckError::Provenance(
                            SourceCheckProvenanceError::MismatchedNodeData {
                                node: statement,
                                kind: node.kind,
                            },
                        ));
                    };
                    if node.flags.0 != 0
                        || interface.flow_node.is_some()
                        || interface.local_symbol.is_some()
                        || interface.symbol.is_some()
                    {
                        return Err(self.unsupported(
                            statement,
                            node.kind,
                            SourceSyntaxRole::InterfaceDeclaration,
                        ));
                    }
                    let export_modifier = self.validate_named_type_modifiers(
                        statement,
                        node.range,
                        interface.name,
                        interface.modifiers.as_ref(),
                        SyntaxKind::InterfaceDeclaration,
                        SourceSyntaxRole::InterfaceDeclaration,
                    )?;
                    if let Some(export_modifier) = export_modifier
                        && !is_external_module
                    {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::MissingExternalModuleFact {
                                node: export_modifier,
                                role: SourceSyntaxRole::InterfaceDeclaration,
                            },
                        ));
                    }
                    let symbol =
                        self.bound
                            .symbol(statement)
                            .ok_or(SourceCheckError::Provenance(
                                SourceCheckProvenanceError::MissingDeclarationSymbol(statement),
                            ))?;
                    if let Some((store, host)) = self.semantic {
                        if interface.type_parameters.is_some() {
                            let plan =
                                super::object_members::plan_generic_interface(store, host, symbol)
                                    .map_err(|error| self.interface_plan_error(statement, error))?;
                            statements.push(PlannedStatement::GenericInterface(plan));
                            continue;
                        }
                        super::object_members::plan_interface(store, host, symbol)
                            .map_err(|error| self.interface_plan_error(statement, error))?;
                    }
                    statements.push(PlannedStatement::Interface(symbol));
                }
                SyntaxKind::ClassDeclaration => {
                    let node = self.node(statement)?;
                    let NodeData::ClassDeclaration(class) = &node.data else {
                        return Err(SourceCheckError::Provenance(
                            SourceCheckProvenanceError::MismatchedNodeData {
                                node: statement,
                                kind: node.kind,
                            },
                        ));
                    };
                    let Some(name) = class.name else {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Class(statement),
                        ));
                    };
                    self.reject_class_declaration_modifiers(
                        statement,
                        node.range,
                        name,
                        class.modifiers.as_ref(),
                    )?;
                    let Some((store, host)) = self.semantic else {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Class(statement),
                        ));
                    };
                    let symbol =
                        self.bound
                            .symbol(statement)
                            .ok_or(SourceCheckError::Provenance(
                                SourceCheckProvenanceError::MissingDeclarationSymbol(statement),
                            ))?;
                    let class = plan_nongeneric_class_member_query(store, host, symbol)
                        .map_err(|error| Self::class_plan_error(statement, error))?;
                    if class
                        .base_plan()
                        .is_some_and(|base| self.prior_classes.get(&base.symbol()) != Some(base))
                    {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Class(statement),
                        ));
                    }
                    preflight_nongeneric_class_member_query(store, host, &class)
                        .map_err(|error| Self::class_plan_error(statement, error))?;
                    if !self.planned_classes.insert(class.symbol()) {
                        return Err(SourceCheckError::Class(statement));
                    }
                    if let Some(direct) = class.direct_plan()
                        && self
                            .prior_classes
                            .insert(class.symbol(), direct.clone())
                            .is_some()
                    {
                        return Err(SourceCheckError::Class(statement));
                    }
                    statements.push(PlannedStatement::Class(class));
                }
                SyntaxKind::EnumDeclaration => {
                    let Some((store, host)) = self.semantic else {
                        return Err(self.unsupported(
                            statement,
                            SyntaxKind::EnumDeclaration,
                            SourceSyntaxRole::Statement,
                        ));
                    };
                    let enumeration = plan_top_level_enum(store, host, statement)
                        .map_err(|error| Self::enum_plan_error(statement, error))?;
                    statements.push(PlannedStatement::Enum(enumeration));
                }
                SyntaxKind::ExportDeclaration => {
                    if !is_external_module {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::MissingExternalModuleFact {
                                node: statement,
                                role: SourceSyntaxRole::ExportDeclaration,
                            },
                        ));
                    }
                    let NodeData::ExportDeclaration(export) = &self.node(statement)?.data else {
                        return Err(SourceCheckError::Provenance(
                            SourceCheckProvenanceError::MismatchedNodeData {
                                node: statement,
                                kind: SyntaxKind::ExportDeclaration,
                            },
                        ));
                    };
                    if export.module_specifier.is_some() {
                        let Some((store, _)) = self.semantic else {
                            return Err(SourceCheckError::Unsupported(
                                UnsupportedSourceSyntax::Import(statement),
                            ));
                        };
                        let reexport =
                            plan_top_level_named_reexport(self.arena, self.bound, store, statement)
                                .map_err(|error| Self::import_plan_error(statement, &error))?;
                        named_reexports.push(reexport);
                        statements.push(PlannedStatement::NamedReexport);
                    } else {
                        self.plan_external_module_marker(statement)?;
                        statements.push(PlannedStatement::ExternalModuleMarker);
                    }
                }
                SyntaxKind::FunctionDeclaration => {
                    if preplanned_overload_declarations.remove(&statement) {
                        statements.push(PlannedStatement::AmbientOverload);
                        continue;
                    }
                    let callable = preplanned_functions.remove(&statement).ok_or(
                        SourceCheckError::Function(SourceFunctionInvariant::MissingDeclaration(
                            statement,
                        )),
                    )?;
                    let (parameter_initializers, body) = if callable.body_mode.is_ambient() {
                        (Vec::new(), PlannedFunctionBody::Ambient)
                    } else {
                        self.plan_function_body(&callable)?
                    };
                    let index = functions.len();
                    functions.push(PlannedFunction {
                        callable,
                        parameter_initializers,
                        body,
                    });
                    statements.push(PlannedStatement::Function(index));
                }
                SyntaxKind::VariableStatement => {
                    if let Some(variables) = preplanned_ambient_variables.remove(&statement) {
                        ambient_variables.extend(variables);
                        statements.push(PlannedStatement::AmbientVariables);
                        continue;
                    }
                    let (declaration_list, exported) = {
                        let node = self.node(statement)?;
                        let NodeData::VariableStatement(variable) = &node.data else {
                            return Err(SourceCheckError::Provenance(
                                SourceCheckProvenanceError::MismatchedNodeData {
                                    node: statement,
                                    kind: node.kind,
                                },
                            ));
                        };
                        if node.flags.0 != 0 || variable.flow_node.is_some() || variable.facts != 0
                        {
                            return Err(self.unsupported(
                                statement,
                                node.kind,
                                SourceSyntaxRole::VariableStatement,
                            ));
                        }
                        let export_modifier = self.validate_variable_modifiers(
                            statement,
                            node.range,
                            variable.declaration_list,
                            variable.modifiers.as_ref(),
                        )?;
                        if let Some(export_modifier) = export_modifier
                            && !is_external_module
                        {
                            return Err(SourceCheckError::Unsupported(
                                UnsupportedSourceSyntax::MissingExternalModuleFact {
                                    node: export_modifier,
                                    role: SourceSyntaxRole::VariableModifier,
                                },
                            ));
                        }
                        (variable.declaration_list, export_modifier.is_some())
                    };
                    match self.plan_variable_statement(statement, declaration_list, exported)? {
                        PlannedVariableStatement::Arrow(arrow) => {
                            let index = arrows.len();
                            arrows.push(*arrow);
                            statements.push(PlannedStatement::Arrow(index));
                        }
                        PlannedVariableStatement::ContextualArrow(arrow) => {
                            let index = contextual_arrows.len();
                            contextual_arrows.push(PlannedContextualArrow { source: *arrow });
                            statements.push(PlannedStatement::ContextualArrow(index));
                        }
                        PlannedVariableStatement::Variables(variables) => {
                            statements.push(PlannedStatement::Variables(variables));
                        }
                    }
                }
                SyntaxKind::ExpressionStatement => {
                    if let Some(call) =
                        self.plan_top_level_direct_identifier_call_statement(statement)?
                    {
                        statements.push(PlannedStatement::ExpressionCall(call));
                        continue;
                    }
                    let Some((store, host)) = self.semantic else {
                        return Err(self.unsupported(
                            statement,
                            SyntaxKind::ExpressionStatement,
                            SourceSyntaxRole::Statement,
                        ));
                    };
                    let assignment = if self.assignable_ambient_variables.is_empty()
                        && self.assignable_uninitialized_variables.is_empty()
                        && self.assignable_mutable_variables.is_empty()
                    {
                        super::assignment::plan_simple_assignment(
                            self.arena, self.bound, store, host, statement,
                        )
                    } else if self.assignable_uninitialized_variables.is_empty()
                        && self.assignable_mutable_variables.is_empty()
                    {
                        super::assignment::plan_simple_assignment_with_ambient_targets(
                            self.arena,
                            self.bound,
                            store,
                            host,
                            &self.assignable_ambient_variables,
                            statement,
                        )
                    } else if self.assignable_mutable_variables.is_empty() {
                        super::assignment::plan_simple_assignment_with_source_targets(
                            self.arena,
                            self.bound,
                            store,
                            host,
                            &self.assignable_ambient_variables,
                            &self.assignable_uninitialized_variables,
                            statement,
                        )
                    } else {
                        super::assignment::plan_simple_assignment_with_all_source_targets(
                            self.arena,
                            self.bound,
                            store,
                            host,
                            &self.assignable_ambient_variables,
                            &self.assignable_uninitialized_variables,
                            &self.assignable_mutable_variables,
                            statement,
                        )
                    }
                    .map_err(Self::assignment_plan_error)?;
                    if !self.prior_variables.contains(&assignment.target_symbol) {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Assignment(
                                AssignmentUnsupported::TargetNotPrior {
                                    node: assignment.left,
                                    symbol: assignment.target_symbol,
                                },
                            ),
                        ));
                    }
                    if let Some(target_type_node) = assignment.target_type_node
                        && self
                            .type_import_references
                            .iter()
                            .any(|reference| reference.root == target_type_node)
                    {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Import(target_type_node),
                        ));
                    }
                    self.primitive_binary_position_roots
                        .insert(assignment.right);
                    let right = self.plan_expression(assignment.right)?;
                    self.assigned_variables.insert(assignment.target_symbol);
                    statements.push(PlannedStatement::Assignment(PlannedAssignment {
                        expression: assignment.expression,
                        left: assignment.left,
                        target_symbol: assignment.target_symbol,
                        target_type_node: assignment.target_type_node,
                        right,
                    }));
                }
                kind => {
                    return Err(self.unsupported(statement, kind, SourceSyntaxRole::Statement));
                }
            }
        }
        let arrows = arrows
            .into_iter()
            .map(|arrow| self.plan_arrow_body(arrow))
            .collect::<Result<Vec<_>, _>>()?;
        self.validate_type_import_reference_boundaries()?;
        Ok(SourceCheckPlan {
            statements,
            value_imports,
            type_imports,
            named_reexports,
            import_reads: self.import_reads,
            type_import_references: self.type_import_references,
            type_import_value_uses: self.type_import_value_uses,
            ambient_variables,
            overloads,
            functions,
            arrows,
            contextual_arrows,
            identifier_reads: self.identifier_reads,
            default_news: self.default_news,
            javascript_jsdoc: self.javascript_jsdoc,
            strings: self.strings,
            numbers: self.numbers,
            bigints: self.bigints,
        })
    }

    fn import_is_type_only(&self, declaration: NodeRef) -> Result<bool, SourceCheckError> {
        let record = self.node(declaration)?;
        let NodeData::ImportDeclaration(import) = &record.data else {
            return Ok(false);
        };
        let Some(clause) = import.import_clause.map(|node| self.reference(node)) else {
            return Ok(false);
        };
        let clause = self.node(clause)?;
        let NodeData::ImportClause(clause) = &clause.data else {
            return Ok(false);
        };
        Ok(clause.phase_modifier == Some(SyntaxKind::TypeKeyword))
    }

    fn type_import_alias_for_type_reference(
        &self,
        reference: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, SourceCheckError> {
        let record = self.node(reference)?;
        let NodeData::TypeReferenceNode(type_reference) = &record.data else {
            return Ok(None);
        };
        let mut name = self.reference(type_reference.type_name);
        let text = loop {
            match &self.node(name)?.data {
                NodeData::Identifier(identifier) => break identifier.text.as_str(),
                NodeData::QualifiedName(qualified) => name = self.reference(qualified.left),
                _ => return Ok(None),
            }
        };
        let mut matches = self
            .type_import_bindings
            .iter()
            .filter_map(|(&symbol, binding)| (binding.local_text == text).then_some(symbol));
        let Some(symbol) = matches.next() else {
            return Ok(None);
        };
        if matches.next().is_some() {
            return Err(SourceCheckError::Import(reference));
        }
        Ok(Some(symbol))
    }

    fn resolved_type_import_alias_for_reference(
        &self,
        reference: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, SourceCheckError> {
        let record = self.node(reference)?;
        let NodeData::TypeReferenceNode(type_reference) = &record.data else {
            return Ok(None);
        };
        let name = self.reference(type_reference.type_name);
        let name_record = self.node(name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Ok(None);
        };
        let Some((store, host)) = self.semantic else {
            return Ok(None);
        };
        let mut callback_host = host.name_resolver_host(store)?;
        let result = CanonicalNameResolver::new(
            self.arena,
            self.bound,
            store.symbol_store(),
            &mut callback_host,
        )
        .map_err(DeclaredTypeError::from)?
        .resolve(
            Some(CanonicalResolutionLocation::Bound(name)),
            &identifier.text,
            SymbolFlags::TYPE,
            None,
            true,
            false,
        );
        Ok(match result {
            Err(ts_binder::CanonicalNameResolutionError::AliasResolutionUnavailable(alias))
                if self.type_import_bindings.contains_key(&alias) =>
            {
                Some(alias)
            }
            _ => None,
        })
    }

    fn plan_type_import_annotation_root(&mut self, root: NodeRef) -> Result<(), SourceCheckError> {
        let mut references = Vec::new();
        let mut unsupported = None;
        let mut visited = HashSet::new();
        self.collect_type_import_annotation_graph(
            root,
            root,
            &mut visited,
            &mut references,
            &mut unsupported,
        )?;
        if references.is_empty() {
            return Ok(());
        }
        if let Some(node) = unsupported {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Import(node),
            ));
        }
        self.type_import_references.extend(references);
        Ok(())
    }

    fn collect_type_import_annotation_graph(
        &self,
        root: NodeRef,
        node: NodeRef,
        visited: &mut HashSet<NodeRef>,
        references: &mut Vec<PlannedSourceTypeImportReference>,
        unsupported: &mut Option<NodeRef>,
    ) -> Result<(), SourceCheckError> {
        if !visited.insert(node) {
            unsupported.get_or_insert(node);
            return Ok(());
        }
        let record = self.node(node)?;
        if record.flags.0 != 0 {
            unsupported.get_or_insert(node);
            return Ok(());
        }
        match &record.data {
            NodeData::TypeReferenceNode(reference) if record.kind == SyntaxKind::TypeReference => {
                if let Some(alias_symbol) = self.resolved_type_import_alias_for_reference(node)? {
                    if reference.type_arguments.is_some() {
                        unsupported.get_or_insert(node);
                    }
                    references.push(PlannedSourceTypeImportReference {
                        root,
                        node,
                        alias_symbol,
                    });
                } else {
                    unsupported.get_or_insert(node);
                }
            }
            NodeData::ParenthesizedTypeNode(parenthesized)
                if record.kind == SyntaxKind::ParenthesizedType =>
            {
                let child = self.reference(parenthesized.type_);
                if self.node(child)?.parent == Some(node.node) {
                    self.collect_type_import_annotation_graph(
                        root,
                        child,
                        visited,
                        references,
                        unsupported,
                    )?;
                } else {
                    unsupported.get_or_insert(node);
                }
            }
            NodeData::ArrayTypeNode(array) if record.kind == SyntaxKind::ArrayType => {
                let child = self.reference(array.element_type);
                if self.node(child)?.parent == Some(node.node) {
                    self.collect_type_import_annotation_graph(
                        root,
                        child,
                        visited,
                        references,
                        unsupported,
                    )?;
                } else {
                    unsupported.get_or_insert(node);
                }
            }
            NodeData::UnionTypeNode(union) if record.kind == SyntaxKind::UnionType => {
                if union.types.nodes.len() < 2 || union.types.has_trailing_comma {
                    unsupported.get_or_insert(node);
                }
                for child in &union.types.nodes {
                    let child = self.reference(*child);
                    if self.node(child)?.parent != Some(node.node) {
                        unsupported.get_or_insert(node);
                        continue;
                    }
                    self.collect_type_import_annotation_graph(
                        root,
                        child,
                        visited,
                        references,
                        unsupported,
                    )?;
                }
            }
            _ if matches!(
                record.kind,
                SyntaxKind::AnyKeyword
                    | SyntaxKind::UnknownKeyword
                    | SyntaxKind::StringKeyword
                    | SyntaxKind::NumberKeyword
                    | SyntaxKind::BigIntKeyword
                    | SyntaxKind::BooleanKeyword
                    | SyntaxKind::SymbolKeyword
                    | SyntaxKind::VoidKeyword
                    | SyntaxKind::UndefinedKeyword
                    | SyntaxKind::NullKeyword
                    | SyntaxKind::NeverKeyword
                    | SyntaxKind::ObjectKeyword
                    | SyntaxKind::IntrinsicKeyword
                    | SyntaxKind::LiteralType
            ) => {}
            _ => {
                unsupported.get_or_insert(node);
            }
        }
        Ok(())
    }

    fn validate_type_import_reference_boundaries(&self) -> Result<(), SourceCheckError> {
        if self.type_import_bindings.is_empty() {
            return Ok(());
        }
        let planned = self
            .type_import_references
            .iter()
            .map(|reference| reference.node)
            .collect::<HashSet<_>>();
        for (node, record) in self.arena.iter() {
            if record.kind != SyntaxKind::TypeReference {
                continue;
            }
            let reference = self.reference(node);
            if self
                .type_import_alias_for_type_reference(reference)?
                .is_some()
                && !planned.contains(&reference)
            {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Import(reference),
                ));
            }
        }
        Ok(())
    }

    /// Plans the strict top-level `identifier(arguments);` expression-statement
    /// leaf. Every other expression statement remains on the existing simple
    /// assignment route.
    fn plan_top_level_direct_identifier_call_statement(
        &mut self,
        statement: NodeRef,
    ) -> Result<Option<PlannedExpression>, SourceCheckError> {
        let (statement_range, expression) = {
            let node = self.node(statement)?;
            let NodeData::ExpressionStatement(data) = &node.data else {
                return Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MismatchedNodeData {
                        node: statement,
                        kind: node.kind,
                    },
                ));
            };
            let expression = self.reference(data.expression);
            if self.node(expression)?.kind != SyntaxKind::CallExpression {
                return Ok(None);
            }
            if node.kind != SyntaxKind::ExpressionStatement
                || node.flags.0 != 0
                || node.parent != Some(self.source.node_ref().node)
                || data.flow_node.is_some()
            {
                return Err(self.unsupported(statement, node.kind, SourceSyntaxRole::Statement));
            }
            (node.range, expression)
        };
        let (expression_range, callee) = {
            let node = self.node(expression)?;
            let NodeData::CallExpression(call) = &node.data else {
                return Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MismatchedNodeData {
                        node: expression,
                        kind: node.kind,
                    },
                ));
            };
            if node.kind != SyntaxKind::CallExpression
                || node.flags.0 != 0
                || node.parent != Some(statement.node)
                || node.range.start < statement_range.start
                || node.range.end > statement_range.end
                || call.question_dot_token.is_some()
                || call.symbol.is_some()
                || call.facts != 0
            {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(expression),
                ));
            }
            (node.range, self.reference(call.expression))
        };
        let callee_node = self.node(callee)?;
        let NodeData::Identifier(identifier) = &callee_node.data else {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Call(expression),
            ));
        };
        if callee_node.kind != SyntaxKind::Identifier
            || callee_node.flags.0 != 0
            || callee_node.parent != Some(expression.node)
            || callee_node.range.start < expression_range.start
            || callee_node.range.end > expression_range.end
            || identifier.text.is_empty()
            || identifier.flow_node.is_some()
        {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Call(expression),
            ));
        }
        let planned = self.plan_expression(expression)?;
        if planned.node != expression || !matches!(&planned.kind, PlannedExpressionKind::Call(_)) {
            return Err(SourceCheckError::Call(expression));
        }
        Ok(Some(planned))
    }

    fn is_direct_top_level_variable_initializer(
        &self,
        expression: NodeRef,
    ) -> Result<bool, SourceCheckError> {
        let Some(declaration) = self
            .node(expression)?
            .parent
            .map(|node| self.reference(node))
        else {
            return Ok(false);
        };
        let declaration_record = self.node(declaration)?;
        let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
            return Ok(false);
        };
        if declaration_record.kind != SyntaxKind::VariableDeclaration
            || variable.initializer != Some(expression.node)
        {
            return Ok(false);
        }
        let Some(list) = declaration_record.parent.map(|node| self.reference(node)) else {
            return Ok(false);
        };
        let list_record = self.node(list)?;
        let Some(statement) = list_record.parent.map(|node| self.reference(node)) else {
            return Ok(false);
        };
        let statement_record = self.node(statement)?;
        Ok(list_record.kind == SyntaxKind::VariableDeclarationList
            && statement_record.kind == SyntaxKind::VariableStatement
            && statement_record.parent == Some(self.source.node_ref().node))
    }

    fn assignment_plan_error(error: super::assignment::AssignmentPlanError) -> SourceCheckError {
        match error {
            super::assignment::AssignmentPlanError::Unsupported(error) => {
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Assignment(error))
            }
            super::assignment::AssignmentPlanError::Invariant(error) => {
                SourceCheckError::Assignment(error)
            }
            super::assignment::AssignmentPlanError::DeclaredType(error) => {
                SourceCheckError::DeclaredType(error)
            }
        }
    }

    fn variable_plan_error(error: VariablePlanError) -> SourceCheckError {
        match error {
            VariablePlanError::Unsupported(error) => {
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Variable(error))
            }
            VariablePlanError::Invariant(error) => SourceCheckError::Variable(error),
            VariablePlanError::DeclaredType(error) => SourceCheckError::DeclaredType(error),
        }
    }

    fn function_statements_plan_error(
        callable: &SourceCallablePlan,
        error: SourceFunctionStatementsError,
    ) -> SourceCheckError {
        match error {
            SourceFunctionStatementsError::Unsupported(_) => {
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
                    SourceFunctionUnsupported::FunctionBody(callable.body),
                ))
            }
            SourceFunctionStatementsError::Variable(error) => Self::variable_plan_error(error),
            SourceFunctionStatementsError::Invariant(reason) => {
                let node = match reason {
                    SourceFunctionStatementsInvariant::BoundSourceMismatch(node)
                    | SourceFunctionStatementsInvariant::MissingNode(node)
                    | SourceFunctionStatementsInvariant::NodeNotBound(node)
                    | SourceFunctionStatementsInvariant::MismatchedNodeData { node, .. }
                    | SourceFunctionStatementsInvariant::InvalidParent { node, .. }
                    | SourceFunctionStatementsInvariant::InvalidRange { node, .. }
                    | SourceFunctionStatementsInvariant::InvalidListRange(node)
                    | SourceFunctionStatementsInvariant::InvalidCallableEdge(node)
                    | SourceFunctionStatementsInvariant::InvalidContainer { node, .. }
                    | SourceFunctionStatementsInvariant::InvalidBlockScopeContainer {
                        node, ..
                    }
                    | SourceFunctionStatementsInvariant::MissingLocals(node)
                    | SourceFunctionStatementsInvariant::InvalidFlowContainer { node, .. }
                    | SourceFunctionStatementsInvariant::MissingFlowStart(node)
                    | SourceFunctionStatementsInvariant::UnexpectedFlowEnd(node)
                    | SourceFunctionStatementsInvariant::UnexpectedReturnFlow(node)
                    | SourceFunctionStatementsInvariant::CyclicCondition(node) => node,
                    SourceFunctionStatementsInvariant::LocalTableMismatch {
                        declaration, ..
                    } => declaration,
                    SourceFunctionStatementsInvariant::InvalidOrder { next, .. } => next,
                };
                SourceCheckError::Function(SourceFunctionInvariant::Callable(node))
            }
        }
    }

    fn joined_function_statements_plan_error(
        callable: &SourceCallablePlan,
        error: SourceJoinedFunctionStatementsError,
    ) -> SourceCheckError {
        match error {
            SourceJoinedFunctionStatementsError::Statements(error) => {
                Self::function_statements_plan_error(callable, error)
            }
            SourceJoinedFunctionStatementsError::Unsupported(_) => {
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
                    SourceFunctionUnsupported::FunctionBody(callable.body),
                ))
            }
            SourceJoinedFunctionStatementsError::Invariant(reason) => {
                let node = match reason {
                    SourceJoinedFunctionStatementsInvariant::InvalidCallableEdge(node)
                    | SourceJoinedFunctionStatementsInvariant::InvalidFlowContainer {
                        node, ..
                    }
                    | SourceJoinedFunctionStatementsInvariant::MissingFlowStart(node)
                    | SourceJoinedFunctionStatementsInvariant::UnexpectedFlowEnd(node)
                    | SourceJoinedFunctionStatementsInvariant::UnexpectedReturnFlow(node)
                    | SourceJoinedFunctionStatementsInvariant::MissingFlowPoint(node)
                    | SourceJoinedFunctionStatementsInvariant::FlowPointMismatch { node, .. } => {
                        node
                    }
                    SourceJoinedFunctionStatementsInvariant::MissingFlowNode(_)
                    | SourceJoinedFunctionStatementsInvariant::InvalidFlowNode(_) => {
                        callable.declaration
                    }
                };
                SourceCheckError::Function(SourceFunctionInvariant::Callable(node))
            }
        }
    }

    fn source_flow_plan_error(
        callable: &SourceCallablePlan,
        error: SourceFlowError,
    ) -> SourceCheckError {
        match error {
            SourceFlowError::Unsupported(_)
            | SourceFlowError::Narrowing {
                error: LogicalBinaryError::Unsupported(LogicalBinaryUnsupported::Type(_)),
                ..
            } => SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
                SourceFunctionUnsupported::FunctionBody(callable.body),
            )),
            SourceFlowError::Invariant(_) => {
                SourceCheckError::Function(SourceFunctionInvariant::Callable(callable.declaration))
            }
            SourceFlowError::Narrowing {
                condition,
                error:
                    LogicalBinaryError::Unsupported(LogicalBinaryUnsupported::Operator(_))
                    | LogicalBinaryError::Invariant(_),
            } => SourceCheckError::LogicalOperator(condition),
            #[cfg(not(test))]
            SourceFlowError::Narrowing {
                condition,
                error: LogicalBinaryError::Unsupported(LogicalBinaryUnsupported::MissingGlobalTypes),
            } => SourceCheckError::LogicalOperator(condition),
            SourceFlowError::Narrowing {
                error: LogicalBinaryError::Literal(error),
                ..
            } => error.into(),
            SourceFlowError::Join { error, .. } => error.into(),
        }
    }

    fn function_plan_error(error: SourceFunctionPlanError) -> SourceCheckError {
        match error {
            SourceFunctionPlanError::Unsupported(error) => {
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(error))
            }
            SourceFunctionPlanError::Invariant(error) => SourceCheckError::Function(error),
            SourceFunctionPlanError::DeclaredType(error) => SourceCheckError::DeclaredType(error),
        }
    }

    fn enum_plan_error(declaration: NodeRef, error: SourceEnumError) -> SourceCheckError {
        let node = error.node().unwrap_or(declaration);
        match error {
            SourceEnumError::Unsupported(_) => {
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Enum(node))
            }
            SourceEnumError::Invariant(_) => SourceCheckError::Enum(node),
            SourceEnumError::DeclaredType(error) => SourceCheckError::DeclaredType(error),
        }
    }

    fn class_plan_error(
        declaration: NodeRef,
        error: super::classes::ClassError,
    ) -> SourceCheckError {
        let node = error.node().unwrap_or(declaration);
        match error {
            super::classes::ClassError::Unsupported(_) => {
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(node))
            }
            super::classes::ClassError::Invariant(_) => SourceCheckError::Class(node),
            super::classes::ClassError::DeclaredType(error) => {
                SourceCheckError::DeclaredType(error)
            }
        }
    }

    fn new_plan_error(expression: NodeRef, error: SourceNewError) -> SourceCheckError {
        let node = error.node().unwrap_or(expression);
        match error {
            SourceNewError::Unsupported(reason) => {
                let boundary = match reason {
                    SourceNewUnsupported::Expression(node)
                    | SourceNewUnsupported::Constructor(node)
                    | SourceNewUnsupported::MissingArgumentList(node)
                    | SourceNewUnsupported::Arguments(node)
                    | SourceNewUnsupported::TypeArguments(node)
                    | SourceNewUnsupported::ConstructorClass { node, .. }
                    | SourceNewUnsupported::ConstructorNotPrior { node, .. } => node,
                };
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(boundary))
            }
            SourceNewError::Invariant(SourceNewInvariant::NameResolution { error, .. }) => {
                SourceCheckError::Variable(VariableInvariant::NameResolution(error))
            }
            SourceNewError::Invariant(_) => SourceCheckError::Call(node),
            SourceNewError::DeclaredType(error) => SourceCheckError::DeclaredType(error),
            SourceNewError::Class(error) => Self::class_plan_error(expression, error),
        }
    }

    fn import_plan_error(declaration: NodeRef, error: &SourceImportError) -> SourceCheckError {
        let node = error.node().unwrap_or(declaration);
        match error {
            SourceImportError::Unsupported(_) | SourceImportError::CircularAlias { .. } => {
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Import(node))
            }
            SourceImportError::Invariant(_) => SourceCheckError::Import(node),
            SourceImportError::Alias(error) => {
                if import_alias_error_is_unsupported(*error) {
                    SourceCheckError::Unsupported(UnsupportedSourceSyntax::Import(node))
                } else {
                    SourceCheckError::Import(node)
                }
            }
            SourceImportError::DeclaredType(error) => SourceCheckError::DeclaredType(*error),
            SourceImportError::Variable(error) => match *error {
                VariablePlanError::Unsupported(_) => {
                    SourceCheckError::Unsupported(UnsupportedSourceSyntax::Import(node))
                }
                VariablePlanError::Invariant(_) => SourceCheckError::Import(node),
                VariablePlanError::DeclaredType(error) => SourceCheckError::DeclaredType(error),
            },
            SourceImportError::Callable(error) => match *error {
                SourceCallableError::Unsupported(_) => {
                    SourceCheckError::Unsupported(UnsupportedSourceSyntax::Import(node))
                }
                SourceCallableError::Invariant(_) => SourceCheckError::Import(node),
                SourceCallableError::DeclaredType(error) => SourceCheckError::DeclaredType(error),
                SourceCallableError::LiteralCache(error) => error.into(),
            },
        }
    }

    fn property_plan_error(error: SourcePropertyError) -> SourceCheckError {
        match error {
            SourcePropertyError::Unsupported(reason) => {
                let node = match reason {
                    SourcePropertyUnsupported::Access(node)
                    | SourcePropertyUnsupported::Receiver(node)
                    | SourcePropertyUnsupported::MemberCall(node)
                    | SourcePropertyUnsupported::MissingOwnProperty { node, .. }
                    | SourcePropertyUnsupported::OptionalProperty { node, .. }
                    | SourcePropertyUnsupported::ApparentObjectProperty { node, .. }
                    | SourcePropertyUnsupported::AmbiguousPropertySuggestion { node, .. } => node,
                };
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Property(node))
            }
            SourcePropertyError::InvalidCache(node) | SourcePropertyError::Capacity(node) => {
                SourceCheckError::Property(node)
            }
            SourcePropertyError::Union { node, error } => {
                use super::member_resolution::UnionPropertyError;

                match error {
                    UnionPropertyError::UnsupportedUnion(_)
                    | UnionPropertyError::UnsupportedConstituent(_)
                    | UnionPropertyError::UnsupportedPropertyType(_)
                    | UnionPropertyError::UnsupportedExactOptionalProperty(_) => {
                        SourceCheckError::Unsupported(UnsupportedSourceSyntax::Property(node))
                    }
                    UnionPropertyError::InvalidUnion(_)
                    | UnionPropertyError::InvalidProperty(_)
                    | UnionPropertyError::InvalidCache(_)
                    | UnionPropertyError::Capacity(_) => SourceCheckError::Property(node),
                    UnionPropertyError::Relation(error) => {
                        SourceCheckError::RelationUnavailable(error)
                    }
                    UnionPropertyError::TypeCache(error) => error.into(),
                }
            }
            SourcePropertyError::Relation(error) => SourceCheckError::RelationUnavailable(error),
            SourcePropertyError::Display(error) => SourceCheckError::TypeDisplayUnavailable(error),
            SourcePropertyError::MissingDiagnostic(code) => {
                SourceCheckError::MissingDiagnostic(code)
            }
        }
    }

    fn element_plan_error(access: NodeRef, error: SourceElementError) -> SourceCheckError {
        match error {
            SourceElementError::Unsupported(reason) => {
                let node = match reason {
                    SourceElementUnsupported::Access(node)
                    | SourceElementUnsupported::Receiver(node)
                    | SourceElementUnsupported::Index(node)
                    | SourceElementUnsupported::MemberCall(node)
                    | SourceElementUnsupported::Write(node)
                    | SourceElementUnsupported::OptionalProperty { node, .. } => node,
                    SourceElementUnsupported::IndexType(_)
                    | SourceElementUnsupported::IndexSignatureSurface(_) => access,
                };
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Element(node))
            }
            SourceElementError::InvalidCache(node) => SourceCheckError::Element(node),
            SourceElementError::InvalidType(_) => SourceCheckError::Element(access),
            SourceElementError::Relation(error) => SourceCheckError::RelationUnavailable(error),
            SourceElementError::Array(error) => SourceCheckError::ArrayType(error),
            SourceElementError::Literal(error) => error.into(),
            SourceElementError::Display(error) => SourceCheckError::TypeDisplayUnavailable(error),
            SourceElementError::MissingDiagnostic(code) => {
                SourceCheckError::MissingDiagnostic(code)
            }
        }
    }

    fn callable_plan_error(error: SourceCallableError) -> SourceCheckError {
        let node = error.node();
        match error {
            SourceCallableError::Unsupported(_) => SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::Callable(
                    node.expect("source callable unsupported errors retain their syntax node"),
                )),
            ),
            SourceCallableError::Invariant(_) => {
                SourceCheckError::Function(SourceFunctionInvariant::Callable(
                    node.expect("source callable invariant errors retain their syntax node"),
                ))
            }
            SourceCallableError::DeclaredType(error) => SourceCheckError::DeclaredType(error),
            SourceCallableError::LiteralCache(error) => error.into(),
        }
    }

    fn overload_plan_error(fallback: NodeRef, error: SourceOverloadError) -> SourceCheckError {
        match error {
            SourceOverloadError::Unsupported(node) => SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::Callable(node)),
            ),
            SourceOverloadError::Callable(error) => Self::callable_plan_error(error),
            SourceOverloadError::Literal(error) => error.into(),
            SourceOverloadError::Invariant(_) => SourceCheckError::Function(
                SourceFunctionInvariant::Callable(error.node().unwrap_or(fallback)),
            ),
        }
    }

    fn arrow_plan_error(error: SourceArrowError) -> SourceCheckError {
        let node = error.node();
        match error {
            SourceArrowError::Unsupported(_) => {
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Arrow(
                    node.expect("source arrow unsupported errors retain their syntax node"),
                ))
            }
            SourceArrowError::Invariant(_) => SourceCheckError::Arrow(
                node.expect("source arrow invariant errors retain their syntax node"),
            ),
            SourceArrowError::DeclaredType(error) => SourceCheckError::DeclaredType(error),
            SourceArrowError::LiteralCache(error) => error.into(),
        }
    }

    fn contextual_arrow_plan_error(error: SourceContextualArrowError) -> SourceCheckError {
        let node = error.node();
        match error {
            SourceContextualArrowError::Unsupported(_) => {
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Arrow(
                    node.expect("contextual arrow unsupported errors retain their syntax node"),
                ))
            }
            SourceContextualArrowError::Invariant(_) => SourceCheckError::Arrow(
                node.expect("contextual arrow invariant errors retain their syntax node"),
            ),
            SourceContextualArrowError::DeclaredType(error) => {
                SourceCheckError::DeclaredType(error)
            }
            SourceContextualArrowError::LiteralCache(error) => error.into(),
        }
    }

    fn preplan_function_header(
        &self,
        declaration: NodeRef,
        is_external_module: bool,
        is_declaration_file: bool,
    ) -> Result<PlannedFunctionHeader, SourceCheckError> {
        let (range, flags, facts, modifiers, name_id) = {
            let node = self.node(declaration)?;
            let NodeData::FunctionDeclaration(function) = &node.data else {
                return Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MismatchedNodeData {
                        node: declaration,
                        kind: node.kind,
                    },
                ));
            };
            (
                node.range,
                node.flags.0,
                function.facts,
                function.modifiers.clone(),
                function.name,
            )
        };
        if flags != 0 || facts != 0 {
            return Err(self.unsupported(
                declaration,
                SyntaxKind::FunctionDeclaration,
                SourceSyntaxRole::FunctionDeclaration,
            ));
        }
        let name = name_id.map(|name| self.reference(name)).ok_or_else(|| {
            self.unsupported(
                declaration,
                SyntaxKind::FunctionDeclaration,
                SourceSyntaxRole::FunctionName,
            )
        })?;
        let (name_text, name_start) = {
            let node = self.node(name)?;
            let NodeData::Identifier(identifier) = &node.data else {
                return Err(self.unsupported(name, node.kind, SourceSyntaxRole::FunctionName));
            };
            if node.kind != SyntaxKind::Identifier
                || node.flags.0 != 0
                || node.parent != Some(declaration.node)
                || identifier.flow_node.is_some()
            {
                return Err(self.unsupported(name, node.kind, SourceSyntaxRole::FunctionName));
            }
            (identifier.text.clone(), node.range.start.get())
        };
        let modifier_mode =
            self.validate_function_modifiers(declaration, range, name_start, modifiers.as_ref())?;
        match modifier_mode {
            PlannedFunctionModifierMode::Export(export_modifier)
            | PlannedFunctionModifierMode::ExportDeclare(export_modifier)
                if !is_external_module =>
            {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::MissingExternalModuleFact {
                        node: export_modifier,
                        role: SourceSyntaxRole::FunctionModifier,
                    },
                ));
            }
            _ => {}
        }
        if matches!(modifier_mode, PlannedFunctionModifierMode::None)
            && is_declaration_file
            && self
                .node(declaration)?
                .parent
                .is_none_or(|parent| parent != self.source.node_ref().node)
        {
            return Err(self.unsupported(
                declaration,
                SyntaxKind::FunctionDeclaration,
                SourceSyntaxRole::FunctionDeclaration,
            ));
        }
        Ok(PlannedFunctionHeader {
            name,
            name_text,
            modifier_mode,
        })
    }

    fn preplan_function_declaration(
        &mut self,
        declaration: NodeRef,
        is_external_module: bool,
        is_declaration_file: bool,
    ) -> Result<SourceCallablePlan, SourceCheckError> {
        let header =
            self.preplan_function_header(declaration, is_external_module, is_declaration_file)?;
        let Some((store, host)) = self.semantic else {
            return Err(self.unsupported(
                declaration,
                SyntaxKind::FunctionDeclaration,
                SourceSyntaxRole::FunctionDeclaration,
            ));
        };
        let function = plan_top_level_function(
            self.bound,
            store,
            declaration,
            header.name,
            &header.name_text,
            matches!(
                header.modifier_mode,
                PlannedFunctionModifierMode::Export(_)
                    | PlannedFunctionModifierMode::ExportDeclare(_)
            ),
        )
        .map_err(Self::function_plan_error)?;
        let callable = plan_source_callable(
            store,
            host,
            declaration,
            function.owner_symbol,
            self.array_targets,
        )
        .map_err(Self::callable_plan_error)?;
        let body_mode_matches = matches!(
            (header.modifier_mode, callable.body_mode),
            (
                PlannedFunctionModifierMode::Declare
                    | PlannedFunctionModifierMode::ExportDeclare(_),
                SourceCallableBodyMode::AmbientDeclaration
            ) | (
                PlannedFunctionModifierMode::None | PlannedFunctionModifierMode::Export(_),
                SourceCallableBodyMode::Present
            )
        ) || is_declaration_file
            && matches!(
                (header.modifier_mode, callable.body_mode),
                (
                    PlannedFunctionModifierMode::None | PlannedFunctionModifierMode::Export(_),
                    SourceCallableBodyMode::AmbientDeclaration
                )
            );
        if !body_mode_matches {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(declaration),
            ));
        }
        if !self.hoisted_functions.insert(function.owner_symbol) {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::DuplicateDeclaration(declaration),
            ));
        }
        Ok(callable)
    }

    fn preplan_function_overload_group(
        &mut self,
        declarations: &[NodeRef],
        is_external_module: bool,
        is_declaration_file: bool,
    ) -> Result<SourceOverloadPlan, SourceCheckError> {
        let Some(first) = declarations.first().copied() else {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::MissingDeclaration(self.source.node_ref()),
            ));
        };
        let Some((store, host)) = self.semantic else {
            return Err(self.unsupported(
                first,
                SyntaxKind::FunctionDeclaration,
                SourceSyntaxRole::FunctionDeclaration,
            ));
        };
        let raw_owner = self
            .bound
            .symbol(first)
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(first),
            ))?;
        let owner = store
            .get_merged_symbol(raw_owner)
            .ok_or(SourceCheckError::Function(
                SourceFunctionInvariant::InvalidMergedSymbol(raw_owner),
            ))?;
        if owner != raw_owner {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::MergedSymbol {
                    node: first,
                    source: raw_owner,
                    target: owner,
                }),
            ));
        }
        let owner_record = store.symbol(owner).ok_or(SourceCheckError::Function(
            SourceFunctionInvariant::InvalidSymbol(owner),
        ))?;
        let actual_declarations = owner_record
            .declarations()
            .ok_or(SourceCheckError::Function(
                SourceFunctionInvariant::MissingDeclarations(owner),
            ))?;
        if owner_record.flags() != SymbolFlags::FUNCTION {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::NonFunctionSymbol {
                    node: first,
                    symbol: owner,
                    flags: owner_record.flags(),
                }),
            ));
        }
        if actual_declarations != declarations
            || owner_record.value_declaration() != Some(first)
            || owner_record.parent().is_some()
            || owner_record.export_symbol().is_some()
            || owner_record.exports().is_some()
        {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Function(
                    SourceFunctionUnsupported::NonUniqueDeclaration {
                        node: first,
                        symbol: owner,
                        declaration_count: actual_declarations.len(),
                    },
                ),
            ));
        }
        let mut expected_name = None;
        for declaration in declarations {
            let header = self.preplan_function_header(
                *declaration,
                is_external_module,
                is_declaration_file,
            )?;
            if !matches!(header.modifier_mode, PlannedFunctionModifierMode::Declare)
                || expected_name
                    .as_ref()
                    .is_some_and(|name: &String| name != &header.name_text)
                || self.bound.symbol(*declaration) != Some(owner)
            {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Function(
                        SourceFunctionUnsupported::NonUniqueDeclaration {
                            node: *declaration,
                            symbol: owner,
                            declaration_count: declarations.len(),
                        },
                    ),
                ));
            }
            expected_name.get_or_insert(header.name_text);
        }
        let plan = plan_source_ambient_overload_group(
            store,
            host,
            owner,
            declarations,
            self.array_targets,
        )
        .map_err(|error| Self::overload_plan_error(first, error))?;
        if !self.hoisted_functions.insert(owner) {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::DuplicateDeclaration(first),
            ));
        }
        Ok(plan)
    }

    fn validate_named_type_modifiers(
        &self,
        declaration: NodeRef,
        declaration_range: TextRange,
        name: NodeId,
        modifiers: Option<&ModifierList>,
        declaration_kind: SyntaxKind,
        role: SourceSyntaxRole,
    ) -> Result<Option<NodeRef>, SourceCheckError> {
        let Some(modifiers) = modifiers else {
            return Ok(None);
        };
        let [modifier_id] = modifiers.list.nodes.as_slice() else {
            return Err(self.unsupported(declaration, declaration_kind, role));
        };
        let modifier = self.reference(*modifier_id);
        let modifier_node = self.node(modifier)?;
        let name_start = self.node(self.reference(name))?.range.start.get();
        if modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
            || modifiers.list.range.start != declaration_range.start
            || modifiers.list.range.end.get() > name_start
            || modifier_node.kind != SyntaxKind::ExportKeyword
            || !matches!(modifier_node.data, NodeData::Token(_))
            || modifier_node.flags.0 != 0
            || modifier_node.parent != Some(declaration.node)
            || modifier_node.range.start != declaration_range.start
            || modifier_node.range.end.get() > modifiers.list.range.end.get()
            || !self.source_spelling_matches(modifier, "export")
        {
            return Err(self.unsupported(modifier, modifier_node.kind, role));
        }
        Ok(Some(modifier))
    }

    fn reject_class_declaration_modifiers(
        &self,
        declaration: NodeRef,
        declaration_range: TextRange,
        name: NodeId,
        modifiers: Option<&ModifierList>,
    ) -> Result<(), SourceCheckError> {
        let Some(modifiers) = modifiers else {
            return Ok(());
        };
        match self.validate_named_type_modifiers(
            declaration,
            declaration_range,
            name,
            Some(modifiers),
            SyntaxKind::ClassDeclaration,
            SourceSyntaxRole::Statement,
        ) {
            Err(error @ SourceCheckError::Provenance(_)) => Err(error),
            Ok(_) | Err(_) => Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Class(declaration),
            )),
        }
    }

    fn validate_function_modifiers(
        &self,
        declaration: NodeRef,
        declaration_range: TextRange,
        name_start: u32,
        modifiers: Option<&ModifierList>,
    ) -> Result<PlannedFunctionModifierMode, SourceCheckError> {
        let Some(modifiers) = modifiers else {
            return Ok(PlannedFunctionModifierMode::None);
        };
        let (export_modifier, modifier_id) = match modifiers.list.nodes.as_slice() {
            [modifier] => (None, *modifier),
            [export, declare] => (Some(self.reference(*export)), *declare),
            _ => {
                return Err(self.unsupported(
                    declaration,
                    SyntaxKind::FunctionDeclaration,
                    SourceSyntaxRole::FunctionModifier,
                ));
            }
        };
        let modifier = self.reference(modifier_id);
        let node = self.node(modifier)?;
        if let Some(export_modifier) = export_modifier {
            let export_node = self.node(export_modifier)?;
            if export_node.kind != SyntaxKind::ExportKeyword
                || !matches!(export_node.data, NodeData::Token(_))
                || export_node.flags.0 != 0
                || export_node.parent != Some(declaration.node)
                || export_node.range.start != declaration_range.start
                || export_node.range.end > node.range.start
                || !self.source_spelling_matches(export_modifier, "export")
                || node.kind != SyntaxKind::DeclareKeyword
            {
                return Err(self.unsupported(
                    export_modifier,
                    export_node.kind,
                    SourceSyntaxRole::FunctionModifier,
                ));
            }
        }
        if modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
            || modifiers.list.range.start != declaration_range.start
            || modifiers.list.range.end.get() > name_start
            || !matches!(
                node.kind,
                SyntaxKind::ExportKeyword | SyntaxKind::DeclareKeyword
            )
            || !matches!(node.data, NodeData::Token(_))
            || node.flags.0 != 0
            || node.parent != Some(declaration.node)
            || (export_modifier.is_none() && node.range.start != declaration_range.start)
            || node.range.end.get() > name_start
            || (export_modifier.is_none() && node.range.end.get() > modifiers.list.range.end.get())
            || !self.source_spelling_matches(
                modifier,
                if node.kind == SyntaxKind::ExportKeyword {
                    "export"
                } else {
                    "declare"
                },
            )
        {
            return Err(self.unsupported(modifier, node.kind, SourceSyntaxRole::FunctionModifier));
        }
        Ok(match (export_modifier, node.kind) {
            (Some(export), SyntaxKind::DeclareKeyword) => {
                PlannedFunctionModifierMode::ExportDeclare(export)
            }
            (None, SyntaxKind::ExportKeyword) => PlannedFunctionModifierMode::Export(modifier),
            (None, SyntaxKind::DeclareKeyword) => PlannedFunctionModifierMode::Declare,
            _ => {
                return Err(self.unsupported(
                    modifier,
                    node.kind,
                    SourceSyntaxRole::FunctionModifier,
                ));
            }
        })
    }

    fn plan_function_body(
        &mut self,
        callable: &SourceCallablePlan,
    ) -> Result<(Vec<PlannedParameterInitializer>, PlannedFunctionBody), SourceCheckError> {
        if callable.body_mode != SourceCallableBodyMode::Present {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(callable.declaration),
            ));
        }
        let parameter_initializers = self.plan_parameter_initializers_and_enter_scope(callable)?;
        let body_prior_variables = self.prior_variables.clone();
        let body_readable_variables = self.readable_variables.clone();
        let result = self.plan_function_body_contents(callable);
        // Statement planning may enter leading and branch-local scopes. Always
        // restore the exact parameter-entry state, including on a typed
        // unsupported boundary, before removing the parameters themselves.
        self.prior_variables = body_prior_variables;
        self.readable_variables = body_readable_variables;
        self.leave_callable_parameter_scope(callable)?;
        Ok((parameter_initializers, result?))
    }

    fn plan_parameter_initializers_and_enter_scope(
        &mut self,
        callable: &SourceCallablePlan,
    ) -> Result<Vec<PlannedParameterInitializer>, SourceCheckError> {
        let mut initializers = Vec::new();
        for (entered, parameter) in callable.parameters.iter().enumerate() {
            if let Some(initializer) = parameter.initializer {
                self.primitive_binary_position_roots.insert(initializer);
                let expression = match self.plan_expression(initializer) {
                    Ok(expression) => expression,
                    Err(error) => {
                        self.leave_callable_parameter_prefix_scope(callable, entered)?;
                        return Err(error);
                    }
                };
                initializers.push(PlannedParameterInitializer {
                    parameter: *parameter,
                    expression,
                });
            }
            let inserted_prior = self.prior_variables.insert(parameter.symbol);
            let inserted_readable = self.readable_variables.insert(parameter.symbol);
            if !inserted_prior || !inserted_readable {
                if inserted_prior {
                    self.prior_variables.remove(&parameter.symbol);
                }
                if inserted_readable {
                    self.readable_variables.remove(&parameter.symbol);
                }
                self.leave_callable_parameter_prefix_scope(callable, entered)?;
                return Err(callable_parameter_execution_error(
                    callable,
                    parameter.declaration,
                ));
            }
        }
        Ok(initializers)
    }

    fn leave_callable_parameter_scope(
        &mut self,
        callable: &SourceCallablePlan,
    ) -> Result<(), SourceCheckError> {
        self.leave_callable_parameter_prefix_scope(callable, callable.parameters.len())
    }

    fn leave_callable_parameter_prefix_scope(
        &mut self,
        callable: &SourceCallablePlan,
        entered: usize,
    ) -> Result<(), SourceCheckError> {
        let mut invalid = None;
        for parameter in callable.parameters.iter().take(entered) {
            let removed_prior = self.prior_variables.remove(&parameter.symbol);
            let removed_readable = self.readable_variables.remove(&parameter.symbol);
            if (!removed_prior || !removed_readable) && invalid.is_none() {
                invalid = Some(parameter.declaration);
            }
        }
        invalid.map_or(Ok(()), |parameter| {
            Err(callable_parameter_execution_error(callable, parameter))
        })
    }

    fn plan_function_body_contents(
        &mut self,
        callable: &SourceCallablePlan,
    ) -> Result<PlannedFunctionBody, SourceCheckError> {
        let body = callable.body;
        let statements = {
            let node = self.node(body)?;
            let NodeData::Block(block) = &node.data else {
                return Err(self.unsupported(body, node.kind, SourceSyntaxRole::FunctionBody));
            };
            if node.kind != SyntaxKind::Block
                || node.flags.0 != 0
                || node.parent != Some(callable.declaration.node)
                || block.flow_node.is_some()
                || block.next_container.is_some()
                || block.statements.has_trailing_comma
                || block.facts != 0
            {
                return Err(self.unsupported(body, node.kind, SourceSyntaxRole::FunctionBody));
            }
            block.statements.nodes.clone()
        };
        if let [statement_id] = statements.as_slice()
            && self.node(self.reference(*statement_id))?.kind == SyntaxKind::ReturnStatement
        {
            let statement = self.reference(*statement_id);
            let expression = {
                let node = self.node(statement)?;
                let NodeData::ReturnStatement(return_statement) = &node.data else {
                    return Err(self.unsupported(
                        statement,
                        node.kind,
                        SourceSyntaxRole::ReturnStatement,
                    ));
                };
                if node.kind != SyntaxKind::ReturnStatement
                    || node.flags.0 != 0
                    || node.parent != Some(body.node)
                    || return_statement.flow_node.is_some()
                    || return_statement.facts != 0
                {
                    return Err(self.unsupported(
                        statement,
                        node.kind,
                        SourceSyntaxRole::ReturnStatement,
                    ));
                }
                return_statement
                    .expression
                    .map(|node| self.reference(node))
                    .ok_or_else(|| {
                        self.unsupported(statement, node.kind, SourceSyntaxRole::ReturnStatement)
                    })?
            };
            if self.node(expression)?.parent != Some(statement.node) {
                let kind = self.node(expression)?.kind;
                return Err(self.unsupported(expression, kind, SourceSyntaxRole::ReturnStatement));
            }
            return Ok(PlannedFunctionBody::Return {
                statement,
                expression: self.plan_expression(expression)?,
            });
        }
        if !statements.is_empty() {
            return self.plan_function_statements(callable);
        }
        if !self.function_empty_body_return_supported(callable.return_type)? {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::FunctionBody(body)),
            ));
        }
        Ok(PlannedFunctionBody::Empty)
    }

    fn plan_function_statements(
        &mut self,
        callable: &SourceCallablePlan,
    ) -> Result<PlannedFunctionBody, SourceCheckError> {
        let Some((store, _)) = self.semantic else {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::FunctionBody(
                    callable.body,
                )),
            ));
        };
        match plan_source_linear_function_statements_syntax(self.arena, self.bound, store, callable)
        {
            Ok(syntax) => {
                let planned = self.finish_linear_function_statements(callable, syntax)?;
                return Ok(PlannedFunctionBody::Linear(Box::new(planned)));
            }
            Err(SourceFunctionStatementsError::Unsupported(_)) => {}
            Err(error) => return Err(Self::function_statements_plan_error(callable, error)),
        }
        match plan_source_function_statements_syntax(self.arena, self.bound, store, callable) {
            Ok(syntax) => {
                let planned = self.finish_function_statements(callable, syntax)?;
                Ok(PlannedFunctionBody::Statements(Box::new(planned)))
            }
            Err(SourceFunctionStatementsError::Unsupported(_)) => {
                let syntax = plan_source_joined_function_statements_syntax(
                    self.arena, self.bound, store, callable,
                )
                .map_err(|error| Self::joined_function_statements_plan_error(callable, error))?;
                let planned = self.finish_joined_function_statements(callable, syntax)?;
                Ok(PlannedFunctionBody::JoinedStatements(Box::new(planned)))
            }
            Err(error) => Err(Self::function_statements_plan_error(callable, error)),
        }
    }

    fn finish_linear_function_statements(
        &mut self,
        callable: &SourceCallablePlan,
        syntax: SourceLinearFunctionStatementsSyntax,
    ) -> Result<PlannedLinearFunctionStatements, SourceCheckError> {
        let SourceLinearFunctionStatementsSyntax {
            body,
            locals: local_syntax,
            return_statement,
            return_expression,
        } = syntax;
        if body != callable.body {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(callable.body),
            ));
        }
        if return_expression.is_none()
            && !self.function_empty_body_return_supported(callable.return_type)?
        {
            return Err(Self::unsupported_function_body(callable));
        }

        let mut locals = Vec::with_capacity(local_syntax.len());
        for local in local_syntax {
            locals.push(self.finish_local_declaration(local)?);
        }
        let return_expression = return_expression
            .map(|expression| self.plan_expression(expression))
            .transpose()?;
        let points = locals
            .iter()
            .map(|local| local.name)
            .chain(return_statement)
            .collect::<Vec<_>>();
        let assignments = locals
            .iter()
            .map(|local| SourceFlowAssignment {
                declaration: local.declaration,
                symbol: local.symbol,
            })
            .collect::<Vec<_>>();
        let flow = SourceFlowPlan::preflight(
            self.bound,
            callable.declaration,
            None,
            points,
            [],
            assignments,
        )
        .map_err(|error| Self::source_flow_plan_error(callable, error))?;

        Ok(PlannedLinearFunctionStatements {
            locals,
            return_statement,
            return_expression,
            flow,
        })
    }

    fn finish_function_statements(
        &mut self,
        callable: &SourceCallablePlan,
        syntax: SourceFunctionStatementsSyntax,
    ) -> Result<PlannedFunctionStatements, SourceCheckError> {
        let SourceFunctionStatementsSyntax {
            body,
            leading: leading_syntax,
            final_if,
        } = syntax;
        if body != callable.body {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(callable.body),
            ));
        }

        let mut leading = Vec::with_capacity(leading_syntax.len());
        for local in leading_syntax {
            leading.push(self.finish_local_declaration(local)?);
        }

        let condition = self.finish_source_condition(
            callable,
            final_if.condition,
            final_if.condition_identifier,
            final_if.typeof_condition,
        )?;

        let then_branch = self.finish_return_branch(final_if.then_branch)?;
        let else_branch = self.finish_return_branch(final_if.else_branch)?;

        let points = leading
            .iter()
            .map(|local| local.name)
            .chain(std::iter::once(condition.flow_point()))
            .chain(then_branch.locals.iter().map(|local| local.name))
            .chain(std::iter::once(then_branch.return_statement))
            .chain(else_branch.locals.iter().map(|local| local.name))
            .chain(std::iter::once(else_branch.return_statement))
            .collect::<Vec<_>>();
        let assignments = leading
            .iter()
            .chain(&then_branch.locals)
            .chain(&else_branch.locals)
            .map(|local| SourceFlowAssignment {
                declaration: local.declaration,
                symbol: local.symbol,
            })
            .collect::<Vec<_>>();
        let flow = SourceFlowPlan::preflight(
            self.bound,
            callable.declaration,
            None,
            points,
            [condition.flow_condition()],
            assignments,
        )
        .map_err(|error| Self::source_flow_plan_error(callable, error))?;

        Ok(PlannedFunctionStatements {
            leading,
            condition,
            then_branch,
            else_branch,
            flow,
        })
    }

    fn finish_source_condition(
        &mut self,
        callable: &SourceCallablePlan,
        expression: NodeRef,
        identifier: NodeRef,
        typeof_syntax: Option<SourceTypeofConditionSyntax>,
    ) -> Result<PlannedSourceCondition, SourceCheckError> {
        let Some(typeof_syntax) = typeof_syntax else {
            let expression = self.plan_expression(expression)?;
            let symbol = match &expression.unparenthesized().kind {
                PlannedExpressionKind::Identifier(read)
                    if expression.unparenthesized().node == identifier
                        && read.kind == PlannedIdentifierReadKind::Variable =>
                {
                    read.value_symbol
                }
                _ => return Err(Self::unsupported_function_body(callable)),
            };
            return Ok(PlannedSourceCondition::Truthiness { expression, symbol });
        };

        if typeof_syntax.identifier != identifier
            || expression == identifier
            || expression == typeof_syntax.type_of_expression
        {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(callable.declaration),
            ));
        }
        let operator_text = match typeof_syntax.comparison {
            SourceTypeofComparison::Equal => "===",
            SourceTypeofComparison::NotEqual => "!==",
        };
        if !self.source_spelling_matches(typeof_syntax.operator, operator_text) {
            return Err(SourceCheckError::LogicalOperator(typeof_syntax.operator));
        }

        let identifier = self.plan_expression(identifier)?;
        let symbol = match &identifier.kind {
            PlannedExpressionKind::Identifier(read)
                if read.kind == PlannedIdentifierReadKind::Variable =>
            {
                read.value_symbol
            }
            _ => return Err(Self::unsupported_function_body(callable)),
        };
        let literal = self.plan_expression(typeof_syntax.literal)?;
        if !matches!(
            &literal.kind,
            PlannedExpressionKind::String(value) if value == source_typeof_tag_text(typeof_syntax.tag)
        ) {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(callable.declaration),
            ));
        }

        let Some((store, _)) = self.semantic else {
            return Err(Self::unsupported_function_body(callable));
        };
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?;
        preflight_source_expression_cache(
            store,
            typeof_syntax.type_of_expression,
            bootstrap.typeof_type,
        )?;
        preflight_source_expression_cache(store, expression, bootstrap.boolean_type)?;

        Ok(PlannedSourceCondition::Typeof(Box::new(
            PlannedTypeofCondition {
                expression,
                type_of_expression: typeof_syntax.type_of_expression,
                identifier,
                literal,
                tag: typeof_syntax.tag,
                comparison: typeof_syntax.comparison,
                type_of_on_left: typeof_syntax.type_of_on_left,
                symbol,
            },
        )))
    }

    fn unsupported_function_body(callable: &SourceCallablePlan) -> SourceCheckError {
        SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
            SourceFunctionUnsupported::FunctionBody(callable.body),
        ))
    }

    fn finish_return_branch(
        &mut self,
        syntax: SourceReturnBranchSyntax,
    ) -> Result<PlannedReturnBranch, SourceCheckError> {
        let branch_prior = self.prior_variables.clone();
        let branch_readable = self.readable_variables.clone();
        let result = (|| {
            let mut locals = Vec::with_capacity(syntax.locals.len());
            for local in syntax.locals {
                locals.push(self.finish_local_declaration(local)?);
            }
            Ok(PlannedReturnBranch {
                locals,
                return_statement: syntax.return_statement,
                return_expression: self.plan_expression(syntax.return_expression)?,
            })
        })();
        self.prior_variables = branch_prior;
        self.readable_variables = branch_readable;
        result
    }

    fn finish_joined_function_statements(
        &mut self,
        callable: &SourceCallablePlan,
        syntax: SourceJoinedFunctionStatementsSyntax,
    ) -> Result<PlannedJoinedFunctionStatements, SourceCheckError> {
        let SourceJoinedFunctionStatementsSyntax {
            body,
            leading: leading_syntax,
            joined_if,
            trailing: trailing_syntax,
            return_statement,
            return_expression,
        } = syntax;
        if body != callable.body {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(callable.body),
            ));
        }

        let mut leading = Vec::with_capacity(leading_syntax.len());
        for local in leading_syntax {
            leading.push(self.finish_local_declaration(local)?);
        }

        let condition = self.finish_source_condition(
            callable,
            joined_if.condition,
            joined_if.condition_identifier,
            joined_if.typeof_condition,
        )?;

        let then_branch = self.finish_fallthrough_branch(joined_if.then_branch)?;
        let else_branch = self.finish_fallthrough_branch(joined_if.else_branch)?;

        let mut trailing = Vec::with_capacity(trailing_syntax.len());
        for local in trailing_syntax {
            trailing.push(self.finish_local_declaration(local)?);
        }
        let return_expression = self.plan_expression(return_expression)?;

        let points = leading
            .iter()
            .map(|local| local.name)
            .chain(std::iter::once(condition.flow_point()))
            .chain(then_branch.locals.iter().map(|local| local.name))
            .chain(else_branch.locals.iter().map(|local| local.name))
            .chain(trailing.iter().map(|local| local.name))
            .chain(std::iter::once(return_statement))
            .collect::<Vec<_>>();
        let assignments = leading
            .iter()
            .chain(&then_branch.locals)
            .chain(&else_branch.locals)
            .chain(&trailing)
            .map(|local| SourceFlowAssignment {
                declaration: local.declaration,
                symbol: local.symbol,
            })
            .collect::<Vec<_>>();
        let flow = SourceFlowPlan::preflight(
            self.bound,
            callable.declaration,
            None,
            points,
            [condition.flow_condition()],
            assignments,
        )
        .map_err(|error| Self::source_flow_plan_error(callable, error))?;

        Ok(PlannedJoinedFunctionStatements {
            leading,
            condition,
            then_branch,
            else_branch,
            trailing,
            return_statement,
            return_expression,
            flow,
        })
    }

    fn finish_fallthrough_branch(
        &mut self,
        syntax: SourceFallthroughBranchSyntax,
    ) -> Result<PlannedFallthroughBranch, SourceCheckError> {
        let branch_prior = self.prior_variables.clone();
        let branch_readable = self.readable_variables.clone();
        let result = (|| {
            let mut locals = Vec::with_capacity(syntax.locals.len());
            for local in syntax.locals {
                locals.push(self.finish_local_declaration(local)?);
            }
            Ok(PlannedFallthroughBranch { locals })
        })();
        self.prior_variables = branch_prior;
        self.readable_variables = branch_readable;
        result
    }

    fn finish_local_declaration(
        &mut self,
        syntax: SourceLocalDeclarationSyntax,
    ) -> Result<PlannedVariable, SourceCheckError> {
        if let Some(type_node) = syntax.type_node {
            self.plan_type_import_annotation_root(type_node)?;
        }
        let initializer = self.plan_expression(syntax.initializer)?;
        if syntax.type_node.is_none()
            && matches!(&initializer.kind, PlannedExpressionKind::Array(elements) if elements.is_empty())
        {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Variable(VariableUnsupported::InferredEmptyArrayOption(
                    syntax.declaration,
                )),
            ));
        }
        if syntax.type_node.is_none()
            && !syntax.binding.is_const()
            && matches!(
                &initializer.unparenthesized().kind,
                PlannedExpressionKind::Null | PlannedExpressionKind::GlobalUndefined
            )
        {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Variable(
                    VariableUnsupported::InferredMutableNullishOption(syntax.declaration),
                ),
            ));
        }
        if !self.prior_variables.insert(syntax.symbol)
            || !self.readable_variables.insert(syntax.symbol)
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidSymbolShape(syntax.symbol),
            ));
        }
        Ok(PlannedVariable {
            declaration: syntax.declaration,
            name: syntax.name,
            symbol: syntax.symbol,
            binding: syntax.binding,
            type_node: syntax.type_node,
            jsdoc_type: None,
            initializer: PlannedVariableInitializer::Expression(initializer),
        })
    }

    fn plan_arrow_body(
        &mut self,
        source: SourceArrowPlan,
    ) -> Result<PlannedArrow, SourceCheckError> {
        let parameter_initializers =
            self.plan_parameter_initializers_and_enter_scope(&source.callable)?;
        let body = match source.body {
            SourceArrowBodyPlan::EmptyBlock { block } => {
                match self.function_empty_body_return_supported(source.callable.return_type) {
                    Ok(true) => Ok(PlannedArrowBody::Empty),
                    Ok(false) => Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Arrow(block),
                    )),
                    Err(error) => Err(error),
                }
            }
            SourceArrowBodyPlan::ReturnExpression {
                statement,
                expression,
                ..
            } => self
                .plan_expression(expression)
                .map(|expression| PlannedArrowBody::Return {
                    diagnostic_node: statement,
                    expression,
                }),
            SourceArrowBodyPlan::ConciseExpression { expression } => self
                .plan_expression(expression)
                .map(|expression| PlannedArrowBody::Return {
                    diagnostic_node: expression.node,
                    expression,
                }),
        };
        self.leave_callable_parameter_scope(&source.callable)?;
        Ok(PlannedArrow {
            source,
            parameter_initializers,
            body: body?,
        })
    }

    fn function_empty_body_return_supported(
        &self,
        return_type: SourceCallableReturnPlan,
    ) -> Result<bool, SourceCheckError> {
        let Some(mut type_node) = return_type.type_node() else {
            return Ok(true);
        };
        loop {
            let node = self.node(type_node)?;
            if matches!(
                node.kind,
                SyntaxKind::AnyKeyword | SyntaxKind::VoidKeyword | SyntaxKind::UndefinedKeyword
            ) {
                return Ok(true);
            }
            let NodeData::ParenthesizedTypeNode(parenthesized) = &node.data else {
                return Ok(false);
            };
            if node.kind != SyntaxKind::ParenthesizedType {
                return Ok(false);
            }
            let inner = self.reference(parenthesized.type_);
            if self.node(inner)?.parent != Some(type_node.node) {
                return Ok(false);
            }
            type_node = inner;
        }
    }

    fn plan_external_module_marker(&self, statement: NodeRef) -> Result<(), SourceCheckError> {
        let statement_node = self.node(statement)?;
        let NodeData::ExportDeclaration(export) = &statement_node.data else {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MismatchedNodeData {
                    node: statement,
                    kind: statement_node.kind,
                },
            ));
        };
        if statement_node.flags.0 != 0
            || export.attributes.is_some()
            || export.flow_node.is_some()
            || export.is_type_only
            || export.module_specifier.is_some()
            || export.symbol.is_some()
            || export.facts != 0
            || export.modifiers.is_some()
        {
            return Err(self.unsupported(
                statement,
                statement_node.kind,
                SourceSyntaxRole::ExportDeclaration,
            ));
        }

        let clause = export
            .export_clause
            .map(|node| self.reference(node))
            .ok_or_else(|| {
                self.unsupported(
                    statement,
                    statement_node.kind,
                    SourceSyntaxRole::ExportDeclaration,
                )
            })?;
        let clause_node = self.node(clause)?;
        let NodeData::NamedExports(exports) = &clause_node.data else {
            return Err(self.unsupported(clause, clause_node.kind, SourceSyntaxRole::ExportClause));
        };
        if clause_node.kind != SyntaxKind::NamedExports
            || clause_node.flags.0 != 0
            || clause_node.parent != Some(statement.node)
            || exports.elements.range != clause_node.range
            || !exports.elements.nodes.is_empty()
            || exports.elements.has_trailing_comma
            || exports.facts != 0
        {
            return Err(self.unsupported(clause, clause_node.kind, SourceSyntaxRole::ExportClause));
        }
        Ok(())
    }

    fn preplan_ambient_variable_statement(
        &mut self,
        statement: NodeRef,
        is_external_module: bool,
        is_declaration_file: bool,
    ) -> Result<Option<Vec<PlannedAmbientVariable>>, SourceCheckError> {
        let statement_node = self.node(statement)?;
        let NodeData::VariableStatement(variable) = &statement_node.data else {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MismatchedNodeData {
                    node: statement,
                    kind: statement_node.kind,
                },
            ));
        };
        let Some(modifiers) = variable.modifiers.as_ref() else {
            return Ok(None);
        };
        let (export_modifier, declare_modifier) = match modifiers.list.nodes.as_slice() {
            [modifier] => {
                let modifier = self.reference(*modifier);
                match self.node(modifier)?.kind {
                    SyntaxKind::DeclareKeyword => (None, Some(modifier)),
                    SyntaxKind::ExportKeyword if is_declaration_file => (Some(modifier), None),
                    _ => return Ok(None),
                }
            }
            [export, declare] => (
                Some(self.reference(*export)),
                Some(self.reference(*declare)),
            ),
            _ => return Ok(None),
        };
        let modifier = declare_modifier
            .or(export_modifier)
            .expect("ambient variable modifiers contain an export or declare token");
        let modifier_node = self.node(modifier)?;
        if declare_modifier.is_some() && modifier_node.kind != SyntaxKind::DeclareKeyword {
            return Ok(None);
        }
        if let Some(export_modifier) = export_modifier {
            let export_node = self.node(export_modifier)?;
            if export_node.kind != SyntaxKind::ExportKeyword
                || !matches!(export_node.data, NodeData::Token(_))
                || export_node.flags.0 != 0
                || export_node.parent != Some(statement.node)
                || export_node.range.start != statement_node.range.start
                || declare_modifier
                    .is_some_and(|_| export_node.range.end > modifier_node.range.start)
                || !self.source_spelling_matches(export_modifier, "export")
            {
                return Err(self.unsupported(
                    export_modifier,
                    export_node.kind,
                    SourceSyntaxRole::VariableModifier,
                ));
            }
            if !is_external_module {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::MissingExternalModuleFact {
                        node: export_modifier,
                        role: SourceSyntaxRole::VariableModifier,
                    },
                ));
            }
        }
        let declaration_list = self.reference(variable.declaration_list);
        let declaration_start = self.node(declaration_list)?.range.start.get();
        if statement_node.flags.0 != 0
            || variable.flow_node.is_some()
            || variable.facts != 0
            || modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
            || modifiers.list.range.start != statement_node.range.start
            || modifiers.list.range.end.get() >= declaration_start
            || !matches!(modifier_node.data, NodeData::Token(_))
            || modifier_node.flags.0 != 0
            || modifier_node.parent != Some(statement.node)
            || (export_modifier.is_none()
                && modifier_node.range.start != statement_node.range.start)
            || modifier_node.range.end.get() >= declaration_start
            || (declare_modifier.is_none()
                && modifier_node.range.start != statement_node.range.start)
            || (export_modifier.is_none()
                && modifier_node.range.end.get() >= modifiers.list.range.end.get())
            || !self.source_spelling_matches(
                modifier,
                if declare_modifier.is_some() {
                    "declare"
                } else {
                    "export"
                },
            )
        {
            return Err(self.unsupported(
                modifier,
                modifier_node.kind,
                SourceSyntaxRole::VariableModifier,
            ));
        }

        let (
            list_kind,
            list_parent,
            list_flags,
            list_range,
            declarations,
            declaration_range,
            trailing_comma,
            facts,
        ) = {
            let list_node = self.node(declaration_list)?;
            let NodeData::VariableDeclarationList(list_data) = &list_node.data else {
                return Err(self.unsupported(
                    declaration_list,
                    list_node.kind,
                    SourceSyntaxRole::VariableDeclarationList,
                ));
            };
            (
                list_node.kind,
                list_node.parent,
                list_node.flags.0,
                list_node.range,
                list_data.declarations.nodes.clone(),
                list_data.declarations.range,
                list_data.declarations.has_trailing_comma,
                list_data.facts,
            )
        };
        if list_kind != SyntaxKind::VariableDeclarationList
            || list_parent != Some(statement.node)
            || !matches!(list_flags, 0 | NODE_FLAG_LET | NODE_FLAG_CONST)
            || declaration_range != list_range
            || trailing_comma
            || facts != 0
        {
            return Err(self.unsupported(
                declaration_list,
                list_kind,
                SourceSyntaxRole::VariableDeclarationList,
            ));
        }
        if declarations.is_empty() {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::EmptyVariableDeclarationList(declaration_list),
            ));
        }
        let binding = match list_flags {
            0 => VariableBindingKind::Var,
            NODE_FLAG_LET => VariableBindingKind::Let,
            NODE_FLAG_CONST => VariableBindingKind::Const,
            _ => unreachable!("the ambient declaration-list gate accepted one binding kind"),
        };

        let mut variables = Vec::with_capacity(declarations.len());
        for declaration in declarations {
            variables.push(self.plan_ambient_variable_declaration(
                declaration_list,
                self.reference(declaration),
                binding,
                export_modifier.is_some(),
            )?);
        }
        Ok(Some(variables))
    }

    fn plan_ambient_variable_declaration(
        &mut self,
        list: NodeRef,
        declaration: NodeRef,
        binding: VariableBindingKind,
        exported: bool,
    ) -> Result<PlannedAmbientVariable, SourceCheckError> {
        let (
            declaration_kind,
            declaration_parent,
            declaration_flags,
            name_id,
            type_id,
            initializer_id,
            definite,
            local_symbol,
            symbol,
            facts,
        ) = {
            let declaration_node = self.node(declaration)?;
            let NodeData::VariableDeclaration(variable) = &declaration_node.data else {
                return Err(self.unsupported(
                    declaration,
                    declaration_node.kind,
                    SourceSyntaxRole::VariableDeclaration,
                ));
            };
            (
                declaration_node.kind,
                declaration_node.parent,
                declaration_node.flags.0,
                variable.name,
                variable.type_,
                variable.initializer,
                variable.exclamation_token.is_some(),
                variable.local_symbol.is_some(),
                variable.symbol.is_some(),
                variable.facts,
            )
        };
        if declaration_kind != SyntaxKind::VariableDeclaration
            || declaration_parent != Some(list.node)
            || declaration_flags != 0
            || definite
            || local_symbol
            || symbol
            || facts != 0
        {
            return Err(self.unsupported(
                declaration,
                declaration_kind,
                SourceSyntaxRole::VariableDeclaration,
            ));
        }

        let name = self.reference(name_id);
        let name_node = self.node(name)?;
        let NodeData::Identifier(identifier) = &name_node.data else {
            return Err(self.unsupported(name, name_node.kind, SourceSyntaxRole::VariableName));
        };
        if name_node.kind != SyntaxKind::Identifier
            || name_node.flags.0 != 0
            || name_node.parent != Some(declaration.node)
            || identifier.flow_node.is_some()
        {
            return Err(self.unsupported(name, name_node.kind, SourceSyntaxRole::VariableName));
        }
        let name_text = identifier.text.clone();
        let Some((store, _)) = self.semantic else {
            return Err(self.unsupported(
                declaration,
                declaration_kind,
                SourceSyntaxRole::VariableDeclaration,
            ));
        };
        let variable_symbol = plan_top_level_variable(
            self.bound,
            store,
            declaration,
            name,
            &name_text,
            binding,
            exported,
        )
        .map_err(Self::variable_plan_error)?;

        if let Some(initializer) = initializer_id.map(|node| self.reference(node)) {
            let initializer_node = self.node(initializer)?;
            if initializer_node.parent != Some(declaration.node) {
                return Err(self.unsupported(
                    initializer,
                    initializer_node.kind,
                    SourceSyntaxRole::VariableInitializer,
                ));
            }
            return Err(self.unsupported(
                initializer,
                initializer_node.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
        let type_node =
            type_id
                .map(|node| self.reference(node))
                .ok_or(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::MissingVariableType(declaration),
                ))?;
        if self.node(type_node)?.parent != Some(declaration.node) {
            let kind = self.node(type_node)?.kind;
            return Err(self.unsupported(type_node, kind, SourceSyntaxRole::VariableType));
        }
        self.plan_type_import_annotation_root(type_node)?;

        if !self.prior_variables.insert(variable_symbol)
            || !self.readable_variables.insert(variable_symbol)
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidSymbolShape(variable_symbol),
            ));
        }
        if !binding.is_const() && !self.assignable_ambient_variables.insert(variable_symbol) {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidSymbolShape(variable_symbol),
            ));
        }
        Ok(PlannedAmbientVariable {
            symbol: variable_symbol,
            binding,
            type_node,
        })
    }

    fn validate_variable_modifiers(
        &self,
        statement: NodeRef,
        statement_range: TextRange,
        declaration_list: NodeId,
        modifiers: Option<&ModifierList>,
    ) -> Result<Option<NodeRef>, SourceCheckError> {
        let Some(modifiers) = modifiers else {
            return Ok(None);
        };
        let [modifier_id] = modifiers.list.nodes.as_slice() else {
            return Err(self.unsupported(
                statement,
                SyntaxKind::VariableStatement,
                SourceSyntaxRole::VariableStatement,
            ));
        };
        let modifier = self.reference(*modifier_id);
        let modifier_node = self.node(modifier)?;
        let declaration_start = self
            .node(self.reference(declaration_list))?
            .range
            .start
            .get();
        if modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
            || modifiers.list.range.start != statement_range.start
            || modifiers.list.range.end.get() >= declaration_start
            || modifier_node.kind != SyntaxKind::ExportKeyword
            || !matches!(modifier_node.data, NodeData::Token(_))
            || modifier_node.flags.0 != 0
            || modifier_node.parent != Some(statement.node)
            || modifier_node.range.start != statement_range.start
            || modifier_node.range.end.get() >= modifiers.list.range.end.get()
            || !self.source_spelling_matches(modifier, "export")
        {
            return Err(self.unsupported(
                modifier,
                modifier_node.kind,
                SourceSyntaxRole::VariableModifier,
            ));
        }
        Ok(Some(modifier))
    }

    fn validate_complete_tree(&self) -> Result<(), SourceCheckError> {
        if !self.store_source_shape_matches() {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::BoundSourceMismatch {
                    expected: self.bound.source_file(),
                    actual: self.source,
                },
            ));
        }
        let source_range = self.node(self.source.node_ref())?.range;
        let mut seen = HashSet::new();
        let mut pending = vec![(self.source.node_ref().node, None, None)];
        while let Some((node_id, expected_parent, parent_range)) = pending.pop() {
            let reference = self.reference(node_id);
            if !seen.insert(node_id) {
                return Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::RepeatedNode(reference),
                ));
            }
            let node = self.node(reference)?;
            if node.parent != expected_parent {
                return Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::InvalidParent {
                        node: reference,
                        expected: expected_parent,
                        actual: node.parent,
                    },
                ));
            }
            if node.flags.0 & NODE_FLAG_JSDOC != 0 {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::JsDoc(reference),
                ));
            }
            if !valid_range(
                node.range,
                parent_range,
                source_range,
                self.arena.source_text(),
            ) {
                return Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::InvalidRange {
                        node: reference,
                        range: node.range,
                        parent: parent_range,
                    },
                ));
            }
            let mut children = Vec::new();
            node.for_each_child(|child| children.push(child));
            pending.extend(
                children
                    .into_iter()
                    .rev()
                    .map(|child| (child, Some(node_id), Some(node.range))),
            );
        }
        Ok(())
    }

    fn store_source_shape_matches(&self) -> bool {
        self.source.node_ref() == self.bound.source_file()
            && self
                .source
                .node_ref()
                .is_for(self.arena.id(), self.bound.file_id())
    }

    fn plan_variable_statement(
        &mut self,
        statement: NodeRef,
        declaration_list: NodeId,
        exported: bool,
    ) -> Result<PlannedVariableStatement, SourceCheckError> {
        let list = self.reference(declaration_list);
        let (kind, parent, flags, range, declarations, declaration_range, trailing_comma, facts) = {
            let list_node = self.node(list)?;
            let NodeData::VariableDeclarationList(list_data) = &list_node.data else {
                return Err(self.unsupported(
                    list,
                    list_node.kind,
                    SourceSyntaxRole::VariableDeclarationList,
                ));
            };
            (
                list_node.kind,
                list_node.parent,
                list_node.flags.0,
                list_node.range,
                list_data.declarations.nodes.clone(),
                list_data.declarations.range,
                list_data.declarations.has_trailing_comma,
                list_data.facts,
            )
        };
        if kind != SyntaxKind::VariableDeclarationList
            || parent != Some(statement.node)
            || !matches!(flags, 0 | NODE_FLAG_LET | NODE_FLAG_CONST)
            || declaration_range != range
            || trailing_comma
            || facts != 0
        {
            return Err(self.unsupported(list, kind, SourceSyntaxRole::VariableDeclarationList));
        }
        if declarations.is_empty() {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::EmptyVariableDeclarationList(list),
            ));
        }
        let binding = match flags {
            0 => VariableBindingKind::Var,
            NODE_FLAG_LET => VariableBindingKind::Let,
            NODE_FLAG_CONST => VariableBindingKind::Const,
            _ => unreachable!("the declaration-list flag gate accepted one exact binding kind"),
        };

        for declaration in &declarations {
            let declaration = self.reference(*declaration);
            let declaration_node = self.node(declaration)?;
            let NodeData::VariableDeclaration(variable) = &declaration_node.data else {
                continue;
            };
            let Some(initializer) = variable.initializer.map(|node| self.reference(node)) else {
                continue;
            };
            if self.node(initializer)?.kind != SyntaxKind::ArrowFunction {
                continue;
            }
            let Some((store, host)) = self.semantic else {
                return Err(self.unsupported(
                    initializer,
                    SyntaxKind::ArrowFunction,
                    SourceSyntaxRole::VariableInitializer,
                ));
            };
            let contextual = variable.type_.is_some();
            let (variable_symbol, planned) = if contextual {
                let arrow =
                    plan_contextual_source_arrow(store, host, declaration, self.array_targets)
                        .map_err(Self::contextual_arrow_plan_error)?;
                preflight_contextual_source_publication(store, &arrow, None)?;
                (
                    arrow.variable_symbol,
                    PlannedVariableStatement::ContextualArrow(Box::new(arrow)),
                )
            } else {
                let arrow = plan_source_arrow(store, host, declaration, self.array_targets)
                    .map_err(Self::arrow_plan_error)?;
                (
                    arrow.variable_symbol,
                    PlannedVariableStatement::Arrow(Box::new(arrow)),
                )
            };
            if !self.prior_variables.insert(variable_symbol)
                || !self.readable_variables.insert(variable_symbol)
            {
                return Err(SourceCheckError::Variable(
                    VariableInvariant::InvalidSymbolShape(variable_symbol),
                ));
            }
            return Ok(planned);
        }

        let mut variables = Vec::with_capacity(declarations.len());
        for declaration in declarations {
            variables.push(self.plan_variable_declaration(
                list,
                self.reference(declaration),
                binding,
                exported,
            )?);
        }
        Ok(PlannedVariableStatement::Variables(variables))
    }

    fn plan_variable_declaration(
        &mut self,
        list: NodeRef,
        declaration: NodeRef,
        binding: VariableBindingKind,
        exported: bool,
    ) -> Result<PlannedVariable, SourceCheckError> {
        let (
            declaration_kind,
            declaration_parent,
            declaration_flags,
            name_id,
            type_id,
            initializer_id,
            definite,
            local_symbol,
            symbol,
            facts,
        ) = {
            let declaration_node = self.node(declaration)?;
            let NodeData::VariableDeclaration(variable) = &declaration_node.data else {
                return Err(self.unsupported(
                    declaration,
                    declaration_node.kind,
                    SourceSyntaxRole::VariableDeclaration,
                ));
            };
            (
                declaration_node.kind,
                declaration_node.parent,
                declaration_node.flags.0,
                variable.name,
                variable.type_,
                variable.initializer,
                variable.exclamation_token.is_some(),
                variable.local_symbol.is_some(),
                variable.symbol.is_some(),
                variable.facts,
            )
        };
        if declaration_kind != SyntaxKind::VariableDeclaration
            || declaration_parent != Some(list.node)
            || declaration_flags != 0
            || definite
            || local_symbol
            || symbol
            || facts != 0
        {
            return Err(self.unsupported(
                declaration,
                declaration_kind,
                SourceSyntaxRole::VariableDeclaration,
            ));
        }

        let name = self.reference(name_id);
        let name_node = self.node(name)?;
        let NodeData::Identifier(identifier) = &name_node.data else {
            return Err(self.unsupported(name, name_node.kind, SourceSyntaxRole::VariableName));
        };
        if name_node.kind != SyntaxKind::Identifier
            || name_node.flags.0 != 0
            || name_node.parent != Some(declaration.node)
            || identifier.flow_node.is_some()
        {
            return Err(self.unsupported(name, name_node.kind, SourceSyntaxRole::VariableName));
        }
        let name_text = identifier.text.clone();
        let Some((store, _)) = self.semantic else {
            return Err(self.unsupported(
                declaration,
                declaration_kind,
                SourceSyntaxRole::VariableDeclaration,
            ));
        };
        let variable_symbol = plan_top_level_variable(
            self.bound,
            store,
            declaration,
            name,
            &name_text,
            binding,
            exported,
        )
        .map_err(Self::variable_plan_error)?;

        let type_node = type_id.map(|node| self.reference(node));
        if let Some(type_node) = type_node
            && self.node(type_node)?.parent != Some(declaration.node)
        {
            let kind = self.node(type_node)?.kind;
            return Err(self.unsupported(type_node, kind, SourceSyntaxRole::VariableType));
        }
        if let Some(type_node) = type_node {
            self.plan_type_import_annotation_root(type_node)?;
        }

        let initializer = match initializer_id.map(|node| self.reference(node)) {
            Some(initializer) => {
                if self.node(initializer)?.parent != Some(declaration.node) {
                    let kind = self.node(initializer)?.kind;
                    return Err(self.unsupported(
                        initializer,
                        kind,
                        SourceSyntaxRole::VariableInitializer,
                    ));
                }
                if matches!(
                    self.node(initializer)?.kind,
                    SyntaxKind::JsxElement
                        | SyntaxKind::JsxSelfClosingElement
                        | SyntaxKind::JsxFragment
                ) {
                    let Some((store, host)) = self.semantic else {
                        return Err(self.unsupported(
                            initializer,
                            self.node(initializer)?.kind,
                            SourceSyntaxRole::VariableInitializer,
                        ));
                    };
                    store.preflight_jsx_element(host, initializer)?;
                    PlannedVariableInitializer::Jsx(initializer)
                } else {
                    let initializer = self.plan_expression(initializer)?;
                    if type_node.is_none()
                        && !exported
                        && matches!(&initializer.kind, PlannedExpressionKind::Array(elements) if elements.is_empty())
                    {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Variable(
                                VariableUnsupported::InferredEmptyArrayOption(declaration),
                            ),
                        ));
                    }
                    if type_node.is_none()
                        && !exported
                        && !binding.is_const()
                        && matches!(
                            &initializer.unparenthesized().kind,
                            PlannedExpressionKind::Null | PlannedExpressionKind::GlobalUndefined
                        )
                    {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Variable(
                                VariableUnsupported::InferredMutableNullishOption(declaration),
                            ),
                        ));
                    }
                    PlannedVariableInitializer::Expression(initializer)
                }
            }
            None if type_node.is_some() && !binding.is_const() && !exported => {
                PlannedVariableInitializer::AbsentAnnotated
            }
            None if self.javascript_jsdoc.is_some() && !binding.is_const() && !exported => {
                PlannedVariableInitializer::AbsentJavaScript
            }
            None => {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::MissingVariableInitializer(declaration),
                ));
            }
        };
        if !self.prior_variables.insert(variable_symbol) {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidSymbolShape(variable_symbol),
            ));
        }
        if !self.readable_variables.insert(variable_symbol) {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidSymbolShape(variable_symbol),
            ));
        }
        if matches!(&initializer, PlannedVariableInitializer::AbsentAnnotated)
            && !self
                .assignable_uninitialized_variables
                .insert(variable_symbol)
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidSymbolShape(variable_symbol),
            ));
        }
        if !binding.is_const()
            && matches!(
                &initializer,
                PlannedVariableInitializer::Expression(_) | PlannedVariableInitializer::Jsx(_)
            )
            && self.javascript_jsdoc.is_none()
            && !self.assignable_mutable_variables.insert(variable_symbol)
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidSymbolShape(variable_symbol),
            ));
        }
        Ok(PlannedVariable {
            declaration,
            name,
            symbol: variable_symbol,
            binding,
            type_node,
            jsdoc_type: self
                .javascript_jsdoc
                .as_ref()
                .and_then(|plan| plan.declaration(declaration))
                .and_then(|declaration| declaration.type_())
                .cloned(),
            initializer,
        })
    }

    fn is_top_level_execution_expression(
        &self,
        expression: NodeRef,
    ) -> Result<bool, SourceCheckError> {
        let mut current = expression;
        loop {
            let node = self.node(current)?;
            match node.kind {
                SyntaxKind::FunctionDeclaration | SyntaxKind::ArrowFunction => return Ok(false),
                SyntaxKind::SourceFile => return Ok(current == self.source.node_ref()),
                _ => {
                    current = node.parent.map(|parent| self.reference(parent)).ok_or(
                        SourceCheckError::Provenance(SourceCheckProvenanceError::InvalidParent {
                            node: current,
                            expected: Some(self.source.node_ref().node),
                            actual: None,
                        }),
                    )?;
                }
            }
        }
    }

    fn plan_expression(
        &mut self,
        expression: NodeRef,
    ) -> Result<PlannedExpression, SourceCheckError> {
        let kind = self.node(expression)?.kind;
        match kind {
            SyntaxKind::NullKeyword
                if matches!(self.node(expression)?.data, NodeData::KeywordExpression(_)) =>
            {
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::Null,
                ))
            }
            SyntaxKind::TrueKeyword
                if matches!(self.node(expression)?.data, NodeData::KeywordExpression(_)) =>
            {
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::Boolean(true),
                ))
            }
            SyntaxKind::FalseKeyword
                if matches!(self.node(expression)?.data, NodeData::KeywordExpression(_)) =>
            {
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::Boolean(false),
                ))
            }
            SyntaxKind::Identifier => {
                let node = self.node(expression)?;
                let NodeData::Identifier(identifier) = &node.data else {
                    return Err(self.unsupported(
                        expression,
                        node.kind,
                        SourceSyntaxRole::VariableInitializer,
                    ));
                };
                if node.flags.0 != 0 || identifier.flow_node.is_some() {
                    return Err(self.unsupported(
                        expression,
                        node.kind,
                        SourceSyntaxRole::VariableInitializer,
                    ));
                }
                let name = identifier.text.clone();
                if name == "undefined" && self.is_global_undefined() {
                    return Ok(PlannedExpression::new(
                        expression,
                        PlannedExpressionKind::GlobalUndefined,
                    ));
                }
                let Some((store, host)) = self.semantic else {
                    return Err(self.unsupported(
                        expression,
                        node.kind,
                        SourceSyntaxRole::VariableInitializer,
                    ));
                };
                let variable_read = plan_identifier_read(
                    self.arena,
                    self.bound,
                    store,
                    host,
                    &self.prior_variables,
                    &self.readable_variables,
                    expression,
                    &name,
                );
                let kind = match variable_read {
                    Ok(read) => {
                        PlannedExpressionKind::Identifier(PlannedIdentifierRead::variable(read))
                    }
                    Err(VariablePlanError::Unsupported(
                        VariableUnsupported::UnresolvedIdentifier(node),
                    )) if node == expression => {
                        let bootstrap =
                            store
                                .intrinsic_bootstrap()
                                .ok_or(SourceCheckError::LiteralCache(
                                    SourceLiteralCacheError::BootstrapUninitialized,
                                ))?;
                        preflight_source_expression_cache(store, expression, bootstrap.error_type)?;
                        if store
                            .symbol_node_links(expression)
                            .and_then(|links| links.resolved_symbol)
                            .is_some_and(|cached| cached != bootstrap.unknown_symbol)
                        {
                            return Err(SourceCheckError::Variable(
                                VariableInvariant::InvalidSymbolNodeCache {
                                    node: expression,
                                    cached: store
                                        .symbol_node_links(expression)
                                        .and_then(|links| links.resolved_symbol),
                                    expected: bootstrap.unknown_symbol,
                                },
                            ));
                        }
                        PlannedExpressionKind::Identifier(PlannedIdentifierRead::unresolved(
                            bootstrap.unknown_symbol,
                        ))
                    }
                    Err(VariablePlanError::Unsupported(
                        VariableUnsupported::NonVariableSymbol { flags, .. },
                    )) if flags == ts_binder::SymbolFlags::FUNCTION => {
                        PlannedExpressionKind::Identifier(PlannedIdentifierRead::function(
                            plan_function_identifier_read(
                                self.arena,
                                self.bound,
                                store,
                                host,
                                &self.hoisted_functions,
                                expression,
                                &name,
                            )
                            .map_err(Self::function_plan_error)?,
                        ))
                    }
                    Err(
                        error @ VariablePlanError::Unsupported(VariableUnsupported::AliasSymbol {
                            symbol,
                            ..
                        }),
                    ) => {
                        if let Some(binding) = self.value_import_bindings.get(&symbol) {
                            let import_read = plan_source_import_identifier_read(
                                self.arena, self.bound, store, binding, expression, &name, symbol,
                            )
                            .map_err(|error| Self::import_plan_error(expression, &error))?;
                            self.import_reads.push(import_read);
                            PlannedExpressionKind::Identifier(PlannedIdentifierRead::import(
                                import_read,
                            ))
                        } else if self.type_import_bindings.contains_key(&symbol) {
                            if !self.is_direct_top_level_variable_initializer(expression)? {
                                return Err(SourceCheckError::Unsupported(
                                    UnsupportedSourceSyntax::Import(expression),
                                ));
                            }
                            let read = PlannedSourceTypeImportValueUse {
                                node: expression,
                                alias_symbol: symbol,
                                name,
                            };
                            self.type_import_value_uses.push(read.clone());
                            PlannedExpressionKind::TypeImportValueUse(read)
                        } else {
                            return Err(Self::variable_plan_error(error));
                        }
                    }
                    Err(error) => return Err(Self::variable_plan_error(error)),
                };
                let resolved_symbol = match &kind {
                    PlannedExpressionKind::Identifier(read) => read.resolved_symbol,
                    PlannedExpressionKind::TypeImportValueUse(read) => read.alias_symbol,
                    _ => unreachable!("an identifier syntax plans one identifier-family read"),
                };
                self.identifier_reads.push((expression, resolved_symbol));
                let used_before_assignment = matches!(
                    &kind,
                    PlannedExpressionKind::Identifier(read)
                        if self.assignable_uninitialized_variables.contains(&read.value_symbol)
                            && !self.assigned_variables.contains(&read.value_symbol)
                ) && self
                    .is_top_level_execution_expression(expression)?;
                Ok(PlannedExpression::new(expression, kind)
                    .with_used_before_assignment(used_before_assignment))
            }
            SyntaxKind::StringLiteral => {
                let value = {
                    let node = self.node(expression)?;
                    let NodeData::StringLiteral(literal) = &node.data else {
                        return Err(self.unsupported(
                            expression,
                            node.kind,
                            SourceSyntaxRole::VariableInitializer,
                        ));
                    };
                    if literal.token_flags.0 != 0 {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::InvalidLiteralFlags(expression),
                        ));
                    }
                    literal.text.clone()
                };
                self.strings.push(value.clone());
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::String(value),
                ))
            }
            SyntaxKind::NoSubstitutionTemplateLiteral => {
                let value = {
                    let node = self.node(expression)?;
                    let NodeData::NoSubstitutionTemplateLiteral(literal) = &node.data else {
                        return Err(self.unsupported(
                            expression,
                            node.kind,
                            SourceSyntaxRole::VariableInitializer,
                        ));
                    };
                    if literal.token_flags.0 != 0 || literal.template_flags.0 != 0 {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::InvalidLiteralFlags(expression),
                        ));
                    }
                    literal.text.clone()
                };
                self.strings.push(value.clone());
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::String(value),
                ))
            }
            SyntaxKind::NumericLiteral => {
                let value = self.plan_numeric_literal(expression)?;
                self.numbers.push(value);
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::Number {
                        value,
                        unary_operand: None,
                    },
                ))
            }
            SyntaxKind::BigIntLiteral => {
                let value = self.plan_bigint_literal(expression)?;
                self.bigints.push(value.clone());
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::BigInt {
                        value,
                        unary_operand: None,
                    },
                ))
            }
            SyntaxKind::ParenthesizedExpression => {
                let inner_id = {
                    let node = self.node(expression)?;
                    let NodeData::ParenthesizedExpression(parenthesized) = &node.data else {
                        return Err(self.unsupported(
                            expression,
                            node.kind,
                            SourceSyntaxRole::VariableInitializer,
                        ));
                    };
                    parenthesized.expression
                };
                let inner = self.reference(inner_id);
                if self.node(inner)?.parent != Some(expression.node) {
                    let kind = self.node(inner)?.kind;
                    return Err(self.unsupported(
                        inner,
                        kind,
                        SourceSyntaxRole::VariableInitializer,
                    ));
                }
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::Parenthesized(Box::new(self.plan_expression(inner)?)),
                ))
            }
            SyntaxKind::BinaryExpression => self.plan_binary(expression),
            SyntaxKind::ConditionalExpression => self.plan_conditional(expression),
            SyntaxKind::PrefixUnaryExpression => self.plan_prefix_unary(expression),
            SyntaxKind::TypeAssertionExpression | SyntaxKind::AsExpression => {
                self.plan_assertion(expression)
            }
            SyntaxKind::ArrayLiteralExpression => self.plan_array_literal(expression),
            SyntaxKind::ObjectLiteralExpression => self.plan_object_literal(expression),
            SyntaxKind::PropertyAccessExpression => {
                let Some((store, _)) = self.semantic else {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Property(expression),
                    ));
                };
                let syntax = plan_direct_source_property_syntax(self.arena, store, expression)
                    .map_err(Self::property_plan_error)?;
                let receiver = self.plan_expression(syntax.receiver())?;
                let property = finish_direct_source_property_plan(&syntax, receiver)
                    .map_err(Self::property_plan_error)?;
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::Property(Box::new(property)),
                ))
            }
            SyntaxKind::ElementAccessExpression => {
                let Some((store, _)) = self.semantic else {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Element(expression),
                    ));
                };
                let syntax = plan_direct_source_element_syntax(self.arena, store, expression)
                    .map_err(|error| Self::element_plan_error(expression, error))?;
                let receiver = self.plan_expression(syntax.receiver())?;
                let index = self.plan_expression(syntax.index())?;
                let element = finish_direct_source_element_plan(syntax, receiver, index)
                    .map_err(|error| Self::element_plan_error(expression, error))?;
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::Element(Box::new(element)),
                ))
            }
            SyntaxKind::CallExpression => {
                let Some((store, _)) = self.semantic else {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Call(expression),
                    ));
                };
                let syntax = plan_direct_source_call_syntax(self.arena, store, expression)?;
                let callee_node = syntax.callee();
                let argument_nodes = syntax.arguments().to_vec();
                self.primitive_binary_position_roots
                    .extend(argument_nodes.iter().copied());
                let callee = match syntax.callee_form() {
                    SourceCallCalleeForm::Identifier => self.plan_expression(callee_node)?,
                    SourceCallCalleeForm::RequiredOwnProperty => {
                        let Some((store, _)) = self.semantic else {
                            return Err(SourceCheckError::Unsupported(
                                UnsupportedSourceSyntax::Property(callee_node),
                            ));
                        };
                        let property_syntax = plan_direct_source_property_call_syntax(
                            self.arena,
                            store,
                            callee_node,
                            expression,
                        )
                        .map_err(Self::property_plan_error)?;
                        if property_syntax.name_node() != syntax.callee_diagnostic_node() {
                            return Err(SourceCheckError::Unsupported(
                                UnsupportedSourceSyntax::Call(expression),
                            ));
                        }
                        let receiver = self.plan_expression(property_syntax.receiver())?;
                        let property =
                            finish_direct_source_property_plan(&property_syntax, receiver)
                                .map_err(Self::property_plan_error)?;
                        PlannedExpression::new(
                            callee_node,
                            PlannedExpressionKind::Property(Box::new(property)),
                        )
                    }
                };
                let arguments = argument_nodes
                    .into_iter()
                    .map(|argument| self.plan_expression(argument))
                    .collect::<Result<Vec<_>, _>>()?;
                let call = finish_direct_source_call_plan(&syntax, callee, arguments)?;
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::Call(Box::new(call)),
                ))
            }
            SyntaxKind::NewExpression => {
                if !self.is_direct_top_level_variable_initializer(expression)? {
                    return Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                        expression,
                    )));
                }
                let Some((store, host)) = self.semantic else {
                    return Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                        expression,
                    )));
                };
                let construction = plan_direct_default_new(
                    self.arena,
                    self.bound,
                    store,
                    host,
                    &self.prior_classes,
                    expression,
                )
                .map_err(|error| Self::new_plan_error(expression, error))?;
                self.default_news.push(construction.clone());
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::New(Box::new(construction)),
                ))
            }
            _ => Err(self.unsupported(expression, kind, SourceSyntaxRole::VariableInitializer)),
        }
    }

    fn plan_conditional(
        &mut self,
        expression: NodeRef,
    ) -> Result<PlannedExpression, SourceCheckError> {
        let mut root = expression;
        while let Some(parent) = self.node(root)?.parent.map(|node| self.reference(node)) {
            let parent_node = self.node(parent)?;
            let NodeData::ConditionalExpression(conditional) = &parent_node.data else {
                break;
            };
            if conditional.when_true != root.node && conditional.when_false != root.node {
                break;
            }
            root = parent;
        }
        if !self.is_direct_top_level_variable_initializer(root)? {
            return Err(self.unsupported(
                expression,
                SyntaxKind::ConditionalExpression,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
        let declaration = self
            .node(root)?
            .parent
            .map(|node| self.reference(node))
            .ok_or_else(|| {
                self.unsupported(
                    expression,
                    SyntaxKind::ConditionalExpression,
                    SourceSyntaxRole::VariableInitializer,
                )
            })?;
        let NodeData::VariableDeclaration(variable) = &self.node(declaration)?.data else {
            return Err(self.unsupported(
                expression,
                SyntaxKind::ConditionalExpression,
                SourceSyntaxRole::VariableInitializer,
            ));
        };
        if variable.type_.is_some() {
            return Err(self.unsupported(
                expression,
                SyntaxKind::ConditionalExpression,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
        let (condition_id, question_id, when_true_id, colon_id, when_false_id) = {
            let record = self.node(expression)?;
            let NodeData::ConditionalExpression(conditional) = &record.data else {
                return Err(self.unsupported(
                    expression,
                    record.kind,
                    SourceSyntaxRole::VariableInitializer,
                ));
            };
            if record.kind != SyntaxKind::ConditionalExpression
                || record.flags.0 != 0
                || conditional.facts != 0
            {
                return Err(self.unsupported(
                    expression,
                    record.kind,
                    SourceSyntaxRole::VariableInitializer,
                ));
            }
            (
                conditional.condition,
                conditional.question_token,
                conditional.when_true,
                conditional.colon_token,
                conditional.when_false,
            )
        };
        let condition = self.reference(condition_id);
        let question = self.reference(question_id);
        let when_true = self.reference(when_true_id);
        let colon = self.reference(colon_id);
        let when_false = self.reference(when_false_id);
        let condition_record = self.node(condition)?;
        let question_record = self.node(question)?;
        let when_true_record = self.node(when_true)?;
        let colon_record = self.node(colon)?;
        let when_false_record = self.node(when_false)?;
        if condition_record.parent != Some(expression.node)
            || question_record.parent != Some(expression.node)
            || when_true_record.parent != Some(expression.node)
            || colon_record.parent != Some(expression.node)
            || when_false_record.parent != Some(expression.node)
            || question_record.kind != SyntaxKind::QuestionToken
            || colon_record.kind != SyntaxKind::ColonToken
            || question_record.flags.0 != 0
            || colon_record.flags.0 != 0
            || !matches!(question_record.data, NodeData::Token(_))
            || !matches!(colon_record.data, NodeData::Token(_))
            || condition_record.range.end > question_record.range.start
            || question_record.range.end > when_true_record.range.start
            || when_true_record.range.end > colon_record.range.start
            || colon_record.range.end > when_false_record.range.start
            || !self.source_spelling_matches(question, "?")
            || !self.source_spelling_matches(colon, ":")
        {
            return Err(self.unsupported(
                expression,
                SyntaxKind::ConditionalExpression,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
        let condition = self.plan_expression(condition)?;
        let condition_target = condition.unparenthesized();
        let PlannedExpressionKind::Identifier(condition_read) = &condition_target.kind else {
            return Err(self.unsupported(
                condition_target.node,
                self.node(condition_target.node)?.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        };
        if !matches!(
            condition_read.kind,
            PlannedIdentifierReadKind::Variable | PlannedIdentifierReadKind::Unresolved
        ) {
            return Err(self.unsupported(
                condition_target.node,
                SyntaxKind::Identifier,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
        let condition_symbol = (condition_read.kind == PlannedIdentifierReadKind::Variable)
            .then_some(condition_read.value_symbol);
        let Some(condition_expectation) = self.conditional_scalar_expectation(&condition)? else {
            return Err(self.unsupported(
                condition_target.node,
                SyntaxKind::Identifier,
                SourceSyntaxRole::VariableInitializer,
            ));
        };
        let when_true = self.plan_expression(when_true)?;
        if !conditional_scalar_operand_plan_is_supported(&when_true)
            || condition_symbol
                .is_some_and(|symbol| planned_expression_reads_symbol(&when_true, symbol))
        {
            return Err(self.unsupported(
                when_true.node,
                self.node(when_true.node)?.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
        let Some(when_true_expectation) = self.conditional_scalar_expectation(&when_true)? else {
            return Err(self.unsupported(
                when_true.node,
                self.node(when_true.node)?.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        };
        if matches!(
            when_true_expectation,
            ConditionalScalarExpectation::Exact {
                family: ConditionalScalarFamily::Boolean,
                ..
            }
        ) {
            return Err(self.unsupported(
                when_true.node,
                self.node(when_true.node)?.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
        let when_false = self.plan_expression(when_false)?;
        if !conditional_scalar_operand_plan_is_supported(&when_false)
            || condition_symbol
                .is_some_and(|symbol| planned_expression_reads_symbol(&when_false, symbol))
        {
            return Err(self.unsupported(
                when_false.node,
                self.node(when_false.node)?.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
        let Some(when_false_expectation) = self.conditional_scalar_expectation(&when_false)? else {
            return Err(self.unsupported(
                when_false.node,
                self.node(when_false.node)?.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        };
        if matches!(
            when_false_expectation,
            ConditionalScalarExpectation::Exact {
                family: ConditionalScalarFamily::Boolean,
                ..
            }
        ) {
            return Err(self.unsupported(
                when_false.node,
                self.node(when_false.node)?.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
        let Some(expected_result) =
            self.conditional_expected_result(when_true_expectation, when_false_expectation)?
        else {
            return Err(self.unsupported(
                expression,
                SyntaxKind::ConditionalExpression,
                SourceSyntaxRole::VariableInitializer,
            ));
        };
        if let Some((store, _)) = self.semantic {
            preflight_source_expression_cache(store, expression, expected_result)?;
            preflight_uncached_conditional_operand_links(store, &condition)?;
            preflight_uncached_conditional_operand_links(store, &when_true)?;
            preflight_uncached_conditional_operand_links(store, &when_false)?;
        }
        Ok(PlannedExpression::new(
            expression,
            PlannedExpressionKind::Conditional(Box::new(ConditionalExpressionPlan {
                node: expression,
                condition,
                condition_expectation,
                when_true,
                when_true_expectation,
                when_false,
                when_false_expectation,
                expected_result,
            })),
        ))
    }

    fn conditional_scalar_expectation(
        &self,
        expression: &PlannedExpression,
    ) -> Result<Option<ConditionalScalarExpectation>, SourceCheckError> {
        let literal = match &expression.kind {
            PlannedExpressionKind::String(_) => Some(ConditionalScalarFamily::String),
            PlannedExpressionKind::Number { .. } => Some(ConditionalScalarFamily::Number),
            PlannedExpressionKind::BigInt { .. } => Some(ConditionalScalarFamily::BigInt),
            PlannedExpressionKind::Boolean(_) => Some(ConditionalScalarFamily::Boolean),
            PlannedExpressionKind::Parenthesized(inner) => {
                return self.conditional_scalar_expectation(inner);
            }
            PlannedExpressionKind::Identifier(read)
                if read.kind == PlannedIdentifierReadKind::Unresolved =>
            {
                return Ok(Some(ConditionalScalarExpectation::Error));
            }
            PlannedExpressionKind::Conditional(conditional) => {
                let Some((store, _)) = self.semantic else {
                    return Ok(None);
                };
                let error_type = store
                    .intrinsic_bootstrap()
                    .map(|bootstrap| bootstrap.error_type)
                    .ok_or(SourceCheckError::LiteralCache(
                        SourceLiteralCacheError::BootstrapUninitialized,
                    ))?;
                return Ok((conditional.expected_result == error_type)
                    .then_some(ConditionalScalarExpectation::Error));
            }
            PlannedExpressionKind::Identifier(read)
                if read.kind == PlannedIdentifierReadKind::Variable =>
            {
                if self.assigned_variables.contains(&read.value_symbol) {
                    return Ok(None);
                }
                let Some((store, _)) = self.semantic else {
                    return Ok(None);
                };
                let declaration = store
                    .symbol(read.value_symbol)
                    .and_then(ts_binder::semantic::Symbol::value_declaration)
                    .ok_or(SourceCheckError::Conditional(expression.node))?;
                let declaration_record = self.node(declaration)?;
                let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
                    return Err(SourceCheckError::Conditional(expression.node));
                };
                if declaration_record.kind != SyntaxKind::VariableDeclaration {
                    return Err(SourceCheckError::Conditional(expression.node));
                }
                let Some(type_node) = variable.type_.map(|node| self.reference(node)) else {
                    return Ok(None);
                };
                let type_record = self.node(type_node)?;
                if type_record.parent != Some(declaration.node) {
                    return Err(SourceCheckError::Conditional(type_node));
                }
                if type_record.flags.0 != 0 {
                    return Ok(None);
                }
                let family = match type_record.kind {
                    SyntaxKind::StringKeyword => ConditionalScalarFamily::String,
                    SyntaxKind::NumberKeyword => ConditionalScalarFamily::Number,
                    SyntaxKind::BigIntKeyword => ConditionalScalarFamily::BigInt,
                    SyntaxKind::BooleanKeyword => ConditionalScalarFamily::Boolean,
                    _ => return Ok(None),
                };
                if !matches!(type_record.data, NodeData::KeywordTypeNode(_)) {
                    return Err(SourceCheckError::Conditional(type_node));
                }
                let bootstrap =
                    store
                        .intrinsic_bootstrap()
                        .ok_or(SourceCheckError::LiteralCache(
                            SourceLiteralCacheError::BootstrapUninitialized,
                        ))?;
                let type_ = match family {
                    ConditionalScalarFamily::String => bootstrap.string_type,
                    ConditionalScalarFamily::Number => bootstrap.number_type,
                    ConditionalScalarFamily::BigInt => bootstrap.bigint_type,
                    ConditionalScalarFamily::Boolean => {
                        let Some(initializer) =
                            variable.initializer.map(|node| self.reference(node))
                        else {
                            return Ok(None);
                        };
                        match self.conditional_boolean_initializer(initializer)? {
                            Some(true) => bootstrap.true_type,
                            Some(false) => bootstrap.false_type,
                            None => return Ok(None),
                        }
                    }
                };
                return Ok(Some(ConditionalScalarExpectation::Exact { family, type_ }));
            }
            _ => None,
        };
        Ok(literal.map(ConditionalScalarExpectation::Literal))
    }

    fn conditional_boolean_initializer(
        &self,
        expression: NodeRef,
    ) -> Result<Option<bool>, SourceCheckError> {
        let record = self.node(expression)?;
        if record.flags.0 != 0 {
            return Ok(None);
        }
        match (&record.kind, &record.data) {
            (SyntaxKind::TrueKeyword, NodeData::KeywordExpression(_)) => Ok(Some(true)),
            (SyntaxKind::FalseKeyword, NodeData::KeywordExpression(_)) => Ok(Some(false)),
            (
                SyntaxKind::ParenthesizedExpression,
                NodeData::ParenthesizedExpression(parenthesized),
            ) => {
                let inner = self.reference(parenthesized.expression);
                if self.node(inner)?.parent != Some(expression.node) {
                    return Err(SourceCheckError::Conditional(expression));
                }
                self.conditional_boolean_initializer(inner)
            }
            _ => Ok(None),
        }
    }

    fn conditional_expected_result(
        &self,
        when_true: ConditionalScalarExpectation,
        when_false: ConditionalScalarExpectation,
    ) -> Result<Option<TypeId>, SourceCheckError> {
        let Some((store, _)) = self.semantic else {
            return Ok(None);
        };
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?;
        let result = match (when_true, when_false) {
            (ConditionalScalarExpectation::Error, _) | (_, ConditionalScalarExpectation::Error) => {
                Some(bootstrap.error_type)
            }
            (
                ConditionalScalarExpectation::Exact {
                    family: left_family,
                    type_: left,
                },
                ConditionalScalarExpectation::Exact {
                    family: right_family,
                    type_: right,
                },
            ) if left == right && left_family == right_family => Some(left),
            (
                ConditionalScalarExpectation::Exact { family, type_ },
                ConditionalScalarExpectation::Literal(literal),
            )
            | (
                ConditionalScalarExpectation::Literal(literal),
                ConditionalScalarExpectation::Exact { family, type_ },
            ) if family == literal => Some(type_),
            (
                ConditionalScalarExpectation::Exact {
                    family: ConditionalScalarFamily::String,
                    ..
                },
                ConditionalScalarExpectation::Exact {
                    family: ConditionalScalarFamily::Number,
                    ..
                },
            )
            | (
                ConditionalScalarExpectation::Exact {
                    family: ConditionalScalarFamily::Number,
                    ..
                },
                ConditionalScalarExpectation::Exact {
                    family: ConditionalScalarFamily::String,
                    ..
                },
            ) => Some(bootstrap.string_or_number_type),
            (
                ConditionalScalarExpectation::Exact {
                    family: ConditionalScalarFamily::Number,
                    ..
                },
                ConditionalScalarExpectation::Exact {
                    family: ConditionalScalarFamily::BigInt,
                    ..
                },
            )
            | (
                ConditionalScalarExpectation::Exact {
                    family: ConditionalScalarFamily::BigInt,
                    ..
                },
                ConditionalScalarExpectation::Exact {
                    family: ConditionalScalarFamily::Number,
                    ..
                },
            ) => Some(bootstrap.number_or_bigint_type),
            _ => None,
        };
        if let Some(result) = result {
            store.validate_union_constituent(result)?;
        }
        Ok(result)
    }

    fn plan_binary(&mut self, expression: NodeRef) -> Result<PlannedExpression, SourceCheckError> {
        let (left_id, operator_id, right_id) = {
            let record = self.node(expression)?;
            let NodeData::BinaryExpression(binary) = &record.data else {
                return Err(self.unsupported(
                    expression,
                    record.kind,
                    SourceSyntaxRole::BinaryExpression,
                ));
            };
            if record.kind != SyntaxKind::BinaryExpression
                || record.flags.0 != 0
                || binary.symbol.is_some()
                || binary.type_.is_some()
                || binary.facts != 0
                || binary.modifiers.is_some()
            {
                return Err(self.unsupported(
                    expression,
                    record.kind,
                    SourceSyntaxRole::BinaryExpression,
                ));
            }
            (binary.left, binary.operator_token, binary.right)
        };
        if !self.primitive_binary_position_is_supported(expression)? {
            return Err(self.unsupported(
                expression,
                SyntaxKind::BinaryExpression,
                SourceSyntaxRole::BinaryExpression,
            ));
        }

        let Some((store, _)) = self.semantic else {
            return Err(self.unsupported(
                expression,
                SyntaxKind::BinaryExpression,
                SourceSyntaxRole::BinaryExpression,
            ));
        };
        if let Some(links) = store.type_node_links(expression) {
            let expected = TypeNodeLinks {
                resolved_type: links.resolved_type,
                ..TypeNodeLinks::default()
            };
            if links != &expected
                || links
                    .resolved_type
                    .is_some_and(|type_| store.type_payload(type_).is_none())
            {
                return Err(SourceCheckError::PrimitiveOperator(expression));
            }
        }

        let left = self.reference(left_id);
        let operator = self.reference(operator_id);
        let right = self.reference(right_id);
        let left_record = self.node(left)?;
        let operator_record = self.node(operator)?;
        let right_record = self.node(right)?;
        if left_record.parent != Some(expression.node)
            || operator_record.parent != Some(expression.node)
            || right_record.parent != Some(expression.node)
            || left_record.range.end > operator_record.range.start
            || operator_record.range.end > right_record.range.start
        {
            return Err(SourceCheckError::PrimitiveOperator(expression));
        }
        let left_kind = left_record.kind;
        let right_kind = right_record.kind;
        if operator_record.flags.0 != 0 || !matches!(operator_record.data, NodeData::Token(_)) {
            return Err(SourceCheckError::PrimitiveOperator(operator));
        }
        let operator_kind = operator_record.kind;
        let logical = matches!(
            operator_kind,
            SyntaxKind::AmpersandAmpersandToken
                | SyntaxKind::BarBarToken
                | SyntaxKind::QuestionQuestionToken
        );
        let Some(operator_text) = binary_operator_text(operator_kind) else {
            return Err(self.unsupported(
                operator,
                operator_kind,
                SourceSyntaxRole::BinaryOperator,
            ));
        };
        if !self.source_spelling_matches(operator, operator_text) {
            return Err(if logical {
                SourceCheckError::LogicalOperator(operator)
            } else {
                SourceCheckError::PrimitiveOperator(operator)
            });
        }

        let mut left_plan = self.plan_expression(left)?;
        if !logical && !primitive_binary_operand_plan_is_supported(&left_plan) {
            return Err(self.unsupported(left, left_kind, SourceSyntaxRole::BinaryOperand));
        }
        let mut right_plan = self.plan_expression(right)?;
        if !logical && !primitive_binary_operand_plan_is_supported(&right_plan) {
            return Err(self.unsupported(right, right_kind, SourceSyntaxRole::BinaryOperand));
        }
        let parent = DirectBinaryParent {
            left: left_plan.node,
            left_is_binary: matches!(
                &left_plan.kind,
                PlannedExpressionKind::Binary(_) | PlannedExpressionKind::Logical(_)
            ),
            operator: operator_kind,
        };
        set_direct_binary_parent(&mut left_plan, parent);
        set_direct_binary_parent(&mut right_plan, parent);
        let kind = if logical {
            PlannedExpressionKind::Logical(Box::new(LogicalBinaryPlan {
                node: expression,
                left: left_plan,
                operator: operator_kind,
                right: right_plan,
                parent: None,
            }))
        } else {
            PlannedExpressionKind::Binary(Box::new(PrimitiveBinaryPlan {
                node: expression,
                left: left_plan,
                operator: operator_kind,
                right: right_plan,
            }))
        };
        Ok(PlannedExpression::new(expression, kind))
    }

    fn primitive_binary_position_is_supported(
        &self,
        expression: NodeRef,
    ) -> Result<bool, SourceCheckError> {
        let mut current = expression;
        loop {
            if self.primitive_binary_position_roots.contains(&current) {
                return Ok(true);
            }
            let Some(parent_id) = self.node(current)?.parent else {
                return Ok(false);
            };
            let parent = self.reference(parent_id);
            let record = self.node(parent)?;
            match &record.data {
                NodeData::ParenthesizedExpression(parenthesized)
                    if parenthesized.expression == current.node =>
                {
                    current = parent;
                }
                NodeData::BinaryExpression(binary)
                    if binary.left == current.node || binary.right == current.node =>
                {
                    current = parent;
                }
                NodeData::AsExpression(assertion) if assertion.expression == current.node => {
                    current = parent;
                }
                NodeData::TypeAssertion(assertion) if assertion.expression == current.node => {
                    current = parent;
                }
                NodeData::VariableDeclaration(variable)
                    if variable.initializer == Some(current.node) =>
                {
                    return Ok(true);
                }
                NodeData::ReturnStatement(statement)
                    if statement.expression == Some(current.node) =>
                {
                    return Ok(true);
                }
                NodeData::ArrowFunction(arrow) if arrow.body == current.node => return Ok(true),
                _ => return Ok(false),
            }
        }
    }

    fn plan_assertion(
        &mut self,
        expression: NodeRef,
    ) -> Result<PlannedExpression, SourceCheckError> {
        let (type_id, operand_id) = {
            let node = self.node(expression)?;
            match (&node.data, node.kind) {
                (NodeData::TypeAssertion(assertion), SyntaxKind::TypeAssertionExpression) => {
                    (assertion.type_, assertion.expression)
                }
                (NodeData::AsExpression(assertion), SyntaxKind::AsExpression) => {
                    (assertion.type_, assertion.expression)
                }
                _ => {
                    return Err(self.unsupported(
                        expression,
                        node.kind,
                        SourceSyntaxRole::VariableInitializer,
                    ));
                }
            }
        };
        let type_node = self.reference(type_id);
        let operand = self.reference(operand_id);
        let type_record = self.node(type_node)?;
        if type_record.parent != Some(expression.node) {
            return Err(self.unsupported(
                type_node,
                type_record.kind,
                SourceSyntaxRole::AssertionType,
            ));
        }
        let operand_record = self.node(operand)?;
        if operand_record.parent != Some(expression.node) {
            return Err(self.unsupported(
                operand,
                operand_record.kind,
                SourceSyntaxRole::AssertionOperand,
            ));
        }
        if self.is_const_assertion_type(type_node)? {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::ConstAssertion(expression),
            ));
        }
        Ok(PlannedExpression::new(
            expression,
            PlannedExpressionKind::Assertion {
                type_node,
                operand: Box::new(self.plan_expression(operand)?),
            },
        ))
    }

    fn is_const_assertion_type(&self, type_node: NodeRef) -> Result<bool, SourceCheckError> {
        let record = self.node(type_node)?;
        let NodeData::TypeReferenceNode(reference) = &record.data else {
            return Ok(false);
        };
        if record.kind != SyntaxKind::TypeReference || reference.type_arguments.is_some() {
            return Ok(false);
        }
        let name = self.reference(reference.type_name);
        let name_record = self.node(name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Ok(false);
        };
        Ok(name_record.kind == SyntaxKind::Identifier
            && name_record.parent == Some(type_node.node)
            && identifier.text == "const")
    }

    fn is_global_undefined(&self) -> bool {
        let Some((store, _)) = self.semantic else {
            return false;
        };
        let Some(bootstrap) = store.intrinsic_bootstrap() else {
            return false;
        };
        let global_matches = store
            .symbol_table(bootstrap.globals)
            .and_then(|globals| globals.get_source("undefined"))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            == Some(bootstrap.undefined_symbol);
        let locally_shadowed = self
            .bound
            .locals(self.bound.source_file())
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source("undefined"))
            .is_some_and(|symbol| {
                store.get_merged_symbol(symbol) != Some(bootstrap.undefined_symbol)
            });
        global_matches && !locally_shadowed
    }

    fn plan_array_literal(
        &mut self,
        expression: NodeRef,
    ) -> Result<PlannedExpression, SourceCheckError> {
        let elements = {
            let node = self.node(expression)?;
            let NodeData::ArrayLiteralExpression(array) = &node.data else {
                return Err(self.unsupported(
                    expression,
                    node.kind,
                    SourceSyntaxRole::ArrayLiteral,
                ));
            };
            if node.flags.0 != 0 || array.facts != 0 {
                return Err(self.unsupported(
                    expression,
                    node.kind,
                    SourceSyntaxRole::ArrayLiteral,
                ));
            }
            array.elements.nodes.clone()
        };
        let mut planned = Vec::with_capacity(elements.len());
        for element in elements {
            let element = self.reference(element);
            let record = self.node(element)?;
            if record.parent != Some(expression.node)
                || matches!(
                    record.kind,
                    SyntaxKind::SpreadElement | SyntaxKind::OmittedExpression
                )
            {
                return Err(self.unsupported(element, record.kind, SourceSyntaxRole::ArrayElement));
            }
            planned.push(self.plan_expression(element)?);
        }
        Ok(PlannedExpression::new(
            expression,
            PlannedExpressionKind::Array(planned),
        ))
    }

    fn plan_object_literal(
        &mut self,
        expression: NodeRef,
    ) -> Result<PlannedExpression, SourceCheckError> {
        let Some((store, host)) = self.semantic else {
            return Err(self.unsupported(
                expression,
                SyntaxKind::ObjectLiteralExpression,
                SourceSyntaxRole::ObjectLiteral,
            ));
        };
        let plan = super::object_members::plan_object_literal(store, host, expression)
            .map_err(|error| self.object_plan_error(error))?;
        let mut properties = Vec::with_capacity(plan.properties.len());
        for initializer in plan.property_type_nodes() {
            properties.push(self.plan_expression(initializer)?);
        }
        Ok(PlannedExpression::new(
            expression,
            PlannedExpressionKind::Object { plan, properties },
        ))
    }

    fn object_plan_error(
        &self,
        error: super::object_members::PropertyObjectError,
    ) -> SourceCheckError {
        use super::object_members::PropertyObjectError;
        match error {
            PropertyObjectError::UnsupportedMember { node, kind } => {
                self.unsupported(node, kind, SourceSyntaxRole::ObjectProperty)
            }
            PropertyObjectError::InvalidObjectLiteral(node)
            | PropertyObjectError::InvalidTypeLiteral(node)
            | PropertyObjectError::InvalidCachedTypeLiteral { node, .. }
            | PropertyObjectError::Capacity(node) => self.unsupported(
                node,
                self.arena
                    .get(node.node)
                    .map_or(SyntaxKind::ObjectLiteralExpression, |record| record.kind),
                SourceSyntaxRole::ObjectLiteral,
            ),
            PropertyObjectError::InvalidInterface { declaration, .. } => self.unsupported(
                declaration,
                SyntaxKind::InterfaceDeclaration,
                SourceSyntaxRole::ObjectLiteral,
            ),
            PropertyObjectError::InvalidInterfaceSymbol(_)
            | PropertyObjectError::InvalidCachedInterface { .. } => self.unsupported(
                self.source.node_ref(),
                SyntaxKind::SourceFile,
                SourceSyntaxRole::ObjectLiteral,
            ),
        }
    }

    fn interface_plan_error(
        &self,
        declaration: NodeRef,
        error: super::object_members::PropertyObjectError,
    ) -> SourceCheckError {
        use super::object_members::PropertyObjectError;
        let (node, kind) = match error {
            PropertyObjectError::UnsupportedMember { node, kind } => (node, kind),
            PropertyObjectError::InvalidInterface { declaration, .. } => {
                (declaration, SyntaxKind::InterfaceDeclaration)
            }
            PropertyObjectError::InvalidInterfaceSymbol(_)
            | PropertyObjectError::InvalidCachedInterface { .. } => {
                (self.source.node_ref(), SyntaxKind::SourceFile)
            }
            PropertyObjectError::InvalidTypeLiteral(node)
            | PropertyObjectError::InvalidObjectLiteral(node)
            | PropertyObjectError::InvalidCachedTypeLiteral { node, .. }
            | PropertyObjectError::Capacity(node) => (
                node,
                if node.is_for(self.arena.id(), self.bound.file_id()) {
                    self.arena
                        .get(node.node)
                        .map_or(SyntaxKind::SourceFile, |record| record.kind)
                } else {
                    SyntaxKind::InterfaceDeclaration
                },
            ),
        };
        let (node, kind) = if node.is_for(self.arena.id(), self.bound.file_id()) {
            (node, kind)
        } else {
            // A merged global interface may fail on a declaration contributed
            // by a default library. Source diagnostics must remain anchored in
            // the source currently being planned rather than crossing arenas.
            (declaration, SyntaxKind::InterfaceDeclaration)
        };
        self.unsupported(node, kind, SourceSyntaxRole::InterfaceDeclaration)
    }

    fn plan_prefix_unary(
        &mut self,
        expression: NodeRef,
    ) -> Result<PlannedExpression, SourceCheckError> {
        let (operator, operand_id) = {
            let node = self.node(expression)?;
            let NodeData::PrefixUnaryExpression(prefix) = &node.data else {
                return Err(self.unsupported(
                    expression,
                    node.kind,
                    SourceSyntaxRole::VariableInitializer,
                ));
            };
            (prefix.operator, prefix.operand)
        };
        if operator != SyntaxKind::MinusToken {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::InvalidPrefixUnaryOperator {
                    node: expression,
                    operator,
                },
            ));
        }
        let operand = self.reference(operand_id);
        let (operand_kind, operand_parent) = {
            let operand_node = self.node(operand)?;
            (operand_node.kind, operand_node.parent)
        };
        if operand_parent != Some(expression.node) {
            return Err(self.unsupported(
                operand,
                operand_kind,
                SourceSyntaxRole::PrefixUnaryOperand,
            ));
        }
        match operand_kind {
            SyntaxKind::NumericLiteral => {
                let positive = self.plan_numeric_literal(operand)?;
                let value = -positive;
                self.numbers.push(positive);
                self.numbers.push(value);
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::Number {
                        value,
                        unary_operand: Some(positive),
                    },
                ))
            }
            SyntaxKind::BigIntLiteral => {
                let positive = self.plan_bigint_literal(operand)?;
                let value = PseudoBigInt::new(&positive.base10_value, true);
                self.bigints.push(positive.clone());
                self.bigints.push(value.clone());
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::BigInt {
                        value,
                        unary_operand: Some(positive),
                    },
                ))
            }
            _ => Err(self.unsupported(operand, operand_kind, SourceSyntaxRole::PrefixUnaryOperand)),
        }
    }

    fn plan_numeric_literal(&self, literal: NodeRef) -> Result<Number, SourceCheckError> {
        let node = self.node(literal)?;
        let NodeData::NumericLiteral(data) = &node.data else {
            return Err(self.unsupported(
                literal,
                node.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        };
        if data.token_flags.0 != 0 {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::InvalidLiteralFlags(literal),
            ));
        }
        let value = ts_jsnum::from_string(&data.text);
        if value.is_nan() {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::InvalidLiteralSpelling(literal),
            ));
        }
        if let Some(source) = self.arena.source_text() {
            let spelling = source
                .get(node.range.start.get() as usize..node.range.end.get() as usize)
                .and_then(normalize_numeric_separators)
                .ok_or(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::InvalidLiteralSpelling(literal),
                ))?;
            let source_value = ts_jsnum::from_string(&spelling);
            if source_value.is_nan() || source_value != value {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::InvalidLiteralSpelling(literal),
                ));
            }
        }
        Ok(value)
    }

    fn plan_bigint_literal(&self, literal: NodeRef) -> Result<PseudoBigInt, SourceCheckError> {
        let node = self.node(literal)?;
        let NodeData::BigIntLiteral(data) = &node.data else {
            return Err(self.unsupported(
                literal,
                node.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        };
        if data.token_flags.0 != 0 {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::InvalidLiteralFlags(literal),
            ));
        }
        let normalized = normalize_bigint_literal(&data.text).ok_or(
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::InvalidLiteralSpelling(literal)),
        )?;
        let value = PseudoBigInt::parse_valid(&normalized);
        if let Some(source) = self.arena.source_text() {
            let spelling = source
                .get(node.range.start.get() as usize..node.range.end.get() as usize)
                .and_then(normalize_bigint_literal)
                .ok_or(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::InvalidLiteralSpelling(literal),
                ))?;
            if PseudoBigInt::parse_valid(&spelling) != value {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::InvalidLiteralSpelling(literal),
                ));
            }
        }
        Ok(value)
    }

    fn source_spelling_matches(&self, node: NodeRef, expected: &str) -> bool {
        let Some(source) = self.arena.source_text() else {
            return true;
        };
        let Some(record) = self.arena.get(node.node) else {
            return false;
        };
        source.get(record.range.start.get() as usize..record.range.end.get() as usize)
            == Some(expected)
    }

    fn node(&self, reference: NodeRef) -> Result<&Node, SourceCheckError> {
        if !reference.is_for(self.arena.id(), self.bound.file_id()) {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingNode(reference),
            ));
        }
        if !self.bound.contains(reference) {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::NodeNotBound(reference),
            ));
        }
        let node = self
            .arena
            .get(reference.node)
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingNode(reference),
            ))?;
        if !node.data.matches_syntax_kind(node.kind) {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MismatchedNodeData {
                    node: reference,
                    kind: node.kind,
                },
            ));
        }
        Ok(node)
    }

    fn reference(&self, node: NodeId) -> NodeRef {
        NodeRef::new(self.arena.id(), self.bound.file_id(), node)
    }

    fn unsupported(
        &self,
        node: NodeRef,
        kind: SyntaxKind,
        role: SourceSyntaxRole,
    ) -> SourceCheckError {
        debug_assert!(node.is_for(self.arena.id(), self.bound.file_id()));
        SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax { node, kind, role })
    }
}

fn import_alias_error_is_unsupported(error: super::alias::CanonicalAliasResolutionError) -> bool {
    use super::alias::{CanonicalAliasResolutionError, CanonicalAliasTargetUnavailable};

    let CanonicalAliasResolutionError::TargetUnavailable { reason, .. } = error else {
        return false;
    };
    matches!(
        reason,
        CanonicalAliasTargetUnavailable::UnsupportedDeclarationFamily
            | CanonicalAliasTargetUnavailable::TargetProviderUnavailable
            | CanonicalAliasTargetUnavailable::ModuleResolutionCapabilityUnavailable(_)
            | CanonicalAliasTargetUnavailable::ModuleResolutionEntryAbsent(_)
            | CanonicalAliasTargetUnavailable::ModuleResolutionUnresolved(_)
            | CanonicalAliasTargetUnavailable::UnsupportedAliasDeclaration(_)
            | CanonicalAliasTargetUnavailable::UnsupportedDefaultAlias(_)
            | CanonicalAliasTargetUnavailable::UnsupportedLocalExport(_)
            | CanonicalAliasTargetUnavailable::ExportStarResolutionUnsupported { .. }
            | CanonicalAliasTargetUnavailable::ExportEqualsResolutionUnsupported { .. }
            | CanonicalAliasTargetUnavailable::CommonJsModuleUnsupported { .. }
            | CanonicalAliasTargetUnavailable::JavaScriptModuleUnsupported { .. }
            | CanonicalAliasTargetUnavailable::SyntheticModuleResolutionUnsupported { .. }
            | CanonicalAliasTargetUnavailable::MissingExport { .. }
    )
}

fn valid_range(
    range: TextRange,
    parent: Option<TextRange>,
    source: TextRange,
    source_text: Option<&str>,
) -> bool {
    let start = range.start.get();
    let end = range.end.get();
    if start > end || start < source.start.get() || end > source.end.get() {
        return false;
    }
    if parent.is_some_and(|parent| {
        start < parent.start.get()
            || end > parent.end.get()
            || parent.start.get() > parent.end.get()
    }) {
        return false;
    }
    source_text.is_none_or(|text| usize::try_from(end).is_ok_and(|end| end <= text.len()))
}

fn primitive_binary_operand_plan_is_supported(expression: &PlannedExpression) -> bool {
    match &expression.kind {
        PlannedExpressionKind::Null
        | PlannedExpressionKind::GlobalUndefined
        | PlannedExpressionKind::String(_)
        | PlannedExpressionKind::Number { .. }
        | PlannedExpressionKind::BigInt { .. }
        | PlannedExpressionKind::Boolean(_)
        | PlannedExpressionKind::Identifier(_)
        | PlannedExpressionKind::Call(_)
        | PlannedExpressionKind::Element(_) => true,
        PlannedExpressionKind::Parenthesized(inner) => {
            primitive_binary_operand_plan_is_supported(inner)
        }
        PlannedExpressionKind::Binary(binary) => {
            binary.node == expression.node
                && primitive_binary_operand_plan_is_supported(&binary.left)
                && primitive_binary_operand_plan_is_supported(&binary.right)
        }
        PlannedExpressionKind::Logical(logical) => {
            logical.node == expression.node
                && primitive_binary_operand_plan_is_supported(&logical.left)
                && primitive_binary_operand_plan_is_supported(&logical.right)
        }
        PlannedExpressionKind::TypeImportValueUse(_)
        | PlannedExpressionKind::Assertion { .. }
        | PlannedExpressionKind::Array(_)
        | PlannedExpressionKind::Object { .. }
        | PlannedExpressionKind::Property(_)
        | PlannedExpressionKind::New(_)
        | PlannedExpressionKind::Conditional(_) => false,
    }
}

fn conditional_scalar_operand_plan_is_supported(expression: &PlannedExpression) -> bool {
    match &expression.kind {
        PlannedExpressionKind::String(_)
        | PlannedExpressionKind::Number { .. }
        | PlannedExpressionKind::BigInt { .. }
        | PlannedExpressionKind::Boolean(_) => true,
        PlannedExpressionKind::Identifier(read) => matches!(
            read.kind,
            PlannedIdentifierReadKind::Variable | PlannedIdentifierReadKind::Unresolved
        ),
        PlannedExpressionKind::Parenthesized(inner) => {
            conditional_scalar_operand_plan_is_supported(inner)
        }
        PlannedExpressionKind::Conditional(_) => true,
        PlannedExpressionKind::Null
        | PlannedExpressionKind::GlobalUndefined
        | PlannedExpressionKind::TypeImportValueUse(_)
        | PlannedExpressionKind::Assertion { .. }
        | PlannedExpressionKind::Array(_)
        | PlannedExpressionKind::Object { .. }
        | PlannedExpressionKind::Property(_)
        | PlannedExpressionKind::Element(_)
        | PlannedExpressionKind::Call(_)
        | PlannedExpressionKind::New(_)
        | PlannedExpressionKind::Binary(_)
        | PlannedExpressionKind::Logical(_) => false,
    }
}

fn planned_expression_reads_symbol(
    expression: &PlannedExpression,
    symbol: SemanticSymbolId,
) -> bool {
    match &expression.kind {
        PlannedExpressionKind::Identifier(read) => read.value_symbol == symbol,
        PlannedExpressionKind::Parenthesized(inner) => {
            planned_expression_reads_symbol(inner, symbol)
        }
        _ => false,
    }
}

fn preflight_uncached_conditional_operand_links(
    store: &CanonicalTypeMapperStore,
    expression: &PlannedExpression,
) -> Result<(), SourceCheckError> {
    match &expression.kind {
        PlannedExpressionKind::Identifier(read)
            if read.kind == PlannedIdentifierReadKind::Unresolved =>
        {
            let error_type = store
                .intrinsic_bootstrap()
                .map(|bootstrap| bootstrap.error_type)
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?;
            return preflight_source_expression_cache(store, expression.node, error_type);
        }
        PlannedExpressionKind::Conditional(conditional) => {
            return preflight_source_expression_cache(
                store,
                expression.node,
                conditional.expected_result,
            );
        }
        _ => {}
    }
    if store
        .type_node_links(expression.node)
        .is_some_and(|links| links != &TypeNodeLinks::default())
    {
        let expected = store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.error_type)
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?;
        return Err(SourceCheckError::Assertion(
            SourceAssertionError::InvalidExpressionCache {
                node: expression.node,
                cached: store
                    .type_node_links(expression.node)
                    .and_then(|links| links.resolved_type),
                expected,
            },
        ));
    }
    if let PlannedExpressionKind::Parenthesized(inner) = &expression.kind {
        preflight_uncached_conditional_operand_links(store, inner)?;
    }
    Ok(())
}

/// Proves that a hoisted inferred function can be checked before statement
/// execution without observing a pending inferred callable or statement-local
/// flow. This is deliberately a dependency gate, not a second expression
/// planner: every admitted expression was already proven by `SourcePlanner`.
fn preflight_inferred_function_return_dependencies(
    functions: &[PlannedFunction],
) -> Result<(), SourceCheckError> {
    fn expression_is_closed(
        expression: &PlannedExpression,
        parameters: &[SourceCallableParameterPlan],
        locals: &HashSet<SemanticSymbolId>,
        functions: &[PlannedFunction],
    ) -> bool {
        match &expression.kind {
            PlannedExpressionKind::Null
            | PlannedExpressionKind::String(_)
            | PlannedExpressionKind::Number { .. }
            | PlannedExpressionKind::BigInt { .. }
            | PlannedExpressionKind::Boolean(_)
            | PlannedExpressionKind::GlobalUndefined => true,
            PlannedExpressionKind::Identifier(read) => {
                read.kind == PlannedIdentifierReadKind::Variable
                    && (parameters
                        .iter()
                        .any(|parameter| parameter.symbol == read.value_symbol)
                        || locals.contains(&read.value_symbol))
            }
            PlannedExpressionKind::TypeImportValueUse(_) | PlannedExpressionKind::New(_) => false,
            PlannedExpressionKind::Parenthesized(inner)
            | PlannedExpressionKind::Assertion { operand: inner, .. } => {
                expression_is_closed(inner, parameters, locals, functions)
            }
            PlannedExpressionKind::Array(elements) => elements
                .iter()
                .all(|element| expression_is_closed(element, parameters, locals, functions)),
            PlannedExpressionKind::Object { properties, .. } => properties
                .iter()
                .all(|property| expression_is_closed(property, parameters, locals, functions)),
            PlannedExpressionKind::Property(property) => {
                expression_is_closed(&property.receiver, parameters, locals, functions)
            }
            PlannedExpressionKind::Element(element) => {
                expression_is_closed(&element.receiver, parameters, locals, functions)
                    && expression_is_closed(&element.index, parameters, locals, functions)
            }
            PlannedExpressionKind::Call(call) => {
                let callee = call.callee.unparenthesized();
                let PlannedExpressionKind::Identifier(read) = &callee.kind else {
                    return false;
                };
                read.kind == PlannedIdentifierReadKind::Function
                    && functions.iter().any(|function| {
                        function.callable.owner_symbol == read.value_symbol
                            && !function.callable.return_type.is_inferred()
                    })
                    && call.arguments.iter().all(|argument| {
                        expression_is_closed(argument, parameters, locals, functions)
                    })
            }
            PlannedExpressionKind::Binary(binary) => {
                expression_is_closed(&binary.left, parameters, locals, functions)
                    && expression_is_closed(&binary.right, parameters, locals, functions)
            }
            PlannedExpressionKind::Logical(logical) => {
                expression_is_closed(&logical.left, parameters, locals, functions)
                    && expression_is_closed(&logical.right, parameters, locals, functions)
            }
            PlannedExpressionKind::Conditional(conditional) => {
                expression_is_closed(&conditional.condition, parameters, locals, functions)
                    && expression_is_closed(&conditional.when_true, parameters, locals, functions)
                    && expression_is_closed(&conditional.when_false, parameters, locals, functions)
            }
        }
    }

    for function in functions {
        if !function.callable.return_type.is_inferred() {
            continue;
        }
        let mut locals = HashSet::new();
        let initializers_supported = function.parameter_initializers.iter().all(|initializer| {
            expression_is_closed(
                &initializer.expression,
                &function.callable.parameters,
                &locals,
                functions,
            )
        });
        let body_supported = match &function.body {
            PlannedFunctionBody::Ambient => !function.callable.return_type.is_inferred(),
            PlannedFunctionBody::Empty => true,
            PlannedFunctionBody::Return { expression, .. } => expression_is_closed(
                expression,
                &function.callable.parameters,
                &locals,
                functions,
            ),
            PlannedFunctionBody::Linear(statements) => {
                let mut supported = true;
                for local in &statements.locals {
                    let PlannedVariableInitializer::Expression(initializer) = &local.initializer
                    else {
                        supported = false;
                        break;
                    };
                    if !expression_is_closed(
                        initializer,
                        &function.callable.parameters,
                        &locals,
                        functions,
                    ) {
                        supported = false;
                        break;
                    }
                    locals.insert(local.symbol);
                }
                supported
                    && statements
                        .return_expression
                        .as_ref()
                        .is_none_or(|expression| {
                            expression_is_closed(
                                expression,
                                &function.callable.parameters,
                                &locals,
                                functions,
                            )
                        })
            }
            PlannedFunctionBody::Statements(_) | PlannedFunctionBody::JoinedStatements(_) => false,
        };
        if !initializers_supported || !body_supported {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::FunctionBody(
                    function.callable.body,
                )),
            ));
        }
    }
    Ok(())
}

pub(super) const fn primitive_binary_operator_text(kind: SyntaxKind) -> Option<&'static str> {
    match kind {
        SyntaxKind::PlusToken => Some("+"),
        SyntaxKind::MinusToken => Some("-"),
        SyntaxKind::AsteriskToken => Some("*"),
        SyntaxKind::SlashToken => Some("/"),
        SyntaxKind::PercentToken => Some("%"),
        SyntaxKind::AsteriskAsteriskToken => Some("**"),
        SyntaxKind::BarToken => Some("|"),
        SyntaxKind::AmpersandToken => Some("&"),
        SyntaxKind::CaretToken => Some("^"),
        SyntaxKind::LessThanLessThanToken => Some("<<"),
        SyntaxKind::GreaterThanGreaterThanToken => Some(">>"),
        SyntaxKind::GreaterThanGreaterThanGreaterThanToken => Some(">>>"),
        SyntaxKind::LessThanToken => Some("<"),
        SyntaxKind::LessThanEqualsToken => Some("<="),
        SyntaxKind::GreaterThanToken => Some(">"),
        SyntaxKind::GreaterThanEqualsToken => Some(">="),
        SyntaxKind::EqualsEqualsToken => Some("=="),
        SyntaxKind::ExclamationEqualsToken => Some("!="),
        SyntaxKind::EqualsEqualsEqualsToken => Some("==="),
        SyntaxKind::ExclamationEqualsEqualsToken => Some("!=="),
        _ => None,
    }
}

pub(super) const fn logical_binary_operator_text(kind: SyntaxKind) -> Option<&'static str> {
    match kind {
        SyntaxKind::AmpersandAmpersandToken => Some("&&"),
        SyntaxKind::BarBarToken => Some("||"),
        SyntaxKind::QuestionQuestionToken => Some("??"),
        _ => None,
    }
}

const fn binary_operator_text(kind: SyntaxKind) -> Option<&'static str> {
    match logical_binary_operator_text(kind) {
        Some(text) => Some(text),
        None => primitive_binary_operator_text(kind),
    }
}

fn set_direct_binary_parent(expression: &mut PlannedExpression, parent: DirectBinaryParent) {
    if let PlannedExpressionKind::Logical(binary) = &mut expression.kind {
        binary.parent = Some(parent);
    }
}

fn logical_mix_grammar_diagnostic(binary: &LogicalBinaryPlan) -> Option<LogicalGrammarDiagnostic> {
    fn direct_logical(expression: &PlannedExpression) -> Option<&LogicalBinaryPlan> {
        let PlannedExpressionKind::Logical(binary) = &expression.kind else {
            return None;
        };
        Some(binary)
    }

    if binary.operator != SyntaxKind::QuestionQuestionToken {
        return None;
    }
    if let Some(parent) = binary.parent {
        return (parent.left_is_binary && parent.operator == SyntaxKind::BarBarToken).then_some(
            LogicalGrammarDiagnostic {
                node: parent.left,
                first: binary.operator,
                second: parent.operator,
            },
        );
    }
    if let Some(left) = direct_logical(&binary.left).filter(|left| {
        matches!(
            left.operator,
            SyntaxKind::AmpersandAmpersandToken | SyntaxKind::BarBarToken
        )
    }) {
        return Some(LogicalGrammarDiagnostic {
            node: left.node,
            first: left.operator,
            second: binary.operator,
        });
    }
    direct_logical(&binary.right)
        .filter(|right| right.operator == SyntaxKind::AmpersandAmpersandToken)
        .map(|right| LogicalGrammarDiagnostic {
            node: right.node,
            first: binary.operator,
            second: right.operator,
        })
}

#[cfg(test)]
fn expression_type(
    store: &mut CanonicalTypeMapperStore,
    expression: &PlannedExpression,
    prepared: &PreparedExpression,
) -> Result<TypeId, SourceCheckError> {
    let mut property_diagnostics = prepare_source_property_diagnostic_sink(expression)?;
    Ok(execute_expression_types(
        store,
        None,
        &HashMap::new(),
        expression,
        prepared,
        &mut property_diagnostics,
    )?
    .result)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum CheckedExpressionShape {
    Leaf,
    Array(Vec<CheckedExpressionTypes>),
    Object(Vec<CheckedExpressionTypes>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CheckedExpressionTypes {
    raw: TypeId,
    pub(super) result: TypeId,
    pub(super) shape: CheckedExpressionShape,
    primitive_binary_recovery: Option<PrimitiveBinaryRecovery>,
}

impl CheckedExpressionTypes {
    fn leaf(raw: TypeId, result: TypeId) -> Self {
        Self {
            raw,
            result,
            shape: CheckedExpressionShape::Leaf,
            primitive_binary_recovery: None,
        }
    }

    fn primitive_binary(type_: TypeId, recovery: Option<PrimitiveBinaryRecovery>) -> Self {
        Self {
            raw: type_,
            result: type_,
            shape: CheckedExpressionShape::Leaf,
            primitive_binary_recovery: recovery,
        }
    }
}

fn prepare_source_property_diagnostic_sink(
    expression: &PlannedExpression,
) -> Result<Vec<SourcePropertyDiagnostic>, SourceCheckError> {
    fn capacity(expression: &PlannedExpression) -> Option<usize> {
        match &expression.kind {
            PlannedExpressionKind::Parenthesized(inner) => capacity(inner),
            PlannedExpressionKind::Array(elements) => {
                elements.iter().try_fold(0usize, |count, element| {
                    count.checked_add(capacity(element)?)
                })
            }
            PlannedExpressionKind::Object { properties, .. } => {
                properties.iter().try_fold(0usize, |count, property| {
                    count.checked_add(capacity(property)?)
                })
            }
            PlannedExpressionKind::Property(_) => Some(1),
            _ => Some(0),
        }
    }

    let capacity = capacity(expression).ok_or(SourceCheckError::Property(expression.node))?;
    let mut diagnostics = Vec::new();
    diagnostics
        .try_reserve_exact(capacity)
        .map_err(|_| SourceCheckError::Property(expression.node))?;
    Ok(diagnostics)
}

fn execute_expression_types(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
    expression: &PlannedExpression,
    prepared: &PreparedExpression,
    property_diagnostics: &mut Vec<SourcePropertyDiagnostic>,
) -> Result<CheckedExpressionTypes, SourceCheckError> {
    let types = match (&expression.kind, prepared) {
        (PlannedExpressionKind::Null, PreparedExpression::Literal(LiteralTreatment::Identity)) => {
            store
                .intrinsic_bootstrap()
                .map(|bootstrap| {
                    CheckedExpressionTypes::leaf(
                        bootstrap.null_widening_type,
                        bootstrap.null_widening_type,
                    )
                })
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))
        }
        (PlannedExpressionKind::Boolean(value), PreparedExpression::Literal(treatment)) => {
            let (regular, widened) = store
                .intrinsic_bootstrap()
                .map(|bootstrap| {
                    (
                        if *value {
                            bootstrap.regular_true_type
                        } else {
                            bootstrap.regular_false_type
                        },
                        bootstrap.boolean_type,
                    )
                })
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?;
            checked_literal_types(store, regular, widened, *treatment)
        }
        (
            PlannedExpressionKind::GlobalUndefined,
            PreparedExpression::Literal(LiteralTreatment::Identity),
        ) => store
            .intrinsic_bootstrap()
            .map(|bootstrap| {
                CheckedExpressionTypes::leaf(
                    bootstrap.undefined_widening_type,
                    bootstrap.undefined_widening_type,
                )
            })
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            )),
        (PlannedExpressionKind::Identifier(read), PreparedExpression::Identifier(treatment)) => {
            let raw = *current_flow_types
                .get(&read.value_symbol)
                .ok_or(match read.kind {
                    PlannedIdentifierReadKind::Variable | PlannedIdentifierReadKind::Unresolved => {
                        SourceCheckError::Variable(VariableInvariant::MissingCurrentFlowType(
                            read.value_symbol,
                        ))
                    }
                    PlannedIdentifierReadKind::Function => SourceCheckError::Function(
                        SourceFunctionInvariant::MissingCallableType(read.value_symbol),
                    ),
                    PlannedIdentifierReadKind::Import => SourceCheckError::Import(expression.node),
                })?;
            let result = identifier_expression_type(store, raw, *treatment)?;
            Ok(CheckedExpressionTypes::leaf(raw, result))
        }
        (PlannedExpressionKind::String(value), PreparedExpression::Literal(treatment)) => {
            let regular = store.regular_string_literal_type(value.clone())?;
            let widened = store
                .intrinsic_bootstrap()
                .map(|bootstrap| bootstrap.string_type)
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?;
            checked_literal_types(store, regular, widened, *treatment)
        }
        (
            PlannedExpressionKind::Number {
                value,
                unary_operand,
            },
            PreparedExpression::Literal(treatment),
        ) => {
            if let Some(operand) = unary_operand {
                store.regular_number_literal_type(*operand)?;
            }
            let regular = store.regular_number_literal_type(*value)?;
            let widened = store
                .intrinsic_bootstrap()
                .map(|bootstrap| bootstrap.number_type)
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?;
            checked_literal_types(store, regular, widened, *treatment)
        }
        (
            PlannedExpressionKind::BigInt {
                value,
                unary_operand,
            },
            PreparedExpression::Literal(treatment),
        ) => {
            if let Some(operand) = unary_operand {
                store.regular_bigint_literal_type(operand.clone())?;
            }
            let regular = store.regular_bigint_literal_type(value.clone())?;
            let widened = store
                .intrinsic_bootstrap()
                .map(|bootstrap| bootstrap.bigint_type)
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?;
            checked_literal_types(store, regular, widened, *treatment)
        }
        (
            PlannedExpressionKind::Parenthesized(inner),
            PreparedExpression::Parenthesized(prepared),
        ) => execute_expression_types(
            store,
            global_types,
            current_flow_types,
            inner,
            prepared,
            property_diagnostics,
        ),
        (PlannedExpressionKind::Array(elements), PreparedExpression::Array(prepared_elements)) => {
            debug_assert_eq!(elements.len(), prepared_elements.len());
            let global_types = global_types.ok_or(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Syntax {
                    node: expression.node,
                    kind: SyntaxKind::ArrayLiteralExpression,
                    role: SourceSyntaxRole::ArrayLiteral,
                },
            ))?;
            let mut checked_elements = Vec::with_capacity(elements.len());
            let mut element_types = Vec::with_capacity(elements.len());
            for (element, prepared) in elements.iter().zip(prepared_elements) {
                let checked = execute_expression_types(
                    store,
                    Some(global_types),
                    current_flow_types,
                    element,
                    prepared,
                    property_diagnostics,
                )?;
                element_types.push(checked.result);
                checked_elements.push(checked);
            }
            let element_type = if element_types.is_empty() {
                let bootstrap =
                    store
                        .intrinsic_bootstrap()
                        .ok_or(SourceCheckError::LiteralCache(
                            SourceLiteralCacheError::BootstrapUninitialized,
                        ))?;
                if bootstrap.options.strict_null_checks {
                    bootstrap.implicit_never_type
                } else {
                    bootstrap.undefined_widening_type
                }
            } else {
                store.expression_union_type_with_global_types(
                    global_types,
                    &element_types,
                    UnionReduction::Subtype,
                )?
            };
            let base = store.create_canonical_array_type(global_types, element_type, false)?;
            let array = store.create_array_literal_type(global_types, base)?;
            Ok(CheckedExpressionTypes {
                raw: array,
                result: array,
                shape: CheckedExpressionShape::Array(checked_elements),
                primitive_binary_recovery: None,
            })
        }
        (
            PlannedExpressionKind::Object { plan, properties },
            PreparedExpression::Object(prepared_properties),
        ) => {
            debug_assert_eq!(expression.node, plan.node);
            debug_assert_eq!(properties.len(), prepared_properties.len());
            super::object_members::object_literal_state(store, plan)
                .map_err(source_object_execution_error)?;
            let mut checked_properties = Vec::with_capacity(properties.len());
            let mut property_types = Vec::with_capacity(properties.len());
            for (property, prepared) in properties.iter().zip(prepared_properties) {
                let checked = execute_expression_types(
                    store,
                    global_types,
                    current_flow_types,
                    property,
                    prepared,
                    property_diagnostics,
                )?;
                property_types.push(checked.result);
                checked_properties.push(checked);
            }
            let object =
                super::object_members::publish_object_literal(store, plan, &property_types)
                    .map_err(source_object_execution_error)?;
            Ok(CheckedExpressionTypes {
                raw: object,
                result: object,
                shape: CheckedExpressionShape::Object(checked_properties),
                primitive_binary_recovery: None,
            })
        }
        (
            PlannedExpressionKind::Property(property),
            PreparedExpression::Property(prepared_receiver),
        ) => {
            let receiver = execute_expression_types(
                store,
                global_types,
                current_flow_types,
                &property.receiver,
                prepared_receiver,
                property_diagnostics,
            )?;
            let checked =
                check_direct_source_property(store, global_types, property, receiver.result)
                    .map_err(SourcePlanner::property_plan_error)?;
            if let Some(diagnostic) = checked.diagnostic {
                if property_diagnostics.len() == property_diagnostics.capacity() {
                    return Err(SourceCheckError::Property(property.node));
                }
                property_diagnostics.push(diagnostic);
            }
            Ok(CheckedExpressionTypes::leaf(checked.type_, checked.type_))
        }
        _ => unreachable!("a prepared expression must retain its planned expression shape"),
    }?;
    publish_expression_type(store, expression.node, types.raw)?;
    Ok(types)
}

fn checked_literal_types(
    store: &CanonicalTypeMapperStore,
    regular: TypeId,
    widened: TypeId,
    treatment: LiteralTreatment,
) -> Result<CheckedExpressionTypes, SourceCheckError> {
    let raw = store.fresh_type_of_literal_type(regular)?;
    let result = prepared_literal_type(store, regular, widened, treatment)?;
    Ok(CheckedExpressionTypes::leaf(raw, result))
}

fn prepared_literal_type(
    store: &CanonicalTypeMapperStore,
    regular: TypeId,
    widened: TypeId,
    treatment: LiteralTreatment,
) -> Result<TypeId, SourceCheckError> {
    match treatment {
        LiteralTreatment::Fresh => store
            .fresh_type_of_literal_type(regular)
            .map_err(Into::into),
        LiteralTreatment::Regular => Ok(regular),
        LiteralTreatment::WidenedPrimitive => Ok(widened),
        LiteralTreatment::Identity => {
            unreachable!("null and undefined do not use literal-pair treatment")
        }
    }
}

fn identifier_expression_type(
    store: &CanonicalTypeMapperStore,
    raw: TypeId,
    treatment: LiteralTreatment,
) -> Result<TypeId, SourceCheckError> {
    match treatment {
        LiteralTreatment::Identity | LiteralTreatment::Fresh => Ok(raw),
        LiteralTreatment::Regular => {
            store.validate_union_constituent(raw)?;
            let TypeData::Literal(literal) = store
                .type_payload(raw)
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::InvalidCachedLiteral(raw),
                ))?
                .data()
            else {
                return Err(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::InvalidCachedLiteral(raw),
                ));
            };
            Ok(literal.regular_type)
        }
        LiteralTreatment::WidenedPrimitive => widened_fresh_literal_type(store, raw),
    }
}

fn widened_fresh_literal_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<TypeId, SourceCheckError> {
    let Some(record) = store.type_payload(type_) else {
        return Err(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::InvalidCachedLiteral(type_),
        ));
    };
    let TypeData::Literal(literal) = record.data() else {
        return Ok(type_);
    };
    store.validate_union_constituent(type_)?;
    if literal.fresh_type != Some(type_) || literal.regular_type == type_ {
        return Ok(type_);
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::BootstrapUninitialized,
        ))?;
    if record.flags().intersects(TypeFlags::STRING_LITERAL) {
        Ok(bootstrap.string_type)
    } else if record.flags().intersects(TypeFlags::NUMBER_LITERAL) {
        Ok(bootstrap.number_type)
    } else if record.flags().intersects(TypeFlags::BIG_INT_LITERAL) {
        Ok(bootstrap.bigint_type)
    } else if record.flags().intersects(TypeFlags::BOOLEAN_LITERAL) {
        Ok(bootstrap.boolean_type)
    } else {
        Err(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::InvalidCachedLiteral(type_),
        ))
    }
}

fn source_object_execution_error(
    error: super::object_members::PropertyObjectError,
) -> SourceCheckError {
    use super::object_members::PropertyObjectError;
    match error {
        PropertyObjectError::Capacity(node) => {
            SourceCheckError::ObjectLiteral(SourceObjectLiteralError::Capacity(node))
        }
        PropertyObjectError::InvalidCachedTypeLiteral { node, type_ } => {
            SourceCheckError::ObjectLiteral(SourceObjectLiteralError::InvalidCache {
                node,
                type_: Some(type_),
            })
        }
        PropertyObjectError::InvalidObjectLiteral(node)
        | PropertyObjectError::InvalidTypeLiteral(node)
        | PropertyObjectError::UnsupportedMember { node, .. } => {
            SourceCheckError::ObjectLiteral(SourceObjectLiteralError::InvalidCache {
                node,
                type_: None,
            })
        }
        PropertyObjectError::InvalidInterface { declaration, .. } => {
            SourceCheckError::ObjectLiteral(SourceObjectLiteralError::InvalidCache {
                node: declaration,
                type_: None,
            })
        }
        PropertyObjectError::InvalidInterfaceSymbol(_)
        | PropertyObjectError::InvalidCachedInterface { .. } => {
            unreachable!("object-literal execution cannot produce an interface cache error")
        }
    }
}

const fn source_typeof_tag_text(tag: SourceTypeofTag) -> &'static str {
    match tag {
        SourceTypeofTag::String => "string",
        SourceTypeofTag::Number => "number",
        SourceTypeofTag::Boolean => "boolean",
        SourceTypeofTag::BigInt => "bigint",
        SourceTypeofTag::Symbol => "symbol",
        SourceTypeofTag::Undefined => "undefined",
        SourceTypeofTag::Object => "object",
        SourceTypeofTag::Function => "function",
    }
}

fn preflight_source_expression_cache(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    expected: TypeId,
) -> Result<(), SourceCheckError> {
    let Some(links) = store.type_node_links(node) else {
        return Ok(());
    };
    let canonical = TypeNodeLinks {
        resolved_type: links.resolved_type,
        ..TypeNodeLinks::default()
    };
    if links != &canonical
        || links
            .resolved_type
            .is_some_and(|cached| cached != expected || store.type_payload(cached).is_none())
    {
        return Err(SourceCheckError::Assertion(
            SourceAssertionError::InvalidExpressionCache {
                node,
                cached: links.resolved_type,
                expected,
            },
        ));
    }
    Ok(())
}

fn publish_expression_type(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    type_: TypeId,
) -> Result<(), SourceCheckError> {
    let mut links = store.type_node_links(node).cloned().unwrap_or_default();
    if let Some(cached) = links.resolved_type {
        return if cached == type_ {
            Ok(())
        } else {
            Err(SourceCheckError::Assertion(
                SourceAssertionError::InvalidExpressionCache {
                    node,
                    cached: Some(cached),
                    expected: type_,
                },
            ))
        };
    }
    links.resolved_type = Some(type_);
    if !store.set_type_node_links(node, links) {
        return Err(SourceCheckError::Assertion(
            SourceAssertionError::InvalidExpressionCache {
                node,
                cached: None,
                expected: type_,
            },
        ));
    }
    Ok(())
}

fn publish_assertion_operand(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    operand_type: TypeId,
) -> Result<(), SourceCheckError> {
    if let Some(links) = store.assertion_links(node) {
        return if links.expr_type == Some(operand_type) {
            Ok(())
        } else if links.expr_type.is_some() {
            Err(SourceCheckError::Assertion(
                SourceAssertionError::InvalidOperandCache {
                    node,
                    cached: links.expr_type,
                    expected: operand_type,
                },
            ))
        } else if store.set_assertion_links(
            node,
            AssertionLinks {
                expr_type: Some(operand_type),
            },
        ) {
            Ok(())
        } else {
            Err(SourceCheckError::Assertion(
                SourceAssertionError::InvalidOperandCache {
                    node,
                    cached: None,
                    expected: operand_type,
                },
            ))
        };
    }
    if !store.set_assertion_links(
        node,
        AssertionLinks {
            expr_type: Some(operand_type),
        },
    ) {
        return Err(SourceCheckError::Assertion(
            SourceAssertionError::InvalidOperandCache {
                node,
                cached: None,
                expected: operand_type,
            },
        ));
    }
    Ok(())
}

fn enqueue_deferred_assertion(
    store: &mut CanonicalTypeMapperStore,
    source: SourceFileRef,
    node: NodeRef,
) -> Result<(), SourceCheckError> {
    let mut links = store.source_file_links(source).cloned().unwrap_or_default();
    links.deferred_nodes.insert(node);
    if !store.set_source_file_links(source, links) {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::SourceLinkPublication(source),
        ));
    }
    Ok(())
}

fn preflight_type_import_value_use(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    resolved_type_imports: &HashMap<SemanticSymbolId, ResolvedSourceTypeImportBinding>,
    read: &PlannedSourceTypeImportValueUse,
) -> Result<PreparedSourceTypeImportValueUse, SourceCheckError> {
    let resolved = resolved_type_imports
        .get(&read.alias_symbol)
        .ok_or(SourceCheckError::Import(read.node))?;
    match reject_source_type_import_value_use(
        arena,
        bound,
        store,
        resolved,
        read.node,
        &read.name,
        read.alias_symbol,
    ) {
        Err(SourceImportError::Unsupported(SourceImportUnsupported::ValueUseOfTypeOnlyImport(
            node,
        ))) if node == read.node => {}
        Err(error) => return Err(SourcePlanner::import_plan_error(read.node, &error)),
        Ok(()) => return Err(SourceCheckError::Import(read.node)),
    }
    let error_type = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.error_type)
        .ok_or(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::BootstrapUninitialized,
        ))?;
    let prior_links = store.type_node_links(read.node).cloned();
    let mut publication = prior_links.clone().unwrap_or_default();
    if !store.contains_node_ref(read.node)
        || store.type_payload(error_type).is_none()
        || publication
            .outer_type_parameters
            .as_deref()
            .is_some_and(|types| {
                types
                    .iter()
                    .any(|type_| store.type_payload(*type_).is_none())
            })
        || publication
            .resolved_type
            .is_some_and(|cached| cached != error_type)
    {
        return Err(SourceCheckError::Assertion(
            SourceAssertionError::InvalidExpressionCache {
                node: read.node,
                cached: publication.resolved_type,
                expected: error_type,
            },
        ));
    }
    publication.resolved_type = Some(error_type);
    Ok(PreparedSourceTypeImportValueUse {
        diagnostic: CanonicalCheckerDiagnostic {
            node: Some(read.node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(1361).ok_or(SourceCheckError::MissingDiagnostic(1361))?,
                [read.name.clone()],
            ),
            related_information: Vec::new(),
        },
        error_type,
        prior_links,
        publication,
    })
}

fn check_type_import_value_use(
    store: &mut CanonicalTypeMapperStore,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    read: &PlannedSourceTypeImportValueUse,
) -> Result<CheckedExpressionTypes, SourceCheckError> {
    let prepared = preflighted_type_import_value_uses
        .get(&read.node)
        .ok_or(SourceCheckError::Import(read.node))?;
    if store.type_node_links(read.node) != prepared.prior_links.as_ref() {
        return Err(SourceCheckError::Assertion(
            SourceAssertionError::InvalidExpressionCache {
                node: read.node,
                cached: store
                    .type_node_links(read.node)
                    .and_then(|links| links.resolved_type),
                expected: prepared.error_type,
            },
        ));
    }
    // Preflight proved node, error-type, and outer-type provenance. The store is
    // append-only for all three, and the exact link comparison above prevents
    // an intervening source statement from invalidating this prepared payload.
    if !store.set_type_node_links(read.node, prepared.publication.clone()) {
        return Err(SourceCheckError::Assertion(
            SourceAssertionError::InvalidExpressionCache {
                node: read.node,
                cached: prepared
                    .prior_links
                    .as_ref()
                    .and_then(|links| links.resolved_type),
                expected: prepared.error_type,
            },
        ));
    }
    merge_retry_diagnostic(diagnostics, prepared.diagnostic.clone());
    Ok(CheckedExpressionTypes::leaf(
        prepared.error_type,
        prepared.error_type,
    ))
}

fn check_unresolved_identifier(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    expression: &PlannedExpression,
    read: PlannedIdentifierRead,
) -> Result<CheckedExpressionTypes, SourceCheckError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::BootstrapUninitialized,
        ))?;
    let unknown_symbol = bootstrap.unknown_symbol;
    let error_type = bootstrap.error_type;
    if read.kind != PlannedIdentifierReadKind::Unresolved
        || read.resolved_symbol != unknown_symbol
        || read.value_symbol != unknown_symbol
        || store.symbol(unknown_symbol).is_none()
        || store.type_payload(error_type).is_none()
    {
        return Err(SourceCheckError::Variable(
            VariableInvariant::InvalidSymbolShape(read.value_symbol),
        ));
    }
    let record = host
        .node(expression.node)
        .ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingNode(expression.node),
        ))?;
    let NodeData::Identifier(identifier) = &record.data else {
        return Err(SourceCheckError::Variable(
            VariableInvariant::InvalidSymbolShape(read.value_symbol),
        ));
    };
    let name = identifier.text.clone();
    preflight_source_expression_cache(store, expression.node, error_type)?;
    publish_expression_type(store, expression.node, error_type)?;
    merge_retry_diagnostic(
        diagnostics,
        CanonicalCheckerDiagnostic {
            node: Some(expression.node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2304).ok_or(SourceCheckError::MissingDiagnostic(2304))?,
                [name],
            ),
            related_information: Vec::new(),
        },
    );
    Ok(CheckedExpressionTypes::leaf(error_type, error_type))
}

fn emit_uninitialized_variable_read_diagnostics(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    expression: &PlannedExpression,
) -> Result<(), SourceCheckError> {
    match &expression.kind {
        PlannedExpressionKind::Identifier(read) if expression.used_before_assignment => {
            let type_ =
                *current_flow_types
                    .get(&read.value_symbol)
                    .ok_or(SourceCheckError::Variable(
                        VariableInvariant::MissingCurrentFlowType(read.value_symbol),
                    ))?;
            let record = store.type_payload(type_).ok_or(SourceCheckError::Variable(
                VariableInvariant::MissingCurrentFlowType(read.value_symbol),
            ))?;
            let permits_uninitialized = record
                .flags()
                .intersects(TypeFlags::ANY_OR_UNKNOWN | TypeFlags::UNDEFINED | TypeFlags::VOID)
                || matches!(
                    record.data(),
                    TypeData::Union(union) if union.union.types.iter().any(|constituent| {
                        store
                            .type_payload(*constituent)
                            .is_some_and(|record| record.flags().intersects(TypeFlags::UNDEFINED))
                    })
                );
            if permits_uninitialized {
                return Ok(());
            }
            let node = host
                .node(expression.node)
                .ok_or(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MissingNode(expression.node),
                ))?;
            let NodeData::Identifier(identifier) = &node.data else {
                return Err(SourceCheckError::Variable(
                    VariableInvariant::InvalidSymbolShape(read.value_symbol),
                ));
            };
            merge_retry_diagnostic(
                diagnostics,
                CanonicalCheckerDiagnostic {
                    node: Some(expression.node),
                    range_override: None,
                    diagnostic: Diagnostic::with_arguments(
                        message_by_code(2454).ok_or(SourceCheckError::MissingDiagnostic(2454))?,
                        [identifier.text.clone()],
                    ),
                    related_information: Vec::new(),
                },
            );
        }
        PlannedExpressionKind::Parenthesized(inner)
        | PlannedExpressionKind::Assertion { operand: inner, .. } => {
            emit_uninitialized_variable_read_diagnostics(
                store,
                host,
                current_flow_types,
                diagnostics,
                inner,
            )?;
        }
        PlannedExpressionKind::Array(elements)
        | PlannedExpressionKind::Object {
            properties: elements,
            ..
        } => {
            for element in elements {
                emit_uninitialized_variable_read_diagnostics(
                    store,
                    host,
                    current_flow_types,
                    diagnostics,
                    element,
                )?;
            }
        }
        PlannedExpressionKind::Property(property) => {
            emit_uninitialized_variable_read_diagnostics(
                store,
                host,
                current_flow_types,
                diagnostics,
                &property.receiver,
            )?;
        }
        PlannedExpressionKind::Element(element) => {
            for operand in [&element.receiver, &element.index] {
                emit_uninitialized_variable_read_diagnostics(
                    store,
                    host,
                    current_flow_types,
                    diagnostics,
                    operand,
                )?;
            }
        }
        PlannedExpressionKind::Call(call) => {
            emit_uninitialized_variable_read_diagnostics(
                store,
                host,
                current_flow_types,
                diagnostics,
                &call.callee,
            )?;
            for argument in &call.arguments {
                emit_uninitialized_variable_read_diagnostics(
                    store,
                    host,
                    current_flow_types,
                    diagnostics,
                    argument,
                )?;
            }
        }
        PlannedExpressionKind::Binary(binary) => {
            for operand in [&binary.left, &binary.right] {
                emit_uninitialized_variable_read_diagnostics(
                    store,
                    host,
                    current_flow_types,
                    diagnostics,
                    operand,
                )?;
            }
        }
        PlannedExpressionKind::Logical(binary) => {
            for operand in [&binary.left, &binary.right] {
                emit_uninitialized_variable_read_diagnostics(
                    store,
                    host,
                    current_flow_types,
                    diagnostics,
                    operand,
                )?;
            }
        }
        PlannedExpressionKind::Conditional(conditional) => {
            for operand in [
                &conditional.condition,
                &conditional.when_true,
                &conditional.when_false,
            ] {
                emit_uninitialized_variable_read_diagnostics(
                    store,
                    host,
                    current_flow_types,
                    diagnostics,
                    operand,
                )?;
            }
        }
        PlannedExpressionKind::Null
        | PlannedExpressionKind::String(_)
        | PlannedExpressionKind::Number { .. }
        | PlannedExpressionKind::BigInt { .. }
        | PlannedExpressionKind::Boolean(_)
        | PlannedExpressionKind::GlobalUndefined
        | PlannedExpressionKind::Identifier(_)
        | PlannedExpressionKind::TypeImportValueUse(_)
        | PlannedExpressionKind::New(_) => {}
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_expression_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    expression: &PlannedExpression,
    contextual_type: Option<TypeId>,
    deferred: &mut Vec<DeferredAssertion>,
) -> Result<CheckedExpressionTypes, SourceCheckError> {
    session.reset_query();
    if options.intrinsic.strict_null_checks {
        emit_uninitialized_variable_read_diagnostics(
            store,
            host,
            current_flow_types,
            diagnostics,
            expression,
        )?;
    }
    match &expression.kind {
        PlannedExpressionKind::Identifier(read)
            if read.kind == PlannedIdentifierReadKind::Unresolved =>
        {
            check_unresolved_identifier(store, host, diagnostics, expression, *read)
        }
        PlannedExpressionKind::TypeImportValueUse(read) => check_type_import_value_use(
            store,
            diagnostics,
            preflighted_type_import_value_uses,
            read,
        ),
        PlannedExpressionKind::Conditional(conditional) => {
            if contextual_type.is_some() {
                return Err(SourceCheckError::Conditional(conditional.node));
            }
            let condition =
                if conditional.condition_expectation == ConditionalScalarExpectation::Error {
                    check_expression_type(
                        store,
                        host,
                        global_types,
                        source,
                        options,
                        session,
                        diagnostics,
                        current_flow_types,
                        preflighted_type_import_value_uses,
                        &conditional.condition,
                        None,
                        deferred,
                    )?
                } else {
                    check_uncached_conditional_scalar(
                        store,
                        current_flow_types,
                        &conditional.condition,
                    )?
                };
            validate_conditional_scalar_expectation(
                store,
                &conditional.condition,
                condition.result,
                conditional.condition_expectation,
            )?;
            if !source_truthiness_condition_type_is_supported(
                store,
                condition.result,
                conditional.condition.node,
                &mut HashSet::new(),
            )? {
                return Err(SourceCheckError::Conditional(conditional.condition.node));
            }
            emit_truthiness_operand_diagnostics(
                store,
                host,
                diagnostics,
                &conditional.condition,
                condition.result,
                conditional.node,
            )?;
            let when_true =
                if conditional.when_true_expectation == ConditionalScalarExpectation::Error {
                    check_expression_type(
                        store,
                        host,
                        global_types,
                        source,
                        options,
                        session,
                        diagnostics,
                        current_flow_types,
                        preflighted_type_import_value_uses,
                        &conditional.when_true,
                        None,
                        deferred,
                    )?
                } else {
                    check_uncached_conditional_scalar(
                        store,
                        current_flow_types,
                        &conditional.when_true,
                    )?
                };
            validate_conditional_scalar_expectation(
                store,
                &conditional.when_true,
                when_true.result,
                conditional.when_true_expectation,
            )?;
            let when_false =
                if conditional.when_false_expectation == ConditionalScalarExpectation::Error {
                    check_expression_type(
                        store,
                        host,
                        global_types,
                        source,
                        options,
                        session,
                        diagnostics,
                        current_flow_types,
                        preflighted_type_import_value_uses,
                        &conditional.when_false,
                        None,
                        deferred,
                    )?
                } else {
                    check_uncached_conditional_scalar(
                        store,
                        current_flow_types,
                        &conditional.when_false,
                    )?
                };
            validate_conditional_scalar_expectation(
                store,
                &conditional.when_false,
                when_false.result,
                conditional.when_false_expectation,
            )?;
            let result_type = store.expression_union_type_with_global_types(
                global_types,
                &[when_true.result, when_false.result],
                UnionReduction::Subtype,
            )?;
            if result_type != conditional.expected_result {
                return Err(SourceCheckError::Conditional(conditional.node));
            }
            publish_expression_type(store, conditional.node, result_type)?;
            Ok(CheckedExpressionTypes::leaf(result_type, result_type))
        }
        PlannedExpressionKind::Element(element) => {
            let receiver = check_expression_type(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                current_flow_types,
                preflighted_type_import_value_uses,
                &element.receiver,
                None,
                deferred,
            )?;
            let index = check_expression_type(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                current_flow_types,
                preflighted_type_import_value_uses,
                &element.index,
                None,
                deferred,
            )?;
            let checked = check_direct_source_element(
                store,
                host,
                global_types,
                options,
                element,
                receiver.result,
                index.result,
            )
            .map_err(|error| SourcePlanner::element_plan_error(element.node, error))?;
            if let Some(diagnostic) = checked.diagnostic {
                merge_retry_diagnostic(diagnostics, diagnostic);
            }
            Ok(CheckedExpressionTypes::leaf(checked.type_, checked.type_))
        }
        PlannedExpressionKind::Logical(binary) => {
            let left_contextual_type = match binary.operator {
                SyntaxKind::BarBarToken | SyntaxKind::QuestionQuestionToken => contextual_type,
                SyntaxKind::AmpersandAmpersandToken => None,
                _ => return Err(SourceCheckError::LogicalOperator(binary.node)),
            };
            let left = check_expression_type(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                current_flow_types,
                preflighted_type_import_value_uses,
                &binary.left,
                left_contextual_type,
                deferred,
            )?;
            let narrowed_flow_types = narrow_logical_right_flow_types(
                store,
                host,
                global_types,
                binary,
                current_flow_types,
            )?;
            let right_contextual_type = match binary.operator {
                SyntaxKind::AmpersandAmpersandToken => contextual_type,
                SyntaxKind::BarBarToken | SyntaxKind::QuestionQuestionToken => {
                    contextual_type.or(Some(left.result))
                }
                _ => return Err(SourceCheckError::LogicalOperator(binary.node)),
            };
            let right = check_expression_type(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                narrowed_flow_types.as_ref().unwrap_or(current_flow_types),
                preflighted_type_import_value_uses,
                &binary.right,
                right_contextual_type,
                deferred,
            )?;
            emit_logical_grammar_diagnostic(diagnostics, binary)?;
            emit_logical_operand_diagnostics(store, host, diagnostics, binary, left.result)?;
            let resolution = check_logical_binary(
                store,
                Some(global_types),
                LogicalBinaryRequest {
                    operator: binary.operator,
                    left_type: left.result,
                    right_type: right.result,
                },
            )
            .map_err(|error| logical_binary_check_error(host, binary, &error))?;
            publish_expression_type(store, binary.node, resolution.result_type)?;
            Ok(CheckedExpressionTypes::leaf(
                resolution.result_type,
                resolution.result_type,
            ))
        }
        PlannedExpressionKind::Binary(binary) => {
            let left = check_expression_type(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                current_flow_types,
                preflighted_type_import_value_uses,
                &binary.left,
                None,
                deferred,
            )?;
            let right = check_expression_type(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                current_flow_types,
                preflighted_type_import_value_uses,
                &binary.right,
                None,
                deferred,
            )?;
            let resolution = check_primitive_binary(
                store,
                PrimitiveBinaryRequest {
                    expression: binary.node,
                    left: binary.left.node,
                    operator: binary.operator,
                    right: binary.right.node,
                    left_type: left.result,
                    right_type: right.result,
                    left_recovery: left.primitive_binary_recovery,
                    right_recovery: right.primitive_binary_recovery,
                    bigint_exponentiation_target: PrimitiveBigIntExponentiationTarget::Unknown,
                },
            )
            .map_err(|error| primitive_binary_check_error(host, binary.node, &error))?;
            for diagnostic in resolution.diagnostics {
                merge_retry_diagnostic(diagnostics, diagnostic);
            }
            publish_expression_type(store, binary.node, resolution.result_type)?;
            Ok(CheckedExpressionTypes::primitive_binary(
                resolution.result_type,
                resolution.recovery,
            ))
        }
        PlannedExpressionKind::New(construction) => {
            if contextual_type.is_some() {
                return Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                    construction.node(),
                )));
            }
            preflight_direct_default_new(store, host, construction)
                .map_err(|error| SourcePlanner::new_plan_error(construction.node(), error))?;
            let checked = check_direct_default_new(store, host, construction)
                .map_err(|error| SourcePlanner::new_plan_error(construction.node(), error))?;
            if store
                .symbol_node_links(construction.constructor())
                .and_then(|links| links.resolved_symbol)
                != Some(construction.resolved_symbol())
                || store
                    .type_node_links(construction.constructor())
                    .and_then(|links| links.resolved_type)
                    != Some(checked.value_type)
                || store
                    .signature_links(construction.node())
                    .and_then(|links| links.resolved_signature.signature())
                    != Some(checked.signature)
                || store
                    .type_node_links(construction.node())
                    .and_then(|links| links.resolved_type)
                    != Some(checked.instance_type)
            {
                return Err(SourceCheckError::Call(construction.node()));
            }
            Ok(CheckedExpressionTypes::leaf(
                checked.instance_type,
                checked.instance_type,
            ))
        }
        PlannedExpressionKind::Call(call) => {
            emit_call_type_argument_grammar_diagnostics(diagnostics, call)?;
            let callee = check_expression_type(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                current_flow_types,
                preflighted_type_import_value_uses,
                &call.callee,
                None,
                deferred,
            )?;
            let mut argument_types = Vec::with_capacity(call.arguments.len());
            for (index, argument) in call.arguments.iter().enumerate() {
                let contextual_type = source_call_argument_contextual_type(
                    store,
                    global_types,
                    call,
                    callee.result,
                    index,
                )?;
                argument_types.push(
                    check_expression_type(
                        store,
                        host,
                        global_types,
                        source,
                        options,
                        session,
                        diagnostics,
                        current_flow_types,
                        preflighted_type_import_value_uses,
                        argument,
                        contextual_type,
                        deferred,
                    )?
                    .result,
                );
            }
            let checked = check_direct_source_call(
                store,
                host,
                global_types,
                options,
                session,
                diagnostics,
                call,
                callee.result,
                &argument_types,
            )?;
            Ok(CheckedExpressionTypes::leaf(
                checked.return_type,
                checked.return_type,
            ))
        }
        PlannedExpressionKind::Parenthesized(inner) => {
            let types = check_expression_type(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                current_flow_types,
                preflighted_type_import_value_uses,
                inner,
                contextual_type,
                deferred,
            )?;
            publish_expression_type(store, expression.node, types.raw)?;
            Ok(types)
        }
        PlannedExpressionKind::Assertion { type_node, operand } => {
            let operand_types = check_expression_type(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                current_flow_types,
                preflighted_type_import_value_uses,
                operand,
                None,
                deferred,
            )?;
            publish_assertion_operand(store, expression.node, operand_types.result)?;
            let mut assertion_diagnostics = CanonicalCheckerDiagnostics::default();
            let target = CanonicalTypeQuery::new_with_global_types_and_session(
                store,
                host,
                global_types,
                options,
                session,
                &mut assertion_diagnostics,
            )?
            .get_type_from_type_node(*type_node);
            merge_retry_diagnostics(diagnostics, assertion_diagnostics);
            let target = target?;
            publish_expression_type(store, expression.node, target)?;
            enqueue_deferred_assertion(store, source, expression.node)?;
            deferred.push(DeferredAssertion {
                node: expression.node,
                operand_type: operand_types.result,
                target_type: target,
            });
            Ok(CheckedExpressionTypes::leaf(target, target))
        }
        _ => {
            let mut property_diagnostics = prepare_source_property_diagnostic_sink(expression)?;
            let mut rendered_property_diagnostics = Vec::new();
            rendered_property_diagnostics
                .try_reserve_exact(property_diagnostics.capacity())
                .map_err(|_| SourceCheckError::Property(expression.node))?;
            let prepared = if let Some(contextual_type) = contextual_type {
                prepare_expression_context_with_global_types(
                    store,
                    host,
                    global_types,
                    current_flow_types,
                    expression,
                    contextual_type,
                )?
            } else {
                prepare_expression_without_context_with_global_types(
                    store,
                    host,
                    global_types,
                    current_flow_types,
                    expression,
                )?
            };
            let mut resolved_members = HashSet::new();
            let mut resolved_properties = HashSet::new();
            let checked = loop {
                match execute_expression_types(
                    store,
                    Some(global_types),
                    current_flow_types,
                    expression,
                    &prepared,
                    &mut property_diagnostics,
                ) {
                    Ok(checked) => break checked,
                    Err(SourceCheckError::RelationUnavailable(error)) => {
                        let candidates = current_flow_types.values().copied().collect::<Vec<_>>();
                        retry_source_generic_member_failure(
                            store,
                            global_types,
                            session,
                            error,
                            &candidates,
                            &mut resolved_members,
                            &mut resolved_properties,
                        )?;
                        property_diagnostics.clear();
                    }
                    Err(error) => return Err(error),
                }
            };
            for deferred in &property_diagnostics {
                let diagnostic = prepare_source_property_diagnostic(
                    store,
                    host,
                    global_types,
                    options,
                    deferred,
                )
                .map_err(SourcePlanner::property_plan_error)?;
                if rendered_property_diagnostics.len() == rendered_property_diagnostics.capacity() {
                    return Err(SourceCheckError::Property(expression.node));
                }
                rendered_property_diagnostics.push(diagnostic);
            }
            for diagnostic in rendered_property_diagnostics {
                merge_retry_diagnostic(diagnostics, diagnostic);
            }
            Ok(checked)
        }
    }
}

fn check_uncached_conditional_scalar(
    store: &mut CanonicalTypeMapperStore,
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
    expression: &PlannedExpression,
) -> Result<CheckedExpressionTypes, SourceCheckError> {
    match &expression.kind {
        PlannedExpressionKind::Identifier(read)
            if read.kind == PlannedIdentifierReadKind::Variable =>
        {
            let raw =
                *current_flow_types
                    .get(&read.value_symbol)
                    .ok_or(SourceCheckError::Variable(
                        VariableInvariant::MissingCurrentFlowType(read.value_symbol),
                    ))?;
            let result = identifier_expression_type(store, raw, LiteralTreatment::Identity)?;
            Ok(CheckedExpressionTypes::leaf(raw, result))
        }
        PlannedExpressionKind::String(value) => {
            let regular = store.regular_string_literal_type(value.clone())?;
            let string = store
                .intrinsic_bootstrap()
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?
                .string_type;
            checked_literal_types(store, regular, string, LiteralTreatment::Fresh)
        }
        PlannedExpressionKind::Number {
            value,
            unary_operand,
        } => {
            if let Some(operand) = unary_operand {
                store.regular_number_literal_type(*operand)?;
            }
            let regular = store.regular_number_literal_type(*value)?;
            let number = store
                .intrinsic_bootstrap()
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?
                .number_type;
            checked_literal_types(store, regular, number, LiteralTreatment::Fresh)
        }
        PlannedExpressionKind::BigInt {
            value,
            unary_operand,
        } => {
            if let Some(operand) = unary_operand {
                store.regular_bigint_literal_type(operand.clone())?;
            }
            let regular = store.regular_bigint_literal_type(value.clone())?;
            let bigint = store
                .intrinsic_bootstrap()
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?
                .bigint_type;
            checked_literal_types(store, regular, bigint, LiteralTreatment::Fresh)
        }
        PlannedExpressionKind::Boolean(value) => {
            let bootstrap = store
                .intrinsic_bootstrap()
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?;
            let regular = if *value {
                bootstrap.regular_true_type
            } else {
                bootstrap.regular_false_type
            };
            checked_literal_types(
                store,
                regular,
                bootstrap.boolean_type,
                LiteralTreatment::Fresh,
            )
        }
        PlannedExpressionKind::Parenthesized(inner) => {
            check_uncached_conditional_scalar(store, current_flow_types, inner)
        }
        _ => Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Syntax {
                node: expression.node,
                kind: SyntaxKind::ConditionalExpression,
                role: SourceSyntaxRole::VariableInitializer,
            },
        )),
    }
}

fn validate_conditional_scalar_expectation(
    store: &CanonicalTypeMapperStore,
    expression: &PlannedExpression,
    type_: TypeId,
    expectation: ConditionalScalarExpectation,
) -> Result<(), SourceCheckError> {
    store.validate_union_constituent(type_)?;
    match expectation {
        ConditionalScalarExpectation::Exact {
            type_: expected, ..
        } if type_ == expected => Ok(()),
        ConditionalScalarExpectation::Literal(family) => {
            let expected = match family {
                ConditionalScalarFamily::String => TypeFlags::STRING_LITERAL,
                ConditionalScalarFamily::Number => TypeFlags::NUMBER_LITERAL,
                ConditionalScalarFamily::BigInt => TypeFlags::BIG_INT_LITERAL,
                ConditionalScalarFamily::Boolean => TypeFlags::BOOLEAN_LITERAL,
            };
            if store
                .type_payload(type_)
                .is_some_and(|record| record.flags() == expected)
            {
                Ok(())
            } else {
                Err(SourceCheckError::Conditional(expression.node))
            }
        }
        ConditionalScalarExpectation::Exact { .. } => {
            Err(SourceCheckError::Conditional(expression.node))
        }
        ConditionalScalarExpectation::Error => {
            let expected = store
                .intrinsic_bootstrap()
                .map(|bootstrap| bootstrap.error_type)
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?;
            if type_ == expected {
                Ok(())
            } else {
                Err(SourceCheckError::Conditional(expression.node))
            }
        }
    }
}

fn narrow_logical_right_flow_types(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    binary: &LogicalBinaryPlan,
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
) -> Result<Option<HashMap<SemanticSymbolId, TypeId>>, SourceCheckError> {
    fn collect<'a>(
        expression: &'a PlannedExpression,
        operator: SyntaxKind,
        reads: &mut Vec<&'a PlannedIdentifierRead>,
    ) {
        let expression = expression.unparenthesized();
        match &expression.kind {
            PlannedExpressionKind::Identifier(read)
                if read.kind == PlannedIdentifierReadKind::Variable =>
            {
                reads.push(read);
            }
            PlannedExpressionKind::Logical(logical) if logical.operator == operator => {
                collect(&logical.left, operator, reads);
                collect(&logical.right, operator, reads);
            }
            _ => {}
        }
    }

    let mut reads = Vec::new();
    collect(&binary.left, binary.operator, &mut reads);
    if reads.is_empty() {
        return Ok(None);
    }
    let mut narrowed = current_flow_types.clone();
    let mut seen = HashSet::new();
    for read in reads {
        if !seen.insert(read.value_symbol) {
            continue;
        }
        let current =
            *current_flow_types
                .get(&read.value_symbol)
                .ok_or(SourceCheckError::Variable(
                    VariableInvariant::MissingCurrentFlowType(read.value_symbol),
                ))?;
        let type_ =
            narrow_logical_right_operand(store, Some(global_types), binary.operator, current)
                .map_err(|error| logical_binary_check_error(host, binary, &error))?;
        narrowed.insert(read.value_symbol, type_);
    }
    Ok(Some(narrowed))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PredicateSemantics {
    Always,
    Never,
    Sometimes,
}

fn combine_predicate_semantics(
    left: PredicateSemantics,
    right: PredicateSemantics,
) -> PredicateSemantics {
    if left == right {
        left
    } else {
        PredicateSemantics::Sometimes
    }
}

fn emit_logical_grammar_diagnostic(
    diagnostics: &mut CanonicalCheckerDiagnostics,
    binary: &LogicalBinaryPlan,
) -> Result<(), SourceCheckError> {
    let Some(grammar) = logical_mix_grammar_diagnostic(binary) else {
        return Ok(());
    };
    let first = logical_binary_operator_text(grammar.first)
        .ok_or(SourceCheckError::LogicalOperator(binary.node))?;
    let second = logical_binary_operator_text(grammar.second)
        .ok_or(SourceCheckError::LogicalOperator(binary.node))?;
    let message = message_by_code(5076).ok_or(SourceCheckError::MissingDiagnostic(5076))?;
    merge_retry_diagnostic(
        diagnostics,
        CanonicalCheckerDiagnostic {
            node: Some(grammar.node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(message, [first, second]),
            related_information: Vec::new(),
        },
    );
    Ok(())
}

fn emit_logical_operand_diagnostics(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    binary: &LogicalBinaryPlan,
    left_type: TypeId,
) -> Result<(), SourceCheckError> {
    match binary.operator {
        SyntaxKind::AmpersandAmpersandToken | SyntaxKind::BarBarToken => {
            emit_truthiness_operand_diagnostics(
                store,
                host,
                diagnostics,
                &binary.left,
                left_type,
                binary.node,
            )?;
        }
        SyntaxKind::QuestionQuestionToken => {
            let left_target = outer_expression_target(&binary.left);
            match syntactic_nullishness(left_target) {
                PredicateSemantics::Always => {
                    issue_node_diagnostic(diagnostics, left_target.node, 2871)?;
                }
                PredicateSemantics::Never => {
                    issue_node_diagnostic(diagnostics, left_target.node, 2869)?;
                }
                PredicateSemantics::Sometimes => {}
            }
        }
        _ => return Err(SourceCheckError::LogicalOperator(binary.node)),
    }
    Ok(())
}

fn emit_truthiness_operand_diagnostics(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    expression: &PlannedExpression,
    type_: TypeId,
    invariant_node: NodeRef,
) -> Result<(), SourceCheckError> {
    if store
        .type_payload(type_)
        .ok_or(SourceCheckError::LogicalOperator(invariant_node))?
        .flags()
        .intersects(TypeFlags::VOID)
    {
        issue_node_diagnostic(diagnostics, expression.node, 1345)?;
        return Ok(());
    }
    match syntactic_truthiness(host, expression) {
        PredicateSemantics::Always => {
            issue_node_diagnostic(diagnostics, expression.node, 2872)?;
        }
        PredicateSemantics::Never => {
            issue_node_diagnostic(diagnostics, expression.node, 2873)?;
        }
        PredicateSemantics::Sometimes => {}
    }
    Ok(())
}

fn outer_expression_target(mut expression: &PlannedExpression) -> &PlannedExpression {
    loop {
        expression = match &expression.kind {
            PlannedExpressionKind::Parenthesized(inner)
            | PlannedExpressionKind::Assertion { operand: inner, .. } => inner,
            _ => return expression,
        };
    }
}

fn issue_node_diagnostic(
    diagnostics: &mut CanonicalCheckerDiagnostics,
    node: NodeRef,
    code: u32,
) -> Result<(), SourceCheckError> {
    let message = message_by_code(code).ok_or(SourceCheckError::MissingDiagnostic(code))?;
    merge_retry_diagnostic(
        diagnostics,
        CanonicalCheckerDiagnostic {
            node: Some(node),
            range_override: None,
            diagnostic: Diagnostic::new(message),
            related_information: Vec::new(),
        },
    );
    Ok(())
}

fn syntactic_truthiness(
    host: &DeclaredTypeHost<'_>,
    expression: &PlannedExpression,
) -> PredicateSemantics {
    match &expression.kind {
        PlannedExpressionKind::Parenthesized(inner)
        | PlannedExpressionKind::Assertion { operand: inner, .. } => {
            syntactic_truthiness(host, inner)
        }
        PlannedExpressionKind::Number { .. }
            if numeric_literal_has_plain_boolean_idiom_spelling(host, expression.node) =>
        {
            PredicateSemantics::Sometimes
        }
        PlannedExpressionKind::Number { .. }
            if host
                .node(expression.node)
                .is_some_and(|node| node.kind == SyntaxKind::NumericLiteral) =>
        {
            PredicateSemantics::Always
        }
        PlannedExpressionKind::Array(_)
        | PlannedExpressionKind::Object { .. }
        | PlannedExpressionKind::New(_)
        | PlannedExpressionKind::BigInt { .. } => PredicateSemantics::Always,
        PlannedExpressionKind::Null | PlannedExpressionKind::GlobalUndefined => {
            PredicateSemantics::Never
        }
        PlannedExpressionKind::String(value) => {
            if value.is_empty() {
                PredicateSemantics::Never
            } else {
                PredicateSemantics::Always
            }
        }
        PlannedExpressionKind::Conditional(conditional) => combine_predicate_semantics(
            syntactic_truthiness(host, &conditional.when_true),
            syntactic_truthiness(host, &conditional.when_false),
        ),
        PlannedExpressionKind::Boolean(_)
        | PlannedExpressionKind::Identifier(_)
        | PlannedExpressionKind::TypeImportValueUse(_)
        | PlannedExpressionKind::Property(_)
        | PlannedExpressionKind::Element(_)
        | PlannedExpressionKind::Call(_)
        | PlannedExpressionKind::Binary(_)
        | PlannedExpressionKind::Logical(_)
        | PlannedExpressionKind::Number { .. } => PredicateSemantics::Sometimes,
    }
}

fn numeric_literal_has_plain_boolean_idiom_spelling(
    host: &DeclaredTypeHost<'_>,
    literal: NodeRef,
) -> bool {
    let Some(node) = host.node(literal) else {
        return false;
    };
    let NodeData::NumericLiteral(data) = &node.data else {
        return false;
    };
    let spelling = host
        .source(literal)
        .and_then(|(arena, _)| arena.source_text())
        .and_then(|source| {
            source.get(node.range.start.get() as usize..node.range.end.get() as usize)
        })
        .unwrap_or(&data.text);
    matches!(spelling, "0" | "1")
}

fn syntactic_nullishness(expression: &PlannedExpression) -> PredicateSemantics {
    match &expression.kind {
        PlannedExpressionKind::Parenthesized(inner)
        | PlannedExpressionKind::Assertion { operand: inner, .. } => syntactic_nullishness(inner),
        PlannedExpressionKind::Null | PlannedExpressionKind::GlobalUndefined => {
            PredicateSemantics::Always
        }
        PlannedExpressionKind::Identifier(_)
        | PlannedExpressionKind::TypeImportValueUse(_)
        | PlannedExpressionKind::Property(_)
        | PlannedExpressionKind::Element(_)
        | PlannedExpressionKind::Call(_) => PredicateSemantics::Sometimes,
        PlannedExpressionKind::Logical(binary) => match binary.operator {
            SyntaxKind::AmpersandAmpersandToken | SyntaxKind::BarBarToken => {
                PredicateSemantics::Sometimes
            }
            SyntaxKind::QuestionQuestionToken => syntactic_nullishness(&binary.right),
            _ => PredicateSemantics::Never,
        },
        PlannedExpressionKind::Conditional(conditional) => combine_predicate_semantics(
            syntactic_nullishness(&conditional.when_true),
            syntactic_nullishness(&conditional.when_false),
        ),
        PlannedExpressionKind::String(_)
        | PlannedExpressionKind::Number { .. }
        | PlannedExpressionKind::BigInt { .. }
        | PlannedExpressionKind::Boolean(_)
        | PlannedExpressionKind::Array(_)
        | PlannedExpressionKind::Object { .. }
        | PlannedExpressionKind::New(_)
        | PlannedExpressionKind::Binary(_) => PredicateSemantics::Never,
    }
}

fn logical_binary_check_error(
    host: &DeclaredTypeHost<'_>,
    binary: &LogicalBinaryPlan,
    error: &LogicalBinaryError,
) -> SourceCheckError {
    match error {
        LogicalBinaryError::Unsupported(LogicalBinaryUnsupported::Operator(kind)) => {
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                node: binary.node,
                kind: *kind,
                role: SourceSyntaxRole::BinaryOperator,
            })
        }
        LogicalBinaryError::Unsupported(LogicalBinaryUnsupported::Type(_)) => {
            let node = binary.left.node;
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                node,
                kind: host
                    .node(node)
                    .map_or(SyntaxKind::Unknown, |record| record.kind),
                role: SourceSyntaxRole::BinaryOperand,
            })
        }
        #[cfg(not(test))]
        LogicalBinaryError::Unsupported(LogicalBinaryUnsupported::MissingGlobalTypes) => {
            SourceCheckError::LogicalOperator(binary.node)
        }
        LogicalBinaryError::Invariant(
            LogicalBinaryInvariant::MissingBootstrap
            | LogicalBinaryInvariant::InvalidType(_)
            | LogicalBinaryInvariant::CyclicUnion(_)
            | LogicalBinaryInvariant::InvalidUnion(_),
        ) => SourceCheckError::LogicalOperator(binary.node),
        LogicalBinaryError::Literal(error) => (*error).into(),
    }
}

fn primitive_binary_check_error(
    host: &DeclaredTypeHost<'_>,
    expression: NodeRef,
    error: &PrimitiveBinaryError,
) -> SourceCheckError {
    match error {
        PrimitiveBinaryError::Unsupported(PrimitiveBinaryUnsupported::Operator(kind)) => {
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                node: expression,
                kind: *kind,
                role: SourceSyntaxRole::BinaryOperator,
            })
        }
        PrimitiveBinaryError::Unsupported(PrimitiveBinaryUnsupported::Operand { node, .. }) => {
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                node: *node,
                kind: host
                    .node(*node)
                    .map_or(SyntaxKind::Unknown, |record| record.kind),
                role: SourceSyntaxRole::BinaryOperand,
            })
        }
        PrimitiveBinaryError::Unsupported(
            PrimitiveBinaryUnsupported::BigIntExponentiationTarget(node),
        ) => SourceCheckError::Unsupported(UnsupportedSourceSyntax::BigIntExponentiationTarget(
            *node,
        )),
        PrimitiveBinaryError::Invariant(_) => SourceCheckError::PrimitiveOperator(expression),
        PrimitiveBinaryError::Literal(error) => (*error).into(),
        PrimitiveBinaryError::Relation(error) => (*error).into(),
        PrimitiveBinaryError::Display(error) => (*error).into(),
    }
}

fn validate_deferred_assertions(
    store: &CanonicalTypeMapperStore,
    source: SourceFileRef,
    deferred: &[DeferredAssertion],
) -> Result<(), SourceCheckError> {
    let actual = store
        .source_file_links(source)
        .map(|links| links.deferred_nodes.iter().copied().collect::<Vec<_>>())
        .unwrap_or_default();
    let expected = deferred
        .iter()
        .map(|assertion| assertion.node)
        .collect::<Vec<_>>();
    if actual != expected {
        return Err(SourceCheckError::Assertion(
            SourceAssertionError::InvalidDeferredNodes(source),
        ));
    }
    Ok(())
}

fn assertion_operand_types(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    operand: TypeId,
) -> Result<(TypeId, TypeId), SourceCheckError> {
    let flags = store
        .type_payload(operand)
        .map(TypeRecord::flags)
        .ok_or(DerivedTypeError::Type(operand))?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(DerivedTypeError::BootstrapUninitialized)?;
    let base = if flags.intersects(TypeFlags::STRING_LITERAL) {
        bootstrap.string_type
    } else if flags.intersects(TypeFlags::NUMBER_LITERAL) {
        bootstrap.number_type
    } else if flags.intersects(TypeFlags::BIG_INT_LITERAL) {
        bootstrap.bigint_type
    } else if flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
        bootstrap.boolean_type
    } else {
        operand
    };
    let regular = store.get_regular_type_of_object_literal(base)?;
    let widened = store.get_widened_type_with_global_types(regular, global_types)?;
    Ok((regular, widened))
}

fn check_deferred_assertions(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    deferred: &[DeferredAssertion],
) -> Result<(), SourceCheckError> {
    let mut flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
    if options.no_error_truncation {
        flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
    }
    for assertion in deferred {
        session.reset_query();
        let (operand, widened) =
            assertion_operand_types(store, global_types, assertion.operand_type)?;
        if store.are_types_comparable_with_global_types(
            assertion.target_type,
            widened,
            global_types,
        )? {
            continue;
        }
        let display = get_type_names_for_assignability_error_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            operand,
            assertion.target_type,
            flags,
        )?;
        let diagnostic = Diagnostic::with_arguments(
            message_by_code(2352).ok_or(SourceCheckError::MissingDiagnostic(2352))?,
            [display.source, display.target],
        );
        merge_retry_diagnostic(
            diagnostics,
            CanonicalCheckerDiagnostic {
                node: Some(assertion.node),
                range_override: None,
                diagnostic,
                related_information: Vec::new(),
            },
        );
    }
    Ok(())
}

pub(super) fn merge_retry_diagnostic(
    destination: &mut CanonicalCheckerDiagnostics,
    diagnostic: CanonicalCheckerDiagnostic,
) {
    let CanonicalCheckerDiagnostic {
        node,
        range_override,
        diagnostic,
        related_information,
    } = diagnostic;
    let entry = destination.lookup_primary_or_issue(node, range_override, diagnostic);
    for related in related_information {
        if !entry.related_information.contains(&related) {
            entry.append_related(related);
        }
    }
}

pub(super) fn merge_retry_diagnostics(
    destination: &mut CanonicalCheckerDiagnostics,
    source: CanonicalCheckerDiagnostics,
) {
    for diagnostic in source.into_vec() {
        merge_retry_diagnostic(destination, diagnostic);
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CheckedAssignment {
    declared_type: TypeId,
    assigned_type: TypeId,
}

#[allow(clippy::too_many_arguments)] // Keeps the source execution capabilities explicit.
fn check_planned_assignment(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    flow_types: &HashMap<SemanticSymbolId, TypeId>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    deferred: &mut Vec<DeferredAssertion>,
    target_type_node: NodeRef,
    type_reference_alias_targets: &[CanonicalTypeReferenceAliasTarget],
    expression: &PlannedExpression,
    fallback_node: NodeRef,
    assignment_expression: Option<NodeRef>,
) -> Result<CheckedAssignment, SourceCheckError> {
    let mut statement_diagnostics = CanonicalCheckerDiagnostics::default();
    let target = CanonicalTypeQuery::new_with_global_types_and_session(
        store,
        host,
        global_types,
        options,
        session,
        &mut statement_diagnostics,
    )?
    .with_type_reference_alias_targets(type_reference_alias_targets.iter().copied())?
    .get_type_from_type_node(target_type_node);
    merge_retry_diagnostics(diagnostics, statement_diagnostics);
    let target = target?;
    check_assignment_to_type(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        flow_types,
        preflighted_type_import_value_uses,
        deferred,
        target,
        expression,
        fallback_node,
        assignment_expression,
    )
}

#[allow(clippy::too_many_arguments)] // Shares exact assignment checks across TS and JSDoc types.
fn check_assignment_to_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    flow_types: &HashMap<SemanticSymbolId, TypeId>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    deferred: &mut Vec<DeferredAssertion>,
    target: TypeId,
    expression: &PlannedExpression,
    fallback_node: NodeRef,
    assignment_expression: Option<NodeRef>,
) -> Result<CheckedAssignment, SourceCheckError> {
    if assignment_expression.is_some() {
        publish_expression_type(store, fallback_node, target)?;
    }
    let source_types = check_expression_type(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        flow_types,
        preflighted_type_import_value_uses,
        expression,
        Some(target),
        deferred,
    )?;
    if let Some(assignment_expression) = assignment_expression {
        publish_expression_type(store, assignment_expression, source_types.result)?;
    }
    let source_type = source_types.result;
    let assignable = source_type_is_assignable_to(
        store,
        host,
        global_types,
        options,
        session,
        diagnostics,
        source_type,
        target,
    )?;
    if !assignable {
        let staged = super::object_diagnostics::diagnostics_for_failed_assignment(
            store,
            host,
            global_types,
            expression,
            &source_types,
            target,
            fallback_node,
            options,
            session,
        )?;
        for diagnostic in staged {
            merge_retry_diagnostic(diagnostics, diagnostic);
        }
    }
    Ok(CheckedAssignment {
        declared_type: target,
        assigned_type: source_type,
    })
}

#[allow(clippy::too_many_arguments)] // Reuses the caller's checker state and instantiation session.
fn source_type_is_assignable_to(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    source: TypeId,
    target: TypeId,
) -> Result<bool, SourceCheckError> {
    let mut resolved_signatures = HashSet::new();
    let mut resolved_members = HashSet::new();
    let mut resolved_properties = HashSet::new();
    loop {
        match store.is_type_assignable_to_with_global_types_and_strict_function_types(
            source,
            target,
            global_types,
            options.strict_function_types,
        ) {
            Ok(assignable) => return Ok(assignable),
            Err(RelationUnavailable::UnresolvedSignatureReturn(signature)) => {
                if !resolved_signatures.insert(signature) {
                    return Err(RelationUnavailable::UnresolvedSignatureReturn(signature).into());
                }
                let mut resolution_diagnostics = CanonicalCheckerDiagnostics::default();
                let resolved = CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    &mut resolution_diagnostics,
                )?
                .get_return_type_of_signature(signature);
                merge_retry_diagnostics(diagnostics, resolution_diagnostics);
                resolved?;
            }
            Err(
                error @ (RelationUnavailable::UnresolvedStructuredMembers(_)
                | RelationUnavailable::UnresolvedPropertyType(_)),
            ) => {
                retry_source_generic_member_failure(
                    store,
                    global_types,
                    session,
                    error,
                    &[source, target],
                    &mut resolved_members,
                    &mut resolved_properties,
                )?;
            }
            Err(error) => return Err(error.into()),
        }
    }
}

fn retry_source_generic_member_failure(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    error: RelationUnavailable,
    candidates: &[TypeId],
    resolved_members: &mut HashSet<TypeId>,
    resolved_properties: &mut HashSet<SemanticSymbolId>,
) -> Result<(), SourceCheckError> {
    let array_targets = Some(CanonicalArrayTargets::from_global_types(global_types));
    match error {
        RelationUnavailable::UnresolvedStructuredMembers(type_) => {
            if !resolved_members.insert(type_)
                || super::instantiated_members::resolve_members_with_array_targets(
                    store,
                    type_,
                    array_targets,
                )
                .is_err()
            {
                return Err(error.into());
            }
        }
        RelationUnavailable::UnresolvedPropertyType(symbol) => {
            if !resolved_properties.insert(symbol) {
                return Err(error.into());
            }
            let reference = candidates.iter().copied().find(|candidate| {
                super::instantiated_members::validate_generic_interface_members(
                    store,
                    *candidate,
                    array_targets,
                )
                .ok()
                .flatten()
                .is_some_and(|members| members.properties().contains(&symbol))
            });
            let Some(reference) = reference else {
                return Err(error.into());
            };
            if super::instantiated_members::demand_instantiated_property_type(
                store,
                reference,
                symbol,
                array_targets,
                session,
            )
            .is_err()
            {
                return Err(error.into());
            }
        }
        _ => return Err(error.into()),
    }
    Ok(())
}

fn callable_parameter_execution_error(
    callable: &SourceCallablePlan,
    parameter: NodeRef,
) -> SourceCheckError {
    match callable.family {
        SourceCallableFamily::FunctionDeclaration => {
            SourceCheckError::Function(SourceFunctionInvariant::Callable(parameter))
        }
        SourceCallableFamily::ArrowFunction => SourceCheckError::Arrow(parameter),
    }
}

fn issue_implicit_any_parameter_diagnostics(
    arena: &NodeArena,
    host: &DeclaredTypeHost<'_>,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    callable: &SourceCallablePlan,
    javascript_jsdoc: Option<&PlannedJavaScriptJsDoc>,
) -> Result<(), SourceCheckError> {
    for parameter in &callable.parameters {
        if !parameter.is_implicit_any() {
            continue;
        }
        let record = host
            .node(parameter.declaration)
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingNode(parameter.declaration),
            ))?;
        let NodeData::ParameterDeclaration(declaration) = &record.data else {
            return Err(callable_parameter_execution_error(
                callable,
                parameter.declaration,
            ));
        };
        let name = NodeRef::new(
            parameter.declaration.arena,
            parameter.declaration.file,
            declaration.name,
        );
        let name_record = host.node(name).ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingNode(name),
        ))?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(callable_parameter_execution_error(
                callable,
                parameter.declaration,
            ));
        };
        let has_jsdoc_annotation = javascript_jsdoc
            .and_then(|plan| plan.callable_declaration(arena, callable.declaration))
            .and_then(|declaration| declaration.parameter(&identifier.text))
            .and_then(super::jsdoc::PlannedJsDocParameter::type_)
            .is_some();
        if has_jsdoc_annotation {
            continue;
        }
        merge_retry_diagnostic(
            diagnostics,
            CanonicalCheckerDiagnostic {
                node: Some(parameter.declaration),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(7006).ok_or(SourceCheckError::MissingDiagnostic(7006))?,
                    [identifier.text.clone(), "any".to_owned()],
                ),
                related_information: Vec::new(),
            },
        );
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)] // Mirrors expression execution with an explicit flow scope.
fn check_callable_parameter_initializers(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    outer_flow_types: &HashMap<SemanticSymbolId, TypeId>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    deferred: &mut Vec<DeferredAssertion>,
    callable: &SourceCallablePlan,
    initializers: &[PlannedParameterInitializer],
) -> Result<HashMap<SemanticSymbolId, TypeId>, SourceCheckError> {
    let mut flow_types = outer_flow_types.clone();
    let mut initializer_index = 0usize;
    for parameter in &callable.parameters {
        let body_type = store
            .value_symbol_links(parameter.symbol)
            .and_then(|links| links.resolved_type)
            .ok_or(SourceCheckError::Variable(
                VariableInvariant::MissingCurrentFlowType(parameter.symbol),
            ))?;
        if let Some(initializer) = parameter.initializer {
            let planned = initializers.get(initializer_index).ok_or_else(|| {
                callable_parameter_execution_error(callable, parameter.declaration)
            })?;
            if planned.parameter != *parameter || planned.expression.node != initializer {
                return Err(callable_parameter_execution_error(
                    callable,
                    parameter.declaration,
                ));
            }
            let assignment = check_planned_assignment(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                &flow_types,
                preflighted_type_import_value_uses,
                deferred,
                parameter.type_node,
                &[],
                &planned.expression,
                parameter.declaration,
                None,
            )?;
            if assignment.declared_type != body_type {
                return Err(callable_parameter_execution_error(
                    callable,
                    parameter.declaration,
                ));
            }
            initializer_index += 1;
        }
        if flow_types.insert(parameter.symbol, body_type).is_some() {
            return Err(SourceCheckError::Variable(
                VariableInvariant::DuplicateCurrentFlowType(parameter.symbol),
            ));
        }
    }
    if initializer_index != initializers.len() {
        return Err(callable_parameter_execution_error(
            callable,
            callable.declaration,
        ));
    }
    Ok(flow_types)
}

#[allow(clippy::too_many_arguments)] // Reuses the existing source flow and publication transaction.
fn check_planned_linear_function_statements(
    bound: &BoundFile,
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    base_flow_types: HashMap<SemanticSymbolId, TypeId>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    type_import_capabilities: &HashMap<NodeRef, Vec<CanonicalTypeReferenceAliasTarget>>,
    deferred: &mut Vec<DeferredAssertion>,
    callable: &SourceCallablePlan,
    return_type: Option<NodeRef>,
    statements: &PlannedLinearFunctionStatements,
    staged_value_types: &mut HashMap<SemanticSymbolId, TypeId>,
    value_order: &mut Vec<SemanticSymbolId>,
) -> Result<HashMap<SemanticSymbolId, TypeId>, SourceCheckError> {
    let mut frame = statements
        .flow
        .frame(bound, base_flow_types.clone())
        .map_err(|error| SourcePlanner::source_flow_plan_error(callable, error))?;
    check_planned_function_locals(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        &mut frame,
        preflighted_type_import_value_uses,
        type_import_capabilities,
        deferred,
        callable,
        &statements.locals,
        staged_value_types,
        value_order,
    )?;

    let Some(return_statement) = statements.return_statement else {
        if statements.return_expression.is_some() {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(callable.declaration),
            ));
        }
        return Ok(base_flow_types);
    };
    let snapshot = frame
        .snapshot_at(store, global_types, return_statement)
        .map_err(|error| SourcePlanner::source_flow_plan_error(callable, error))?;
    if let (Some(return_type), Some(expression)) =
        (return_type, statements.return_expression.as_ref())
    {
        session.reset_query();
        check_planned_assignment(
            store,
            host,
            global_types,
            source,
            options,
            session,
            diagnostics,
            snapshot.types(),
            preflighted_type_import_value_uses,
            deferred,
            return_type,
            &[],
            expression,
            return_statement,
            None,
        )?;
    }
    Ok(snapshot.types().clone())
}

#[allow(clippy::too_many_arguments)]
fn check_planned_function_statements(
    bound: &BoundFile,
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    base_flow_types: HashMap<SemanticSymbolId, TypeId>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    type_import_capabilities: &HashMap<NodeRef, Vec<CanonicalTypeReferenceAliasTarget>>,
    deferred: &mut Vec<DeferredAssertion>,
    callable: &SourceCallablePlan,
    return_type: NodeRef,
    statements: &PlannedFunctionStatements,
    staged_value_types: &mut HashMap<SemanticSymbolId, TypeId>,
    value_order: &mut Vec<SemanticSymbolId>,
) -> Result<(), SourceCheckError> {
    let mut frame = statements
        .flow
        .frame(bound, base_flow_types)
        .map_err(|error| SourcePlanner::source_flow_plan_error(callable, error))?;
    check_planned_function_locals(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        &mut frame,
        preflighted_type_import_value_uses,
        type_import_capabilities,
        deferred,
        callable,
        &statements.leading,
        staged_value_types,
        value_order,
    )?;

    check_planned_source_condition(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        &mut frame,
        preflighted_type_import_value_uses,
        deferred,
        callable,
        &statements.condition,
    )?;

    check_planned_return_branch(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        &mut frame,
        preflighted_type_import_value_uses,
        type_import_capabilities,
        deferred,
        callable,
        return_type,
        &statements.then_branch,
        staged_value_types,
        value_order,
    )?;
    check_planned_return_branch(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        &mut frame,
        preflighted_type_import_value_uses,
        type_import_capabilities,
        deferred,
        callable,
        return_type,
        &statements.else_branch,
        staged_value_types,
        value_order,
    )
}

#[allow(clippy::too_many_arguments)]
fn check_planned_joined_function_statements(
    bound: &BoundFile,
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    base_flow_types: HashMap<SemanticSymbolId, TypeId>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    type_import_capabilities: &HashMap<NodeRef, Vec<CanonicalTypeReferenceAliasTarget>>,
    deferred: &mut Vec<DeferredAssertion>,
    callable: &SourceCallablePlan,
    return_type: NodeRef,
    statements: &PlannedJoinedFunctionStatements,
    staged_value_types: &mut HashMap<SemanticSymbolId, TypeId>,
    value_order: &mut Vec<SemanticSymbolId>,
) -> Result<(), SourceCheckError> {
    let mut frame = statements
        .flow
        .frame(bound, base_flow_types)
        .map_err(|error| SourcePlanner::source_flow_plan_error(callable, error))?;
    check_planned_function_locals(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        &mut frame,
        preflighted_type_import_value_uses,
        type_import_capabilities,
        deferred,
        callable,
        &statements.leading,
        staged_value_types,
        value_order,
    )?;
    check_planned_source_condition(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        &mut frame,
        preflighted_type_import_value_uses,
        deferred,
        callable,
        &statements.condition,
    )?;
    check_planned_function_locals(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        &mut frame,
        preflighted_type_import_value_uses,
        type_import_capabilities,
        deferred,
        callable,
        &statements.then_branch.locals,
        staged_value_types,
        value_order,
    )?;
    check_planned_function_locals(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        &mut frame,
        preflighted_type_import_value_uses,
        type_import_capabilities,
        deferred,
        callable,
        &statements.else_branch.locals,
        staged_value_types,
        value_order,
    )?;
    check_planned_function_locals(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        &mut frame,
        preflighted_type_import_value_uses,
        type_import_capabilities,
        deferred,
        callable,
        &statements.trailing,
        staged_value_types,
        value_order,
    )?;
    let snapshot = frame
        .snapshot_at(store, global_types, statements.return_statement)
        .map_err(|error| SourcePlanner::source_flow_plan_error(callable, error))?;
    session.reset_query();
    check_planned_assignment(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        snapshot.types(),
        preflighted_type_import_value_uses,
        deferred,
        return_type,
        &[],
        &statements.return_expression,
        statements.return_statement,
        None,
    )?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_planned_source_condition(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    frame: &mut SourceFlowFrame<'_, '_>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    deferred: &mut Vec<DeferredAssertion>,
    callable: &SourceCallablePlan,
    condition: &PlannedSourceCondition,
) -> Result<(), SourceCheckError> {
    match condition {
        PlannedSourceCondition::Truthiness { expression, symbol } => {
            check_planned_truthiness_condition(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                frame,
                preflighted_type_import_value_uses,
                deferred,
                callable,
                expression,
                *symbol,
            )
        }
        PlannedSourceCondition::Typeof(condition) => check_planned_typeof_condition(
            store,
            host,
            global_types,
            source,
            options,
            session,
            diagnostics,
            frame,
            preflighted_type_import_value_uses,
            deferred,
            callable,
            condition,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn check_planned_truthiness_condition(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    frame: &mut SourceFlowFrame<'_, '_>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    deferred: &mut Vec<DeferredAssertion>,
    callable: &SourceCallablePlan,
    condition: &PlannedExpression,
    condition_symbol: SemanticSymbolId,
) -> Result<(), SourceCheckError> {
    let condition_flow = frame
        .snapshot_at(store, global_types, condition.unparenthesized().node)
        .map_err(|error| SourcePlanner::source_flow_plan_error(callable, error))?;
    let checked = check_expression_type(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        condition_flow.types(),
        preflighted_type_import_value_uses,
        condition,
        None,
        deferred,
    )?;
    if condition_flow.type_of(condition_symbol) != Some(checked.raw)
        || !source_truthiness_condition_type_is_supported(
            store,
            checked.result,
            condition.node,
            &mut HashSet::new(),
        )?
    {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::FunctionBody(
                callable.body,
            )),
        ));
    }
    emit_truthiness_operand_diagnostics(
        store,
        host,
        diagnostics,
        condition,
        checked.result,
        condition.node,
    )?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_planned_typeof_condition(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    frame: &mut SourceFlowFrame<'_, '_>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    deferred: &mut Vec<DeferredAssertion>,
    callable: &SourceCallablePlan,
    condition: &PlannedTypeofCondition,
) -> Result<(), SourceCheckError> {
    let condition_flow = frame
        .snapshot_at(store, global_types, condition.identifier.node)
        .map_err(|error| SourcePlanner::source_flow_plan_error(callable, error))?;
    let current = condition_flow
        .type_of(condition.symbol)
        .ok_or(SourceCheckError::Variable(
            VariableInvariant::MissingCurrentFlowType(condition.symbol),
        ))?;
    let supported =
        source_typeof_narrowing_type_is_supported(store, global_types, current, condition.tag)
            .map_err(|_| {
                SourceCheckError::Function(SourceFunctionInvariant::Callable(callable.declaration))
            })?;
    if !supported {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::FunctionBody(
                callable.body,
            )),
        ));
    }
    let (typeof_type, boolean_type) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| (bootstrap.typeof_type, bootstrap.boolean_type))
        .ok_or(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::BootstrapUninitialized,
        ))?;

    if condition.type_of_on_left {
        let identifier = check_expression_type(
            store,
            host,
            global_types,
            source,
            options,
            session,
            diagnostics,
            condition_flow.types(),
            preflighted_type_import_value_uses,
            &condition.identifier,
            None,
            deferred,
        )?;
        if identifier.raw != current {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(callable.declaration),
            ));
        }
        publish_expression_type(store, condition.type_of_expression, typeof_type)?;
        check_expression_type(
            store,
            host,
            global_types,
            source,
            options,
            session,
            diagnostics,
            condition_flow.types(),
            preflighted_type_import_value_uses,
            &condition.literal,
            None,
            deferred,
        )?;
    } else {
        check_expression_type(
            store,
            host,
            global_types,
            source,
            options,
            session,
            diagnostics,
            condition_flow.types(),
            preflighted_type_import_value_uses,
            &condition.literal,
            None,
            deferred,
        )?;
        let identifier = check_expression_type(
            store,
            host,
            global_types,
            source,
            options,
            session,
            diagnostics,
            condition_flow.types(),
            preflighted_type_import_value_uses,
            &condition.identifier,
            None,
            deferred,
        )?;
        if identifier.raw != current {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(callable.declaration),
            ));
        }
        publish_expression_type(store, condition.type_of_expression, typeof_type)?;
    }
    publish_expression_type(store, condition.expression, boolean_type)
}

fn source_truthiness_condition_type_is_supported(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    invariant_node: NodeRef,
    visiting: &mut HashSet<TypeId>,
) -> Result<bool, SourceCheckError> {
    let (flags, named_promise, union_types) = {
        let record = store
            .type_payload(type_)
            .ok_or(SourceCheckError::LogicalOperator(invariant_node))?;
        let named_promise = record
            .symbol()
            .and_then(|symbol| store.symbol(symbol))
            .is_some_and(|symbol| matches!(symbol.name().as_bytes(), b"Promise" | b"PromiseLike"));
        let union_types = match record.data() {
            TypeData::Union(union) => Some(union.union.types.clone()),
            _ => None,
        };
        (record.flags(), named_promise, union_types)
    };
    if flags.intersects(TypeFlags::UNKNOWN | TypeFlags::TYPE_PARAMETER | TypeFlags::INTERSECTION) {
        return Ok(false);
    }
    if named_promise {
        return Ok(false);
    }
    if !matches!(
        validate_stored_single_callable(store, type_),
        StoredSingleCallableValidation::NotCallable
    ) {
        return Ok(false);
    }
    match validate_resolved_declared_property_object(store, type_) {
        DeclaredPropertyObjectValidation::Valid(_) => {
            if store.resolved_own_property(type_, "then")?.is_some() {
                // The pinned checker diagnoses promise-shaped structural
                // values with TS2801. Until that diagnostic path is ported,
                // keep exact own `then` properties outside this condition
                // slice rather than accepting a thenable as an ordinary
                // known-truthy object.
                return Ok(false);
            }
        }
        DeclaredPropertyObjectValidation::NotDeclared => {
            // Other structured objects can expose inherited or apparent
            // callable `then` members. General property lookup is not yet in
            // the canonical source condition path, so accepting them here
            // would fail open for structural promises. Intrinsic `object` is
            // NON_PRIMITIVE rather than OBJECT and remains supported.
            if flags.intersects(TypeFlags::OBJECT) {
                return Ok(false);
            }
        }
        DeclaredPropertyObjectValidation::Malformed => {
            return Err(SourceCheckError::LogicalOperator(invariant_node));
        }
    }
    let Some(union_types) = union_types else {
        return Ok(true);
    };
    if !visiting.insert(type_) {
        return Ok(false);
    }
    for constituent in union_types {
        if !source_truthiness_condition_type_is_supported(
            store,
            constituent,
            invariant_node,
            visiting,
        )? {
            visiting.remove(&type_);
            return Ok(false);
        }
    }
    visiting.remove(&type_);
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn check_planned_function_locals(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    frame: &mut SourceFlowFrame<'_, '_>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    type_import_capabilities: &HashMap<NodeRef, Vec<CanonicalTypeReferenceAliasTarget>>,
    deferred: &mut Vec<DeferredAssertion>,
    callable: &SourceCallablePlan,
    locals: &[PlannedVariable],
    staged_value_types: &mut HashMap<SemanticSymbolId, TypeId>,
    value_order: &mut Vec<SemanticSymbolId>,
) -> Result<(), SourceCheckError> {
    for local in locals {
        let PlannedVariableInitializer::Expression(initializer) = &local.initializer else {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidSymbolShape(local.symbol),
            ));
        };
        session.reset_query();
        let snapshot = frame
            .snapshot_at(store, global_types, local.name)
            .map_err(|error| SourcePlanner::source_flow_plan_error(callable, error))?;
        let (declared_type, current_type) = if let Some(type_node) = local.type_node {
            let assignment = check_planned_assignment(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                snapshot.types(),
                preflighted_type_import_value_uses,
                deferred,
                type_node,
                type_import_capabilities
                    .get(&type_node)
                    .map_or(&[], Vec::as_slice),
                initializer,
                local.name,
                None,
            )?;
            (
                assignment.declared_type,
                current_flow_type_after_assignment(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    assignment,
                )?,
            )
        } else {
            let initializer = check_expression_type(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                snapshot.types(),
                preflighted_type_import_value_uses,
                initializer,
                None,
                deferred,
            )?;
            let declared_type =
                inferred_variable_type(store, global_types, local.binding, initializer.result)?;
            let current_type = current_flow_type_after_assignment(
                store,
                host,
                global_types,
                options,
                session,
                diagnostics,
                CheckedAssignment {
                    declared_type,
                    assigned_type: initializer.result,
                },
            )?;
            (declared_type, current_type)
        };
        stage_value_type(
            store,
            staged_value_types,
            value_order,
            local.symbol,
            declared_type,
        )?;
        frame
            .complete_assignment(local.declaration, local.symbol, current_type)
            .map_err(|error| SourcePlanner::source_flow_plan_error(callable, error))?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_planned_return_branch(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    frame: &mut SourceFlowFrame<'_, '_>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    type_import_capabilities: &HashMap<NodeRef, Vec<CanonicalTypeReferenceAliasTarget>>,
    deferred: &mut Vec<DeferredAssertion>,
    callable: &SourceCallablePlan,
    return_type: NodeRef,
    branch: &PlannedReturnBranch,
    staged_value_types: &mut HashMap<SemanticSymbolId, TypeId>,
    value_order: &mut Vec<SemanticSymbolId>,
) -> Result<(), SourceCheckError> {
    check_planned_function_locals(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        frame,
        preflighted_type_import_value_uses,
        type_import_capabilities,
        deferred,
        callable,
        &branch.locals,
        staged_value_types,
        value_order,
    )?;
    let snapshot = frame
        .snapshot_at(store, global_types, branch.return_statement)
        .map_err(|error| SourcePlanner::source_flow_plan_error(callable, error))?;
    session.reset_query();
    check_planned_assignment(
        store,
        host,
        global_types,
        source,
        options,
        session,
        diagnostics,
        snapshot.types(),
        preflighted_type_import_value_uses,
        deferred,
        return_type,
        &[],
        &branch.return_expression,
        branch.return_statement,
        None,
    )?;
    Ok(())
}

fn current_flow_type_after_assignment(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    assignment: CheckedAssignment,
) -> Result<TypeId, SourceCheckError> {
    let CheckedAssignment {
        declared_type,
        assigned_type,
    } = assignment;
    if declared_type == assigned_type {
        return Ok(declared_type);
    }
    let declared_record = store
        .type_payload(declared_type)
        .ok_or(RelationUnavailable::Type(declared_type))?;
    if !declared_record.flags().intersects(TypeFlags::UNION) {
        return Ok(declared_type);
    }
    let assigned_flags = store
        .type_payload(assigned_type)
        .map(TypeRecord::flags)
        .ok_or(RelationUnavailable::Type(assigned_type))?;
    if assigned_flags.intersects(TypeFlags::NEVER) {
        return Ok(assigned_type);
    }
    let TypeData::Union(declared_union) = declared_record.data() else {
        return Err(RelationUnavailable::MalformedUnion(declared_type).into());
    };
    let declared_constituents = declared_union.union.types.clone();
    let declared_origin = declared_union.origin;
    store
        .validate_union_constituent_with_global_types(global_types, declared_type)
        .map_err(|error| super::relater::union_validation_unavailable(declared_type, error))?;

    let assigned_constituents = match store.type_payload(assigned_type) {
        Some(record) if record.flags().intersects(TypeFlags::UNION) => {
            let TypeData::Union(union) = record.data() else {
                return Err(RelationUnavailable::MalformedUnion(assigned_type).into());
            };
            let constituents = union.union.types.clone();
            store
                .validate_union_constituent_with_global_types(global_types, assigned_type)
                .map_err(|error| {
                    super::relater::union_validation_unavailable(assigned_type, error)
                })?;
            constituents
        }
        Some(_) => vec![assigned_type],
        None => return Err(RelationUnavailable::Type(assigned_type).into()),
    };

    let mut reduced = Vec::with_capacity(declared_constituents.len());
    for target in &declared_constituents {
        if assignment_type_maybe_assignable_to(
            store,
            host,
            global_types,
            options,
            session,
            diagnostics,
            &assigned_constituents,
            *target,
        )? {
            reduced.push(*target);
        }
    }
    if reduced.is_empty() {
        return Ok(declared_type);
    }
    let filtered = filtered_assignment_union_type(
        store,
        host,
        global_types,
        options,
        session,
        diagnostics,
        declared_type,
        &declared_constituents,
        declared_origin,
        &assigned_constituents,
        &reduced,
    )?;
    let candidate = if is_fresh_boolean_literal(store, assigned_type)? {
        map_fresh_boolean_type(store, global_types, filtered)?
    } else {
        filtered
    };
    if source_type_is_assignable_to(
        store,
        host,
        global_types,
        options,
        session,
        diagnostics,
        assigned_type,
        candidate,
    )? {
        Ok(candidate)
    } else {
        Ok(declared_type)
    }
}

#[allow(clippy::too_many_arguments)] // Preserves the caller's complete flow and relation context.
fn assignment_type_maybe_assignable_to(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    assigned_constituents: &[TypeId],
    target: TypeId,
) -> Result<bool, SourceCheckError> {
    for source in assigned_constituents {
        if is_definitely_unassignable_to_structured(store, *source, target)? {
            continue;
        }
        if source_type_is_assignable_to(
            store,
            host,
            global_types,
            options,
            session,
            diagnostics,
            *source,
            target,
        )? {
            return Ok(true);
        }
    }
    Ok(false)
}

#[allow(clippy::too_many_arguments)]
fn filtered_assignment_union_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    declared_type: TypeId,
    declared_constituents: &[TypeId],
    declared_origin: Option<TypeId>,
    assigned_constituents: &[TypeId],
    reduced: &[TypeId],
) -> Result<TypeId, SourceCheckError> {
    if reduced.len() == declared_constituents.len() {
        return Ok(declared_type);
    }

    if let Some(origin) = declared_origin {
        let origin_record = store
            .type_payload(origin)
            .ok_or(RelationUnavailable::Type(origin))?;
        let TypeData::Union(origin_union) = origin_record.data() else {
            return Err(RelationUnavailable::MalformedUnion(origin).into());
        };
        let origin_constituents = origin_union.union.types.clone();
        let mut filtered_origin = Vec::with_capacity(origin_constituents.len());
        for constituent in &origin_constituents {
            let flags = store
                .type_payload(*constituent)
                .map(TypeRecord::flags)
                .ok_or(RelationUnavailable::Type(*constituent))?;
            if flags.intersects(TypeFlags::UNION)
                || assignment_type_maybe_assignable_to(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    assigned_constituents,
                    *constituent,
                )?
            {
                filtered_origin.push(*constituent);
            }
        }
        if origin_constituents.len() - filtered_origin.len()
            == declared_constituents.len() - reduced.len()
        {
            return store
                .expression_union_type_with_global_types(
                    global_types,
                    &filtered_origin,
                    UnionReduction::None,
                )
                .map_err(Into::into);
        }
    }

    store
        .expression_union_type_with_global_types(global_types, reduced, UnionReduction::None)
        .map_err(Into::into)
}

fn map_fresh_boolean_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    type_: TypeId,
) -> Result<TypeId, SourceCheckError> {
    let record = store
        .type_payload(type_)
        .ok_or(RelationUnavailable::Type(type_))?;
    let TypeData::Union(union) = record.data() else {
        return fresh_literal_reduction_constituent(store, type_);
    };
    let constituents = if let Some(origin) = union.origin {
        let origin_record = store
            .type_payload(origin)
            .ok_or(RelationUnavailable::Type(origin))?;
        let TypeData::Union(origin_union) = origin_record.data() else {
            return Err(RelationUnavailable::MalformedUnion(origin).into());
        };
        origin_union.union.types.clone()
    } else {
        union.union.types.clone()
    };
    let mut mapped = Vec::with_capacity(constituents.len());
    let mut changed = false;
    for constituent in constituents {
        let mapped_constituent = map_fresh_boolean_type(store, global_types, constituent)?;
        changed |= mapped_constituent != constituent;
        mapped.push(mapped_constituent);
    }
    if !changed {
        return Ok(type_);
    }
    store
        .expression_union_type_with_global_types(global_types, &mapped, UnionReduction::Literal)
        .map_err(Into::into)
}

fn fresh_literal_reduction_constituent(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<TypeId, SourceCheckError> {
    let record = store
        .type_payload(type_)
        .ok_or(RelationUnavailable::Type(type_))?;
    let TypeData::Literal(literal) = record.data() else {
        return Ok(type_);
    };
    store.validate_union_constituent(type_)?;
    if literal.regular_type == type_ {
        return store.fresh_type_of_literal_type(type_).map_err(Into::into);
    }
    if literal.fresh_type == Some(type_) {
        return Ok(type_);
    }
    Err(SourceCheckError::LiteralCache(
        SourceLiteralCacheError::InvalidCachedLiteral(type_),
    ))
}

fn is_definitely_unassignable_to_structured(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
) -> Result<bool, SourceCheckError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    let source_flags = store
        .type_payload(source)
        .map(TypeRecord::flags)
        .ok_or(RelationUnavailable::Type(source))?;
    let target_flags = store
        .type_payload(target)
        .map(TypeRecord::flags)
        .ok_or(RelationUnavailable::Type(target))?;
    if target_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
        && (source_flags.intersects(TypeFlags::VOID)
            || (bootstrap.options.strict_null_checks
                && source_flags.intersects(TypeFlags::NULLABLE)))
    {
        store.validate_union_constituent(source)?;
        return Ok(true);
    }
    Ok(false)
}

fn is_fresh_boolean_literal(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<bool, SourceCheckError> {
    let Some(record) = store.type_payload(type_) else {
        return Err(RelationUnavailable::Type(type_).into());
    };
    let TypeData::Literal(literal) = record.data() else {
        return Ok(false);
    };
    if !record.flags().intersects(TypeFlags::BOOLEAN_LITERAL)
        || literal.fresh_type != Some(type_)
        || literal.regular_type == type_
    {
        return Ok(false);
    }
    store.validate_union_constituent(type_)?;
    Ok(true)
}

fn inferred_variable_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    binding: VariableBindingKind,
    initializer_type: TypeId,
) -> Result<TypeId, SourceCheckError> {
    let initializer_type = if binding.is_const() {
        initializer_type
    } else {
        widened_fresh_literal_type(store, initializer_type)?
    };
    store
        .get_widened_type_with_global_types(initializer_type, global_types)
        .map_err(Into::into)
}

fn stage_value_type(
    store: &CanonicalTypeMapperStore,
    value_types: &mut HashMap<SemanticSymbolId, TypeId>,
    value_order: &mut Vec<SemanticSymbolId>,
    symbol: SemanticSymbolId,
    expected: TypeId,
) -> Result<(), SourceCheckError> {
    if let Some(cached) = store
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        && cached != expected
    {
        return Err(SourceCheckError::Variable(
            VariableInvariant::CachedValueTypeMismatch {
                symbol,
                cached,
                expected,
            },
        ));
    }
    if value_types.insert(symbol, expected).is_some() {
        return Err(SourceCheckError::Variable(
            VariableInvariant::DuplicateStagedValueType(symbol),
        ));
    }
    value_order.push(symbol);
    Ok(())
}

fn publish_staged_variable_state(
    store: &mut CanonicalTypeMapperStore,
    source: NodeRef,
    value_types: &HashMap<SemanticSymbolId, TypeId>,
    value_order: &[SemanticSymbolId],
    import_publications: &[PreparedSourceImportPublication],
    identifier_reads: &[(NodeRef, SemanticSymbolId)],
) -> Result<(), SourceCheckError> {
    // Build and validate every eventual setter payload before the first sparse
    // variable/reference link is published. The store setters below can then
    // only reject if their validated ownership predicates change in place.
    let mut seen_values = HashSet::with_capacity(value_order.len());
    let mut local_value_publications: Vec<(SemanticSymbolId, ValueSymbolLinks)> =
        Vec::with_capacity(value_order.len());
    for &symbol in value_order {
        if !seen_values.insert(symbol) {
            return Err(SourceCheckError::Variable(
                VariableInvariant::DuplicateStagedValueType(symbol),
            ));
        }
        let resolved_type = *value_types.get(&symbol).ok_or(SourceCheckError::Variable(
            VariableInvariant::MissingStagedValueType(symbol),
        ))?;
        if store.symbol(symbol).is_none() || store.type_payload(resolved_type).is_none() {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidStagedValueType {
                    symbol,
                    type_: resolved_type,
                },
            ));
        }
        let mut links = store
            .value_symbol_links(symbol)
            .cloned()
            .unwrap_or_default();
        if links.write_type.is_some()
            || links.target.is_some()
            || links.mapper.is_some()
            || links.name_type.is_some()
            || links.containing_type.is_some()
            || links.function_or_constructor_checked
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidValueLinks(symbol),
            ));
        }
        if let Some(cached) = links.resolved_type
            && cached != resolved_type
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::CachedValueTypeMismatch {
                    symbol,
                    cached,
                    expected: resolved_type,
                },
            ));
        }
        links.resolved_type = Some(resolved_type);
        local_value_publications.push((symbol, links));
    }
    if value_types.len() != seen_values.len() {
        let symbol = value_types
            .keys()
            .copied()
            .find(|symbol| !seen_values.contains(symbol))
            .expect("different staged value-map and order lengths imply an extra map key");
        return Err(SourceCheckError::Variable(
            VariableInvariant::UnexpectedStagedValueType(symbol),
        ));
    }

    let mut all_value_symbols =
        HashSet::with_capacity(import_publications.len() + local_value_publications.len());
    let mut value_publications =
        Vec::with_capacity(import_publications.len() + local_value_publications.len());
    for publication in import_publications {
        let Some(type_) = publication.links.resolved_type else {
            return Err(SourceCheckError::Import(source));
        };
        if !all_value_symbols.insert(publication.symbol)
            || store.symbol(publication.symbol).is_none()
            || store.type_payload(type_).is_none()
        {
            return Err(SourceCheckError::Import(source));
        }
        value_publications.push((publication.symbol, publication.links.clone()));
    }
    for (symbol, links) in local_value_publications {
        if !all_value_symbols.insert(symbol) {
            return Err(SourceCheckError::Import(source));
        }
        value_publications.push((symbol, links));
    }
    let import_publication_count = import_publications.len();

    let mut seen_reads = HashSet::with_capacity(identifier_reads.len());
    let mut read_publications: Vec<(NodeRef, SymbolNodeLinks)> =
        Vec::with_capacity(identifier_reads.len());
    for &(node, resolved_symbol) in identifier_reads {
        if !seen_reads.insert(node) {
            return Err(SourceCheckError::Variable(
                VariableInvariant::DuplicateIdentifierRead(node),
            ));
        }
        if !store.contains_node_ref(node) || store.symbol(resolved_symbol).is_none() {
            return Err(SourceCheckError::Variable(
                VariableInvariant::SymbolNodePublication(node),
            ));
        }
        let mut links = store.symbol_node_links(node).cloned().unwrap_or_default();
        if links
            .resolved_symbol
            .is_some_and(|cached| cached != resolved_symbol)
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidSymbolNodeCache {
                    node,
                    cached: links.resolved_symbol,
                    expected: resolved_symbol,
                },
            ));
        }
        links.resolved_symbol = Some(resolved_symbol);
        read_publications.push((node, links));
    }

    for (index, (symbol, links)) in value_publications.into_iter().enumerate() {
        if !store.set_value_symbol_links(symbol, links) {
            if index < import_publication_count {
                return Err(SourceCheckError::Import(source));
            }
            return Err(SourceCheckError::Variable(
                VariableInvariant::ValueTypePublication(symbol),
            ));
        }
    }
    for (node, links) in read_publications {
        if !store.set_symbol_node_links(node, links) {
            return Err(SourceCheckError::Variable(
                VariableInvariant::SymbolNodePublication(node),
            ));
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct MaterializedSourceCallable {
    type_: TypeId,
    signature: SignatureId,
}

#[allow(clippy::too_many_arguments)]
fn materialize_source_overloads(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    overloads: &[SourceOverloadPlan],
) -> Result<Vec<MaterializedSourceOverload>, SourceCheckError> {
    let Some(batch_fallback) = overloads
        .first()
        .and_then(|overload| overload.declarations.first())
        .map(|plan| plan.declaration)
    else {
        return Ok(Vec::new());
    };
    let mut prepared = Vec::with_capacity(overloads.len());
    for overload in overloads {
        let fallback = overload
            .declarations
            .first()
            .map_or(batch_fallback, |plan| plan.declaration);
        let mut resolved = Vec::with_capacity(overload.declarations.len());
        for declaration in &overload.declarations {
            let mut parameter_types = Vec::with_capacity(declaration.parameters.len());
            for parameter in &declaration.parameters {
                session.reset_query();
                let mut annotation_diagnostics = CanonicalCheckerDiagnostics::default();
                let result = CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    &mut annotation_diagnostics,
                )?
                .get_type_from_type_node(parameter.type_node);
                merge_retry_diagnostics(diagnostics, annotation_diagnostics);
                parameter_types.push(result?);
            }
            let return_node =
                declaration
                    .return_type
                    .type_node()
                    .ok_or(SourceCheckError::Function(
                        SourceFunctionInvariant::Callable(declaration.declaration),
                    ))?;
            session.reset_query();
            let mut return_diagnostics = CanonicalCheckerDiagnostics::default();
            let return_type = CanonicalTypeQuery::new_with_global_types_and_session(
                store,
                host,
                global_types,
                options,
                session,
                &mut return_diagnostics,
            )?
            .get_type_from_type_node(return_node);
            merge_retry_diagnostics(diagnostics, return_diagnostics);
            resolved.push(ResolvedSourceOverloadSignature {
                parameter_types,
                return_type: return_type?,
            });
        }
        prepared.push(
            prepare_source_overload_publication(store, global_types, overload, &resolved)
                .map_err(|error| SourcePlanner::overload_plan_error(fallback, error))?,
        );
    }
    publish_source_overload_batch(store, overloads, &prepared)
        .map_err(|error| SourcePlanner::overload_plan_error(batch_fallback, error))
}

#[allow(clippy::too_many_arguments)] // Keeps callable source capabilities explicit.
fn materialize_checked_source_callable(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    callable: &SourceCallablePlan,
) -> Result<MaterializedSourceCallable, SourceCheckError> {
    let mut callable_diagnostics = CanonicalCheckerDiagnostics::default();
    let type_result = CanonicalTypeQuery::new_with_global_types_and_session(
        store,
        host,
        global_types,
        options,
        session,
        &mut callable_diagnostics,
    )
    .and_then(|mut query| {
        query.get_type_of_source_callable(callable.declaration, callable.owner_symbol)
    });
    merge_retry_diagnostics(diagnostics, callable_diagnostics);
    let type_ = type_result?;
    let owner = callable.owner_symbol;
    let linked = store
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .ok_or(SourceCheckError::Function(
            SourceFunctionInvariant::MissingCallableType(owner),
        ))?;
    let registered =
        store
            .source_callable_type_for_owner(owner)
            .ok_or(SourceCheckError::Function(
                SourceFunctionInvariant::MissingCallableType(owner),
            ))?;
    if linked != type_ || registered != type_ {
        return Err(SourceCheckError::Function(
            SourceFunctionInvariant::CallableTypeMismatch {
                symbol: owner,
                expected: type_,
                actual: if linked == type_ { registered } else { linked },
            },
        ));
    }
    let signature = store
        .source_callable_provenance(type_)
        .filter(|provenance| {
            provenance.declaration == callable.declaration && provenance.owner_symbol == owner
        })
        .map(|provenance| provenance.signature)
        .ok_or(SourceCheckError::Function(
            SourceFunctionInvariant::MissingCallableType(owner),
        ))?;
    if !callable.return_type.is_inferred() {
        let mut return_diagnostics = CanonicalCheckerDiagnostics::default();
        let return_result = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            &mut return_diagnostics,
        )
        .and_then(|mut query| query.get_return_type_of_signature(signature));
        merge_retry_diagnostics(diagnostics, return_diagnostics);
        return_result?;
    }
    Ok(MaterializedSourceCallable { type_, signature })
}

#[allow(clippy::too_many_arguments)] // Keeps body inference capabilities explicit.
fn publish_checked_source_callable_return(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    flow_types: &HashMap<SemanticSymbolId, TypeId>,
    preflighted_type_import_value_uses: &HashMap<NodeRef, PreparedSourceTypeImportValueUse>,
    deferred: &mut Vec<DeferredAssertion>,
    callable: &SourceCallablePlan,
    signature: SignatureId,
    expression: Option<&PlannedExpression>,
) -> Result<TypeId, SourceCheckError> {
    let inferred = match expression {
        Some(expression) => {
            let checked = check_expression_type(
                store,
                host,
                global_types,
                source,
                options,
                session,
                diagnostics,
                flow_types,
                preflighted_type_import_value_uses,
                expression,
                None,
                deferred,
            )?;
            let widened_literal = widened_fresh_literal_type(store, checked.result)?;
            store.get_widened_type_with_global_types(widened_literal, global_types)?
        }
        None => {
            store
                .intrinsic_bootstrap()
                .ok_or(DerivedTypeError::BootstrapUninitialized)?
                .void_type
        }
    };
    publish_inferred_source_callable_return(store, callable, signature, inferred)
        .map_err(SourcePlanner::callable_plan_error)
}

fn captured_callable_flow_types(
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
    declared_types: &HashMap<SemanticSymbolId, TypeId>,
    mutable_variables: &HashSet<SemanticSymbolId>,
) -> Result<HashMap<SemanticSymbolId, TypeId>, SourceCheckError> {
    let mut captured = current_flow_types.clone();
    for symbol in mutable_variables {
        let declared_type = *declared_types
            .get(symbol)
            .ok_or(SourceCheckError::Variable(
                VariableInvariant::MissingStagedValueType(*symbol),
            ))?;
        captured.insert(*symbol, declared_type);
    }
    Ok(captured)
}

fn function_declaration_flow_types(
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
    declared_types: &HashMap<SemanticSymbolId, TypeId>,
) -> HashMap<SemanticSymbolId, TypeId> {
    let mut captured = current_flow_types.clone();
    captured.extend(
        declared_types
            .iter()
            .map(|(symbol, type_)| (*symbol, *type_)),
    );
    captured
}

#[allow(clippy::too_many_arguments)]
fn resolve_contextual_callable_target(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    arrow: &SourceContextualArrowPlan,
) -> Result<(TypeId, ValidatedSingleCallable), SourceCheckError> {
    let mut target_diagnostics = CanonicalCheckerDiagnostics::default();
    let target = CanonicalTypeQuery::new_with_global_types_and_session(
        store,
        host,
        global_types,
        options,
        session,
        &mut target_diagnostics,
    )?
    .get_type_from_type_node(arrow.contextual_type.type_node);
    merge_retry_diagnostics(diagnostics, target_diagnostics);
    let target = target?;

    let mut resolved_return = false;
    loop {
        match validate_stored_single_callable(store, target) {
            StoredSingleCallableValidation::Valid { callable, .. }
                if callable.return_type.is_some() =>
            {
                return Ok((target, callable));
            }
            StoredSingleCallableValidation::Valid { callable, .. } if !resolved_return => {
                let mut return_diagnostics = CanonicalCheckerDiagnostics::default();
                let result = CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    &mut return_diagnostics,
                )?
                .get_return_type_of_signature(callable.signature);
                merge_retry_diagnostics(diagnostics, return_diagnostics);
                result?;
                resolved_return = true;
            }
            StoredSingleCallableValidation::NotCallable
            | StoredSingleCallableValidation::Pending { .. }
            | StoredSingleCallableValidation::Malformed { .. }
            | StoredSingleCallableValidation::Valid { .. } => {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Arrow(arrow.contextual_type.type_node),
                ));
            }
        }
    }
}

fn contextual_parameter_name(
    host: &DeclaredTypeHost<'_>,
    parameter: &super::source_arrows::ResolvedSourceContextualParameter,
) -> Result<String, SourceCheckError> {
    let node = host
        .node(parameter.name)
        .ok_or(SourceCheckError::Arrow(parameter.name))?;
    let NodeData::Identifier(identifier) = &node.data else {
        return Err(SourceCheckError::Arrow(parameter.name));
    };
    Ok(identifier.text.clone())
}

fn preflight_contextual_source_publication(
    store: &CanonicalTypeMapperStore,
    arrow: &SourceContextualArrowPlan,
    resolved_target: Option<TypeId>,
) -> Result<(), SourceCheckError> {
    let existing_callable = store.source_callable_type_for_owner(arrow.owner_symbol);
    let Some(existing_callable) = existing_callable else {
        if store
            .value_symbol_links(arrow.variable_symbol)
            .is_some_and(|links| links != &ValueSymbolLinks::default())
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidValueLinks(arrow.variable_symbol),
            ));
        }
        if store
            .value_symbol_links(arrow.owner_symbol)
            .is_some_and(|links| links != &ValueSymbolLinks::default())
            || store
                .signature_links(arrow.declaration)
                .is_some_and(|links| links != &super::links::SignatureLinks::default())
            || arrow.parameters.iter().any(|parameter| {
                store
                    .value_symbol_links(parameter.symbol)
                    .is_some_and(|links| links != &ValueSymbolLinks::default())
            })
            || store
                .type_node_links(arrow.declaration)
                .is_some_and(|links| links != &TypeNodeLinks::default())
            || store
                .source_callable_type_for_declaration(arrow.declaration)
                .is_some()
        {
            return Err(SourceCheckError::Arrow(arrow.declaration));
        }
        return Ok(());
    };

    let Some(provenance) = store.source_callable_provenance(existing_callable) else {
        return Err(SourceCheckError::Arrow(arrow.declaration));
    };
    let expected_parameter_symbols = arrow
        .parameters
        .iter()
        .map(|parameter| parameter.symbol)
        .collect::<Vec<_>>();
    let contextual_target = provenance.contextual_target;
    let expected_variable_links = contextual_target.map(|target| ValueSymbolLinks {
        resolved_type: Some(target),
        ..ValueSymbolLinks::default()
    });
    let variable_links_are_admissible = match store.value_symbol_links(arrow.variable_symbol) {
        None => true,
        Some(links) if links == &ValueSymbolLinks::default() => true,
        Some(links) => expected_variable_links.as_ref() == Some(links),
    };
    let warm_source_is_exact = matches!(
        validate_stored_source_callable(store, existing_callable),
        StoredSourceCallableValidation::Valid(_)
    ) && provenance.family == SourceCallableFamily::ArrowFunction
        && provenance.declaration == arrow.declaration
        && provenance.owner_symbol == arrow.owner_symbol
        && provenance.owner_parent.is_none()
        && provenance.export_local.is_none()
        && provenance.contextual_variable == Some(arrow.variable_symbol)
        && provenance.contextual_target.is_some()
        && resolved_target.is_none_or(|target| provenance.contextual_target == Some(target))
        && store
            .signature(provenance.signature)
            .is_some_and(|signature| {
                signature.parameters() == expected_parameter_symbols
                    && signature.flags() == arrow.flags
                    && signature.min_argument_count() == arrow.min_argument_count
            })
        && store.source_callable_type_for_declaration(arrow.declaration) == Some(existing_callable)
        && store.type_node_links(arrow.declaration)
            == Some(&TypeNodeLinks {
                resolved_type: Some(existing_callable),
                ..TypeNodeLinks::default()
            })
        && variable_links_are_admissible;
    if !warm_source_is_exact {
        return Err(SourceCheckError::Arrow(arrow.declaration));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn materialize_contextual_source_arrow(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    arrow: &SourceContextualArrowPlan,
) -> Result<(TypeId, TypeId), SourceCheckError> {
    let (target, target_callable) = resolve_contextual_callable_target(
        store,
        host,
        global_types,
        options,
        session,
        diagnostics,
        arrow,
    )?;
    preflight_contextual_source_publication(store, arrow, Some(target))?;
    let target_signature = store
        .signature(target_callable.signature)
        .ok_or(SourceCheckError::Arrow(arrow.contextual_type.type_node))?;
    let resolved_shape = SourceContextualSignatureShape {
        call_signature_count: 1,
        type_parameter_count: target_signature.type_parameters().len(),
        parameter_count: target_callable.parameters.len(),
        has_effective_rest: target_signature.has_rest_parameter(),
    };
    if resolved_shape != arrow.contextual_signature_shape {
        return Err(SourceCheckError::Arrow(arrow.contextual_type.type_node));
    }
    let resolved = resolve_contextual_arrow_parameter_origins(arrow, resolved_shape)
        .map_err(SourcePlanner::contextual_arrow_plan_error)?;
    let implicit_any_nodes = resolved.implicit_any_diagnostic_nodes(options.no_implicit_any);
    let ResolvedSourceContextualArrowPlan {
        parameters,
        flags,
        min_argument_count,
        ..
    } = resolved;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::Arrow(arrow.declaration))?;
    let any = bootstrap.any_type;
    let undefined = bootstrap.undefined_type;
    let void = bootstrap.void_type;
    let strict_null_checks = bootstrap.options.strict_null_checks;
    let mut prepared_parameters = Vec::with_capacity(parameters.len());
    for parameter in &parameters {
        let base = match parameter.origin {
            SourceContextualParameterOrigin::ContextualPosition { index } => target_callable
                .parameters
                .get(index)
                .copied()
                .ok_or(SourceCheckError::Arrow(parameter.declaration))?,
            SourceContextualParameterOrigin::ImplicitAny { .. } => any,
            SourceContextualParameterOrigin::ContextualEmptyRestTail { .. } => store
                .create_canonical_empty_tuple_type()
                .map_err(|_| SourceCheckError::Arrow(parameter.declaration))?,
        };
        let type_ = if strict_null_checks && parameter.optional && base != any {
            store.expression_union_type_with_global_types(
                global_types,
                &[base, undefined],
                UnionReduction::Literal,
            )?
        } else {
            base
        };
        prepared_parameters.push(ContextualSourceCallableParameter {
            declaration: parameter.declaration,
            symbol: parameter.symbol,
            type_,
        });
    }
    let callable = publish_contextual_source_callable(
        store,
        &PreparedContextualSourceCallable {
            declaration: arrow.declaration,
            owner_symbol: arrow.owner_symbol,
            variable_symbol: arrow.variable_symbol,
            contextual_target: target,
            parameters: prepared_parameters,
            flags,
            min_argument_count,
            return_type: void,
        },
    )
    .map_err(SourcePlanner::callable_plan_error)?;
    publish_expression_type(store, arrow.declaration, callable)?;

    for node in implicit_any_nodes {
        let parameter = parameters
            .iter()
            .find(|parameter| parameter.declaration == node)
            .ok_or(SourceCheckError::Arrow(node))?;
        let diagnostic = Diagnostic::with_arguments(
            message_by_code(7006).ok_or(SourceCheckError::MissingDiagnostic(7006))?,
            [
                contextual_parameter_name(host, parameter)?,
                "any".to_owned(),
            ],
        );
        merge_retry_diagnostic(
            diagnostics,
            CanonicalCheckerDiagnostic {
                node: Some(node),
                range_override: None,
                diagnostic,
                related_information: Vec::new(),
            },
        );
    }

    if !source_type_is_assignable_to(
        store,
        host,
        global_types,
        options,
        session,
        diagnostics,
        callable,
        target,
    )? {
        let mut flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
        if options.no_error_truncation {
            flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
        }
        let display = get_type_names_for_assignability_error_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            callable,
            target,
            flags,
        )?;
        merge_retry_diagnostic(
            diagnostics,
            CanonicalCheckerDiagnostic {
                node: Some(arrow.declaration),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(2322).ok_or(SourceCheckError::MissingDiagnostic(2322))?,
                    [display.source, display.target],
                ),
                related_information: Vec::new(),
            },
        );
    }
    Ok((target, callable))
}

fn preflight_source_namespace_annotations(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    namespace: &SourceNamespacePlan,
) -> Result<(), SourceCheckError> {
    for member in &namespace.members {
        match member {
            SourceNamespaceMemberPlan::Namespace(nested) => {
                preflight_source_namespace_annotations(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    nested,
                )?;
            }
            SourceNamespaceMemberPlan::TypeAlias { annotation, .. }
            | SourceNamespaceMemberPlan::AmbientVariable { annotation, .. } => {
                session.reset_query();
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                )?
                .preflight_type_from_type_node(*annotation)?;
            }
            SourceNamespaceMemberPlan::Interface { annotations, .. } => {
                for annotation in annotations {
                    session.reset_query();
                    CanonicalTypeQuery::new_with_global_types_and_session(
                        store,
                        host,
                        global_types,
                        options,
                        session,
                        diagnostics,
                    )?
                    .preflight_type_from_type_node(*annotation)?;
                }
            }
            SourceNamespaceMemberPlan::EmptyEnum { .. } => {}
        }
    }
    Ok(())
}

/// Checks one already-retained source into context-owned private staging.
#[allow(clippy::too_many_arguments)] // Mirrors the context-owned source execution boundary.
pub(super) fn check_source_file(
    arena: &NodeArena,
    bound: &BoundFile,
    source: SourceFileRef,
    host: &DeclaredTypeHost<'_>,
    alias_host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    global_types: &CanonicalGlobalTypes,
    store: &mut CanonicalTypeMapperStore,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(), SourceCheckError> {
    if !store.contains_source_file(source) {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::StoreSourceMismatch(source),
        ));
    }
    if store
        .source_file_links(source)
        .is_some_and(|links| links.type_checked)
    {
        return Ok(());
    }

    let SourceCheckPlan {
        statements,
        value_imports,
        type_imports,
        named_reexports,
        import_reads,
        type_import_references,
        type_import_value_uses,
        ambient_variables,
        overloads,
        functions,
        arrows,
        contextual_arrows,
        identifier_reads,
        default_news,
        javascript_jsdoc,
        strings,
        numbers,
        bigints,
    } = SourcePlanner::new_semantic_with_global_types(
        arena,
        bound,
        source,
        store,
        host,
        global_types,
    )
    .finish()?;
    if let Some(jsdoc) = &javascript_jsdoc {
        for declaration in jsdoc.declarations() {
            let annotations = declaration
                .type_()
                .into_iter()
                .chain(declaration.return_type())
                .chain(
                    declaration
                        .parameters()
                        .iter()
                        .filter_map(super::jsdoc::PlannedJsDocParameter::type_),
                )
                .chain(
                    declaration
                        .typedefs()
                        .iter()
                        .filter_map(super::jsdoc::PlannedJsDocTypedef::type_),
                );
            for annotation in annotations {
                preflight_planned_jsdoc_type(store, global_types, options, annotation).map_err(
                    |_| {
                        SourceCheckError::Unsupported(UnsupportedSourceSyntax::JsDoc(
                            declaration.node(),
                        ))
                    },
                )?;
            }
        }
        append_javascript_jsdoc_diagnostics(jsdoc, diagnostics);
    }
    preflight_inferred_function_return_dependencies(&functions)?;

    let mut reexport_aliases = HashSet::new();
    for reexport in &named_reexports {
        for binding in &reexport.bindings {
            if !reexport_aliases.insert(binding.alias_symbol) {
                return Err(SourceCheckError::Import(binding.declaration));
            }
        }
    }
    for reexport in &named_reexports {
        for binding in &reexport.bindings {
            resolve_source_named_reexport_binding(store, alias_host, binding)
                .map_err(|error| SourcePlanner::import_plan_error(binding.declaration, &error))?;
        }
    }

    let mut resolved_imports = HashMap::<SemanticSymbolId, ResolvedSourceImportBinding>::new();
    for import in &value_imports {
        for binding in &import.bindings {
            let resolved = resolve_source_import_binding(store, alias_host, binding)
                .map_err(|error| SourcePlanner::import_plan_error(binding.declaration, &error))?;
            if resolved_imports
                .insert(binding.alias_symbol, resolved)
                .is_some()
            {
                return Err(SourceCheckError::Import(binding.declaration));
            }
        }
    }

    let mut resolved_type_imports =
        HashMap::<SemanticSymbolId, ResolvedSourceTypeImportBinding>::new();
    for import in &type_imports {
        for binding in &import.bindings {
            let resolved = resolve_source_type_import_binding(store, alias_host, host, binding)
                .map_err(|error| SourcePlanner::import_plan_error(binding.declaration, &error))?;
            if resolved_type_imports
                .insert(binding.alias_symbol, resolved)
                .is_some()
            {
                return Err(SourceCheckError::Import(binding.declaration));
            }
        }
    }

    let mut type_import_capabilities =
        HashMap::<NodeRef, Vec<CanonicalTypeReferenceAliasTarget>>::new();
    let mut type_import_capability_references = HashSet::new();
    let mut type_import_root_order = Vec::new();
    let mut type_import_roots = HashSet::new();
    for reference in &type_import_references {
        let resolved = resolved_type_imports
            .get(&reference.alias_symbol)
            .ok_or(SourceCheckError::Import(reference.node))?;
        let capability = plan_source_type_import_reference(
            store,
            host,
            resolved,
            reference.root,
            reference.node,
        )
        .map_err(|error| SourcePlanner::import_plan_error(reference.node, &error))?;
        if !type_import_capability_references.insert(reference.node) {
            return Err(SourceCheckError::Import(reference.node));
        }
        if type_import_roots.insert(reference.root) {
            type_import_root_order.push(reference.root);
        }
        type_import_capabilities
            .entry(reference.root)
            .or_default()
            .push(capability);
    }

    let mut type_import_preflight_diagnostics = CanonicalCheckerDiagnostics::default();
    for root in type_import_root_order {
        if let Some(cached) = store
            .type_node_links(root)
            .and_then(|links| links.resolved_type)
            && type_import_references.iter().any(|reference| {
                reference.root == root
                    && reference.node != root
                    && (store
                        .type_node_links(reference.node)
                        .and_then(|links| links.resolved_type)
                        .is_none()
                        || store
                            .symbol_node_links(reference.node)
                            .and_then(|links| links.resolved_symbol)
                            .is_none())
            })
        {
            let root_kind =
                host.node(root)
                    .map(|node| node.kind)
                    .ok_or(SourceCheckError::Provenance(
                        SourceCheckProvenanceError::MissingNode(root),
                    ))?;
            let unavailable = if root_kind == SyntaxKind::UnionType {
                super::type_nodes::TypeNodeUnavailable::InvalidCachedUnionType(cached)
            } else {
                super::type_nodes::TypeNodeUnavailable::InvalidTypeReference(root)
            };
            return Err(SourceCheckError::DeclaredType(
                DeclaredTypeError::TypeNodeUnavailable(unavailable),
            ));
        }
        session.reset_query();
        CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            &mut type_import_preflight_diagnostics,
        )?
        .with_type_reference_alias_targets(
            type_import_capabilities
                .get(&root)
                .ok_or(SourceCheckError::Import(root))?
                .iter()
                .copied(),
        )?
        .preflight_type_from_type_node(root)?;
    }
    for variable in &ambient_variables {
        if type_import_roots.contains(&variable.type_node) {
            continue;
        }
        session.reset_query();
        CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            &mut type_import_preflight_diagnostics,
        )?
        .preflight_type_from_type_node(variable.type_node)?;
    }
    for statement in &statements {
        match statement {
            PlannedStatement::GenericInterface(interface) => {
                for property in interface.property_type_nodes() {
                    session.reset_query();
                    CanonicalTypeQuery::new_with_global_types_and_session(
                        store,
                        host,
                        global_types,
                        options,
                        session,
                        &mut type_import_preflight_diagnostics,
                    )?
                    .preflight_type_from_type_node(property)?;
                }
            }
            PlannedStatement::Namespace(namespace) => {
                preflight_source_namespace_annotations(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    &mut type_import_preflight_diagnostics,
                    namespace,
                )?;
            }
            _ => {}
        }
    }
    for function in &functions {
        session.reset_query();
        CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            &mut type_import_preflight_diagnostics,
        )?
        .preflight_type_of_source_callable(
            function.callable.declaration,
            function.callable.owner_symbol,
        )?;
    }
    for arrow in &arrows {
        session.reset_query();
        CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            &mut type_import_preflight_diagnostics,
        )?
        .preflight_type_of_source_callable(
            arrow.source.callable.declaration,
            arrow.source.callable.owner_symbol,
        )?;
    }
    for arrow in &contextual_arrows {
        session.reset_query();
        CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            &mut type_import_preflight_diagnostics,
        )?
        .preflight_type_from_type_node(arrow.source.contextual_type.type_node)?;
    }
    debug_assert!(type_import_preflight_diagnostics.is_empty());

    let mut preflighted_type_import_value_uses = HashMap::new();
    for read in &type_import_value_uses {
        if preflighted_type_import_value_uses.contains_key(&read.node) {
            return Err(SourceCheckError::Import(read.node));
        }
        let prepared =
            preflight_type_import_value_use(arena, bound, store, &resolved_type_imports, read)?;
        if preflighted_type_import_value_uses
            .insert(read.node, prepared)
            .is_some()
        {
            return Err(SourceCheckError::Import(read.node));
        }
    }

    store.prepare_regular_literal_types(&strings, &numbers, &bigints)?;
    let mut deferred = Vec::new();
    // Publication owns every source value, including function-local symbols.
    // Top-level assignment/capture semantics must remain a separate map so a
    // local `let` can never leak into an unrelated callable's capture frame.
    let mut staged_value_types = HashMap::new();
    let mut top_level_declared_types = HashMap::new();
    let mut current_flow_types = HashMap::new();
    let mut mutable_variables = HashSet::new();
    let mut value_order = Vec::new();

    for variable in &ambient_variables {
        session.reset_query();
        let mut annotation_diagnostics = CanonicalCheckerDiagnostics::default();
        let type_reference_alias_targets: &[CanonicalTypeReferenceAliasTarget] =
            type_import_capabilities
                .get(&variable.type_node)
                .map_or_else(|| &[], Vec::as_slice);
        let declared_type = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            &mut annotation_diagnostics,
        )?
        .with_type_reference_alias_targets(type_reference_alias_targets.iter().copied())?
        .get_type_from_type_node(variable.type_node);
        merge_retry_diagnostics(diagnostics, annotation_diagnostics);
        let declared_type = declared_type?;
        stage_value_type(
            store,
            &mut staged_value_types,
            &mut value_order,
            variable.symbol,
            declared_type,
        )?;
        if top_level_declared_types
            .insert(variable.symbol, declared_type)
            .is_some()
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::DuplicateStagedValueType(variable.symbol),
            ));
        }
        if !variable.binding.is_const() && !mutable_variables.insert(variable.symbol) {
            return Err(SourceCheckError::Variable(
                VariableInvariant::DuplicateCurrentFlowType(variable.symbol),
            ));
        }
        if current_flow_types
            .insert(variable.symbol, declared_type)
            .is_some()
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::DuplicateCurrentFlowType(variable.symbol),
            ));
        }
    }

    let mut prepared_imports = Vec::<PreparedSourceImportValue>::new();
    let mut prepared_import_aliases = HashSet::new();
    for read in &import_reads {
        if !prepared_import_aliases.insert(read.value_symbol) {
            continue;
        }
        session.reset_query();
        let resolved = resolved_imports
            .get(&read.value_symbol)
            .ok_or(SourceCheckError::Import(read.node))?;
        let prepared = prepare_source_import_value(
            store,
            host,
            global_types,
            options,
            session,
            diagnostics,
            resolved,
            read,
        )
        .map_err(|error| SourcePlanner::import_plan_error(read.node, &error))?;
        if current_flow_types
            .insert(read.value_symbol, prepared.type_)
            .is_some()
        {
            return Err(SourceCheckError::Import(read.node));
        }
        prepared_imports.push(prepared);
    }

    let materialized_overloads = materialize_source_overloads(
        store,
        host,
        global_types,
        options,
        session,
        diagnostics,
        &overloads,
    )?;
    if materialized_overloads.len() != overloads.len() {
        return Err(SourceCheckError::Function(
            SourceFunctionInvariant::Callable(source.node_ref()),
        ));
    }
    for (overload, materialized) in overloads.iter().zip(&materialized_overloads) {
        let fallback = overload
            .declarations
            .first()
            .map_or(source.node_ref(), |declaration| declaration.declaration);
        if materialized.signatures.len() != overload.declarations.len()
            || store.source_overload_type_for_owner(overload.owner_symbol)
                != Some(materialized.type_)
            || current_flow_types
                .insert(overload.owner_symbol, materialized.type_)
                .is_some()
        {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(fallback),
            ));
        }
    }

    let mut materialized_functions = Vec::with_capacity(functions.len());
    for function in &functions {
        session.reset_query();
        let materialized = materialize_checked_source_callable(
            store,
            host,
            global_types,
            options,
            session,
            diagnostics,
            &function.callable,
        )?;
        let owner = function.callable.owner_symbol;
        if current_flow_types
            .insert(owner, materialized.type_)
            .is_some()
        {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::DuplicateDeclaration(function.callable.declaration),
            ));
        }
        if options.no_implicit_any {
            issue_implicit_any_parameter_diagnostics(
                arena,
                host,
                diagnostics,
                &function.callable,
                javascript_jsdoc.as_ref(),
            )?;
        }
        materialized_functions.push(materialized);
    }
    let mut inferred_function_diagnostics = (0..functions.len())
        .map(|_| None)
        .collect::<Vec<Option<CanonicalCheckerDiagnostics>>>();
    for (index, (function, materialized)) in
        functions.iter().zip(&materialized_functions).enumerate()
    {
        if !function.callable.return_type.is_inferred() {
            continue;
        }
        session.reset_query();
        let mut function_diagnostics = CanonicalCheckerDiagnostics::default();
        let body_flow_types = check_callable_parameter_initializers(
            store,
            host,
            global_types,
            source,
            options,
            session,
            &mut function_diagnostics,
            &current_flow_types,
            &preflighted_type_import_value_uses,
            &mut deferred,
            &function.callable,
            &function.parameter_initializers,
        )?;
        let (expression, return_flow_types) = match &function.body {
            PlannedFunctionBody::Empty => (None, body_flow_types),
            PlannedFunctionBody::Return { expression, .. } => (Some(expression), body_flow_types),
            PlannedFunctionBody::Linear(statements) => {
                let flow_types = check_planned_linear_function_statements(
                    bound,
                    store,
                    host,
                    global_types,
                    source,
                    options,
                    session,
                    &mut function_diagnostics,
                    body_flow_types,
                    &preflighted_type_import_value_uses,
                    &type_import_capabilities,
                    &mut deferred,
                    &function.callable,
                    None,
                    statements,
                    &mut staged_value_types,
                    &mut value_order,
                )?;
                (statements.return_expression.as_ref(), flow_types)
            }
            PlannedFunctionBody::Ambient
            | PlannedFunctionBody::Statements(_)
            | PlannedFunctionBody::JoinedStatements(_) => {
                return Err(SourceCheckError::Function(
                    SourceFunctionInvariant::Callable(function.callable.body),
                ));
            }
        };
        publish_checked_source_callable_return(
            store,
            host,
            global_types,
            source,
            options,
            session,
            &mut function_diagnostics,
            &return_flow_types,
            &preflighted_type_import_value_uses,
            &mut deferred,
            &function.callable,
            materialized.signature,
            expression,
        )?;
        inferred_function_diagnostics[index] = Some(function_diagnostics);
    }

    prepare_direct_default_news(store, host, &default_news)
        .map_err(|error| SourcePlanner::new_plan_error(source.node_ref(), error))?;
    for statement in statements {
        session.reset_query();
        match statement {
            PlannedStatement::TypeAlias(symbol) | PlannedStatement::Interface(symbol) => {
                let mut statement_diagnostics = CanonicalCheckerDiagnostics::default();
                let result = CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    &mut statement_diagnostics,
                )
                .and_then(|mut query| query.get_declared_type_of_symbol(symbol));
                merge_retry_diagnostics(diagnostics, statement_diagnostics);
                result?;
            }
            PlannedStatement::Namespace(namespace) => {
                execute_source_namespace(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    &namespace,
                )?;
            }
            PlannedStatement::GenericInterface(interface) => {
                let mut statement_diagnostics = CanonicalCheckerDiagnostics::default();
                let target = CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    &mut statement_diagnostics,
                )
                .and_then(|mut query| query.get_declared_type_of_symbol(interface.symbol));
                merge_retry_diagnostics(diagnostics, statement_diagnostics);
                let target = target?;

                let mut property_types = Vec::with_capacity(interface.properties.len());
                for property in &interface.properties {
                    session.reset_query();
                    let mut property_diagnostics = CanonicalCheckerDiagnostics::default();
                    let property_type = CanonicalTypeQuery::new_with_global_types_and_session(
                        store,
                        host,
                        global_types,
                        options,
                        session,
                        &mut property_diagnostics,
                    )?
                    .get_type_from_type_node(property.type_node);
                    merge_retry_diagnostics(diagnostics, property_diagnostics);
                    let mut property_type = property_type?;
                    if options.intrinsic.strict_null_checks && property.optional {
                        let bootstrap =
                            store
                                .intrinsic_bootstrap()
                                .ok_or(SourceCheckError::LiteralCache(
                                    SourceLiteralCacheError::BootstrapUninitialized,
                                ))?;
                        let undefined = bootstrap.undefined_or_missing_type;
                        let record =
                            store
                                .type_payload(property_type)
                                .ok_or(SourceCheckError::Variable(
                                    VariableInvariant::InvalidSymbolShape(property.symbol),
                                ))?;
                        let already_optional = record
                            .flags()
                            .intersects(TypeFlags::ANY_OR_UNKNOWN | TypeFlags::UNDEFINED)
                            || matches!(
                                record.data(),
                                TypeData::Union(union) if union.union.types.contains(&undefined)
                            );
                        if !already_optional {
                            property_type = store.expression_union_type_with_global_types(
                                global_types,
                                &[property_type, undefined],
                                UnionReduction::Literal,
                            )?;
                        }
                    }
                    property_types.push(property_type);
                }
                let bases_resolved = matches!(
                    store.type_payload(target).map(TypeRecord::data),
                    Some(TypeData::Interface(interface)) if interface.base_types_resolved
                );
                if !bases_resolved && !store.publish_interface_no_base_resolution(target) {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Syntax {
                            node: interface.node,
                            kind: SyntaxKind::InterfaceDeclaration,
                            role: SourceSyntaxRole::InterfaceDeclaration,
                        },
                    ));
                }
                super::object_members::publish_generic_interface_declared_members(
                    store,
                    &interface,
                    target,
                    &property_types,
                )
                .map_err(|_| {
                    SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                        node: interface.node,
                        kind: SyntaxKind::InterfaceDeclaration,
                        role: SourceSyntaxRole::InterfaceDeclaration,
                    })
                })?;
            }
            PlannedStatement::Class(class) => {
                let declaration = class.declaration();
                execute_nongeneric_class_member_query(store, host, &class)
                    .map_err(|error| SourcePlanner::class_plan_error(declaration, error))?;
                if options.intrinsic.strict_null_checks && options.strict_property_initialization {
                    for property in class.uninitialized_instance_properties() {
                        let node = host.node(*property).ok_or(SourceCheckError::Provenance(
                            SourceCheckProvenanceError::MissingNode(*property),
                        ))?;
                        let NodeData::Identifier(identifier) = &node.data else {
                            return Err(SourceCheckError::Class(declaration));
                        };
                        merge_retry_diagnostic(
                            diagnostics,
                            CanonicalCheckerDiagnostic {
                                node: Some(*property),
                                range_override: None,
                                diagnostic: Diagnostic::with_arguments(
                                    message_by_code(2564)
                                        .ok_or(SourceCheckError::MissingDiagnostic(2564))?,
                                    [identifier.text.clone()],
                                ),
                                related_information: Vec::new(),
                            },
                        );
                    }
                }
            }
            PlannedStatement::Enum(enumeration) => {
                let materialized =
                    execute_top_level_enum(store, host, &enumeration).map_err(|error| {
                        SourcePlanner::enum_plan_error(enumeration.declaration, error)
                    })?;
                for diagnostic in &enumeration.diagnostics {
                    issue_node_diagnostic(diagnostics, diagnostic.node, diagnostic.code)?;
                }
                stage_value_type(
                    store,
                    &mut staged_value_types,
                    &mut value_order,
                    enumeration.owner_symbol,
                    materialized.value_type,
                )?;
                if current_flow_types
                    .insert(enumeration.owner_symbol, materialized.value_type)
                    .is_some()
                {
                    return Err(SourceCheckError::Enum(enumeration.declaration));
                }
            }
            PlannedStatement::ExternalModuleMarker
            | PlannedStatement::NamedReexport
            | PlannedStatement::AmbientVariables
            | PlannedStatement::AmbientOverload => {}
            PlannedStatement::Function(index) => {
                let function = functions.get(index).ok_or(SourceCheckError::Function(
                    SourceFunctionInvariant::InvalidStatementIndex(index),
                ))?;
                if matches!(function.body, PlannedFunctionBody::Ambient) {
                    if function.callable.body_mode != SourceCallableBodyMode::AmbientDeclaration
                        || function.callable.return_type.is_inferred()
                        || !function.parameter_initializers.is_empty()
                    {
                        return Err(SourceCheckError::Function(
                            SourceFunctionInvariant::Callable(function.callable.declaration),
                        ));
                    }
                    continue;
                }
                if function.callable.body_mode != SourceCallableBodyMode::Present {
                    return Err(SourceCheckError::Function(
                        SourceFunctionInvariant::Callable(function.callable.declaration),
                    ));
                }
                if function.callable.return_type.is_inferred() {
                    let function_diagnostics = inferred_function_diagnostics
                        .get_mut(index)
                        .and_then(Option::take)
                        .ok_or(SourceCheckError::Function(
                            SourceFunctionInvariant::Callable(function.callable.declaration),
                        ))?;
                    merge_retry_diagnostics(diagnostics, function_diagnostics);
                    continue;
                }
                let Some(return_type) = function.callable.return_type.type_node() else {
                    return Err(SourceCheckError::Function(
                        SourceFunctionInvariant::Callable(function.callable.declaration),
                    ));
                };
                let captured_flow_types =
                    function_declaration_flow_types(&current_flow_types, &top_level_declared_types);
                let body_flow_types = check_callable_parameter_initializers(
                    store,
                    host,
                    global_types,
                    source,
                    options,
                    session,
                    diagnostics,
                    &captured_flow_types,
                    &preflighted_type_import_value_uses,
                    &mut deferred,
                    &function.callable,
                    &function.parameter_initializers,
                )?;
                match &function.body {
                    PlannedFunctionBody::Ambient => {
                        return Err(SourceCheckError::Function(
                            SourceFunctionInvariant::Callable(function.callable.declaration),
                        ));
                    }
                    PlannedFunctionBody::Empty => {}
                    PlannedFunctionBody::Return {
                        statement,
                        expression,
                    } => {
                        session.reset_query();
                        check_planned_assignment(
                            store,
                            host,
                            global_types,
                            source,
                            options,
                            session,
                            diagnostics,
                            &body_flow_types,
                            &preflighted_type_import_value_uses,
                            &mut deferred,
                            return_type,
                            &[],
                            expression,
                            *statement,
                            None,
                        )?;
                    }
                    PlannedFunctionBody::Linear(statements) => {
                        check_planned_linear_function_statements(
                            bound,
                            store,
                            host,
                            global_types,
                            source,
                            options,
                            session,
                            diagnostics,
                            body_flow_types,
                            &preflighted_type_import_value_uses,
                            &type_import_capabilities,
                            &mut deferred,
                            &function.callable,
                            Some(return_type),
                            statements,
                            &mut staged_value_types,
                            &mut value_order,
                        )?;
                    }
                    PlannedFunctionBody::Statements(statements) => {
                        check_planned_function_statements(
                            bound,
                            store,
                            host,
                            global_types,
                            source,
                            options,
                            session,
                            diagnostics,
                            body_flow_types,
                            &preflighted_type_import_value_uses,
                            &type_import_capabilities,
                            &mut deferred,
                            &function.callable,
                            return_type,
                            statements,
                            &mut staged_value_types,
                            &mut value_order,
                        )?;
                    }
                    PlannedFunctionBody::JoinedStatements(statements) => {
                        check_planned_joined_function_statements(
                            bound,
                            store,
                            host,
                            global_types,
                            source,
                            options,
                            session,
                            diagnostics,
                            body_flow_types,
                            &preflighted_type_import_value_uses,
                            &type_import_capabilities,
                            &mut deferred,
                            &function.callable,
                            return_type,
                            statements,
                            &mut staged_value_types,
                            &mut value_order,
                        )?;
                    }
                }
            }
            PlannedStatement::Arrow(index) => {
                let arrow = arrows
                    .get(index)
                    .ok_or(SourceCheckError::Arrow(source.node_ref()))?;
                let materialized = materialize_checked_source_callable(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    &arrow.source.callable,
                )?;
                if arrow.source.callable.return_type.is_inferred() {
                    let captured_flow_types = captured_callable_flow_types(
                        &current_flow_types,
                        &top_level_declared_types,
                        &mutable_variables,
                    )?;
                    let body_flow_types = check_callable_parameter_initializers(
                        store,
                        host,
                        global_types,
                        source,
                        options,
                        session,
                        diagnostics,
                        &captured_flow_types,
                        &preflighted_type_import_value_uses,
                        &mut deferred,
                        &arrow.source.callable,
                        &arrow.parameter_initializers,
                    )?;
                    let expression = match &arrow.body {
                        PlannedArrowBody::Empty => None,
                        PlannedArrowBody::Return { expression, .. } => Some(expression),
                    };
                    publish_checked_source_callable_return(
                        store,
                        host,
                        global_types,
                        source,
                        options,
                        session,
                        diagnostics,
                        &body_flow_types,
                        &preflighted_type_import_value_uses,
                        &mut deferred,
                        &arrow.source.callable,
                        materialized.signature,
                        expression,
                    )?;
                }
                stage_value_type(
                    store,
                    &mut staged_value_types,
                    &mut value_order,
                    arrow.source.variable_symbol,
                    materialized.type_,
                )?;
                if current_flow_types
                    .insert(arrow.source.variable_symbol, materialized.type_)
                    .is_some()
                {
                    return Err(SourceCheckError::Variable(
                        VariableInvariant::DuplicateCurrentFlowType(arrow.source.variable_symbol),
                    ));
                }
            }
            PlannedStatement::ContextualArrow(index) => {
                let arrow = contextual_arrows
                    .get(index)
                    .ok_or(SourceCheckError::Arrow(source.node_ref()))?;
                let (target, _) = materialize_contextual_source_arrow(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    &arrow.source,
                )?;
                stage_value_type(
                    store,
                    &mut staged_value_types,
                    &mut value_order,
                    arrow.source.variable_symbol,
                    target,
                )?;
                if current_flow_types
                    .insert(arrow.source.variable_symbol, target)
                    .is_some()
                {
                    return Err(SourceCheckError::Variable(
                        VariableInvariant::DuplicateCurrentFlowType(arrow.source.variable_symbol),
                    ));
                }
            }
            PlannedStatement::Variables(variables) => {
                for variable in variables {
                    let (declared_type, current_flow_type) = match (
                        &variable.initializer,
                        variable.type_node,
                    ) {
                        (PlannedVariableInitializer::Expression(initializer), Some(type_node)) => {
                            let assignment = check_planned_assignment(
                                store,
                                host,
                                global_types,
                                source,
                                options,
                                session,
                                diagnostics,
                                &current_flow_types,
                                &preflighted_type_import_value_uses,
                                &mut deferred,
                                type_node,
                                type_import_capabilities
                                    .get(&type_node)
                                    .map_or(&[], Vec::as_slice),
                                initializer,
                                variable.name,
                                None,
                            )?;
                            (
                                assignment.declared_type,
                                current_flow_type_after_assignment(
                                    store,
                                    host,
                                    global_types,
                                    options,
                                    session,
                                    diagnostics,
                                    assignment,
                                )?,
                            )
                        }
                        (PlannedVariableInitializer::Expression(initializer), None)
                            if variable.jsdoc_type.is_some() =>
                        {
                            let annotation = variable
                                .jsdoc_type
                                .as_ref()
                                .expect("the match guard checked the JSDoc annotation");
                            let declared_type = resolve_planned_jsdoc_type(
                                store,
                                global_types,
                                options,
                                annotation,
                            )
                            .map_err(|_| {
                                SourceCheckError::Unsupported(UnsupportedSourceSyntax::JsDoc(
                                    variable.declaration,
                                ))
                            })?;
                            let assignment = check_assignment_to_type(
                                store,
                                host,
                                global_types,
                                source,
                                options,
                                session,
                                diagnostics,
                                &current_flow_types,
                                &preflighted_type_import_value_uses,
                                &mut deferred,
                                declared_type,
                                initializer,
                                variable.name,
                                None,
                            )?;
                            (
                                assignment.declared_type,
                                current_flow_type_after_assignment(
                                    store,
                                    host,
                                    global_types,
                                    options,
                                    session,
                                    diagnostics,
                                    assignment,
                                )?,
                            )
                        }
                        (PlannedVariableInitializer::Expression(initializer), None) => {
                            let initializer = check_expression_type(
                                store,
                                host,
                                global_types,
                                source,
                                options,
                                session,
                                diagnostics,
                                &current_flow_types,
                                &preflighted_type_import_value_uses,
                                initializer,
                                None,
                                &mut deferred,
                            )?;
                            let declared_type = inferred_variable_type(
                                store,
                                global_types,
                                variable.binding,
                                initializer.result,
                            )?;
                            let current_flow_type = current_flow_type_after_assignment(
                                store,
                                host,
                                global_types,
                                options,
                                session,
                                diagnostics,
                                CheckedAssignment {
                                    declared_type,
                                    assigned_type: initializer.result,
                                },
                            )?;
                            (declared_type, current_flow_type)
                        }
                        (PlannedVariableInitializer::Jsx(initializer), type_node) => {
                            let mut jsx_diagnostics = CanonicalCheckerDiagnostics::default();
                            let jsx_type = store.check_jsx_element(
                                host,
                                *initializer,
                                options,
                                &mut jsx_diagnostics,
                            );
                            merge_retry_diagnostics(diagnostics, jsx_diagnostics);
                            let jsx_type = jsx_type?;
                            let declared_type = if let Some(type_node) = type_node {
                                let mut annotation_diagnostics =
                                    CanonicalCheckerDiagnostics::default();
                                let type_reference_alias_targets: &[CanonicalTypeReferenceAliasTarget] =
                                    type_import_capabilities
                                        .get(&type_node)
                                        .map_or(&[], Vec::as_slice);
                                let declared_type =
                                    CanonicalTypeQuery::new_with_global_types_and_session(
                                        store,
                                        host,
                                        global_types,
                                        options,
                                        session,
                                        &mut annotation_diagnostics,
                                    )?
                                    .with_type_reference_alias_targets(
                                        type_reference_alias_targets.iter().copied(),
                                    )?
                                    .get_type_from_type_node(type_node);
                                merge_retry_diagnostics(diagnostics, annotation_diagnostics);
                                let declared_type = declared_type?;
                                if !source_type_is_assignable_to(
                                    store,
                                    host,
                                    global_types,
                                    options,
                                    session,
                                    diagnostics,
                                    jsx_type,
                                    declared_type,
                                )? {
                                    let mut flags =
                                        CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
                                    if options.no_error_truncation {
                                        flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
                                    }
                                    let display =
                                        get_type_names_for_assignability_error_with_host_global_types_and_flags(
                                            store,
                                            host,
                                            global_types,
                                            jsx_type,
                                            declared_type,
                                            flags,
                                        )?;
                                    merge_retry_diagnostic(
                                        diagnostics,
                                        CanonicalCheckerDiagnostic {
                                            node: Some(variable.name),
                                            range_override: None,
                                            diagnostic: Diagnostic::with_arguments(
                                                message_by_code(2322).ok_or(
                                                    SourceCheckError::MissingDiagnostic(2322),
                                                )?,
                                                [display.source, display.target],
                                            ),
                                            related_information: Vec::new(),
                                        },
                                    );
                                }
                                declared_type
                            } else {
                                inferred_variable_type(
                                    store,
                                    global_types,
                                    variable.binding,
                                    jsx_type,
                                )?
                            };
                            let current_flow_type = current_flow_type_after_assignment(
                                store,
                                host,
                                global_types,
                                options,
                                session,
                                diagnostics,
                                CheckedAssignment {
                                    declared_type,
                                    assigned_type: jsx_type,
                                },
                            )?;
                            (declared_type, current_flow_type)
                        }
                        (PlannedVariableInitializer::AbsentAnnotated, Some(type_node)) => {
                            let mut annotation_diagnostics = CanonicalCheckerDiagnostics::default();
                            let type_reference_alias_targets: &[CanonicalTypeReferenceAliasTarget] =
                                type_import_capabilities
                                    .get(&type_node)
                                    .map_or(&[], Vec::as_slice);
                            let declared_type =
                                CanonicalTypeQuery::new_with_global_types_and_session(
                                    store,
                                    host,
                                    global_types,
                                    options,
                                    session,
                                    &mut annotation_diagnostics,
                                )?
                                .with_type_reference_alias_targets(
                                    type_reference_alias_targets.iter().copied(),
                                )?
                                .get_type_from_type_node(type_node);
                            merge_retry_diagnostics(diagnostics, annotation_diagnostics);
                            let declared_type = declared_type?;
                            (declared_type, declared_type)
                        }
                        (PlannedVariableInitializer::AbsentJavaScript, None) => {
                            let declared_type = if let Some(annotation) = &variable.jsdoc_type {
                                resolve_planned_jsdoc_type(store, global_types, options, annotation)
                                    .map_err(|_| {
                                        SourceCheckError::Unsupported(
                                            UnsupportedSourceSyntax::JsDoc(variable.declaration),
                                        )
                                    })?
                            } else {
                                store
                                    .intrinsic_bootstrap()
                                    .ok_or(SourceCheckError::LiteralCache(
                                        SourceLiteralCacheError::BootstrapUninitialized,
                                    ))?
                                    .any_type
                            };
                            (declared_type, declared_type)
                        }
                        (PlannedVariableInitializer::AbsentAnnotated, None)
                        | (PlannedVariableInitializer::AbsentJavaScript, Some(_)) => {
                            return Err(SourceCheckError::Variable(
                                VariableInvariant::InvalidSymbolShape(variable.symbol),
                            ));
                        }
                    };
                    stage_value_type(
                        store,
                        &mut staged_value_types,
                        &mut value_order,
                        variable.symbol,
                        declared_type,
                    )?;
                    if top_level_declared_types
                        .insert(variable.symbol, declared_type)
                        .is_some()
                    {
                        return Err(SourceCheckError::Variable(
                            VariableInvariant::DuplicateStagedValueType(variable.symbol),
                        ));
                    }
                    if !variable.binding.is_const() && !mutable_variables.insert(variable.symbol) {
                        return Err(SourceCheckError::Variable(
                            VariableInvariant::DuplicateCurrentFlowType(variable.symbol),
                        ));
                    }
                    if current_flow_types
                        .insert(variable.symbol, current_flow_type)
                        .is_some()
                    {
                        return Err(SourceCheckError::Variable(
                            VariableInvariant::DuplicateCurrentFlowType(variable.symbol),
                        ));
                    }
                }
            }
            PlannedStatement::Assignment(assignment) => {
                let staged_declared_type = *top_level_declared_types
                    .get(&assignment.target_symbol)
                    .ok_or(SourceCheckError::Variable(
                        VariableInvariant::MissingStagedValueType(assignment.target_symbol),
                    ))?;
                if !current_flow_types.contains_key(&assignment.target_symbol) {
                    return Err(SourceCheckError::Variable(
                        VariableInvariant::MissingCurrentFlowType(assignment.target_symbol),
                    ));
                }
                let checked = match assignment.target_type_node {
                    Some(type_node) => check_planned_assignment(
                        store,
                        host,
                        global_types,
                        source,
                        options,
                        session,
                        diagnostics,
                        &current_flow_types,
                        &preflighted_type_import_value_uses,
                        &mut deferred,
                        type_node,
                        &[],
                        &assignment.right,
                        assignment.left,
                        Some(assignment.expression),
                    ),
                    None => check_assignment_to_type(
                        store,
                        host,
                        global_types,
                        source,
                        options,
                        session,
                        diagnostics,
                        &current_flow_types,
                        &preflighted_type_import_value_uses,
                        &mut deferred,
                        staged_declared_type,
                        &assignment.right,
                        assignment.left,
                        Some(assignment.expression),
                    ),
                }?;
                if checked.declared_type != staged_declared_type {
                    return Err(SourceCheckError::Variable(
                        VariableInvariant::AssignmentDeclaredTypeMismatch {
                            symbol: assignment.target_symbol,
                            staged: staged_declared_type,
                            resolved: checked.declared_type,
                        },
                    ));
                }
                let current_flow_type = current_flow_type_after_assignment(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    checked,
                )?;
                current_flow_types.insert(assignment.target_symbol, current_flow_type);
            }
            PlannedStatement::ExpressionCall(expression) => {
                if !matches!(&expression.kind, PlannedExpressionKind::Call(_)) {
                    return Err(SourceCheckError::Call(expression.node));
                }
                check_expression_type(
                    store,
                    host,
                    global_types,
                    source,
                    options,
                    session,
                    diagnostics,
                    &current_flow_types,
                    &preflighted_type_import_value_uses,
                    &expression,
                    None,
                    &mut deferred,
                )?;
            }
        }
    }

    let captured_flow_types = captured_callable_flow_types(
        &current_flow_types,
        &top_level_declared_types,
        &mutable_variables,
    )?;
    for arrow in &arrows {
        if arrow.source.callable.return_type.is_inferred() {
            continue;
        }
        session.reset_query();
        let Some(return_type) = arrow.source.callable.return_type.type_node() else {
            return Err(SourceCheckError::Arrow(arrow.source.callable.declaration));
        };
        let body_flow_types = check_callable_parameter_initializers(
            store,
            host,
            global_types,
            source,
            options,
            session,
            diagnostics,
            &captured_flow_types,
            &preflighted_type_import_value_uses,
            &mut deferred,
            &arrow.source.callable,
            &arrow.parameter_initializers,
        )?;
        match &arrow.body {
            PlannedArrowBody::Empty => {}
            PlannedArrowBody::Return {
                diagnostic_node,
                expression,
            } => {
                session.reset_query();
                check_planned_assignment(
                    store,
                    host,
                    global_types,
                    source,
                    options,
                    session,
                    diagnostics,
                    &body_flow_types,
                    &preflighted_type_import_value_uses,
                    &mut deferred,
                    return_type,
                    &[],
                    expression,
                    *diagnostic_node,
                    None,
                )?;
            }
        }
    }

    validate_deferred_assertions(store, source, &deferred)?;
    check_deferred_assertions(
        store,
        host,
        global_types,
        options,
        session,
        diagnostics,
        &deferred,
    )?;
    let import_publications =
        preflight_prepared_source_import_publications(store, &prepared_imports)
            .map_err(|error| SourcePlanner::import_plan_error(source.node_ref(), &error))?;
    publish_staged_variable_state(
        store,
        source.node_ref(),
        &staged_value_types,
        &value_order,
        &import_publications,
        &identifier_reads,
    )?;

    Ok(())
}

pub(super) fn publish_type_checked(
    store: &mut CanonicalTypeMapperStore,
    source: SourceFileRef,
) -> Result<(), SourceCheckError> {
    let mut links = store
        .source_file_links(source)
        .cloned()
        .unwrap_or_else(SourceFileLinks::default);
    links.type_checked = true;
    if !store.set_source_file_links(source, links) {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::SourceLinkPublication(source),
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use ts_ast::NodeFlags;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalProgramBindings, CanonicalSourceFileFacts, CanonicalSourceLanguage, CheckFlags,
        EscapedName, InternalSymbolName, SymbolData, SymbolFlags,
    };
    use ts_diagnostics::Category;
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        AliasTargetState, CanonicalCheckerContext, DeclaredTypeHostError,
        IntrinsicBootstrapOptions, RelationStateSnapshot, TypeAliasLinks, TypeNodeUnavailable,
        module_resolution::{
            CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
            CanonicalModuleResolutionMode, CanonicalResolvedModuleInput,
        },
        object_members::{
            DeclaredPropertyObjectProof, DeclaredPropertyObjectValidation,
            validate_resolved_declared_property_object,
        },
        production::GlobalMergeCompletion,
        type_records::TypeData,
        types::ObjectFlags,
    };

    type ObservableSourceState = (
        [usize; 5],
        [usize; 26],
        usize,
        usize,
        RelationStateSnapshot,
        usize,
        usize,
        usize,
        bool,
        usize,
    );

    fn parsed(text: &str) -> ParseResult {
        let parsed = parse_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn source_facts_with_module_state(
        file: FileId,
        module_state: CanonicalModuleState,
    ) -> CanonicalSourceFileFacts {
        CanonicalSourceFileFacts::new(
            EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
            CanonicalSourceLanguage::TypeScript,
            false,
            module_state,
        )
    }

    fn completed_bindings(files: &[(FileId, &ParseResult)]) -> CanonicalProgramBindings {
        completed_bindings_with_module_state(files, CanonicalModuleState::Script)
    }

    fn completed_bindings_with_module_state(
        files: &[(FileId, &ParseResult)],
        module_state: CanonicalModuleState,
    ) -> CanonicalProgramBindings {
        let mut binder = CanonicalBinder::new();
        for &(file, parsed) in files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    source_facts_with_module_state(file, module_state),
                )
                .unwrap();
        }
        for &(file, parsed) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        binder.finish()
    }

    fn context<'arena>(
        files: &[(FileId, &'arena ParseResult)],
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'arena> {
        context_with_module_state(files, CanonicalModuleState::Script, options)
    }

    fn context_with_module_state<'arena>(
        files: &[(FileId, &'arena ParseResult)],
        module_state: CanonicalModuleState,
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'arena> {
        CanonicalCheckerContext::new(
            completed_bindings_with_module_state(files, module_state),
            files
                .iter()
                .map(|(file, parsed)| (*file, &parsed.arena))
                .collect(),
            options,
        )
        .unwrap()
    }

    fn context_with_declaration_facts<'arena>(
        file: FileId,
        source: &'arena ParseResult,
        module_state: CanonicalModuleState,
        is_declaration_file: bool,
    ) -> CanonicalCheckerContext<'arena> {
        let extension = if is_declaration_file { "d.ts" } else { "ts" };
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/project/{}.{extension}\"", file.index())),
                    CanonicalSourceLanguage::TypeScript,
                    is_declaration_file,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&source.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    #[derive(Clone, Copy)]
    struct SourceImportRoute {
        source: usize,
        specifier: usize,
        target: usize,
    }

    fn source_import_specifiers(parsed: &ParseResult) -> Vec<NodeId> {
        let mut specifiers = parsed
            .arena
            .iter()
            .filter_map(|(_, record)| match &record.data {
                NodeData::ImportDeclaration(import) => Some(import.module_specifier),
                _ => None,
            })
            .collect::<Vec<_>>();
        specifiers.sort_unstable_by_key(|node| parsed.arena.get(*node).unwrap().range.start);
        specifiers
    }

    fn external_context_with_import_routes<'arena>(
        files: &[(FileId, &'arena ParseResult)],
        routes: &[SourceImportRoute],
    ) -> CanonicalCheckerContext<'arena> {
        let entries = routes.iter().map(|route| {
            let (source_file, source) = files[route.source];
            let specifier = source_import_specifiers(source)[route.specifier];
            CanonicalModuleResolutionEntry::resolved(
                NodeRef::new(source.arena.id(), source_file, specifier),
                CanonicalResolvedModuleInput::new(
                    files[route.target].0,
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::Esm,
                ),
            )
        });
        CanonicalCheckerContext::new_with_module_resolutions(
            completed_bindings_with_module_state(files, CanonicalModuleState::External),
            files
                .iter()
                .map(|(file, parsed)| (*file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new(entries),
        )
        .unwrap()
    }

    fn context_with_file_module_states<'arena>(
        files: &[(FileId, &'arena ParseResult, CanonicalModuleState)],
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'arena> {
        let mut binder = CanonicalBinder::new();
        for &(file, parsed, module_state) in files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    source_facts_with_module_state(file, module_state),
                )
                .unwrap();
        }
        for &(file, parsed, _) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .iter()
                .map(|(file, parsed, _)| (*file, &parsed.arena))
                .collect(),
            options,
        )
        .unwrap()
    }

    fn context_with_default_library_files<'arena>(
        files: &[(FileId, &'arena ParseResult)],
        default_library_files: &[FileId],
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'arena> {
        let mut binder = CanonicalBinder::new();
        for &(file, parsed) in files {
            let is_default_library = default_library_files.contains(&file);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        is_default_library,
                        is_default_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for &(file, parsed) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .iter()
                .map(|(file, parsed)| (*file, &parsed.arena))
                .collect(),
            options,
        )
        .unwrap()
    }

    fn variable_name(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        let name = parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::VariableDeclaration(variable) = &node.data else {
                    return None;
                };
                let name = parsed.arena.get(variable.name)?;
                let NodeData::Identifier(identifier) = &name.data else {
                    return None;
                };
                (identifier.text == expected).then_some(variable.name)
            })
            .unwrap_or_else(|| panic!("missing variable {expected}"));
        NodeRef::new(parsed.arena.id(), file, name)
    }

    fn variable_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        let name = variable_name(parsed, file, expected);
        let declaration = parsed.arena.get(name.node).unwrap().parent.unwrap();
        NodeRef::new(parsed.arena.id(), file, declaration)
    }

    fn function_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::FunctionDeclaration(function) = &record.data else {
                    return None;
                };
                let name = parsed.arena.get(function.name?)?;
                let NodeData::Identifier(identifier) = &name.data else {
                    return None;
                };
                (identifier.text == expected).then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap_or_else(|| panic!("missing function {expected}"))
    }

    fn function_symbol(
        context: &CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        file: FileId,
        expected: &str,
    ) -> SemanticSymbolId {
        let declaration = function_declaration(parsed, file, expected);
        let (_, bound) = context.file(file).unwrap();
        let raw = bound.symbol(declaration).unwrap();
        context.store().get_merged_symbol(raw).unwrap()
    }

    fn function_return_statement(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        let declaration = function_declaration(parsed, file, expected);
        let NodeData::FunctionDeclaration(function) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let body = function.body.unwrap();
        let NodeData::Block(block) = &parsed.arena.get(body).unwrap().data else {
            unreachable!()
        };
        let [statement] = block.statements.nodes.as_slice() else {
            panic!("function {expected} does not have one statement")
        };
        NodeRef::new(parsed.arena.id(), file, *statement)
    }

    fn arrow_return_statement(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        let initializer = variable_initializer(parsed, file, expected);
        let NodeData::ArrowFunction(arrow) = &parsed.arena.get(initializer.node).unwrap().data
        else {
            panic!("variable {expected} does not have an arrow initializer")
        };
        let NodeData::Block(block) = &parsed.arena.get(arrow.body).unwrap().data else {
            panic!("arrow {expected} does not have a block body")
        };
        let [statement] = block.statements.nodes.as_slice() else {
            panic!("arrow {expected} does not have one statement")
        };
        NodeRef::new(parsed.arena.id(), file, *statement)
    }

    fn arrow_body(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        let initializer = variable_initializer(parsed, file, expected);
        let NodeData::ArrowFunction(arrow) = &parsed.arena.get(initializer.node).unwrap().data
        else {
            panic!("variable {expected} does not have an arrow initializer")
        };
        NodeRef::new(parsed.arena.id(), file, arrow.body)
    }

    fn variable_symbol(
        context: &CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        file: FileId,
        expected: &str,
    ) -> SemanticSymbolId {
        let declaration = variable_declaration(parsed, file, expected);
        let (_, bound) = context.file(file).unwrap();
        let raw = bound.symbol(declaration).unwrap();
        context.store().get_merged_symbol(raw).unwrap()
    }

    fn variable_value_type(
        context: &CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        file: FileId,
        expected: &str,
    ) -> TypeId {
        let symbol = variable_symbol(context, parsed, file, expected);
        context
            .store()
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type)
            .unwrap_or_else(|| panic!("missing value type for {expected}"))
    }

    fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        let initializer = parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::VariableDeclaration(variable) = &node.data else {
                    return None;
                };
                let name = parsed.arena.get(variable.name)?;
                let NodeData::Identifier(identifier) = &name.data else {
                    return None;
                };
                (identifier.text == expected)
                    .then_some(variable.initializer)
                    .flatten()
            })
            .unwrap_or_else(|| panic!("missing initializer for variable {expected}"));
        NodeRef::new(parsed.arena.id(), file, initializer)
    }

    fn identifier_expressions(parsed: &ParseResult, file: FileId, expected: &str) -> Vec<NodeRef> {
        parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::Identifier(identifier) = &record.data else {
                    return None;
                };
                if identifier.text != expected {
                    return None;
                }
                let is_declaration_name = record
                    .parent
                    .and_then(|parent| parsed.arena.get(parent))
                    .is_some_and(|parent| {
                        matches!(
                            &parent.data,
                            NodeData::VariableDeclaration(variable) if variable.name == node
                        ) || matches!(
                            &parent.data,
                            NodeData::FunctionDeclaration(function) if function.name == Some(node)
                        ) || matches!(
                            &parent.data,
                            NodeData::ParameterDeclaration(parameter) if parameter.name == node
                        )
                    });
                (!is_declaration_name).then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .collect()
    }

    fn variable_type_node(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        let type_node = parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::VariableDeclaration(variable) = &node.data else {
                    return None;
                };
                let name = parsed.arena.get(variable.name)?;
                let NodeData::Identifier(identifier) = &name.data else {
                    return None;
                };
                (identifier.text == expected)
                    .then_some(variable.type_)
                    .flatten()
            })
            .unwrap_or_else(|| panic!("missing type node for variable {expected}"));
        NodeRef::new(parsed.arena.id(), file, type_node)
    }

    fn type_alias_body(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        let type_node = parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::TypeAliasDeclaration(alias) = &node.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(alias.name)?.data else {
                    return None;
                };
                (identifier.text == expected).then_some(alias.type_)
            })
            .unwrap_or_else(|| panic!("missing type alias {expected}"));
        NodeRef::new(parsed.arena.id(), file, type_node)
    }

    fn assignment_parts(parsed: &ParseResult, file: FileId, index: usize) -> (NodeRef, NodeRef) {
        let statement = parsed
            .arena
            .get(parsed.source_file)
            .and_then(|source| match &source.data {
                NodeData::SourceFile(source) => source
                    .statements
                    .nodes
                    .iter()
                    .filter_map(|statement| {
                        let statement = parsed.arena.get(*statement)?;
                        let NodeData::ExpressionStatement(statement) = &statement.data else {
                            return None;
                        };
                        let expression = parsed.arena.get(statement.expression)?;
                        let NodeData::BinaryExpression(binary) = &expression.data else {
                            return None;
                        };
                        Some((binary.left, binary.right))
                    })
                    .nth(index),
                _ => None,
            })
            .unwrap_or_else(|| panic!("missing assignment {index}"));
        (
            NodeRef::new(parsed.arena.id(), file, statement.0),
            NodeRef::new(parsed.arena.id(), file, statement.1),
        )
    }

    fn primitive_binary_parts(
        parsed: &ParseResult,
        file: FileId,
        expression: NodeRef,
    ) -> (NodeRef, NodeRef) {
        let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.node).unwrap().data
        else {
            panic!("expected binary expression")
        };
        (
            NodeRef::new(parsed.arena.id(), file, binary.left),
            NodeRef::new(parsed.arena.id(), file, binary.right),
        )
    }

    fn array_elements(parsed: &ParseResult, file: FileId, array: NodeRef) -> Vec<NodeRef> {
        let NodeData::ArrayLiteralExpression(array) = &parsed.arena.get(array.node).unwrap().data
        else {
            panic!("expected array literal")
        };
        array
            .elements
            .nodes
            .iter()
            .map(|element| NodeRef::new(parsed.arena.id(), file, *element))
            .collect()
    }

    fn node_text(parsed: &ParseResult, node: NodeRef) -> &str {
        let range = parsed.arena.get(node.node).unwrap().range;
        let source = parsed.arena.source_text().unwrap();
        &source
            [usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
    }

    fn assert_property_name_span(
        parsed: &ParseResult,
        node: NodeRef,
        expected: &str,
        source_property: bool,
    ) {
        let record = parsed.arena.get(node.node).unwrap();
        assert_eq!(record.kind, SyntaxKind::Identifier);
        assert_eq!(node_text(parsed, node), expected);
        let parent = parsed.arena.get(record.parent.unwrap()).unwrap();
        if source_property {
            assert_eq!(parent.kind, SyntaxKind::PropertyAssignment);
        } else {
            assert!(matches!(
                parent.kind,
                SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature
            ));
        }
    }

    fn object_property_initializer(
        parsed: &ParseResult,
        file: FileId,
        object: NodeRef,
        expected: &str,
    ) -> NodeRef {
        let object_record = parsed.arena.get(object.node).unwrap();
        let NodeData::ObjectLiteralExpression(object_data) = &object_record.data else {
            panic!("expected object literal")
        };
        let initializer = object_data
            .properties
            .nodes
            .iter()
            .find_map(|property| {
                let property = parsed.arena.get(*property)?;
                let NodeData::PropertyAssignment(property) = &property.data else {
                    return None;
                };
                let name = parsed.arena.get(property.name)?;
                let NodeData::Identifier(name) = &name.data else {
                    return None;
                };
                (name.text == expected).then_some(property.initializer)
            })
            .unwrap_or_else(|| panic!("missing object property {expected}"));
        NodeRef::new(parsed.arena.id(), file, initializer)
    }

    fn object_property_type(
        context: &CanonicalCheckerContext<'_>,
        object: NodeRef,
        expected: &str,
    ) -> TypeId {
        let store = context.store();
        let object = store
            .type_node_links(object)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let TypeData::Object(object) = store.type_payload(object).unwrap().data() else {
            panic!("expected object type")
        };
        let property = store
            .symbol_table(object.structured.members.unwrap())
            .and_then(|members| members.get_source(expected))
            .unwrap_or_else(|| panic!("missing resolved object property {expected}"));
        store
            .value_symbol_links(property)
            .and_then(|links| links.resolved_type)
            .unwrap()
    }

    fn declared_object_property_symbol(
        context: &CanonicalCheckerContext<'_>,
        object: TypeId,
        expected: &str,
    ) -> SemanticSymbolId {
        let store = context.store();
        let structured = store
            .type_payload(object)
            .and_then(|record| record.data().structured())
            .unwrap_or_else(|| panic!("expected structured target {object:?}"));
        store
            .symbol_table(structured.members.unwrap())
            .and_then(|members| members.get_source(expected))
            .unwrap_or_else(|| panic!("missing declared object property {expected}"))
    }

    fn global_symbol(context: &CanonicalCheckerContext<'_>, expected: &str) -> SemanticSymbolId {
        context
            .store()
            .symbol_table(context.globals())
            .and_then(|globals| globals.get_source(expected))
            .unwrap_or_else(|| panic!("missing global symbol {expected}"))
    }

    fn array_element_in_union(
        context: &CanonicalCheckerContext<'_>,
        union: TypeId,
    ) -> (TypeId, TypeId) {
        let TypeData::Union(data) = context.store().type_payload(union).unwrap().data() else {
            panic!("expected canonical union {union:?}")
        };
        data.union
            .types
            .iter()
            .find_map(|constituent| {
                context
                    .store()
                    .canonical_array_reference(context.global_types(), *constituent)
                    .ok()
                    .flatten()
                    .map(|array| (*constituent, array.element_type))
            })
            .unwrap_or_else(|| panic!("union {union:?} has no canonical array constituent"))
    }

    fn resolved_node_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
        context
            .store()
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
            .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
    }

    fn is_type_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
        context
            .source_file(file)
            .and_then(|source| context.store().source_file_links(source))
            .is_some_and(|links| links.type_checked)
    }

    fn mark_source_unchecked(context: &mut CanonicalCheckerContext<'_>, file: FileId) {
        let source = context.source_file(file).unwrap();
        let mut links = context.store().source_file_links(source).cloned().unwrap();
        links.type_checked = false;
        assert!(
            context
                .store_mut_for_test()
                .set_source_file_links(source, links)
        );
    }

    fn observable_state(
        context: &CanonicalCheckerContext<'_>,
        file: FileId,
    ) -> ObservableSourceState {
        let store = context.store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        (
            [
                store.type_len(),
                store.signature_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
            ],
            store.checker_link_allocated_lengths(),
            store.type_resolution_len(),
            store.type_resolution_start(),
            store.relation_state_snapshot(),
            bootstrap.string_literal_cache_len(),
            bootstrap.number_literal_cache_len(),
            bootstrap.bigint_literal_cache_len(),
            is_type_checked(context, file),
            context.diagnostics().len(),
        )
    }

    fn type_reference_nodes(parsed: &ParseResult, file: FileId, expected: &str) -> Vec<NodeRef> {
        let mut references = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::TypeReferenceNode(reference) = &record.data else {
                    return None;
                };
                let name = parsed.arena.get(reference.type_name)?;
                matches!(
                    &name.data,
                    NodeData::Identifier(identifier) if identifier.text == expected
                )
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .collect::<Vec<_>>();
        references.sort_unstable_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
        references
    }

    fn source_import_alias_symbol(
        context: &CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        file: FileId,
        expected: &str,
    ) -> SemanticSymbolId {
        let binding = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ImportSpecifier(specifier) = &record.data else {
                    return None;
                };
                let name = parsed.arena.get(specifier.name)?;
                matches!(
                    &name.data,
                    NodeData::Identifier(identifier) if identifier.text == expected
                )
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap_or_else(|| panic!("missing import binding {expected}"));
        let (_, bound) = context.file(file).unwrap();
        let symbol = bound.symbol(binding).unwrap();
        context.store().get_merged_symbol(symbol).unwrap()
    }

    fn resolved_import_target(
        context: &CanonicalCheckerContext<'_>,
        alias: SemanticSymbolId,
    ) -> SemanticSymbolId {
        match context
            .store()
            .alias_symbol_links(alias)
            .unwrap_or_else(|| panic!("missing alias links for {alias:?}"))
            .alias_target
        {
            AliasTargetState::Resolved(target) => target,
            state => panic!("import alias {alias:?} is not resolved: {state:?}"),
        }
    }

    #[test]
    fn top_level_namespaces_execute_before_same_file_jsx_initializers() {
        let source = ts_parser::parse_jsx_source_file(concat!(
            "declare namespace JSX { ",
            "interface Element {} ",
            "interface IntrinsicElements { div: { label: string } } ",
            "} ",
            "const view = <div label=\"ready\" />;",
        ));
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let file = FileId::new(8_260);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let view = variable_symbol(&context, &source, file, "view");

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert!(
            context
                .store()
                .value_symbol_links(view)
                .and_then(|links| links.resolved_type)
                .is_some()
        );
        let warm = observable_state(&context, file);
        context.recheck_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn unsupported_namespace_members_reject_prior_source_publication() {
        let source = parsed(concat!(
            "const earlier = 1; ",
            "namespace Blocked { export function unsupported(): void {} }",
        ));
        let file = FileId::new(8_261);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let earlier = variable_symbol(&context, &source, file, "earlier");
        let cold = observable_state(&context, file);

        for _ in 0..2 {
            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Syntax { .. }
                ))
            ));
            assert_eq!(observable_state(&context, file), cold);
            assert!(context.store().value_symbol_links(earlier).is_none());
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn jsx_variable_initializers_check_intrinsic_attributes_and_replay_warm() {
        let declarations = parsed(concat!(
            "declare namespace JSX { ",
            "interface Element {} ",
            "interface IntrinsicElements { div: { label: string } } ",
            "}",
        ));
        let source = ts_parser::parse_jsx_source_file(concat!(
            "const good = <div label=\"ready\" />; ",
            "const bad = <div label={1} />;",
        ));
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let declarations_file = FileId::new(3_790);
        let file = FileId::new(3_791);
        let mut context = context(
            &[(declarations_file, &declarations), (file, &source)],
            CanonicalCheckerOptions::default(),
        );
        let good = variable_symbol(&context, &source, file, "good");
        let bad = variable_symbol(&context, &source, file, "bad");

        context.check_source_file(file).unwrap();

        for symbol in [good, bad] {
            assert!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .and_then(|links| links.resolved_type)
                    .is_some()
            );
        }
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one JSX attribute diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        context.recheck_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn unsupported_jsx_spread_rejects_the_complete_source_before_publication() {
        let declarations = parsed(concat!(
            "declare namespace JSX { ",
            "interface Element {} ",
            "interface IntrinsicElements { div: {} } ",
            "}",
        ));
        let source = ts_parser::parse_jsx_source_file(concat!(
            "const earlier = 1; ",
            "const view = <div {...props} />;",
        ));
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let declarations_file = FileId::new(3_792);
        let file = FileId::new(3_793);
        let mut context = context(
            &[(declarations_file, &declarations), (file, &source)],
            CanonicalCheckerOptions::default(),
        );
        let earlier = variable_symbol(&context, &source, file, "earlier");
        let cold = observable_state(&context, file);

        for _ in 0..2 {
            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Syntax { .. }
                ))
            ));
            assert_eq!(observable_state(&context, file), cold);
            assert!(context.store().value_symbol_links(earlier).is_none());
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn type_only_import_annotations_check_direct_roots_in_both_program_orders() {
        let importer = parsed(
            r#"
                import type { User as Local } from "./target";
                const good: Local = { id: 1 };
                const bad: Local = { id: "wrong" };
            "#,
        );
        let target = parsed("export type User = { id: number };");
        let importer_file = FileId::new(900);
        let target_file = FileId::new(901);
        let files = [(importer_file, &importer), (target_file, &target)];
        let route = [SourceImportRoute {
            source: 0,
            specifier: 0,
            target: 1,
        }];

        let mut importer_first = external_context_with_import_routes(&files, &route);
        importer_first.check_source_file(importer_file).unwrap();
        assert_eq!(
            importer_first
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            vec![2322]
        );
        assert!(is_type_checked(&importer_first, importer_file));
        assert!(!is_type_checked(&importer_first, target_file));
        let alias = source_import_alias_symbol(&importer_first, &importer, importer_file, "Local");
        let target_symbol = resolved_import_target(&importer_first, alias);
        assert!(importer_first.store().value_symbol_links(alias).is_none());
        assert!(
            importer_first
                .store()
                .value_symbol_links(target_symbol)
                .is_none()
        );
        let references = type_reference_nodes(&importer, importer_file, "Local");
        assert_eq!(references.len(), 2);
        let declared = variable_value_type(&importer_first, &importer, importer_file, "good");
        assert_eq!(
            variable_value_type(&importer_first, &importer, importer_file, "bad"),
            declared
        );
        for reference in &references {
            assert_eq!(resolved_node_type(&importer_first, *reference), declared);
            assert_eq!(
                importer_first
                    .store()
                    .symbol_node_links(*reference)
                    .and_then(|links| links.resolved_symbol),
                Some(target_symbol)
            );
        }
        let warm = observable_state(&importer_first, importer_file);
        mark_source_unchecked(&mut importer_first, importer_file);
        importer_first.check_source_file(importer_file).unwrap();
        assert_eq!(observable_state(&importer_first, importer_file), warm);

        let mut target_first = external_context_with_import_routes(&files, &route);
        target_first.check_source_file(target_file).unwrap();
        target_first.check_source_file(importer_file).unwrap();
        assert_eq!(
            target_first
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            vec![2322]
        );
        assert!(is_type_checked(&target_first, target_file));
        assert!(is_type_checked(&target_first, importer_file));
    }

    #[test]
    fn unused_type_only_import_resolves_without_materializing_value_or_declared_type() {
        let importer = parsed(
            r#"
                import type { User as Local } from "./target";
                const value = 1;
            "#,
        );
        let target = parsed("export type User = { id: number };");
        let importer_file = FileId::new(902);
        let target_file = FileId::new(903);
        let files = [(importer_file, &importer), (target_file, &target)];
        let mut context = external_context_with_import_routes(
            &files,
            &[SourceImportRoute {
                source: 0,
                specifier: 0,
                target: 1,
            }],
        );

        context.check_source_file(importer_file).unwrap();

        let alias = source_import_alias_symbol(&context, &importer, importer_file, "Local");
        let target_symbol = resolved_import_target(&context, alias);
        assert!(context.store().value_symbol_links(alias).is_none());
        assert!(context.store().value_symbol_links(target_symbol).is_none());
        assert_eq!(
            context
                .store()
                .type_alias_links(target_symbol)
                .and_then(|links| links.declared_type),
            None
        );
        assert_eq!(
            context
                .store()
                .alias_symbol_links(alias)
                .and_then(|links| links.type_only_declaration),
            context
                .store()
                .symbol(alias)
                .and_then(|symbol| symbol.declarations())
                .and_then(|declarations| declarations.first())
                .copied()
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, importer_file));
        assert!(!is_type_checked(&context, target_file));
    }

    #[test]
    fn type_only_import_value_use_reports_ts1361_and_returns_error_type_without_value_state() {
        let importer = parsed(
            r#"
                import type { User as Local } from "./target";
                const invalid = Local;
            "#,
        );
        let target = parsed("export type User = { id: number };");
        let importer_file = FileId::new(904);
        let target_file = FileId::new(905);
        let files = [(importer_file, &importer), (target_file, &target)];
        let mut context = external_context_with_import_routes(
            &files,
            &[SourceImportRoute {
                source: 0,
                specifier: 0,
                target: 1,
            }],
        );

        context.check_source_file(importer_file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one type-only value-use diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 1361);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "'Local' cannot be used as a value because it was imported using 'import type'."
        );
        let alias = source_import_alias_symbol(&context, &importer, importer_file, "Local");
        let target_symbol = resolved_import_target(&context, alias);
        let initializer = variable_initializer(&importer, importer_file, "invalid");
        let error_type = context.store().intrinsic_bootstrap().unwrap().error_type;
        assert_eq!(resolved_node_type(&context, initializer), error_type);
        assert_eq!(
            variable_value_type(&context, &importer, importer_file, "invalid"),
            error_type
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(initializer)
                .and_then(|links| links.resolved_symbol),
            Some(alias)
        );
        assert!(context.store().value_symbol_links(alias).is_none());
        assert!(context.store().value_symbol_links(target_symbol).is_none());
        assert_eq!(
            context
                .store()
                .type_alias_links(target_symbol)
                .and_then(|links| links.declared_type),
            None
        );
        let warm = observable_state(&context, importer_file);
        mark_source_unchecked(&mut context, importer_file);
        context.check_source_file(importer_file).unwrap();
        assert_eq!(observable_state(&context, importer_file), warm);
    }

    #[test]
    fn poisoned_type_only_value_use_fails_before_earlier_publications_and_retries_in_order() {
        let importer = parsed(
            r#"
                import type { User as Local } from "./target";
                const earlier: number = "wrong";
                const invalid = Local;
            "#,
        );
        let target = parsed("export type User = number;");
        let importer_file = FileId::new(912);
        let target_file = FileId::new(913);
        let files = [(importer_file, &importer), (target_file, &target)];
        let mut context = external_context_with_import_routes(
            &files,
            &[SourceImportRoute {
                source: 0,
                specifier: 0,
                target: 1,
            }],
        );
        let initializer = variable_initializer(&importer, importer_file, "invalid");
        let earlier_symbol = variable_symbol(&context, &importer, importer_file, "earlier");
        let (poison, error_type) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.error_type)
        };
        assert_ne!(poison, error_type);
        assert!(context.store_mut_for_test().set_type_node_links(
            initializer,
            TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            }
        ));

        assert!(matches!(
            context.check_source_file(importer_file),
            Err(SourceCheckError::Assertion(
                SourceAssertionError::InvalidExpressionCache {
                    node,
                    cached: Some(cached),
                    expected,
                }
            )) if node == initializer && cached == poison && expected == error_type
        ));
        assert!(context.diagnostics().is_empty());
        assert!(context.store().value_symbol_links(earlier_symbol).is_none());
        assert!(context.store().symbol_node_links(initializer).is_none());
        assert!(!is_type_checked(&context, importer_file));
        assert_eq!(resolved_node_type(&context, initializer), poison);

        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(initializer, TypeNodeLinks::default())
        );
        context.check_source_file(importer_file).unwrap();
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2322, 1361]
        );
        assert!(context.store().value_symbol_links(earlier_symbol).is_some());
        assert_eq!(resolved_node_type(&context, initializer), error_type);
        assert!(is_type_checked(&context, importer_file));
    }

    #[test]
    fn separate_leading_value_and_type_imports_preserve_both_routes() {
        let importer = parsed(
            r#"
                import { count as localCount } from "./target";
                import type { User as LocalUser } from "./target";
                const copy = localCount;
                const user: LocalUser = { id: localCount };
            "#,
        );
        let target = parsed(
            r"
                export const count: number = 1;
                export type User = { id: number };
            ",
        );
        let importer_file = FileId::new(906);
        let target_file = FileId::new(907);
        let files = [(importer_file, &importer), (target_file, &target)];
        let mut context = external_context_with_import_routes(
            &files,
            &[
                SourceImportRoute {
                    source: 0,
                    specifier: 0,
                    target: 1,
                },
                SourceImportRoute {
                    source: 0,
                    specifier: 1,
                    target: 1,
                },
            ],
        );

        context.check_source_file(importer_file).unwrap();

        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            variable_value_type(&context, &importer, importer_file, "copy"),
            number
        );
        let value_alias =
            source_import_alias_symbol(&context, &importer, importer_file, "localCount");
        let type_alias =
            source_import_alias_symbol(&context, &importer, importer_file, "LocalUser");
        assert_eq!(
            context
                .store()
                .value_symbol_links(value_alias)
                .and_then(|links| links.resolved_type),
            Some(number)
        );
        assert!(context.store().value_symbol_links(type_alias).is_none());
        assert!(
            context
                .store()
                .value_symbol_links(resolved_import_target(&context, type_alias))
                .is_none()
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, importer_file));
        assert!(!is_type_checked(&context, target_file));
        context.check_source_file(target_file).unwrap();
        assert!(is_type_checked(&context, target_file));
    }

    #[test]
    fn local_alias_callable_and_assertion_type_imports_fail_before_source_publication() {
        let target = parsed("export type User = number;");
        for (index, body) in [
            "type Wrapped = Local;",
            "function accept(value: Local): void {}",
            "const asserted = null as Local;",
            "function identity<T>(value: T): T { return value; } const called = identity<Local>(1);",
        ]
        .into_iter()
        .enumerate()
        {
            let importer = parsed(&format!(
                "import type {{ User as Local }} from './target'; const earlier: number = 1; {body}"
            ));
            let importer_file = FileId::new(920 + u32::try_from(index).unwrap());
            let target_file = FileId::new(930 + u32::try_from(index).unwrap());
            let files = [(importer_file, &importer), (target_file, &target)];
            let mut context = external_context_with_import_routes(
                &files,
                &[SourceImportRoute {
                    source: 0,
                    specifier: 0,
                    target: 1,
                }],
            );
            let earlier = variable_symbol(&context, &importer, importer_file, "earlier");
            let cold = observable_state(&context, importer_file);

            for _ in 0..2 {
                assert!(matches!(
                    context.check_source_file(importer_file),
                    Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Import(_)
                    ))
                ));
                assert_eq!(observable_state(&context, importer_file), cold);
                assert!(context.store().value_symbol_links(earlier).is_none());
                assert!(!is_type_checked(&context, importer_file));
                assert!(context.diagnostics().is_empty());
            }
        }
    }

    #[test]
    fn composite_import_source_roots_reject_nonzero_wrapper_flags_without_publication() {
        let target = parsed("export type User = number;");
        for (index, kind) in [
            SyntaxKind::UnionType,
            SyntaxKind::ParenthesizedType,
            SyntaxKind::ArrayType,
        ]
        .into_iter()
        .enumerate()
        {
            let mut importer = parsed(
                "import type { User as Local } from './target'; const value: (Local | null)[] = [];",
            );
            let flagged = importer
                .arena
                .iter()
                .find_map(|(node, record)| (record.kind == kind).then_some(node))
                .expect("fixture contains every composite wrapper");
            importer.arena.get_mut(flagged).unwrap().flags = NodeFlags(1);
            let importer_file = FileId::new(950 + u32::try_from(index).unwrap() * 2);
            let target_file = FileId::new(951 + u32::try_from(index).unwrap() * 2);
            let files = [(importer_file, &importer), (target_file, &target)];
            let mut context = external_context_with_import_routes(
                &files,
                &[SourceImportRoute {
                    source: 0,
                    specifier: 0,
                    target: 1,
                }],
            );
            let cold = observable_state(&context, importer_file);

            for _ in 0..2 {
                assert!(matches!(
                    context.check_source_file(importer_file),
                    Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Import(_)
                    ))
                ));
                assert_eq!(observable_state(&context, importer_file), cold);
                assert!(context.diagnostics().is_empty());
                assert!(!is_type_checked(&context, importer_file));
            }
        }
    }

    #[test]
    fn composite_declaration_capability_is_closed_to_later_assignment_before_execution() {
        let importer = parsed(
            r#"
                import type { User as Local } from "./target";
                var value: Local | null = null;
                value = null;
            "#,
        );
        let target = parsed("export type User = number;");
        let importer_file = FileId::new(910);
        let target_file = FileId::new(911);
        let files = [(importer_file, &importer), (target_file, &target)];
        let mut context = external_context_with_import_routes(
            &files,
            &[SourceImportRoute {
                source: 0,
                specifier: 0,
                target: 1,
            }],
        );
        let root = variable_type_node(&importer, importer_file, "value");
        let alias = source_import_alias_symbol(&context, &importer, importer_file, "Local");
        let cold = observable_state(&context, importer_file);

        for _ in 0..2 {
            assert_eq!(
                context.check_source_file(importer_file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Import(root)
                ))
            );
            assert_eq!(observable_state(&context, importer_file), cold);
            assert!(
                context
                    .store()
                    .value_symbol_links(variable_symbol(
                        &context,
                        &importer,
                        importer_file,
                        "value",
                    ))
                    .is_none()
            );
            assert!(context.store().value_symbol_links(alias).is_none());
            assert!(!is_type_checked(&context, importer_file));
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn direct_declaration_capability_is_not_reused_by_a_later_assignment() {
        let importer = parsed(
            r#"
                import type { User as Local } from "./target";
                var value: Local = { id: 1 };
                value = { id: 2 };
            "#,
        );
        let target = parsed("export type User = { id: number };");
        let importer_file = FileId::new(912);
        let target_file = FileId::new(913);
        let files = [(importer_file, &importer), (target_file, &target)];
        let mut context = external_context_with_import_routes(
            &files,
            &[SourceImportRoute {
                source: 0,
                specifier: 0,
                target: 1,
            }],
        );
        let references = type_reference_nodes(&importer, importer_file, "Local");
        let [reference] = references.as_slice() else {
            panic!("expected one imported type reference")
        };
        let alias = source_import_alias_symbol(&context, &importer, importer_file, "Local");
        let cold = observable_state(&context, importer_file);

        for _ in 0..2 {
            assert_eq!(
                context.check_source_file(importer_file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Import(*reference)
                ))
            );
            assert_eq!(observable_state(&context, importer_file), cold);
            assert!(
                context
                    .store()
                    .value_symbol_links(variable_symbol(
                        &context,
                        &importer,
                        importer_file,
                        "value",
                    ))
                    .is_none()
            );
            assert!(context.store().value_symbol_links(alias).is_none());
            assert!(!is_type_checked(&context, importer_file));
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn poisoned_later_type_import_reference_fails_before_earlier_source_publications() {
        let importer = parsed(
            r#"
                import type { User as Local } from "./target";
                const first: Local = { id: 1 };
                const second: Local = { id: 2 };
            "#,
        );
        let target = parsed("export type User = { id: number };");
        let importer_file = FileId::new(908);
        let target_file = FileId::new(909);
        let files = [(importer_file, &importer), (target_file, &target)];
        let mut context = external_context_with_import_routes(
            &files,
            &[SourceImportRoute {
                source: 0,
                specifier: 0,
                target: 1,
            }],
        );
        let references = type_reference_nodes(&importer, importer_file, "Local");
        let [first_reference, second_reference] = references.as_slice() else {
            panic!("expected two direct imported type references")
        };
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            *second_reference,
            TypeNodeLinks {
                resolved_type: Some(number),
                ..TypeNodeLinks::default()
            },
        ));

        assert_eq!(
            context.check_source_file(importer_file),
            Err(SourceCheckError::Import(*second_reference))
        );

        let alias = source_import_alias_symbol(&context, &importer, importer_file, "Local");
        assert!(context.store().value_symbol_links(alias).is_none());
        assert!(
            context
                .store()
                .value_symbol_links(variable_symbol(&context, &importer, importer_file, "first"))
                .is_none()
        );
        assert!(context.store().type_node_links(*first_reference).is_none());
        assert!(!is_type_checked(&context, importer_file));
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn poisoned_composite_import_roots_preflight_before_variables_and_callables() {
        let target = parsed("export type Count = number;");
        for (index, poisoned_name) in ["unionValue", "arrayValue"].into_iter().enumerate() {
            let importer = parsed(
                r#"
                    import type { Count as LocalCount } from "./target";
                    const earlier: number = 1;
                    function callable(value: number): number { return value; }
                    const unionValue: LocalCount | null = null;
                    const arrayValue: LocalCount[] = [];
                "#,
            );
            let importer_file = FileId::new(940 + u32::try_from(index).unwrap() * 2);
            let target_file = FileId::new(941 + u32::try_from(index).unwrap() * 2);
            let files = [(importer_file, &importer), (target_file, &target)];
            let mut context = external_context_with_import_routes(
                &files,
                &[SourceImportRoute {
                    source: 0,
                    specifier: 0,
                    target: 1,
                }],
            );
            let root = variable_type_node(&importer, importer_file, poisoned_name);
            let other_root = variable_type_node(
                &importer,
                importer_file,
                if poisoned_name == "unionValue" {
                    "arrayValue"
                } else {
                    "unionValue"
                },
            );
            let earlier_type = variable_type_node(&importer, importer_file, "earlier");
            let earlier_initializer = variable_initializer(&importer, importer_file, "earlier");
            let earlier = variable_symbol(&context, &importer, importer_file, "earlier");
            let callable_declaration = function_declaration(&importer, importer_file, "callable");
            let callable = function_symbol(&context, &importer, importer_file, "callable");
            let imported_references = type_reference_nodes(&importer, importer_file, "LocalCount");
            let alias =
                source_import_alias_symbol(&context, &importer, importer_file, "LocalCount");
            let poison = context.store().intrinsic_bootstrap().unwrap().string_type;
            assert!(context.store_mut_for_test().set_type_node_links(
                root,
                TypeNodeLinks {
                    resolved_type: Some(poison),
                    ..TypeNodeLinks::default()
                },
            ));

            let first = context.check_source_file(importer_file).unwrap_err();
            if poisoned_name == "unionValue" {
                assert_eq!(
                    first,
                    SourceCheckError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::InvalidCachedUnionType(poison),
                    ))
                );
            } else {
                assert_eq!(
                    first,
                    SourceCheckError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::InvalidTypeReference(root),
                    ))
                );
            }
            let target = resolved_import_target(&context, alias);
            assert!(context.store().alias_symbol_links(alias).is_some());
            assert!(context.store().value_symbol_links(alias).is_none());
            assert!(context.store().value_symbol_links(target).is_none());
            assert!(context.store().type_alias_links(target).is_none());
            assert!(context.store().value_symbol_links(earlier).is_none());
            assert!(context.store().value_symbol_links(callable).is_none());
            assert!(context.store().type_node_links(earlier_type).is_none());
            assert!(
                context
                    .store()
                    .type_node_links(earlier_initializer)
                    .is_none()
            );
            assert!(
                context
                    .store()
                    .type_node_links(callable_declaration)
                    .is_none()
            );
            assert!(context.store().type_node_links(other_root).is_none());
            for reference in &imported_references {
                assert!(context.store().type_node_links(*reference).is_none());
                assert!(context.store().symbol_node_links(*reference).is_none());
            }
            assert!(!is_type_checked(&context, importer_file));
            assert!(context.diagnostics().is_empty());
            assert_eq!(resolved_node_type(&context, root), poison);

            let failed = observable_state(&context, importer_file);
            for _ in 0..2 {
                assert_eq!(context.check_source_file(importer_file), Err(first));
                assert_eq!(observable_state(&context, importer_file), failed);
                assert!(context.store().value_symbol_links(earlier).is_none());
                assert!(context.store().value_symbol_links(callable).is_none());
                assert!(context.store().type_node_links(earlier_type).is_none());
                assert!(context.store().type_node_links(other_root).is_none());
                assert!(!is_type_checked(&context, importer_file));
                assert!(context.diagnostics().is_empty());
            }
        }
    }

    #[test]
    fn top_level_enum_materializes_value_and_declared_identities_and_replays_warm() {
        let source = parsed(r#"enum Status { Ready, Running = 3, Label = "label" }"#);
        let file = FileId::new(410);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let owner = global_symbol(&context, "Status");

        context.check_source_file(file).unwrap();

        let declared = context
            .store()
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .expect("enum declared type must be published");
        let value = context
            .store()
            .value_symbol_links(owner)
            .and_then(|links| links.resolved_type)
            .expect("enum value type must be published");
        assert_ne!(declared, value);
        assert!(context.store().type_payload(declared).is_some());
        assert!(context.store().type_payload(value).is_some());
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
        assert_eq!(
            context
                .store()
                .value_symbol_links(owner)
                .and_then(|links| links.resolved_type),
            Some(value)
        );
    }

    #[test]
    fn unsupported_later_enum_prevents_earlier_enum_publication() {
        let source = parsed("enum Good { A } enum Bad { A = runtime }");
        let file = FileId::new(411);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let good = global_symbol(&context, "Good");
        let bad = source
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::EnumDeclaration)
            .map(|(node, _)| NodeRef::new(source.arena.id(), file, node))
            .nth(1)
            .expect("second enum declaration must exist");
        let before = observable_state(&context, file);

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Enum(bad)
            ))
        );
        assert_eq!(observable_state(&context, file), before);
        assert!(context.store().declared_type_links(good).is_none());
        assert!(context.store().value_symbol_links(good).is_none());
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }

    #[test]
    fn top_level_class_materializes_members_in_source_execution_and_replays_warm() {
        let source = parsed(concat!(
            "class Model { ",
            "readonly value?: string; ",
            "definite!: number; ",
            "static count: number; ",
            "}",
        ));
        let file = FileId::new(417);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let owner = global_symbol(&context, "Model");

        context.check_source_file(file).unwrap();

        let members = context.get_nongeneric_class_members(owner).unwrap();
        assert_eq!(members.instance_properties().len(), 2);
        assert_eq!(members.static_properties().len(), 1);
        assert_eq!(
            context
                .store()
                .declared_type_links(owner)
                .and_then(|links| links.declared_type),
            Some(members.shells().instance_type())
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(owner)
                .and_then(|links| links.resolved_type),
            Some(members.shells().value_type())
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn earlier_statement_failure_prevents_later_class_execution() {
        let source = parsed(concat!(
            "type Broken = string;\n",
            "class Later { value?: string; static count: number; }\n",
        ));
        let file = FileId::new(418);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let alias = global_symbol(&context, "Broken");
        let class = global_symbol(&context, "Later");
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_type_alias_links(
            alias,
            TypeAliasLinks {
                declared_type: Some(number),
                type_parameters: Some(Vec::new()),
                ..TypeAliasLinks::default()
            },
        ));
        let before = observable_state(&context, file);

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::DeclaredType(
                DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::InvalidCachedTypeAlias(alias)
                )
            ))
        );
        assert_eq!(observable_state(&context, file), before);
        assert!(context.store().declared_type_links(class).is_none());
        assert!(context.store().value_symbol_links(class).is_none());
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }

    #[test]
    fn later_poisoned_class_preflights_before_earlier_publication_and_repairs() {
        let source = parsed(concat!(
            "class Early { value?: string; }\n",
            "class Later { value!: number; static count: number; }\n",
        ));
        let file = FileId::new(419);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let early = global_symbol(&context, "Early");
        let later = global_symbol(&context, "Later");
        let later_declaration = context
            .store()
            .symbol(later)
            .and_then(|symbol| symbol.declarations())
            .and_then(|declarations| declarations.first())
            .copied()
            .expect("Later has one declaration");
        let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            later,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned = observable_state(&context, file);

        for _ in 0..2 {
            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Class(later_declaration))
            );
            assert_eq!(observable_state(&context, file), poisoned);
            assert!(context.store().declared_type_links(early).is_none());
            assert!(context.store().value_symbol_links(early).is_none());
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }

        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(later, ValueSymbolLinks::default())
        );
        context.check_source_file(file).unwrap();
        assert_eq!(
            context
                .get_nongeneric_class_members(early)
                .unwrap()
                .instance_properties()
                .len(),
            1
        );
        assert_eq!(
            context
                .get_nongeneric_class_members(later)
                .unwrap()
                .static_properties()
                .len(),
            1
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn inferred_object_property_read_publishes_exact_type_and_symbol_and_replays_warm() {
        let source = parsed("const object = { value: 1 }; const result = object.value;");
        let file = FileId::new(480);
        let access = variable_initializer(&source, file, "result");
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            variable_value_type(&context, &source, file, "result"),
            number
        );
        assert_eq!(resolved_node_type(&context, access), number);
        let property = context
            .store()
            .symbol_node_links(access)
            .and_then(|links| links.resolved_symbol)
            .expect("property symbol must be retained");
        assert!(context.store().symbol(property).is_some());
        assert!(context.diagnostics().is_empty());

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(property)
        );
    }

    #[test]
    fn property_read_keeps_its_type_for_assignment_diagnostics() {
        let source = parsed(concat!(
            "interface Model { value: string } ",
            "const object: Model = { value: 'ok' }; ",
            "const result: number = object.value;",
        ));
        let file = FileId::new(481);
        let access = variable_initializer(&source, file, "result");
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let (string, number) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        assert_eq!(resolved_node_type(&context, access), string);
        assert_eq!(
            variable_value_type(&context, &source, file, "result"),
            number
        );
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one property assignment diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn arrow_capture_reads_a_prior_object_property() {
        let source =
            parsed("const object = { value: 1 }; const read = (): number => object.value;");
        let file = FileId::new(414);
        let access = arrow_body(&source, file, "read");
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(resolved_node_type(&context, access), number);
        assert!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol)
                .is_some()
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn property_reads_remain_context_insensitive_in_arrays_objects_and_calls() {
        let source = parsed(concat!(
            "const object = { value: 1 }; ",
            "function take(value: number): number { return 1; } ",
            "const array = [object.value]; ",
            "const copy = { value: object.value }; ",
            "const called = take(object.value);",
        ));
        let file = FileId::new(416);
        let array = variable_initializer(&source, file, "array");
        let array_elements = array_elements(&source, file, array);
        let [array_access] = array_elements.as_slice() else {
            panic!("array must contain one property read")
        };
        let copy = variable_initializer(&source, file, "copy");
        let object_access = object_property_initializer(&source, file, copy, "value");
        let call = variable_initializer(&source, file, "called");
        let NodeData::CallExpression(call_data) = &source.arena.get(call.node).unwrap().data else {
            panic!("called must have a call initializer")
        };
        let [call_access] = call_data.arguments.nodes.as_slice() else {
            panic!("call must contain one property argument")
        };
        let call_access = NodeRef::new(source.arena.id(), file, *call_access);
        let accesses = [*array_access, object_access, call_access];
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        for access in accesses {
            assert_eq!(resolved_node_type(&context, access), number);
            assert!(
                context
                    .store()
                    .symbol_node_links(access)
                    .and_then(|links| links.resolved_symbol)
                    .is_some()
            );
        }
        assert_eq!(object_property_type(&context, copy, "value"), number);
        assert_eq!(
            variable_value_type(&context, &source, file, "called"),
            number
        );
        assert!(context.diagnostics().is_empty());

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn declared_union_read_access_cache_poison_retains_memo_and_repairs_warm() {
        let source = parsed(concat!(
            "type Left = { value: string }; ",
            "type Right = { value: number }; ",
            "type Both = Left | Right; ",
            "function read(input: Both): string | number { return (input.value); }",
        ));
        let file = FileId::new(482);
        let (access, receiver) = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::PropertyAccessExpression(access) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(source.arena.id(), file, node),
                    NodeRef::new(source.arena.id(), file, access.expression),
                ))
            })
            .expect("fixture must contain one property read");
        let root = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ParenthesizedExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .expect("fixture must contain one parenthesized root");
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let poison = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            access,
            TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            },
        ));

        let error = SourceCheckError::Property(access);
        assert_eq!(context.check_source_file(file), Err(error));
        let union = resolved_node_type(&context, receiver);
        let property = {
            let TypeData::Union(union) = context.store().type_payload(union).unwrap().data() else {
                panic!("receiver must remain a union")
            };
            let cache = union
                .union
                .property_cache
                .expect("rejected access must retain its safe union-property memo");
            context
                .store()
                .symbol_table(cache)
                .and_then(|cache| cache.get_source("value"))
                .expect("full union property must be cached")
        };
        let property_type = context
            .store()
            .value_symbol_links(property)
            .and_then(|links| links.resolved_type)
            .expect("cached union property must retain its value type");
        assert_ne!(property_type, poison);
        assert_eq!(resolved_node_type(&context, access), poison);
        assert!(context.store().symbol_node_links(access).is_none());
        assert!(context.store().type_node_links(root).is_none());
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));

        let rejected = observable_state(&context, file);
        assert_eq!(context.check_source_file(file), Err(error));
        assert_eq!(observable_state(&context, file), rejected);

        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(access, TypeNodeLinks::default())
        );
        context.check_source_file(file).unwrap();
        assert_eq!(resolved_node_type(&context, access), property_type);
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(property)
        );
        assert_eq!(resolved_node_type(&context, root), property_type);
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(property)
        );
    }

    #[test]
    fn optional_property_read_publishes_strict_union_and_replays_warm() {
        let source = parsed(concat!(
            "interface Model { value?: string } ",
            "const object: Model = {}; ",
            "const result = object.value;",
        ));
        let file = FileId::new(415);
        let access = variable_initializer(&source, file, "result");
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = context(&[(file, &source)], options);

        context.check_source_file(file).unwrap();

        let (string, undefined) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.undefined_or_missing_type)
        };
        let result = resolved_node_type(&context, access);
        let TypeData::Union(union) = context.store().type_payload(result).unwrap().data() else {
            panic!("strict optional property reads must produce a union")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&string));
        assert!(union.union.types.contains(&undefined));
        assert_eq!(
            variable_value_type(&context, &source, file, "result"),
            result
        );
        let object = variable_value_type(&context, &source, file, "object");
        let property = declared_object_property_symbol(&context, object, "value");
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(property)
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
        assert_eq!(resolved_node_type(&context, access), result);
        assert_eq!(
            context
                .store()
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(property)
        );
    }

    #[test]
    fn inferred_primitive_variables_publish_const_and_mutable_identities() {
        let source = parsed(concat!(
            "const first = 1, sameList = first; ",
            "let mutableNumber = 2; var varNumber = 3; ",
            "const text = \"text\"; let mutableText = \"mutable\"; ",
            "const bigint = 1n; var mutableBigint = 2n; ",
            "const truth = true; let mutableTruth = false; ",
            "const constAlias = first; let letAlias = first; var varAlias = first; ",
            "const annotated: number = 4;",
        ));
        let file = FileId::new(200);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let (number, string, bigint, boolean) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.bigint_type,
                bootstrap.boolean_type,
            )
        };
        let first = variable_value_type(&context, &source, file, "first");
        assert_eq!(
            first,
            resolved_node_type(&context, variable_initializer(&source, file, "first"))
        );
        assert_ne!(first, number);
        assert_eq!(
            variable_value_type(&context, &source, file, "sameList"),
            first
        );
        assert_eq!(
            variable_value_type(&context, &source, file, "constAlias"),
            first
        );
        for name in [
            "mutableNumber",
            "varNumber",
            "letAlias",
            "varAlias",
            "annotated",
        ] {
            assert_eq!(variable_value_type(&context, &source, file, name), number);
        }
        assert_ne!(
            resolved_node_type(&context, variable_initializer(&source, file, "annotated")),
            number
        );
        assert_eq!(
            variable_value_type(&context, &source, file, "text"),
            resolved_node_type(&context, variable_initializer(&source, file, "text"))
        );
        assert_eq!(
            variable_value_type(&context, &source, file, "mutableText"),
            string
        );
        assert_eq!(
            variable_value_type(&context, &source, file, "bigint"),
            resolved_node_type(&context, variable_initializer(&source, file, "bigint"))
        );
        assert_eq!(
            variable_value_type(&context, &source, file, "mutableBigint"),
            bigint
        );
        assert_eq!(
            variable_value_type(&context, &source, file, "truth"),
            resolved_node_type(&context, variable_initializer(&source, file, "truth"))
        );
        assert_eq!(
            variable_value_type(&context, &source, file, "mutableTruth"),
            boolean
        );

        let first_symbol = variable_symbol(&context, &source, file, "first");
        let reads = identifier_expressions(&source, file, "first");
        assert_eq!(reads.len(), 4);
        for read in reads {
            assert_eq!(resolved_node_type(&context, read), first);
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(read)
                    .and_then(|links| links.resolved_symbol),
                Some(first_symbol)
            );
        }
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn inferred_object_and_array_variables_widen_nested_mutable_locations() {
        let library = parsed("interface Array<T> {}");
        let source = parsed(concat!(
            "interface Exact { value: 1 } const seed = 1; ",
            "const values = [seed]; const matrix = [[seed]]; ",
            "const object = { value: seed, nested: { label: \"x\" }, values: [seed] }; ",
            "let mutableObject = { value: 2 }; ",
            "const exact: Exact = { value: seed }; ",
            "const undefined = \"shadow\"; const shadowed = { missing: undefined };",
        ));
        let library_file = FileId::new(201);
        let file = FileId::new(202);
        let mut context = context_with_file_module_states(
            &[
                (library_file, &library, CanonicalModuleState::Script),
                (file, &source, CanonicalModuleState::External),
            ],
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(file).unwrap();

        let seed = variable_value_type(&context, &source, file, "seed");
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let values = variable_initializer(&source, file, "values");
        let matrix = variable_initializer(&source, file, "matrix");
        let object = variable_initializer(&source, file, "object");
        let mutable_object = variable_initializer(&source, file, "mutableObject");
        let exact = variable_initializer(&source, file, "exact");
        let shadowed = variable_initializer(&source, file, "shadowed");
        assert_eq!(
            context
                .type_to_string(variable_value_type(&context, &source, file, "values"))
                .unwrap(),
            "number[]"
        );
        assert_eq!(
            context
                .type_to_string(variable_value_type(&context, &source, file, "matrix"))
                .unwrap(),
            "number[][]"
        );
        assert_ne!(
            variable_value_type(&context, &source, file, "values"),
            resolved_node_type(&context, values)
        );
        assert_ne!(
            variable_value_type(&context, &source, file, "matrix"),
            resolved_node_type(&context, matrix)
        );
        assert_ne!(
            variable_value_type(&context, &source, file, "object"),
            resolved_node_type(&context, object)
        );
        assert_ne!(
            variable_value_type(&context, &source, file, "mutableObject"),
            resolved_node_type(&context, mutable_object)
        );
        assert_eq!(object_property_type(&context, object, "value"), number);
        let nested = object_property_initializer(&source, file, object, "nested");
        assert_eq!(
            context
                .type_to_string(object_property_type(&context, nested, "label"))
                .unwrap(),
            "string"
        );
        assert_eq!(
            context
                .type_to_string(object_property_type(&context, object, "values"))
                .unwrap(),
            "number[]"
        );
        assert_eq!(
            object_property_type(&context, mutable_object, "value"),
            number
        );
        let TypeData::Literal(seed_literal) = context.store().type_payload(seed).unwrap().data()
        else {
            panic!("expected a fresh seed literal")
        };
        assert_eq!(
            object_property_type(&context, exact, "value"),
            seed_literal.regular_type
        );
        assert_eq!(
            context
                .type_to_string(object_property_type(&context, shadowed, "missing"))
                .unwrap(),
            "string"
        );
        for read in identifier_expressions(&source, file, "seed") {
            assert_eq!(resolved_node_type(&context, read), seed);
        }
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn exported_inferred_variables_route_reads_through_local_export_symbols() {
        let source = parsed(concat!(
            "export const exposed = 1; ",
            "const localAlias = exposed; export let widened = exposed;",
        ));
        let file = FileId::new(203);
        let mut context = context_with_module_state(
            &[(file, &source)],
            CanonicalModuleState::External,
            CanonicalCheckerOptions::default(),
        );
        let exposed_declaration = variable_declaration(&source, file, "exposed");
        let exposed_local = {
            let (_, bound) = context.file(file).unwrap();
            bound.local_symbol(exposed_declaration).unwrap()
        };

        context.check_source_file(file).unwrap();

        let exposed = variable_symbol(&context, &source, file, "exposed");
        let exposed_type = variable_value_type(&context, &source, file, "exposed");
        assert_ne!(exposed_local, exposed);
        assert_eq!(
            context
                .store()
                .value_symbol_links(exposed_local)
                .and_then(|links| links.resolved_type),
            None
        );
        assert_eq!(
            variable_value_type(&context, &source, file, "localAlias"),
            exposed_type
        );
        assert_eq!(
            variable_value_type(&context, &source, file, "widened"),
            context.store().intrinsic_bootstrap().unwrap().number_type
        );
        let reads = identifier_expressions(&source, file, "exposed");
        assert_eq!(reads.len(), 2);
        for read in reads {
            assert_eq!(resolved_node_type(&context, read), exposed_type);
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(read)
                    .and_then(|links| links.resolved_symbol),
                Some(exposed_local)
            );
        }
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn inferred_nullish_variables_follow_strictness_and_exact_auto_type_boundary() {
        let source = parsed(concat!(
            "const nil = null; const missing = undefined; ",
            "let nilAlias = nil; var missingAlias = missing; ",
            "export let exportedNil = null; export var exportedMissing = undefined;",
        ));
        let file = FileId::new(204);
        let strict_options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut strict = context_with_module_state(
            &[(file, &source)],
            CanonicalModuleState::External,
            strict_options,
        );
        let mut loose = context_with_module_state(
            &[(file, &source)],
            CanonicalModuleState::External,
            CanonicalCheckerOptions::default(),
        );

        strict.check_source_file(file).unwrap();
        loose.check_source_file(file).unwrap();

        let (null, undefined) = {
            let bootstrap = strict.store().intrinsic_bootstrap().unwrap();
            (bootstrap.null_type, bootstrap.undefined_type)
        };
        for name in ["nil", "nilAlias", "exportedNil"] {
            assert_eq!(variable_value_type(&strict, &source, file, name), null);
        }
        for name in ["missing", "missingAlias", "exportedMissing"] {
            assert_eq!(variable_value_type(&strict, &source, file, name), undefined);
        }
        let any = loose.store().intrinsic_bootstrap().unwrap().any_type;
        for name in [
            "nil",
            "missing",
            "nilAlias",
            "missingAlias",
            "exportedNil",
            "exportedMissing",
        ] {
            assert_eq!(variable_value_type(&loose, &source, file, name), any);
        }

        // Pinned tsgo-oracle (`typescript-go@dc37b524`, strictNullChecks=true
        // versus false): direct exported mutable null/undefined infer
        // null/undefined versus any. With noImplicitAny=true, non-exported
        // mutable initializers use control-flow autoType even through
        // parentheses. Canonical source-variable planning does not consume the
        // retained noImplicitAny option yet, so that exact syntax fails closed.
        for (index, text) in [
            "const prior = 1; let blocked = null;",
            "const prior = 1; let blocked = (((null)));",
            "const prior = 1; var blocked = undefined;",
            "const prior = 1; var blocked = (((undefined)));",
        ]
        .into_iter()
        .enumerate()
        {
            let blocked = parsed(text);
            let blocked_file = FileId::new(205 + u32::try_from(index).unwrap());
            let mut context = context(&[(blocked_file, &blocked)], strict_options);
            let before = observable_state(&context, blocked_file);
            assert!(matches!(
                context.check_source_file(blocked_file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Variable(
                        VariableUnsupported::InferredMutableNullishOption(node)
                    )
                )) if node == variable_declaration(&blocked, blocked_file, "blocked")
            ));
            assert_eq!(observable_state(&context, blocked_file), before);
            assert!(
                context
                    .store()
                    .value_symbol_links(variable_symbol(&context, &blocked, blocked_file, "prior"))
                    .and_then(|links| links.resolved_type)
                    .is_none()
            );
        }
    }

    #[test]
    fn inferred_empty_arrays_follow_strictness_and_exact_evolving_array_boundary() {
        let library = parsed("interface Array<T> {}");
        let source = parsed("export const direct = []; const wrapped = ([]);");
        let library_file = FileId::new(209);
        let file = FileId::new(210);
        let strict_options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        };
        let files = [
            (library_file, &library, CanonicalModuleState::Script),
            (file, &source, CanonicalModuleState::External),
        ];
        let mut strict = context_with_file_module_states(&files, strict_options);
        let mut loose = context_with_file_module_states(&files, CanonicalCheckerOptions::default());

        strict.check_source_file(file).unwrap();
        loose.check_source_file(file).unwrap();

        for name in ["direct", "wrapped"] {
            assert_eq!(
                strict
                    .type_to_string(variable_value_type(&strict, &source, file, name))
                    .unwrap(),
                "never[]"
            );
            assert_eq!(
                loose
                    .type_to_string(variable_value_type(&loose, &source, file, name))
                    .unwrap(),
                "any[]"
            );
        }

        // Pinned tsgo-oracle (`typescript-go@dc37b524`): exported direct `=[]`
        // and non-exported `=([])` are never[] for
        // strictNullChecks=true,noImplicitAny=false, and any[] for
        // strictNullChecks=false. Non-exported direct `=[]` becomes an evolving
        // auto[] when noImplicitAny=true. Canonical source-variable planning
        // does not consume that retained option yet, so only that direct syntax
        // is rejected.
        let blocked = parsed("const prior = 1; const blocked = [];");
        let blocked_file = FileId::new(211);
        let mut context = context(
            &[(library_file, &library), (blocked_file, &blocked)],
            strict_options,
        );
        let before = observable_state(&context, blocked_file);
        assert!(matches!(
            context.check_source_file(blocked_file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Variable(
                    VariableUnsupported::InferredEmptyArrayOption(node)
                )
            )) if node == variable_declaration(&blocked, blocked_file, "blocked")
        ));
        assert_eq!(observable_state(&context, blocked_file), before);
        assert!(
            context
                .store()
                .value_symbol_links(variable_symbol(&context, &blocked, blocked_file, "prior"))
                .and_then(|links| links.resolved_type)
                .is_none()
        );
    }

    #[test]
    fn inferred_identifier_reads_reject_self_forward_and_cross_file_dependencies() {
        for (index, (text, name)) in [
            ("const self = self;", "self"),
            ("const value = later; const later = 1;", "value"),
        ]
        .into_iter()
        .enumerate()
        {
            let source = parsed(text);
            let file = FileId::new(212 + u32::try_from(index).unwrap());
            let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
            let read = variable_initializer(&source, file, name);
            let before = observable_state(&context, file);
            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Variable(
                        VariableUnsupported::IdentifierNotPrior { node, .. }
                    )
                )) if node == read
            ));
            assert_eq!(observable_state(&context, file), before);
            assert!(!is_type_checked(&context, file));
        }

        let dependency = parsed("const shared = 1;");
        let source = parsed("const value = shared;");
        let dependency_file = FileId::new(214);
        let file = FileId::new(215);
        let mut context = context(
            &[(dependency_file, &dependency), (file, &source)],
            CanonicalCheckerOptions::default(),
        );
        let read = variable_initializer(&source, file, "value");
        let declaration = variable_declaration(&dependency, dependency_file, "shared");
        let before = observable_state(&context, file);
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Variable(VariableUnsupported::CrossFileDeclaration {
                    node: read,
                    declaration,
                })
            ))
        );
        assert_eq!(observable_state(&context, file), before);
        assert!(!is_type_checked(&context, file));
    }

    #[test]
    fn straight_line_variable_reads_track_exact_current_flow_types() {
        let library = parsed("interface Array<T> {} interface Boolean {}");
        let source = parsed(concat!(
            "interface Shape { value: number } ",
            "type NumericA = 1 | 2; type NumericB = NumericA | 3; ",
            "export const fixed: 1 | 2 = 1; export const fixedObserved = fixed; ",
            "export const annotatedBoolean: boolean = false; ",
            "export const annotatedBooleanObserved = annotatedBoolean; ",
            "export let mutableBoolean = false; ",
            "export const mutableBooleanObserved = mutableBoolean; ",
            "export const sameFixed: 1 | 2 = 1, sameObserved = sameFixed; ",
            "export var value: 1 | 2 = 1; export const before = value; ",
            "value = 2; export const after = value; ",
            "export var scalar: string | number = \"x\"; ",
            "export const scalarBefore = scalar; scalar = 2; ",
            "export const scalarAfter = scalar; ",
            "export var asserted: 1 | 2 = 1; asserted = 2 as 1 | 2; ",
            "export const afterAssertion = asserted; ",
            "export var shape: Shape = { value: 1 }; export const shapeBefore = shape; ",
            "shape = { value: 2 }; export const shapeAfter = shape; ",
            "export var values: number[] = [1]; export const valuesBefore = values; ",
            "values = [2]; export const valuesAfter = values; ",
            "export var neverInitial: 1 | 2 = 1 as never; ",
            "export const neverInitialObserved = neverInitial; ",
            "export var neverAssigned: 1 | 2 = 1; neverAssigned = 1 as never; ",
            "export const neverAssignedObserved = neverAssigned; ",
            "export var failed: 1 | 2 = 1; failed = 3; ",
            "export const afterFailed = failed; ",
            "export var partialFailure: 1 | 2 = 1; ",
            "partialFailure = 1 as 1 | string; ",
            "export const afterPartialFailure = partialFailure; ",
            "export var originValue: NumericB = 1 as NumericA; ",
            "export const originObserved = originValue; ",
            "export const emptyObject = {}; ",
            "export var voidOrValues: void | number[] = undefined as void; ",
            "export const voidOrValuesObserved = voidOrValues; ",
            "export var exactFalse: false = false; ",
            "export const exactFalseBefore = exactFalse; exactFalse = false; ",
            "export const exactFalseAfter = exactFalse; ",
            "export var nonUnionNever: number = 1 as never; ",
            "export const nonUnionNeverBefore = nonUnionNever; ",
            "nonUnionNever = 1 as never; ",
            "export const nonUnionNeverAfter = nonUnionNever;",
        ));
        let library_file = FileId::new(217);
        let file = FileId::new(218);
        let mut context = context_with_file_module_states(
            &[
                (library_file, &library, CanonicalModuleState::Script),
                (file, &source, CanonicalModuleState::External),
            ],
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(file).unwrap();

        let regular_literal = |context: &CanonicalCheckerContext<'_>, node| {
            let fresh = resolved_node_type(context, node);
            let TypeData::Literal(literal) = context.store().type_payload(fresh).unwrap().data()
            else {
                panic!("expected a fresh literal for {node:?}")
            };
            assert_eq!(literal.fresh_type, Some(fresh));
            literal.regular_type
        };
        assert_eq!(
            resolved_node_type(
                &context,
                variable_initializer(&source, file, "fixedObserved")
            ),
            regular_literal(&context, variable_initializer(&source, file, "fixed")),
        );
        assert_eq!(
            resolved_node_type(
                &context,
                variable_initializer(&source, file, "annotatedBooleanObserved"),
            ),
            resolved_node_type(
                &context,
                variable_initializer(&source, file, "annotatedBoolean"),
            ),
        );
        assert_eq!(
            resolved_node_type(
                &context,
                variable_initializer(&source, file, "mutableBooleanObserved"),
            ),
            resolved_node_type(
                &context,
                variable_initializer(&source, file, "mutableBoolean"),
            ),
        );
        assert_eq!(
            resolved_node_type(
                &context,
                variable_initializer(&source, file, "sameObserved")
            ),
            regular_literal(&context, variable_initializer(&source, file, "sameFixed")),
        );
        assert_eq!(
            resolved_node_type(&context, variable_initializer(&source, file, "before")),
            regular_literal(&context, variable_initializer(&source, file, "value")),
        );
        let (_, assigned_two) = assignment_parts(&source, file, 0);
        assert_eq!(
            resolved_node_type(&context, variable_initializer(&source, file, "after")),
            regular_literal(&context, assigned_two),
        );
        let (_, assigned_scalar_number) = assignment_parts(&source, file, 1);
        let (string, number) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        assert_eq!(
            resolved_node_type(
                &context,
                variable_initializer(&source, file, "scalarBefore"),
            ),
            string,
        );
        assert_eq!(
            resolved_node_type(&context, variable_initializer(&source, file, "scalarAfter"),),
            number,
        );
        assert_ne!(resolved_node_type(&context, assigned_scalar_number), number);

        for (target, observers) in [
            ("shape", ["shapeBefore", "shapeAfter"]),
            ("values", ["valuesBefore", "valuesAfter"]),
        ] {
            let declared = variable_value_type(&context, &source, file, target);
            for observer in observers {
                assert_eq!(
                    resolved_node_type(&context, variable_initializer(&source, file, observer)),
                    declared,
                );
            }
        }
        assert_eq!(
            resolved_node_type(
                &context,
                variable_initializer(&source, file, "afterAssertion"),
            ),
            variable_value_type(&context, &source, file, "asserted"),
        );
        let never = context.store().intrinsic_bootstrap().unwrap().never_type;
        for observer in ["neverInitialObserved", "neverAssignedObserved"] {
            assert_eq!(
                resolved_node_type(&context, variable_initializer(&source, file, observer)),
                never,
            );
        }
        assert_eq!(
            resolved_node_type(&context, variable_initializer(&source, file, "afterFailed")),
            variable_value_type(&context, &source, file, "failed"),
            "an invalid assignment resets the current flow type to the declaration type",
        );
        assert_eq!(
            resolved_node_type(
                &context,
                variable_initializer(&source, file, "afterPartialFailure"),
            ),
            variable_value_type(&context, &source, file, "partialFailure"),
            "a nonempty but invalid crude reduction must fall back to the declaration type",
        );

        let [empty_reduction, partial_reduction] = context.diagnostics().as_slice() else {
            panic!("expected the two failed assignment diagnostics")
        };
        assert_eq!(empty_reduction.diagnostic.code(), 2322);
        assert_eq!(empty_reduction.diagnostic.arguments, ["3", "1 | 2"]);
        assert_eq!(partial_reduction.diagnostic.code(), 2322);

        let origin_flow = resolved_node_type(
            &context,
            variable_initializer(&source, file, "originObserved"),
        );
        assert_eq!(
            origin_flow,
            resolved_node_type(&context, variable_initializer(&source, file, "originValue")),
            "filterType must preserve the sole retained named origin union",
        );
        assert_ne!(
            origin_flow,
            variable_value_type(&context, &source, file, "originValue"),
        );

        let void_type = context.store().intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(
            resolved_node_type(
                &context,
                variable_initializer(&source, file, "voidOrValuesObserved"),
            ),
            void_type,
            "void must not survive a reducer probe against the array constituent",
        );

        let exact_false_initializer =
            resolved_node_type(&context, variable_initializer(&source, file, "exactFalse"));
        let (_, exact_false_rhs) = assignment_parts(&source, file, 8);
        assert_eq!(
            resolved_node_type(&context, exact_false_rhs),
            exact_false_initializer
        );
        let exact_false_declared = variable_value_type(&context, &source, file, "exactFalse");
        assert_ne!(exact_false_declared, exact_false_initializer);
        for observer in ["exactFalseBefore", "exactFalseAfter"] {
            assert_eq!(
                resolved_node_type(&context, variable_initializer(&source, file, observer)),
                exact_false_declared,
                "non-union declared false must retain the declaration identity",
            );
        }
        let non_union_never_declared =
            variable_value_type(&context, &source, file, "nonUnionNever");
        for observer in ["nonUnionNeverBefore", "nonUnionNeverAfter"] {
            assert_eq!(
                resolved_node_type(&context, variable_initializer(&source, file, observer)),
                non_union_never_declared,
                "non-union declarations must not enter assignment reduction for never",
            );
        }

        let annotated_boolean = variable_initializer(&source, file, "annotatedBoolean");
        let fresh_false = resolved_node_type(&context, annotated_boolean);
        let regular_false = regular_literal(&context, annotated_boolean);
        let empty_object =
            resolved_node_type(&context, variable_initializer(&source, file, "emptyObject"));
        let global_types = context.global_types().clone();
        let (boolean_object, non_literal_named, nested_boolean) = {
            let store = context.store_mut_for_test();
            let boolean_object = store
                .expression_union_type_with_global_types(
                    &global_types,
                    &[regular_false, empty_object],
                    UnionReduction::Literal,
                )
                .unwrap();
            let non_literal_alias = store
                .alloc_symbol(SymbolData::new(
                    SymbolFlags::TYPE_ALIAS,
                    EscapedName::source("__FlowUnchanged"),
                ))
                .unwrap();
            let non_literal_named = store
                .literal_union_type(&[string, number], Some(non_literal_alias))
                .unwrap();
            let inner_alias = store
                .alloc_symbol(SymbolData::new(
                    SymbolFlags::TYPE_ALIAS,
                    EscapedName::source("__FlowNested"),
                ))
                .unwrap();
            let inner_boolean = store
                .literal_union_type(&[regular_false, string], Some(inner_alias))
                .unwrap();
            let nested_boolean = store
                .expression_union_type_with_global_types(
                    &global_types,
                    &[inner_boolean, number],
                    UnionReduction::Literal,
                )
                .unwrap();
            (boolean_object, non_literal_named, nested_boolean)
        };
        let mapped_boolean_object =
            map_fresh_boolean_type(context.store_mut_for_test(), &global_types, boolean_object)
                .unwrap();
        let TypeData::Union(boolean_object_union) = context
            .store()
            .type_payload(mapped_boolean_object)
            .unwrap()
            .data()
        else {
            panic!("fresh false plus an empty object must remain a mapped union")
        };
        assert!(boolean_object_union.union.types.contains(&fresh_false));
        assert!(boolean_object_union.union.types.contains(&empty_object));
        assert_eq!(
            map_fresh_boolean_type(
                context.store_mut_for_test(),
                &global_types,
                non_literal_named,
            )
            .unwrap(),
            non_literal_named,
            "an unchanged recursive map must preserve the named union identity",
        );
        let mapped_nested_boolean =
            map_fresh_boolean_type(context.store_mut_for_test(), &global_types, nested_boolean)
                .unwrap();
        assert_ne!(
            mapped_nested_boolean, nested_boolean,
            "a fresh boolean nested inside a named origin must be mapped recursively",
        );
        let TypeData::Union(nested_boolean_union) = context
            .store()
            .type_payload(mapped_nested_boolean)
            .unwrap()
            .data()
        else {
            panic!("nested fresh boolean mapping must remain a union")
        };
        assert!(nested_boolean_union.union.types.contains(&fresh_false));
        let scalar_initializer = variable_initializer(&source, file, "scalar");
        let fresh_string = resolved_node_type(&context, scalar_initializer);
        assert_eq!(
            fresh_literal_reduction_constituent(
                context.store(),
                regular_literal(&context, scalar_initializer),
            )
            .unwrap(),
            fresh_string,
            "the recursive mapper must use generic getFreshTypeOfLiteralType semantics",
        );
        assert!(is_type_checked(&context, file));

        // Pinned tsgo-oracle (`typescript-go@dc37b524`): annotated unions
        // reduce to their assigned regular constituent, boolean unions retain
        // the assigned fresh boolean, and union-declared `never` remains
        // `never`. Non-unions retain the declaration type even for fresh
        // booleans and `never`; assertions retain their asserted union; and
        // erroneous empty and nonempty crude reductions both fall back to the
        // declaration type. A retry must reproduce every identity without
        // duplicating TS2322.
        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn straight_line_flow_rejects_assignment_before_declaration_without_publication() {
        let source = parsed("target = 2; export var target: 1 | 2 = 1;");
        let file = FileId::new(219);
        let mut context = context_with_module_state(
            &[(file, &source)],
            CanonicalModuleState::External,
            CanonicalCheckerOptions::default(),
        );
        let (left, _) = assignment_parts(&source, file, 0);
        let symbol = variable_symbol(&context, &source, file, "target");
        let before = observable_state(&context, file);

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Assignment(AssignmentUnsupported::TargetNotPrior {
                    node: left,
                    symbol,
                })
            ))
        );
        assert_eq!(observable_state(&context, file), before);
        assert!(
            context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .is_none()
        );
        assert!(!is_type_checked(&context, file));

        let chained = parsed(
            "export var first: 1 | 2 = 1; export var second: 1 | 2 = 1; first = second = 2;",
        );
        let chained_file = FileId::new(220);
        let mut chained_context = context_with_module_state(
            &[(chained_file, &chained)],
            CanonicalModuleState::External,
            CanonicalCheckerOptions::default(),
        );
        let chained_before = observable_state(&chained_context, chained_file);
        assert!(matches!(
            chained_context.check_source_file(chained_file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Assignment(AssignmentUnsupported::ChainedAssignment(_))
            ))
        ));
        assert_eq!(
            observable_state(&chained_context, chained_file),
            chained_before
        );
        for name in ["first", "second"] {
            assert!(
                chained_context
                    .store()
                    .value_symbol_links(variable_symbol(
                        &chained_context,
                        &chained,
                        chained_file,
                        name,
                    ))
                    .and_then(|links| links.resolved_type)
                    .is_none()
            );
        }
    }

    #[test]
    fn variable_and_identifier_sparse_links_preflight_atomically_and_retry() {
        let source = parsed("const first = 1; const second = first; const third = second;");
        let file = FileId::new(216);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let first_symbol = variable_symbol(&context, &source, file, "first");
        let second_symbol = variable_symbol(&context, &source, file, "second");
        let third_symbol = variable_symbol(&context, &source, file, "third");
        let first_read = variable_initializer(&source, file, "second");
        let second_read = variable_initializer(&source, file, "third");
        let (number, string) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };

        assert!(context.store_mut_for_test().set_symbol_node_links(
            second_read,
            SymbolNodeLinks {
                resolved_symbol: Some(first_symbol),
            },
        ));
        let poisoned = observable_state(&context, file);
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Variable(
                VariableInvariant::InvalidSymbolNodeCache {
                    node: second_read,
                    cached: Some(first_symbol),
                    expected: second_symbol,
                }
            ))
        );
        assert_eq!(observable_state(&context, file), poisoned);
        for symbol in [first_symbol, second_symbol, third_symbol] {
            assert!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .and_then(|links| links.resolved_type)
                    .is_none()
            );
        }
        assert!(
            context
                .store_mut_for_test()
                .set_symbol_node_links(second_read, SymbolNodeLinks::default(),)
        );

        assert!(context.store_mut_for_test().set_value_symbol_links(
            third_symbol,
            ValueSymbolLinks {
                write_type: Some(number),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned = observable_state(&context, file);
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Variable(
                VariableInvariant::InvalidValueLinks(third_symbol)
            ))
        );
        assert_eq!(observable_state(&context, file), poisoned);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(third_symbol, ValueSymbolLinks::default(),)
        );

        assert!(context.store_mut_for_test().set_value_symbol_links(
            second_symbol,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        let result = context.check_source_file(file);
        let expected_second =
            resolved_node_type(&context, variable_initializer(&source, file, "first"));
        assert_eq!(
            result,
            Err(SourceCheckError::Variable(
                VariableInvariant::CachedValueTypeMismatch {
                    symbol: second_symbol,
                    cached: string,
                    expected: expected_second,
                }
            ))
        );
        assert!(
            context
                .store()
                .value_symbol_links(first_symbol)
                .and_then(|links| links.resolved_type)
                .is_none()
        );
        assert_eq!(context.store().symbol_node_links(first_read), None);
        assert_eq!(
            context
                .store()
                .symbol_node_links(second_read)
                .and_then(|links| links.resolved_symbol),
            None
        );
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(second_symbol, ValueSymbolLinks::default(),)
        );

        context.check_source_file(file).unwrap();
        assert_eq!(
            variable_value_type(&context, &source, file, "second"),
            expected_second
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(first_read)
                .and_then(|links| links.resolved_symbol),
            Some(first_symbol)
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(second_read)
                .and_then(|links| links.resolved_symbol),
            Some(second_symbol)
        );

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);

        let expected_third_links = context
            .store()
            .value_symbol_links(third_symbol)
            .cloned()
            .unwrap();
        mark_source_unchecked(&mut context, file);
        let mut poisoned_third_links = expected_third_links.clone();
        poisoned_third_links.write_type = Some(number);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(third_symbol, poisoned_third_links)
        );
        let poisoned = observable_state(&context, file);
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Variable(
                VariableInvariant::InvalidValueLinks(third_symbol)
            ))
        );
        assert_eq!(observable_state(&context, file), poisoned);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(third_symbol, expected_third_links)
        );

        assert!(context.store_mut_for_test().set_symbol_node_links(
            second_read,
            SymbolNodeLinks {
                resolved_symbol: Some(first_symbol),
            },
        ));
        let poisoned = observable_state(&context, file);
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Variable(
                VariableInvariant::InvalidSymbolNodeCache {
                    node: second_read,
                    cached: Some(first_symbol),
                    expected: second_symbol,
                }
            ))
        );
        assert_eq!(observable_state(&context, file), poisoned);
        assert!(context.store_mut_for_test().set_symbol_node_links(
            second_read,
            SymbolNodeLinks {
                resolved_symbol: Some(second_symbol),
            },
        ));
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn declaration_file_ambient_variables_publish_script_and_exported_values() {
        let cases = [
            (
                "declare const value: number;",
                CanonicalModuleState::Script,
                "number",
                true,
            ),
            (
                "export declare const value: 1;",
                CanonicalModuleState::External,
                "1",
                true,
            ),
            (
                "export const value: string;",
                CanonicalModuleState::External,
                "string",
                true,
            ),
            (
                "export declare const value: number;",
                CanonicalModuleState::External,
                "number",
                false,
            ),
        ];

        for (index, (text, module_state, expected, is_declaration_file)) in
            cases.into_iter().enumerate()
        {
            let source = parsed(text);
            let file = FileId::new(2_170 + u32::try_from(index).unwrap());
            let mut context =
                context_with_declaration_facts(file, &source, module_state, is_declaration_file);

            context.check_source_file(file).unwrap();

            let value = variable_value_type(&context, &source, file, "value");
            assert_eq!(context.type_to_string(value).unwrap(), expected);
            assert!(context.diagnostics().is_empty());
            assert!(is_type_checked(&context, file));

            let warm = observable_state(&context, file);
            mark_source_unchecked(&mut context, file);
            context.check_source_file(file).unwrap();
            assert_eq!(observable_state(&context, file), warm);
        }
    }

    #[test]
    fn declaration_file_ambient_functions_publish_script_and_exported_values() {
        let cases = [
            (
                "declare function value(): number;",
                CanonicalModuleState::Script,
                true,
            ),
            (
                "export declare function value(): number;",
                CanonicalModuleState::External,
                true,
            ),
            (
                "export function value(): number;",
                CanonicalModuleState::External,
                true,
            ),
            (
                "export declare function value(): number;",
                CanonicalModuleState::External,
                false,
            ),
        ];

        for (index, (text, module_state, is_declaration_file)) in cases.into_iter().enumerate() {
            let source = parsed(text);
            let file = FileId::new(2_180 + u32::try_from(index).unwrap());
            let mut context =
                context_with_declaration_facts(file, &source, module_state, is_declaration_file);

            context.check_source_file(file).unwrap();

            let owner = function_symbol(&context, &source, file, "value");
            let callable = context
                .store()
                .source_callable_type_for_owner(owner)
                .expect("ambient functions must publish their callable type");
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(owner)
                    .and_then(|links| links.resolved_type),
                Some(callable)
            );
            assert!(context.diagnostics().is_empty());
            assert!(is_type_checked(&context, file));

            let warm = observable_state(&context, file);
            mark_source_unchecked(&mut context, file);
            context.check_source_file(file).unwrap();
            assert_eq!(observable_state(&context, file), warm);
        }
    }

    #[test]
    fn ambient_variable_links_preflight_atomically_and_repair_warm() {
        let source = parsed(concat!(
            "declare const early: number;\n",
            "const read = early;\n",
            "declare let later: string;\n",
        ));
        let file = FileId::new(2_103);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let early = variable_symbol(&context, &source, file, "early");
        let later = variable_symbol(&context, &source, file, "later");
        let read_owner = variable_symbol(&context, &source, file, "read");
        let read = variable_initializer(&source, file, "read");
        let (number, string) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };

        assert!(context.store_mut_for_test().set_value_symbol_links(
            later,
            ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned = observable_state(&context, file);
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Variable(
                VariableInvariant::CachedValueTypeMismatch {
                    symbol: later,
                    cached: number,
                    expected: string,
                }
            ))
        );
        assert_eq!(observable_state(&context, file), poisoned);
        assert!(context.store().value_symbol_links(early).is_none());
        assert!(context.store().value_symbol_links(read_owner).is_none());
        assert!(context.store().symbol_node_links(read).is_none());
        assert!(context.store().type_node_links(read).is_none());
        assert!(!is_type_checked(&context, file));
        assert!(context.diagnostics().is_empty());

        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(later, ValueSymbolLinks::default())
        );
        assert!(context.store_mut_for_test().set_value_symbol_links(
            later,
            ValueSymbolLinks {
                write_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned = observable_state(&context, file);
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Variable(
                VariableInvariant::InvalidValueLinks(later)
            ))
        );
        assert_eq!(observable_state(&context, file), poisoned);
        assert!(context.store().value_symbol_links(early).is_none());
        assert!(context.store().value_symbol_links(read_owner).is_none());
        assert!(context.store().symbol_node_links(read).is_none());
        assert!(context.store().type_node_links(read).is_none());
        assert!(!is_type_checked(&context, file));
        assert!(context.diagnostics().is_empty());

        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(later, ValueSymbolLinks::default())
        );
        context.check_source_file(file).unwrap();
        assert_eq!(
            context.store().value_symbol_links(early),
            Some(&ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            })
        );
        assert_eq!(
            context.store().value_symbol_links(later),
            Some(&ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            })
        );
        assert_eq!(
            context.store().value_symbol_links(read_owner),
            Some(&ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            })
        );
        assert_eq!(
            context.store().symbol_node_links(read),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(early),
            })
        );
        assert_eq!(
            context.store().type_node_links(read),
            Some(&TypeNodeLinks {
                resolved_type: Some(number),
                ..TypeNodeLinks::default()
            })
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = (
            observable_state(&context, file),
            context.store().value_symbol_links(early).cloned(),
            context.store().value_symbol_links(later).cloned(),
            context.store().value_symbol_links(read_owner).cloned(),
            context.store().symbol_node_links(read).cloned(),
            context.store().type_node_links(read).cloned(),
        );
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            (
                observable_state(&context, file),
                context.store().value_symbol_links(early).cloned(),
                context.store().value_symbol_links(later).cloned(),
                context.store().value_symbol_links(read_owner).cloned(),
                context.store().symbol_node_links(read).cloned(),
                context.store().type_node_links(read).cloned(),
            ),
            warm
        );
    }

    #[test]
    fn later_ambient_function_cache_poison_preflights_before_earlier_publication() {
        let source = parsed(concat!(
            "declare function early(value: number): number;\n",
            "const read = early(1);\n",
            "declare function later(value: string): string;\n",
        ));
        let file = FileId::new(2_104);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let early_declaration = function_declaration(&source, file, "early");
        let later_declaration = function_declaration(&source, file, "later");
        let early = function_symbol(&context, &source, file, "early");
        let later = function_symbol(&context, &source, file, "later");
        let read_owner = variable_symbol(&context, &source, file, "read");
        let call = variable_initializer(&source, file, "read");
        let callees = identifier_expressions(&source, file, "early");
        let [callee] = callees.as_slice() else {
            panic!("fixture must contain one ambient function read")
        };
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;

        assert!(context.store_mut_for_test().set_value_symbol_links(
            later,
            ValueSymbolLinks {
                write_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned = observable_state(&context, file);
        let expected =
            SourceCheckError::Function(SourceFunctionInvariant::Callable(later_declaration));
        for _ in 0..2 {
            assert_eq!(context.check_source_file(file), Err(expected));
            assert_eq!(observable_state(&context, file), poisoned);
            assert!(context.store().value_symbol_links(early).is_none());
            assert!(context.store().value_symbol_links(read_owner).is_none());
            assert!(context.store().signature_links(early_declaration).is_none());
            assert!(context.store().type_node_links(call).is_none());
            assert!(context.store().signature_links(call).is_none());
            assert!(context.store().symbol_node_links(*callee).is_none());
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }

        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(later, ValueSymbolLinks::default())
        );
        context.check_source_file(file).unwrap();
        let early_type = context
            .store()
            .source_callable_type_for_owner(early)
            .expect("the repaired ambient function must retain its callable type");
        let later_type = context
            .store()
            .source_callable_type_for_owner(later)
            .expect("the repaired later ambient function must retain its callable type");
        assert_ne!(early_type, later_type);
        assert_eq!(
            context
                .store()
                .value_symbol_links(early)
                .and_then(|links| links.resolved_type),
            Some(early_type)
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(later)
                .and_then(|links| links.resolved_type),
            Some(later_type)
        );
        assert!(context.store().signature_links(early_declaration).is_some());
        assert!(context.store().signature_links(later_declaration).is_some());
        assert!(context.store().type_node_links(call).is_some());
        assert!(context.store().signature_links(call).is_some());
        assert_eq!(
            context
                .store()
                .symbol_node_links(*callee)
                .and_then(|links| links.resolved_symbol),
            Some(early)
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
        assert_eq!(
            context.store().source_callable_type_for_owner(early),
            Some(early_type)
        );
        assert_eq!(
            context.store().source_callable_type_for_owner(later),
            Some(later_type)
        );
    }

    #[test]
    fn later_generic_ambient_cache_poison_preflights_before_earlier_publication() {
        let source = parsed(concat!(
            "declare function early<T>(value: T): T;\n",
            "const read = early(1);\n",
            "declare function later<T extends string>(value: T): T;\n",
        ));
        let file = FileId::new(2_105);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let early_declaration = function_declaration(&source, file, "early");
        let later_declaration = function_declaration(&source, file, "later");
        let early = function_symbol(&context, &source, file, "early");
        let later = function_symbol(&context, &source, file, "later");
        let read_owner = variable_symbol(&context, &source, file, "read");
        let call = variable_initializer(&source, file, "read");
        let callees = identifier_expressions(&source, file, "early");
        let [callee] = callees.as_slice() else {
            panic!("fixture must contain one generic ambient function read")
        };
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;

        assert!(context.store_mut_for_test().set_value_symbol_links(
            later,
            ValueSymbolLinks {
                write_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned = observable_state(&context, file);
        let expected =
            SourceCheckError::Function(SourceFunctionInvariant::Callable(later_declaration));
        for _ in 0..2 {
            assert_eq!(context.check_source_file(file), Err(expected));
            assert_eq!(observable_state(&context, file), poisoned);
            assert!(context.store().value_symbol_links(early).is_none());
            assert!(context.store().value_symbol_links(read_owner).is_none());
            assert!(context.store().signature_links(early_declaration).is_none());
            assert!(context.store().type_node_links(call).is_none());
            assert!(context.store().signature_links(call).is_none());
            assert!(context.store().symbol_node_links(*callee).is_none());
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }

        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(later, ValueSymbolLinks::default())
        );
        context.check_source_file(file).unwrap();
        let early_type = context
            .store()
            .source_callable_type_for_owner(early)
            .expect("the repaired generic ambient function must retain its callable type");
        let later_type = context
            .store()
            .source_callable_type_for_owner(later)
            .expect("the repaired later generic ambient function must retain its callable type");
        let early_signature = context
            .store()
            .signature_links(early_declaration)
            .and_then(|links| links.resolved_signature.signature())
            .expect("the generic ambient declaration must own its signature");
        let later_signature = context
            .store()
            .signature_links(later_declaration)
            .and_then(|links| links.resolved_signature.signature())
            .expect("the constrained generic ambient declaration must own its signature");
        assert_ne!(early_type, later_type);
        assert_eq!(
            context
                .store()
                .signature(early_signature)
                .map(|signature| signature.type_parameters().len()),
            Some(1)
        );
        assert_eq!(
            context
                .store()
                .signature(later_signature)
                .map(|signature| signature.type_parameters().len()),
            Some(1)
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(read_owner)
                .and_then(|links| links.resolved_type)
                .and_then(|type_| context.store().type_payload(type_))
                .map(TypeRecord::flags),
            Some(TypeFlags::NUMBER_LITERAL)
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(*callee)
                .and_then(|links| links.resolved_symbol),
            Some(early)
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
        assert_eq!(
            context.store().source_callable_type_for_owner(early),
            Some(early_type)
        );
        assert_eq!(
            context.store().source_callable_type_for_owner(later),
            Some(later_type)
        );
    }

    #[test]
    fn simple_test_multi_file_issues_exact_ts2322_diagnostics_at_identifiers() {
        let first = parsed(r#"const first: number = "wrong";"#);
        let second = parsed("const second: string = 1;");
        let first_file = FileId::new(41);
        let second_file = FileId::new(7);
        let mut context = context(
            &[(first_file, &first), (second_file, &second)],
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(first_file).unwrap();
        context.check_source_file(second_file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(
            diagnostics[0].node,
            Some(variable_name(&first, first_file, "first"))
        );
        assert_eq!(diagnostics[0].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'."
        );
        assert_eq!(
            diagnostics[1].node,
            Some(variable_name(&second, second_file, "second"))
        );
        assert_eq!(diagnostics[1].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics[1].diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert!(is_type_checked(&context, first_file));
        assert!(is_type_checked(&context, second_file));
    }

    #[test]
    fn simple_assignments_contextually_type_rhs_and_match_contextual_typing_16_17() {
        let accepted = parsed("var foo: {id:number;} = {id:4}; foo = {id:5};");
        let accepted_file = FileId::new(109);
        let options = CanonicalCheckerOptions {
            no_error_truncation: true,
            ..CanonicalCheckerOptions::default()
        };
        let mut accepted_context = context(&[(accepted_file, &accepted)], options);
        let (_, accepted_rhs) = assignment_parts(&accepted, accepted_file, 0);

        accepted_context.check_source_file(accepted_file).unwrap();

        let number = accepted_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        assert_eq!(
            object_property_type(&accepted_context, accepted_rhs, "id"),
            number
        );
        assert!(accepted_context.diagnostics().is_empty());
        assert!(is_type_checked(&accepted_context, accepted_file));
        let warm = observable_state(&accepted_context, accepted_file);
        accepted_context.check_source_file(accepted_file).unwrap();
        assert_eq!(observable_state(&accepted_context, accepted_file), warm);

        let rejected = parsed(r#"var foo: {id:number;} = {id:4}; foo = {id: 5, name:"foo"};"#);
        let rejected_file = FileId::new(110);
        let mut rejected_context = context(&[(rejected_file, &rejected)], options);
        let (left, rejected_rhs) = assignment_parts(&rejected, rejected_file, 0);

        rejected_context.check_source_file(rejected_file).unwrap();

        let number = rejected_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        let string = rejected_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        assert_eq!(
            object_property_type(&rejected_context, rejected_rhs, "id"),
            number
        );
        assert_eq!(
            object_property_type(&rejected_context, rejected_rhs, "name"),
            string
        );
        let [diagnostic] = rejected_context.diagnostics().as_slice() else {
            panic!("expected the contextualTyping17 excess-property diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2353);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.diagnostic.arguments, ["name", "{ id: number; }"]);
        assert!(diagnostic.diagnostic.details.is_empty());
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Object literal may only specify known properties, and 'name' does not exist in type '{ id: number; }'."
        );
        let diagnostic_node = diagnostic.node.unwrap();
        assert_ne!(diagnostic_node, left);
        assert_eq!(diagnostic_node.arena, rejected.arena.id());
        assert_eq!(diagnostic_node.file, rejected_file);
        assert_property_name_span(&rejected, diagnostic_node, "name", true);
        let diagnostic_range = rejected.arena.get(diagnostic_node.node).unwrap().range;
        assert_eq!(diagnostic_range.start.get(), 46);
        assert_eq!(diagnostic_range.end.get(), 50);
        assert!(diagnostic.related_information.is_empty());
        assert!(is_type_checked(&rejected_context, rejected_file));
        let warm = observable_state(&rejected_context, rejected_file);
        rejected_context.check_source_file(rejected_file).unwrap();
        assert_eq!(observable_state(&rejected_context, rejected_file), warm);
    }

    #[test]
    fn simple_assignment_mismatch_is_anchored_at_left_identifier() {
        let source = parsed(r#"var target: number = 0; target = "wrong";"#);
        let file = FileId::new(112);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let (left, right) = assignment_parts(&source, file, 0);
        let expression = NodeRef::new(
            source.arena.id(),
            file,
            source.arena.get(left.node).unwrap().parent.unwrap(),
        );

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one assignment diagnostic")
        };
        assert_eq!(diagnostic.node, Some(left));
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(
            resolved_node_type(&context, left),
            context.store().intrinsic_bootstrap().unwrap().number_type,
        );
        assert_eq!(
            resolved_node_type(&context, expression),
            resolved_node_type(&context, right),
            "a simple assignment expression has the checked RHS type",
        );
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn assertion_context_and_deferred_comparison_match_contextual_typing_18() {
        let source = parsed("var foo: {id:number;} = <{id:number;}>({ }); foo = {id: 5};");
        let file = FileId::new(114);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let assertion = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeAssertionExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let NodeData::TypeAssertion(assertion_data) =
            &source.arena.get(assertion.node).unwrap().data
        else {
            panic!("expected a type assertion")
        };
        let target_node = NodeRef::new(source.arena.id(), file, assertion_data.type_);
        let parenthesized = NodeRef::new(source.arena.id(), file, assertion_data.expression);
        let NodeData::ParenthesizedExpression(parenthesized_data) =
            &source.arena.get(parenthesized.node).unwrap().data
        else {
            panic!("expected a parenthesized assertion operand")
        };
        let operand = NodeRef::new(source.arena.id(), file, parenthesized_data.expression);

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        let store = context.store();
        let target_type = store
            .type_node_links(target_node)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let assertion_type = store
            .type_node_links(assertion)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let operand_type = store
            .type_node_links(operand)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(assertion_type, target_type);
        assert_ne!(operand_type, target_type);
        assert_eq!(
            store
                .type_node_links(parenthesized)
                .and_then(|links| links.resolved_type),
            Some(operand_type)
        );
        assert_eq!(
            store.assertion_links(assertion),
            Some(&AssertionLinks {
                expr_type: Some(operand_type),
            })
        );
        let source_ref = context.source_file(file).unwrap();
        assert_eq!(
            store
                .source_file_links(source_ref)
                .unwrap()
                .deferred_nodes
                .iter()
                .copied()
                .collect::<Vec<_>>(),
            [assertion]
        );
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn array_assertion_operands_widen_to_the_canonical_array_identity() {
        let library = parsed("interface Array<T> {}");
        let source = parsed("var x: number[] = ([1] as number[]);");
        let library_file = FileId::new(127);
        let file = FileId::new(128);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions::default(),
        );
        let assertion = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::AsExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let array = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrayLiteralExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
        let operand = resolved_node_type(&context, array);
        let target = resolved_node_type(&context, assertion);
        let operand_array = context
            .store()
            .canonical_array_reference(context.global_types(), operand)
            .unwrap()
            .unwrap();
        let target_array = context
            .store()
            .canonical_array_reference(context.global_types(), target)
            .unwrap()
            .unwrap();
        assert!(operand_array.array_literal);
        assert!(!target_array.array_literal);
        assert_eq!(operand_array.base_type, target);
        assert_eq!(operand_array.element_type, target_array.element_type);
        assert_eq!(context.type_to_string(operand).unwrap(), "number[]");
        assert_eq!(context.type_to_string(target).unwrap(), "number[]");
        assert_eq!(
            context.store().assertion_links(assertion),
            Some(&AssertionLinks {
                expr_type: Some(operand),
            })
        );

        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn nonoverlapping_array_assertions_issue_exact_ts2352_cold_and_warm() {
        let library = parsed("interface Array<T> {}");
        let source = parsed("var x: string[] = ([1] as string[]);");
        let library_file = FileId::new(129);
        let file = FileId::new(130);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions::default(),
        );
        let assertion = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::AsExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one array assertion diagnostic")
        };
        assert_eq!(diagnostic.node, Some(assertion));
        assert_eq!(diagnostic.diagnostic.code(), 2352);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.diagnostic.arguments, ["number[]", "string[]"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Conversion of type 'number[]' to type 'string[]' may be a mistake because neither type sufficiently overlaps with the other. If this was intentional, convert the expression to 'unknown' first."
        );
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(node_text(&source, assertion), "[1] as string[]");
        let range = source.arena.get(assertion.node).unwrap().range;
        assert_eq!(range.start.get(), 19);
        assert_eq!(range.end.get(), 34);
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn contextual_array_literals_match_contextual_typing_19_through_21() {
        let library = parsed("interface Array<T> {}");
        let library_file = FileId::new(118);
        let cases = [
            (
                FileId::new(119),
                "// @target: es2015\nvar foo:{id:number;}[] = [{id:1}]; foo = [{id:1}, {id:2}];",
                "{ id: number; }[]",
                None,
            ),
            (
                FileId::new(120),
                "// @target: es2015\nvar foo:{id:number;}[] = [{id:1}]; foo = [{id:1}, {id:2, name:\"foo\"}];",
                "({ id: number; } | { id: number; name: string; })[]",
                Some((2353, 76, 80, "name")),
            ),
            (
                FileId::new(121),
                "// @target: es2015\nvar foo:{id:number;}[] = [{id:1}]; foo = [{id:1}, 1];",
                "(number | { id: number; })[]",
                Some((2322, 69, 70, "1")),
            ),
        ];

        for (file, text, expected_rhs, expected_diagnostic) in cases {
            let source = parsed(text);
            let mut context = context(
                &[(library_file, &library), (file, &source)],
                CanonicalCheckerOptions::default(),
            );
            let initial = variable_initializer(&source, file, "foo");
            let (left, right) = assignment_parts(&source, file, 0);
            let assignment = NodeRef::new(
                source.arena.id(),
                file,
                source.arena.get(right.node).unwrap().parent.unwrap(),
            );

            context.check_source_file(file).unwrap();

            assert_eq!(
                context
                    .type_to_string(resolved_node_type(&context, initial))
                    .unwrap(),
                "{ id: number; }[]",
            );
            assert_eq!(
                context
                    .type_to_string(resolved_node_type(&context, right))
                    .unwrap(),
                expected_rhs,
            );
            assert_eq!(
                resolved_node_type(&context, assignment),
                resolved_node_type(&context, right),
            );
            assert_eq!(
                resolved_node_type(&context, left),
                context
                    .get_type_from_type_node(variable_type_node(&source, file, "foo"))
                    .unwrap(),
            );

            let initial_elements = array_elements(&source, file, initial);
            let assignment_elements = array_elements(&source, file, right);
            assert_eq!(initial_elements.len(), 1);
            assert_eq!(
                context
                    .type_to_string(resolved_node_type(&context, initial_elements[0]))
                    .unwrap(),
                "{ id: number; }",
            );
            assert_eq!(
                context
                    .type_to_string(resolved_node_type(&context, assignment_elements[0]))
                    .unwrap(),
                "{ id: number; }",
            );
            assert_eq!(
                object_property_type(&context, assignment_elements[0], "id"),
                context.store().intrinsic_bootstrap().unwrap().number_type,
            );
            let first_id = object_property_initializer(&source, file, assignment_elements[0], "id");
            assert_eq!(
                context
                    .type_to_string(resolved_node_type(&context, first_id))
                    .unwrap(),
                "1",
            );
            match source.arena.get(assignment_elements[1].node).unwrap().kind {
                SyntaxKind::ObjectLiteralExpression => {
                    assert_eq!(
                        object_property_type(&context, assignment_elements[1], "id"),
                        context.store().intrinsic_bootstrap().unwrap().number_type,
                    );
                    let id =
                        object_property_initializer(&source, file, assignment_elements[1], "id");
                    assert_eq!(
                        context
                            .type_to_string(resolved_node_type(&context, id))
                            .unwrap(),
                        "2",
                    );
                    if node_text(&source, assignment_elements[1]).contains("name") {
                        assert_eq!(
                            object_property_type(&context, assignment_elements[1], "name"),
                            context.store().intrinsic_bootstrap().unwrap().string_type,
                        );
                        let name = object_property_initializer(
                            &source,
                            file,
                            assignment_elements[1],
                            "name",
                        );
                        assert_eq!(
                            context
                                .type_to_string(resolved_node_type(&context, name))
                                .unwrap(),
                            "\"foo\"",
                        );
                    }
                }
                SyntaxKind::NumericLiteral => assert_eq!(
                    context
                        .type_to_string(resolved_node_type(&context, assignment_elements[1]))
                        .unwrap(),
                    "1",
                ),
                kind => panic!("unexpected contextual array element {kind:?}"),
            }

            match expected_diagnostic {
                None => assert!(context.diagnostics().is_empty()),
                Some((code, start, end, text)) => {
                    let [diagnostic] = context.diagnostics().as_slice() else {
                        panic!("expected one contextual array diagnostic")
                    };
                    assert_eq!(diagnostic.diagnostic.code(), code);
                    assert_eq!(node_text(&source, diagnostic.node.unwrap()), text);
                    let range = source
                        .arena
                        .get(diagnostic.node.unwrap().node)
                        .unwrap()
                        .range;
                    assert_eq!((range.start.get(), range.end.get()), (start, end));
                    match code {
                        2353 => {
                            assert_eq!(
                                diagnostic.diagnostic.arguments,
                                ["name", "{ id: number; }"],
                            );
                            assert_eq!(
                                diagnostic.diagnostic.render().unwrap(),
                                "Object literal may only specify known properties, and 'name' does not exist in type '{ id: number; }'.",
                            );
                        }
                        2322 => {
                            assert_eq!(
                                diagnostic.diagnostic.arguments,
                                ["number", "{ id: number; }"],
                            );
                            assert_eq!(
                                diagnostic.diagnostic.render().unwrap(),
                                "Type 'number' is not assignable to type '{ id: number; }'.",
                            );
                        }
                        _ => unreachable!(),
                    }
                    assert!(diagnostic.related_information.is_empty());
                }
            }
            assert!(is_type_checked(&context, file));
            let warm = observable_state(&context, file);
            context.check_source_file(file).unwrap();
            assert_eq!(observable_state(&context, file), warm);
        }
    }

    #[test]
    fn nested_array_properties_elaborate_at_the_incompatible_element() {
        let library = parsed("interface Array<T> {}");
        let library_file = FileId::new(127);
        for (index, text) in [
            r#"var value: { xs: number[] } = { xs: ["a"] };"#,
            r#"var value: { xs: number[] } = { xs: (["a"]) };"#,
        ]
        .into_iter()
        .enumerate()
        {
            let source = parsed(text);
            let file = FileId::new(128 + u32::try_from(index).unwrap());
            let mut context = context(
                &[(library_file, &library), (file, &source)],
                CanonicalCheckerOptions::default(),
            );
            let object = variable_initializer(&source, file, "value");
            let property_initializer = object_property_initializer(&source, file, object, "xs");
            let array = match &source.arena.get(property_initializer.node).unwrap().data {
                NodeData::ParenthesizedExpression(parenthesized) => {
                    NodeRef::new(source.arena.id(), file, parenthesized.expression)
                }
                NodeData::ArrayLiteralExpression(_) => property_initializer,
                _ => panic!("expected an array or parenthesized array"),
            };
            let elements = array_elements(&source, file, array);
            let [element] = elements.as_slice() else {
                panic!("expected one nested array element")
            };
            let element = *element;

            context.check_source_file(file).unwrap();

            assert_eq!(
                context
                    .type_to_string(resolved_node_type(&context, array))
                    .unwrap(),
                "string[]",
            );
            assert_eq!(
                context
                    .type_to_string(object_property_type(&context, object, "xs"))
                    .unwrap(),
                "string[]",
            );
            assert_eq!(
                context
                    .type_to_string(resolved_node_type(&context, element))
                    .unwrap(),
                "\"a\"",
                "the element link retains its raw fresh literal identity",
            );

            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("expected one nested array diagnostic")
            };
            assert_eq!(diagnostic.node, Some(element));
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'string' is not assignable to type 'number'.",
            );
            assert!(diagnostic.related_information.is_empty());
            let range = source.arena.get(element.node).unwrap().range;
            let start = u32::try_from(text.find("\"a\"").unwrap()).unwrap();
            assert_eq!((range.start.get(), range.end.get()), (start, start + 3));
            assert!(is_type_checked(&context, file));

            let warm = observable_state(&context, file);
            context.check_source_file(file).unwrap();
            assert_eq!(observable_state(&context, file), warm);
        }
    }

    #[test]
    fn malformed_checked_expression_shapes_fail_atomically_before_elaboration() {
        let source = parsed("var value: number[] = [1];");
        let file = FileId::new(130);
        let array_context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let array = variable_initializer(&source, file, "value");
        let planned = PlannedExpression::new(array, PlannedExpressionKind::Array(Vec::new()));
        let number = array_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        let checked_element = CheckedExpressionTypes::leaf(number, number);
        let mismatched_length = CheckedExpressionTypes {
            raw: number,
            result: number,
            shape: CheckedExpressionShape::Array(vec![checked_element]),
            primitive_binary_recovery: None,
        };
        let mismatched_kind = CheckedExpressionTypes::leaf(number, number);
        let before = observable_state(&array_context, file);

        for checked in [&mismatched_length, &mismatched_kind] {
            assert!(matches!(
                super::super::array_diagnostics::checked_array_elements(&planned, checked),
                Err(SourceCheckError::RelationUnavailable(
                    RelationUnavailable::MalformedStructuredType(actual),
                )) if actual == number
            ));
        }

        assert_eq!(observable_state(&array_context, file), before);
        assert!(array_context.diagnostics().is_empty());

        let nested_source = parsed(
            "var value: { ok: number; nested: { value: number } } = \
             { ok: 1, nested: { value: 2 } };",
        );
        let nested_file = FileId::new(131);
        let mut nested_context = context(
            &[(nested_file, &nested_source)],
            CanonicalCheckerOptions::default(),
        );
        let nested_plan = {
            let (arena, bound) = nested_context.file(nested_file).unwrap();
            let source = nested_context.source_file(nested_file).unwrap();
            let host = DeclaredTypeHost::new([(arena, bound)]).unwrap();
            let plan =
                SourcePlanner::new_semantic(arena, bound, source, nested_context.store(), &host)
                    .finish()
                    .unwrap();
            let [PlannedStatement::Variables(variables)] = plan.statements.as_slice() else {
                panic!("expected one variable statement")
            };
            let [variable] = variables.as_slice() else {
                panic!("expected one variable")
            };
            let PlannedVariableInitializer::Expression(initializer) = &variable.initializer else {
                panic!("the fixture retains an initializer expression")
            };
            initializer.clone()
        };
        let number = nested_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        let checked = CheckedExpressionTypes {
            raw: number,
            result: number,
            shape: CheckedExpressionShape::Object(vec![
                CheckedExpressionTypes::leaf(number, number),
                CheckedExpressionTypes::leaf(number, number),
            ]),
            primitive_binary_recovery: None,
        };
        let globals = nested_context.global_types().clone();
        let options = nested_context.options();
        let host = DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();
        let before = observable_state(&nested_context, nested_file);

        let result = super::super::object_diagnostics::diagnostics_for_failed_assignment(
            nested_context.store_mut_for_test(),
            &host,
            &globals,
            &nested_plan,
            &checked,
            number,
            nested_plan.node,
            options,
            &mut InstantiationSession::new(
                crate::semantic::instantiate::InstantiationLimits::default(),
            ),
        );

        assert!(matches!(
            result,
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::InvalidStructuredMembers(actual),
            )) if actual == number
        ));
        assert_eq!(observable_state(&nested_context, nested_file), before);
        assert!(nested_context.diagnostics().is_empty());
    }

    #[test]
    fn spread_and_omitted_array_elements_remain_atomic_typed_boundaries() {
        let library = parsed("interface Array<T> {}");
        let library_file = FileId::new(122);
        for (index, text) in [
            "var value: number[] = [...[1]];",
            "var value: number[] = [, 1];",
        ]
        .into_iter()
        .enumerate()
        {
            let source = parsed(text);
            let file = FileId::new(123 + u32::try_from(index).unwrap());
            let mut context = context(
                &[(library_file, &library), (file, &source)],
                CanonicalCheckerOptions::default(),
            );
            let before = observable_state(&context, file);

            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Syntax {
                        role: SourceSyntaxRole::ArrayElement,
                        ..
                    }
                ))
            ));
            assert_eq!(observable_state(&context, file), before);
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn strict_empty_array_literals_use_the_distinct_implicit_never_element() {
        let library = parsed("interface Array<T> {}");
        let source = parsed("var values: number[] = [];");
        let library_file = FileId::new(125);
        let file = FileId::new(126);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );
        let initializer = variable_initializer(&source, file, "values");

        context.check_source_file(file).unwrap();

        let implicit_never = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .implicit_never_type;
        let source_type = resolved_node_type(&context, initializer);
        assert_eq!(
            context
                .store()
                .canonical_array_element_type(context.global_types(), source_type),
            Ok(Some(implicit_never)),
        );
        assert_eq!(context.type_to_string(source_type).unwrap(), "never[]");
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn nested_array_literals_check_in_direct_and_object_property_positions() {
        let library = parsed("interface Array<T> {}");
        let source = parsed(
            "var direct: number[][] = [[1]];\
             var wrapped: { values: number[][] } = { values: [[2]] };\
             var inferred: any = [{ values: [[3]] }];",
        );
        let library_file = FileId::new(127);
        let file = FileId::new(128);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(file).unwrap();

        let direct = variable_initializer(&source, file, "direct");
        let direct_inner = array_elements(&source, file, direct)[0];
        assert_eq!(
            context
                .type_to_string(resolved_node_type(&context, direct))
                .unwrap(),
            "number[][]",
        );
        assert_eq!(
            context
                .type_to_string(resolved_node_type(&context, direct_inner))
                .unwrap(),
            "number[]",
        );

        let wrapped = variable_initializer(&source, file, "wrapped");
        let wrapped_values = object_property_initializer(&source, file, wrapped, "values");
        assert_eq!(
            context
                .type_to_string(resolved_node_type(&context, wrapped_values))
                .unwrap(),
            "number[][]",
        );
        assert_eq!(
            context
                .type_to_string(object_property_type(&context, wrapped, "values"))
                .unwrap(),
            "number[][]",
        );

        let inferred = variable_initializer(&source, file, "inferred");
        let inferred_object = array_elements(&source, file, inferred)[0];
        let inferred_values = object_property_initializer(&source, file, inferred_object, "values");
        assert_eq!(
            context
                .type_to_string(resolved_node_type(&context, inferred))
                .unwrap(),
            "{ values: number[][]; }[]",
        );
        assert_eq!(
            context
                .type_to_string(resolved_node_type(&context, inferred_values))
                .unwrap(),
            "number[][]",
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn strict_and_loose_nullish_array_literals_keep_canonical_identities() {
        let library = parsed("interface Array<T> {}");
        let source = parsed("var nulls: any = [null]; var undefineds: any = [undefined];");
        let library_file = FileId::new(129);
        for (index, strict_null_checks) in [false, true].into_iter().enumerate() {
            let file = FileId::new(130 + u32::try_from(index).unwrap());
            let mut context = context(
                &[(library_file, &library), (file, &source)],
                CanonicalCheckerOptions {
                    intrinsic: IntrinsicBootstrapOptions {
                        strict_null_checks,
                        exact_optional_property_types: false,
                    },
                    ..CanonicalCheckerOptions::default()
                },
            );

            context.check_source_file(file).unwrap();

            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let null_widening = bootstrap.null_widening_type;
            let undefined_widening = bootstrap.undefined_widening_type;
            let nulls = resolved_node_type(&context, variable_initializer(&source, file, "nulls"));
            let undefineds =
                resolved_node_type(&context, variable_initializer(&source, file, "undefineds"));
            assert_eq!(
                context
                    .store()
                    .canonical_array_element_type(context.global_types(), nulls),
                Ok(Some(null_widening)),
            );
            assert_eq!(
                context
                    .store()
                    .canonical_array_element_type(context.global_types(), undefineds),
                Ok(Some(undefined_widening)),
            );
            assert_eq!(context.type_to_string(nulls).unwrap(), "null[]");
            assert_eq!(context.type_to_string(undefineds).unwrap(), "undefined[]");
            assert!(context.diagnostics().is_empty());
            assert!(is_type_checked(&context, file));

            let warm = observable_state(&context, file);
            context.check_source_file(file).unwrap();
            assert_eq!(observable_state(&context, file), warm);
        }
    }

    // Pinned tsgo 7.0-dev oracle matrix under `--noLib`: an empty `Array<T>`
    // shell makes both `[[1], {}]` orders `number[][]`; adding required
    // `length` makes both orders `{}[]`; a matching `{ length: number }`
    // remains `number[][]`. This slice implements only the required-surface
    // empty-object reduction and keeps the other mixed cases unavailable.
    #[test]
    fn unproven_array_shells_mixed_with_empty_objects_stay_typed_unavailable() {
        for (library_text, source_text) in [
            ("interface Array<T> {}", "var mixed: any = [[1], {}];"),
            ("interface Array<T> {}", "var mixed: any = [{}, [1]];"),
            (
                "interface Array<T> { length?: number }",
                "var mixed: any = [[1], {}];",
            ),
            (
                "interface Array<T> { length?: number }",
                "var mixed: any = [{}, [1]];",
            ),
            (
                "interface Array<T> { push(value: T): number }",
                "var mixed: any = [[1], {}];",
            ),
            (
                "interface Array<T> { push(value: T): number }",
                "var mixed: any = [{}, [1]];",
            ),
        ] {
            let library = parsed(library_text);
            let source = parsed(source_text);
            let library_file = FileId::new(132);
            let file = FileId::new(133);
            let mut context = context(
                &[(library_file, &library), (file, &source)],
                CanonicalCheckerOptions::default(),
            );

            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::UnsupportedUnionConstituent(_)
                )),
            ));
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn required_array_property_reduces_empty_objects_in_both_orders() {
        let library = parsed("interface Array<T> { length: number }");
        let source = parsed("var arrayFirst: any = [[1], {}]; var objectFirst: any = [{}, [1]];");
        let library_file = FileId::new(134);
        let file = FileId::new(135);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(file).unwrap();
        for name in ["arrayFirst", "objectFirst"] {
            let type_ = resolved_node_type(&context, variable_initializer(&source, file, name));
            assert_eq!(context.type_to_string(type_).unwrap(), "{}[]");
        }
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn mixed_array_empty_union_preflight_preserves_typed_poison_and_retry() {
        let library = parsed("interface Array<T> { length: number }");
        let source = parsed("var arrayValue: any = [1]; var emptyValue: any = {};");
        let library_file = FileId::new(136);
        let file = FileId::new(137);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions::default(),
        );
        context.check_source_file(file).unwrap();

        let array = resolved_node_type(&context, variable_initializer(&source, file, "arrayValue"));
        let empty = resolved_node_type(&context, variable_initializer(&source, file, "emptyValue"));
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let global_types = context.global_types().clone();
        assert_eq!(
            context
                .store_mut_for_test()
                .expression_union_type_with_global_types(
                    &global_types,
                    &[array, empty],
                    UnionReduction::Subtype,
                )
                .unwrap(),
            empty
        );

        assert!(context.store_mut_for_test().set_type_reference_resolution(
            array,
            None,
            Some(vec![empty])
        ));
        let poisoned = observable_state(&context, file);
        assert_eq!(
            context
                .store_mut_for_test()
                .expression_union_type_with_global_types(
                    &global_types,
                    &[array, empty],
                    UnionReduction::Subtype,
                ),
            Err(LiteralTypeCacheError::ArrayType {
                type_: array,
                error: ArrayTypeError::InvalidReference(array),
            })
        );
        assert_eq!(observable_state(&context, file), poisoned);

        assert!(context.store_mut_for_test().set_type_reference_resolution(
            array,
            None,
            Some(vec![number])
        ));
        assert_eq!(
            context
                .store_mut_for_test()
                .expression_union_type_with_global_types(
                    &global_types,
                    &[empty, array],
                    UnionReduction::Subtype,
                )
                .unwrap(),
            empty
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn nonempty_array_property_relations_stay_typed_unavailable() {
        for (library_text, source_text) in [
            (
                "interface Array<T> {}",
                "var mixed: any = [[1], { id: 1 }];",
            ),
            (
                "interface Array<T> { length: number }",
                "var mixed: any = [[1], { length: 1 }];",
            ),
        ] {
            let library = parsed(library_text);
            let source = parsed(source_text);
            let library_file = FileId::new(138);
            let file = FileId::new(139);
            let mut context = context(
                &[(library_file, &library), (file, &source)],
                CanonicalCheckerOptions::default(),
            );

            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::UnsupportedUnionConstituent(_)
                )),
            ));
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn global_type_queries_rescan_shared_array_union_cache_with_capability() {
        let library = parsed("interface Array<T> {}");
        let expression = parsed("var nested: any = [[1], \"text\"];");
        let query = parsed("var target: string | number = 1;");
        let library_file = FileId::new(140);
        let expression_file = FileId::new(141);
        let query_file = FileId::new(142);
        let mut context = context(
            &[
                (library_file, &library),
                (expression_file, &expression),
                (query_file, &query),
            ],
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(expression_file).unwrap();
        let nested = resolved_node_type(
            &context,
            variable_initializer(&expression, expression_file, "nested"),
        );
        assert!(context.type_to_string(nested).unwrap().contains("number[]"));

        let scans = context.store().union_cache_validation_scan_count();
        context
            .store_mut_for_test()
            .mark_union_cache_validation_dirty();
        let target = context
            .get_type_from_type_node(variable_type_node(&query, query_file, "target"))
            .unwrap();

        assert_eq!(context.type_to_string(target).unwrap(), "string | number");
        assert_eq!(
            context.store().union_cache_validation_scan_count(),
            scans + 1,
            "the global-aware production query validates the shared cache once",
        );
        assert!(!context.store().union_cache_needs_validation);
    }

    #[test]
    fn global_type_queries_construct_array_union_aliases_cold_and_warm() {
        let library = parsed("interface Array<T> {}");
        let source = parsed("type U = number[] | string;");
        let library_file = FileId::new(137);
        let file = FileId::new(138);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions::default(),
        );
        let body = type_alias_body(&source, file, "U");

        let union = context.get_type_from_type_node(body).unwrap();

        assert_eq!(context.type_to_string(union).unwrap(), "U");
        let TypeData::Union(data) = context.store().type_payload(union).unwrap().data() else {
            panic!("array union alias must resolve to a canonical union")
        };
        assert_eq!(data.union.types.len(), 2);
        assert!(data.union.types.iter().any(|constituent| {
            context
                .store()
                .canonical_array_reference(context.global_types(), *constituent)
                .is_ok_and(|reference| reference.is_some())
        }));

        let warm = observable_state(&context, file);
        assert_eq!(context.get_type_from_type_node(body), Ok(union));
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn declared_property_objects_are_array_union_elements_cold_warm_and_recursive() {
        let library = parsed("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parsed(concat!(
            "interface Foo { value: string } ",
            "type Shape = { value: number }; ",
            "interface Node { next?: Node; payload: Shape } ",
            "type FooMaybe = Foo[] | null; ",
            "type ShapeMaybe = Shape[] | null; ",
            "type InlineMaybe = ({ enabled: boolean })[] | null; ",
            "type EmptyMaybe = {}[] | null; ",
            "type NodeMaybe = Node[] | null; ",
            "type DirectFooMaybe = Array<Foo> | null; ",
            "type ReadonlyShapeMaybe = ReadonlyArray<Shape> | null; ",
            "let foo: FooMaybe = null; ",
            "let shape: ShapeMaybe = null; ",
            "let inline: InlineMaybe = null; ",
            "let empty: EmptyMaybe = null; ",
            "let node: NodeMaybe = null; ",
            "let directFoo: DirectFooMaybe = null; ",
            "let readonlyShape: ReadonlyShapeMaybe = null;",
        ));
        let library_file = FileId::new(143);
        let file = FileId::new(144);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );

        context.check_source_file(file).unwrap();

        let mut unions = Vec::new();
        let mut node_element = None;
        for (alias, expected_proof) in [
            ("FooMaybe", DeclaredPropertyObjectProof::Interface),
            ("ShapeMaybe", DeclaredPropertyObjectProof::TypeLiteral),
            ("InlineMaybe", DeclaredPropertyObjectProof::TypeLiteral),
            ("EmptyMaybe", DeclaredPropertyObjectProof::TypeLiteral),
            ("NodeMaybe", DeclaredPropertyObjectProof::Interface),
            ("DirectFooMaybe", DeclaredPropertyObjectProof::Interface),
            (
                "ReadonlyShapeMaybe",
                DeclaredPropertyObjectProof::TypeLiteral,
            ),
        ] {
            let body = type_alias_body(&source, file, alias);
            let union = context.get_type_from_type_node(body).unwrap();
            let (_, element) = array_element_in_union(&context, union);
            assert_eq!(
                validate_resolved_declared_property_object(context.store(), element),
                DeclaredPropertyObjectValidation::Valid(expected_proof),
            );
            unions.push((body, union));
            if alias == "NodeMaybe" {
                node_element = Some(element);
            }
        }
        let node = node_element.unwrap();
        let next = declared_object_property_symbol(&context, node, "next");
        assert_eq!(
            context
                .store()
                .value_symbol_links(next)
                .and_then(|links| links.resolved_type),
            Some(node),
            "recursive declared properties remain opaque store-owned identities",
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        for (body, union) in unions {
            assert_eq!(context.get_type_from_type_node(body), Ok(union));
        }
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn declared_array_union_cache_poison_rescans_atomically_and_retries() {
        #[derive(Clone, Copy, Debug)]
        enum Poison {
            Shell,
            OwnerMembers,
            PropertyOrder,
            AliasOwner,
            PropertyLinks,
        }

        let library = parsed("interface Array<T> {}");
        let source = parsed(concat!(
            "type Item = { first: string; second: number }; ",
            "type Items = Item[] | null; ",
            "type Probe = string | number;",
        ));
        let library_file = FileId::new(145);
        let file = FileId::new(146);
        for poison in [
            Poison::Shell,
            Poison::OwnerMembers,
            Poison::PropertyOrder,
            Poison::AliasOwner,
            Poison::PropertyLinks,
        ] {
            let mut context = context(
                &[(library_file, &library), (file, &source)],
                CanonicalCheckerOptions {
                    intrinsic: IntrinsicBootstrapOptions {
                        strict_null_checks: true,
                        exact_optional_property_types: false,
                    },
                    ..CanonicalCheckerOptions::default()
                },
            );
            let items_body = type_alias_body(&source, file, "Items");
            let items = context.get_type_from_type_node(items_body).unwrap();
            let (_, item) = array_element_in_union(&context, items);
            assert_eq!(
                validate_resolved_declared_property_object(context.store(), item),
                DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::TypeLiteral,),
            );
            let (flags, owner, alias_symbol, members, properties, property, property_links) = {
                let record = context.store().type_payload(item).unwrap();
                let structured = record.data().structured().unwrap();
                let owner = record.symbol().unwrap();
                let alias_symbol = record
                    .alias()
                    .and_then(|alias| context.store().type_alias(alias))
                    .and_then(super::super::type_records::TypeAlias::symbol)
                    .unwrap();
                let properties = structured.properties.clone().unwrap();
                let property = properties[0];
                (
                    record.object_flags(),
                    owner,
                    alias_symbol,
                    structured.members,
                    properties,
                    property,
                    context
                        .store()
                        .value_symbol_links(property)
                        .cloned()
                        .unwrap(),
                )
            };
            match poison {
                Poison::Shell => assert!(
                    context
                        .store_mut_for_test()
                        .set_type_object_flags(item, ObjectFlags::ANONYMOUS)
                ),
                Poison::OwnerMembers => assert!(
                    context
                        .store_mut_for_test()
                        .set_symbol_relationships(owner, None, None, None, None)
                ),
                Poison::PropertyOrder => {
                    let mut reversed = properties.clone();
                    reversed.reverse();
                    assert!(context.store_mut_for_test().set_structured_type_members(
                        item,
                        members,
                        Some(reversed),
                        None,
                        None,
                        None,
                    ));
                }
                Poison::AliasOwner => {
                    assert!(context.store_mut_for_test().set_symbol_relationships(
                        alias_symbol,
                        None,
                        None,
                        Some(owner),
                        None
                    ));
                }
                Poison::PropertyLinks => {
                    let mut links = property_links.clone();
                    links.write_type =
                        Some(context.store().intrinsic_bootstrap().unwrap().string_type);
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_value_symbol_links(property, links)
                    );
                }
            }
            context
                .store_mut_for_test()
                .mark_union_cache_validation_dirty();
            let scans = context.store().union_cache_validation_scan_count();
            let poisoned_state = observable_state(&context, file);
            let probe_body = type_alias_body(&source, file, "Probe");

            assert!(
                matches!(
                    context.get_type_from_type_node(probe_body),
                    Err(DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::InvalidCachedUnionType(type_)
                    )) if type_ == item
                ),
                "poison: {poison:?}"
            );
            assert_eq!(
                context.store().union_cache_validation_scan_count(),
                scans + 1,
                "poison: {poison:?}",
            );
            assert_eq!(
                observable_state(&context, file),
                poisoned_state,
                "poison: {poison:?}",
            );

            match poison {
                Poison::Shell => {
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_type_object_flags(item, flags)
                    );
                }
                Poison::OwnerMembers => {
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_symbol_relationships(owner, members, None, None, None,)
                    );
                }
                Poison::PropertyOrder => {
                    assert!(context.store_mut_for_test().set_structured_type_members(
                        item,
                        members,
                        Some(properties.clone()),
                        None,
                        None,
                        None,
                    ));
                }
                Poison::AliasOwner => {
                    assert!(context.store_mut_for_test().set_symbol_relationships(
                        alias_symbol,
                        None,
                        None,
                        None,
                        None,
                    ));
                }
                Poison::PropertyLinks => {
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_value_symbol_links(property, property_links)
                    );
                }
            }
            let probe = context.get_type_from_type_node(probe_body).unwrap();
            assert_eq!(context.type_to_string(probe).unwrap(), "Probe");
            assert_eq!(context.get_type_from_type_node(items_body), Ok(items));
            assert_eq!(
                validate_resolved_declared_property_object(context.store(), item),
                DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::TypeLiteral,),
            );
            assert_eq!(
                context.store().union_cache_validation_scan_count(),
                scans + 2,
                "poison: {poison:?}",
            );
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn declared_recursive_interface_array_union_cache_poison_is_invariant_and_retryable() {
        let library = parsed("interface Array<T> {}");
        let source = parsed(concat!(
            "interface Node { next?: Node } ",
            "type Nodes = Node[] | null; ",
            "type Probe = string | number;",
        ));
        let library_file = FileId::new(147);
        let file = FileId::new(148);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );
        let nodes_body = type_alias_body(&source, file, "Nodes");
        let nodes = context.get_type_from_type_node(nodes_body).unwrap();
        let (_, node) = array_element_in_union(&context, nodes);
        let next = declared_object_property_symbol(&context, node, "next");
        let links = context.store().value_symbol_links(next).cloned().unwrap();
        let mut poisoned_links = links.clone();
        poisoned_links.write_type =
            Some(context.store().intrinsic_bootstrap().unwrap().string_type);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(next, poisoned_links)
        );
        context
            .store_mut_for_test()
            .mark_union_cache_validation_dirty();
        let scans = context.store().union_cache_validation_scan_count();
        let poisoned_state = observable_state(&context, file);
        let probe_body = type_alias_body(&source, file, "Probe");

        assert!(matches!(
            context.get_type_from_type_node(probe_body),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedUnionType(type_)
            )) if type_ == node
        ));
        assert_eq!(
            context.store().union_cache_validation_scan_count(),
            scans + 1,
        );
        assert_eq!(observable_state(&context, file), poisoned_state);

        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(next, links)
        );
        let probe = context.get_type_from_type_node(probe_body).unwrap();
        assert_eq!(context.type_to_string(probe).unwrap(), "Probe");
        assert_eq!(context.get_type_from_type_node(nodes_body), Ok(nodes));
        assert_eq!(
            validate_resolved_declared_property_object(context.store(), node),
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface),
        );
        assert_eq!(
            context.store().union_cache_validation_scan_count(),
            scans + 2,
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn declared_method_signatures_and_unpublished_generic_array_elements_remain_boundaries() {
        let library = parsed("interface Array<T> {}");
        let library_file = FileId::new(149);
        for (index, declaration) in [
            "interface Callable { run(): string }",
            "interface Callable { (): string }",
        ]
        .into_iter()
        .enumerate()
        {
            let source = parsed(declaration);
            let file = FileId::new(150 + u32::try_from(index).unwrap());
            let mut context = context(
                &[(library_file, &library), (file, &source)],
                CanonicalCheckerOptions::default(),
            );
            let callable = global_symbol(&context, "Callable");
            let global_types = context.global_types().clone();
            let callable_type = context
                .store_mut_for_test()
                .alloc_interface_type(ObjectFlags::INTERFACE, Some(callable))
                .unwrap();
            let array = context
                .store_mut_for_test()
                .create_canonical_array_type(&global_types, callable_type, false)
                .unwrap();

            assert_eq!(
                validate_resolved_declared_property_object(context.store(), callable_type),
                DeclaredPropertyObjectValidation::NotDeclared,
                "source: {declaration}",
            );
            assert_eq!(
                context
                    .store()
                    .validate_union_constituent_with_global_types(&global_types, array),
                Err(LiteralTypeCacheError::UnsupportedUnionConstituent(
                    callable_type,
                )),
                "source: {declaration}",
            );
        }

        let source = parsed(concat!(
            "interface Box<T> { value: T } ",
            "type Instantiated = Box<number>[] | null;",
        ));
        let file = FileId::new(152);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );
        let body = type_alias_body(&source, file, "Instantiated");
        let error = context.get_type_from_type_node(body).unwrap_err();
        assert!(matches!(
            error,
            DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituentType(_)
            )
        ));
        let retained = observable_state(&context, file);
        assert_eq!(context.get_type_from_type_node(body), Err(error));
        assert_eq!(observable_state(&context, file), retained);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn cached_array_aliases_remain_global_aware_union_constituents_in_every_query_order() {
        let library = parsed("interface Array<T> {}");
        let source = parsed(
            "type ArrayAlias = number[];\
             type Outer = ArrayAlias | string;\
             type ArrayUnion = number[] | string;\
             type NestedUnion = ArrayUnion | boolean;",
        );
        let library_file = FileId::new(141);
        let file = FileId::new(142);

        let mut cold = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions::default(),
        );
        let outer_body = type_alias_body(&source, file, "Outer");
        let outer = cold.get_type_from_type_node(outer_body).unwrap();
        assert_eq!(cold.type_to_string(outer).unwrap(), "Outer");
        let cold_warm = observable_state(&cold, file);
        assert_eq!(cold.get_type_from_type_node(outer_body), Ok(outer));
        assert_eq!(observable_state(&cold, file), cold_warm);

        let mut ordered = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions::default(),
        );
        let array_alias_body = type_alias_body(&source, file, "ArrayAlias");
        let array_alias = ordered.get_type_from_type_node(array_alias_body).unwrap();
        assert_eq!(ordered.type_to_string(array_alias).unwrap(), "number[]");
        let ordered_outer = ordered.get_type_from_type_node(outer_body).unwrap();
        assert_eq!(ordered.type_to_string(ordered_outer).unwrap(), "Outer");

        let array_union_body = type_alias_body(&source, file, "ArrayUnion");
        let nested_union_body = type_alias_body(&source, file, "NestedUnion");
        let array_union = ordered.get_type_from_type_node(array_union_body).unwrap();
        assert_eq!(ordered.type_to_string(array_union).unwrap(), "ArrayUnion");
        let nested_union = ordered.get_type_from_type_node(nested_union_body).unwrap();
        assert_eq!(ordered.type_to_string(nested_union).unwrap(), "NestedUnion",);

        let ordered_warm = observable_state(&ordered, file);
        assert_eq!(
            ordered.get_type_from_type_node(outer_body),
            Ok(ordered_outer),
        );
        assert_eq!(
            ordered.get_type_from_type_node(array_union_body),
            Ok(array_union),
        );
        assert_eq!(
            ordered.get_type_from_type_node(nested_union_body),
            Ok(nested_union),
        );
        assert_eq!(observable_state(&ordered, file), ordered_warm);
    }

    #[test]
    fn contextual_literal_unions_validate_sibling_arrays_with_global_capability() {
        let library = parsed("interface Array<T> {}");
        let source = parsed("var values: (1 | number[])[] = [1];");
        let library_file = FileId::new(139);
        let file = FileId::new(140);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions::default(),
        );
        let initializer = variable_initializer(&source, file, "values");

        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .type_to_string(resolved_node_type(&context, initializer))
                .unwrap(),
            "1[]",
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn asserted_types_do_not_contextually_type_object_operands() {
        let source = parsed("var value: {id: 1} = ({id: 1} as {id: 1});");
        let file = FileId::new(117);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let operand = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ObjectLiteralExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert_eq!(
            object_property_type(&context, operand, "id"),
            context.store().intrinsic_bootstrap().unwrap().number_type,
        );
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn nonoverlapping_assertions_issue_exact_ts2352_at_the_assertion() {
        let source = parsed(r#"var value: number = "x" as number;"#);
        let file = FileId::new(115);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let assertion = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::AsExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one assertion diagnostic")
        };
        assert_eq!(diagnostic.node, Some(assertion));
        assert_eq!(diagnostic.diagnostic.code(), 2352);
        assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Conversion of type 'string' to type 'number' may be a mistake because neither type sufficiently overlaps with the other. If this was intentional, convert the expression to 'unknown' first."
        );
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(node_text(&source, assertion), r#""x" as number"#);
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn const_assertions_remain_an_atomic_typed_boundary() {
        let source = parsed(r#"var value: "x" = "x" as const;"#);
        let file = FileId::new(116);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let before = observable_state(&context, file);

        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::ConstAssertion(_)
            ))
        ));
        assert_eq!(observable_state(&context, file), before);
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }

    #[test]
    fn initialized_mutable_let_assignments_preserve_annotated_and_inferred_types() {
        let source = parsed(concat!(
            "let annotated: number = 0; annotated = 1; ",
            "let inferred = 'ready'; inferred = 2;",
        ));
        let file = FileId::new(8_250);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one incompatible inferred let assignment")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        let warm = observable_state(&context, file);
        context.recheck_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn unsupported_assignment_target_rejects_the_source_plan_without_writes() {
        let source = parsed(concat!(
            "var earlier: number = 0; ",
            "const target: number = 0; target = 1;",
        ));
        let file = FileId::new(113);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let before = observable_state(&context, file);

        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Assignment(
                    AssignmentUnsupported::BlockScopedTarget { .. }
                )
            ))
        ));
        assert_eq!(observable_state(&context, file), before);
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }

    #[test]
    fn passing_primitives_parentheses_unary_literals_and_alias_target_check() {
        let source = parsed(concat!(
            "type Text = string; ",
            r#"const text: string = (("value")); "#,
            "const number: number = -1; ",
            "const bigint: bigint = (-2n); ",
            "const yes: boolean = true; const no: boolean = false; ",
            "const nothing: null = null; ",
            "const template: string = `value`; ",
            r#"const alias: Text = "value";"#,
        ));
        let file = FileId::new(42);
        let mut context = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn source_union_assignments_preserve_alias_display_and_nullable_order() {
        let source = parsed(concat!(
            "type Scalar = string | number; ",
            r#"const namedOk: Scalar = "ok"; "#,
            "const anonymousOk: string | number = 1; ",
            "const nullableOk: string | number | null = null; ",
            "const namedBad: Scalar = false; ",
            "const anonymousBad: string | number | null = false;",
        ));
        let file = FileId::new(55);
        let mut context = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(
            diagnostics[0].node,
            Some(variable_name(&source, file, "namedBad"))
        );
        assert_eq!(diagnostics[0].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Type 'boolean' is not assignable to type 'Scalar'."
        );
        assert_eq!(
            diagnostics[1].node,
            Some(variable_name(&source, file, "anonymousBad"))
        );
        assert_eq!(diagnostics[1].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics[1].diagnostic.render().unwrap(),
            "Type 'false' is not assignable to type 'string | number | null'."
        );
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn empty_export_marker_and_exported_ordinary_variables_check_idempotently() {
        let source = parsed(concat!(
            "export {}; ",
            r#"export const text: string = "ok"; "#,
            "export let count: number = 1; ",
            "export var enabled: boolean = true; ",
            r#"export const scalar: string | number = "ok";"#,
        ));
        let file = FileId::new(56);
        let mut context = context_with_module_state(
            &[(file, &source)],
            CanonicalModuleState::External,
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(file).unwrap();
        let after_first = observable_state(&context, file);

        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), after_first);
    }

    #[test]
    fn exported_variables_issue_ordered_ts2322_diagnostics_at_identifiers() {
        let source = parsed(concat!(
            "export {}; ",
            r#"export const first: number = "wrong", second: string = 1;"#,
        ));
        let file = FileId::new(57);
        let mut context = context_with_module_state(
            &[(file, &source)],
            CanonicalModuleState::External,
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(
            diagnostics[0].node,
            Some(variable_name(&source, file, "first"))
        );
        assert_eq!(diagnostics[0].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'."
        );
        assert_eq!(
            diagnostics[1].node,
            Some(variable_name(&source, file, "second"))
        );
        assert_eq!(diagnostics[1].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics[1].diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn exported_type_aliases_check_idempotently() {
        let source = parsed(concat!(
            "export type Label = string; ",
            "export type Model = { value: number }; ",
            r#"export const label: Label = "ok";"#,
        ));
        let file = FileId::new(5_600);
        let mut context = context_with_module_state(
            &[(file, &source)],
            CanonicalModuleState::External,
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(file).unwrap();
        let after_first = observable_state(&context, file);

        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), after_first);
    }

    #[test]
    fn export_near_misses_reject_the_whole_plan_without_writes() {
        let near_misses = [
            ("export { A };", SourceSyntaxRole::ExportClause),
            (
                r#"export {} from "./dependency";"#,
                SourceSyntaxRole::ExportDeclaration,
            ),
            ("export type {};", SourceSyntaxRole::ExportDeclaration),
            (
                r#"export declare const value: string = "ok";"#,
                SourceSyntaxRole::VariableInitializer,
            ),
            (
                "export default interface Model {}",
                SourceSyntaxRole::InterfaceDeclaration,
            ),
        ];

        for (index, (near_miss, expected_role)) in near_misses.into_iter().enumerate() {
            let source = parsed(&format!("type A = A; {near_miss}"));
            let file = FileId::new(58 + u32::try_from(index).unwrap());
            let mut context = context_with_module_state(
                &[(file, &source)],
                CanonicalModuleState::External,
                CanonicalCheckerOptions::default(),
            );
            let before = observable_state(&context, file);

            let result = context.check_source_file(file);
            assert!(
                matches!(
                    result,
                    Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Syntax { role, .. }
                    )) if role == expected_role
                ) || near_miss.contains(" from ")
                    && matches!(
                        result,
                        Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Import(_)
                        ))
                    ),
                "source: {near_miss}, actual: {result:?}"
            );
            assert_eq!(observable_state(&context, file), before);
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn export_forms_require_external_module_facts_before_any_writes() {
        let cases = [
            (
                "type A = A; export {};",
                SourceSyntaxRole::ExportDeclaration,
            ),
            (
                r#"type A = A; export const value: string = "ok";"#,
                SourceSyntaxRole::VariableModifier,
            ),
            (
                "type A = A; export type Alias = string;",
                SourceSyntaxRole::TypeAliasDeclaration,
            ),
        ];

        for (index, (text, expected_role)) in cases.into_iter().enumerate() {
            let source = parsed(text);
            let file = FileId::new(63 + u32::try_from(index).unwrap());
            let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
            let before = observable_state(&context, file);

            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::MissingExternalModuleFact { role, .. }
                )) if role == expected_role
            ));
            assert_eq!(observable_state(&context, file), before);
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn source_generic_aliases_substitute_nested_union_and_default_arguments() {
        let source = parsed(concat!(
            "type Id<T> = T; ",
            "type Wrap<T> = Id<T>; ",
            "type Value<T = number> = T; ",
            r#"const text: Wrap<string> = "ok"; "#,
            "const scalar: Wrap<string | number> = 1; ",
            "const defaulted: Value = 1; ",
            "const bad: Id<string> = 1;",
        ));
        let file = FileId::new(65);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(
            diagnostics[0].node,
            Some(variable_name(&source, file, "bad"))
        );
        assert_eq!(diagnostics[0].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert!(is_type_checked(&context, file));

        let state = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), state);
    }

    #[test]
    fn source_generic_alias_arity_errors_do_not_cascade_to_assignability() {
        let source = parsed(concat!(
            "type Id<T> = T; ",
            "type Optional<T = string, U = number> = U; ",
            "type Plain = string; ",
            "const missing: Id = 1; ",
            "const range: Optional<string, number, boolean> = true; ",
            "const plain: Plain<string> = 1;",
        ));
        let file = FileId::new(66);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2314, 2707, 2315]
        );
        assert!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() != 2322)
        );
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn simple_interfaces_and_nested_object_literals_check_and_reuse_warm_identity() {
        let source = parsed(concat!(
            "interface Leaf { value: string } ",
            "interface Model { count: number; nested: Leaf } ",
            "type Shape = { label: string; nested: { enabled: boolean } }; ",
            r#"const model: Model = { count: 1, nested: { value: "ok" } }; "#,
            r#"const leaf: Leaf = { value: "also ok" }; "#,
            r#"const shape: Shape = { label: "shape", nested: { enabled: true } };"#,
        ));
        let file = FileId::new(67);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn contextual_object_properties_preserve_literals_or_widen_primitives_by_kind() {
        let source = parsed(concat!(
            "interface Expected { ",
            r#"exactString: "x"; broadString: string; "#,
            "exactNumber: 1; broadNumber: number; ",
            "exactBigInt: 1n; broadBigInt: bigint; ",
            "exactBoolean: true; broadBoolean: boolean; ",
            "nullValue: null; undefinedValue: undefined; } ",
            r#"const contextual: Expected = { exactString: "x", broadString: "x", "#,
            "exactNumber: 1, broadNumber: 1, exactBigInt: 1n, broadBigInt: 1n, ",
            "exactBoolean: true, broadBoolean: true, nullValue: null, ",
            "undefinedValue: undefined }; ",
            r#"const uncontextual: any = { stringValue: "x", numberValue: 1, "#,
            "bigintValue: 1n, booleanValue: true, nullValue: null, ",
            "undefinedValue: undefined };",
        ));
        let file = FileId::new(89);
        let mut context = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );
        let contextual = variable_initializer(&source, file, "contextual");
        let uncontextual = variable_initializer(&source, file, "uncontextual");
        let exact_string = object_property_initializer(&source, file, contextual, "exactString");
        let broad_string = object_property_initializer(&source, file, contextual, "broadString");
        let exact_number = object_property_initializer(&source, file, contextual, "exactNumber");
        let broad_number = object_property_initializer(&source, file, contextual, "broadNumber");

        context.check_source_file(file).unwrap();

        let (
            string,
            number,
            bigint,
            boolean,
            null_widening,
            undefined_widening,
            regular_x,
            regular_one,
            regular_one_bigint,
            regular_true,
        ) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.boolean_type,
                bootstrap.null_widening_type,
                bootstrap.undefined_widening_type,
                bootstrap.cached_string_literal_type("x").unwrap(),
                bootstrap
                    .cached_number_literal_type(Number::new(1.0))
                    .unwrap(),
                bootstrap
                    .cached_bigint_literal_type(&PseudoBigInt::parse_valid("1n"))
                    .unwrap(),
                bootstrap.regular_true_type,
            )
        };
        assert_eq!(
            [
                object_property_type(&context, contextual, "exactString"),
                object_property_type(&context, contextual, "broadString"),
                object_property_type(&context, contextual, "exactNumber"),
                object_property_type(&context, contextual, "broadNumber"),
                object_property_type(&context, contextual, "exactBigInt"),
                object_property_type(&context, contextual, "broadBigInt"),
                object_property_type(&context, contextual, "exactBoolean"),
                object_property_type(&context, contextual, "broadBoolean"),
                object_property_type(&context, contextual, "nullValue"),
                object_property_type(&context, contextual, "undefinedValue"),
            ],
            [
                regular_x,
                string,
                regular_one,
                number,
                regular_one_bigint,
                bigint,
                regular_true,
                regular_true,
                null_widening,
                undefined_widening,
            ]
        );
        assert_eq!(
            [
                object_property_type(&context, uncontextual, "stringValue"),
                object_property_type(&context, uncontextual, "numberValue"),
                object_property_type(&context, uncontextual, "bigintValue"),
                object_property_type(&context, uncontextual, "booleanValue"),
                object_property_type(&context, uncontextual, "nullValue"),
                object_property_type(&context, uncontextual, "undefinedValue"),
            ],
            [
                string,
                number,
                bigint,
                boolean,
                null_widening,
                undefined_widening,
            ]
        );
        let fresh_x = context
            .store()
            .fresh_type_of_literal_type(regular_x)
            .unwrap();
        let fresh_one = context
            .store()
            .fresh_type_of_literal_type(regular_one)
            .unwrap();
        assert_eq!(
            [
                resolved_node_type(&context, exact_string),
                resolved_node_type(&context, broad_string),
                resolved_node_type(&context, exact_number),
                resolved_node_type(&context, broad_number),
            ],
            [fresh_x, fresh_x, fresh_one, fresh_one],
            "expression links retain raw literal identity while mutable property results are transformed",
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn contextual_literal_kind_matching_is_value_independent_at_source_level() {
        let source = parsed(concat!(
            "interface Context { ",
            r#"exact: "expected"; literalOrNumber: "expected" | number; "#,
            "primitiveOrNumber: string | number; booleanValue: boolean; } ",
            r#"const value: Context = { exact: "wrong", literalOrNumber: "wrong", "#,
            r#"primitiveOrNumber: "wrong", booleanValue: true };"#,
        ));
        let file = FileId::new(90);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let value = variable_initializer(&source, file, "value");

        context.check_source_file(file).unwrap();

        let (regular_wrong, string, regular_true) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.cached_string_literal_type("wrong").unwrap(),
                bootstrap.string_type,
                bootstrap.regular_true_type,
            )
        };
        assert_eq!(
            [
                object_property_type(&context, value, "exact"),
                object_property_type(&context, value, "literalOrNumber"),
                object_property_type(&context, value, "primitiveOrNumber"),
                object_property_type(&context, value, "booleanValue"),
            ],
            [regular_wrong, regular_wrong, string, regular_true]
        );
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        for (diagnostic, property, source_display, target) in [
            (&diagnostics[0], "exact", "\"wrong\"", "\"expected\""),
            (
                &diagnostics[1],
                "literalOrNumber",
                "\"wrong\"",
                "number | \"expected\"",
            ),
        ] {
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.arguments,
                [source_display.to_owned(), target.to_owned()]
            );
            assert_property_name_span(&source, diagnostic.node.unwrap(), property, true);
            assert_eq!(diagnostic.related_information.len(), 1);
            assert_eq!(diagnostic.related_information[0].diagnostic.code(), 6500);
            assert_property_name_span(
                &source,
                diagnostic.related_information[0].node.unwrap(),
                property,
                false,
            );
            assert_eq!(
                diagnostic.related_information[0].diagnostic.arguments,
                [property.to_owned(), "Context".to_owned()]
            );
        }
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn nested_context_and_no_match_widening_reuse_warm_object_identity() {
        let source = parsed(concat!(
            r#"interface Node { tag: "node"; broad: string; next?: Node } "#,
            r#"interface Outer { known: { exact: "x"; broad: string }; recursive: Node } "#,
            r#"const value: Outer = { known: { exact: "x", broad: "a" }, "#,
            r#"recursive: { tag: "node", broad: "a", next: { tag: "node", broad: "b" } } }; "#,
            r#"const noContext: any = { unknown: { exact: "free", "#,
            r#"broad: "free", deeper: { count: 1 } } };"#,
        ));
        let file = FileId::new(91);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let value = variable_initializer(&source, file, "value");
        let known = object_property_initializer(&source, file, value, "known");
        let recursive = object_property_initializer(&source, file, value, "recursive");
        let next = object_property_initializer(&source, file, recursive, "next");
        let no_context = variable_initializer(&source, file, "noContext");
        let unknown = object_property_initializer(&source, file, no_context, "unknown");
        let deeper = object_property_initializer(&source, file, unknown, "deeper");
        let object_nodes = [value, known, recursive, next, no_context, unknown, deeper];

        context.check_source_file(file).unwrap();

        let (regular_x, regular_node, string, number) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.cached_string_literal_type("x").unwrap(),
                bootstrap.cached_string_literal_type("node").unwrap(),
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        assert_eq!(object_property_type(&context, known, "exact"), regular_x);
        assert_eq!(object_property_type(&context, known, "broad"), string);
        assert_eq!(
            object_property_type(&context, recursive, "tag"),
            regular_node
        );
        assert_eq!(object_property_type(&context, recursive, "broad"), string);
        assert_eq!(object_property_type(&context, next, "tag"), regular_node);
        assert_eq!(object_property_type(&context, next, "broad"), string);
        assert_eq!(object_property_type(&context, unknown, "exact"), string);
        assert_eq!(object_property_type(&context, unknown, "broad"), string);
        assert_eq!(object_property_type(&context, deeper, "count"), number);
        assert!(context.diagnostics().is_empty());

        let object_types = object_nodes.map(|node| resolved_node_type(&context, node));
        let warm = observable_state(&context, file);
        let source_ref = context.source_file(file).unwrap();
        let mut source_links = context
            .store()
            .source_file_links(source_ref)
            .cloned()
            .unwrap();
        source_links.type_checked = false;
        assert!(
            context
                .store_mut_for_test()
                .set_source_file_links(source_ref, source_links)
        );

        context.check_source_file(file).unwrap();

        assert_eq!(
            object_nodes.map(|node| resolved_node_type(&context, node)),
            object_types
        );
        assert_eq!(observable_state(&context, file), warm);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn cached_alias_context_contract_poisons_reject_cold_source_without_writes() {
        #[derive(Clone, Copy)]
        enum Poison {
            OwnerMembers,
            AliasParent,
            PropertyLinks,
        }

        for (index, poison) in [
            Poison::OwnerMembers,
            Poison::AliasParent,
            Poison::PropertyLinks,
        ]
        .into_iter()
        .enumerate()
        {
            let source = parsed(concat!(
                "const value: Target = { good: true }; ",
                "type Target = { good: boolean; missing: string };",
            ));
            let file = FileId::new(92 + u32::try_from(index).unwrap());
            let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
            let target = context
                .get_type_from_type_node(variable_type_node(&source, file, "value"))
                .unwrap();
            let record = context.store().type_payload(target).unwrap();
            let owner = record.symbol().unwrap();
            let alias = record.alias().unwrap();
            let alias_symbol = context.store().type_alias(alias).unwrap().symbol().unwrap();
            match poison {
                Poison::OwnerMembers => {
                    assert!(context.store().symbol(owner).unwrap().members().is_some());
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_symbol_relationships(owner, None, None, None, None,)
                    );
                }
                Poison::AliasParent => {
                    assert!(context.store_mut_for_test().set_symbol_relationships(
                        alias_symbol,
                        None,
                        None,
                        Some(owner),
                        None,
                    ));
                }
                Poison::PropertyLinks => {
                    let property = declared_object_property_symbol(&context, target, "missing");
                    let mut links = context
                        .store()
                        .value_symbol_links(property)
                        .cloned()
                        .unwrap();
                    links.write_type =
                        Some(context.store().intrinsic_bootstrap().unwrap().string_type);
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_value_symbol_links(property, links)
                    );
                }
            }
            let before = observable_state(&context, file);

            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::DeclaredType(
                    DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::InvalidCachedUnionType(target)
                    )
                ))
            );
            assert_eq!(observable_state(&context, file), before);
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
            assert!(
                context
                    .store()
                    .type_node_links(variable_initializer(&source, file, "value"))
                    .and_then(|links| links.resolved_type)
                    .is_none()
            );
        }
    }

    #[test]
    fn unmatched_malformed_nested_alias_context_rejects_before_source_publication() {
        let source = parsed(concat!(
            "const value: Target = { good: true }; ",
            "type Target = { good: boolean; missing: NestedTarget }; ",
            "type NestedTarget = { bad: string };",
        ));
        let file = FileId::new(95);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let target = context
            .get_type_from_type_node(variable_type_node(&source, file, "value"))
            .unwrap();
        let missing = declared_object_property_symbol(&context, target, "missing");
        let nested = context
            .store()
            .value_symbol_links(missing)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let nested_owner = context
            .store()
            .type_payload(nested)
            .unwrap()
            .symbol()
            .unwrap();
        assert!(
            context
                .store()
                .symbol(nested_owner)
                .unwrap()
                .members()
                .is_some()
        );
        assert!(context.store_mut_for_test().set_symbol_relationships(
            nested_owner,
            None,
            None,
            None,
            None,
        ));
        let before = observable_state(&context, file);

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::DeclaredType(
                DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::InvalidCachedUnionType(nested)
                )
            ))
        );
        assert_eq!(observable_state(&context, file), before);
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
        assert!(
            context
                .store()
                .type_node_links(variable_initializer(&source, file, "value"))
                .and_then(|links| links.resolved_type)
                .is_none()
        );
    }

    #[test]
    fn interface_object_assignability_uses_property_object_display() {
        let source = parsed(concat!(
            "interface TextValue { value: string } ",
            "interface NumberValue { value: number } ",
            "const first: TextValue = { value: 1 }; ",
            r#"const second: NumberValue = { value: "wrong" };"#,
        ));
        let file = FileId::new(68);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let first = variable_initializer(&source, file, "first");
        let second = variable_initializer(&source, file, "second");

        context.check_source_file(file).unwrap();

        assert!(
            context
                .store()
                .type_node_links(first)
                .and_then(|links| links.resolved_type)
                .is_some()
        );
        assert!(
            context
                .store()
                .type_node_links(second)
                .and_then(|links| links.resolved_type)
                .is_some()
        );
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(node_text(&source, diagnostics[0].node.unwrap()), "value");
        assert_eq!(diagnostics[0].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert_eq!(diagnostics[0].related_information.len(), 1);
        assert_eq!(
            node_text(&source, diagnostics[0].related_information[0].node.unwrap()),
            "value"
        );
        assert_eq!(
            diagnostics[0].related_information[0].diagnostic.code(),
            6500
        );
        assert_eq!(
            diagnostics[0].related_information[0]
                .diagnostic
                .render()
                .unwrap(),
            "The expected type comes from property 'value' which is declared here on type 'TextValue'"
        );

        assert_eq!(node_text(&source, diagnostics[1].node.unwrap()), "value");
        assert_eq!(diagnostics[1].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics[1].diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'."
        );
        assert_eq!(diagnostics[1].related_information.len(), 1);
        assert_eq!(
            node_text(&source, diagnostics[1].related_information[0].node.unwrap()),
            "value"
        );
        assert_eq!(
            diagnostics[1].related_information[0].diagnostic.code(),
            6500
        );
        assert_eq!(
            diagnostics[1].related_information[0]
                .diagnostic
                .render()
                .unwrap(),
            "The expected type comes from property 'value' which is declared here on type 'NumberValue'"
        );
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn leaf_declared_property_relation_details_use_target_order_and_plain_fallbacks() {
        let source = parsed(concat!(
            "type Source = { second: number; first: number }; ",
            "type Target = { first: string; second: string }; ",
            "type Disjoint = { other: number }; ",
            "const source: Source = { second: 2, first: 1 }; ",
            "const disjoint: Disjoint = { other: 1 }; ",
            "const chained: Target = source; ",
            "const primitive: string = 1; ",
            "const missing: Target = disjoint;",
        ));
        let file = FileId::new(132);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 3);
        assert_eq!(diagnostics[0].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            concat!(
                "Type 'Source' is not assignable to type 'Target'.\n",
                "  Types of property 'first' are incompatible.\n",
                "    Type 'number' is not assignable to type 'string'.",
            ),
            "the first incompatible target property controls the relation chain"
        );
        assert_eq!(
            diagnostics[1].diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert!(diagnostics[1].diagnostic.details.is_empty());
        assert_eq!(
            diagnostics[2].diagnostic.render().unwrap(),
            "Type 'Disjoint' is not assignable to type 'Target'."
        );
        assert!(diagnostics[2].diagnostic.details.is_empty());
        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.related_information.is_empty())
        );

        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn nonterminal_nested_declared_property_details_fall_back_to_plain_root() {
        let source = parsed(concat!(
            "type SourceChild = { id: number }; ",
            "type TargetChild = { id: string }; ",
            "type Source = { child: SourceChild }; ",
            "type Target = { child: TargetChild }; ",
            "const child: SourceChild = { id: 1 }; ",
            "const source: Source = { child: child }; ",
            "const value: Target = source;",
        ));
        let file = FileId::new(134);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one nested declared-property diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'Source' is not assignable to type 'Target'."
        );
        assert!(diagnostic.diagnostic.details.is_empty());
    }

    #[test]
    fn malformed_leaf_declared_property_graph_fails_without_diagnostic_publication() {
        let source = parsed(concat!(
            "type Source = { value: number }; ",
            "type Target = { value: string }; ",
            "const source: Source = { value: 1 }; ",
            "const target: Target = { value: 'ok' };",
        ));
        let file = FileId::new(133);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let source_type = context
            .get_type_from_type_node(variable_type_node(&source, file, "source"))
            .unwrap();
        let target_type = context
            .get_type_from_type_node(variable_type_node(&source, file, "target"))
            .unwrap();
        let property = declared_object_property_symbol(&context, source_type, "value");
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(property, ValueSymbolLinks::default())
        );
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();
        let before = observable_state(&context, file);

        let result = super::super::object_diagnostics::declared_property_mismatch_details(
            context.store_mut_for_test(),
            &host,
            &globals,
            source_type,
            target_type,
            CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            CanonicalCheckerOptions::default(),
        );

        assert!(matches!(
            result,
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::InvalidStructuredMembers(actual),
            )) if actual == source_type
        ));
        assert_eq!(observable_state(&context, file), before);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn object_literal_excess_properties_use_exact_names_and_pinned_messages_in_source_order() {
        let source = parsed(concat!(
            "interface Child { id: number; value: string } ",
            "type Config = { count: number }; ",
            r#"const child: Child = { id: 1, value: "ok", extra: true }; "#,
            "const config: Config = ({ count: 1, surplus: false });",
        ));
        let file = FileId::new(96);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2353, 2353]
        );
        assert_eq!(node_text(&source, diagnostics[0].node.unwrap()), "extra");
        assert_eq!(node_text(&source, diagnostics[1].node.unwrap()), "surplus");
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Object literal may only specify known properties, and 'extra' does not exist in type 'Child'."
        );
        assert_eq!(
            diagnostics[1].diagnostic.render().unwrap(),
            "Object literal may only specify known properties, and 'surplus' does not exist in type 'Config'."
        );
        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.related_information.is_empty())
        );

        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
        assert_eq!(context.diagnostics().len(), 2);
    }

    #[test]
    fn fresh_object_literals_accept_empty_and_canonical_global_object_targets() {
        let library = parsed(concat!(
            "interface IArguments {} ",
            "interface Array<T> {} ",
            "interface Object {} ",
            "declare var Object: unknown; ",
            "interface Function {} ",
            "interface String {} ",
            "interface Number {} ",
            "interface Boolean {} ",
            "interface RegExp {}",
        ));
        let source = parsed(concat!(
            "const empty: {} = { extra: 1 }; ",
            "const global: Object = { extra: 1 };",
        ));
        let library_file = FileId::new(105);
        let file = FileId::new(106);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
        for variable in ["empty", "global"] {
            assert!(
                context
                    .store()
                    .type_node_links(variable_initializer(&source, file, variable))
                    .and_then(|links| links.resolved_type)
                    .is_some()
            );
        }
        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn excess_property_suggestion_ties_follow_target_declaration_order() {
        let source = parsed(concat!(
            "type First = { foo: number; foooo: number }; ",
            "type Reversed = { foooo: number; foo: number }; ",
            "const first: First = { fooo: 1 }; ",
            "const reversed: Reversed = { fooo: 1 };",
        ));
        let file = FileId::new(97);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(diagnostics[0].diagnostic.code(), 2561);
        assert_eq!(diagnostics[1].diagnostic.code(), 2561);
        assert_property_name_span(&source, diagnostics[0].node.unwrap(), "fooo", true);
        assert_property_name_span(&source, diagnostics[1].node.unwrap(), "fooo", true);
        assert_eq!(
            diagnostics[0].diagnostic.arguments,
            ["fooo", "First", "foo"]
        );
        assert_eq!(
            diagnostics[1].diagnostic.arguments,
            ["fooo", "Reversed", "foooo"]
        );
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Object literal may only specify known properties, but 'fooo' does not exist in type 'First'. Did you mean to write 'foo'?"
        );
        assert_eq!(
            diagnostics[1].diagnostic.render().unwrap(),
            "Object literal may only specify known properties, but 'fooo' does not exist in type 'Reversed'. Did you mean to write 'foooo'?"
        );
    }

    #[test]
    fn first_excess_in_source_order_suppresses_later_excess_and_missing_fallbacks() {
        let source = parsed(concat!(
            "type Target = { required: string }; ",
            "const actual: Target = { first: true, second: false };",
        ));
        let file = FileId::new(104);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected exactly one first-excess diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2353);
        assert_eq!(diagnostic.diagnostic.arguments, ["first", "Target"]);
        assert_property_name_span(&source, diagnostic.node.unwrap(), "first", true);
        assert!(diagnostic.related_information.is_empty());
    }

    #[test]
    fn known_property_mismatches_recurse_in_source_order_and_suppress_shape_fallbacks() {
        let source = parsed(concat!(
            "type Leaf = { value: string }; ",
            "type Root = { scalar: string; nested: Leaf; required: number }; ",
            "const actual: Root = { scalar: 1, nested: { value: 2, extra: true }, ",
            "unexpected: false };",
        ));
        let file = FileId::new(98);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        for (diagnostic, property, target) in [
            (&diagnostics[0], "scalar", "Root"),
            (&diagnostics[1], "value", "Leaf"),
        ] {
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'number' is not assignable to type 'string'."
            );
            assert_property_name_span(&source, diagnostic.node.unwrap(), property, true);
            assert_eq!(diagnostic.related_information.len(), 1);
            let related = &diagnostic.related_information[0];
            assert_eq!(related.diagnostic.code(), 6500);
            assert_property_name_span(&source, related.node.unwrap(), property, false);
            assert_eq!(
                related.diagnostic.arguments,
                [property.to_owned(), target.to_owned()]
            );
        }
        assert!(diagnostics.iter().all(|diagnostic| {
            !matches!(
                diagnostic.diagnostic.code(),
                2353 | 2561 | 2739 | 2740 | 2741
            )
        }));
    }

    #[test]
    fn multi_property_diagnostics_stage_atomically_before_later_display_failure() {
        let split_literal = format!("{}é{}", "x".repeat(315), "x".repeat(10));
        let source = parsed(&format!(
            "type Target = {{ first: string; second: \"{split_literal}\" }}; \
             const actual: Target = {{ first: 1, second: 2 }};"
        ));
        let file = FileId::new(107);
        let mut truncated = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let mut complete = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                no_error_truncation: true,
                ..CanonicalCheckerOptions::default()
            },
        );
        let target = truncated
            .get_type_from_type_node(variable_type_node(&source, file, "actual"))
            .unwrap();
        let second = declared_object_property_symbol(&truncated, target, "second");
        let split_target = truncated
            .store()
            .value_symbol_links(second)
            .and_then(|links| links.resolved_type)
            .unwrap();

        assert_eq!(
            truncated.check_source_file(file),
            Err(SourceCheckError::TypeDisplayUnavailable(
                TypeDisplayUnavailable::Utf8TruncationBoundary {
                    type_id: split_target,
                    boundary: 317,
                }
            ))
        );
        assert!(truncated.diagnostics().is_empty());
        assert!(!is_type_checked(&truncated, file));

        complete.check_source_file(file).unwrap();

        let diagnostics = complete.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        for (diagnostic, property, target_display) in [
            (&diagnostics[0], "first", "string".to_owned()),
            (&diagnostics[1], "second", format!("\"{split_literal}\"")),
        ] {
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.arguments,
                ["number".to_owned(), target_display]
            );
            assert_property_name_span(&source, diagnostic.node.unwrap(), property, true);
            assert_eq!(diagnostic.related_information.len(), 1);
            let related = &diagnostic.related_information[0];
            assert_eq!(related.diagnostic.code(), 6500);
            assert_eq!(related.diagnostic.arguments, [property, "Target"]);
            assert_property_name_span(&source, related.node.unwrap(), property, false);
        }
        assert!(is_type_checked(&complete, file));
    }

    #[test]
    fn nested_shape_errors_attach_only_the_immediate_containing_property() {
        let source = parsed(concat!(
            "type ExcessInner = { known: string }; ",
            "type ExcessRoot = { outer: ExcessInner }; ",
            r#"const excess: ExcessRoot = { outer: { known: "ok", extra: true } }; "#,
            "type SingleInner = { inner: string }; ",
            "type SingleRoot = { outer: SingleInner }; ",
            "const single: SingleRoot = { outer: {} }; ",
            "type MultiInner = { first: string; second: number }; ",
            "type MultiRoot = { outer: MultiInner }; ",
            "const multi: MultiRoot = { outer: {} };",
        ));
        let file = FileId::new(99);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 3);

        let excess = &diagnostics[0];
        assert_eq!(excess.diagnostic.code(), 2353);
        assert_eq!(excess.diagnostic.arguments, ["extra", "ExcessInner"]);
        assert_property_name_span(&source, excess.node.unwrap(), "extra", true);
        assert_eq!(excess.related_information.len(), 1);
        assert_eq!(excess.related_information[0].diagnostic.code(), 6500);
        assert_eq!(
            excess.related_information[0].diagnostic.arguments,
            ["outer", "ExcessRoot"]
        );
        assert_property_name_span(
            &source,
            excess.related_information[0].node.unwrap(),
            "outer",
            false,
        );

        let single = &diagnostics[1];
        assert_eq!(single.diagnostic.code(), 2741);
        assert_eq!(single.diagnostic.arguments, ["inner", "{}", "SingleInner"]);
        assert_property_name_span(&source, single.node.unwrap(), "outer", true);
        assert_eq!(
            single
                .related_information
                .iter()
                .map(|related| related.diagnostic.code())
                .collect::<Vec<_>>(),
            [2728, 6500]
        );
        assert_property_name_span(
            &source,
            single.related_information[0].node.unwrap(),
            "inner",
            false,
        );
        assert_property_name_span(
            &source,
            single.related_information[1].node.unwrap(),
            "outer",
            false,
        );
        assert_eq!(
            single.related_information[1].diagnostic.arguments,
            ["outer", "SingleRoot"]
        );

        let multi = &diagnostics[2];
        assert_eq!(multi.diagnostic.code(), 2739);
        assert_eq!(
            multi.diagnostic.arguments,
            ["{}", "MultiInner", "first, second"]
        );
        assert_property_name_span(&source, multi.node.unwrap(), "outer", true);
        assert_eq!(multi.related_information.len(), 1);
        assert_eq!(multi.related_information[0].diagnostic.code(), 6500);
        assert_eq!(
            multi.related_information[0].diagnostic.arguments,
            ["outer", "MultiRoot"]
        );
        assert_property_name_span(
            &source,
            multi.related_information[0].node.unwrap(),
            "outer",
            false,
        );
    }

    #[test]
    fn missing_required_properties_use_target_order_and_pinned_count_thresholds() {
        let source = parsed(concat!(
            "type One = { a: string }; ",
            "type Two = { a: string; b: number }; ",
            "type Five = { a: string; b: number; c: boolean; d: string; e: number }; ",
            "type Six = { a: string; b: number; c: boolean; d: string; e: number; f: boolean }; ",
            "type Optional = { maybe?: string }; ",
            "const one: One = {}; const two: Two = {}; const five: Five = {}; ",
            "const six: Six = {}; const optional: Optional = {};",
        ));
        let file = FileId::new(100);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 4);
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2741, 2739, 2739, 2740]
        );
        for (diagnostic, variable) in diagnostics.iter().zip(["one", "two", "five", "six"]) {
            assert_eq!(
                diagnostic.node,
                Some(variable_name(&source, file, variable))
            );
        }
        assert_eq!(diagnostics[0].diagnostic.arguments, ["a", "{}", "One"]);
        assert_eq!(diagnostics[0].related_information.len(), 1);
        assert_eq!(
            diagnostics[0].related_information[0].diagnostic.code(),
            2728
        );
        assert_property_name_span(
            &source,
            diagnostics[0].related_information[0].node.unwrap(),
            "a",
            false,
        );
        assert_eq!(diagnostics[1].diagnostic.arguments, ["{}", "Two", "a, b"]);
        assert_eq!(
            diagnostics[2].diagnostic.arguments,
            ["{}", "Five", "a, b, c, d, e"]
        );
        assert_eq!(
            diagnostics[3].diagnostic.arguments,
            ["{}", "Six", "a, b, c, d", "2"]
        );
        assert!(
            diagnostics[1..]
                .iter()
                .all(|diagnostic| diagnostic.related_information.is_empty())
        );
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn no_error_truncation_controls_object_diagnostic_type_arguments() {
        let declarations = (0..20)
            .map(|index| format!("property{index}: number"))
            .collect::<Vec<_>>()
            .join("; ");
        let assignments = (0..20)
            .map(|index| format!("property{index}: {index}"))
            .collect::<Vec<_>>()
            .join(", ");
        let source = parsed(&format!(
            "const value: {{ {declarations} }} = {{ {assignments}, extra: true }};"
        ));
        let file = FileId::new(101);
        let mut truncated = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let mut complete = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                no_error_truncation: true,
                ..CanonicalCheckerOptions::default()
            },
        );

        truncated.check_source_file(file).unwrap();
        complete.check_source_file(file).unwrap();

        let truncated = &truncated.diagnostics().as_slice()[0];
        let complete = &complete.diagnostics().as_slice()[0];
        assert_eq!(truncated.diagnostic.code(), 2353);
        assert_eq!(complete.diagnostic.code(), 2353);
        assert_property_name_span(&source, truncated.node.unwrap(), "extra", true);
        assert_property_name_span(&source, complete.node.unwrap(), "extra", true);
        assert!(truncated.diagnostic.arguments[1].contains("..."));
        assert!(!complete.diagnostic.arguments[1].contains("..."));
        assert!(complete.diagnostic.arguments[1].contains("property19: number"));
    }

    #[test]
    fn ts6500_uses_exact_default_library_source_provenance() {
        let usage = parsed(concat!(
            "const mismatch: Target = { value: 1 }; ",
            "const libraryMismatch: LibraryTarget = { value: 1 }; ",
            "const missing: Missing = {};",
        ));
        let declarations = parsed(concat!(
            "interface Target { value: string } ",
            "interface Missing { required: number }",
        ));
        let library = parsed("interface LibraryTarget { value: string }");
        let usage_file = FileId::new(102);
        let declarations_file = FileId::new(103);
        let library_file = FileId::new(108);
        let mut context = context_with_default_library_files(
            &[
                (usage_file, &usage),
                (declarations_file, &declarations),
                (library_file, &library),
            ],
            &[library_file],
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(usage_file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 3);
        assert_eq!(diagnostics[0].diagnostic.code(), 2322);
        assert_eq!(diagnostics[0].related_information.len(), 1);
        assert_eq!(
            diagnostics[0].related_information[0].diagnostic.code(),
            6500
        );
        assert_eq!(
            diagnostics[0].related_information[0]
                .node
                .map(|node| node.file),
            Some(declarations_file)
        );
        assert_property_name_span(
            &declarations,
            diagnostics[0].related_information[0].node.unwrap(),
            "value",
            false,
        );
        assert_eq!(diagnostics[1].diagnostic.code(), 2322);
        assert!(diagnostics[1].related_information.is_empty());
        assert_eq!(diagnostics[2].diagnostic.code(), 2741);
        assert_eq!(diagnostics[2].related_information.len(), 1);
        assert_eq!(
            diagnostics[2].related_information[0].diagnostic.code(),
            2728
        );
        assert_eq!(
            diagnostics[2].related_information[0]
                .node
                .map(|node| node.file),
            Some(declarations_file)
        );
        assert_property_name_span(
            &declarations,
            diagnostics[2].related_information[0].node.unwrap(),
            "required",
            false,
        );
    }

    #[test]
    fn unsupported_interfaces_reject_the_complete_source_plan_atomically() {
        let cases = [
            "type Earlier = Earlier; export declare interface Bad { value: string }",
            "type Earlier = Earlier; export default interface Bad { value: string }",
            "type Earlier = Earlier; export interface Bad { method(): string }",
        ];
        for (index, text) in cases.into_iter().enumerate() {
            let source = parsed(text);
            let file = FileId::new(80 + u32::try_from(index).unwrap());
            let mut context = context_with_module_state(
                &[(file, &source)],
                CanonicalModuleState::External,
                CanonicalCheckerOptions::default(),
            );
            let before = observable_state(&context, file);

            let result = context.check_source_file(file);
            assert!(
                matches!(
                    result,
                    Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Syntax {
                            role: SourceSyntaxRole::InterfaceDeclaration,
                            ..
                        }
                    ))
                ),
                "source: {text}, actual: {result:?}"
            );
            assert_eq!(observable_state(&context, file), before, "source: {text}");
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn source_object_literals_publish_nested_members_in_order_without_structural_relation() {
        let source = parsed(concat!(
            r#"const value: any = { text: "ok", "#,
            "nested: { count: -1, missing: undefined } };",
        ));
        let file = FileId::new(70);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let objects = source
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::ObjectLiteralExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        assert_eq!(objects.len(), 2);

        context.check_source_file(file).unwrap();

        for object in &objects {
            let type_ = context
                .store()
                .type_node_links(*object)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let record = context.store().type_payload(type_).unwrap();
            assert_eq!(
                record.object_flags(),
                ObjectFlags::ANONYMOUS
                    | ObjectFlags::OBJECT_LITERAL
                    | ObjectFlags::FRESH_LITERAL
                    | ObjectFlags::CONTAINS_WIDENING_TYPE
                    | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL
                    | ObjectFlags::MEMBERS_RESOLVED
            );
            let TypeData::Object(object_data) = record.data() else {
                panic!("object-literal type must use the plain object payload")
            };
            let owner = record.symbol().unwrap();
            let owner_record = context.store().symbol(owner).unwrap();
            assert_eq!(owner_record.flags(), SymbolFlags::OBJECT_LITERAL);
            assert_eq!(owner_record.check_flags(), CheckFlags::NONE);
            assert_eq!(owner_record.name(), InternalSymbolName::Object.as_ref());
            assert_eq!(owner_record.declarations(), Some([*object].as_slice()));
            assert_eq!(owner_record.value_declaration(), Some(*object));
            assert!(owner_record.parent().is_none());
            assert!(owner_record.exports().is_none());
            assert!(owner_record.export_symbol().is_none());

            let raw_members = owner_record.members().unwrap();
            let cloned_members = object_data.structured.members.unwrap();
            assert_ne!(cloned_members, raw_members);
            let raw_table = context.store().symbol_table(raw_members).unwrap();
            let cloned_table = context.store().symbol_table(cloned_members).unwrap();
            let cloned_properties = object_data.structured.properties.as_ref().unwrap();
            assert_eq!(cloned_table.len(), cloned_properties.len());
            for cloned in cloned_properties {
                let clone_record = context.store().symbol(*cloned).unwrap();
                let clone_links = context.store().value_symbol_links(*cloned).unwrap();
                let raw = clone_links.target.unwrap();
                let raw_record = context.store().symbol(raw).unwrap();
                assert_eq!(raw_record.flags(), SymbolFlags::PROPERTY);
                assert_eq!(raw_record.check_flags(), CheckFlags::NONE);
                assert_eq!(
                    clone_record.flags(),
                    raw_record.flags() | SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
                );
                assert_eq!(clone_record.check_flags(), CheckFlags::NONE);
                assert_eq!(clone_record.name(), raw_record.name());
                assert_eq!(clone_record.declarations(), raw_record.declarations());
                assert_eq!(
                    clone_record.value_declaration(),
                    raw_record.value_declaration()
                );
                assert_eq!(clone_record.parent(), Some(owner));
                assert_eq!(raw_record.parent(), Some(owner));
                assert_eq!(context.store().get_merged_symbol(*cloned), Some(*cloned));
                assert!(clone_record.members().is_none());
                assert!(clone_record.exports().is_none());
                assert!(clone_record.export_symbol().is_none());
                assert_eq!(
                    cloned_table.get(clone_record.name()),
                    Some(*cloned),
                    "the result table owns the checker clone"
                );
                assert_eq!(
                    raw_table.get(raw_record.name()),
                    Some(raw),
                    "the binder table retains the raw member"
                );
                assert!(
                    context
                        .store()
                        .value_symbol_links(raw)
                        .is_none_or(|links| links == &ValueSymbolLinks::default())
                );
                assert_eq!(
                    clone_links,
                    &ValueSymbolLinks {
                        resolved_type: clone_links.resolved_type,
                        target: Some(raw),
                        ..ValueSymbolLinks::default()
                    }
                );
            }
        }
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn empty_object_literal_allocates_a_distinct_empty_result_table_and_reuses_it_warm() {
        let source = parsed("const value: any = {};");
        let file = FileId::new(87);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let object = variable_initializer(&source, file, "value");
        let owner = context.file(file).unwrap().1.symbol(object).unwrap();
        assert!(context.store().symbol(owner).unwrap().members().is_none());

        context.check_source_file(file).unwrap();
        let type_ = context
            .store()
            .type_node_links(object)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let record = context.store().type_payload(type_).unwrap();
        assert_eq!(record.symbol(), Some(owner));
        assert_eq!(
            record.object_flags(),
            ObjectFlags::ANONYMOUS
                | ObjectFlags::OBJECT_LITERAL
                | ObjectFlags::FRESH_LITERAL
                | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL
                | ObjectFlags::MEMBERS_RESOLVED
        );
        let TypeData::Object(object_data) = record.data() else {
            panic!("empty object literal must retain a plain object payload")
        };
        let result_members = object_data.structured.members.unwrap();
        assert!(
            context
                .store()
                .symbol_table(result_members)
                .unwrap()
                .is_empty()
        );
        assert!(object_data.structured.properties.is_none());
        assert!(context.store().symbol(owner).unwrap().members().is_none());

        let warm = observable_state(&context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
        let warm_record = context.store().type_payload(type_).unwrap();
        let TypeData::Object(warm_object) = warm_record.data() else {
            unreachable!()
        };
        assert_eq!(warm_object.structured.members, Some(result_members));
    }

    #[test]
    fn object_literal_owner_parent_poison_rejects_planning_without_writes() {
        let source = parsed("const value: any = {};");
        let file = FileId::new(88);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let object = variable_initializer(&source, file, "value");
        let owner = context.file(file).unwrap().1.symbol(object).unwrap();
        let parent = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_symbol;
        assert!(context.store_mut_for_test().set_symbol_relationships(
            owner,
            None,
            None,
            Some(parent),
            None,
        ));
        let before = observable_state(&context, file);

        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Syntax {
                    node,
                    role: SourceSyntaxRole::ObjectLiteral,
                    ..
                }
            )) if node == object
        ));
        assert_eq!(observable_state(&context, file), before);
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }

    #[test]
    fn warm_object_propagating_flag_poison_is_typed_and_repair_reuses_identity() {
        let source = parsed("const value: any = { nested: { missing: undefined } };");
        let file = FileId::new(86);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let outer = variable_initializer(&source, file, "value");

        context.check_source_file(file).unwrap();
        let outer_type = context
            .store()
            .type_node_links(outer)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let expected_flags = context
            .store()
            .type_payload(outer_type)
            .unwrap()
            .object_flags();
        assert!(expected_flags.contains(ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL));
        assert!(expected_flags.contains(ObjectFlags::CONTAINS_WIDENING_TYPE));

        let poisoned_flags = expected_flags & !ObjectFlags::CONTAINS_WIDENING_TYPE;
        assert!(
            context
                .store_mut_for_test()
                .set_type_object_flags(outer_type, poisoned_flags)
        );
        let source_ref = context.source_file(file).unwrap();
        let mut source_links = context
            .store()
            .source_file_links(source_ref)
            .cloned()
            .unwrap();
        source_links.type_checked = false;
        assert!(
            context
                .store_mut_for_test()
                .set_source_file_links(source_ref, source_links)
        );
        let poisoned = observable_state(&context, file);

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::ObjectLiteral(
                SourceObjectLiteralError::InvalidCache {
                    node: outer,
                    type_: Some(outer_type),
                }
            ))
        );
        assert_eq!(observable_state(&context, file), poisoned);
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));

        assert!(
            context
                .store_mut_for_test()
                .set_type_object_flags(outer_type, expected_flags)
        );
        context.check_source_file(file).unwrap();
        assert_eq!(
            context
                .store()
                .type_node_links(outer)
                .and_then(|links| links.resolved_type),
            Some(outer_type)
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn warm_object_property_poison_is_typed_and_repair_reuses_identity() {
        let source = parsed(r#"const value: any = { text: "ok" };"#);
        let file = FileId::new(71);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let object = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ObjectLiteralExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();

        context.check_source_file(file).unwrap();
        let object_type = context
            .store()
            .type_node_links(object)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let property = match context.store().type_payload(object_type).unwrap().data() {
            TypeData::Object(object) => object.structured.properties.as_ref().unwrap()[0],
            _ => unreachable!(),
        };
        let expected = context
            .store()
            .value_symbol_links(property)
            .cloned()
            .unwrap();
        let poison = context.store().intrinsic_bootstrap().unwrap().number_type;
        let mut wrong_type = expected.clone();
        wrong_type.resolved_type = Some(poison);
        let mut missing_target = expected.clone();
        missing_target.target = None;
        let source_ref = context.source_file(file).unwrap();
        let mut source_links = context
            .store()
            .source_file_links(source_ref)
            .cloned()
            .unwrap();
        source_links.type_checked = false;
        assert!(
            context
                .store_mut_for_test()
                .set_source_file_links(source_ref, source_links)
        );
        for poisoned_links in [wrong_type, missing_target] {
            assert!(
                context
                    .store_mut_for_test()
                    .set_value_symbol_links(property, poisoned_links)
            );
            let poisoned = observable_state(&context, file);
            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::ObjectLiteral(
                    SourceObjectLiteralError::InvalidCache {
                        node,
                        type_: Some(type_),
                    }
                )) if node == object && type_ == object_type
            ));
            assert_eq!(observable_state(&context, file), poisoned);
            assert!(!is_type_checked(&context, file));
            assert!(
                context
                    .store_mut_for_test()
                    .set_value_symbol_links(property, expected.clone())
            );
        }
        context.check_source_file(file).unwrap();
        assert_eq!(
            context
                .store()
                .type_node_links(object)
                .and_then(|links| links.resolved_type),
            Some(object_type)
        );
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn unsupported_object_forms_fail_before_writes() {
        let cases = [
            (
                r#"const property: string = "ok"; const value: any = { property };"#,
                SourceSyntaxRole::ObjectProperty,
            ),
            (
                "const value: any = { ...{ property: 1 } };",
                SourceSyntaxRole::ObjectLiteral,
            ),
            (
                "const value: any = { method(): string { return ''; } };",
                SourceSyntaxRole::ObjectProperty,
            ),
            (
                "const value: any = { ['property']: 1 };",
                SourceSyntaxRole::ObjectProperty,
            ),
        ];
        for (index, (text, role)) in cases.into_iter().enumerate() {
            let source = parsed(text);
            let file = FileId::new(72 + u32::try_from(index).unwrap());
            let mut context = context_with_module_state(
                &[(file, &source)],
                CanonicalModuleState::External,
                CanonicalCheckerOptions::default(),
            );
            let before = observable_state(&context, file);

            let result = context.check_source_file(file);
            assert!(
                matches!(
                    result,
                    Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Syntax {
                            role: actual,
                            ..
                        }
                    )) if actual == role
                ),
                "source: {text}; result: {result:?}"
            );
            assert_eq!(observable_state(&context, file), before, "source: {text}");
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn expression_literals_use_fresh_booleans_and_null_widening_identity() {
        let source =
            parsed("const yes: any = true; const no: any = false; const none: any = null;");
        let file = FileId::new(43);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let (true_type, regular_true, false_type, regular_false, null_type, null_widening) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.true_type,
                bootstrap.regular_true_type,
                bootstrap.false_type,
                bootstrap.regular_false_type,
                bootstrap.null_type,
                bootstrap.null_widening_type,
            )
        };

        let store = context.store_mut_for_test();
        let yes = variable_initializer(&source, file, "yes");
        let no = variable_initializer(&source, file, "no");
        let none = variable_initializer(&source, file, "none");
        assert_eq!(
            expression_type(
                store,
                &PlannedExpression::new(yes, PlannedExpressionKind::Boolean(true)),
                &PreparedExpression::Literal(LiteralTreatment::Fresh),
            ),
            Ok(true_type)
        );
        assert_eq!(
            expression_type(
                store,
                &PlannedExpression::new(no, PlannedExpressionKind::Boolean(false)),
                &PreparedExpression::Literal(LiteralTreatment::Fresh),
            ),
            Ok(false_type)
        );
        assert_eq!(
            expression_type(
                store,
                &PlannedExpression::new(none, PlannedExpressionKind::Null),
                &PreparedExpression::Literal(LiteralTreatment::Identity),
            ),
            Ok(null_widening)
        );
        assert_ne!(true_type, regular_true);
        assert_ne!(false_type, regular_false);
        assert_ne!(null_widening, null_type);
    }

    #[test]
    fn alias_cycle_diagnostic_is_staged_then_committed_with_source_marker() {
        let source = parsed(r#"type A = A; const value: string = "ok";"#);
        let file = FileId::new(44);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].diagnostic.code(), 2456);
        assert_eq!(diagnostics[0].diagnostic.arguments, ["A"]);
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn later_unsupported_statement_rejects_the_whole_plan_without_writes() {
        let source = parsed(concat!(
            "type A = A; ",
            r#"const value: string = "ok"; "#,
            "if (true) {}",
        ));
        let file = FileId::new(45);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let before = observable_state(&context, file);

        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Syntax {
                    role: SourceSyntaxRole::Statement,
                    ..
                }
            ))
        ));

        assert_eq!(observable_state(&context, file), before);
    }

    #[test]
    fn malformed_literal_cache_is_atomic_and_can_be_repaired_and_retried() {
        let source = parsed(r#"const value: string = "bad";"#);
        let file = FileId::new(46);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let (regular, fresh) = {
            let store = context.store_mut_for_test();
            let regular = store.regular_string_literal_type("bad".into()).unwrap();
            let fresh = store.fresh_type_of_literal_type(regular).unwrap();
            assert!(store.set_literal_links(regular, Some(regular), regular));
            (regular, fresh)
        };
        let before = observable_state(&context, file);

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::InvalidCachedLiteral(regular)
            ))
        );
        assert_eq!(observable_state(&context, file), before);
        assert!(!is_type_checked(&context, file));
        assert!(context.diagnostics().is_empty());

        assert!(
            context
                .store_mut_for_test()
                .set_literal_links(regular, Some(fresh), regular)
        );
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn retry_preserves_cycle_diagnostic_sealed_before_later_display_failure() {
        let source = parsed(concat!(
            "type A = A; const first: A = 1; ",
            "const later: string = true;",
        ));
        let file = FileId::new(52);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let (fresh_true, regular_true) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.true_type, bootstrap.regular_true_type)
        };
        assert!(context.store_mut_for_test().set_literal_links(
            fresh_true,
            Some(fresh_true),
            fresh_true,
        ));

        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::InvalidCachedLiteral(id)
            )) if id == regular_true
        ));
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));

        assert!(context.store_mut_for_test().set_literal_links(
            fresh_true,
            Some(fresh_true),
            regular_true,
        ));
        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2456, 2322]
        );
        assert!(is_type_checked(&context, file));
        context.check_source_file(file).unwrap();
        assert_eq!(context.diagnostics().len(), 2);
    }

    #[test]
    fn cross_source_retry_diagnostic_publishes_when_its_owner_succeeds() {
        let first = parsed("const first: B = 1; const blocked: string = true;");
        let second = parsed("type B = B;");
        let first_file = FileId::new(53);
        let second_file = FileId::new(54);
        let mut context = context(
            &[(first_file, &first), (second_file, &second)],
            CanonicalCheckerOptions::default(),
        );
        let (fresh_true, regular_true) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.true_type, bootstrap.regular_true_type)
        };
        assert!(context.store_mut_for_test().set_literal_links(
            fresh_true,
            Some(fresh_true),
            fresh_true,
        ));

        let result = context.check_source_file(first_file);
        assert!(
            matches!(
                result,
                Err(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::InvalidCachedLiteral(id)
                )) if id == regular_true
            ),
            "unexpected first-file result: {result:?}"
        );
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, first_file));
        assert!(!is_type_checked(&context, second_file));

        context.check_source_file(second_file).unwrap();
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].diagnostic.code(), 2456);
        assert_eq!(diagnostics[0].diagnostic.arguments, ["B"]);
        assert_eq!(diagnostics[0].node.map(|node| node.file), Some(second_file));
        assert!(is_type_checked(&context, second_file));

        assert!(context.check_source_file(first_file).is_err());
        assert_eq!(context.diagnostics().len(), 1);
    }

    #[test]
    fn semantic_diagnostic_is_idempotent_after_successful_publication() {
        let source = parsed(r#"const value: number = "bad";"#);
        let file = FileId::new(47);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();
        let after_first = observable_state(&context, file);
        assert_eq!(context.diagnostics().len(), 1);
        context.check_source_file(file).unwrap();

        assert_eq!(observable_state(&context, file), after_first);
        assert_eq!(context.diagnostics().len(), 1);
    }

    #[test]
    fn foreign_file_and_stale_or_malformed_source_provenance_are_typed() {
        let source = parsed(r#"const value: string = "ok";"#);
        let file = FileId::new(48);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let foreign = FileId::new(1_048);
        assert_eq!(
            context.check_source_file(foreign),
            Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingFile(foreign)
            ))
        );

        let mut malformed = parsed(r#"const value: string = "ok";"#);
        let malformed_file = FileId::new(49);
        let bindings = completed_bindings(&[(malformed_file, &malformed)]);
        let (symbols, mut files) = bindings.try_into_parts().unwrap();
        let bound = files.remove(&malformed_file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        let source = store
            .register_source_file(&malformed.arena, malformed.source_file, malformed_file)
            .unwrap();
        let name = variable_name(&malformed, malformed_file, "value").node;
        malformed.arena.get_mut(name).unwrap().parent = None;

        let stale = DeclaredTypeHost::new_after_global_merge(
            [(&malformed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap_err();
        assert!(matches!(
            SourceCheckError::from(DeclaredTypeError::from(stale)),
            SourceCheckError::DeclaredType(DeclaredTypeError::Host(
                DeclaredTypeHostError::ArenaRevisionMismatch { .. }
            ))
        ));

        assert!(matches!(
            SourcePlanner::new(&malformed.arena, &bound, source).finish(),
            Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::InvalidParent { node, .. }
            )) if node.node == name
        ));
    }

    #[test]
    fn strict_and_loose_null_checking_follow_null_widening_relation() {
        let source = parsed("const value: string = null;");
        let file = FileId::new(50);
        let mut loose = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let mut strict = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );

        loose.check_source_file(file).unwrap();
        strict.check_source_file(file).unwrap();

        assert!(loose.diagnostics().is_empty());
        assert_eq!(strict.diagnostics().len(), 1);
        assert_eq!(strict.diagnostics().as_slice()[0].diagnostic.code(), 2322);
        assert_eq!(
            strict.diagnostics().as_slice()[0]
                .diagnostic
                .render()
                .unwrap(),
            "Type 'null' is not assignable to type 'string'."
        );
        assert!(is_type_checked(&loose, file));
        assert!(is_type_checked(&strict, file));
    }

    #[test]
    fn source_assignments_use_retained_strict_function_types() {
        let source = parsed(concat!(
            "const narrow: (input: 'only') => void = null as any; ",
            "const value: (input: string) => void = narrow;",
        ));
        let file = FileId::new(55);
        let mut strict = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                strict_function_types: true,
                ..CanonicalCheckerOptions::default()
            },
        );
        let mut bivariant = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                strict_function_types: false,
                ..CanonicalCheckerOptions::default()
            },
        );

        strict.check_source_file(file).unwrap();
        bivariant.check_source_file(file).unwrap();

        assert_eq!(strict.diagnostics().len(), 1);
        assert_eq!(strict.diagnostics().as_slice()[0].diagnostic.code(), 2322);
        assert_eq!(
            strict.diagnostics().as_slice()[0]
                .diagnostic
                .render()
                .unwrap(),
            "Type '(input: \"only\") => void' is not assignable to type '(input: string) => void'."
        );
        assert!(bivariant.diagnostics().is_empty());
        assert!(is_type_checked(&strict, file));
        assert!(is_type_checked(&bivariant, file));
        strict.check_source_file(file).unwrap();
        bivariant.check_source_file(file).unwrap();
        assert_eq!(strict.diagnostics().len(), 1);
        assert!(bivariant.diagnostics().is_empty());
    }

    #[test]
    fn source_functions_are_hoisted_and_reuse_their_cold_identity_on_retry() {
        let source = parsed(concat!(
            "const before: (input: string) => number = fn; ",
            "function fn(input: string): number { return 1; } ",
            "const after = fn;",
        ));
        let file = FileId::new(301);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let owner = function_symbol(&context, &source, file, "fn");
        let callable = context
            .store()
            .source_callable_type_for_owner(owner)
            .unwrap();
        assert_eq!(
            context
                .store()
                .value_symbol_links(owner)
                .and_then(|links| links.resolved_type),
            Some(callable)
        );
        let annotated_before = variable_value_type(&context, &source, file, "before");
        assert_ne!(annotated_before, callable);
        assert_eq!(
            context
                .store_mut_for_test()
                .is_type_assignable_to_with_strict_function_types(
                    callable,
                    annotated_before,
                    false,
                ),
            Ok(true)
        );
        assert_eq!(
            variable_value_type(&context, &source, file, "after"),
            callable
        );
        let reads = identifier_expressions(&source, file, "fn");
        assert_eq!(reads.len(), 2);
        assert!(reads.iter().all(|read| {
            context
                .store()
                .symbol_node_links(*read)
                .and_then(|links| links.resolved_symbol)
                == Some(owner)
        }));
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            context.store().source_callable_type_for_owner(owner),
            Some(callable)
        );
        assert_eq!(observable_state(&context, file), warm);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn exported_source_functions_keep_local_and_owner_symbols_distinct() {
        let source = parsed("export function fn(value: string): void {} const copy = fn;");
        let file = FileId::new(302);
        let mut context = context_with_module_state(
            &[(file, &source)],
            CanonicalModuleState::External,
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(file).unwrap();

        let declaration = function_declaration(&source, file, "fn");
        let (_, bound) = context.file(file).unwrap();
        let owner = bound.symbol(declaration).unwrap();
        let local = bound.local_symbol(declaration).unwrap();
        let owner_record = context.store().symbol(owner).unwrap();
        let local_record = context.store().symbol(local).unwrap();
        assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
        assert_eq!(local_record.flags(), SymbolFlags::EXPORT_VALUE);
        assert_eq!(local_record.declarations(), Some(&[declaration][..]));
        assert_eq!(local_record.value_declaration(), None);
        assert_eq!(local_record.export_symbol(), Some(owner));
        assert!(owner_record.parent().is_some());
        let callable = context
            .store()
            .source_callable_type_for_owner(owner)
            .unwrap();
        assert_eq!(
            context
                .store()
                .value_symbol_links(owner)
                .and_then(|links| links.resolved_type),
            Some(callable)
        );
        assert!(context.store().value_symbol_links(local).is_none());
        assert_eq!(
            variable_value_type(&context, &source, file, "copy"),
            callable
        );
        let reads = identifier_expressions(&source, file, "fn");
        let [read] = reads.as_slice() else {
            panic!("expected one exported function read")
        };
        assert_eq!(
            context
                .store()
                .symbol_node_links(*read)
                .and_then(|links| links.resolved_symbol),
            Some(local)
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn optional_source_function_parameters_publish_strict_value_types() {
        let source = parsed("function maybe(value?: string): void {}");
        let file = FileId::new(303);
        let mut context = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );

        context.check_source_file(file).unwrap();

        let owner = function_symbol(&context, &source, file, "maybe");
        let callable = context
            .store()
            .source_callable_type_for_owner(owner)
            .unwrap();
        let provenance = context
            .store()
            .source_callable_provenance(callable)
            .unwrap();
        let signature = context.store().signature(provenance.signature).unwrap();
        assert_eq!(signature.min_argument_count(), 0);
        let [parameter] = signature.parameters() else {
            panic!("expected one optional parameter")
        };
        let parameter_type = context
            .store()
            .value_symbol_links(*parameter)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let TypeData::Union(union) = context.store().type_payload(parameter_type).unwrap().data()
        else {
            panic!("strict optional parameter must include undefined")
        };
        assert!(
            union.union.types.contains(
                &context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .undefined_type
            )
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn unsupported_source_function_plans_are_atomic_and_missing_names_recover() {
        let source = parsed(concat!(
            "function ready(): void {} ",
            "function generic<T>(value: T) { return value; }",
        ));
        let file = FileId::new(304);
        let mut blocked = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let ready = function_symbol(&blocked, &source, file, "ready");
        let before = observable_state(&blocked, file);

        assert!(matches!(
            blocked.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::Callable(_))
            ))
        ));
        assert_eq!(observable_state(&blocked, file), before);
        assert!(blocked.store().value_symbol_links(ready).is_none());
        assert!(
            blocked
                .store()
                .source_callable_type_for_owner(ready)
                .is_none()
        );
        assert!(!is_type_checked(&blocked, file));

        let unresolved = parsed("const value = missing;");
        let unresolved_file = FileId::new(305);
        let mut unresolved_context = context(
            &[(unresolved_file, &unresolved)],
            CanonicalCheckerOptions::default(),
        );
        let read = variable_initializer(&unresolved, unresolved_file, "value");
        let (error_type, unknown_symbol) = {
            let bootstrap = unresolved_context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.error_type, bootstrap.unknown_symbol)
        };

        unresolved_context
            .check_source_file(unresolved_file)
            .unwrap();

        let [diagnostic] = unresolved_context.diagnostics().as_slice() else {
            panic!("expected one missing-name diagnostic")
        };
        assert_eq!(diagnostic.node, Some(read));
        assert_eq!(diagnostic.diagnostic.code(), 2304);
        assert_eq!(diagnostic.diagnostic.arguments, ["missing"]);
        assert_eq!(resolved_node_type(&unresolved_context, read), error_type);
        assert_eq!(
            variable_value_type(&unresolved_context, &unresolved, unresolved_file, "value"),
            error_type
        );
        assert_eq!(
            unresolved_context
                .store()
                .symbol_node_links(read)
                .and_then(|links| links.resolved_symbol),
            Some(unknown_symbol)
        );
        assert!(is_type_checked(&unresolved_context, unresolved_file));

        let warm = observable_state(&unresolved_context, unresolved_file);
        mark_source_unchecked(&mut unresolved_context, unresolved_file);
        unresolved_context
            .check_source_file(unresolved_file)
            .unwrap();
        assert_eq!(observable_state(&unresolved_context, unresolved_file), warm);
    }

    #[test]
    fn source_function_returns_and_strict_relations_use_callable_semantics() {
        let bad_return = parsed("function bad(): string { return 1; }");
        let return_file = FileId::new(306);
        let mut return_context = context(
            &[(return_file, &bad_return)],
            CanonicalCheckerOptions::default(),
        );

        return_context.check_source_file(return_file).unwrap();

        let [diagnostic] = return_context.diagnostics().as_slice() else {
            panic!("expected one return diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.node,
            Some(function_return_statement(&bad_return, return_file, "bad"))
        );
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert!(is_type_checked(&return_context, return_file));
        return_context.check_source_file(return_file).unwrap();
        assert_eq!(return_context.diagnostics().len(), 1);

        let relation = parsed(concat!(
            "function narrow(input: 'only'): void {} ",
            "const value: (input: string) => void = narrow;",
        ));
        let relation_file = FileId::new(307);
        let mut strict = context(
            &[(relation_file, &relation)],
            CanonicalCheckerOptions {
                strict_function_types: true,
                ..CanonicalCheckerOptions::default()
            },
        );
        let mut bivariant = context(
            &[(relation_file, &relation)],
            CanonicalCheckerOptions {
                strict_function_types: false,
                ..CanonicalCheckerOptions::default()
            },
        );

        strict.check_source_file(relation_file).unwrap();
        bivariant.check_source_file(relation_file).unwrap();

        let owner = function_symbol(&strict, &relation, relation_file, "narrow");
        let callable = strict
            .store()
            .source_callable_type_for_owner(owner)
            .unwrap();
        let signature = strict
            .store()
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        assert!(
            strict
                .store()
                .signature(signature)
                .unwrap()
                .resolved_return_type()
                .is_some()
        );
        assert_eq!(strict.diagnostics().len(), 1);
        assert_eq!(strict.diagnostics().as_slice()[0].diagnostic.code(), 2322);
        assert_eq!(
            strict.diagnostics().as_slice()[0]
                .diagnostic
                .render()
                .unwrap(),
            "Type '(input: \"only\") => void' is not assignable to type '(input: string) => void'."
        );
        assert!(bivariant.diagnostics().is_empty());
        assert!(is_type_checked(&strict, relation_file));
        assert!(is_type_checked(&bivariant, relation_file));
    }

    #[test]
    fn direct_source_arrows_infer_exact_callable_identity_and_retry_warm() {
        let source = parsed(concat!(
            "const f = (value: string, optional?: number): string => value; ",
            "const forward = (): string => later; ",
            "const later = 'ok'; ",
            "const copy = f;",
        ));
        let file = FileId::new(308);
        let mut context = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );

        context.check_source_file(file).unwrap();

        let variable = variable_symbol(&context, &source, file, "f");
        let declaration = variable_declaration(&source, file, "f");
        let arrow = variable_initializer(&source, file, "f");
        let (_, bound) = context.file(file).unwrap();
        let owner = bound.symbol(arrow).unwrap();
        assert_ne!(variable, owner);
        assert_eq!(bound.symbol(declaration), Some(variable));
        let callable = variable_value_type(&context, &source, file, "f");
        assert_eq!(
            variable_value_type(&context, &source, file, "copy"),
            callable
        );
        assert_eq!(
            context.store().source_callable_type_for_owner(owner),
            Some(callable)
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(owner)
                .and_then(|links| links.resolved_type),
            Some(callable)
        );
        let provenance = context
            .store()
            .source_callable_provenance(callable)
            .unwrap();
        assert_eq!(provenance.declaration, arrow);
        assert_eq!(provenance.owner_symbol, owner);
        let signature = context.store().signature(provenance.signature).unwrap();
        assert!(signature.resolved_return_type().is_some());
        let [value, optional] = signature.parameters() else {
            panic!("expected two arrow parameters")
        };
        assert!([*value, *optional].iter().all(|parameter| {
            context
                .store()
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type)
                .is_some()
        }));
        let value_reads = identifier_expressions(&source, file, "value");
        let [value_read] = value_reads.as_slice() else {
            panic!("expected one arrow parameter read")
        };
        assert_eq!(
            context
                .store()
                .symbol_node_links(*value_read)
                .and_then(|links| links.resolved_symbol),
            Some(*value)
        );
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
        assert_eq!(variable_value_type(&context, &source, file, "f"), callable);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn contextual_optional_and_exhausted_rest_arrow_matches_the_pinned_oracle() {
        let source = parsed("const f: () => void = (a?, ...b) => {};");
        let file = FileId::new(315);
        let mut context = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                no_implicit_any: true,
                ..CanonicalCheckerOptions::default()
            },
        );

        context.check_source_file(file).unwrap();

        let arrow = variable_initializer(&source, file, "f");
        let NodeData::ArrowFunction(arrow_data) = &source.arena.get(arrow.node).unwrap().data
        else {
            panic!("expected arrow initializer")
        };
        let [a_id, b_id] = arrow_data.parameters.nodes.as_slice() else {
            panic!("expected optional and rest parameters")
        };
        let a = NodeRef::new(source.arena.id(), file, *a_id);
        let b = NodeRef::new(source.arena.id(), file, *b_id);
        let (_, bound) = context.file(file).unwrap();
        let owner = bound.symbol(arrow).unwrap();
        let variable = variable_symbol(&context, &source, file, "f");
        assert_ne!(owner, variable);

        let target = variable_value_type(&context, &source, file, "f");
        let callable = context
            .store()
            .source_callable_type_for_owner(owner)
            .unwrap();
        assert_ne!(target, callable);
        assert_eq!(resolved_node_type(&context, arrow), callable);
        assert_eq!(context.type_to_string(target).unwrap(), "() => void");
        assert_eq!(
            context.type_to_string(callable).unwrap(),
            "(a?: any) => void"
        );

        let provenance = context
            .store()
            .source_callable_provenance(callable)
            .unwrap();
        assert_eq!(provenance.contextual_target, Some(target));
        assert_eq!(provenance.contextual_variable, Some(variable));
        let signature = context.store().signature(provenance.signature).unwrap();
        assert_eq!(signature.min_argument_count(), 0);
        assert!(signature.has_rest_parameter());
        assert_eq!(
            signature.resolved_return_type(),
            Some(context.store().intrinsic_bootstrap().unwrap().void_type)
        );
        let [a_symbol, b_symbol] = signature.parameters() else {
            panic!("expected retained optional and rest parameter symbols")
        };
        assert_eq!(bound.symbol(a), Some(*a_symbol));
        assert_eq!(bound.symbol(b), Some(*b_symbol));
        assert_eq!(
            context
                .store()
                .value_symbol_links(*a_symbol)
                .and_then(|links| links.resolved_type),
            Some(context.store().intrinsic_bootstrap().unwrap().any_type)
        );
        let empty_tuple = context
            .store()
            .value_symbol_links(*b_symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(context.type_to_string(empty_tuple).unwrap(), "[]");
        assert_eq!(
            context
                .store()
                .validate_canonical_empty_tuple_type(empty_tuple),
            Ok(())
        );

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected only TS7006 for the non-contextual optional parameter")
        };
        assert_eq!(diagnostic.node, Some(a));
        assert_eq!(diagnostic.diagnostic.code(), 7006);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Parameter 'a' implicitly has an 'any' type."
        );
        assert!(is_type_checked(&context, file));

        let warm = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
        assert_eq!(context.diagnostics().len(), 1);
        assert_eq!(variable_value_type(&context, &source, file, "f"), target);
        assert_eq!(resolved_node_type(&context, arrow), callable);
    }

    #[test]
    fn linear_function_bodies_publish_locals_and_preserve_return_types() {
        let source = parsed(concat!(
            "function inferred() { var hidden = 1; } ",
            "function selected(input: number): number { ",
            "const first = input; var second: number = first; return second; ",
            "} ",
            "const result: number = selected(1);",
        ));
        let file = FileId::new(8_270);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let hidden = variable_symbol(&context, &source, file, "hidden");

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert!(
            context
                .store()
                .value_symbol_links(hidden)
                .and_then(|links| links.resolved_type)
                .is_some()
        );
        assert_eq!(
            variable_value_type(&context, &source, file, "result"),
            context.store().intrinsic_bootstrap().unwrap().number_type
        );
        let warm = observable_state(&context, file);
        context.recheck_source_file(file).unwrap();
        assert_eq!(observable_state(&context, file), warm);
    }

    #[test]
    fn unannotated_function_parameters_report_implicit_any_only_when_enabled() {
        for (index, enabled) in [false, true].into_iter().enumerate() {
            let source = parsed("function read(value) { return value; }");
            let file = FileId::new(8_271 + u32::try_from(index).unwrap());
            let mut context = context(
                &[(file, &source)],
                CanonicalCheckerOptions {
                    no_implicit_any: enabled,
                    ..CanonicalCheckerOptions::default()
                },
            );

            context.check_source_file(file).unwrap();

            if enabled {
                let [diagnostic] = context.diagnostics().as_slice() else {
                    panic!("expected one implicit-any parameter diagnostic")
                };
                assert_eq!(diagnostic.diagnostic.code(), 7006);
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    "Parameter 'value' implicitly has an 'any' type."
                );
            } else {
                assert!(context.diagnostics().is_empty());
            }
        }
    }

    #[test]
    fn contextual_parameter_origins_control_implicit_any_diagnostics() {
        for (file, text, no_implicit_any, expected_diagnostics) in [
            (
                FileId::new(316),
                "const f: () => void = (a?) => {};",
                false,
                0,
            ),
            (
                FileId::new(317),
                "const f: (a?: any) => void = (a) => {};",
                true,
                0,
            ),
            (
                FileId::new(318),
                "const f: (a: number) => void = (a) => {};",
                true,
                0,
            ),
        ] {
            let source = parsed(text);
            let mut context = context(
                &[(file, &source)],
                CanonicalCheckerOptions {
                    intrinsic: IntrinsicBootstrapOptions {
                        strict_null_checks: true,
                        exact_optional_property_types: false,
                    },
                    no_implicit_any,
                    ..CanonicalCheckerOptions::default()
                },
            );

            context.check_source_file(file).unwrap();

            assert_eq!(context.diagnostics().len(), expected_diagnostics);
            let arrow = variable_initializer(&source, file, "f");
            let (_, bound) = context.file(file).unwrap();
            let owner = bound.symbol(arrow).unwrap();
            let callable = context
                .store()
                .source_callable_type_for_owner(owner)
                .unwrap();
            assert!(context.type_to_string(callable).unwrap().contains('a'));
            assert!(is_type_checked(&context, file));
        }
    }

    #[test]
    fn contextual_optional_array_target_replays_from_warm_caches() {
        let library = parsed("interface Array<T> {}");
        let source = parsed("const f: (a?: string[]) => void = (a) => {};");
        let library_file = FileId::new(330);
        let file = FileId::new(325);
        let mut context = context(
            &[(library_file, &library), (file, &source)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );

        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let warm = observable_state(&context, file);

        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();

        assert_eq!(observable_state(&context, file), warm);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn contextual_arrow_shape_failures_preflight_the_whole_file_atomically() {
        for (file, text) in [
            (
                FileId::new(319),
                concat!(
                    "const ready: () => void = () => {}; ",
                    "const bad: () => void = (required) => {};",
                ),
            ),
            (
                FileId::new(320),
                concat!(
                    "const ready: () => void = () => {}; ",
                    "const bad: () => undefined = () => {};",
                ),
            ),
            (
                FileId::new(323),
                concat!(
                    "const ready: () => void = () => {}; ",
                    "const bad: (this: unknown) => void = () => {};",
                ),
            ),
            (
                FileId::new(324),
                concat!(
                    "const ready: () => void = () => {}; ",
                    "const bad: (value) => void = () => {};",
                ),
            ),
        ] {
            let source = parsed(text);
            let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
            let ready = variable_initializer(&source, file, "ready");
            let (_, bound) = context.file(file).unwrap();
            let ready_owner = bound.symbol(ready).unwrap();
            let before = observable_state(&context, file);

            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Arrow(_)
                ))
            ));
            assert_eq!(observable_state(&context, file), before);
            assert!(
                context
                    .store()
                    .source_callable_type_for_owner(ready_owner)
                    .is_none()
            );
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn contextual_arrow_sparse_cache_poison_precedes_source_publication() {
        let expression_poison = parsed("const f: () => void = (a?) => {};");
        let expression_file = FileId::new(321);
        let mut expression_context = context(
            &[(expression_file, &expression_poison)],
            CanonicalCheckerOptions::default(),
        );
        let arrow = variable_initializer(&expression_poison, expression_file, "f");
        let (_, bound) = expression_context.file(expression_file).unwrap();
        let owner = bound.symbol(arrow).unwrap();
        let number = expression_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        assert!(expression_context.store_mut_for_test().set_type_node_links(
            arrow,
            TypeNodeLinks {
                outer_type_parameters: Some(vec![number]),
                ..TypeNodeLinks::default()
            },
        ));

        assert_eq!(
            expression_context.check_source_file(expression_file),
            Err(SourceCheckError::Arrow(arrow)),
        );
        assert!(
            expression_context
                .store()
                .source_callable_type_for_owner(owner)
                .is_none()
        );
        assert!(
            expression_context
                .store()
                .value_symbol_links(owner)
                .is_none()
        );
        assert!(expression_context.store().signature_links(arrow).is_none());
        assert!(!is_type_checked(&expression_context, expression_file));

        let variable_poison = parsed("const f: () => void = (a?) => {};");
        let variable_file = FileId::new(322);
        let mut variable_context = context(
            &[(variable_file, &variable_poison)],
            CanonicalCheckerOptions::default(),
        );
        let arrow = variable_initializer(&variable_poison, variable_file, "f");
        let variable = variable_symbol(&variable_context, &variable_poison, variable_file, "f");
        let (_, bound) = variable_context.file(variable_file).unwrap();
        let owner = bound.symbol(arrow).unwrap();
        let number = variable_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        assert!(
            variable_context
                .store_mut_for_test()
                .set_value_symbol_links(
                    variable,
                    ValueSymbolLinks {
                        resolved_type: Some(number),
                        ..ValueSymbolLinks::default()
                    },
                )
        );

        assert!(matches!(
            variable_context.check_source_file(variable_file),
            Err(SourceCheckError::Variable(_))
        ));
        assert!(
            variable_context
                .store()
                .source_callable_type_for_owner(owner)
                .is_none()
        );
        assert!(variable_context.store().value_symbol_links(owner).is_none());
        assert!(variable_context.store().signature_links(arrow).is_none());
        assert!(!is_type_checked(&variable_context, variable_file));
    }

    #[test]
    fn later_contextual_arrow_cache_poison_preflights_before_earlier_publication() {
        for (file, poison) in [
            (FileId::new(326), 0_u8),
            (FileId::new(327), 1_u8),
            (FileId::new(328), 2_u8),
            (FileId::new(329), 3_u8),
        ] {
            let source = parsed(concat!(
                "const ready: () => void = () => {}; ",
                "const bad: () => void = (value?) => {};",
            ));
            let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
            let ready = variable_initializer(&source, file, "ready");
            let bad = variable_initializer(&source, file, "bad");
            let NodeData::ArrowFunction(bad_data) = &source.arena.get(bad.node).unwrap().data
            else {
                panic!("expected bad arrow")
            };
            let [parameter_id] = bad_data.parameters.nodes.as_slice() else {
                panic!("expected one bad parameter")
            };
            let parameter = NodeRef::new(source.arena.id(), file, *parameter_id);
            let (_, bound) = context.file(file).unwrap();
            let ready_owner = bound.symbol(ready).unwrap();
            let bad_owner = bound.symbol(bad).unwrap();
            let bad_parameter = bound.symbol(parameter).unwrap();
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;

            match poison {
                0 => assert!(context.store_mut_for_test().set_type_node_links(
                    bad,
                    TypeNodeLinks {
                        outer_type_parameters: Some(vec![number]),
                        ..TypeNodeLinks::default()
                    },
                )),
                1 => assert!(context.store_mut_for_test().set_value_symbol_links(
                    bad_owner,
                    ValueSymbolLinks {
                        resolved_type: Some(number),
                        ..ValueSymbolLinks::default()
                    },
                )),
                2 => assert!(context.store_mut_for_test().set_value_symbol_links(
                    bad_parameter,
                    ValueSymbolLinks {
                        resolved_type: Some(number),
                        ..ValueSymbolLinks::default()
                    },
                )),
                3 => assert!(context.store_mut_for_test().set_signature_links(
                    bad,
                    crate::semantic::links::SignatureLinks {
                        resolved_signature:
                            crate::semantic::links::ResolvedSignatureState::Resolving,
                        ..crate::semantic::links::SignatureLinks::default()
                    },
                )),
                _ => unreachable!(),
            }
            let before = observable_state(&context, file);

            assert!(context.check_source_file(file).is_err());

            assert_eq!(observable_state(&context, file), before);
            assert!(
                context
                    .store()
                    .source_callable_type_for_owner(ready_owner)
                    .is_none()
            );
            assert!(context.store().value_symbol_links(ready_owner).is_none());
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn source_arrow_mutable_captures_use_their_declared_entry_types() {
        for (file, text) in [
            (
                FileId::new(312),
                "let x: string | number = 1; const f = (): string => x;",
            ),
            (
                FileId::new(313),
                concat!(
                    "var x: string | number = 1; ",
                    "const f = (): string => x; ",
                    "x = 'ok';",
                ),
            ),
        ] {
            let source = parsed(text);
            let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

            context.check_source_file(file).unwrap();

            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("expected one mutable capture diagnostic")
            };
            assert_eq!(diagnostic.node, Some(arrow_body(&source, file, "f")));
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'string | number' is not assignable to type 'string'."
            );
            assert!(is_type_checked(&context, file));
        }
    }

    #[test]
    fn deferred_arrow_parameters_remain_body_local() {
        let source = parsed(concat!(
            "const text = (value: string): string => value; ",
            "const numeric = (value: number): number => value;",
        ));
        let file = FileId::new(314);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let (_, bound) = context.file(file).unwrap();
        let mut parameters = Vec::new();
        for name in ["text", "numeric"] {
            let arrow = variable_initializer(&source, file, name);
            let owner = bound.symbol(arrow).unwrap();
            let callable = context
                .store()
                .source_callable_type_for_owner(owner)
                .unwrap();
            let provenance = context
                .store()
                .source_callable_provenance(callable)
                .unwrap();
            let signature = context.store().signature(provenance.signature).unwrap();
            let [parameter] = signature.parameters() else {
                panic!("expected one parameter for {name}")
            };
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(arrow_body(&source, file, name))
                    .and_then(|links| links.resolved_symbol),
                Some(*parameter)
            );
            parameters.push(*parameter);
        }
        assert_ne!(parameters[0], parameters[1]);
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn source_arrow_concise_and_block_returns_report_exact_nodes() {
        let source = parsed(concat!(
            "const concise = (): string => 1; ",
            "const blocked = (): string => { return 2; };",
        ));
        let file = FileId::new(309);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let concise = variable_initializer(&source, file, "concise");
        let NodeData::ArrowFunction(concise_arrow) = &source.arena.get(concise.node).unwrap().data
        else {
            unreachable!()
        };
        let concise_body = NodeRef::new(source.arena.id(), file, concise_arrow.body);
        let blocked_return = arrow_return_statement(&source, file, "blocked");
        assert_eq!(context.diagnostics().len(), 2);
        for node in [concise_body, blocked_return] {
            let diagnostic = context
                .diagnostics()
                .as_slice()
                .iter()
                .find(|diagnostic| diagnostic.node == Some(node))
                .unwrap_or_else(|| panic!("missing arrow return diagnostic at {node:?}"));
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'number' is not assignable to type 'string'."
            );
        }
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn source_arrow_consumers_use_strict_callable_relations() {
        let source = parsed(concat!(
            "const narrow = (input: 'only'): void => {}; ",
            "const value: (input: string) => void = narrow;",
        ));
        let file = FileId::new(310);
        let mut strict = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                strict_function_types: true,
                ..CanonicalCheckerOptions::default()
            },
        );
        let mut bivariant = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                strict_function_types: false,
                ..CanonicalCheckerOptions::default()
            },
        );

        strict.check_source_file(file).unwrap();
        bivariant.check_source_file(file).unwrap();

        let [diagnostic] = strict.diagnostics().as_slice() else {
            panic!("expected one strict arrow relation diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type '(input: \"only\") => void' is not assignable to type '(input: string) => void'."
        );
        assert!(bivariant.diagnostics().is_empty());
        assert!(is_type_checked(&strict, file));
        assert!(is_type_checked(&bivariant, file));
    }

    #[test]
    fn unsupported_source_arrow_keeps_the_complete_plan_atomic() {
        let source = parsed(concat!(
            "const ready = (): void => {}; ",
            "const generic = <T>(value: T): T => value;",
        ));
        let file = FileId::new(311);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let ready = variable_initializer(&source, file, "ready");
        let generic = variable_initializer(&source, file, "generic");
        let (_, bound) = context.file(file).unwrap();
        let ready_owner = bound.symbol(ready).unwrap();
        let before = observable_state(&context, file);

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Arrow(generic)
            ))
        );
        assert_eq!(observable_state(&context, file), before);
        assert!(
            context
                .store()
                .source_callable_type_for_owner(ready_owner)
                .is_none()
        );
        assert!(context.store().value_symbol_links(ready_owner).is_none());
        assert!(!is_type_checked(&context, file));
    }

    #[test]
    fn callable_union_flow_resolves_returns_through_the_source_relation_boundary() {
        let source = parsed(concat!(
            "type A = (input: string) => void; ",
            "type B = (input: string) => number; ",
            "const a: A = null as any; ",
            "const value: A | B = a;",
        ));
        let file = FileId::new(56);
        let mut context = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                strict_function_types: true,
                ..CanonicalCheckerOptions::default()
            },
        );

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn no_error_truncation_controls_long_source_ts2322_arguments() {
        let value = "x".repeat(400);
        let source = parsed(&format!(r#"const value: "other" = "{value}";"#));
        let file = FileId::new(51);
        let mut truncated = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let mut complete = context(
            &[(file, &source)],
            CanonicalCheckerOptions {
                no_error_truncation: true,
                ..CanonicalCheckerOptions::default()
            },
        );

        truncated.check_source_file(file).unwrap();
        complete.check_source_file(file).unwrap();

        let truncated = &truncated.diagnostics().as_slice()[0].diagnostic;
        let complete = &complete.diagnostics().as_slice()[0].diagnostic;
        assert_eq!(truncated.code(), 2322);
        assert_eq!(complete.code(), 2322);
        assert_eq!(truncated.arguments[0], format!("\"{}...", "x".repeat(316)));
        assert_eq!(complete.arguments[0], format!("\"{value}\""));
        assert_eq!(complete.arguments[1], "\"other\"");
    }

    #[test]
    fn unknown_bigint_exponentiation_target_fails_closed_with_stable_safe_memos() {
        let source = parsed("const ready = 1 + 2; const blocked = 1n ** 2n;");
        let file = FileId::new(401);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let ready = variable_initializer(&source, file, "ready");
        let blocked = variable_initializer(&source, file, "blocked");
        let ready_symbol = variable_symbol(&context, &source, file, "ready");
        let blocked_symbol = variable_symbol(&context, &source, file, "blocked");
        let expected = SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::BigIntExponentiationTarget(blocked),
        );

        assert_eq!(context.check_source_file(file), Err(expected));

        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
        assert!(context.store().type_node_links(blocked).is_none());
        assert_eq!(
            resolved_node_type(&context, ready),
            context.store().intrinsic_bootstrap().unwrap().number_type,
        );
        assert!(context.store().value_symbol_links(ready_symbol).is_none());
        assert!(context.store().value_symbol_links(blocked_symbol).is_none());
        let rejected = observable_state(&context, file);

        assert_eq!(context.check_source_file(file), Err(expected));
        assert_eq!(observable_state(&context, file), rejected);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn nested_binary_positions_fail_during_whole_source_preflight() {
        for (file, text) in [
            (FileId::new(402), "const value = [1 + 2];"),
            (FileId::new(403), "const value = { item: 1 + 2 };"),
        ] {
            let source = parsed(text);
            let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
            let binary = source
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::BinaryExpression)
                        .then(|| NodeRef::new(source.arena.id(), file, node))
                })
                .expect("fixture must contain a binary expression");
            let value = variable_symbol(&context, &source, file, "value");
            let before = observable_state(&context, file);

            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Syntax {
                        node: binary,
                        kind: SyntaxKind::BinaryExpression,
                        role: SourceSyntaxRole::BinaryExpression,
                    },
                )),
            );

            assert_eq!(observable_state(&context, file), before, "source: {text}");
            assert!(context.store().type_node_links(binary).is_none());
            assert!(context.store().value_symbol_links(value).is_none());
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn primitive_binary_operator_kind_must_match_its_exact_source_spelling() {
        for (file, text) in [
            (FileId::new(409), "const value = 1 + 2;"),
            (FileId::new(410), "var target: number = 0; target = 1 + 2;"),
            (
                FileId::new(411),
                concat!(
                    "function take(value: number): number { return value; } ",
                    "const value = take(1 + 2);",
                ),
            ),
        ] {
            let mut source = parsed(text);
            let (binary_id, operator_id) = source
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::BinaryExpression(binary) = &record.data else {
                        return None;
                    };
                    (source.arena.get(binary.operator_token)?.kind == SyntaxKind::PlusToken)
                        .then_some((node, binary.operator_token))
                })
                .expect("fixture must contain a primitive plus expression");
            source.arena.get_mut(operator_id).unwrap().kind = SyntaxKind::MinusToken;
            let binary = NodeRef::new(source.arena.id(), file, binary_id);
            let operator = NodeRef::new(source.arena.id(), file, operator_id);
            let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
            let before = observable_state(&context, file);

            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::PrimitiveOperator(operator)),
                "source: {text}",
            );

            assert_eq!(observable_state(&context, file), before, "source: {text}");
            assert!(context.store().type_node_links(binary).is_none());
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }
    }

    #[test]
    fn primitive_binary_root_cache_poison_retains_diagnostics_only_until_repair() {
        let source = parsed("const value = 1 + true;");
        let file = FileId::new(405);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let binary = variable_initializer(&source, file, "value");
        let (poison, expected) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.any_type)
        };
        assert_ne!(poison, expected);
        assert!(context.store_mut_for_test().set_type_node_links(
            binary,
            TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            },
        ));

        let error = SourceCheckError::Assertion(SourceAssertionError::InvalidExpressionCache {
            node: binary,
            cached: Some(poison),
            expected,
        });
        assert_eq!(context.check_source_file(file), Err(error));
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
        let rejected = observable_state(&context, file);
        assert_eq!(context.check_source_file(file), Err(error));
        assert_eq!(observable_state(&context, file), rejected);

        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(binary, TypeNodeLinks::default())
        );
        context.check_source_file(file).unwrap();
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected the retained operator diagnostic")
        };
        assert_eq!(diagnostic.node, Some(binary));
        assert_eq!(diagnostic.diagnostic.code(), 2365);
        assert_eq!(diagnostic.diagnostic.arguments, ["+", "number", "boolean"]);
        assert_eq!(resolved_node_type(&context, binary), expected);
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn missing_names_in_conditionals_report_ts2304_in_source_order() {
        let cases: [(&str, &[&str]); 2] = [
            ("var v = a ? b : c;", &["a", "b", "c"]),
            (
                "var v = a\n  ? b ? d : e\n  : c ? f : g;",
                &["a", "b", "d", "e", "c", "f", "g"],
            ),
        ];

        for (index, (text, expected_names)) in cases.into_iter().enumerate() {
            let source = parsed(text);
            let file = FileId::new(2_190 + u32::try_from(index).unwrap());
            let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
            let (error_type, unknown_symbol) = {
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                (bootstrap.error_type, bootstrap.unknown_symbol)
            };

            context.check_source_file(file).unwrap();

            let diagnostics = context.diagnostics().as_slice();
            assert_eq!(diagnostics.len(), expected_names.len());
            for (diagnostic, expected_name) in diagnostics.iter().zip(expected_names) {
                let reads = identifier_expressions(&source, file, expected_name);
                let [read] = reads.as_slice() else {
                    panic!("expected one missing identifier named {expected_name}")
                };
                assert_eq!(diagnostic.node, Some(*read));
                assert_eq!(diagnostic.diagnostic.code(), 2304);
                assert_eq!(diagnostic.diagnostic.arguments, [*expected_name]);
                assert_eq!(resolved_node_type(&context, *read), error_type);
                assert_eq!(
                    context
                        .store()
                        .symbol_node_links(*read)
                        .and_then(|links| links.resolved_symbol),
                    Some(unknown_symbol)
                );
            }

            for (node, record) in source.arena.iter() {
                if record.kind == SyntaxKind::ConditionalExpression {
                    assert_eq!(
                        resolved_node_type(&context, NodeRef::new(source.arena.id(), file, node)),
                        error_type
                    );
                }
            }
            assert_eq!(
                variable_value_type(&context, &source, file, "v"),
                error_type
            );
            assert_eq!(context.type_to_string(error_type).unwrap(), "any");
            assert!(is_type_checked(&context, file));

            let warm = observable_state(&context, file);
            mark_source_unchecked(&mut context, file);
            context.check_source_file(file).unwrap();
            assert_eq!(observable_state(&context, file), warm);
        }
    }

    #[test]
    fn conditional_forced_replay_revalidates_exact_caches_without_allocating() {
        let source = parsed(concat!(
            "let condition: string = \"\"; ",
            "let text: string = \"x\"; ",
            "let count: number = 1; ",
            "const mixed = condition ? text : count;",
        ));
        let file = FileId::new(412);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let conditional = variable_initializer(&source, file, "mixed");

        context.check_source_file(file).unwrap();
        let result = resolved_node_type(&context, conditional);
        let before = observable_state(&context, file);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();

        assert_eq!(observable_state(&context, file), before);
        assert_eq!(resolved_node_type(&context, conditional), result);
        let NodeData::ConditionalExpression(data) =
            &source.arena.get(conditional.node).unwrap().data
        else {
            unreachable!()
        };
        for child in [data.condition, data.when_true, data.when_false] {
            assert!(
                context
                    .store()
                    .type_node_links(NodeRef::new(source.arena.id(), file, child))
                    .is_none()
            );
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn conditional_wrong_root_cache_fails_before_any_source_publication() {
        let source = parsed(concat!(
            "let condition: boolean = true; ",
            "let text: string = \"x\"; ",
            "let count: number = 1; ",
            "const mixed = condition ? text : count;",
        ));
        let file = FileId::new(413);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let conditional = variable_initializer(&source, file, "mixed");
        let (poison, expected) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_or_number_type)
        };
        assert_ne!(poison, expected);
        assert!(context.store_mut_for_test().set_type_node_links(
            conditional,
            TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            },
        ));
        let before = observable_state(&context, file);
        let error = SourceCheckError::Assertion(SourceAssertionError::InvalidExpressionCache {
            node: conditional,
            cached: Some(poison),
            expected,
        });

        assert_eq!(context.check_source_file(file), Err(error));
        assert_eq!(observable_state(&context, file), before);
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
        for name in ["condition", "text", "count", "mixed"] {
            let symbol = variable_symbol(&context, &source, file, name);
            assert!(context.store().value_symbol_links(symbol).is_none());
        }
        assert_eq!(context.check_source_file(file), Err(error));
        assert_eq!(observable_state(&context, file), before);

        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(conditional, TypeNodeLinks::default())
        );
        context.check_source_file(file).unwrap();
        assert_eq!(resolved_node_type(&context, conditional), expected);
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn primitive_binary_child_cache_poison_is_retry_stable_and_publishes_no_root() {
        let source = parsed("const value = 1 + true;");
        let file = FileId::new(406);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let binary = variable_initializer(&source, file, "value");
        let (left, right) = primitive_binary_parts(&source, file, binary);
        let poison = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            left,
            TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            },
        ));

        let first = context.check_source_file(file).unwrap_err();
        assert!(matches!(
            first,
            SourceCheckError::Assertion(SourceAssertionError::InvalidExpressionCache {
                node,
                cached: Some(cached),
                expected,
            }) if node == left && cached == poison && expected != poison
        ));
        assert!(context.store().type_node_links(binary).is_none());
        assert!(context.store().type_node_links(right).is_none());
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
        let rejected = observable_state(&context, file);

        assert_eq!(context.check_source_file(file), Err(first));
        assert_eq!(observable_state(&context, file), rejected);

        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(left, TypeNodeLinks::default())
        );
        context.check_source_file(file).unwrap();
        assert_eq!(
            resolved_node_type(&context, binary),
            context.store().intrinsic_bootstrap().unwrap().any_type,
        );
        assert_eq!(context.diagnostics().len(), 1);
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn forced_inferred_return_replay_rejects_signature_and_body_cache_poison() {
        let source = parsed("function inferred() { return 1; } const value = inferred();");
        let file = FileId::new(409);
        let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
        let declaration = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let body_expression = source
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ReturnStatement(statement) = &record.data else {
                    return None;
                };
                statement
                    .expression
                    .map(|node| NodeRef::new(source.arena.id(), file, node))
            })
            .unwrap();

        context.check_source_file(file).unwrap();
        let callable = context
            .store()
            .source_callable_type_for_declaration(declaration)
            .unwrap();
        let signature = context
            .store()
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let body_links = context
            .store()
            .type_node_links(body_expression)
            .cloned()
            .unwrap();
        assert_eq!(
            context
                .store()
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(number),
        );

        assert!(
            context
                .store_mut_for_test()
                .set_signature_resolved_return_type(signature, Some(string))
        );
        let source_ref = context.source_file(file).unwrap();
        let mut source_links = context
            .store()
            .source_file_links(source_ref)
            .cloned()
            .unwrap();
        source_links.type_checked = false;
        assert!(
            context
                .store_mut_for_test()
                .set_source_file_links(source_ref, source_links)
        );

        let poisoned_signature_result = context.check_source_file(file);
        assert!(
            matches!(
                poisoned_signature_result,
                Err(SourceCheckError::Call(node))
                    if node == variable_initializer(&source, file, "value")
            ),
            "poisoned inferred return was not rejected: {poisoned_signature_result:?}"
        );
        assert_eq!(
            context
                .store()
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(string),
        );
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));

        assert!(
            context
                .store_mut_for_test()
                .set_signature_resolved_return_type(signature, Some(number))
        );
        assert!(context.store_mut_for_test().set_type_node_links(
            body_expression,
            TypeNodeLinks {
                resolved_type: Some(string),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Assertion(
                SourceAssertionError::InvalidExpressionCache {
                    node,
                    cached: Some(cached),
                    ..
                }
            )) if node == body_expression && cached == string
        ));
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));

        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(body_expression, body_links)
        );
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }

    #[test]
    fn untagged_any_identifiers_and_calls_remain_typed_binary_boundaries() {
        for (file, text) in [
            (
                FileId::new(407),
                "const input: any = 1; const result = input + 2;",
            ),
            (
                FileId::new(408),
                concat!(
                    "function identity(value: any): any { return value; } ",
                    "const result = identity(1) + 2;",
                ),
            ),
        ] {
            let source = parsed(text);
            let mut context = context(&[(file, &source)], CanonicalCheckerOptions::default());
            let binary = variable_initializer(&source, file, "result");
            let (left, _) = primitive_binary_parts(&source, file, binary);
            let kind = source.arena.get(left.node).unwrap().kind;

            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Syntax {
                        node: left,
                        kind,
                        role: SourceSyntaxRole::BinaryOperand,
                    },
                )),
            );

            assert!(context.store().type_node_links(binary).is_none());
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
            let rejected = observable_state(&context, file);
            assert!(context.check_source_file(file).is_err());
            assert_eq!(observable_state(&context, file), rejected);
        }
    }
}
