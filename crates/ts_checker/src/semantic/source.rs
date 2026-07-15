//! Atomic canonical checking for the first source-statement slice.
//!
//! This module deliberately supports only unmodified type aliases and simple
//! interfaces, empty external-module markers, explicitly typed ordinary
//! variable declarations (optionally exported), and direct assignments back
//! to supported `var` declarations. The complete source tree and the complete
//! supported-statement plan are validated before checker state is touched.
//! Unsupported syntax is therefore
//! a typed boundary, never a request to fall back to the legacy checker or to
//! synthesize `any`. Canonical memo caches are not rolled back after a later
//! semantic failure; diagnostics coupled to those caches remain in private
//! source staging until a retry completes and publishes them atomically.

use std::collections::HashSet;

use ts_ast::{FileId, ModifierList, Node, NodeArena, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{BoundFile, SemanticSymbolId};
use ts_core::TextRange;
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_jsnum::{Number, PseudoBigInt};

use super::{
    ArrayTypeError, AssertionLinks, AssignmentInvariant, AssignmentUnsupported,
    CanonicalCheckerDiagnostic, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost,
    DerivedTypeError, RelationUnavailable, SourceFileLinks, SourceFileRef, TypeDisplayUnavailable,
    TypeId,
    bootstrap::{LiteralTypeCacheError, UnionReduction},
    contextual::{
        LiteralTreatment, PreparedExpression, prepare_expression_context_with_global_types,
        prepare_expression_without_context_with_global_types,
    },
    formatter::{
        CanonicalTypeFormatFlags,
        get_type_names_for_assignability_error_with_host_global_types_and_flags,
    },
    type_nodes::{CanonicalTypeQuery, normalize_bigint_literal, normalize_numeric_separators},
    type_records::TypeRecord,
    types::TypeFlags,
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
    ConstAssertion(NodeRef),
    NestedAssertion(NodeRef),
    Assignment(AssignmentUnsupported),
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
}

impl PlannedExpression {
    pub(super) fn new(node: NodeRef, kind: PlannedExpressionKind) -> Self {
        Self { node, kind }
    }

    pub(super) fn unparenthesized(&self) -> &Self {
        let mut expression = self;
        while let PlannedExpressionKind::Parenthesized(inner) = &expression.kind {
            expression = inner;
        }
        expression
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
}

#[derive(Clone, Debug)]
struct PlannedVariable {
    name: NodeRef,
    type_node: NodeRef,
    initializer: PlannedExpression,
}

#[derive(Clone, Debug)]
struct PlannedAssignment {
    expression: NodeRef,
    left: NodeRef,
    target_type_node: NodeRef,
    right: PlannedExpression,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DeferredAssertion {
    node: NodeRef,
    operand_type: TypeId,
    target_type: TypeId,
}

#[derive(Clone, Debug)]
enum PlannedStatement {
    TypeAlias(SemanticSymbolId),
    Interface(SemanticSymbolId),
    ExternalModuleMarker,
    Variables(Vec<PlannedVariable>),
    Assignment(PlannedAssignment),
}

#[derive(Debug)]
struct SourceCheckPlan {
    statements: Vec<PlannedStatement>,
    strings: Vec<String>,
    numbers: Vec<Number>,
    bigints: Vec<PseudoBigInt>,
}

struct SourcePlanner<'arena, 'semantic, 'sources> {
    arena: &'arena NodeArena,
    bound: &'arena BoundFile,
    source: SourceFileRef,
    strings: Vec<String>,
    numbers: Vec<Number>,
    bigints: Vec<PseudoBigInt>,
    semantic: Option<(
        &'semantic CanonicalTypeMapperStore,
        &'semantic DeclaredTypeHost<'sources>,
    )>,
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
            semantic: None,
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
            semantic: Some((store, host)),
        }
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
        let facts = self
            .bound
            .source_facts()
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingSourceFacts(self.source.file()),
            ))?;
        let is_javascript_file = facts.is_javascript_file();
        let is_external_module = facts.is_external_module();
        if is_javascript_file {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::JavaScriptSource(self.source),
            ));
        }

        let source_statements = source_data.statements.nodes.clone();
        let mut statements = Vec::with_capacity(source_statements.len());
        for statement in source_statements {
            let statement = self.reference(statement);
            match self.node(statement)?.kind {
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
                    if node.flags.0 != 0 || alias.modifiers.is_some() {
                        return Err(self.unsupported(
                            statement,
                            node.kind,
                            SourceSyntaxRole::TypeAliasDeclaration,
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
                        || interface.modifiers.is_some()
                    {
                        return Err(self.unsupported(
                            statement,
                            node.kind,
                            SourceSyntaxRole::InterfaceDeclaration,
                        ));
                    }
                    let symbol =
                        self.bound
                            .symbol(statement)
                            .ok_or(SourceCheckError::Provenance(
                                SourceCheckProvenanceError::MissingDeclarationSymbol(statement),
                            ))?;
                    if let Some((store, host)) = self.semantic {
                        super::object_members::plan_interface(store, host, symbol)
                            .map_err(|error| self.interface_plan_error(error))?;
                    }
                    statements.push(PlannedStatement::Interface(symbol));
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
                    self.plan_external_module_marker(statement)?;
                    statements.push(PlannedStatement::ExternalModuleMarker);
                }
                SyntaxKind::VariableStatement => {
                    let declaration_list = {
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
                        variable.declaration_list
                    };
                    statements.push(PlannedStatement::Variables(
                        self.plan_variable_statement(statement, declaration_list)?,
                    ));
                }
                SyntaxKind::ExpressionStatement => {
                    let Some((store, host)) = self.semantic else {
                        return Err(self.unsupported(
                            statement,
                            SyntaxKind::ExpressionStatement,
                            SourceSyntaxRole::Statement,
                        ));
                    };
                    let assignment = super::assignment::plan_simple_assignment(
                        self.arena, self.bound, store, host, statement,
                    )
                    .map_err(Self::assignment_plan_error)?;
                    let right = self.plan_expression(assignment.right)?;
                    statements.push(PlannedStatement::Assignment(PlannedAssignment {
                        expression: assignment.expression,
                        left: assignment.left,
                        target_type_node: assignment.target_type_node,
                        right,
                    }));
                }
                kind => {
                    return Err(self.unsupported(statement, kind, SourceSyntaxRole::Statement));
                }
            }
        }
        Ok(SourceCheckPlan {
            statements,
            strings: self.strings,
            numbers: self.numbers,
            bigints: self.bigints,
        })
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
    ) -> Result<Vec<PlannedVariable>, SourceCheckError> {
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

        let mut variables = Vec::with_capacity(declarations.len());
        for declaration in declarations {
            variables.push(self.plan_variable_declaration(list, self.reference(declaration))?);
        }
        Ok(variables)
    }

    fn plan_variable_declaration(
        &mut self,
        list: NodeRef,
        declaration: NodeRef,
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
        if name_node.kind != SyntaxKind::Identifier
            || !matches!(name_node.data, NodeData::Identifier(_))
            || name_node.parent != Some(declaration.node)
        {
            return Err(self.unsupported(name, name_node.kind, SourceSyntaxRole::VariableName));
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

        let initializer = initializer_id.map(|node| self.reference(node)).ok_or(
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::MissingVariableInitializer(
                declaration,
            )),
        )?;
        if self.node(initializer)?.parent != Some(declaration.node) {
            let kind = self.node(initializer)?.kind;
            return Err(self.unsupported(initializer, kind, SourceSyntaxRole::VariableInitializer));
        }
        let initializer = self.plan_expression(initializer)?;
        Ok(PlannedVariable {
            name,
            type_node,
            initializer,
        })
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
                if identifier.text != "undefined" || !self.is_global_undefined() {
                    return Err(self.unsupported(
                        expression,
                        node.kind,
                        SourceSyntaxRole::VariableInitializer,
                    ));
                }
                Ok(PlannedExpression::new(
                    expression,
                    PlannedExpressionKind::GlobalUndefined,
                ))
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
            SyntaxKind::PrefixUnaryExpression => self.plan_prefix_unary(expression),
            SyntaxKind::TypeAssertionExpression | SyntaxKind::AsExpression => {
                self.plan_assertion(expression)
            }
            SyntaxKind::ArrayLiteralExpression => self.plan_array_literal(expression),
            SyntaxKind::ObjectLiteralExpression => self.plan_object_literal(expression),
            _ => Err(self.unsupported(expression, kind, SourceSyntaxRole::VariableInitializer)),
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
                self.arena
                    .get(node.node)
                    .map_or(SyntaxKind::SourceFile, |record| record.kind),
            ),
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
        if !self.source_spelling_matches(literal, &data.text) {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::InvalidLiteralSpelling(literal),
            ));
        }
        let normalized = normalize_numeric_separators(&data.text).ok_or(
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::InvalidLiteralSpelling(literal)),
        )?;
        let value = ts_jsnum::from_string(&normalized);
        if value.is_nan() {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::InvalidLiteralSpelling(literal),
            ));
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
        if !self.source_spelling_matches(literal, &data.text) {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::InvalidLiteralSpelling(literal),
            ));
        }
        let normalized = normalize_bigint_literal(&data.text).ok_or(
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::InvalidLiteralSpelling(literal)),
        )?;
        Ok(PseudoBigInt::parse_valid(&normalized))
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

#[cfg(test)]
fn expression_type(
    store: &mut CanonicalTypeMapperStore,
    expression: &PlannedExpression,
    prepared: &PreparedExpression,
) -> Result<TypeId, SourceCheckError> {
    Ok(execute_expression_types(store, None, expression, prepared)?.result)
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
}

impl CheckedExpressionTypes {
    fn leaf(raw: TypeId, result: TypeId) -> Self {
        Self {
            raw,
            result,
            shape: CheckedExpressionShape::Leaf,
        }
    }
}

fn execute_expression_types(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    expression: &PlannedExpression,
    prepared: &PreparedExpression,
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
        ) => execute_expression_types(store, global_types, inner, prepared),
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
                let checked =
                    execute_expression_types(store, Some(global_types), element, prepared)?;
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
                let checked = execute_expression_types(store, global_types, property, prepared)?;
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
            })
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

#[allow(clippy::too_many_arguments)]
fn check_expression_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    expression: &PlannedExpression,
    contextual_type: Option<TypeId>,
    deferred: &mut Vec<DeferredAssertion>,
) -> Result<CheckedExpressionTypes, SourceCheckError> {
    match &expression.kind {
        PlannedExpressionKind::Parenthesized(inner) => {
            let types = check_expression_type(
                store,
                host,
                global_types,
                source,
                options,
                diagnostics,
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
                diagnostics,
                operand,
                None,
                deferred,
            )?;
            publish_assertion_operand(store, expression.node, operand_types.result)?;
            let mut assertion_diagnostics = CanonicalCheckerDiagnostics::default();
            let target = CanonicalTypeQuery::new_with_global_types(
                store,
                host,
                global_types,
                options,
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
            let prepared = if let Some(contextual_type) = contextual_type {
                prepare_expression_context_with_global_types(
                    store,
                    host,
                    global_types,
                    expression,
                    contextual_type,
                )?
            } else {
                prepare_expression_without_context_with_global_types(
                    store,
                    host,
                    global_types,
                    expression,
                )?
            };
            execute_expression_types(store, Some(global_types), expression, &prepared)
        }
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
    diagnostics: &mut CanonicalCheckerDiagnostics,
    deferred: &[DeferredAssertion],
) -> Result<(), SourceCheckError> {
    let mut flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
    if options.no_error_truncation {
        flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
    }
    for assertion in deferred {
        let (operand, widened) =
            assertion_operand_types(store, global_types, assertion.operand_type)?;
        if store.is_type_comparable_to_with_global_types(
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
        diagnostic,
        related_information,
    } = diagnostic;
    let entry = destination.lookup_primary_or_issue(node, diagnostic);
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

#[allow(clippy::too_many_arguments)] // Keeps the source execution capabilities explicit.
fn check_planned_assignment(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: SourceFileRef,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    deferred: &mut Vec<DeferredAssertion>,
    target_type_node: NodeRef,
    expression: &PlannedExpression,
    fallback_node: NodeRef,
    assignment_expression: Option<NodeRef>,
) -> Result<(), SourceCheckError> {
    let mut statement_diagnostics = CanonicalCheckerDiagnostics::default();
    let target = CanonicalTypeQuery::new_with_global_types(
        store,
        host,
        global_types,
        options,
        &mut statement_diagnostics,
    )?
    .get_type_from_type_node(target_type_node);
    merge_retry_diagnostics(diagnostics, statement_diagnostics);
    let target = target?;
    if assignment_expression.is_some() {
        publish_expression_type(store, fallback_node, target)?;
    }
    let source_types = check_expression_type(
        store,
        host,
        global_types,
        source,
        options,
        diagnostics,
        expression,
        Some(target),
        deferred,
    )?;
    if let Some(assignment_expression) = assignment_expression {
        publish_expression_type(store, assignment_expression, source_types.result)?;
    }
    let source_type = source_types.result;
    if !store.is_type_assignable_to_with_global_types(source_type, target, global_types)? {
        let staged = super::object_diagnostics::diagnostics_for_failed_assignment(
            store,
            host,
            global_types,
            expression,
            &source_types,
            target,
            fallback_node,
            options,
        )?;
        for diagnostic in staged {
            merge_retry_diagnostic(diagnostics, diagnostic);
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
    global_types: &CanonicalGlobalTypes,
    store: &mut CanonicalTypeMapperStore,
    options: CanonicalCheckerOptions,
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

    let plan = SourcePlanner::new_semantic(arena, bound, source, store, host).finish()?;
    store.prepare_regular_literal_types(&plan.strings, &plan.numbers, &plan.bigints)?;
    let mut deferred = Vec::new();

    for statement in plan.statements {
        match statement {
            PlannedStatement::TypeAlias(symbol) | PlannedStatement::Interface(symbol) => {
                let mut statement_diagnostics = CanonicalCheckerDiagnostics::default();
                let result = CanonicalTypeQuery::new_with_global_types(
                    store,
                    host,
                    global_types,
                    options,
                    &mut statement_diagnostics,
                )
                .and_then(|mut query| query.get_declared_type_of_symbol(symbol));
                merge_retry_diagnostics(diagnostics, statement_diagnostics);
                result?;
            }
            PlannedStatement::ExternalModuleMarker => {}
            PlannedStatement::Variables(variables) => {
                for variable in variables {
                    check_planned_assignment(
                        store,
                        host,
                        global_types,
                        source,
                        options,
                        diagnostics,
                        &mut deferred,
                        variable.type_node,
                        &variable.initializer,
                        variable.name,
                        None,
                    )?;
                }
            }
            PlannedStatement::Assignment(assignment) => check_planned_assignment(
                store,
                host,
                global_types,
                source,
                options,
                diagnostics,
                &mut deferred,
                assignment.target_type_node,
                &assignment.right,
                assignment.left,
                Some(assignment.expression),
            )?,
        }
    }

    validate_deferred_assertions(store, source, &deferred)?;
    check_deferred_assertions(store, host, global_types, options, diagnostics, &deferred)?;

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
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalProgramBindings, CanonicalSourceFileFacts, CanonicalSourceLanguage, CheckFlags,
        EscapedName, InternalSymbolName, SymbolFlags,
    };
    use ts_diagnostics::Category;
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, DeclaredTypeHostError, IntrinsicBootstrapOptions,
        RelationStateSnapshot, TypeNodeUnavailable, ValueSymbolLinks,
        object_members::{
            DeclaredPropertyObjectProof, DeclaredPropertyObjectValidation,
            validate_resolved_declared_property_object,
        },
        production::GlobalMergeCompletion,
        type_records::TypeData,
        types::ObjectFlags,
    };

    type ObservableSourceState = (
        [usize; 4],
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

    fn observable_state(
        context: &CanonicalCheckerContext<'_>,
        file: FileId,
    ) -> ObservableSourceState {
        let store = context.store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        (
            [
                store.type_len(),
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
            variable.initializer.clone()
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

    #[test]
    fn mixed_array_and_property_object_subtype_reduction_stays_typed_unavailable() {
        let library = parsed("interface Array<T> {}");
        let source = parsed("var mixed: any = [[1], { id: 1 }];");
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

    #[test]
    fn global_type_queries_rescan_shared_array_union_cache_with_capability() {
        let library = parsed("interface Array<T> {}");
        let expression = parsed("var nested: any = [[1], \"text\"];");
        let query = parsed("var target: string | number = 1;");
        let library_file = FileId::new(134);
        let expression_file = FileId::new(135);
        let query_file = FileId::new(136);
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
    fn declared_method_signature_and_generic_array_elements_remain_typed_boundaries() {
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
        let before = observable_state(&context, file);
        assert!(matches!(
            context.get_type_from_type_node(type_alias_body(&source, file, "Instantiated")),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::TypeArgumentsUnsupported(_)
            )),
        ));
        assert_eq!(observable_state(&context, file), before);
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
        let array_alias = ordered
            .get_type_from_type_node(array_alias_body)
            .unwrap();
        assert_eq!(ordered.type_to_string(array_alias).unwrap(), "number[]");
        let ordered_outer = ordered.get_type_from_type_node(outer_body).unwrap();
        assert_eq!(ordered.type_to_string(ordered_outer).unwrap(), "Outer");

        let array_union_body = type_alias_body(&source, file, "ArrayUnion");
        let nested_union_body = type_alias_body(&source, file, "NestedUnion");
        let array_union = ordered
            .get_type_from_type_node(array_union_body)
            .unwrap();
        assert_eq!(ordered.type_to_string(array_union).unwrap(), "ArrayUnion");
        let nested_union = ordered
            .get_type_from_type_node(nested_union_body)
            .unwrap();
        assert_eq!(
            ordered.type_to_string(nested_union).unwrap(),
            "NestedUnion",
        );

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
    fn unsupported_assignment_target_rejects_the_source_plan_without_writes() {
        let source = parsed(concat!(
            "var earlier: number = 0; ",
            "let target: number = 0; target = 1;",
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
            "Type 'boolean' is not assignable to type 'string | number | null'."
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
                SourceSyntaxRole::VariableStatement,
            ),
            (
                "export type Alias = string;",
                SourceSyntaxRole::TypeAliasDeclaration,
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

            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Syntax { role, .. }
                )) if role == expected_role
            ));
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
                "string",
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
                Err(SourceCheckError::RelationUnavailable(
                    RelationUnavailable::InvalidStructuredMembers(target)
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
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::InvalidStructuredMembers(nested)
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
            "type Earlier = Earlier; export interface Bad { value: string }",
            "type Earlier = Earlier; interface Bad<T> { value: T }",
            "type Earlier = Earlier; interface Base {} interface Bad extends Base {}",
            "type Earlier = Earlier; interface Bad { method(): string }",
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

            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Syntax {
                        role: SourceSyntaxRole::InterfaceDeclaration,
                        ..
                    }
                ))
            ));
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
    fn unsupported_object_forms_and_shadowed_undefined_fail_before_writes() {
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
            (
                r#"const undefined: string = "shadow"; const value: any = { missing: undefined };"#,
                SourceSyntaxRole::VariableInitializer,
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
            "function unsupported() {}",
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
        let first = parsed(concat!(
            "type Blocked<T> = T; ",
            "const first: B = 1; ",
            r#"const blocked: Blocked<() => string> = "";"#,
        ));
        let second = parsed("type B = B;");
        let first_file = FileId::new(53);
        let second_file = FileId::new(54);
        let mut context = context(
            &[(first_file, &first), (second_file, &second)],
            CanonicalCheckerOptions::default(),
        );

        let result = context.check_source_file(first_file);
        assert!(
            matches!(
                result,
                Err(SourceCheckError::DeclaredType(
                    DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::UnsupportedSyntax {
                            kind: SyntaxKind::FunctionType,
                            ..
                        }
                    )
                ))
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
}
