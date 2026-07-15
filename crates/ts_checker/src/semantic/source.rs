//! Atomic canonical checking for the first source-statement slice.
//!
//! This module deliberately supports only type aliases and explicitly typed
//! ordinary variable declarations with primitive literal initializers. The
//! complete source tree and the complete supported-statement plan are
//! validated before checker state is touched. Unsupported syntax is therefore
//! a typed boundary, never a request to fall back to the legacy checker or to
//! synthesize `any`. Canonical memo caches are not rolled back after a later
//! semantic failure; diagnostics coupled to those caches remain in private
//! source staging until a retry completes and publishes them atomically.

use std::collections::HashSet;

use ts_ast::{FileId, Node, NodeArena, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{BoundFile, SemanticSymbolId};
use ts_core::TextRange;
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_jsnum::{Number, PseudoBigInt};

use super::{
    AssignabilityErrorDisplay, CanonicalCheckerDiagnostic, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalTypeFormatFlags, CanonicalTypeMapperStore, DeclaredTypeError,
    DeclaredTypeHost, RelationUnavailable, SourceFileLinks, SourceFileRef, TypeDisplayUnavailable,
    TypeId,
    bootstrap::LiteralTypeCacheError,
    formatter::get_type_names_for_assignability_error_with_flags,
    type_nodes::{CanonicalTypeQuery, normalize_bigint_literal, normalize_numeric_separators},
};

const NODE_FLAG_JSDOC: u32 = 1 << 22;
const NODE_FLAG_LET: u32 = 1 << 0;
const NODE_FLAG_CONST: u32 = 1 << 1;

/// The syntactic position whose dependency-closed source-check support ended.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceSyntaxRole {
    SourceFile,
    Statement,
    VariableStatement,
    VariableDeclarationList,
    VariableDeclaration,
    VariableName,
    VariableType,
    VariableInitializer,
    PrefixUnaryOperand,
}

/// Syntax that cannot be checked exactly by the installed source slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnsupportedSourceSyntax {
    Syntax {
        node: NodeRef,
        kind: SyntaxKind,
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
    InvalidUnionAlias(SemanticSymbolId),
    InvalidPreparedQuery,
    Capacity,
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
            Self::Provenance(_)
            | Self::Unsupported(_)
            | Self::LiteralCache(_)
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

#[derive(Clone, Debug)]
enum PlannedExpression {
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
}

#[derive(Clone, Debug)]
struct PlannedVariable {
    name: NodeRef,
    type_node: NodeRef,
    initializer: PlannedExpression,
}

#[derive(Clone, Debug)]
enum PlannedStatement {
    TypeAlias(SemanticSymbolId),
    Variables(Vec<PlannedVariable>),
}

#[derive(Debug)]
struct SourceCheckPlan {
    statements: Vec<PlannedStatement>,
    strings: Vec<String>,
    numbers: Vec<Number>,
    bigints: Vec<PseudoBigInt>,
}

struct SourcePlanner<'arena> {
    arena: &'arena NodeArena,
    bound: &'arena BoundFile,
    source: SourceFileRef,
    strings: Vec<String>,
    numbers: Vec<Number>,
    bigints: Vec<PseudoBigInt>,
}

impl<'arena> SourcePlanner<'arena> {
    fn new(arena: &'arena NodeArena, bound: &'arena BoundFile, source: SourceFileRef) -> Self {
        Self {
            arena,
            bound,
            source,
            strings: Vec::new(),
            numbers: Vec::new(),
            bigints: Vec::new(),
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
        if facts.is_javascript_file() {
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
                    if !matches!(node.data, NodeData::TypeAliasDeclaration(_)) {
                        return Err(SourceCheckError::Provenance(
                            SourceCheckProvenanceError::MismatchedNodeData {
                                node: statement,
                                kind: node.kind,
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
                        if node.flags.0 != 0
                            || variable.modifiers.is_some()
                            || variable.flow_node.is_some()
                            || variable.facts != 0
                        {
                            return Err(self.unsupported(
                                statement,
                                node.kind,
                                SourceSyntaxRole::VariableStatement,
                            ));
                        }
                        variable.declaration_list
                    };
                    statements.push(PlannedStatement::Variables(
                        self.plan_variable_statement(statement, declaration_list)?,
                    ));
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
                Ok(PlannedExpression::Null)
            }
            SyntaxKind::TrueKeyword
                if matches!(self.node(expression)?.data, NodeData::KeywordExpression(_)) =>
            {
                Ok(PlannedExpression::Boolean(true))
            }
            SyntaxKind::FalseKeyword
                if matches!(self.node(expression)?.data, NodeData::KeywordExpression(_)) =>
            {
                Ok(PlannedExpression::Boolean(false))
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
                Ok(PlannedExpression::String(value))
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
                Ok(PlannedExpression::String(value))
            }
            SyntaxKind::NumericLiteral => {
                let value = self.plan_numeric_literal(expression)?;
                self.numbers.push(value);
                Ok(PlannedExpression::Number {
                    value,
                    unary_operand: None,
                })
            }
            SyntaxKind::BigIntLiteral => {
                let value = self.plan_bigint_literal(expression)?;
                self.bigints.push(value.clone());
                Ok(PlannedExpression::BigInt {
                    value,
                    unary_operand: None,
                })
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
                self.plan_expression(inner)
            }
            SyntaxKind::PrefixUnaryExpression => self.plan_prefix_unary(expression),
            _ => Err(self.unsupported(expression, kind, SourceSyntaxRole::VariableInitializer)),
        }
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
                Ok(PlannedExpression::Number {
                    value,
                    unary_operand: Some(positive),
                })
            }
            SyntaxKind::BigIntLiteral => {
                let positive = self.plan_bigint_literal(operand)?;
                let value = PseudoBigInt::new(&positive.base10_value, true);
                self.bigints.push(positive.clone());
                self.bigints.push(value.clone());
                Ok(PlannedExpression::BigInt {
                    value,
                    unary_operand: Some(positive),
                })
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

fn expression_type(
    store: &mut CanonicalTypeMapperStore,
    expression: &PlannedExpression,
) -> Result<TypeId, SourceCheckError> {
    match expression {
        PlannedExpression::Null => store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.null_widening_type)
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            )),
        PlannedExpression::Boolean(value) => store
            .intrinsic_bootstrap()
            .map(|bootstrap| {
                if *value {
                    bootstrap.regular_true_type
                } else {
                    bootstrap.regular_false_type
                }
            })
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))
            .and_then(|regular| {
                store
                    .fresh_type_of_literal_type(regular)
                    .map_err(Into::into)
            }),
        PlannedExpression::String(value) => {
            let regular = store.regular_string_literal_type(value.clone())?;
            Ok(store.fresh_type_of_literal_type(regular)?)
        }
        PlannedExpression::Number {
            value,
            unary_operand,
        } => {
            if let Some(operand) = unary_operand {
                store.regular_number_literal_type(*operand)?;
            }
            let regular = store.regular_number_literal_type(*value)?;
            Ok(store.fresh_type_of_literal_type(regular)?)
        }
        PlannedExpression::BigInt {
            value,
            unary_operand,
        } => {
            if let Some(operand) = unary_operand {
                store.regular_bigint_literal_type(operand.clone())?;
            }
            let regular = store.regular_bigint_literal_type(value.clone())?;
            Ok(store.fresh_type_of_literal_type(regular)?)
        }
    }
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

fn assignability_display_flags(options: CanonicalCheckerOptions) -> CanonicalTypeFormatFlags {
    if options.no_error_truncation {
        CanonicalTypeFormatFlags::NO_TRUNCATION
    } else {
        CanonicalTypeFormatFlags::NONE
    }
}

/// Checks one already-retained source into context-owned private staging.
pub(super) fn check_source_file(
    arena: &NodeArena,
    bound: &BoundFile,
    source: SourceFileRef,
    host: &DeclaredTypeHost<'_>,
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

    let plan = SourcePlanner::new(arena, bound, source).finish()?;
    store.prepare_regular_literal_types(&plan.strings, &plan.numbers, &plan.bigints)?;

    for statement in plan.statements {
        match statement {
            PlannedStatement::TypeAlias(symbol) => {
                let mut statement_diagnostics = CanonicalCheckerDiagnostics::default();
                let result =
                    CanonicalTypeQuery::new(store, host, options, &mut statement_diagnostics)
                        .and_then(|mut query| query.get_declared_type_of_symbol(symbol));
                merge_retry_diagnostics(diagnostics, statement_diagnostics);
                result?;
            }
            PlannedStatement::Variables(variables) => {
                for variable in variables {
                    let mut statement_diagnostics = CanonicalCheckerDiagnostics::default();
                    let target =
                        CanonicalTypeQuery::new(store, host, options, &mut statement_diagnostics)?
                            .get_type_from_type_node(variable.type_node);
                    merge_retry_diagnostics(diagnostics, statement_diagnostics);
                    let target = target?;
                    let source_type = expression_type(store, &variable.initializer)?;
                    if !store.is_type_assignable_to(source_type, target)? {
                        let AssignabilityErrorDisplay { source, target } =
                            get_type_names_for_assignability_error_with_flags(
                                store,
                                source_type,
                                target,
                                assignability_display_flags(options),
                            )?;
                        let message = message_by_code(2322)
                            .ok_or(SourceCheckError::MissingDiagnostic(2322))?;
                        diagnostics.lookup_or_issue(
                            Some(variable.name),
                            Diagnostic::with_arguments(message, [source, target]),
                        );
                    }
                }
            }
        }
    }

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
        CanonicalProgramBindings, CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, DeclaredTypeHostError, IntrinsicBootstrapOptions,
        RelationStateSnapshot, TypeNodeUnavailable, production::GlobalMergeCompletion,
    };

    type ObservableSourceState = (
        usize,
        usize,
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

    fn source_facts(file: FileId) -> CanonicalSourceFileFacts {
        CanonicalSourceFileFacts::new(
            EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::Script,
        )
    }

    fn completed_bindings(files: &[(FileId, &ParseResult)]) -> CanonicalProgramBindings {
        let mut binder = CanonicalBinder::new();
        for &(file, parsed) in files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    source_facts(file),
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
        CanonicalCheckerContext::new(
            completed_bindings(files),
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
            store.type_len(),
            store.mapper_len(),
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
    fn expression_literals_use_fresh_booleans_and_null_widening_identity() {
        let source = parsed("");
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
        assert_eq!(
            expression_type(store, &PlannedExpression::Boolean(true)),
            Ok(true_type)
        );
        assert_eq!(
            expression_type(store, &PlannedExpression::Boolean(false)),
            Ok(false_type)
        );
        assert_eq!(
            expression_type(store, &PlannedExpression::Null),
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
            "const first: B = 1; ",
            r#"const blocked: Array<string> = "";"#,
        ));
        let second = parsed("type B = B;");
        let first_file = FileId::new(53);
        let second_file = FileId::new(54);
        let mut context = context(
            &[(first_file, &first), (second_file, &second)],
            CanonicalCheckerOptions::default(),
        );

        assert!(matches!(
            context.check_source_file(first_file),
            Err(SourceCheckError::DeclaredType(
                DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::TypeArgumentsUnsupported(_)
                )
            ))
        ));
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
