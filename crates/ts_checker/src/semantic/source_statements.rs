//! Exact syntax and binder proof for the first function-statement vertical.
//!
//! This leaf admits two additive annotated-function shapes. The first contains
//! initialized identifier-named `var`/`let`/`const` declarations followed by
//! one final two-arm `if`, with a value return in each arm. The second contains
//! one fallthrough `if` between leading and trailing declarations, followed by
//! one final value return. The fallthrough `else` arm may be absent. This leaf
//! deliberately stops before expression planning,
//! lexical admission-set mutation, flow narrowing, or checking. Direct
//! identifier truthiness and the bounded strict `typeof` comparison form are
//! proven here; their semantic execution remains a source-dispatch
//! responsibility.

use std::collections::HashSet;

use ts_ast::{
    FlowFlags, FlowNode, FlowNodePayload, FlowRef, Node, NodeArena, NodeData, NodeId, NodeRef,
    SyntaxKind,
};
use ts_binder::{BoundFile, SemanticSymbolId};
use ts_core::{TextPos, TextRange};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerDiagnosticRange, CanonicalTypeMapperStore,
    source_callables::{SourceCallableFamily, SourceCallablePlan},
    source_flow::{SourceTypeofComparison, SourceTypeofTag},
    variables::{VariableBindingKind, VariablePlanError, plan_top_level_variable},
};

const NODE_FLAG_LET: u32 = 1 << 0;
const NODE_FLAG_CONST: u32 = 1 << 1;

/// The exact syntactic owner at which the closed statement proof stopped.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFunctionStatementsRole {
    Callable,
    FunctionBody,
    BodyStatement,
    LocalStatement,
    LocalDeclarationList,
    LocalDeclaration,
    LocalName,
    LocalType,
    LocalInitializer,
    IfStatement,
    Condition,
    BranchBlock,
    BranchStatement,
    ReturnStatement,
    ReturnExpression,
}

/// Valid source forms intentionally outside this first closed statement slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFunctionStatementsUnsupported {
    Syntax {
        node: NodeRef,
        kind: SyntaxKind,
        role: SourceFunctionStatementsRole,
    },
    InferredCallable(NodeRef),
    MissingFinalIf(NodeRef),
    MissingElse(NodeRef),
    MissingReturn(NodeRef),
    MissingInitializer(NodeRef),
    BindingKind(NodeRef),
    IncompleteFlow(NodeRef),
}

/// Malformed AST, binder, or callable provenance in an otherwise admitted form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFunctionStatementsInvariant {
    BoundSourceMismatch(NodeRef),
    MissingNode(NodeRef),
    NodeNotBound(NodeRef),
    MismatchedNodeData {
        node: NodeRef,
        kind: SyntaxKind,
    },
    InvalidParent {
        node: NodeRef,
        expected: Option<NodeId>,
        actual: Option<NodeId>,
    },
    InvalidRange {
        node: NodeRef,
        parent: NodeRef,
    },
    InvalidOrder {
        previous: NodeRef,
        next: NodeRef,
    },
    InvalidListRange(NodeRef),
    InvalidCallableEdge(NodeRef),
    InvalidContainer {
        node: NodeRef,
        expected: NodeRef,
        actual: Option<NodeRef>,
    },
    InvalidBlockScopeContainer {
        node: NodeRef,
        expected: NodeRef,
        actual: Option<NodeRef>,
    },
    MissingLocals(NodeRef),
    LocalTableMismatch {
        declaration: NodeRef,
        scope: NodeRef,
        expected: SemanticSymbolId,
        actual: Option<SemanticSymbolId>,
    },
    InvalidFlowContainer {
        node: NodeRef,
        expected: NodeRef,
        actual: Option<NodeRef>,
    },
    MissingFlowStart(NodeRef),
    UnexpectedFlowEnd(NodeRef),
    UnexpectedReturnFlow(NodeRef),
    CyclicCondition(NodeRef),
}

/// Read-only failure from the exact statement syntax/provenance leaf.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFunctionStatementsError {
    Unsupported(SourceFunctionStatementsUnsupported),
    Invariant(SourceFunctionStatementsInvariant),
    Variable(VariablePlanError),
}

impl From<SourceFunctionStatementsInvariant> for SourceFunctionStatementsError {
    fn from(error: SourceFunctionStatementsInvariant) -> Self {
        Self::Invariant(error)
    }
}

impl From<VariablePlanError> for SourceFunctionStatementsError {
    fn from(error: VariablePlanError) -> Self {
        Self::Variable(error)
    }
}

/// One exact local declaration, retaining both statement and list ownership.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceLocalDeclarationSyntax {
    pub(super) statement: NodeRef,
    pub(super) list: NodeRef,
    pub(super) declaration: NodeRef,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) binding: VariableBindingKind,
    pub(super) type_node: Option<NodeRef>,
    pub(super) initializer: NodeRef,
}

/// One exact `if` arm ending in a value-returning `return`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceReturnBranchSyntax {
    pub(super) block: Option<NodeRef>,
    pub(super) locals: Vec<SourceLocalDeclarationSyntax>,
    pub(super) return_statement: NodeRef,
    pub(super) return_expression: NodeRef,
}

/// The exact final `if` and its unwrapped direct identifier condition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceFinalIfSyntax {
    pub(super) statement: NodeRef,
    pub(super) condition: NodeRef,
    pub(super) condition_identifier: NodeRef,
    pub(super) typeof_condition: Option<SourceTypeofConditionSyntax>,
    pub(super) then_branch: SourceReturnBranchSyntax,
    pub(super) else_branch: SourceReturnBranchSyntax,
}

/// Proven `if` children and grammar diagnostics for nested export declarations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceControlIfSyntax {
    pub(super) statement: NodeRef,
    pub(super) condition: NodeRef,
    pub(super) then_statement: NodeRef,
    pub(super) else_statement: Option<NodeRef>,
    pub(super) nested_export_diagnostics: Vec<CanonicalCheckerDiagnostic>,
}

/// Exact source nodes retained for one direct `typeof` identifier comparison.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceTypeofConditionSyntax {
    pub(super) type_of_expression: NodeRef,
    pub(super) identifier: NodeRef,
    pub(super) operator: NodeRef,
    pub(super) literal: NodeRef,
    pub(super) tag: SourceTypeofTag,
    pub(super) comparison: SourceTypeofComparison,
    pub(super) type_of_on_left: bool,
}

/// Complete source-ordered syntax for the first closed function-body vertical.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) leading: Vec<SourceLocalDeclarationSyntax>,
    pub(super) final_if: SourceFinalIfSyntax,
}

/// Ordered local declarations with an optional final return statement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceLinearFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) locals: Vec<SourceLocalDeclarationSyntax>,
    pub(super) return_statement: Option<NodeRef>,
    pub(super) return_expression: Option<NodeRef>,
}

/// One fallthrough arm containing initialized locals only.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceFallthroughBranchSyntax {
    pub(super) block: Option<NodeRef>,
    pub(super) locals: Vec<SourceLocalDeclarationSyntax>,
}

/// The exact joined `if` and its unwrapped direct identifier condition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceJoinedIfSyntax {
    pub(super) statement: NodeRef,
    pub(super) condition: NodeRef,
    pub(super) condition_identifier: NodeRef,
    pub(super) typeof_condition: Option<SourceTypeofConditionSyntax>,
    pub(super) then_branch: SourceFallthroughBranchSyntax,
    pub(super) else_branch: SourceFallthroughBranchSyntax,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PlannedConditionSyntax {
    identifier: NodeRef,
    typeof_condition: Option<SourceTypeofConditionSyntax>,
}

/// Complete source-ordered syntax for the first post-`if` join vertical.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceJoinedFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) leading: Vec<SourceLocalDeclarationSyntax>,
    pub(super) joined_if: SourceJoinedIfSyntax,
    pub(super) trailing: Vec<SourceLocalDeclarationSyntax>,
    pub(super) return_statement: NodeRef,
    pub(super) return_expression: NodeRef,
}

/// Valid source forms intentionally outside the first post-`if` join slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceJoinedFunctionStatementsUnsupported {
    InferredCallable(NodeRef),
    MissingIf(NodeRef),
    AdditionalIf(NodeRef),
    MissingReturn(NodeRef),
    IncompleteFlow(NodeRef),
}

/// Malformed binder flow in an otherwise admitted joined body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceJoinedFunctionStatementsInvariant {
    InvalidCallableEdge(NodeRef),
    InvalidFlowContainer {
        node: NodeRef,
        expected: NodeRef,
        actual: Option<NodeRef>,
    },
    MissingFlowStart(NodeRef),
    UnexpectedFlowEnd(NodeRef),
    UnexpectedReturnFlow(NodeRef),
    MissingFlowPoint(NodeRef),
    MissingFlowNode(FlowRef),
    InvalidFlowNode(FlowRef),
    FlowPointMismatch {
        node: NodeRef,
        expected: FlowRef,
        actual: FlowRef,
    },
}

/// Read-only failure from the additive joined-body syntax/provenance leaf.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceJoinedFunctionStatementsError {
    Statements(SourceFunctionStatementsError),
    Unsupported(SourceJoinedFunctionStatementsUnsupported),
    Invariant(SourceJoinedFunctionStatementsInvariant),
}

impl From<SourceFunctionStatementsError> for SourceJoinedFunctionStatementsError {
    fn from(error: SourceFunctionStatementsError) -> Self {
        Self::Statements(error)
    }
}

impl From<SourceFunctionStatementsInvariant> for SourceJoinedFunctionStatementsError {
    fn from(error: SourceFunctionStatementsInvariant) -> Self {
        Self::Statements(error.into())
    }
}

impl From<SourceJoinedFunctionStatementsInvariant> for SourceJoinedFunctionStatementsError {
    fn from(error: SourceJoinedFunctionStatementsInvariant) -> Self {
        Self::Invariant(error)
    }
}

/// Proves the complete local-plus-final-`if` syntax and immutable binder route.
///
/// The returned vectors retain parser statement/declaration order. No checker
/// cache, scope-admission set, or flow type is changed by this operation.
pub(super) fn plan_source_function_statements_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    callable: &SourceCallablePlan,
) -> Result<SourceFunctionStatementsSyntax, SourceFunctionStatementsError> {
    SyntaxPlanner {
        arena,
        bound,
        store,
        callable,
    }
    .plan()
}

/// Validates an `if` statement independently of its enclosing source scope.
pub(super) fn plan_source_control_if_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    statement: NodeRef,
    expected_parent: NodeRef,
) -> Result<SourceControlIfSyntax, SourceFunctionStatementsError> {
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || !expected_parent.is_for(arena.id(), bound.file_id())
    {
        return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(statement).into());
    }
    let record = control_statement_node(arena, bound, statement)?;
    let NodeData::IfStatement(data) = &record.data else {
        return Err(SourceFunctionStatementsError::Unsupported(
            SourceFunctionStatementsUnsupported::Syntax {
                node: statement,
                kind: record.kind,
                role: SourceFunctionStatementsRole::IfStatement,
            },
        ));
    };
    if record.kind != SyntaxKind::IfStatement
        || record.flags.0 != 0
        || data.flow_node.is_some()
        || data.facts != 0
    {
        return Err(SourceFunctionStatementsError::Unsupported(
            SourceFunctionStatementsUnsupported::Syntax {
                node: statement,
                kind: record.kind,
                role: SourceFunctionStatementsRole::IfStatement,
            },
        ));
    }
    let container = validate_control_statement_parent(arena, bound, statement, expected_parent)?;

    let condition = NodeRef::new(statement.arena, statement.file, data.expression);
    validate_control_statement_child(arena, bound, statement, condition, container)?;
    let then_statement = NodeRef::new(statement.arena, statement.file, data.then_statement);
    validate_control_statement_child(arena, bound, statement, then_statement, container)?;
    let condition_range = control_statement_node(arena, bound, condition)?.range;
    let then_range = control_statement_node(arena, bound, then_statement)?.range;
    if condition_range.end > then_range.start {
        return Err(SourceFunctionStatementsInvariant::InvalidOrder {
            previous: condition,
            next: then_statement,
        }
        .into());
    }

    let else_statement = data
        .else_statement
        .map(|node| NodeRef::new(statement.arena, statement.file, node));
    if let Some(else_statement) = else_statement {
        validate_control_statement_child(arena, bound, statement, else_statement, container)?;
        if then_range.end
            > control_statement_node(arena, bound, else_statement)?
                .range
                .start
        {
            return Err(SourceFunctionStatementsInvariant::InvalidOrder {
                previous: then_statement,
                next: else_statement,
            }
            .into());
        }
    }

    let nested_export_diagnostics = std::iter::once(then_statement)
        .chain(else_statement)
        .filter_map(|branch| nested_export_declaration_diagnostic(arena, bound, branch))
        .collect();
    Ok(SourceControlIfSyntax {
        statement,
        condition,
        then_statement,
        else_statement,
        nested_export_diagnostics,
    })
}

fn control_statement_node<'arena>(
    arena: &'arena NodeArena,
    bound: &BoundFile,
    node: NodeRef,
) -> Result<&'arena Node, SourceFunctionStatementsError> {
    if !node.is_for(arena.id(), bound.file_id()) {
        return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(node).into());
    }
    if !bound.contains(node) {
        return Err(SourceFunctionStatementsInvariant::NodeNotBound(node).into());
    }
    let record = arena
        .get(node.node)
        .ok_or(SourceFunctionStatementsInvariant::MissingNode(node))?;
    if !record.data.matches_syntax_kind(record.kind) {
        return Err(SourceFunctionStatementsInvariant::MismatchedNodeData {
            node,
            kind: record.kind,
        }
        .into());
    }
    Ok(record)
}

fn validate_control_statement_parent(
    arena: &NodeArena,
    bound: &BoundFile,
    statement: NodeRef,
    expected_parent: NodeRef,
) -> Result<NodeRef, SourceFunctionStatementsError> {
    let record = control_statement_node(arena, bound, statement)?;
    if record.parent != Some(expected_parent.node) {
        return Err(SourceFunctionStatementsInvariant::InvalidParent {
            node: statement,
            expected: Some(expected_parent.node),
            actual: record.parent,
        }
        .into());
    }
    let parent = control_statement_node(arena, bound, expected_parent)?;
    if !range_contains(parent.range, record.range) {
        return Err(SourceFunctionStatementsInvariant::InvalidRange {
            node: statement,
            parent: expected_parent,
        }
        .into());
    }
    bound.container(statement).ok_or_else(|| {
        SourceFunctionStatementsInvariant::InvalidContainer {
            node: statement,
            expected: expected_parent,
            actual: None,
        }
        .into()
    })
}

fn validate_control_statement_child(
    arena: &NodeArena,
    bound: &BoundFile,
    parent: NodeRef,
    child: NodeRef,
    container: NodeRef,
) -> Result<(), SourceFunctionStatementsError> {
    let record = control_statement_node(arena, bound, child)?;
    if record.parent != Some(parent.node) {
        return Err(SourceFunctionStatementsInvariant::InvalidParent {
            node: child,
            expected: Some(parent.node),
            actual: record.parent,
        }
        .into());
    }
    if !range_contains(
        control_statement_node(arena, bound, parent)?.range,
        record.range,
    ) {
        return Err(SourceFunctionStatementsInvariant::InvalidRange {
            node: child,
            parent,
        }
        .into());
    }
    let actual = bound.container(child);
    if actual != Some(container) {
        return Err(SourceFunctionStatementsInvariant::InvalidContainer {
            node: child,
            expected: container,
            actual,
        }
        .into());
    }
    Ok(())
}

fn nested_export_declaration_diagnostic(
    arena: &NodeArena,
    bound: &BoundFile,
    declaration: NodeRef,
) -> Option<CanonicalCheckerDiagnostic> {
    let record = control_statement_node(arena, bound, declaration).ok()?;
    if !matches!(&record.data, NodeData::ExportDeclaration(_)) {
        return None;
    }
    let parent = record.parent.and_then(|node| arena.get(node))?;
    if matches!(
        parent.kind,
        SyntaxKind::SourceFile | SyntaxKind::ModuleBlock | SyntaxKind::ModuleDeclaration
    ) {
        return None;
    }
    let source = arena.source_text()?;
    let start = usize::try_from(record.range.start.get()).ok()?;
    let end = usize::try_from(record.range.end.get()).ok()?;
    let text = source.get(start..end)?;
    let leading = text.find(|character: char| !character.is_whitespace())?;
    let keyword_start = start.checked_add(leading)?;
    let keyword_end = keyword_start.checked_add("export".len())?;
    if source.get(keyword_start..keyword_end) != Some("export") {
        return None;
    }
    let range = TextRange::new(
        TextPos::new(u32::try_from(keyword_start).ok()?),
        TextPos::new(u32::try_from(keyword_end).ok()?),
    );
    let code = if bound.source_facts()?.is_javascript_file() {
        1_474
    } else {
        1_233
    };
    Some(CanonicalCheckerDiagnostic {
        node: Some(declaration),
        range_override: Some(CanonicalCheckerDiagnosticRange::new(declaration, range)),
        diagnostic: Diagnostic::new(message_by_code(code)?),
        related_information: Vec::new(),
    })
}

/// Proves an inferred or annotated function body with straight-line locals.
pub(super) fn plan_source_linear_function_statements_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    callable: &SourceCallablePlan,
) -> Result<SourceLinearFunctionStatementsSyntax, SourceFunctionStatementsError> {
    SyntaxPlanner {
        arena,
        bound,
        store,
        callable,
    }
    .plan_linear()
}

/// Proves one local-plus-fallthrough-`if`-plus-return body and its binder join.
///
/// This is intentionally separate from [`plan_source_function_statements_syntax`]
/// so the existing final-`if` capability and all of its callers remain stable.
/// Returned vectors retain parser declaration order and no checker state is
/// mutated.
pub(super) fn plan_source_joined_function_statements_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    callable: &SourceCallablePlan,
) -> Result<SourceJoinedFunctionStatementsSyntax, SourceJoinedFunctionStatementsError> {
    SyntaxPlanner {
        arena,
        bound,
        store,
        callable,
    }
    .plan_joined()
}

struct SyntaxPlanner<'a> {
    arena: &'a NodeArena,
    bound: &'a BoundFile,
    store: &'a CanonicalTypeMapperStore,
    callable: &'a SourceCallablePlan,
}

impl SyntaxPlanner<'_> {
    fn plan_linear(
        &self,
    ) -> Result<SourceLinearFunctionStatementsSyntax, SourceFunctionStatementsError> {
        let declaration = self.callable.declaration;
        if !declaration.is_for(self.arena.id(), self.bound.file_id())
            || self.bound.node_arena_id() != self.arena.id()
            || self.bound.node_arena_revision() != self.arena.revision()
        {
            return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(declaration).into());
        }
        if self.callable.family != SourceCallableFamily::FunctionDeclaration {
            return Err(self.unsupported(
                declaration,
                self.node(declaration)?.kind,
                SourceFunctionStatementsRole::Callable,
            ));
        }

        let record = self.node(declaration)?;
        let NodeData::FunctionDeclaration(function) = &record.data else {
            return Err(self.unsupported(
                declaration,
                record.kind,
                SourceFunctionStatementsRole::Callable,
            ));
        };
        if record.kind != SyntaxKind::FunctionDeclaration
            || function.body != Some(self.callable.body.node)
            || function.type_
                != self
                    .callable
                    .return_type
                    .type_node()
                    .map(|type_node| type_node.node)
        {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        }

        let body = self.callable.body;
        self.validate_range(body, declaration)?;
        let statements = self.plan_body(body, declaration)?;
        let mut locals = Vec::new();
        let mut return_statement = None;
        let mut return_expression = None;
        for (index, statement_id) in statements.iter().copied().enumerate() {
            let statement = self.reference(statement_id);
            match self.node(statement)?.kind {
                SyntaxKind::VariableStatement | SyntaxKind::Block | SyntaxKind::EmptyStatement => {
                    locals.extend(self.plan_local_or_block_statement(
                        statement,
                        body,
                        declaration,
                    )?);
                }
                SyntaxKind::ReturnStatement if index + 1 == statements.len() => {
                    return_expression = self.plan_linear_return(statement, body, declaration)?;
                    return_statement = Some(statement);
                }
                kind => {
                    return Err(self.unsupported(
                        statement,
                        kind,
                        SourceFunctionStatementsRole::BodyStatement,
                    ));
                }
            }
        }

        let flow = self.bound.flow_graph();
        if flow.container_is_complete(declaration) != Some(true) {
            return Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::IncompleteFlow(declaration),
            ));
        }
        if flow.container_start(declaration).is_none() {
            return Err(SourceFunctionStatementsInvariant::MissingFlowStart(declaration).into());
        }
        if return_statement.is_some() && flow.container_end(declaration).is_some() {
            return Err(SourceFunctionStatementsInvariant::UnexpectedFlowEnd(declaration).into());
        }
        if flow.container_return(declaration).is_some() {
            return Err(
                SourceFunctionStatementsInvariant::UnexpectedReturnFlow(declaration).into(),
            );
        }

        Ok(SourceLinearFunctionStatementsSyntax {
            body,
            locals,
            return_statement,
            return_expression,
        })
    }

    fn plan_linear_return(
        &self,
        statement: NodeRef,
        body: NodeRef,
        callable: NodeRef,
    ) -> Result<Option<NodeRef>, SourceFunctionStatementsError> {
        let record = self.node(statement)?;
        let NodeData::ReturnStatement(return_data) = &record.data else {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::ReturnStatement,
            ));
        };
        if record.kind != SyntaxKind::ReturnStatement
            || record.flags.0 != 0
            || record.parent != Some(body.node)
            || return_data.flow_node.is_some()
            || return_data.facts != 0
        {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::ReturnStatement,
            ));
        }
        self.validate_range(statement, body)?;
        self.validate_container(statement, callable)?;
        self.validate_block_scope_container(statement, callable)?;

        let Some(expression) = return_data.expression.map(|node| self.reference(node)) else {
            return Ok(None);
        };
        self.validate_parent(
            expression,
            Some(statement.node),
            SourceFunctionStatementsRole::ReturnExpression,
        )?;
        self.validate_range(expression, statement)?;
        self.validate_container(expression, callable)?;
        self.validate_block_scope_container(expression, callable)?;
        Ok(Some(expression))
    }

    fn plan_nested_local_block(
        &self,
        block: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<Vec<SourceLocalDeclarationSyntax>, SourceFunctionStatementsError> {
        let record = self.node(block)?;
        let NodeData::Block(data) = &record.data else {
            return Err(self.unsupported(
                block,
                record.kind,
                SourceFunctionStatementsRole::BranchBlock,
            ));
        };
        if record.kind != SyntaxKind::Block
            || record.flags.0 != 0
            || record.parent != Some(parent.node)
            || data.flow_node.is_some()
            || data.next_container.is_some()
            || data.statements.has_trailing_comma
            || data.facts != 0
        {
            return Err(self.unsupported(
                block,
                record.kind,
                SourceFunctionStatementsRole::BranchBlock,
            ));
        }
        self.validate_range(block, parent)?;
        self.validate_container(block, callable)?;
        let outer_scope = if parent == self.callable.body {
            callable
        } else {
            parent
        };
        self.validate_block_scope_container(block, outer_scope)?;
        self.validate_node_list(block, data.statements.range, &data.statements.nodes)?;

        let mut locals = Vec::new();
        for &statement_id in &data.statements.nodes {
            let statement = self.reference(statement_id);
            match self.node(statement)?.kind {
                SyntaxKind::VariableStatement | SyntaxKind::Block | SyntaxKind::EmptyStatement => {
                    locals.extend(self.plan_local_or_block_statement(statement, block, callable)?);
                }
                kind => {
                    return Err(self.unsupported(
                        statement,
                        kind,
                        SourceFunctionStatementsRole::BranchStatement,
                    ));
                }
            }
        }
        Ok(locals)
    }

    fn plan_local_or_block_statement(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<Vec<SourceLocalDeclarationSyntax>, SourceFunctionStatementsError> {
        match self.node(statement)?.kind {
            SyntaxKind::Block => self.plan_nested_local_block(statement, parent, callable),
            SyntaxKind::EmptyStatement => {
                self.validate_empty_statement(statement, parent, callable)?;
                Ok(Vec::new())
            }
            _ => self.plan_local_statement(statement, parent, callable),
        }
    }

    fn validate_empty_statement(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<(), SourceFunctionStatementsError> {
        let record = self.node(statement)?;
        let NodeData::EmptyStatement(empty) = &record.data else {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        };
        if record.kind != SyntaxKind::EmptyStatement
            || record.flags.0 != 0
            || record.parent != Some(parent.node)
            || empty.flow_node.is_some()
        {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }
        self.validate_range(statement, parent)?;
        self.validate_container(statement, callable)?;
        let scope = if parent == self.callable.body {
            callable
        } else {
            parent
        };
        self.validate_block_scope_container(statement, scope)
    }

    fn plan(&self) -> Result<SourceFunctionStatementsSyntax, SourceFunctionStatementsError> {
        let declaration = self.callable.declaration;
        if !declaration.is_for(self.arena.id(), self.bound.file_id())
            || self.bound.node_arena_id() != self.arena.id()
            || self.bound.node_arena_revision() != self.arena.revision()
        {
            return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(declaration).into());
        }
        if self.callable.family != SourceCallableFamily::FunctionDeclaration {
            return Err(self.unsupported(
                declaration,
                self.node(declaration)?.kind,
                SourceFunctionStatementsRole::Callable,
            ));
        }
        if self.callable.return_type.is_inferred() {
            return Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::InferredCallable(declaration),
            ));
        }

        let declaration_record = self.node(declaration)?;
        let NodeData::FunctionDeclaration(function) = &declaration_record.data else {
            return Err(self.unsupported(
                declaration,
                declaration_record.kind,
                SourceFunctionStatementsRole::Callable,
            ));
        };
        if declaration_record.kind != SyntaxKind::FunctionDeclaration
            || function.body != Some(self.callable.body.node)
            || function.type_
                != self
                    .callable
                    .return_type
                    .type_node()
                    .map(|type_node| type_node.node)
        {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        }

        let body = self.callable.body;
        self.validate_range(body, declaration)?;
        let statements = self.plan_body(body, declaration)?;
        let Some((&final_statement_id, leading_statement_ids)) = statements.split_last() else {
            return Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::MissingFinalIf(body),
            ));
        };

        let mut leading = Vec::new();
        for &statement_id in leading_statement_ids {
            let statement = self.reference(statement_id);
            leading.extend(self.plan_local_or_block_statement(statement, body, declaration)?);
        }

        let final_if = self.plan_final_if(self.reference(final_statement_id), body, declaration)?;
        self.validate_flow(&final_if)?;

        Ok(SourceFunctionStatementsSyntax {
            body,
            leading,
            final_if,
        })
    }

    fn plan_body(
        &self,
        body: NodeRef,
        declaration: NodeRef,
    ) -> Result<Vec<NodeId>, SourceFunctionStatementsError> {
        let record = self.node(body)?;
        let NodeData::Block(block) = &record.data else {
            return Err(self.unsupported(
                body,
                record.kind,
                SourceFunctionStatementsRole::FunctionBody,
            ));
        };
        if record.kind != SyntaxKind::Block
            || record.flags.0 != 0
            || record.parent != Some(declaration.node)
            || block.flow_node.is_some()
            || block.next_container.is_some()
            || block.statements.has_trailing_comma
            || block.facts != 0
        {
            return Err(self.unsupported(
                body,
                record.kind,
                SourceFunctionStatementsRole::FunctionBody,
            ));
        }
        self.validate_container(body, declaration)?;
        self.validate_block_scope_container(body, declaration)?;
        self.validate_node_list(body, block.statements.range, &block.statements.nodes)?;
        Ok(block.statements.nodes.clone())
    }

    fn plan_local_statement(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<Vec<SourceLocalDeclarationSyntax>, SourceFunctionStatementsError> {
        let expected_scope = if parent == self.callable.body {
            callable
        } else {
            parent
        };
        let record = self.node(statement)?;
        let NodeData::VariableStatement(variable) = &record.data else {
            return Err(self.unsupported(
                statement,
                record.kind,
                if parent == self.callable.body {
                    SourceFunctionStatementsRole::BodyStatement
                } else {
                    SourceFunctionStatementsRole::BranchStatement
                },
            ));
        };
        if record.kind != SyntaxKind::VariableStatement
            || record.flags.0 != 0
            || record.parent != Some(parent.node)
            || variable.modifiers.is_some()
            || variable.flow_node.is_some()
            || variable.facts != 0
        {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::LocalStatement,
            ));
        }
        self.validate_range(statement, parent)?;
        self.validate_container(statement, callable)?;
        self.validate_block_scope_container(statement, expected_scope)?;

        let list = self.reference(variable.declaration_list);
        let list_record = self.node(list)?;
        let NodeData::VariableDeclarationList(list_data) = &list_record.data else {
            return Err(self.unsupported(
                list,
                list_record.kind,
                SourceFunctionStatementsRole::LocalDeclarationList,
            ));
        };
        if list_record.kind != SyntaxKind::VariableDeclarationList
            || list_record.parent != Some(statement.node)
            || list_data.declarations.range != list_record.range
            || list_data.declarations.has_trailing_comma
            || list_data.declarations.nodes.is_empty()
            || list_data.facts != 0
        {
            return Err(self.unsupported(
                list,
                list_record.kind,
                SourceFunctionStatementsRole::LocalDeclarationList,
            ));
        }
        self.validate_range(list, statement)?;
        self.validate_container(list, callable)?;
        self.validate_block_scope_container(list, expected_scope)?;
        self.validate_node_list(
            list,
            list_data.declarations.range,
            &list_data.declarations.nodes,
        )?;
        let binding = match list_record.flags.0 {
            0 if parent == self.callable.body => VariableBindingKind::Var,
            NODE_FLAG_LET => VariableBindingKind::Let,
            NODE_FLAG_CONST => VariableBindingKind::Const,
            _ => {
                return Err(SourceFunctionStatementsError::Unsupported(
                    SourceFunctionStatementsUnsupported::BindingKind(list),
                ));
            }
        };

        let mut declarations = Vec::with_capacity(list_data.declarations.nodes.len());
        for &declaration_id in &list_data.declarations.nodes {
            declarations.push(self.plan_local_declaration(
                statement,
                list,
                self.reference(declaration_id),
                callable,
                expected_scope,
                binding,
            )?);
        }
        Ok(declarations)
    }

    #[allow(clippy::too_many_arguments)]
    fn plan_local_declaration(
        &self,
        statement: NodeRef,
        list: NodeRef,
        declaration: NodeRef,
        callable: NodeRef,
        expected_scope: NodeRef,
        binding: VariableBindingKind,
    ) -> Result<SourceLocalDeclarationSyntax, SourceFunctionStatementsError> {
        let record = self.node(declaration)?;
        let NodeData::VariableDeclaration(variable) = &record.data else {
            return Err(self.unsupported(
                declaration,
                record.kind,
                SourceFunctionStatementsRole::LocalDeclaration,
            ));
        };
        if record.kind != SyntaxKind::VariableDeclaration
            || record.flags.0 != 0
            || record.parent != Some(list.node)
            || variable.exclamation_token.is_some()
            || variable.local_symbol.is_some()
            || variable.symbol.is_some()
            || variable.facts != 0
        {
            return Err(self.unsupported(
                declaration,
                record.kind,
                SourceFunctionStatementsRole::LocalDeclaration,
            ));
        }
        self.validate_range(declaration, list)?;

        let name = self.reference(variable.name);
        let name_record = self.node(name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(self.unsupported(
                name,
                name_record.kind,
                SourceFunctionStatementsRole::LocalName,
            ));
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(declaration.node)
            || identifier.flow_node.is_some()
        {
            return Err(self.unsupported(
                name,
                name_record.kind,
                SourceFunctionStatementsRole::LocalName,
            ));
        }
        let name_text = identifier.text.clone();
        self.validate_range(name, declaration)?;
        self.validate_container(name, callable)?;
        self.validate_block_scope_container(name, expected_scope)?;

        let type_node = variable.type_.map(|node| self.reference(node));
        if let Some(type_node) = type_node {
            self.validate_parent(
                type_node,
                Some(declaration.node),
                SourceFunctionStatementsRole::LocalType,
            )?;
            self.validate_range(type_node, declaration)?;
            self.validate_order(name, type_node)?;
            self.validate_container(type_node, callable)?;
            self.validate_block_scope_container(type_node, expected_scope)?;
        }
        let initializer = variable
            .initializer
            .map(|node| self.reference(node))
            .ok_or(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::MissingInitializer(declaration),
            ))?;
        self.validate_parent(
            initializer,
            Some(declaration.node),
            SourceFunctionStatementsRole::LocalInitializer,
        )?;
        self.validate_range(initializer, declaration)?;
        self.validate_order(type_node.unwrap_or(name), initializer)?;
        self.validate_container(initializer, callable)?;
        self.validate_block_scope_container(initializer, expected_scope)?;

        self.validate_container(declaration, callable)?;
        self.validate_block_scope_container(declaration, expected_scope)?;
        let symbol = plan_top_level_variable(
            self.bound,
            self.store,
            declaration,
            name,
            &name_text,
            binding,
            false,
        )?;
        let locals = self.bound.locals(expected_scope).ok_or(
            SourceFunctionStatementsInvariant::MissingLocals(expected_scope),
        )?;
        let actual = self
            .store
            .symbol_table(locals)
            .and_then(|table| table.get_source(&name_text));
        if actual != Some(symbol) {
            return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                declaration,
                scope: expected_scope,
                expected: symbol,
                actual,
            }
            .into());
        }

        Ok(SourceLocalDeclarationSyntax {
            statement,
            list,
            declaration,
            name,
            symbol,
            binding,
            type_node,
            initializer,
        })
    }

    fn plan_final_if(
        &self,
        statement: NodeRef,
        body: NodeRef,
        callable: NodeRef,
    ) -> Result<SourceFinalIfSyntax, SourceFunctionStatementsError> {
        let record = self.node(statement)?;
        let NodeData::IfStatement(if_statement) = &record.data else {
            return Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::MissingFinalIf(statement),
            ));
        };
        if record.kind != SyntaxKind::IfStatement
            || record.flags.0 != 0
            || record.parent != Some(body.node)
            || if_statement.flow_node.is_some()
            || if_statement.facts != 0
        {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::IfStatement,
            ));
        }
        self.validate_range(statement, body)?;
        self.validate_container(statement, callable)?;
        self.validate_block_scope_container(statement, callable)?;
        let control = plan_source_control_if_syntax(self.arena, self.bound, statement, body)?;
        debug_assert_eq!(control.statement, statement);
        if !control.nested_export_diagnostics.is_empty() {
            return Err(self.unsupported(
                control.then_statement,
                self.node(control.then_statement)?.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }

        let condition = control.condition;
        self.validate_parent(
            condition,
            Some(statement.node),
            SourceFunctionStatementsRole::Condition,
        )?;
        self.validate_range(condition, statement)?;
        let condition_syntax = self.plan_condition(condition, callable)?;

        let then_block = control.then_statement;
        let else_block =
            control
                .else_statement
                .ok_or(SourceFunctionStatementsError::Unsupported(
                    SourceFunctionStatementsUnsupported::MissingElse(statement),
                ))?;
        self.validate_range(then_block, statement)?;
        self.validate_range(else_block, statement)?;
        self.validate_order(condition, then_block)?;
        self.validate_order(then_block, else_block)?;
        let then_branch = self.plan_branch(then_block, statement, callable)?;
        let else_branch = self.plan_branch(else_block, statement, callable)?;

        Ok(SourceFinalIfSyntax {
            statement,
            condition,
            condition_identifier: condition_syntax.identifier,
            typeof_condition: condition_syntax.typeof_condition,
            then_branch,
            else_branch,
        })
    }

    fn plan_condition(
        &self,
        condition: NodeRef,
        callable: NodeRef,
    ) -> Result<PlannedConditionSyntax, SourceFunctionStatementsError> {
        if self.node(condition)?.kind == SyntaxKind::BinaryExpression {
            return self.plan_typeof_condition(condition, callable);
        }
        let mut current = condition;
        let mut seen = HashSet::new();
        loop {
            if !seen.insert(current.node) {
                return Err(SourceFunctionStatementsInvariant::CyclicCondition(condition).into());
            }
            let record = self.node(current)?;
            match &record.data {
                NodeData::Identifier(identifier)
                    if record.kind == SyntaxKind::Identifier
                        && record.flags.0 == 0
                        && identifier.flow_node.is_none() =>
                {
                    self.validate_container(current, callable)?;
                    self.validate_block_scope_container(current, callable)?;
                    return Ok(PlannedConditionSyntax {
                        identifier: current,
                        typeof_condition: None,
                    });
                }
                NodeData::ParenthesizedExpression(parenthesized)
                    if record.kind == SyntaxKind::ParenthesizedExpression
                        && record.flags.0 == 0 =>
                {
                    self.validate_container(current, callable)?;
                    self.validate_block_scope_container(current, callable)?;
                    let inner = self.reference(parenthesized.expression);
                    self.validate_parent(
                        inner,
                        Some(current.node),
                        SourceFunctionStatementsRole::Condition,
                    )?;
                    self.validate_range(inner, current)?;
                    current = inner;
                }
                _ => {
                    return Err(self.unsupported(
                        current,
                        record.kind,
                        SourceFunctionStatementsRole::Condition,
                    ));
                }
            }
        }
    }

    fn plan_typeof_condition(
        &self,
        condition: NodeRef,
        callable: NodeRef,
    ) -> Result<PlannedConditionSyntax, SourceFunctionStatementsError> {
        let record = self.node(condition)?;
        let NodeData::BinaryExpression(binary) = &record.data else {
            return Err(self.unsupported(
                condition,
                record.kind,
                SourceFunctionStatementsRole::Condition,
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
                condition,
                record.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        }
        self.validate_container(condition, callable)?;
        self.validate_block_scope_container(condition, callable)?;

        let left = self.reference(binary.left);
        let operator = self.reference(binary.operator_token);
        let right = self.reference(binary.right);
        self.validate_parent(
            left,
            Some(condition.node),
            SourceFunctionStatementsRole::Condition,
        )?;
        self.validate_parent(
            operator,
            Some(condition.node),
            SourceFunctionStatementsRole::Condition,
        )?;
        self.validate_parent(
            right,
            Some(condition.node),
            SourceFunctionStatementsRole::Condition,
        )?;
        self.validate_range(left, condition)?;
        self.validate_range(operator, condition)?;
        self.validate_range(right, condition)?;
        self.validate_order(left, operator)?;
        self.validate_order(operator, right)?;

        let operator_record = self.node(operator)?;
        if operator_record.flags.0 != 0 || !matches!(operator_record.data, NodeData::Token(_)) {
            return Err(self.unsupported(
                operator,
                operator_record.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        }
        self.validate_container(operator, callable)?;
        self.validate_block_scope_container(operator, callable)?;
        let comparison = match operator_record.kind {
            SyntaxKind::EqualsEqualsEqualsToken => SourceTypeofComparison::Equal,
            SyntaxKind::ExclamationEqualsEqualsToken => SourceTypeofComparison::NotEqual,
            _ => {
                return Err(self.unsupported(
                    operator,
                    operator_record.kind,
                    SourceFunctionStatementsRole::Condition,
                ));
            }
        };

        let left_kind = self.node(left)?.kind;
        let right_kind = self.node(right)?.kind;
        let string_like = |kind| {
            matches!(
                kind,
                SyntaxKind::StringLiteral | SyntaxKind::NoSubstitutionTemplateLiteral
            )
        };
        let (type_of_expression, literal, type_of_on_left) =
            if left_kind == SyntaxKind::TypeOfExpression && string_like(right_kind) {
                (left, right, true)
            } else if right_kind == SyntaxKind::TypeOfExpression && string_like(left_kind) {
                (right, left, false)
            } else {
                return Err(self.unsupported(
                    condition,
                    record.kind,
                    SourceFunctionStatementsRole::Condition,
                ));
            };

        let type_of_record = self.node(type_of_expression)?;
        let NodeData::TypeOfExpression(type_of) = &type_of_record.data else {
            return Err(self.unsupported(
                type_of_expression,
                type_of_record.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        };
        if type_of_record.kind != SyntaxKind::TypeOfExpression || type_of_record.flags.0 != 0 {
            return Err(self.unsupported(
                type_of_expression,
                type_of_record.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        }
        self.validate_container(type_of_expression, callable)?;
        self.validate_block_scope_container(type_of_expression, callable)?;
        let identifier = self.reference(type_of.expression);
        self.validate_parent(
            identifier,
            Some(type_of_expression.node),
            SourceFunctionStatementsRole::Condition,
        )?;
        self.validate_range(identifier, type_of_expression)?;
        let identifier_record = self.node(identifier)?;
        let NodeData::Identifier(identifier_data) = &identifier_record.data else {
            return Err(self.unsupported(
                identifier,
                identifier_record.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        };
        if identifier_record.kind != SyntaxKind::Identifier
            || identifier_record.flags.0 != 0
            || identifier_data.flow_node.is_some()
        {
            return Err(self.unsupported(
                identifier,
                identifier_record.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        }
        self.validate_container(identifier, callable)?;
        self.validate_block_scope_container(identifier, callable)?;

        let literal_record = self.node(literal)?;
        if literal_record.flags.0 != 0 {
            return Err(self.unsupported(
                literal,
                literal_record.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        }
        let literal_text = match &literal_record.data {
            NodeData::StringLiteral(data)
                if literal_record.kind == SyntaxKind::StringLiteral && data.token_flags.0 == 0 =>
            {
                data.text.as_str()
            }
            NodeData::NoSubstitutionTemplateLiteral(data)
                if literal_record.kind == SyntaxKind::NoSubstitutionTemplateLiteral
                    && data.token_flags.0 == 0
                    && data.template_flags.0 == 0 =>
            {
                data.text.as_str()
            }
            _ => {
                return Err(self.unsupported(
                    literal,
                    literal_record.kind,
                    SourceFunctionStatementsRole::Condition,
                ));
            }
        };
        self.validate_container(literal, callable)?;
        self.validate_block_scope_container(literal, callable)?;
        let tag = match literal_text {
            "string" => SourceTypeofTag::String,
            "number" => SourceTypeofTag::Number,
            "boolean" => SourceTypeofTag::Boolean,
            "bigint" => SourceTypeofTag::BigInt,
            "symbol" => SourceTypeofTag::Symbol,
            "undefined" => SourceTypeofTag::Undefined,
            "object" => SourceTypeofTag::Object,
            "function" => SourceTypeofTag::Function,
            _ => {
                return Err(self.unsupported(
                    literal,
                    literal_record.kind,
                    SourceFunctionStatementsRole::Condition,
                ));
            }
        };

        Ok(PlannedConditionSyntax {
            identifier,
            typeof_condition: Some(SourceTypeofConditionSyntax {
                type_of_expression,
                identifier,
                operator,
                literal,
                tag,
                comparison,
                type_of_on_left,
            }),
        })
    }

    fn plan_branch(
        &self,
        block: NodeRef,
        if_statement: NodeRef,
        callable: NodeRef,
    ) -> Result<SourceReturnBranchSyntax, SourceFunctionStatementsError> {
        let record = self.node(block)?;
        if let NodeData::ReturnStatement(return_data) = &record.data {
            if record.kind != SyntaxKind::ReturnStatement
                || record.flags.0 != 0
                || record.parent != Some(if_statement.node)
                || return_data.flow_node.is_some()
                || return_data.facts != 0
            {
                return Err(self.unsupported(
                    block,
                    record.kind,
                    SourceFunctionStatementsRole::ReturnStatement,
                ));
            }
            self.validate_range(block, if_statement)?;
            self.validate_container(block, callable)?;
            self.validate_block_scope_container(block, callable)?;
            let return_expression = return_data
                .expression
                .map(|node| self.reference(node))
                .ok_or(SourceFunctionStatementsError::Unsupported(
                    SourceFunctionStatementsUnsupported::MissingReturn(block),
                ))?;
            self.validate_parent(
                return_expression,
                Some(block.node),
                SourceFunctionStatementsRole::ReturnExpression,
            )?;
            self.validate_range(return_expression, block)?;
            self.validate_container(return_expression, callable)?;
            self.validate_block_scope_container(return_expression, callable)?;
            return Ok(SourceReturnBranchSyntax {
                block: None,
                locals: Vec::new(),
                return_statement: block,
                return_expression,
            });
        }
        let NodeData::Block(block_data) = &record.data else {
            return Err(self.unsupported(
                block,
                record.kind,
                SourceFunctionStatementsRole::BranchBlock,
            ));
        };
        if record.kind != SyntaxKind::Block
            || record.flags.0 != 0
            || record.parent != Some(if_statement.node)
            || block_data.flow_node.is_some()
            || block_data.next_container.is_some()
            || block_data.statements.has_trailing_comma
            || block_data.facts != 0
        {
            return Err(self.unsupported(
                block,
                record.kind,
                SourceFunctionStatementsRole::BranchBlock,
            ));
        }
        self.validate_range(block, if_statement)?;
        self.validate_container(block, callable)?;
        self.validate_block_scope_container(block, callable)?;
        self.validate_node_list(
            block,
            block_data.statements.range,
            &block_data.statements.nodes,
        )?;

        let Some((&return_id, local_statement_ids)) = block_data.statements.nodes.split_last()
        else {
            return Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::MissingReturn(block),
            ));
        };
        let mut locals = Vec::new();
        for &statement_id in local_statement_ids {
            let statement = self.reference(statement_id);
            locals.extend(self.plan_local_or_block_statement(statement, block, callable)?);
        }

        let return_statement = self.reference(return_id);
        let return_record = self.node(return_statement)?;
        let NodeData::ReturnStatement(return_data) = &return_record.data else {
            return Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::MissingReturn(return_statement),
            ));
        };
        if return_record.kind != SyntaxKind::ReturnStatement
            || return_record.flags.0 != 0
            || return_record.parent != Some(block.node)
            || return_data.flow_node.is_some()
            || return_data.facts != 0
        {
            return Err(self.unsupported(
                return_statement,
                return_record.kind,
                SourceFunctionStatementsRole::ReturnStatement,
            ));
        }
        self.validate_container(return_statement, callable)?;
        self.validate_block_scope_container(return_statement, block)?;
        let return_expression = return_data
            .expression
            .map(|node| self.reference(node))
            .ok_or(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::MissingReturn(return_statement),
            ))?;
        self.validate_parent(
            return_expression,
            Some(return_statement.node),
            SourceFunctionStatementsRole::ReturnExpression,
        )?;
        self.validate_range(return_expression, return_statement)?;
        self.validate_container(return_expression, callable)?;
        self.validate_block_scope_container(return_expression, block)?;

        Ok(SourceReturnBranchSyntax {
            block: Some(block),
            locals,
            return_statement,
            return_expression,
        })
    }

    fn validate_flow(
        &self,
        final_if: &SourceFinalIfSyntax,
    ) -> Result<(), SourceFunctionStatementsError> {
        let declaration = self.callable.declaration;
        let flow = self.bound.flow_graph();
        if flow.container_is_complete(declaration) != Some(true) {
            return Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::IncompleteFlow(declaration),
            ));
        }
        if flow.container_start(declaration).is_none() {
            return Err(SourceFunctionStatementsInvariant::MissingFlowStart(declaration).into());
        }
        if flow.container_end(declaration).is_some() {
            return Err(SourceFunctionStatementsInvariant::UnexpectedFlowEnd(declaration).into());
        }
        // The current canonical binder creates a return aggregation target only
        // for constructors. Ordinary FunctionDeclaration returns terminate the
        // current path directly, so a retained return flow would be malformed.
        if flow.container_return(declaration).is_some() {
            return Err(
                SourceFunctionStatementsInvariant::UnexpectedReturnFlow(declaration).into(),
            );
        }
        let actual = flow.flow_container(final_if.statement);
        if actual != Some(declaration) {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: final_if.statement,
                expected: declaration,
                actual,
            }
            .into());
        }
        Ok(())
    }

    fn validate_range(
        &self,
        node: NodeRef,
        parent: NodeRef,
    ) -> Result<(), SourceFunctionStatementsError> {
        let range = self.node(node)?.range;
        let parent_range = self.node(parent)?.range;
        if !range_contains(parent_range, range) {
            return Err(SourceFunctionStatementsInvariant::InvalidRange { node, parent }.into());
        }
        Ok(())
    }

    fn validate_order(
        &self,
        previous: NodeRef,
        next: NodeRef,
    ) -> Result<(), SourceFunctionStatementsError> {
        let previous_range = self.node(previous)?.range;
        let next_range = self.node(next)?.range;
        if previous_range.end > next_range.start {
            return Err(SourceFunctionStatementsInvariant::InvalidOrder { previous, next }.into());
        }
        Ok(())
    }

    fn validate_node_list(
        &self,
        owner: NodeRef,
        range: ts_core::TextRange,
        nodes: &[NodeId],
    ) -> Result<(), SourceFunctionStatementsError> {
        let owner_range = self.node(owner)?.range;
        if !range_contains(owner_range, range) {
            return Err(SourceFunctionStatementsInvariant::InvalidListRange(owner).into());
        }

        let mut previous = None;
        for &node_id in nodes {
            let node = self.reference(node_id);
            let node_range = self.node(node)?.range;
            if !range_contains(range, node_range) {
                return Err(SourceFunctionStatementsInvariant::InvalidRange {
                    node,
                    parent: owner,
                }
                .into());
            }
            if let Some(previous) = previous {
                self.validate_order(previous, node)?;
            }
            previous = Some(node);
        }
        Ok(())
    }

    fn validate_parent(
        &self,
        node: NodeRef,
        expected: Option<NodeId>,
        role: SourceFunctionStatementsRole,
    ) -> Result<(), SourceFunctionStatementsError> {
        let record = self.node(node)?;
        if record.parent != expected {
            return Err(SourceFunctionStatementsInvariant::InvalidParent {
                node,
                expected,
                actual: record.parent,
            }
            .into());
        }
        if !record.data.matches_syntax_kind(record.kind) {
            return Err(self.unsupported(node, record.kind, role));
        }
        Ok(())
    }

    fn validate_container(
        &self,
        node: NodeRef,
        expected: NodeRef,
    ) -> Result<(), SourceFunctionStatementsError> {
        let actual = self.bound.container(node);
        if actual != Some(expected) {
            return Err(SourceFunctionStatementsInvariant::InvalidContainer {
                node,
                expected,
                actual,
            }
            .into());
        }
        Ok(())
    }

    fn validate_block_scope_container(
        &self,
        node: NodeRef,
        expected: NodeRef,
    ) -> Result<(), SourceFunctionStatementsError> {
        let actual = self.bound.block_scope_container(node);
        if actual != Some(expected) {
            return Err(
                SourceFunctionStatementsInvariant::InvalidBlockScopeContainer {
                    node,
                    expected,
                    actual,
                }
                .into(),
            );
        }
        Ok(())
    }

    fn node(&self, reference: NodeRef) -> Result<&Node, SourceFunctionStatementsError> {
        if !reference.is_for(self.arena.id(), self.bound.file_id()) {
            return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(reference).into());
        }
        if !self.bound.contains(reference) {
            return Err(SourceFunctionStatementsInvariant::NodeNotBound(reference).into());
        }
        let node = self
            .arena
            .get(reference.node)
            .ok_or(SourceFunctionStatementsInvariant::MissingNode(reference))?;
        if !node.data.matches_syntax_kind(node.kind) {
            return Err(SourceFunctionStatementsInvariant::MismatchedNodeData {
                node: reference,
                kind: node.kind,
            }
            .into());
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
        role: SourceFunctionStatementsRole,
    ) -> SourceFunctionStatementsError {
        debug_assert!(node.is_for(self.arena.id(), self.bound.file_id()));
        SourceFunctionStatementsError::Unsupported(SourceFunctionStatementsUnsupported::Syntax {
            node,
            kind,
            role,
        })
    }
}

const JOIN_FLOW_METADATA_BITS: u32 = FlowFlags::REFERENCED.bits() | FlowFlags::SHARED.bits();

impl SyntaxPlanner<'_> {
    #[allow(clippy::too_many_lines)]
    fn plan_joined(
        &self,
    ) -> Result<SourceJoinedFunctionStatementsSyntax, SourceJoinedFunctionStatementsError> {
        let declaration = self.callable.declaration;
        if !declaration.is_for(self.arena.id(), self.bound.file_id())
            || self.bound.node_arena_id() != self.arena.id()
            || self.bound.node_arena_revision() != self.arena.revision()
        {
            return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(declaration).into());
        }
        if self.callable.family != SourceCallableFamily::FunctionDeclaration {
            return Err(self
                .unsupported(
                    declaration,
                    self.node(declaration)?.kind,
                    SourceFunctionStatementsRole::Callable,
                )
                .into());
        }
        if self.callable.return_type.is_inferred() {
            return Err(SourceJoinedFunctionStatementsError::Unsupported(
                SourceJoinedFunctionStatementsUnsupported::InferredCallable(declaration),
            ));
        }

        let declaration_record = self.node(declaration)?;
        let NodeData::FunctionDeclaration(function) = &declaration_record.data else {
            return Err(self
                .unsupported(
                    declaration,
                    declaration_record.kind,
                    SourceFunctionStatementsRole::Callable,
                )
                .into());
        };
        if declaration_record.kind != SyntaxKind::FunctionDeclaration
            || function.body != Some(self.callable.body.node)
            || function.type_
                != self
                    .callable
                    .return_type
                    .type_node()
                    .map(|type_node| type_node.node)
        {
            return Err(
                SourceJoinedFunctionStatementsInvariant::InvalidCallableEdge(declaration).into(),
            );
        }

        let body = self.callable.body;
        self.validate_range(body, declaration)?;
        let statements = self.plan_body(body, declaration)?;
        let Some((&return_id, preceding)) = statements.split_last() else {
            return Err(SourceJoinedFunctionStatementsError::Unsupported(
                SourceJoinedFunctionStatementsUnsupported::MissingIf(body),
            ));
        };
        let return_statement = self.reference(return_id);
        if self.node(return_statement)?.kind != SyntaxKind::ReturnStatement {
            return Err(SourceJoinedFunctionStatementsError::Unsupported(
                SourceJoinedFunctionStatementsUnsupported::MissingReturn(return_statement),
            ));
        }

        let mut if_index = None;
        for (index, statement_id) in preceding.iter().copied().enumerate() {
            let statement = self.reference(statement_id);
            if self.node(statement)?.kind == SyntaxKind::IfStatement
                && if_index.replace(index).is_some()
            {
                return Err(SourceJoinedFunctionStatementsError::Unsupported(
                    SourceJoinedFunctionStatementsUnsupported::AdditionalIf(statement),
                ));
            }
        }
        let Some(if_index) = if_index else {
            return Err(SourceJoinedFunctionStatementsError::Unsupported(
                SourceJoinedFunctionStatementsUnsupported::MissingIf(body),
            ));
        };

        let mut leading = Vec::new();
        for &statement_id in &preceding[..if_index] {
            leading.extend(self.plan_local_or_block_statement(
                self.reference(statement_id),
                body,
                declaration,
            )?);
        }
        let joined_if =
            self.plan_joined_if(self.reference(preceding[if_index]), body, declaration)?;
        let mut trailing = Vec::new();
        for &statement_id in &preceding[if_index + 1..] {
            trailing.extend(self.plan_local_or_block_statement(
                self.reference(statement_id),
                body,
                declaration,
            )?);
        }
        let return_expression = self.plan_joined_return(return_statement, body, declaration)?;

        let syntax = SourceJoinedFunctionStatementsSyntax {
            body,
            leading,
            joined_if,
            trailing,
            return_statement,
            return_expression,
        };
        self.validate_joined_flow(&syntax)?;
        Ok(syntax)
    }

    fn plan_joined_if(
        &self,
        statement: NodeRef,
        body: NodeRef,
        callable: NodeRef,
    ) -> Result<SourceJoinedIfSyntax, SourceJoinedFunctionStatementsError> {
        let record = self.node(statement)?;
        let NodeData::IfStatement(if_statement) = &record.data else {
            return Err(SourceJoinedFunctionStatementsError::Unsupported(
                SourceJoinedFunctionStatementsUnsupported::MissingIf(statement),
            ));
        };
        if record.kind != SyntaxKind::IfStatement
            || record.flags.0 != 0
            || record.parent != Some(body.node)
            || if_statement.flow_node.is_some()
            || if_statement.facts != 0
        {
            return Err(self
                .unsupported(
                    statement,
                    record.kind,
                    SourceFunctionStatementsRole::IfStatement,
                )
                .into());
        }
        self.validate_range(statement, body)?;
        self.validate_container(statement, callable)?;
        self.validate_block_scope_container(statement, callable)?;
        let control = plan_source_control_if_syntax(self.arena, self.bound, statement, body)?;
        debug_assert_eq!(control.statement, statement);
        if !control.nested_export_diagnostics.is_empty() {
            return Err(self
                .unsupported(
                    control.then_statement,
                    self.node(control.then_statement)?.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                )
                .into());
        }

        let condition = control.condition;
        self.validate_parent(
            condition,
            Some(statement.node),
            SourceFunctionStatementsRole::Condition,
        )?;
        self.validate_range(condition, statement)?;
        let condition_syntax = self.plan_condition(condition, callable)?;

        let then_block = control.then_statement;
        self.validate_range(then_block, statement)?;
        self.validate_order(condition, then_block)?;
        let then_branch = self.plan_fallthrough_branch(then_block, statement, callable)?;
        let else_branch = if let Some(else_block) = control.else_statement {
            self.validate_range(else_block, statement)?;
            self.validate_order(then_block, else_block)?;
            self.plan_fallthrough_branch(else_block, statement, callable)?
        } else {
            SourceFallthroughBranchSyntax {
                block: None,
                locals: Vec::new(),
            }
        };

        Ok(SourceJoinedIfSyntax {
            statement,
            condition,
            condition_identifier: condition_syntax.identifier,
            typeof_condition: condition_syntax.typeof_condition,
            then_branch,
            else_branch,
        })
    }

    fn plan_fallthrough_branch(
        &self,
        block: NodeRef,
        if_statement: NodeRef,
        callable: NodeRef,
    ) -> Result<SourceFallthroughBranchSyntax, SourceJoinedFunctionStatementsError> {
        let record = self.node(block)?;
        let NodeData::Block(block_data) = &record.data else {
            return Err(self
                .unsupported(
                    block,
                    record.kind,
                    SourceFunctionStatementsRole::BranchBlock,
                )
                .into());
        };
        if record.kind != SyntaxKind::Block
            || record.flags.0 != 0
            || record.parent != Some(if_statement.node)
            || block_data.flow_node.is_some()
            || block_data.next_container.is_some()
            || block_data.statements.has_trailing_comma
            || block_data.facts != 0
        {
            return Err(self
                .unsupported(
                    block,
                    record.kind,
                    SourceFunctionStatementsRole::BranchBlock,
                )
                .into());
        }
        self.validate_range(block, if_statement)?;
        self.validate_container(block, callable)?;
        self.validate_block_scope_container(block, callable)?;
        self.validate_node_list(
            block,
            block_data.statements.range,
            &block_data.statements.nodes,
        )?;

        let mut locals = Vec::new();
        for &statement_id in &block_data.statements.nodes {
            let statement = self.reference(statement_id);
            locals.extend(self.plan_local_or_block_statement(statement, block, callable)?);
        }
        Ok(SourceFallthroughBranchSyntax {
            block: Some(block),
            locals,
        })
    }

    fn plan_joined_return(
        &self,
        statement: NodeRef,
        body: NodeRef,
        callable: NodeRef,
    ) -> Result<NodeRef, SourceJoinedFunctionStatementsError> {
        let record = self.node(statement)?;
        let NodeData::ReturnStatement(return_data) = &record.data else {
            return Err(SourceJoinedFunctionStatementsError::Unsupported(
                SourceJoinedFunctionStatementsUnsupported::MissingReturn(statement),
            ));
        };
        if record.kind != SyntaxKind::ReturnStatement
            || record.flags.0 != 0
            || record.parent != Some(body.node)
            || return_data.flow_node.is_some()
            || return_data.facts != 0
        {
            return Err(self
                .unsupported(
                    statement,
                    record.kind,
                    SourceFunctionStatementsRole::ReturnStatement,
                )
                .into());
        }
        self.validate_range(statement, body)?;
        self.validate_container(statement, callable)?;
        self.validate_block_scope_container(statement, callable)?;

        let expression = return_data
            .expression
            .map(|node| self.reference(node))
            .ok_or(SourceJoinedFunctionStatementsError::Unsupported(
                SourceJoinedFunctionStatementsUnsupported::MissingReturn(statement),
            ))?;
        self.validate_parent(
            expression,
            Some(statement.node),
            SourceFunctionStatementsRole::ReturnExpression,
        )?;
        self.validate_range(expression, statement)?;
        self.validate_container(expression, callable)?;
        self.validate_block_scope_container(expression, callable)?;
        Ok(expression)
    }

    fn validate_joined_flow(
        &self,
        syntax: &SourceJoinedFunctionStatementsSyntax,
    ) -> Result<(), SourceJoinedFunctionStatementsError> {
        let declaration = self.callable.declaration;
        let graph = self.bound.flow_graph();
        if graph.container_is_complete(declaration) != Some(true) {
            return Err(SourceJoinedFunctionStatementsError::Unsupported(
                SourceJoinedFunctionStatementsUnsupported::IncompleteFlow(declaration),
            ));
        }
        let start = graph.container_start(declaration).ok_or(
            SourceJoinedFunctionStatementsInvariant::MissingFlowStart(declaration),
        )?;
        self.expect_start_flow(start)?;
        if graph.container_end(declaration).is_some() {
            return Err(
                SourceJoinedFunctionStatementsInvariant::UnexpectedFlowEnd(declaration).into(),
            );
        }
        if graph.container_return(declaration).is_some() {
            return Err(
                SourceJoinedFunctionStatementsInvariant::UnexpectedReturnFlow(declaration).into(),
            );
        }
        let actual = graph.flow_container(syntax.joined_if.statement);
        if actual != Some(declaration) {
            return Err(
                SourceJoinedFunctionStatementsInvariant::InvalidFlowContainer {
                    node: syntax.joined_if.statement,
                    expected: declaration,
                    actual,
                }
                .into(),
            );
        }

        for (index, local) in syntax.leading.iter().enumerate() {
            let flow = self.joined_flow_at(local.name)?;
            self.expect_start_route(local.name, flow, &syntax.leading[..index], start)?;
        }
        let if_flow = self.joined_flow_at(syntax.joined_if.statement)?;
        self.expect_start_route(syntax.joined_if.statement, if_flow, &syntax.leading, start)?;
        let condition_flow = self.joined_flow_at(syntax.joined_if.condition_identifier)?;
        self.expect_start_route(
            syntax.joined_if.condition_identifier,
            condition_flow,
            &syntax.leading,
            start,
        )?;

        for (index, local) in syntax.joined_if.then_branch.locals.iter().enumerate() {
            let flow = self.joined_flow_at(local.name)?;
            self.expect_condition_route(
                local.name,
                flow,
                &syntax.joined_if.then_branch.locals[..index],
                true,
                &syntax.joined_if,
                &syntax.leading,
                start,
            )?;
        }
        for (index, local) in syntax.joined_if.else_branch.locals.iter().enumerate() {
            let flow = self.joined_flow_at(local.name)?;
            self.expect_condition_route(
                local.name,
                flow,
                &syntax.joined_if.else_branch.locals[..index],
                false,
                &syntax.joined_if,
                &syntax.leading,
                start,
            )?;
        }
        for (index, local) in syntax.trailing.iter().enumerate() {
            let flow = self.joined_flow_at(local.name)?;
            self.expect_join_route(local.name, flow, &syntax.trailing[..index], syntax, start)?;
        }
        let return_flow = self.joined_flow_at(syntax.return_statement)?;
        self.expect_join_route(
            syntax.return_statement,
            return_flow,
            &syntax.trailing,
            syntax,
            start,
        )?;
        Ok(())
    }

    fn joined_flow_at(
        &self,
        node: NodeRef,
    ) -> Result<FlowRef, SourceJoinedFunctionStatementsError> {
        self.bound
            .flow_at(node)
            .ok_or_else(|| SourceJoinedFunctionStatementsInvariant::MissingFlowPoint(node).into())
    }

    fn joined_flow_node(
        &self,
        flow: FlowRef,
    ) -> Result<&FlowNode, SourceJoinedFunctionStatementsError> {
        self.bound
            .flow_graph()
            .nodes()
            .get(flow)
            .ok_or_else(|| SourceJoinedFunctionStatementsInvariant::MissingFlowNode(flow).into())
    }

    fn expect_start_flow(&self, flow: FlowRef) -> Result<(), SourceJoinedFunctionStatementsError> {
        let node = self.joined_flow_node(flow)?;
        if joined_semantic_flow_flags(node.flags) != FlowFlags::START.bits()
            || node.payload.is_some()
            || node.antecedent.is_some()
            || !node.antecedents.is_empty()
        {
            return Err(SourceJoinedFunctionStatementsInvariant::InvalidFlowNode(flow).into());
        }
        Ok(())
    }

    fn expect_start_route(
        &self,
        point: NodeRef,
        flow: FlowRef,
        assignments: &[SourceLocalDeclarationSyntax],
        start: FlowRef,
    ) -> Result<(), SourceJoinedFunctionStatementsError> {
        let actual = self.peel_joined_assignments(flow, assignments)?;
        Self::expect_flow_point(point, actual, start)
    }

    #[allow(clippy::too_many_arguments)]
    fn expect_condition_route(
        &self,
        point: NodeRef,
        flow: FlowRef,
        branch_assignments: &[SourceLocalDeclarationSyntax],
        assume_true: bool,
        joined_if: &SourceJoinedIfSyntax,
        leading: &[SourceLocalDeclarationSyntax],
        start: FlowRef,
    ) -> Result<(), SourceJoinedFunctionStatementsError> {
        let condition_flow = self.peel_joined_assignments(flow, branch_assignments)?;
        let condition = self.joined_flow_node(condition_flow)?;
        let expected_flags = if assume_true {
            FlowFlags::TRUE_CONDITION
        } else {
            FlowFlags::FALSE_CONDITION
        };
        let Some(antecedent) = condition.antecedent else {
            return Err(
                SourceJoinedFunctionStatementsInvariant::InvalidFlowNode(condition_flow).into(),
            );
        };
        if joined_semantic_flow_flags(condition.flags) != expected_flags.bits()
            || condition.payload != Some(FlowNodePayload::Ast(joined_if.condition))
            || !condition.antecedents.is_empty()
        {
            return Err(
                SourceJoinedFunctionStatementsInvariant::InvalidFlowNode(condition_flow).into(),
            );
        }
        let actual = self.peel_joined_assignments(antecedent, leading)?;
        Self::expect_flow_point(point, actual, start)
    }

    fn expect_join_route(
        &self,
        point: NodeRef,
        flow: FlowRef,
        trailing_assignments: &[SourceLocalDeclarationSyntax],
        syntax: &SourceJoinedFunctionStatementsSyntax,
        start: FlowRef,
    ) -> Result<(), SourceJoinedFunctionStatementsError> {
        let join_flow = self.peel_joined_assignments(flow, trailing_assignments)?;
        let join = self.joined_flow_node(join_flow)?;
        if joined_semantic_flow_flags(join.flags) != FlowFlags::BRANCH_LABEL.bits()
            || join.payload.is_some()
            || join.antecedent.is_some()
            || join.antecedents.len() != 2
            || join.antecedents[0] == join.antecedents[1]
        {
            return Err(SourceJoinedFunctionStatementsInvariant::InvalidFlowNode(join_flow).into());
        }
        self.expect_condition_route(
            point,
            join.antecedents[0],
            &syntax.joined_if.then_branch.locals,
            true,
            &syntax.joined_if,
            &syntax.leading,
            start,
        )?;
        self.expect_condition_route(
            point,
            join.antecedents[1],
            &syntax.joined_if.else_branch.locals,
            false,
            &syntax.joined_if,
            &syntax.leading,
            start,
        )
    }

    fn peel_joined_assignments(
        &self,
        mut flow: FlowRef,
        assignments: &[SourceLocalDeclarationSyntax],
    ) -> Result<FlowRef, SourceJoinedFunctionStatementsError> {
        for assignment in assignments.iter().rev() {
            let node = self.joined_flow_node(flow)?;
            let Some(antecedent) = node.antecedent else {
                return Err(SourceJoinedFunctionStatementsInvariant::InvalidFlowNode(flow).into());
            };
            if joined_semantic_flow_flags(node.flags) != FlowFlags::ASSIGNMENT.bits()
                || node.payload != Some(FlowNodePayload::Ast(assignment.declaration))
                || !node.antecedents.is_empty()
            {
                return Err(SourceJoinedFunctionStatementsInvariant::InvalidFlowNode(flow).into());
            }
            flow = antecedent;
        }
        Ok(flow)
    }

    fn expect_flow_point(
        point: NodeRef,
        actual: FlowRef,
        expected: FlowRef,
    ) -> Result<(), SourceJoinedFunctionStatementsError> {
        if actual != expected {
            return Err(SourceJoinedFunctionStatementsInvariant::FlowPointMismatch {
                node: point,
                expected,
                actual,
            }
            .into());
        }
        Ok(())
    }
}

const fn joined_semantic_flow_flags(flags: FlowFlags) -> u32 {
    flags.bits() & !JOIN_FLOW_METADATA_BITS
}

fn range_contains(parent: ts_core::TextRange, child: ts_core::TextRange) -> bool {
    parent.start <= parent.end
        && child.start <= child.end
        && child.start >= parent.start
        && child.end <= parent.end
}

#[cfg(test)]
mod joined_tests {
    use ts_ast::{FileId, NodeData};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        DeclaredTypeHost, IntrinsicBootstrapOptions,
        production::GlobalMergeCompletion,
        source_callables::{SourceCallablePlan, plan_source_callable},
        source_flow::{SourceFlowAssignment, SourceFlowPlan},
    };

    const JOINED_SOURCE: &str = concat!(
        "type Choice = \"yes\" | \"\" | undefined;\n",
        "function joined(value: Choice): Choice {\n",
        "  const before: Choice = value;\n",
        "  if (((value))) {\n",
        "    const truthy: \"yes\" = value;\n",
        "  } else {\n",
        "    const falsy: \"\" | undefined = value;\n",
        "  }\n",
        "  const after: Choice = value;\n",
        "  return value;\n",
        "}\n",
    );

    struct JoinedFixture {
        parsed: ParseResult,
        file: FileId,
        bound: BoundFile,
        store: CanonicalTypeMapperStore,
    }

    impl JoinedFixture {
        fn new(source: &str, file: FileId) -> Self {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/source_joined_statements.ts\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
            let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
            let bound = files.remove(&file).unwrap();
            let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some()
            );
            store
                .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                })
                .unwrap();
            Self {
                parsed,
                file,
                bound,
                store,
            }
        }

        fn declaration(&self) -> NodeRef {
            let source = self.parsed.arena.get(self.parsed.source_file).unwrap();
            let NodeData::SourceFile(source) = &source.data else {
                panic!("expected source file")
            };
            source
                .statements
                .nodes
                .iter()
                .copied()
                .find(|statement| {
                    self.parsed
                        .arena
                        .get(*statement)
                        .is_some_and(|node| node.kind == SyntaxKind::FunctionDeclaration)
                })
                .map(|node| NodeRef::new(self.parsed.arena.id(), self.file, node))
                .expect("expected function declaration")
        }

        fn callable(&self) -> SourceCallablePlan {
            let declaration = self.declaration();
            let owner = self.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&self.parsed.arena, &self.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            plan_source_callable(&self.store, &host, declaration, owner, None).unwrap()
        }

        fn plan(
            &self,
        ) -> Result<SourceJoinedFunctionStatementsSyntax, SourceJoinedFunctionStatementsError>
        {
            let callable = self.callable();
            plan_source_joined_function_statements_syntax(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                &callable,
            )
        }

        fn linear_plan(
            &self,
        ) -> Result<SourceLinearFunctionStatementsSyntax, SourceFunctionStatementsError> {
            let callable = self.callable();
            plan_source_linear_function_statements_syntax(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                &callable,
            )
        }
    }

    #[test]
    fn linear_body_accepts_inferred_function_scoped_var_and_covers_final_assignment() {
        let fixture = JoinedFixture::new("function avoid() { var x = 1; }", FileId::new(1_190));
        let syntax = fixture.linear_plan().unwrap();
        assert_eq!(syntax.locals.len(), 1);
        assert_eq!(syntax.locals[0].binding, VariableBindingKind::Var);
        assert!(syntax.return_statement.is_none());
        assert!(syntax.return_expression.is_none());

        let assignments = syntax.locals.iter().map(|local| SourceFlowAssignment {
            declaration: local.declaration,
            symbol: local.symbol,
        });
        assert!(
            SourceFlowPlan::preflight(
                &fixture.bound,
                fixture.declaration(),
                None,
                syntax.locals.iter().map(|local| local.name),
                [],
                assignments,
            )
            .is_ok()
        );
    }

    #[test]
    fn linear_body_retains_ordered_locals_and_optional_final_return() {
        let returned = JoinedFixture::new(
            concat!(
                "function value(input: number): number {\n",
                "  const first: number = input;\n",
                "  var second: number = first;\n",
                "  return second;\n",
                "}\n",
            ),
            FileId::new(1_191),
        );
        let syntax = returned.linear_plan().unwrap();
        assert_eq!(syntax.locals.len(), 2);
        assert_eq!(syntax.locals[0].binding, VariableBindingKind::Const);
        assert_eq!(syntax.locals[1].binding, VariableBindingKind::Var);
        assert!(syntax.return_statement.is_some());
        assert!(syntax.return_expression.is_some());

        let bare = JoinedFixture::new(
            "function empty(): void { let value = 1; return; }",
            FileId::new(1_192),
        );
        let syntax = bare.linear_plan().unwrap();
        assert_eq!(syntax.locals.len(), 1);
        assert!(syntax.return_statement.is_some());
        assert!(syntax.return_expression.is_none());
    }

    #[test]
    fn linear_body_flattens_nested_lexical_blocks_and_empty_statements() {
        let fixture = JoinedFixture::new(
            concat!(
                "function nested(value: number): number {\n",
                "  ;\n",
                "  {\n",
                "    const first: number = value;\n",
                "    {\n",
                "      let second: number = first;\n",
                "      ;\n",
                "    }\n",
                "  }\n",
                "  const result: number = value;\n",
                "  return result;\n",
                "}\n",
            ),
            FileId::new(1_194),
        );
        let syntax = fixture.linear_plan().unwrap();
        assert_eq!(syntax.locals.len(), 3);
        assert_eq!(syntax.locals[0].binding, VariableBindingKind::Const);
        assert_eq!(syntax.locals[1].binding, VariableBindingKind::Let);
        assert_eq!(syntax.locals[2].binding, VariableBindingKind::Const);
        assert!(syntax.return_statement.is_some());
        assert!(syntax.return_expression.is_some());
    }

    #[test]
    fn linear_body_rejects_statements_after_return() {
        let fixture = JoinedFixture::new(
            "function invalid(): void { return; const later = 1; }",
            FileId::new(1_193),
        );
        assert!(matches!(
            fixture.linear_plan(),
            Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::Syntax {
                    role: SourceFunctionStatementsRole::BodyStatement,
                    ..
                },
            )),
        ));
    }

    #[test]
    fn top_level_if_retains_nested_export_grammar_diagnostic_and_token_range() {
        let source = "if (true) export type {};";
        let fixture = JoinedFixture::new(source, FileId::new(1_195));
        let statement = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::IfStatement).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let syntax = plan_source_control_if_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            statement,
            fixture.bound.source_file(),
        )
        .unwrap();
        assert_eq!(syntax.statement, statement);
        assert!(syntax.else_statement.is_none());
        let [diagnostic] = syntax.nested_export_diagnostics.as_slice() else {
            panic!("expected one nested export diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 1_233);
        assert_eq!(diagnostic.node, Some(syntax.then_statement));
        let range = diagnostic.range_override.unwrap().range();
        let start = usize::try_from(range.start.get()).unwrap();
        let end = usize::try_from(range.end.get()).unwrap();
        assert_eq!(source.get(start..end).unwrap(), "export",);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "An export declaration can only be used at the top level of a namespace or module.",
        );
    }

    #[test]
    fn top_level_if_keeps_ordered_block_branches_without_grammar_diagnostics() {
        let fixture = JoinedFixture::new("if (true) {} else {}", FileId::new(1_196));
        let statement = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::IfStatement).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let syntax = plan_source_control_if_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            statement,
            fixture.bound.source_file(),
        )
        .unwrap();
        assert!(syntax.else_statement.is_some());
        assert!(syntax.nested_export_diagnostics.is_empty());
    }

    #[test]
    fn joined_named_union_syntax_retains_exact_ordered_label_routes() {
        let fixture = JoinedFixture::new(JOINED_SOURCE, FileId::new(1_201));
        let syntax = fixture.plan().unwrap();
        assert_eq!(syntax.leading.len(), 1);
        assert_eq!(syntax.joined_if.then_branch.locals.len(), 1);
        assert_eq!(syntax.joined_if.else_branch.locals.len(), 1);
        assert_eq!(syntax.trailing.len(), 1);

        let join_flow = fixture.bound.flow_at(syntax.trailing[0].name).unwrap();
        let join = fixture.bound.flow_graph().nodes().get(join_flow).unwrap();
        assert_eq!(
            joined_semantic_flow_flags(join.flags),
            FlowFlags::BRANCH_LABEL.bits(),
        );
        assert!(join.payload.is_none());
        assert!(join.antecedent.is_none());
        let [then_flow, else_flow] = join.antecedents.as_slice() else {
            panic!("expected ordered then/else join antecedents")
        };
        let then_assignment = fixture.bound.flow_graph().nodes().get(*then_flow).unwrap();
        let else_assignment = fixture.bound.flow_graph().nodes().get(*else_flow).unwrap();
        assert_eq!(
            then_assignment.payload,
            Some(FlowNodePayload::Ast(
                syntax.joined_if.then_branch.locals[0].declaration,
            )),
        );
        assert_eq!(
            else_assignment.payload,
            Some(FlowNodePayload::Ast(
                syntax.joined_if.else_branch.locals[0].declaration,
            )),
        );
    }

    #[test]
    fn joined_typeof_syntax_retains_strict_comparison_and_binder_payload() {
        for (file, condition, comparison, type_of_on_left) in [
            (
                FileId::new(1_205),
                "typeof value === \"string\"",
                SourceTypeofComparison::Equal,
                true,
            ),
            (
                FileId::new(1_206),
                "\"number\" !== typeof value",
                SourceTypeofComparison::NotEqual,
                false,
            ),
            (
                FileId::new(1_209),
                "typeof value === `string`",
                SourceTypeofComparison::Equal,
                true,
            ),
            (
                FileId::new(1_213),
                "`number` !== typeof value",
                SourceTypeofComparison::NotEqual,
                false,
            ),
        ] {
            let source = format!(
                "function narrowed(value: string | number): string | number {{\n  if ({condition}) {{\n    const selected: string | number = value;\n  }} else {{\n    const rejected: string | number = value;\n  }}\n  return value;\n}}\n"
            );
            let fixture = JoinedFixture::new(&source, file);
            let syntax = fixture.plan().unwrap();
            let typeof_condition = syntax
                .joined_if
                .typeof_condition
                .expect("expected a retained typeof condition");
            assert_eq!(
                typeof_condition.identifier,
                syntax.joined_if.condition_identifier
            );
            assert_eq!(typeof_condition.comparison, comparison);
            assert_eq!(typeof_condition.type_of_on_left, type_of_on_left);

            for branch in [&syntax.joined_if.then_branch, &syntax.joined_if.else_branch] {
                let flow = fixture.bound.flow_at(branch.locals[0].name).unwrap();
                let flow = fixture.bound.flow_graph().nodes().get(flow).unwrap();
                assert_eq!(
                    flow.payload,
                    Some(FlowNodePayload::Ast(syntax.joined_if.condition)),
                );
            }
        }
    }

    #[test]
    fn joined_typeof_syntax_rejects_loose_comparisons_and_unknown_tags() {
        for (file, condition) in [
            (FileId::new(1_207), "typeof value == \"string\""),
            (FileId::new(1_208), "typeof value === \"decimal\""),
        ] {
            let source = format!(
                "function narrowed(value: string | number): string | number {{ if ({condition}) {{}} else {{}} return value; }}"
            );
            let fixture = JoinedFixture::new(&source, file);
            assert!(matches!(
                fixture.plan(),
                Err(SourceJoinedFunctionStatementsError::Statements(
                    SourceFunctionStatementsError::Unsupported(
                        SourceFunctionStatementsUnsupported::Syntax {
                            role: SourceFunctionStatementsRole::Condition,
                            ..
                        },
                    ),
                )),
            ));
        }
    }

    #[test]
    fn joined_shape_accepts_missing_else_and_function_scoped_var_locals() {
        let fixture = JoinedFixture::new(
            concat!(
                "function f(value: string | undefined): string | undefined {\n",
                "  var before: string | undefined = value;\n",
                "  if (value) {\n",
                "    const selected: string = value;\n",
                "  }\n",
                "  var after: string | undefined = value;\n",
                "  return value;\n",
                "}\n",
            ),
            FileId::new(1_210),
        );
        let syntax = fixture.plan().unwrap();
        assert_eq!(syntax.leading.len(), 1);
        assert_eq!(syntax.leading[0].binding, VariableBindingKind::Var);
        assert_eq!(syntax.joined_if.then_branch.locals.len(), 1);
        assert!(syntax.joined_if.else_branch.block.is_none());
        assert!(syntax.joined_if.else_branch.locals.is_empty());
        assert_eq!(syntax.trailing.len(), 1);
        assert_eq!(syntax.trailing[0].binding, VariableBindingKind::Var);
    }

    #[test]
    fn joined_branches_flatten_nested_blocks_in_binder_assignment_order() {
        let fixture = JoinedFixture::new(
            concat!(
                "function nested(value: string | undefined): string | undefined {\n",
                "  if (value) {\n",
                "    ;\n",
                "    { const selected: string = value; }\n",
                "  } else {\n",
                "    { const rejected: string | undefined = value; }\n",
                "    ;\n",
                "  }\n",
                "  return value;\n",
                "}\n",
            ),
            FileId::new(1_214),
        );
        let syntax = fixture.plan().unwrap();
        assert_eq!(syntax.joined_if.then_branch.locals.len(), 1);
        assert_eq!(syntax.joined_if.else_branch.locals.len(), 1);
    }

    #[test]
    fn final_if_flattens_nested_blocks_before_each_return() {
        let fixture = JoinedFixture::new(
            concat!(
                "function nested(value: string | undefined): string | undefined {\n",
                "  ;\n",
                "  { const initial: string | undefined = value; }\n",
                "  if (value) {\n",
                "    ;\n",
                "    { const selected: string = value; }\n",
                "    return value;\n",
                "  } else {\n",
                "    { const rejected: string | undefined = value; }\n",
                "    ;\n",
                "    return value;\n",
                "  }\n",
                "}\n",
            ),
            FileId::new(1_215),
        );
        let callable = fixture.callable();
        let syntax = plan_source_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();
        assert_eq!(syntax.leading.len(), 1);
        assert_eq!(syntax.final_if.then_branch.locals.len(), 1);
        assert_eq!(syntax.final_if.else_branch.locals.len(), 1);
    }

    #[test]
    fn joined_shape_rejects_branch_returns_and_nested_control() {
        for (file, source) in [
            (
                FileId::new(1_211),
                "function f(value: boolean): boolean { if (value) { return value; } else {} return value; }",
            ),
            (
                FileId::new(1_212),
                "function f(value: boolean): boolean { if (value) { if (value) {} } else {} return value; }",
            ),
        ] {
            let fixture = JoinedFixture::new(source, file);
            assert!(matches!(
                fixture.plan(),
                Err(SourceJoinedFunctionStatementsError::Statements(
                    SourceFunctionStatementsError::Unsupported(
                        SourceFunctionStatementsUnsupported::Syntax {
                            role: SourceFunctionStatementsRole::BranchStatement,
                            ..
                        },
                    ),
                )),
            ));
        }
    }

    #[test]
    fn joined_shape_rejects_foreign_callable_provenance() {
        let first = JoinedFixture::new(JOINED_SOURCE, FileId::new(1_220));
        let second = JoinedFixture::new(JOINED_SOURCE, FileId::new(1_220));
        let callable = first.callable();
        assert!(matches!(
            plan_source_joined_function_statements_syntax(
                &second.parsed.arena,
                &second.bound,
                &second.store,
                &callable,
            ),
            Err(SourceJoinedFunctionStatementsError::Statements(
                SourceFunctionStatementsError::Invariant(
                    SourceFunctionStatementsInvariant::BoundSourceMismatch(_),
                ),
            )),
        ));
    }
}
