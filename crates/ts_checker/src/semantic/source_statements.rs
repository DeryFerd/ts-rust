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
use ts_binder::{BoundFile, CheckFlags, SemanticSymbolId, SymbolFlags};
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

/// One inferred-void function whose sole branch declares a local const enum.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceConditionalEnumFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) control: SourceControlIfSyntax,
    pub(super) condition_identifier: NodeRef,
    pub(super) enum_declaration: NodeRef,
    pub(super) enum_symbol: SemanticSymbolId,
    pub(super) join_flow: FlowRef,
}

/// Loop families whose binder graph preserves source evaluation order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceControlLoopKind {
    While,
    DoWhile,
    For,
    ForIn,
    ForOf,
}

/// Proven loop children retained without evaluating their expressions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceControlLoopSyntax {
    pub(super) statement: NodeRef,
    pub(super) kind: SourceControlLoopKind,
    pub(super) initializer: Option<NodeRef>,
    pub(super) condition: Option<NodeRef>,
    pub(super) incrementor: Option<NodeRef>,
    pub(super) iterable: Option<NodeRef>,
    pub(super) body: NodeRef,
}

impl SourceControlLoopSyntax {
    /// Returns the loop's retained children in lexical source order.
    pub(super) fn ordered_nodes(&self) -> Vec<NodeRef> {
        if self.kind == SourceControlLoopKind::DoWhile {
            return std::iter::once(self.body).chain(self.condition).collect();
        }
        self.initializer
            .into_iter()
            .chain(self.condition)
            .chain(self.incrementor)
            .chain(self.iterable)
            .chain(std::iter::once(self.body))
            .collect()
    }
}

/// One ordered `case` or `default` clause in a proven switch statement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceControlSwitchClauseSyntax {
    pub(super) clause: NodeRef,
    pub(super) expression: Option<NodeRef>,
    pub(super) statements: Vec<NodeRef>,
    pub(super) unreachable_ranges: Vec<CanonicalCheckerDiagnosticRange>,
}

/// Proven switch expression and ordered case/default clause bodies.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceControlSwitchSyntax {
    pub(super) statement: NodeRef,
    pub(super) expression: NodeRef,
    pub(super) case_block: NodeRef,
    pub(super) clauses: Vec<SourceControlSwitchClauseSyntax>,
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

/// One supported statement retained in its original function-body order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceLinearFunctionStatementSyntax {
    Local(SourceLocalDeclarationSyntax),
    Function(NodeRef),
    Enum(SourceLocalEnumStatementSyntax),
    Expression {
        statement: NodeRef,
        expression: NodeRef,
    },
}

/// One function-owned enum, including the binder's reachability classification.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceLocalEnumStatementSyntax {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) is_const: bool,
    pub(super) unreachable: bool,
}

/// Ordered local statements with a return that can precede one unreachable enum.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceLinearFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) locals: Vec<SourceLocalDeclarationSyntax>,
    pub(super) statements: Vec<SourceLinearFunctionStatementSyntax>,
    pub(super) return_statement: Option<NodeRef>,
    pub(super) return_expression: Option<NodeRef>,
}

/// One value return owned directly by a grouped switch clause.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceSwitchReturnSyntax {
    pub(super) clause: NodeRef,
    pub(super) statement: NodeRef,
    pub(super) expression: NodeRef,
}

/// One function-body switch with literal cases and exhaustive value returns.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceSwitchFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) switch: SourceControlSwitchSyntax,
    pub(super) returns: Vec<SourceSwitchReturnSyntax>,
    /// A no-default edge that still requires canonical constraint coverage proof.
    pub(super) no_match_flow: Option<FlowRef>,
}

/// One grouped `typeof` case whose expression is followed by an unlabeled break.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceTypeofSwitchExpressionSyntax {
    pub(super) clause: NodeRef,
    pub(super) statement: NodeRef,
    pub(super) expression: NodeRef,
    pub(super) tag: SourceTypeofTag,
}

/// One inferred-void switch over a directly referenced function parameter.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceTypeofSwitchFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) switch: SourceControlSwitchSyntax,
    pub(super) identifier: NodeRef,
    pub(super) expressions: Vec<SourceTypeofSwitchExpressionSyntax>,
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

    let mut nested_export_diagnostics = Vec::new();
    for branch in std::iter::once(then_statement).chain(else_statement) {
        collect_nested_export_diagnostics(
            arena,
            bound,
            statement,
            branch,
            &mut nested_export_diagnostics,
        )?;
    }
    Ok(SourceControlIfSyntax {
        statement,
        condition,
        then_statement,
        else_statement,
        nested_export_diagnostics,
    })
}

/// Validates one loop and retains its source-ordered initializer and body.
pub(super) fn plan_source_control_loop_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    statement: NodeRef,
    expected_parent: NodeRef,
) -> Result<SourceControlLoopSyntax, SourceFunctionStatementsError> {
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || !expected_parent.is_for(arena.id(), bound.file_id())
    {
        return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(statement).into());
    }
    let record = control_statement_node(arena, bound, statement)?;
    if record.flags.0 != 0 {
        return Err(unsupported_control_statement(statement, record.kind));
    }
    let syntax = control_loop_shape(statement, record)?;
    let container = validate_control_statement_parent(arena, bound, statement, expected_parent)?;
    if bound.flow_graph().container_is_complete(container) != Some(true) {
        return Err(SourceFunctionStatementsError::Unsupported(
            SourceFunctionStatementsUnsupported::IncompleteFlow(container),
        ));
    }

    let mut previous = None;
    for child in syntax.ordered_nodes() {
        validate_control_statement_child(arena, bound, statement, child, container)?;
        if let Some(previous) = previous
            && control_statement_node(arena, bound, previous)?.range.end
                > control_statement_node(arena, bound, child)?.range.start
        {
            return Err(SourceFunctionStatementsInvariant::InvalidOrder {
                previous,
                next: child,
            }
            .into());
        }
        previous = Some(child);
    }
    Ok(syntax)
}

/// Validates a switch and retains every case/default clause in source order.
pub(super) fn plan_source_control_switch_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    statement: NodeRef,
    expected_parent: NodeRef,
) -> Result<SourceControlSwitchSyntax, SourceFunctionStatementsError> {
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || !expected_parent.is_for(arena.id(), bound.file_id())
    {
        return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(statement).into());
    }
    let record = control_statement_node(arena, bound, statement)?;
    let NodeData::SwitchStatement(data) = &record.data else {
        return Err(unsupported_control_statement(statement, record.kind));
    };
    if record.kind != SyntaxKind::SwitchStatement
        || record.flags.0 != 0
        || data.flow_node.is_some()
        || data.facts != 0
    {
        return Err(unsupported_control_statement(statement, record.kind));
    }
    let container = validate_control_statement_parent(arena, bound, statement, expected_parent)?;
    if bound.flow_graph().container_is_complete(container) != Some(true) {
        return Err(SourceFunctionStatementsError::Unsupported(
            SourceFunctionStatementsUnsupported::IncompleteFlow(container),
        ));
    }

    let expression = NodeRef::new(statement.arena, statement.file, data.expression);
    let case_block = NodeRef::new(statement.arena, statement.file, data.case_block);
    validate_control_statement_child(arena, bound, statement, expression, container)?;
    validate_control_statement_child(arena, bound, statement, case_block, container)?;
    if control_statement_node(arena, bound, expression)?.range.end
        > control_statement_node(arena, bound, case_block)?
            .range
            .start
    {
        return Err(SourceFunctionStatementsInvariant::InvalidOrder {
            previous: expression,
            next: case_block,
        }
        .into());
    }
    let clauses = plan_control_switch_clauses(arena, bound, case_block, container)?;
    Ok(SourceControlSwitchSyntax {
        statement,
        expression,
        case_block,
        clauses,
    })
}

fn plan_control_switch_clauses(
    arena: &NodeArena,
    bound: &BoundFile,
    case_block: NodeRef,
    container: NodeRef,
) -> Result<Vec<SourceControlSwitchClauseSyntax>, SourceFunctionStatementsError> {
    let record = control_statement_node(arena, bound, case_block)?;
    let NodeData::CaseBlock(data) = &record.data else {
        return Err(unsupported_control_statement(case_block, record.kind));
    };
    if record.kind != SyntaxKind::CaseBlock
        || record.flags.0 != 0
        || data.next_container.is_some()
        || data.clauses.has_trailing_comma
        || data.facts != 0
        || !range_contains(record.range, data.clauses.range)
    {
        return Err(unsupported_control_statement(case_block, record.kind));
    }

    let mut clauses = Vec::with_capacity(data.clauses.nodes.len());
    let mut previous = None;
    for node in &data.clauses.nodes {
        let clause = NodeRef::new(case_block.arena, case_block.file, *node);
        validate_control_statement_child(arena, bound, case_block, clause, container)?;
        if let Some(previous) = previous
            && control_statement_node(arena, bound, previous)?.range.end
                > control_statement_node(arena, bound, clause)?.range.start
        {
            return Err(SourceFunctionStatementsInvariant::InvalidOrder {
                previous,
                next: clause,
            }
            .into());
        }
        clauses.push(plan_control_switch_clause(arena, bound, clause, container)?);
        previous = Some(clause);
    }
    Ok(clauses)
}

fn plan_control_switch_clause(
    arena: &NodeArena,
    bound: &BoundFile,
    clause: NodeRef,
    container: NodeRef,
) -> Result<SourceControlSwitchClauseSyntax, SourceFunctionStatementsError> {
    let record = control_statement_node(arena, bound, clause)?;
    let NodeData::CaseOrDefaultClause(data) = &record.data else {
        return Err(unsupported_control_statement(clause, record.kind));
    };
    if !matches!(
        record.kind,
        SyntaxKind::CaseClause | SyntaxKind::DefaultClause
    ) || record.flags.0 != 0
        || data.fallthrough_flow_node.is_some()
        || data.statements.has_trailing_comma
        || data.facts != 0
        || data.statements.range.start > data.statements.range.end
    {
        return Err(unsupported_control_statement(clause, record.kind));
    }
    let expression = (record.kind == SyntaxKind::CaseClause)
        .then(|| NodeRef::new(clause.arena, clause.file, data.expression));
    if let Some(expression) = expression {
        validate_control_statement_child(arena, bound, clause, expression, container)?;
    }

    let mut statements = Vec::with_capacity(data.statements.nodes.len());
    let mut previous = expression;
    for node in &data.statements.nodes {
        let statement = NodeRef::new(clause.arena, clause.file, *node);
        validate_control_statement_child(arena, bound, clause, statement, container)?;
        if let Some(previous) = previous
            && control_statement_node(arena, bound, previous)?.range.end
                > control_statement_node(arena, bound, statement)?.range.start
        {
            return Err(SourceFunctionStatementsInvariant::InvalidOrder {
                previous,
                next: statement,
            }
            .into());
        }
        statements.push(statement);
        previous = Some(statement);
    }
    Ok(SourceControlSwitchClauseSyntax {
        clause,
        expression,
        unreachable_ranges: switch_clause_unreachable_ranges(arena, bound, clause, &statements)?,
        statements,
    })
}

fn switch_clause_unreachable_ranges(
    arena: &NodeArena,
    bound: &BoundFile,
    clause: NodeRef,
    statements: &[NodeRef],
) -> Result<Vec<CanonicalCheckerDiagnosticRange>, SourceFunctionStatementsError> {
    let mut ranges = Vec::new();
    let mut start = None;
    let mut end = None;
    for statement in statements {
        let record = control_statement_node(arena, bound, *statement)?;
        let range = record.range;
        let unreachable = match bound.flow_graph().is_unreachable(*statement) {
            Some(unreachable) => unreachable,
            None if matches!(
                record.kind,
                SyntaxKind::ExportDeclaration
                    | SyntaxKind::ImportDeclaration
                    | SyntaxKind::TypeAliasDeclaration
                    | SyntaxKind::InterfaceDeclaration
            ) =>
            {
                false
            }
            None => {
                return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                    node: *statement,
                    expected: bound.container(clause).unwrap_or(bound.source_file()),
                    actual: bound.flow_container(*statement),
                }
                .into());
            }
        };
        if unreachable {
            start.get_or_insert(range.start);
            end = Some(range.end);
        } else if let (Some(first), Some(last)) = (start.take(), end.take()) {
            ranges.push(CanonicalCheckerDiagnosticRange::new(
                clause,
                TextRange::new(first, last),
            ));
        }
    }
    if let (Some(first), Some(last)) = (start, end) {
        ranges.push(CanonicalCheckerDiagnosticRange::new(
            clause,
            TextRange::new(first, last),
        ));
    }
    Ok(ranges)
}

fn control_loop_shape(
    statement: NodeRef,
    record: &Node,
) -> Result<SourceControlLoopSyntax, SourceFunctionStatementsError> {
    let reference = |node| NodeRef::new(statement.arena, statement.file, node);
    let (kind, initializer, condition, incrementor, iterable, body) = match &record.data {
        NodeData::WhileStatement(data)
            if record.kind == SyntaxKind::WhileStatement
                && data.flow_node.is_none()
                && data.facts == 0 =>
        {
            (
                SourceControlLoopKind::While,
                None,
                Some(reference(data.expression)),
                None,
                None,
                reference(data.statement),
            )
        }
        NodeData::DoStatement(data)
            if record.kind == SyntaxKind::DoStatement
                && data.flow_node.is_none()
                && data.facts == 0 =>
        {
            (
                SourceControlLoopKind::DoWhile,
                None,
                Some(reference(data.expression)),
                None,
                None,
                reference(data.statement),
            )
        }
        NodeData::ForStatement(data)
            if record.kind == SyntaxKind::ForStatement
                && data.flow_node.is_none()
                && data.next_container.is_none()
                && data.facts == 0 =>
        {
            (
                SourceControlLoopKind::For,
                data.initializer.map(reference),
                data.condition.map(reference),
                data.incrementor.map(reference),
                None,
                reference(data.statement),
            )
        }
        NodeData::ForInOrOfStatement(data)
            if matches!(
                record.kind,
                SyntaxKind::ForInStatement | SyntaxKind::ForOfStatement
            ) && data.await_modifier.is_none()
                && data.flow_node.is_none()
                && data.next_container.is_none()
                && data.facts == 0 =>
        {
            (
                if record.kind == SyntaxKind::ForInStatement {
                    SourceControlLoopKind::ForIn
                } else {
                    SourceControlLoopKind::ForOf
                },
                Some(reference(data.initializer)),
                None,
                None,
                Some(reference(data.expression)),
                reference(data.statement),
            )
        }
        _ => return Err(unsupported_control_statement(statement, record.kind)),
    };
    Ok(SourceControlLoopSyntax {
        statement,
        kind,
        initializer,
        condition,
        incrementor,
        iterable,
        body,
    })
}

fn unsupported_control_statement(node: NodeRef, kind: SyntaxKind) -> SourceFunctionStatementsError {
    SourceFunctionStatementsError::Unsupported(SourceFunctionStatementsUnsupported::Syntax {
        node,
        kind,
        role: SourceFunctionStatementsRole::BodyStatement,
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

fn validate_labeled_statement(
    arena: &NodeArena,
    bound: &BoundFile,
    statement: NodeRef,
    expected_parent: NodeRef,
) -> Result<NodeRef, SourceFunctionStatementsError> {
    let record = control_statement_node(arena, bound, statement)?;
    let NodeData::LabeledStatement(labeled) = &record.data else {
        return Err(unsupported_control_statement(statement, record.kind));
    };
    if record.kind != SyntaxKind::LabeledStatement
        || record.flags.0 != 0
        || labeled.flow_node.is_some()
    {
        return Err(unsupported_control_statement(statement, record.kind));
    }

    let container = validate_control_statement_parent(arena, bound, statement, expected_parent)?;
    let label = NodeRef::new(statement.arena, statement.file, labeled.label);
    validate_control_statement_child(arena, bound, statement, label, container)?;
    let label_record = control_statement_node(arena, bound, label)?;
    let NodeData::Identifier(identifier) = &label_record.data else {
        return Err(unsupported_control_statement(label, label_record.kind));
    };
    if label_record.kind != SyntaxKind::Identifier
        || label_record.flags.0 != 0
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported_control_statement(label, label_record.kind));
    }

    let child = NodeRef::new(statement.arena, statement.file, labeled.statement);
    validate_control_statement_child(arena, bound, statement, child, container)?;
    if label_record.range.end > control_statement_node(arena, bound, child)?.range.start {
        return Err(SourceFunctionStatementsInvariant::InvalidOrder {
            previous: label,
            next: child,
        }
        .into());
    }

    let expected_scope = bound.block_scope_container(statement).ok_or(
        SourceFunctionStatementsInvariant::InvalidBlockScopeContainer {
            node: statement,
            expected: container,
            actual: None,
        },
    )?;
    for nested in [label, child] {
        let actual = bound.block_scope_container(nested);
        if actual != Some(expected_scope) {
            return Err(
                SourceFunctionStatementsInvariant::InvalidBlockScopeContainer {
                    node: nested,
                    expected: expected_scope,
                    actual,
                }
                .into(),
            );
        }
    }

    let mut ancestor = Some(expected_parent);
    while let Some(current) = ancestor {
        let current_record = control_statement_node(arena, bound, current)?;
        if matches!(
            current_record.kind,
            SyntaxKind::SourceFile
                | SyntaxKind::FunctionDeclaration
                | SyntaxKind::FunctionExpression
                | SyntaxKind::ArrowFunction
        ) {
            break;
        }
        if let NodeData::LabeledStatement(outer) = &current_record.data {
            let outer_label = NodeRef::new(current.arena, current.file, outer.label);
            let outer_record = control_statement_node(arena, bound, outer_label)?;
            let NodeData::Identifier(outer_identifier) = &outer_record.data else {
                return Err(unsupported_control_statement(
                    outer_label,
                    outer_record.kind,
                ));
            };
            if outer_identifier.text == identifier.text {
                return Err(unsupported_control_statement(statement, record.kind));
            }
        }
        ancestor = current_record
            .parent
            .map(|node| NodeRef::new(current.arena, current.file, node));
    }

    Ok(child)
}

/// Returns whether a branch contains only blocks, labels, and semicolon statements.
pub(super) fn source_control_branch_is_empty(
    arena: &NodeArena,
    bound: &BoundFile,
    statement: NodeRef,
) -> Result<bool, SourceFunctionStatementsError> {
    let record = control_statement_node(arena, bound, statement)?;
    match &record.data {
        NodeData::EmptyStatement(empty)
            if record.kind == SyntaxKind::EmptyStatement
                && record.flags.0 == 0
                && empty.flow_node.is_none() =>
        {
            Ok(true)
        }
        NodeData::Block(block)
            if record.kind == SyntaxKind::Block
                && record.flags.0 == 0
                && block.flow_node.is_none()
                && block.next_container.is_none()
                && !block.statements.has_trailing_comma
                && block.facts == 0 =>
        {
            if !range_contains(record.range, block.statements.range) {
                return Err(SourceFunctionStatementsInvariant::InvalidListRange(statement).into());
            }
            let container = bound.container(statement).ok_or(
                SourceFunctionStatementsInvariant::InvalidContainer {
                    node: statement,
                    expected: bound.source_file(),
                    actual: None,
                },
            )?;
            for child in &block.statements.nodes {
                let child = NodeRef::new(statement.arena, statement.file, *child);
                validate_control_statement_child(arena, bound, statement, child, container)?;
                if !source_control_branch_is_empty(arena, bound, child)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        NodeData::LabeledStatement(_) => {
            let parent = record
                .parent
                .map(|node| NodeRef::new(statement.arena, statement.file, node))
                .ok_or(SourceFunctionStatementsInvariant::InvalidParent {
                    node: statement,
                    expected: None,
                    actual: None,
                })?;
            let child = validate_labeled_statement(arena, bound, statement, parent)?;
            source_control_branch_is_empty(arena, bound, child)
        }
        NodeData::EmptyStatement(_) | NodeData::Block(_) => {
            Err(unsupported_control_statement(statement, record.kind))
        }
        _ => Ok(false),
    }
}

fn collect_nested_export_diagnostics(
    arena: &NodeArena,
    bound: &BoundFile,
    parent: NodeRef,
    statement: NodeRef,
    diagnostics: &mut Vec<CanonicalCheckerDiagnostic>,
) -> Result<(), SourceFunctionStatementsError> {
    if source_control_branch_is_empty(arena, bound, statement)? {
        return Ok(());
    }
    let record = control_statement_node(arena, bound, statement)?;
    match &record.data {
        NodeData::ExportDeclaration(_) => {
            let diagnostic = nested_export_declaration_diagnostic(arena, bound, statement)
                .ok_or_else(|| unsupported_control_statement(statement, record.kind))?;
            diagnostics.push(diagnostic);
        }
        NodeData::Block(block) => {
            if record.kind != SyntaxKind::Block
                || record.flags.0 != 0
                || block.flow_node.is_some()
                || block.next_container.is_some()
                || block.statements.has_trailing_comma
                || block.facts != 0
            {
                return Err(unsupported_control_statement(statement, record.kind));
            }
            let container = validate_control_statement_parent(arena, bound, statement, parent)?;
            if !range_contains(record.range, block.statements.range) {
                return Err(SourceFunctionStatementsInvariant::InvalidListRange(statement).into());
            }
            let mut previous = None;
            for node in &block.statements.nodes {
                let child = NodeRef::new(statement.arena, statement.file, *node);
                validate_control_statement_child(arena, bound, statement, child, container)?;
                if let Some(previous) = previous
                    && control_statement_node(arena, bound, previous)?.range.end
                        > control_statement_node(arena, bound, child)?.range.start
                {
                    return Err(SourceFunctionStatementsInvariant::InvalidOrder {
                        previous,
                        next: child,
                    }
                    .into());
                }
                collect_nested_export_diagnostics(arena, bound, statement, child, diagnostics)?;
                previous = Some(child);
            }
        }
        NodeData::IfStatement(_) => {
            let nested = plan_source_control_if_syntax(arena, bound, statement, parent)?;
            diagnostics.extend(nested.nested_export_diagnostics);
        }
        NodeData::LabeledStatement(_) => {
            let child = validate_labeled_statement(arena, bound, statement, parent)?;
            collect_nested_export_diagnostics(arena, bound, statement, child, diagnostics)?;
        }
        NodeData::WhileStatement(_)
        | NodeData::DoStatement(_)
        | NodeData::ForStatement(_)
        | NodeData::ForInOrOfStatement(_) => {
            let nested = plan_source_control_loop_syntax(arena, bound, statement, parent)?;
            debug_assert_eq!(nested.statement, statement);
            collect_nested_export_diagnostics(arena, bound, statement, nested.body, diagnostics)?;
        }
        NodeData::SwitchStatement(_) => {
            let nested = plan_source_control_switch_syntax(arena, bound, statement, parent)?;
            debug_assert_eq!(nested.statement, statement);
            debug_assert_ne!(nested.expression, nested.case_block);
            for clause in &nested.clauses {
                debug_assert!(
                    clause
                        .unreachable_ranges
                        .iter()
                        .all(|range| range.anchor() == clause.clause)
                );
                if let Some(expression) = clause.expression {
                    debug_assert!(control_statement_node(arena, bound, expression).is_ok());
                }
                for child in &clause.statements {
                    collect_nested_export_diagnostics(
                        arena,
                        bound,
                        clause.clause,
                        *child,
                        diagnostics,
                    )?;
                }
            }
        }
        _ => {}
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

/// Proves an inferred-void `if (parameter) const enum` function body.
pub(super) fn plan_source_conditional_enum_function_statements_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    callable: &SourceCallablePlan,
) -> Result<SourceConditionalEnumFunctionStatementsSyntax, SourceFunctionStatementsError> {
    SyntaxPlanner {
        arena,
        bound,
        store,
        callable,
    }
    .plan_conditional_enum()
}

/// Proves an exhaustive literal-case switch and its grouped binder-flow paths.
pub(super) fn plan_source_switch_function_statements_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    callable: &SourceCallablePlan,
) -> Result<SourceSwitchFunctionStatementsSyntax, SourceFunctionStatementsError> {
    SyntaxPlanner {
        arena,
        bound,
        store,
        callable,
    }
    .plan_switch()
}

/// Proves grouped `typeof` cases that contain one expression and an unlabeled break.
pub(super) fn plan_source_typeof_switch_function_statements_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    callable: &SourceCallablePlan,
) -> Result<SourceTypeofSwitchFunctionStatementsSyntax, SourceFunctionStatementsError> {
    SyntaxPlanner {
        arena,
        bound,
        store,
        callable,
    }
    .plan_typeof_switch()
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
    fn plan_typeof_switch(
        &self,
    ) -> Result<SourceTypeofSwitchFunctionStatementsSyntax, SourceFunctionStatementsError> {
        let declaration = self.callable.declaration;
        if !declaration.is_for(self.arena.id(), self.bound.file_id())
            || self.bound.node_arena_id() != self.arena.id()
            || self.bound.node_arena_revision() != self.arena.revision()
        {
            return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(declaration).into());
        }
        if self.callable.family != SourceCallableFamily::FunctionDeclaration
            || !self.callable.return_type.is_inferred()
            || !self.callable.type_parameters.is_empty()
        {
            return Err(self.unsupported(
                declaration,
                self.node(declaration)?.kind,
                SourceFunctionStatementsRole::Callable,
            ));
        }
        let [parameter] = self.callable.parameters.as_slice() else {
            return Err(self.unsupported(
                declaration,
                self.node(declaration)?.kind,
                SourceFunctionStatementsRole::Callable,
            ));
        };
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
            || function.type_.is_some()
            || self.bound.symbol(parameter.declaration) != Some(parameter.symbol)
        {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        }

        let body = self.callable.body;
        self.validate_range(body, declaration)?;
        let statements = self.plan_body(body, declaration)?;
        let [statement] = statements.as_slice() else {
            return Err(self.unsupported(
                body,
                self.node(body)?.kind,
                SourceFunctionStatementsRole::FunctionBody,
            ));
        };
        let switch = plan_source_control_switch_syntax(
            self.arena,
            self.bound,
            self.reference(*statement),
            body,
        )?;
        for node in [switch.statement, switch.expression, switch.case_block] {
            self.validate_block_scope_container(node, declaration)?;
        }

        let discriminant = self.node(switch.expression)?;
        let NodeData::TypeOfExpression(type_of) = &discriminant.data else {
            return Err(self.unsupported(
                switch.expression,
                discriminant.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        };
        if discriminant.kind != SyntaxKind::TypeOfExpression || discriminant.flags.0 != 0 {
            return Err(self.unsupported(
                switch.expression,
                discriminant.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        }
        let identifier = self.reference(type_of.expression);
        self.validate_parent(
            identifier,
            Some(switch.expression.node),
            SourceFunctionStatementsRole::Condition,
        )?;
        self.validate_range(identifier, switch.expression)?;
        self.validate_container(identifier, declaration)?;
        self.validate_block_scope_container(identifier, declaration)?;
        let identifier_record = self.node(identifier)?;
        let NodeData::Identifier(identifier_data) = &identifier_record.data else {
            return Err(self.unsupported(
                identifier,
                identifier_record.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        };
        let parameter_record = self.node(parameter.declaration)?;
        let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        };
        let parameter_name = self.reference(parameter_data.name);
        let parameter_name_record = self.node(parameter_name)?;
        let NodeData::Identifier(parameter_identifier) = &parameter_name_record.data else {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        };
        if identifier_record.kind != SyntaxKind::Identifier
            || identifier_record.flags.0 != 0
            || identifier_data.flow_node.is_some()
            || identifier_data.text != parameter_identifier.text
            || parameter_name_record.kind != SyntaxKind::Identifier
            || parameter_name_record.parent != Some(parameter.declaration.node)
        {
            return Err(self.unsupported(
                identifier,
                identifier_record.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        }

        let graph = self.bound.flow_graph();
        let start = graph.container_start(declaration).ok_or(
            SourceFunctionStatementsInvariant::MissingFlowStart(declaration),
        )?;
        if graph.container_is_complete(declaration) != Some(true)
            || graph.container_return(declaration).is_some()
            || graph.container_end(declaration).is_none()
            || self.switch_flow_at(switch.statement, declaration)? != start
            || self.switch_flow_at(identifier, declaration)? != start
        {
            return Err(Self::incomplete_switch_flow(switch.statement));
        }

        let mut expressions = Vec::new();
        let mut seen_cases = HashSet::new();
        let mut group_start = 0usize;
        for (index, clause) in switch.clauses.iter().enumerate() {
            self.validate_block_scope_container(clause.clause, switch.case_block)?;
            let Some(expression) = clause.expression else {
                return Err(self.unsupported(
                    clause.clause,
                    self.node(clause.clause)?.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            };
            self.validate_block_scope_container(expression, switch.case_block)?;
            let literal_record = self.node(expression)?;
            let NodeData::StringLiteral(literal) = &literal_record.data else {
                return Err(self.unsupported(
                    expression,
                    literal_record.kind,
                    SourceFunctionStatementsRole::Condition,
                ));
            };
            if literal_record.kind != SyntaxKind::StringLiteral
                || literal_record.flags.0 != 0
                || literal.token_flags.0 != 0
                || !seen_cases.insert(literal.text.as_str())
                || !clause.unreachable_ranges.is_empty()
            {
                return Err(self.unsupported(
                    expression,
                    literal_record.kind,
                    SourceFunctionStatementsRole::Condition,
                ));
            }
            if clause.statements.is_empty() {
                if index + 1 == switch.clauses.len() {
                    return Err(self.unsupported(
                        clause.clause,
                        self.node(clause.clause)?.kind,
                        SourceFunctionStatementsRole::BranchStatement,
                    ));
                }
                continue;
            }
            let [statement, break_statement] = clause.statements.as_slice() else {
                return Err(self.unsupported(
                    clause.statements[0],
                    self.node(clause.statements[0])?.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            };
            let tag = match literal.text.as_str() {
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
                        expression,
                        literal_record.kind,
                        SourceFunctionStatementsRole::Condition,
                    ));
                }
            };
            let statement_record = self.node(*statement)?;
            let NodeData::ExpressionStatement(expression_statement) = &statement_record.data else {
                return Err(self.unsupported(
                    *statement,
                    statement_record.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            };
            if statement_record.kind != SyntaxKind::ExpressionStatement
                || statement_record.flags.0 != 0
                || statement_record.parent != Some(clause.clause.node)
                || expression_statement.flow_node.is_some()
            {
                return Err(self.unsupported(
                    *statement,
                    statement_record.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            }
            self.validate_block_scope_container(*statement, switch.case_block)?;
            let value = self.reference(expression_statement.expression);
            self.validate_parent(
                value,
                Some(statement.node),
                SourceFunctionStatementsRole::BranchStatement,
            )?;
            self.validate_range(value, *statement)?;
            self.validate_container(value, declaration)?;
            self.validate_block_scope_container(value, switch.case_block)?;
            if self.node(value)?.kind != SyntaxKind::CallExpression {
                return Err(self.unsupported(
                    value,
                    self.node(value)?.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            }

            let break_record = self.node(*break_statement)?;
            let NodeData::BreakStatement(break_data) = &break_record.data else {
                return Err(self.unsupported(
                    *break_statement,
                    break_record.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            };
            if break_record.kind != SyntaxKind::BreakStatement
                || break_record.flags.0 != 0
                || break_record.parent != Some(clause.clause.node)
                || break_data.label.is_some()
                || break_data.flow_node.is_some()
            {
                return Err(self.unsupported(
                    *break_statement,
                    break_record.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            }
            self.validate_block_scope_container(*break_statement, switch.case_block)?;
            let statement_flow = self.switch_flow_at(*statement, declaration)?;
            let node = graph
                .nodes()
                .get(statement_flow)
                .ok_or_else(|| Self::incomplete_switch_flow(*statement))?;
            let clause_start =
                i32::try_from(group_start).map_err(|_| Self::incomplete_switch_flow(*statement))?;
            let clause_end =
                i32::try_from(index + 1).map_err(|_| Self::incomplete_switch_flow(*statement))?;
            if joined_semantic_flow_flags(node.flags) != FlowFlags::SWITCH_CLAUSE.bits()
                || node.payload
                    != Some(FlowNodePayload::SwitchClause {
                        switch_statement: switch.statement,
                        clause_start,
                        clause_end,
                    })
                || node.antecedent != Some(start)
                || !node.antecedents.is_empty()
            {
                return Err(Self::incomplete_switch_flow(*statement));
            }
            self.switch_flow_at(*break_statement, declaration)?;
            expressions.push(SourceTypeofSwitchExpressionSyntax {
                clause: clause.clause,
                statement: *statement,
                expression: value,
                tag,
            });
            group_start = index + 1;
        }
        if expressions.is_empty() {
            return Err(self.unsupported(
                switch.statement,
                SyntaxKind::SwitchStatement,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }

        Ok(SourceTypeofSwitchFunctionStatementsSyntax {
            body,
            switch,
            identifier,
            expressions,
        })
    }

    fn plan_conditional_enum(
        &self,
    ) -> Result<SourceConditionalEnumFunctionStatementsSyntax, SourceFunctionStatementsError> {
        let declaration = self.callable.declaration;
        if !declaration.is_for(self.arena.id(), self.bound.file_id())
            || self.bound.node_arena_id() != self.arena.id()
            || self.bound.node_arena_revision() != self.arena.revision()
        {
            return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(declaration).into());
        }
        if self.callable.family != SourceCallableFamily::FunctionDeclaration
            || !self.callable.return_type.is_inferred()
            || !self.callable.type_parameters.is_empty()
        {
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
            || function.type_.is_some()
        {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        }
        let [parameter] = self.callable.parameters.as_slice() else {
            return Err(self.unsupported(
                declaration,
                record.kind,
                SourceFunctionStatementsRole::Callable,
            ));
        };
        let parameter_record = self.node(parameter.declaration)?;
        let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
            return Err(self.unsupported(
                parameter.declaration,
                parameter_record.kind,
                SourceFunctionStatementsRole::Callable,
            ));
        };
        let parameter_name = self.reference(parameter_data.name);
        let parameter_name_record = self.node(parameter_name)?;
        let NodeData::Identifier(parameter_identifier) = &parameter_name_record.data else {
            return Err(self.unsupported(
                parameter_name,
                parameter_name_record.kind,
                SourceFunctionStatementsRole::Callable,
            ));
        };
        if parameter_name_record.kind != SyntaxKind::Identifier
            || parameter_name_record.parent != Some(parameter.declaration.node)
            || self.bound.symbol(parameter.declaration) != Some(parameter.symbol)
        {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        }

        let body = self.callable.body;
        self.validate_range(body, declaration)?;
        let statements = self.plan_body(body, declaration)?;
        let [statement] = statements.as_slice() else {
            return Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::MissingFinalIf(body),
            ));
        };
        let statement = self.reference(*statement);
        let control = plan_source_control_if_syntax(self.arena, self.bound, statement, body)?;
        if control.else_statement.is_some() || !control.nested_export_diagnostics.is_empty() {
            return Err(self.unsupported(
                statement,
                SyntaxKind::IfStatement,
                SourceFunctionStatementsRole::IfStatement,
            ));
        }
        self.validate_container(statement, declaration)?;
        self.validate_block_scope_container(statement, declaration)?;
        let condition = self.plan_condition(control.condition, declaration)?;
        if condition.identifier != control.condition || condition.typeof_condition.is_some() {
            return Err(self.unsupported(
                control.condition,
                self.node(control.condition)?.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        }
        let NodeData::Identifier(identifier) = &self.node(condition.identifier)?.data else {
            return Err(self.unsupported(
                condition.identifier,
                self.node(condition.identifier)?.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        };
        if identifier.text != parameter_identifier.text {
            return Err(self.unsupported(
                condition.identifier,
                SyntaxKind::Identifier,
                SourceFunctionStatementsRole::Condition,
            ));
        }

        let (enum_symbol, enum_name) =
            self.plan_embedded_const_enum(control.then_statement, control.statement, declaration)?;
        let join_flow = self.validate_conditional_enum_flow(&control, enum_name)?;

        Ok(SourceConditionalEnumFunctionStatementsSyntax {
            body,
            enum_declaration: control.then_statement,
            control,
            condition_identifier: condition.identifier,
            enum_symbol,
            join_flow,
        })
    }

    fn plan_embedded_const_enum(
        &self,
        declaration: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<(SemanticSymbolId, NodeRef), SourceFunctionStatementsError> {
        let record = self.node(declaration)?;
        let NodeData::EnumDeclaration(enumeration) = &record.data else {
            return Err(self.unsupported(
                declaration,
                record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        };
        if record.kind != SyntaxKind::EnumDeclaration
            || record.flags.0 != 0
            || record.parent != Some(parent.node)
            || enumeration.flow_node.is_some()
            || enumeration.local_symbol.is_some()
            || enumeration.symbol.is_some()
            || enumeration.facts != 0
            || enumeration.members.has_trailing_comma
        {
            return Err(self.unsupported(
                declaration,
                record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }
        self.validate_range(declaration, parent)?;
        self.validate_container(declaration, callable)?;
        self.validate_block_scope_container(declaration, callable)?;

        let Some(modifiers) = enumeration.modifiers.as_ref() else {
            return Err(self.unsupported(
                declaration,
                record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        };
        let [modifier] = modifiers.list.nodes.as_slice() else {
            return Err(self.unsupported(
                declaration,
                record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        };
        let modifier = self.reference(*modifier);
        let modifier_record = self.node(modifier)?;
        if modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
            || modifier_record.kind != SyntaxKind::ConstKeyword
            || modifier_record.flags.0 != 0
            || modifier_record.parent != Some(declaration.node)
            || !matches!(modifier_record.data, NodeData::Token(_))
        {
            return Err(self.unsupported(
                modifier,
                modifier_record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }
        self.validate_range(modifier, declaration)?;

        let name = self.reference(enumeration.name);
        let name_record = self.node(name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(self.unsupported(
                name,
                name_record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(declaration.node)
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
        {
            return Err(self.unsupported(
                name,
                name_record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }
        self.validate_range(name, declaration)?;
        self.validate_order(modifier, name)?;
        self.validate_container(name, declaration)?;
        self.validate_block_scope_container(name, declaration)?;

        let [member] = enumeration.members.nodes.as_slice() else {
            return Err(self.unsupported(
                declaration,
                record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        };
        let member = self.reference(*member);
        let member_record = self.node(member)?;
        let NodeData::EnumMember(member_data) = &member_record.data else {
            return Err(self.unsupported(
                member,
                member_record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        };
        if member_record.kind != SyntaxKind::EnumMember
            || member_record.flags.0 != 0
            || member_record.parent != Some(declaration.node)
            || member_data.postfix_token.is_some()
            || member_data.symbol.is_some()
            || member_data.facts != 0
            || member_data.modifiers.is_some()
        {
            return Err(self.unsupported(
                member,
                member_record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }
        self.validate_range(member, declaration)?;
        self.validate_container(member, declaration)?;
        self.validate_block_scope_container(member, declaration)?;
        let member_name = self.reference(member_data.name);
        let member_name_record = self.node(member_name)?;
        let NodeData::Identifier(member_identifier) = &member_name_record.data else {
            return Err(self.unsupported(
                member_name,
                member_name_record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        };
        if member_name_record.kind != SyntaxKind::Identifier
            || member_name_record.flags.0 != 0
            || member_name_record.parent != Some(member.node)
            || member_identifier.flow_node.is_some()
            || member_identifier.text.is_empty()
        {
            return Err(self.unsupported(
                member_name,
                member_name_record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }
        let initializer = member_data.initializer.map(|node| self.reference(node));
        let Some(initializer) = initializer else {
            return Err(self.unsupported(
                member,
                member_record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        };
        let initializer_record = self.node(initializer)?;
        let NodeData::NumericLiteral(literal) = &initializer_record.data else {
            return Err(self.unsupported(
                initializer,
                initializer_record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        };
        if initializer_record.kind != SyntaxKind::NumericLiteral
            || initializer_record.flags.0 != 0
            || initializer_record.parent != Some(member.node)
            || literal.token_flags.0 != 0
        {
            return Err(self.unsupported(
                initializer,
                initializer_record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }
        self.validate_range(member_name, member)?;
        self.validate_range(initializer, member)?;
        self.validate_order(member_name, initializer)?;

        let symbol = self.bound.symbol(declaration).ok_or(
            SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration),
        )?;
        let owner = self
            .store
            .symbol(symbol)
            .filter(|owner| {
                owner.flags() == SymbolFlags::CONST_ENUM
                    && owner.name().as_utf8() == Some(identifier.text.as_str())
                    && owner.value_declaration() == Some(declaration)
                    && self.store.get_merged_symbol(symbol) == Some(symbol)
            })
            .ok_or(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                declaration,
            ))?;
        if owner.declarations() != Some(&[declaration]) {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        }
        let locals = self
            .bound
            .locals(callable)
            .ok_or(SourceFunctionStatementsInvariant::MissingLocals(callable))?;
        let actual = self
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source(&identifier.text));
        if actual != Some(symbol) {
            return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                declaration,
                scope: callable,
                expected: symbol,
                actual,
            }
            .into());
        }
        Ok((symbol, name))
    }

    fn validate_conditional_enum_flow(
        &self,
        control: &SourceControlIfSyntax,
        enum_name: NodeRef,
    ) -> Result<FlowRef, SourceFunctionStatementsError> {
        let declaration = self.callable.declaration;
        let graph = self.bound.flow_graph();
        if graph.container_is_complete(declaration) != Some(true) {
            return Err(Self::incomplete_switch_flow(declaration));
        }
        let start = graph.container_start(declaration).ok_or(
            SourceFunctionStatementsInvariant::MissingFlowStart(declaration),
        )?;
        let start_node = graph
            .nodes()
            .get(start)
            .ok_or_else(|| Self::incomplete_switch_flow(declaration))?;
        if joined_semantic_flow_flags(start_node.flags) != FlowFlags::START.bits()
            || start_node.payload.is_some()
            || start_node.antecedent.is_some()
            || !start_node.antecedents.is_empty()
            || self.bound.flow_at(control.statement) != Some(start)
            || self.bound.flow_at(control.condition) != Some(start)
        {
            return Err(Self::incomplete_switch_flow(control.statement));
        }
        if graph.container_return(declaration).is_some() {
            return Err(
                SourceFunctionStatementsInvariant::UnexpectedReturnFlow(declaration).into(),
            );
        }
        let join_flow = graph
            .container_end(declaration)
            .ok_or_else(|| Self::incomplete_switch_flow(control.statement))?;
        let join = graph
            .nodes()
            .get(join_flow)
            .ok_or_else(|| Self::incomplete_switch_flow(control.statement))?;
        if joined_semantic_flow_flags(join.flags) != FlowFlags::BRANCH_LABEL.bits()
            || join.payload.is_some()
            || join.antecedent.is_some()
            || join.antecedents.len() != 2
            || join.antecedents[0] == join.antecedents[1]
        {
            return Err(Self::incomplete_switch_flow(control.statement));
        }
        for (edge, flags) in join
            .antecedents
            .iter()
            .copied()
            .zip([FlowFlags::TRUE_CONDITION, FlowFlags::FALSE_CONDITION])
        {
            let node = graph
                .nodes()
                .get(edge)
                .ok_or_else(|| Self::incomplete_switch_flow(control.statement))?;
            if joined_semantic_flow_flags(node.flags) != flags.bits()
                || node.payload != Some(FlowNodePayload::Ast(control.condition))
                || node.antecedent != Some(start)
                || !node.antecedents.is_empty()
            {
                return Err(Self::incomplete_switch_flow(control.statement));
            }
        }
        if self.bound.flow_container(enum_name) != Some(declaration)
            || self.bound.flow_at(enum_name) != Some(join.antecedents[0])
        {
            return Err(Self::incomplete_switch_flow(enum_name));
        }
        Ok(join_flow)
    }

    fn plan_switch(
        &self,
    ) -> Result<SourceSwitchFunctionStatementsSyntax, SourceFunctionStatementsError> {
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
        let [switch_id] = statements.as_slice() else {
            let statement = statements
                .first()
                .copied()
                .map_or(body, |node| self.reference(node));
            return Err(self.unsupported(
                statement,
                self.node(statement)?.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        };
        let switch = plan_source_control_switch_syntax(
            self.arena,
            self.bound,
            self.reference(*switch_id),
            body,
        )?;
        self.validate_block_scope_container(switch.statement, declaration)?;
        self.validate_block_scope_container(switch.expression, declaration)?;
        self.validate_block_scope_container(switch.case_block, declaration)?;

        let discriminant = self.node(switch.expression)?;
        let NodeData::Identifier(identifier) = &discriminant.data else {
            return Err(self.unsupported(
                switch.expression,
                discriminant.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        };
        if discriminant.kind != SyntaxKind::Identifier
            || discriminant.flags.0 != 0
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
        {
            return Err(self.unsupported(
                switch.expression,
                discriminant.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        }

        let has_default = switch
            .clauses
            .iter()
            .any(|clause| clause.expression.is_none());
        let returns = self.plan_switch_returns(&switch, declaration)?;
        if !has_default {
            self.validate_no_default_switch(&switch)?;
        }
        let no_match_flow = self.validate_switch_flow(&switch, &returns, has_default)?;

        Ok(SourceSwitchFunctionStatementsSyntax {
            body,
            switch,
            returns,
            no_match_flow,
        })
    }

    fn validate_switch_flow(
        &self,
        switch: &SourceControlSwitchSyntax,
        returns: &[SourceSwitchReturnSyntax],
        has_default: bool,
    ) -> Result<Option<FlowRef>, SourceFunctionStatementsError> {
        let declaration = self.callable.declaration;
        let flow = self.bound.flow_graph();
        if flow.container_is_complete(declaration) != Some(true) {
            return Err(Self::incomplete_switch_flow(declaration));
        }
        let start = flow.container_start(declaration).ok_or(
            SourceFunctionStatementsInvariant::MissingFlowStart(declaration),
        )?;
        let start_node = flow
            .nodes()
            .get(start)
            .ok_or_else(|| Self::incomplete_switch_flow(declaration))?;
        if joined_semantic_flow_flags(start_node.flags) != FlowFlags::START.bits()
            || start_node.payload.is_some()
            || start_node.antecedent.is_some()
            || !start_node.antecedents.is_empty()
        {
            return Err(Self::incomplete_switch_flow(declaration));
        }
        if has_default && flow.container_end(declaration).is_some() {
            return Err(SourceFunctionStatementsInvariant::UnexpectedFlowEnd(declaration).into());
        }
        if flow.container_return(declaration).is_some() {
            return Err(
                SourceFunctionStatementsInvariant::UnexpectedReturnFlow(declaration).into(),
            );
        }

        let switch_flow = self.switch_flow_at(switch.statement, declaration)?;
        if self.switch_flow_at(switch.expression, declaration)? != switch_flow {
            return Err(Self::incomplete_switch_flow(switch.expression));
        }

        let mut returned_clauses = returns.iter();
        let mut group_start = 0;
        for (index, clause) in switch.clauses.iter().enumerate() {
            if flow.fallthrough_flow_at(clause.clause).is_some() {
                return Err(Self::incomplete_switch_flow(clause.clause));
            }
            if clause.statements.is_empty() {
                continue;
            }

            let Some(value) = returned_clauses.next() else {
                return Err(Self::incomplete_switch_flow(clause.clause));
            };
            if value.clause != clause.clause {
                return Err(Self::incomplete_switch_flow(value.statement));
            }
            let return_flow = self.switch_flow_at(value.statement, declaration)?;
            let return_node = flow
                .nodes()
                .get(return_flow)
                .ok_or_else(|| Self::incomplete_switch_flow(value.statement))?;
            let clause_start = i32::try_from(group_start)
                .map_err(|_| Self::incomplete_switch_flow(value.statement))?;
            let clause_end = i32::try_from(index + 1)
                .map_err(|_| Self::incomplete_switch_flow(value.statement))?;
            let payload = FlowNodePayload::SwitchClause {
                switch_statement: switch.statement,
                clause_start,
                clause_end,
            };
            if joined_semantic_flow_flags(return_node.flags) != FlowFlags::SWITCH_CLAUSE.bits()
                || return_node.payload.as_ref() != Some(&payload)
                || return_node.antecedent != Some(switch_flow)
                || !return_node.antecedents.is_empty()
            {
                return Err(Self::incomplete_switch_flow(value.statement));
            }
            group_start = index + 1;
        }
        if returned_clauses.next().is_some() {
            return Err(Self::incomplete_switch_flow(switch.statement));
        }

        let no_match_flow = if has_default {
            None
        } else {
            let no_match_flow = flow
                .container_end(declaration)
                .ok_or_else(|| Self::incomplete_switch_flow(switch.statement))?;
            let no_match = flow
                .nodes()
                .get(no_match_flow)
                .ok_or_else(|| Self::incomplete_switch_flow(switch.statement))?;
            let payload = FlowNodePayload::SwitchClause {
                switch_statement: switch.statement,
                clause_start: 0,
                clause_end: 0,
            };
            if joined_semantic_flow_flags(no_match.flags) != FlowFlags::SWITCH_CLAUSE.bits()
                || no_match.payload.as_ref() != Some(&payload)
                || no_match.antecedent != Some(switch_flow)
                || !no_match.antecedents.is_empty()
            {
                return Err(Self::incomplete_switch_flow(switch.statement));
            }
            Some(no_match_flow)
        };
        Ok(no_match_flow)
    }

    fn validate_no_default_switch(
        &self,
        switch: &SourceControlSwitchSyntax,
    ) -> Result<(), SourceFunctionStatementsError> {
        let [type_parameter] = self.callable.type_parameters.as_slice() else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        let [parameter] = self.callable.parameters.as_slice() else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        if !self
            .callable
            .type_parameter_syntax
            .generic_fixed_return_is_exact()
            || self.bound.symbol(type_parameter.declaration) != Some(type_parameter.symbol)
            || self.bound.symbol(parameter.declaration) != Some(parameter.symbol)
        {
            return Err(Self::missing_switch_return(switch.statement));
        }

        let parameter_record = self.node(parameter.declaration)?;
        let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        let parameter_name = self.reference(parameter_data.name);
        let parameter_name_record = self.node(parameter_name)?;
        let NodeData::Identifier(parameter_identifier) = &parameter_name_record.data else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        let discriminant = self.node(switch.expression)?;
        let NodeData::Identifier(discriminant_identifier) = &discriminant.data else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        if parameter_name_record.kind != SyntaxKind::Identifier
            || parameter_name_record.parent != Some(parameter.declaration.node)
            || parameter_identifier.text != discriminant_identifier.text
        {
            return Err(Self::missing_switch_return(switch.statement));
        }

        let Some(annotation) = parameter.explicit_type_node() else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        let annotation_record = self.node(annotation)?;
        let NodeData::TypeReferenceNode(annotation_data) = &annotation_record.data else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        if annotation_record.kind != SyntaxKind::TypeReference
            || annotation_record.parent != Some(parameter.declaration.node)
            || annotation_data.type_arguments.is_some()
        {
            return Err(Self::missing_switch_return(switch.statement));
        }
        let annotation_name = self.reference(annotation_data.type_name);
        let annotation_name_record = self.node(annotation_name)?;
        let NodeData::Identifier(annotation_identifier) = &annotation_name_record.data else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        let type_parameter_record = self.node(type_parameter.declaration)?;
        let NodeData::TypeParameterDeclaration(type_parameter_data) = &type_parameter_record.data
        else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        let type_parameter_name = self.reference(type_parameter_data.name);
        let type_parameter_name_record = self.node(type_parameter_name)?;
        let NodeData::Identifier(type_parameter_identifier) = &type_parameter_name_record.data
        else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        if annotation_name_record.kind != SyntaxKind::Identifier
            || annotation_name_record.parent != Some(annotation.node)
            || type_parameter_name_record.kind != SyntaxKind::Identifier
            || type_parameter_name_record.parent != Some(type_parameter.declaration.node)
            || annotation_identifier.text != type_parameter_identifier.text
        {
            return Err(Self::missing_switch_return(switch.statement));
        }

        let Some(constraint) = type_parameter.constraint else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        let constraint_record = self.node(constraint)?;
        let NodeData::TypeOperatorNode(operator) = &constraint_record.data else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        if constraint_record.kind != SyntaxKind::TypeOperator
            || constraint_record.parent != Some(type_parameter.declaration.node)
            || operator.operator != SyntaxKind::KeyOfKeyword
        {
            return Err(Self::missing_switch_return(switch.statement));
        }
        let target = self.reference(operator.type_);
        let target_record = self.node(target)?;
        let NodeData::TypeReferenceNode(target_data) = &target_record.data else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        if target_record.kind != SyntaxKind::TypeReference
            || target_record.parent != Some(constraint.node)
            || target_data.type_arguments.is_some()
        {
            return Err(Self::missing_switch_return(switch.statement));
        }
        let target_name = self.reference(target_data.type_name);
        let target_name_record = self.node(target_name)?;
        let NodeData::Identifier(target_identifier) = &target_name_record.data else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        if target_name_record.kind != SyntaxKind::Identifier
            || target_name_record.parent != Some(target.node)
        {
            return Err(Self::missing_switch_return(switch.statement));
        }

        let source = self.bound.source_file();
        let interface_symbol = self
            .bound
            .locals(source)
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&target_identifier.text))
            .and_then(|symbol| self.store.get_merged_symbol(symbol))
            .and_then(|symbol| self.store.symbol(symbol))
            .filter(|symbol| symbol.flags() == SymbolFlags::INTERFACE)
            .ok_or_else(|| Self::missing_switch_return(switch.statement))?;
        let Some([interface]) = interface_symbol.declarations() else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        let interface_record = self.node(*interface)?;
        let NodeData::InterfaceDeclaration(interface_data) = &interface_record.data else {
            return Err(Self::missing_switch_return(switch.statement));
        };
        if interface_record.kind != SyntaxKind::InterfaceDeclaration
            || interface_record.parent != Some(source.node)
            || interface_data.heritage_clauses.is_some()
            || interface_data.type_parameters.is_some()
            || interface_data.members.nodes.is_empty()
        {
            return Err(Self::missing_switch_return(switch.statement));
        }

        let mut keys = HashSet::with_capacity(interface_data.members.nodes.len());
        for member_id in &interface_data.members.nodes {
            let member = self.reference(*member_id);
            let member_record = self.node(member)?;
            if member_record.parent != Some(interface.node) {
                return Err(Self::missing_switch_return(switch.statement));
            }
            let property_name = match &member_record.data {
                NodeData::PropertyDeclaration(property)
                    if member_record.kind == SyntaxKind::PropertyDeclaration
                        && property.initializer.is_none()
                        && property.type_.is_some()
                        && property.symbol.is_none()
                        && property.facts == 0 =>
                {
                    self.reference(property.name)
                }
                NodeData::PropertySignatureDeclaration(property)
                    if member_record.kind == SyntaxKind::PropertySignature
                        && property.symbol.is_none() =>
                {
                    self.reference(property.name)
                }
                _ => return Err(Self::missing_switch_return(switch.statement)),
            };
            let property_name_record = self.node(property_name)?;
            let NodeData::Identifier(property_identifier) = &property_name_record.data else {
                return Err(Self::missing_switch_return(switch.statement));
            };
            if property_name_record.kind != SyntaxKind::Identifier
                || property_name_record.parent != Some(member.node)
                || !keys.insert(property_identifier.text.as_str())
            {
                return Err(Self::missing_switch_return(switch.statement));
            }
        }

        let mut cases = HashSet::with_capacity(switch.clauses.len());
        for clause in &switch.clauses {
            let Some(expression) = clause.expression else {
                return Err(Self::missing_switch_return(switch.statement));
            };
            let record = self.node(expression)?;
            let NodeData::StringLiteral(literal) = &record.data else {
                return Err(self.unsupported(
                    expression,
                    record.kind,
                    SourceFunctionStatementsRole::Condition,
                ));
            };
            if !cases.insert(literal.text.as_str()) {
                return Err(self.unsupported(
                    expression,
                    record.kind,
                    SourceFunctionStatementsRole::Condition,
                ));
            }
        }
        if cases != keys {
            return Err(Self::missing_switch_return(switch.statement));
        }
        Ok(())
    }

    fn missing_switch_return(node: NodeRef) -> SourceFunctionStatementsError {
        SourceFunctionStatementsError::Unsupported(
            SourceFunctionStatementsUnsupported::MissingReturn(node),
        )
    }

    fn switch_flow_at(
        &self,
        node: NodeRef,
        callable: NodeRef,
    ) -> Result<FlowRef, SourceFunctionStatementsError> {
        let actual = self.bound.flow_container(node);
        if actual != Some(callable) {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node,
                expected: callable,
                actual,
            }
            .into());
        }
        self.bound
            .flow_at(node)
            .ok_or_else(|| Self::incomplete_switch_flow(node))
    }

    fn incomplete_switch_flow(node: NodeRef) -> SourceFunctionStatementsError {
        SourceFunctionStatementsError::Unsupported(
            SourceFunctionStatementsUnsupported::IncompleteFlow(node),
        )
    }

    fn plan_switch_returns(
        &self,
        switch: &SourceControlSwitchSyntax,
        declaration: NodeRef,
    ) -> Result<Vec<SourceSwitchReturnSyntax>, SourceFunctionStatementsError> {
        let mut returns = Vec::new();
        let mut has_default = false;
        for (index, clause) in switch.clauses.iter().enumerate() {
            self.validate_block_scope_container(clause.clause, switch.case_block)?;
            if let Some(expression) = clause.expression {
                self.validate_block_scope_container(expression, switch.case_block)?;
                self.validate_switch_literal(expression, SourceFunctionStatementsRole::Condition)?;
            } else if has_default || index + 1 != switch.clauses.len() {
                return Err(self.unsupported(
                    clause.clause,
                    self.node(clause.clause)?.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            } else {
                has_default = true;
            }

            if !clause.unreachable_ranges.is_empty() {
                return Err(self.unsupported(
                    clause.clause,
                    self.node(clause.clause)?.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            }
            match clause.statements.as_slice() {
                [] if index + 1 != switch.clauses.len() => {}
                [statement] => returns.push(self.plan_switch_return(
                    clause.clause,
                    *statement,
                    switch.case_block,
                    declaration,
                )?),
                [] => {
                    return Err(SourceFunctionStatementsError::Unsupported(
                        SourceFunctionStatementsUnsupported::MissingReturn(clause.clause),
                    ));
                }
                [statement, ..] => {
                    return Err(self.unsupported(
                        *statement,
                        self.node(*statement)?.kind,
                        SourceFunctionStatementsRole::BranchStatement,
                    ));
                }
            }
        }
        if returns.is_empty() {
            return Err(Self::missing_switch_return(switch.statement));
        }
        Ok(returns)
    }

    fn plan_switch_return(
        &self,
        clause: NodeRef,
        statement: NodeRef,
        scope: NodeRef,
        callable: NodeRef,
    ) -> Result<SourceSwitchReturnSyntax, SourceFunctionStatementsError> {
        let record = self.node(statement)?;
        let NodeData::ReturnStatement(data) = &record.data else {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::ReturnStatement,
            ));
        };
        if record.kind != SyntaxKind::ReturnStatement
            || record.flags.0 != 0
            || record.parent != Some(clause.node)
            || data.flow_node.is_some()
            || data.facts != 0
        {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::ReturnStatement,
            ));
        }
        self.validate_range(statement, clause)?;
        self.validate_container(statement, callable)?;
        self.validate_block_scope_container(statement, scope)?;
        if self.bound.flow_container(statement) != Some(callable) {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: statement,
                expected: callable,
                actual: self.bound.flow_container(statement),
            }
            .into());
        }

        let expression = data.expression.map(|node| self.reference(node)).ok_or(
            SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::MissingReturn(statement),
            ),
        )?;
        self.validate_parent(
            expression,
            Some(statement.node),
            SourceFunctionStatementsRole::ReturnExpression,
        )?;
        self.validate_range(expression, statement)?;
        self.validate_container(expression, callable)?;
        self.validate_block_scope_container(expression, scope)?;
        self.validate_switch_literal(expression, SourceFunctionStatementsRole::ReturnExpression)?;
        Ok(SourceSwitchReturnSyntax {
            clause,
            statement,
            expression,
        })
    }

    fn validate_switch_literal(
        &self,
        expression: NodeRef,
        role: SourceFunctionStatementsRole,
    ) -> Result<(), SourceFunctionStatementsError> {
        let record = self.node(expression)?;
        let supported = match &record.data {
            NodeData::NumericLiteral(literal) => {
                record.kind == SyntaxKind::NumericLiteral && literal.token_flags.0 == 0
            }
            NodeData::StringLiteral(literal) => {
                record.kind == SyntaxKind::StringLiteral && literal.token_flags.0 == 0
            }
            NodeData::KeywordExpression(keyword) => {
                matches!(
                    record.kind,
                    SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword
                ) && keyword.flow_node.is_none()
            }
            _ => false,
        };
        if record.flags.0 != 0 || !supported {
            return Err(self.unsupported(expression, record.kind, role));
        }
        Ok(())
    }

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
        let body_statements = self.plan_body(body, declaration)?;
        let mut locals = Vec::new();
        let mut statements = Vec::new();
        let mut return_statement = None;
        let mut return_expression = None;
        for (index, statement_id) in body_statements.iter().copied().enumerate() {
            let statement = self.reference(statement_id);
            match self.node(statement)?.kind {
                SyntaxKind::VariableStatement
                | SyntaxKind::Block
                | SyntaxKind::EmptyStatement
                | SyntaxKind::LabeledStatement => {
                    let declarations =
                        self.plan_local_or_block_statement(statement, body, declaration)?;
                    statements.extend(
                        declarations
                            .iter()
                            .copied()
                            .map(SourceLinearFunctionStatementSyntax::Local),
                    );
                    locals.extend(declarations);
                }
                SyntaxKind::FunctionDeclaration => {
                    statements.push(SourceLinearFunctionStatementSyntax::Function(
                        self.plan_nested_function_statement(statement, body, declaration)?,
                    ));
                }
                SyntaxKind::EnumDeclaration
                    if index + 1 == body_statements.len()
                        && return_statement.is_some()
                        && return_expression.is_some() =>
                {
                    statements.push(SourceLinearFunctionStatementSyntax::Enum(
                        self.plan_linear_enum_statement(statement, body, declaration)?,
                    ));
                }
                SyntaxKind::ExpressionStatement => {
                    let expression =
                        self.plan_linear_expression_statement(statement, body, declaration)?;
                    statements.push(SourceLinearFunctionStatementSyntax::Expression {
                        statement,
                        expression,
                    });
                }
                SyntaxKind::ReturnStatement
                    if index + 1 == body_statements.len()
                        || index + 2 == body_statements.len()
                            && self.node(self.reference(body_statements[index + 1]))?.kind
                                == SyntaxKind::EnumDeclaration =>
                {
                    return_expression = self.plan_linear_return(statement, body, declaration)?;
                    if index + 1 != body_statements.len() && return_expression.is_none() {
                        return Err(self.unsupported(
                            statement,
                            SyntaxKind::ReturnStatement,
                            SourceFunctionStatementsRole::BodyStatement,
                        ));
                    }
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
            statements,
            return_statement,
            return_expression,
        })
    }

    fn plan_linear_enum_statement(
        &self,
        declaration: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<SourceLocalEnumStatementSyntax, SourceFunctionStatementsError> {
        let record = self.node(declaration)?;
        let NodeData::EnumDeclaration(enumeration) = &record.data else {
            return Err(self.unsupported(
                declaration,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        };
        if record.kind != SyntaxKind::EnumDeclaration
            || record.flags.0 != 0
            || record.parent != Some(parent.node)
            || enumeration.flow_node.is_some()
            || enumeration.local_symbol.is_some()
            || enumeration.symbol.is_some()
            || enumeration.facts != 0
        {
            return Err(self.unsupported(
                declaration,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }
        self.validate_range(declaration, parent)?;
        self.validate_container(declaration, callable)?;
        self.validate_block_scope_container(declaration, callable)?;
        self.validate_node_list(
            declaration,
            enumeration.members.range,
            &enumeration.members.nodes,
        )?;

        let name = self.reference(enumeration.name);
        let name_record = self.node(name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(self.unsupported(
                name,
                name_record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
        {
            return Err(self.unsupported(
                name,
                name_record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }
        self.validate_parent(
            name,
            Some(declaration.node),
            SourceFunctionStatementsRole::BodyStatement,
        )?;
        self.validate_range(name, declaration)?;
        self.validate_container(name, declaration)?;
        self.validate_block_scope_container(name, declaration)?;

        let is_const = if let Some(modifiers) = &enumeration.modifiers {
            let [modifier] = modifiers.list.nodes.as_slice() else {
                return Err(self.unsupported(
                    declaration,
                    record.kind,
                    SourceFunctionStatementsRole::BodyStatement,
                ));
            };
            let modifier = self.reference(*modifier);
            let modifier_record = self.node(modifier)?;
            if modifiers.flags.0 != 0
                || modifiers.list.has_trailing_comma
                || modifier_record.kind != SyntaxKind::ConstKeyword
                || modifier_record.flags.0 != 0
                || modifier_record.parent != Some(declaration.node)
                || !matches!(modifier_record.data, NodeData::Token(_))
            {
                return Err(self.unsupported(
                    modifier,
                    modifier_record.kind,
                    SourceFunctionStatementsRole::BodyStatement,
                ));
            }
            self.validate_range(modifier, declaration)?;
            self.validate_order(modifier, name)?;
            true
        } else {
            false
        };

        let symbol = self.bound.symbol(declaration).ok_or(
            SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration),
        )?;
        let expected_flags = if is_const {
            SymbolFlags::CONST_ENUM
        } else {
            SymbolFlags::REGULAR_ENUM
        };
        let owner = self
            .store
            .symbol(symbol)
            .filter(|owner| {
                owner.flags() == expected_flags
                    && owner.check_flags() == CheckFlags::NONE
                    && owner.name().as_utf8() == Some(identifier.text.as_str())
                    && owner.declarations() == Some(&[declaration])
                    && owner.value_declaration() == Some(declaration)
                    && owner.parent().is_none()
                    && owner.export_symbol().is_none()
                    && self.store.get_merged_symbol(symbol) == Some(symbol)
            })
            .ok_or(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                declaration,
            ))?;
        if self.bound.local_symbol(declaration).is_some() || owner.members().is_some() {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        }
        let locals = self
            .bound
            .locals(callable)
            .ok_or(SourceFunctionStatementsInvariant::MissingLocals(callable))?;
        let actual = self
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source(&identifier.text));
        if actual != Some(symbol) {
            return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                declaration,
                scope: callable,
                expected: symbol,
                actual,
            }
            .into());
        }

        for member in &enumeration.members.nodes {
            let member = self.reference(*member);
            self.validate_parent(
                member,
                Some(declaration.node),
                SourceFunctionStatementsRole::BodyStatement,
            )?;
            self.validate_container(member, declaration)?;
            self.validate_block_scope_container(member, declaration)?;
            let member_symbol = self.bound.symbol(member).ok_or(
                SourceFunctionStatementsInvariant::InvalidCallableEdge(member),
            )?;
            if self.store.symbol(member_symbol).is_none_or(|record| {
                record.flags() != SymbolFlags::ENUM_MEMBER || record.parent() != Some(symbol)
            }) {
                return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(member).into());
            }
        }

        let flow = self.bound.flow_graph();
        let actual = self.bound.flow_container(declaration);
        if actual != Some(callable)
            || flow.is_unreachable(declaration) != Some(true)
            || self.bound.flow_at(declaration).is_some()
        {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: declaration,
                expected: callable,
                actual,
            }
            .into());
        }

        Ok(SourceLocalEnumStatementSyntax {
            declaration,
            symbol,
            is_const,
            unreachable: true,
        })
    }

    fn plan_nested_function_statement(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<NodeRef, SourceFunctionStatementsError> {
        let record = self.node(statement)?;
        let NodeData::FunctionDeclaration(function) = &record.data else {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        };
        if record.kind != SyntaxKind::FunctionDeclaration
            || record.flags.0 != 0
            || record.parent != Some(parent.node)
            || function.modifiers.is_some()
            || function.asterisk_token.is_some()
            || function.type_parameters.is_some()
            || !function.parameters.nodes.is_empty()
            || function.parameters.has_trailing_comma
            || function.type_.is_some()
            || function.flow_node.is_some()
            || function.full_signature.is_some()
            || function.local_symbol.is_some()
            || function.symbol.is_some()
            || function.end_flow_node.is_some()
            || function.return_flow_node.is_some()
            || function.next_container.is_some()
            || function.facts != 0
        {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }
        self.validate_range(statement, parent)?;
        self.validate_container(statement, callable)?;
        self.validate_block_scope_container(statement, callable)?;

        let name = function
            .name
            .map(|node| self.reference(node))
            .ok_or_else(|| {
                self.unsupported(
                    statement,
                    record.kind,
                    SourceFunctionStatementsRole::Callable,
                )
            })?;
        let name_record = self.node(name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(self.unsupported(
                name,
                name_record.kind,
                SourceFunctionStatementsRole::Callable,
            ));
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
        {
            return Err(self.unsupported(
                name,
                name_record.kind,
                SourceFunctionStatementsRole::Callable,
            ));
        }
        self.validate_parent(
            name,
            Some(statement.node),
            SourceFunctionStatementsRole::Callable,
        )?;
        self.validate_range(name, statement)?;
        self.validate_container(name, statement)?;
        self.validate_block_scope_container(name, statement)?;

        let body = function
            .body
            .map(|node| self.reference(node))
            .ok_or_else(|| {
                self.unsupported(
                    statement,
                    record.kind,
                    SourceFunctionStatementsRole::FunctionBody,
                )
            })?;
        self.validate_parent(
            body,
            Some(statement.node),
            SourceFunctionStatementsRole::FunctionBody,
        )?;
        self.validate_range(body, statement)?;
        self.validate_order(name, body)?;
        self.validate_container(body, statement)?;
        self.validate_block_scope_container(body, statement)?;

        let symbol = self.bound.symbol(statement).ok_or(
            SourceFunctionStatementsInvariant::InvalidCallableEdge(statement),
        )?;
        let locals = self
            .bound
            .locals(callable)
            .ok_or(SourceFunctionStatementsInvariant::MissingLocals(callable))?;
        let actual = self
            .store
            .symbol_table(locals)
            .and_then(|table| table.get_source(&identifier.text));
        if actual != Some(symbol) {
            return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                declaration: statement,
                scope: callable,
                expected: symbol,
                actual,
            }
            .into());
        }

        Ok(statement)
    }

    fn plan_linear_expression_statement(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<NodeRef, SourceFunctionStatementsError> {
        let record = self.node(statement)?;
        let NodeData::ExpressionStatement(data) = &record.data else {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        };
        if record.kind != SyntaxKind::ExpressionStatement
            || record.flags.0 != 0
            || record.parent != Some(parent.node)
            || data.flow_node.is_some()
        {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }
        self.validate_range(statement, parent)?;
        self.validate_container(statement, callable)?;
        self.validate_block_scope_container(statement, callable)?;

        let expression = self.reference(data.expression);
        let expression_record = self.node(expression)?;
        self.validate_parent(
            expression,
            Some(statement.node),
            SourceFunctionStatementsRole::BodyStatement,
        )?;
        self.validate_range(expression, statement)?;
        self.validate_container(expression, callable)?;
        self.validate_block_scope_container(expression, callable)?;
        if expression_record.flags.0 != 0 {
            return Err(self.unsupported(
                expression,
                expression_record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }

        match &expression_record.data {
            NodeData::Identifier(identifier)
                if expression_record.kind == SyntaxKind::Identifier
                    && !identifier.text.is_empty()
                    && identifier.flow_node.is_none() => {}
            NodeData::CallExpression(call)
                if expression_record.kind == SyntaxKind::CallExpression
                    && call.question_dot_token.is_none()
                    && call.symbol.is_none()
                    && call.facts == 0 =>
            {
                let callee = self.reference(call.expression);
                let callee_record = self.node(callee)?;
                if !matches!(
                    callee_record.kind,
                    SyntaxKind::Identifier | SyntaxKind::PropertyAccessExpression
                ) || callee_record.flags.0 != 0
                {
                    return Err(self.unsupported(
                        callee,
                        callee_record.kind,
                        SourceFunctionStatementsRole::BodyStatement,
                    ));
                }
                self.validate_parent(
                    callee,
                    Some(expression.node),
                    SourceFunctionStatementsRole::BodyStatement,
                )?;
                self.validate_range(callee, expression)?;
                self.validate_container(callee, callable)?;
                self.validate_block_scope_container(callee, callable)?;
            }
            NodeData::BinaryExpression(binary)
                if expression_record.kind == SyntaxKind::BinaryExpression
                    && binary.symbol.is_none()
                    && binary.type_.is_none()
                    && binary.facts == 0
                    && binary.modifiers.is_none() =>
            {
                self.validate_linear_assignment_expression(expression, callable)?;
            }
            _ => {
                return Err(self.unsupported(
                    expression,
                    expression_record.kind,
                    SourceFunctionStatementsRole::BodyStatement,
                ));
            }
        }

        let actual = self.bound.flow_container(statement);
        if actual != Some(callable) {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: statement,
                expected: callable,
                actual,
            }
            .into());
        }
        Ok(expression)
    }

    fn validate_linear_assignment_expression(
        &self,
        expression: NodeRef,
        callable: NodeRef,
    ) -> Result<(), SourceFunctionStatementsError> {
        let record = self.node(expression)?;
        let NodeData::BinaryExpression(binary) = &record.data else {
            return Err(self.unsupported(
                expression,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        };
        let left = self.reference(binary.left);
        let operator = self.reference(binary.operator_token);
        let right = self.reference(binary.right);
        for node in [left, operator, right] {
            self.validate_parent(
                node,
                Some(expression.node),
                SourceFunctionStatementsRole::BodyStatement,
            )?;
            self.validate_range(node, expression)?;
            self.validate_container(node, callable)?;
            self.validate_block_scope_container(node, callable)?;
        }
        self.validate_order(left, operator)?;
        self.validate_order(operator, right)?;

        let target = self.node(left)?;
        let NodeData::Identifier(identifier) = &target.data else {
            return Err(self.unsupported(
                left,
                target.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        };
        if target.kind != SyntaxKind::Identifier
            || target.flags.0 != 0
            || identifier.text.is_empty()
            || identifier.flow_node.is_some()
        {
            return Err(self.unsupported(
                left,
                target.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }

        let token = self.node(operator)?;
        if token.kind != SyntaxKind::EqualsToken
            || token.flags.0 != 0
            || !matches!(token.data, NodeData::Token(_))
        {
            return Err(self.unsupported(
                operator,
                token.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }
        Ok(())
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
        let outer_scope = self.statement_lexical_scope(parent, callable)?;
        self.validate_block_scope_container(block, outer_scope)?;
        self.validate_node_list(block, data.statements.range, &data.statements.nodes)?;

        let mut locals = Vec::new();
        for &statement_id in &data.statements.nodes {
            let statement = self.reference(statement_id);
            match self.node(statement)?.kind {
                SyntaxKind::VariableStatement
                | SyntaxKind::Block
                | SyntaxKind::EmptyStatement
                | SyntaxKind::LabeledStatement => {
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
            SyntaxKind::LabeledStatement => {
                self.plan_labeled_local_statement(statement, parent, callable)
            }
            SyntaxKind::EmptyStatement => {
                self.validate_empty_statement(statement, parent, callable)?;
                Ok(Vec::new())
            }
            _ => self.plan_local_statement(statement, parent, callable),
        }
    }

    fn plan_labeled_local_statement(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<Vec<SourceLocalDeclarationSyntax>, SourceFunctionStatementsError> {
        let child = validate_labeled_statement(self.arena, self.bound, statement, parent)?;
        self.validate_container(statement, callable)?;
        self.validate_block_scope_container(
            statement,
            self.statement_lexical_scope(parent, callable)?,
        )?;
        match self.node(child)?.kind {
            SyntaxKind::Block | SyntaxKind::EmptyStatement | SyntaxKind::LabeledStatement => {
                self.plan_local_or_block_statement(child, statement, callable)
            }
            kind => {
                Err(self.unsupported(child, kind, SourceFunctionStatementsRole::BranchStatement))
            }
        }
    }

    fn statement_lexical_scope(
        &self,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<NodeRef, SourceFunctionStatementsError> {
        if parent == self.callable.body {
            return Ok(callable);
        }
        if self.node(parent)?.kind != SyntaxKind::LabeledStatement {
            return Ok(parent);
        }
        self.bound.block_scope_container(parent).ok_or_else(|| {
            SourceFunctionStatementsInvariant::InvalidBlockScopeContainer {
                node: parent,
                expected: callable,
                actual: None,
            }
            .into()
        })
    }

    fn is_straight_line_variable_parent(
        &self,
        parent: NodeRef,
    ) -> Result<bool, SourceFunctionStatementsError> {
        let mut current = parent;
        while current != self.callable.body {
            let record = self.node(current)?;
            if !matches!(
                record.kind,
                SyntaxKind::Block | SyntaxKind::LabeledStatement
            ) {
                return Ok(false);
            }
            let Some(next) = record.parent else {
                return Ok(false);
            };
            current = self.reference(next);
        }
        Ok(true)
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
        let scope = self.statement_lexical_scope(parent, callable)?;
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

        let mut statements = Vec::with_capacity(block.statements.nodes.len());
        let mut directive_prologue = true;
        for &statement_id in &block.statements.nodes {
            let statement = self.reference(statement_id);
            if directive_prologue && self.node(statement)?.kind == SyntaxKind::ExpressionStatement {
                let NodeData::ExpressionStatement(expression_statement) =
                    &self.node(statement)?.data
                else {
                    return Err(self.unsupported(
                        statement,
                        SyntaxKind::ExpressionStatement,
                        SourceFunctionStatementsRole::BodyStatement,
                    ));
                };
                let expression = self.reference(expression_statement.expression);
                if self.node(expression)?.kind == SyntaxKind::StringLiteral {
                    self.validate_directive_statement(statement, body, declaration)?;
                    continue;
                }
            }
            directive_prologue = false;
            statements.push(statement_id);
        }
        Ok(statements)
    }

    fn validate_directive_statement(
        &self,
        statement: NodeRef,
        body: NodeRef,
        callable: NodeRef,
    ) -> Result<(), SourceFunctionStatementsError> {
        let record = self.node(statement)?;
        let NodeData::ExpressionStatement(data) = &record.data else {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        };
        if record.kind != SyntaxKind::ExpressionStatement
            || record.flags.0 != 0
            || record.parent != Some(body.node)
            || data.flow_node.is_some()
        {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }
        self.validate_range(statement, body)?;
        self.validate_container(statement, callable)?;
        self.validate_block_scope_container(statement, callable)?;

        let expression = self.reference(data.expression);
        let expression_record = self.node(expression)?;
        let NodeData::StringLiteral(literal) = &expression_record.data else {
            return Err(self.unsupported(
                expression,
                expression_record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        };
        if expression_record.kind != SyntaxKind::StringLiteral
            || expression_record.flags.0 != 0
            || literal.token_flags.0 != 0
        {
            return Err(self.unsupported(
                expression,
                expression_record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }
        self.validate_parent(
            expression,
            Some(statement.node),
            SourceFunctionStatementsRole::BodyStatement,
        )?;
        self.validate_range(expression, statement)?;
        self.validate_container(expression, callable)?;
        self.validate_block_scope_container(expression, callable)
    }

    fn plan_local_statement(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<Vec<SourceLocalDeclarationSyntax>, SourceFunctionStatementsError> {
        let expected_scope = self.statement_lexical_scope(parent, callable)?;
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
            0 if self.is_straight_line_variable_parent(parent)? => VariableBindingKind::Var,
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
        let symbol_scope = if binding == VariableBindingKind::Var {
            callable
        } else {
            expected_scope
        };
        let locals = self.bound.locals(symbol_scope).ok_or(
            SourceFunctionStatementsInvariant::MissingLocals(symbol_scope),
        )?;
        let actual = self
            .store
            .symbol_table(locals)
            .and_then(|table| table.get_source(&name_text));
        if actual != Some(symbol) {
            return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                declaration,
                scope: symbol_scope,
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

        fn conditional_enum_plan(
            &self,
        ) -> Result<SourceConditionalEnumFunctionStatementsSyntax, SourceFunctionStatementsError>
        {
            let callable = self.callable();
            plan_source_conditional_enum_function_statements_syntax(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                &callable,
            )
        }
    }

    #[test]
    fn inferred_void_if_authenticates_embedded_const_enum_and_branch_join() {
        let fixture = JoinedFixture::new(
            concat!(
                "function choose(value: number) {\n",
                "  if (value)\n",
                "    const enum Choice { Ready = 1 }\n",
                "}\n",
            ),
            FileId::new(1_350),
        );
        let syntax = fixture.conditional_enum_plan().unwrap();
        let callable = fixture.declaration();
        assert_eq!(syntax.body, fixture.callable().body);
        assert_eq!(syntax.control.condition, syntax.condition_identifier);
        assert_eq!(syntax.control.then_statement, syntax.enum_declaration);
        assert!(syntax.control.else_statement.is_none());
        assert_eq!(
            fixture.bound.symbol(syntax.enum_declaration),
            Some(syntax.enum_symbol),
        );
        assert_eq!(
            fixture
                .store
                .symbol_table(fixture.bound.locals(callable).unwrap())
                .and_then(|locals| locals.get_source("Choice")),
            Some(syntax.enum_symbol),
        );
        assert_eq!(
            fixture.bound.flow_graph().container_end(callable),
            Some(syntax.join_flow),
        );
        let join = fixture
            .bound
            .flow_graph()
            .nodes()
            .get(syntax.join_flow)
            .unwrap();
        assert_eq!(
            joined_semantic_flow_flags(join.flags),
            FlowFlags::BRANCH_LABEL.bits(),
        );
        assert_eq!(join.antecedents.len(), 2);
    }

    #[test]
    fn inferred_void_if_rejects_unsupported_enum_branches_and_callable_shapes() {
        for (index, source) in [
            "function choose(value: number): void { if (value) const enum E { A = 1 } }",
            "function choose(value: number) { if (value) enum E { A = 1 } }",
            "function choose(value: number) { if (value) { const enum E { A = 1 } } }",
            "function choose(value: number) { if (value) const enum E { A = 1 } else ; }",
            "function choose(value: number) { if (value) const enum E { A = 1, B = 2 } }",
            "function choose(value: number) { if (value) const enum E { A = 'ready' } }",
            "function choose(value: number) { if ((value)) const enum E { A = 1 } }",
            "function choose(value: number, other: number) { if (value) const enum E { A = 1 } }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_351 + u32::try_from(index).unwrap()));
            assert!(matches!(
                fixture.conditional_enum_plan(),
                Err(SourceFunctionStatementsError::Unsupported(_)),
            ));
        }
    }

    #[test]
    fn embedded_const_enum_planning_replays_without_semantic_publication() {
        let fixture = JoinedFixture::new(
            "function choose(value: number) { if (value) const enum E { A = 1 } }",
            FileId::new(1_359),
        );
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.mapper_len(),
        );
        let first = fixture.conditional_enum_plan().unwrap();
        let second = fixture.conditional_enum_plan().unwrap();
        assert_eq!(first, second);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.mapper_len(),
            ),
            before,
        );
    }

    #[test]
    fn linear_body_accepts_inferred_function_scoped_var_and_covers_final_assignment() {
        let fixture = JoinedFixture::new("function avoid() { var x = 1; }", FileId::new(1_190));
        let syntax = fixture.linear_plan().unwrap();
        assert_eq!(syntax.locals.len(), 1);
        assert_eq!(
            syntax.statements,
            [SourceLinearFunctionStatementSyntax::Local(syntax.locals[0])],
        );
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
    fn linear_body_preserves_nested_function_order_and_distinct_shadowed_locals() {
        let fixture = JoinedFixture::new(
            concat!(
                "function outer() {\n",
                "  const x = 0;\n",
                "  function inner() {\n",
                "    var x = \"inner\";\n",
                "  }\n",
                "  const after = x;\n",
                "}\n",
            ),
            FileId::new(1_198),
        );
        let syntax = fixture.linear_plan().unwrap();
        assert_eq!(syntax.locals.len(), 2);
        let [
            SourceLinearFunctionStatementSyntax::Local(first),
            SourceLinearFunctionStatementSyntax::Function(inner),
            SourceLinearFunctionStatementSyntax::Local(after),
        ] = syntax.statements.as_slice()
        else {
            panic!("expected local, nested function, and trailing local in source order")
        };
        assert_eq!(*first, syntax.locals[0]);
        assert_eq!(*after, syntax.locals[1]);
        assert_eq!(first.binding, VariableBindingKind::Const);

        let outer = fixture.declaration();
        let outer_locals = fixture.bound.locals(outer).unwrap();
        let inner_symbol = fixture.bound.symbol(*inner).unwrap();
        assert_eq!(
            fixture
                .store
                .symbol_table(outer_locals)
                .and_then(|table| table.get_source("inner")),
            Some(inner_symbol),
        );

        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let callable =
            plan_source_callable(&fixture.store, &host, *inner, inner_symbol, None).unwrap();
        let inner_syntax = plan_source_linear_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();
        let [shadowed] = inner_syntax.locals.as_slice() else {
            panic!("expected one function-scoped inner variable")
        };
        assert_eq!(shadowed.binding, VariableBindingKind::Var);
        assert_ne!(shadowed.symbol, first.symbol);
        assert_eq!(
            fixture
                .store
                .symbol_table(fixture.bound.locals(*inner).unwrap())
                .and_then(|table| table.get_source("x")),
            Some(shadowed.symbol),
        );
    }

    #[test]
    fn linear_body_rejects_nested_functions_outside_the_zero_argument_inferred_shape() {
        for (index, source) in [
            "function outer() { function inner(value: number) {} }",
            "function outer() { function inner(): void {} }",
            "function outer() { function inner<T>() {} }",
            "function outer() { { function inner() {} } }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_280 + u32::try_from(index).unwrap()));
            assert!(matches!(
                fixture.linear_plan(),
                Err(SourceFunctionStatementsError::Unsupported(_)),
            ));
        }
    }

    #[test]
    fn linear_body_retains_identifier_assignment_and_call_statements_in_source_order() {
        let fixture = JoinedFixture::new(
            concat!(
                "function effects(value: number): void {\n",
                "  \"use strict\";\n",
                "  value;\n",
                "  const saved = value;\n",
                "  value = 1;\n",
                "  consume(saved);\n",
                "}\n",
            ),
            FileId::new(1_290),
        );
        let syntax = fixture.linear_plan().unwrap();
        assert_eq!(syntax.locals.len(), 1);
        let [
            SourceLinearFunctionStatementSyntax::Expression {
                statement: read_statement,
                expression: read,
            },
            SourceLinearFunctionStatementSyntax::Local(saved),
            SourceLinearFunctionStatementSyntax::Expression {
                statement: assignment_statement,
                expression: assignment,
            },
            SourceLinearFunctionStatementSyntax::Expression {
                statement: call_statement,
                expression: call,
            },
        ] = syntax.statements.as_slice()
        else {
            panic!("expected read, local, assignment, and call in source order")
        };
        assert_eq!(*saved, syntax.locals[0]);
        assert_eq!(
            fixture.parsed.arena.get(read.node).unwrap().kind,
            SyntaxKind::Identifier,
        );
        assert_eq!(
            fixture.parsed.arena.get(assignment.node).unwrap().kind,
            SyntaxKind::BinaryExpression,
        );
        assert_eq!(
            fixture.parsed.arena.get(call.node).unwrap().kind,
            SyntaxKind::CallExpression,
        );
        for statement in [*read_statement, *assignment_statement, *call_statement] {
            assert_eq!(
                fixture.bound.flow_container(statement),
                Some(fixture.declaration()),
            );
        }
    }

    #[test]
    fn linear_body_accepts_a_leading_call_after_a_real_directive_prologue() {
        for (index, source) in [
            "function invoke(): void { consume(); }",
            "function invoke(): void { \"use strict\"; consume(); }",
            "function invoke(): void { object.consume(); }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_291 + u32::try_from(index).unwrap()));
            let syntax = fixture.linear_plan().unwrap();
            assert!(syntax.locals.is_empty());
            assert!(matches!(
                syntax.statements.as_slice(),
                [SourceLinearFunctionStatementSyntax::Expression { .. }],
            ));
        }
    }

    #[test]
    fn linear_body_rejects_unsupported_expression_targets_and_loop_statements() {
        for (index, source) in [
            "function invalid(value: number): void { value += 1; }",
            "function invalid(value: number): void { value.property = 1; }",
            "function invalid(value: number): void { value.property; }",
            "function invalid(value: number): void { consume?.(value); }",
            "function invalid(value: number): void { while (value) { value; } }",
            "function invalid(value: number): void { { value; } }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_300 + u32::try_from(index).unwrap()));
            assert!(matches!(
                fixture.linear_plan(),
                Err(SourceFunctionStatementsError::Unsupported(_)),
            ));
        }
    }

    #[test]
    fn linear_body_ignores_leading_string_directives_without_changing_flow() {
        let fixture = JoinedFixture::new(
            concat!(
                "var abstract = true;\n",
                "function foo() {\n",
                "  \"use strict\";\n",
                "  \"another directive\";\n",
                "  var abstract = true;\n",
                "}\n",
            ),
            FileId::new(1_196),
        );
        let syntax = fixture.linear_plan().unwrap();
        assert_eq!(syntax.locals.len(), 1);
        assert_eq!(syntax.locals[0].binding, VariableBindingKind::Var);
        assert!(syntax.return_statement.is_none());

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
    fn linear_body_rejects_non_directive_expression_statements() {
        for source in [
            "function invalid() { 1; var value = 1; }",
            "function invalid() { var value = 1; \"use strict\"; }",
            "function invalid() { ; \"use strict\"; var value = 1; }",
        ] {
            let fixture = JoinedFixture::new(source, FileId::new(1_197));
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
    fn linear_body_preserves_labeled_blocks_and_function_scoped_nested_variables() {
        let fixture = JoinedFixture::new(
            concat!(
                "function labeled(value: number): number {\n",
                "  outer: {\n",
                "    var lifted: number = value;\n",
                "    inner: {\n",
                "      let nested: number = lifted;\n",
                "      empty: ;\n",
                "    }\n",
                "  }\n",
                "  trailing: ;\n",
                "  const result: number = lifted;\n",
                "  return result;\n",
                "}\n",
            ),
            FileId::new(1_270),
        );
        let syntax = fixture.linear_plan().unwrap();
        assert_eq!(syntax.locals.len(), 3);
        assert_eq!(syntax.locals[0].binding, VariableBindingKind::Var);
        assert_eq!(syntax.locals[1].binding, VariableBindingKind::Let);
        assert_eq!(syntax.locals[2].binding, VariableBindingKind::Const);

        let callable = fixture.declaration();
        let locals = fixture.bound.locals(callable).unwrap();
        assert_eq!(
            fixture
                .store
                .symbol_table(locals)
                .and_then(|table| table.get_source("lifted")),
            Some(syntax.locals[0].symbol),
        );
        let points = syntax
            .locals
            .iter()
            .map(|local| local.name)
            .chain(syntax.return_statement);
        let assignments = syntax.locals.iter().map(|local| SourceFlowAssignment {
            declaration: local.declaration,
            symbol: local.symbol,
        });
        assert!(
            SourceFlowPlan::preflight(&fixture.bound, callable, None, points, [], assignments)
                .is_ok()
        );
    }

    #[test]
    fn linear_body_rejects_duplicate_labels_and_labeled_jumps() {
        for (index, source) in [
            "function invalid(): void { outer: { outer: ; } }",
            "function invalid(): void { outer: { break outer; } }",
            "function invalid(): void { outer: value; }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_271 + u32::try_from(index).unwrap()));
            assert!(matches!(
                fixture.linear_plan(),
                Err(SourceFunctionStatementsError::Unsupported(_)),
            ));
        }
    }

    #[test]
    fn linear_body_preserves_unreachable_regular_and_const_enum_declarations() {
        for (index, source, is_const) in [
            (0, "function regular() { return E.A; enum E { A } }", false),
            (
                1,
                "function constant() { return E.A; const enum E { A } }",
                true,
            ),
        ] {
            let fixture = JoinedFixture::new(source, FileId::new(1_360 + index));
            let syntax = fixture.linear_plan().unwrap();
            let callable = fixture.declaration();
            assert!(syntax.locals.is_empty());
            assert!(syntax.return_statement.is_some());
            assert!(syntax.return_expression.is_some());
            let [SourceLinearFunctionStatementSyntax::Enum(enumeration)] =
                syntax.statements.as_slice()
            else {
                panic!("expected exactly one trailing local enum")
            };
            assert_eq!(enumeration.is_const, is_const);
            assert!(enumeration.unreachable);
            assert_eq!(
                fixture.bound.symbol(enumeration.declaration),
                Some(enumeration.symbol),
            );
            assert_eq!(
                fixture
                    .store
                    .symbol_table(fixture.bound.locals(callable).unwrap())
                    .and_then(|locals| locals.get_source("E")),
                Some(enumeration.symbol),
            );
            assert_eq!(
                fixture
                    .bound
                    .flow_graph()
                    .is_unreachable(enumeration.declaration),
                Some(true),
            );
            assert!(fixture.bound.flow_at(enumeration.declaration).is_none());

            let return_statement = syntax.return_statement.unwrap();
            assert!(
                SourceFlowPlan::preflight(
                    &fixture.bound,
                    callable,
                    None,
                    [return_statement],
                    [],
                    [],
                )
                .is_ok(),
            );
        }
    }

    #[test]
    fn linear_body_rejects_other_enum_positions_and_trailing_statements() {
        for (index, source) in [
            "function invalid() { enum E { A } return E.A; }",
            "function invalid() { return; enum E { A } }",
            "function invalid() { return E.A; enum E { A } const later = 1; }",
            "function invalid() { return E.A; enum E { A } enum Other { A } }",
            "function invalid() { return E.A; { enum E { A } } }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_370 + u32::try_from(index).unwrap()));
            assert!(
                matches!(
                    fixture.linear_plan(),
                    Err(SourceFunctionStatementsError::Unsupported(_)),
                ),
                "unexpectedly admitted enum statement shape: {source}",
            );
        }
    }

    #[test]
    fn trailing_local_enum_rejects_a_forged_function_scope_symbol() {
        let mut fixture = JoinedFixture::new(
            "enum Other { A } function invalid() { return E.A; enum E { A } }",
            FileId::new(1_380),
        );
        let syntax = fixture.linear_plan().unwrap();
        let [SourceLinearFunctionStatementSyntax::Enum(enumeration)] = syntax.statements.as_slice()
        else {
            panic!("expected exactly one trailing local enum")
        };
        let enumeration = *enumeration;
        let other = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::EnumDeclaration(enumeration) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &fixture.parsed.arena.get(enumeration.name)?.data
                else {
                    return None;
                };
                (name.text == "Other").then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let other_symbol = fixture.bound.symbol(other).unwrap();
        let callable = fixture.declaration();
        let locals = fixture.bound.locals(callable).unwrap();
        assert_eq!(
            fixture
                .store
                .insert_symbol(locals, EscapedName::source("E"), other_symbol),
            Some(Some(enumeration.symbol)),
        );
        assert_eq!(
            fixture.linear_plan(),
            Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                declaration: enumeration.declaration,
                scope: callable,
                expected: enumeration.symbol,
                actual: Some(other_symbol),
            }
            .into()),
        );
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
        assert!(
            source_control_branch_is_empty(
                &fixture.parsed.arena,
                &fixture.bound,
                syntax.then_statement,
            )
            .unwrap()
        );
        assert!(
            source_control_branch_is_empty(
                &fixture.parsed.arena,
                &fixture.bound,
                syntax.else_statement.unwrap(),
            )
            .unwrap()
        );
    }

    #[test]
    fn empty_control_branches_reject_real_statements_without_hiding_them() {
        for (index, source, expected_empty) in [
            (0u32, "if (flag) { { ; } ; }", true),
            (1, "if (flag) { value; }", false),
            (2, "if (flag) outer: { inner: ; ; }", true),
            (3, "if (flag) outer: { value; }", false),
        ] {
            let fixture = JoinedFixture::new(source, FileId::new(1_250 + index));
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
            assert_eq!(
                source_control_branch_is_empty(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    syntax.then_statement,
                )
                .unwrap(),
                expected_empty,
            );
        }
    }

    #[test]
    fn control_branch_rejects_duplicate_active_labels() {
        let fixture = JoinedFixture::new("if (true) outer: { outer: ; }", FileId::new(1_275));
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
        assert!(matches!(
            plan_source_control_if_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                statement,
                fixture.bound.source_file(),
            ),
            Err(SourceFunctionStatementsError::Unsupported(_)),
        ));
    }

    #[test]
    fn nested_if_and_loop_blocks_retain_invalid_export_diagnostics() {
        for (index, source) in [
            "if (true) { if (false) export type {}; }",
            "if (true) for (;;) { export type {}; }",
            "if (true) { switch (value) { case 0: export type {}; } }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_216 + u32::try_from(index).unwrap()));
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::IfStatement
                        && record.parent == Some(fixture.parsed.source_file))
                    .then_some(NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
                })
                .unwrap();
            let syntax = plan_source_control_if_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                statement,
                fixture.bound.source_file(),
            )
            .unwrap();
            let [diagnostic] = syntax.nested_export_diagnostics.as_slice() else {
                panic!("expected one nested export diagnostic in {source}")
            };
            assert_eq!(diagnostic.diagnostic.code(), 1_233);
        }
    }

    #[test]
    fn control_loop_syntax_preserves_all_standard_loop_orders() {
        for (index, (source, expected_kind, expected_children)) in [
            ("while (flag) {}", SourceControlLoopKind::While, 2usize),
            ("do {} while (flag);", SourceControlLoopKind::DoWhile, 2),
            (
                "for (let index = 0; index < 3; index++) {}",
                SourceControlLoopKind::For,
                4,
            ),
            (
                "for (const key in value) {}",
                SourceControlLoopKind::ForIn,
                3,
            ),
            (
                "for (const item of values) {}",
                SourceControlLoopKind::ForOf,
                3,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_230 + u32::try_from(index).unwrap()));
            let source_node = fixture
                .parsed
                .arena
                .get(fixture.parsed.source_file)
                .unwrap();
            let NodeData::SourceFile(root) = &source_node.data else {
                panic!("expected source root")
            };
            let statement = NodeRef::new(
                fixture.parsed.arena.id(),
                fixture.file,
                root.statements.nodes[0],
            );
            let syntax = plan_source_control_loop_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                statement,
                fixture.bound.source_file(),
            )
            .unwrap();
            assert_eq!(syntax.kind, expected_kind);
            let children = syntax.ordered_nodes();
            assert_eq!(children.len(), expected_children);
            assert!(children.windows(2).all(|pair| {
                fixture.parsed.arena.get(pair[0].node).unwrap().range.end
                    <= fixture.parsed.arena.get(pair[1].node).unwrap().range.start
            }));
        }
    }

    #[test]
    fn control_switch_syntax_preserves_grouped_cases_and_default_order() {
        let fixture = JoinedFixture::new(
            concat!(
                "switch (value) {\n",
                "  case 'first': break;\n",
                "  case 'second':\n",
                "  case 'third': break;\n",
                "  default: break;\n",
                "}\n",
            ),
            FileId::new(1_240),
        );
        let source = fixture
            .parsed
            .arena
            .get(fixture.parsed.source_file)
            .unwrap();
        let NodeData::SourceFile(source) = &source.data else {
            panic!("expected source root")
        };
        let statement = NodeRef::new(
            fixture.parsed.arena.id(),
            fixture.file,
            source.statements.nodes[0],
        );
        let syntax = plan_source_control_switch_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            statement,
            fixture.bound.source_file(),
        )
        .unwrap();
        assert_eq!(syntax.clauses.len(), 4);
        assert!(syntax.clauses[0].expression.is_some());
        assert_eq!(syntax.clauses[0].statements.len(), 1);
        assert!(syntax.clauses[1].expression.is_some());
        assert!(syntax.clauses[1].statements.is_empty());
        assert!(syntax.clauses[2].expression.is_some());
        assert_eq!(syntax.clauses[2].statements.len(), 1);
        assert!(syntax.clauses[3].expression.is_none());
        assert_eq!(syntax.clauses[3].statements.len(), 1);
        assert!(
            syntax
                .clauses
                .iter()
                .all(|clause| clause.unreachable_ranges.is_empty())
        );
    }

    #[test]
    fn function_switch_retains_grouped_literal_cases_and_value_returns() {
        let fixture = JoinedFixture::new(
            concat!(
                "function getSecurity(level) {\n",
                "  switch (level) {\n",
                "    case 0:\n",
                "    case 1:\n",
                "    case 2:\n",
                "      return \"Hi\";\n",
                "    case 3:\n",
                "    case 4:\n",
                "      return \"hello\";\n",
                "    case 5:\n",
                "    default:\n",
                "      return \"world\";\n",
                "  }\n",
                "}\n",
            ),
            FileId::new(1_242),
        );
        let callable = fixture.callable();
        assert!(callable.return_type.is_inferred());
        let syntax = plan_source_switch_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();
        assert_eq!(syntax.body, callable.body);
        assert_eq!(syntax.switch.clauses.len(), 7);
        assert_eq!(syntax.returns.len(), 3);
        assert!(syntax.no_match_flow.is_none());
        assert_eq!(syntax.returns[0].clause, syntax.switch.clauses[2].clause);
        assert_eq!(syntax.returns[1].clause, syntax.switch.clauses[4].clause);
        assert_eq!(syntax.returns[2].clause, syntax.switch.clauses[6].clause);
        let switch_flow = fixture.bound.flow_at(syntax.switch.statement).unwrap();
        assert_eq!(
            fixture.bound.flow_at(syntax.switch.expression),
            Some(switch_flow),
        );
        for (value, (clause_start, clause_end)) in
            syntax.returns.iter().zip([(0, 3), (3, 5), (5, 7)])
        {
            assert!(
                fixture
                    .parsed
                    .arena
                    .get(value.expression.node)
                    .is_some_and(|node| node.kind == SyntaxKind::StringLiteral)
            );
            let return_flow = fixture.bound.flow_at(value.statement).unwrap();
            let return_node = fixture.bound.flow_graph().nodes().get(return_flow).unwrap();
            assert_eq!(
                return_node.payload,
                Some(FlowNodePayload::SwitchClause {
                    switch_statement: syntax.switch.statement,
                    clause_start,
                    clause_end,
                }),
            );
            assert_eq!(return_node.antecedent, Some(switch_flow));
        }
    }

    #[test]
    fn function_switch_accepts_annotated_returns_and_string_case_groups() {
        let fixture = JoinedFixture::new(
            concat!(
                "function classify(value: string): number {\n",
                "  switch (value) {\n",
                "    case 'first':\n",
                "    case 'second':\n",
                "      return 1;\n",
                "    default:\n",
                "      return 'invalid';\n",
                "  }\n",
                "}\n",
            ),
            FileId::new(1_260),
        );
        let callable = fixture.callable();
        assert!(!callable.return_type.is_inferred());
        let syntax = plan_source_switch_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();

        assert_eq!(syntax.switch.clauses.len(), 3);
        assert_eq!(syntax.returns.len(), 2);
        assert!(syntax.switch.clauses[..2].iter().all(|clause| {
            clause.expression.is_some_and(|expression| {
                fixture
                    .parsed
                    .arena
                    .get(expression.node)
                    .is_some_and(|node| node.kind == SyntaxKind::StringLiteral)
            })
        }));
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(syntax.returns[0].expression.node)
                .unwrap()
                .kind,
            SyntaxKind::NumericLiteral,
        );
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(syntax.returns[1].expression.node)
                .unwrap()
                .kind,
            SyntaxKind::StringLiteral,
        );
    }

    #[test]
    fn function_switch_accepts_boolean_cases_and_returns() {
        let fixture = JoinedFixture::new(
            concat!(
                "function invert(value: boolean): boolean {\n",
                "  switch (value) {\n",
                "    case true:\n",
                "      return false;\n",
                "    default:\n",
                "      return true;\n",
                "  }\n",
                "}\n",
            ),
            FileId::new(1_276),
        );
        let callable = fixture.callable();
        let syntax = plan_source_switch_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();

        assert_eq!(syntax.switch.clauses.len(), 2);
        assert_eq!(syntax.returns.len(), 2);
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(syntax.switch.clauses[0].expression.unwrap().node)
                .unwrap()
                .kind,
            SyntaxKind::TrueKeyword,
        );
        assert_eq!(
            syntax
                .returns
                .iter()
                .map(|value| fixture
                    .parsed
                    .arena
                    .get(value.expression.node)
                    .unwrap()
                    .kind)
                .collect::<Vec<_>>(),
            [SyntaxKind::FalseKeyword, SyntaxKind::TrueKeyword],
        );
    }

    #[test]
    fn function_switch_accepts_complete_named_keyof_cases_without_default() {
        let fixture = JoinedFixture::new(
            concat!(
                "interface Choices { left: number; right: number; }\n",
                "function classify<T extends keyof Choices>(value: T): boolean {\n",
                "  switch (value) {\n",
                "    case 'left': return true;\n",
                "    case 'right': return false;\n",
                "  }\n",
                "}\n",
            ),
            FileId::new(1_330),
        );
        let NodeData::SourceFile(source) = &fixture
            .parsed
            .arena
            .get(fixture.parsed.source_file)
            .unwrap()
            .data
        else {
            panic!("expected source file")
        };
        let NodeData::InterfaceDeclaration(interface) = &fixture
            .parsed
            .arena
            .get(source.statements.nodes[0])
            .unwrap()
            .data
        else {
            panic!("expected named interface declaration")
        };
        assert!(interface.members.nodes.iter().all(|member| {
            matches!(
                fixture.parsed.arena.get(*member).unwrap().data,
                NodeData::PropertyDeclaration(_)
            )
        }));
        let callable = fixture.callable();
        let syntax = plan_source_switch_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();

        assert_eq!(syntax.switch.clauses.len(), 2);
        assert_eq!(syntax.returns.len(), 2);
        let no_match = syntax.no_match_flow.unwrap();
        assert_eq!(
            fixture
                .bound
                .flow_graph()
                .container_end(callable.declaration),
            Some(no_match),
        );
        let unmatched = fixture.bound.flow_graph().nodes().get(no_match).unwrap();
        assert_eq!(
            joined_semantic_flow_flags(unmatched.flags),
            FlowFlags::SWITCH_CLAUSE.bits(),
        );
        assert_eq!(
            unmatched.payload,
            Some(FlowNodePayload::SwitchClause {
                switch_statement: syntax.switch.statement,
                clause_start: 0,
                clause_end: 0,
            }),
        );
        assert_eq!(
            unmatched.antecedent,
            fixture.bound.flow_at(syntax.switch.statement),
        );
        assert!(unmatched.antecedents.is_empty());
    }

    #[test]
    fn function_switch_rejects_incomplete_duplicate_or_nonliteral_named_keyof_cases() {
        for (index, cases) in [
            "case 'left': return true;",
            "case 'left': return true; case 'left': return false; case 'right': return true;",
            "case 'left': return true; case value: return false;",
            "case 'left': return true; case 'right': return false; case 'other': return true;",
        ]
        .into_iter()
        .enumerate()
        {
            let source = format!(
                "interface Choices {{ left: number; right: number; }}\n\
                 function classify<T extends keyof Choices>(value: T): boolean {{\n\
                 switch (value) {{ {cases} }}\n\
                 }}\n",
            );
            let fixture =
                JoinedFixture::new(&source, FileId::new(1_331 + u32::try_from(index).unwrap()));
            let callable = fixture.callable();
            assert!(matches!(
                plan_source_switch_function_statements_syntax(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    &fixture.store,
                    &callable,
                ),
                Err(SourceFunctionStatementsError::Unsupported(_)),
            ));
        }
    }

    #[test]
    fn function_switch_replays_named_keyof_no_match_flow_without_publication() {
        let fixture = JoinedFixture::new(
            concat!(
                "interface Choices { first: string; second: number; }\n",
                "function choose<T extends keyof Choices>(key: T): number {\n",
                "  switch (key) {\n",
                "    case 'first': return 1;\n",
                "    case 'second': return 2;\n",
                "  }\n",
                "}\n",
            ),
            FileId::new(1_335),
        );
        let callable = fixture.callable();
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.mapper_len(),
        );
        let first = plan_source_switch_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();
        let second = plan_source_switch_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();

        assert_eq!(first, second);
        assert!(first.no_match_flow.is_some());
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.mapper_len(),
            ),
            before,
        );
    }

    #[test]
    fn typeof_switch_retains_grouped_case_and_narrowed_expression() {
        let fixture = JoinedFixture::new(
            concat!(
                "function choose(value: string | number) {\n",
                "  switch (typeof value) {\n",
                "    case '':\n",
                "    case 'string':\n",
                "      value.charAt(0);\n",
                "      break;\n",
                "  }\n",
                "}\n",
            ),
            FileId::new(1_336),
        );
        let callable = fixture.callable();
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.mapper_len(),
        );
        let first = plan_source_typeof_switch_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();
        let second = plan_source_typeof_switch_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();

        assert_eq!(first, second);
        assert_eq!(first.switch.clauses.len(), 2);
        let [expression] = first.expressions.as_slice() else {
            panic!("expected one grouped switch expression")
        };
        assert_eq!(expression.tag, SourceTypeofTag::String);
        assert_eq!(expression.clause, first.switch.clauses[1].clause);
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(expression.expression.node)
                .unwrap()
                .kind,
            SyntaxKind::CallExpression,
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.mapper_len(),
            ),
            before,
        );
    }

    #[test]
    fn typeof_switch_rejects_unknown_execution_tags_and_missing_breaks() {
        for (index, source) in [
            "function f(value: string) { switch (typeof value) { case 'other': value.charAt(0); break; } }",
            "function f(value: string) { switch (typeof value) { case 'string': value.charAt(0); } }",
            "function f(value: string) { switch (typeof value) { default: value.charAt(0); break; } }",
            "function f(value: string, other: string) { switch (typeof other) { case 'string': value.charAt(0); break; } }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_337 + u32::try_from(index).unwrap()));
            let callable = fixture.callable();
            assert!(
                matches!(
                    plan_source_typeof_switch_function_statements_syntax(
                        &fixture.parsed.arena,
                        &fixture.bound,
                        &fixture.store,
                        &callable,
                    ),
                    Err(SourceFunctionStatementsError::Unsupported(_)),
                ),
                "{source}",
            );
        }
    }

    #[test]
    fn function_switch_rejects_nonexhaustive_or_nonliteral_shapes() {
        for (index, source) in [
            "function f(level) { switch (level) { case 0: return \"value\"; } }",
            "function f(level) { switch (level) { default: return; } }",
            "function f(level) { switch (level) { case level: return \"value\"; default: return \"fallback\"; } }",
            "function f(level) { switch (level) { default: return level; } }",
            "function f(level) { switch (level) { default: return \"first\"; return \"second\"; } }",
            "function f(level) { switch (level) { default: return \"first\"; case 0: return \"second\"; } }",
            "function f(level) { switch (level + 1) { default: return \"value\"; } }",
            "function f(level) { switch ((level)) { default: return \"value\"; } }",
            "function f(level) { switch (level) { case 0: case 1: default: } }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = JoinedFixture::new(
                source,
                FileId::new(1_243 + u32::try_from(index).unwrap()),
            );
            let callable = fixture.callable();
            assert!(matches!(
                plan_source_switch_function_statements_syntax(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    &fixture.store,
                    &callable,
                ),
                Err(SourceFunctionStatementsError::Unsupported(_)),
            ));
        }
    }

    #[test]
    fn switch_clauses_group_consecutive_unreachable_statements() {
        let source = concat!(
            "function choose(value: string): void {\n",
            "  switch (value) {\n",
            "    case 'first':\n",
            "      return;\n",
            "      value;\n",
            "      value;\n",
            "    default:\n",
            "      return;\n",
            "      value;\n",
            "  }\n",
            "}\n",
        );
        let fixture = JoinedFixture::new(source, FileId::new(1_241));
        let (statement, parent) = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::SwitchStatement).then_some((
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, node),
                    NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        record.parent.unwrap(),
                    ),
                ))
            })
            .unwrap();
        let syntax = plan_source_control_switch_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            statement,
            parent,
        )
        .unwrap();
        let [first, default] = syntax.clauses.as_slice() else {
            panic!("expected one case and one default clause")
        };
        assert_eq!(first.unreachable_ranges.len(), 1);
        assert_eq!(default.unreachable_ranges.len(), 1);
        let range = first.unreachable_ranges[0].range();
        let start = usize::try_from(range.start.get()).unwrap();
        let end = usize::try_from(range.end.get()).unwrap();
        assert_eq!(source.get(start..end).unwrap(), "value;\n      value;");
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
    fn joined_branches_preserve_unique_labels_but_reject_conditional_var() {
        let accepted = JoinedFixture::new(
            concat!(
                "function labeled(value: string | undefined): string | undefined {\n",
                "  before: ;\n",
                "  if (value) {\n",
                "    truthy: { const selected: string = value; }\n",
                "  } else {\n",
                "    falsy: { const rejected: string | undefined = value; }\n",
                "  }\n",
                "  after: ;\n",
                "  return value;\n",
                "}\n",
            ),
            FileId::new(1_277),
        );
        let syntax = accepted.plan().unwrap();
        assert_eq!(syntax.joined_if.then_branch.locals.len(), 1);
        assert_eq!(syntax.joined_if.else_branch.locals.len(), 1);

        let rejected = JoinedFixture::new(
            concat!(
                "function conditional(value: string | undefined): string | undefined {\n",
                "  if (value) { var selected = value; }\n",
                "  return value;\n",
                "}\n",
            ),
            FileId::new(1_278),
        );
        assert!(matches!(
            rejected.plan(),
            Err(SourceJoinedFunctionStatementsError::Statements(
                SourceFunctionStatementsError::Unsupported(
                    SourceFunctionStatementsUnsupported::BindingKind(_),
                ),
            )),
        ));
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
