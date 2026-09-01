//! Source-ordered callable statements and their binder identities.
//!
//! Returning branches retain local declarations, expression statements, and
//! their actual return nodes. A trailing return path can supply the false path
//! of an if without an else. Fallthrough branches retain their calls and local
//! declarations before the final return. Expression checking, narrowing, and
//! return inference stay in the source checker.
//! The common statement list retains nested blocks and conditional early returns
//! for synchronous nongeneric functions and arrows. Its leaves use these same
//! local, expression, condition, and return syntax checks.

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
    source_callables::{
        SourceCallableFamily, SourceCallablePlan, source_parameter_declarations_are_exact,
    },
    source_flow::{SourceTypeofComparison, SourceTypeofTag},
    variables::{VariableBindingKind, VariablePlanError, plan_top_level_variable},
};

const NODE_FLAG_LET: u32 = 1 << 0;
const NODE_FLAG_CONST: u32 = 1 << 1;
const MAX_NESTED_CAPTURED_LOOPS: usize = 8;
const MAX_CALLABLE_STATEMENT_DEPTH: usize = 64;

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
    pub(super) initializer: Option<NodeRef>,
}

/// One exact `if` arm ending in a value-returning `return`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceReturnBranchSyntax {
    pub(super) block: Option<NodeRef>,
    pub(super) locals: Vec<SourceLocalDeclarationSyntax>,
    pub(super) statements: Vec<SourceLinearFunctionStatementSyntax>,
    pub(super) return_statement: NodeRef,
    pub(super) return_expression: NodeRef,
}

/// One returning `if`, with an explicit else or the actual trailing return path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceFinalIfSyntax {
    pub(super) statement: NodeRef,
    pub(super) condition: NodeRef,
    pub(super) condition_identifier: Option<NodeRef>,
    pub(super) typeof_condition: Option<SourceTypeofConditionSyntax>,
    pub(super) equality_condition: Option<SourceEqualityConditionSyntax>,
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

/// One top-level `for...of` loop with a direct call or an iteration-property read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceForOfStatementSyntax {
    pub(super) control: SourceControlLoopSyntax,
    pub(super) declaration: NodeRef,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) body_statement: NodeRef,
    pub(super) call: NodeRef,
    pub(super) binding_flow: FlowRef,
}

/// One ordinary top-level `for`, retaining its real declarations and jump targets.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceForStatementSyntax {
    pub(super) control: SourceControlLoopSyntax,
    pub(super) initializers: Vec<SourceLocalDeclarationSyntax>,
    pub(super) statements: Vec<SourceCapturedIterationStatementSyntax>,
    pub(super) terminal_jump: Option<NodeRef>,
}

/// One expression statement retained inside an authenticated `for...in` body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceForInBodyStatementSyntax {
    pub(super) statement: NodeRef,
    pub(super) expression: NodeRef,
}

/// One binder-owned identifier retained from an iteration declaration or array pattern.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceIterationBindingSyntax {
    pub(super) declaration: NodeRef,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

/// One lexical `for...in` or callable-owned `for...of` iteration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceForInStatementSyntax {
    pub(super) control: SourceControlLoopSyntax,
    pub(super) declaration: NodeRef,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) binding: VariableBindingKind,
    pub(super) bindings: Vec<SourceIterationBindingSyntax>,
    pub(super) body_statements: Vec<SourceForInBodyStatementSyntax>,
    pub(super) locals: Vec<SourceLocalDeclarationSyntax>,
    pub(super) statements: Vec<SourceLoopFunctionStatementSyntax>,
    pub(super) trailing_statements: Vec<SourceForInBodyStatementSyntax>,
    pub(super) binding_flow: Option<FlowRef>,
}

/// The single unused declaration retained inside an iteration body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceUnusedIterationDeclarationKind {
    Function,
    ArrowVariable,
}

/// One loop containing an unused local callable that reads its iteration binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceUnusedIterationStatementSyntax {
    pub(super) control: SourceControlLoopSyntax,
    pub(super) binding: VariableBindingKind,
    pub(super) binding_declaration: NodeRef,
    pub(super) binding_element: Option<NodeRef>,
    pub(super) binding_name: NodeRef,
    pub(super) binding_symbol: SemanticSymbolId,
    pub(super) local_kind: SourceUnusedIterationDeclarationKind,
    pub(super) local_statement: NodeRef,
    pub(super) local_declaration: NodeRef,
    pub(super) local_name: NodeRef,
    pub(super) local_symbol: SemanticSymbolId,
    pub(super) callable: NodeRef,
    pub(super) callable_symbol: SemanticSymbolId,
    pub(super) capture_statement: NodeRef,
    pub(super) capture: NodeRef,
}

/// One identifier or shorthand object binding owned by a top-level loop.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceCapturedIterationBindingSyntax {
    pub(super) declaration: NodeRef,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) binding: VariableBindingKind,
    pub(super) initializer: Option<NodeRef>,
    pub(super) destructured: bool,
}

/// One standalone capture or authenticated conditional loop jump.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCapturedIterationStatementSyntax {
    Local(SourceLocalDeclarationSyntax),
    Expression(NodeRef),
    ConditionalJump { condition: NodeRef, jump: NodeRef },
}

/// One loop-local callable or a source-ordered set of captures and jumps.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SourceCapturedIterationBodySyntax {
    Function {
        declaration: NodeRef,
        name: NodeRef,
        symbol: SemanticSymbolId,
        read: NodeRef,
    },
    ArrowVariable {
        declaration: NodeRef,
        name: NodeRef,
        symbol: SemanticSymbolId,
        binding: VariableBindingKind,
        arrow: NodeRef,
        read: NodeRef,
    },
    ControlFlow(Vec<SourceCapturedIterationStatementSyntax>),
}

/// One top-level lexical loop with authenticated captures and optional labels.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceCapturedIterationSyntax {
    pub(super) labels: Vec<NodeRef>,
    pub(super) control: SourceControlLoopSyntax,
    pub(super) binding: SourceCapturedIterationBindingSyntax,
    pub(super) additional_bindings: Vec<SourceCapturedIterationBindingSyntax>,
    pub(super) body: SourceCapturedIterationBodySyntax,
}

/// One top-level `while` or `do...while` that captures its block-owned locals.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceCapturedBlockLoopSyntax {
    pub(super) control: SourceControlLoopSyntax,
    pub(super) statements: Vec<SourceCapturedIterationStatementSyntax>,
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

/// Exact source nodes retained for one literal or discriminant comparison.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceEqualityConditionSyntax {
    pub(super) operand: NodeRef,
    pub(super) identifier: NodeRef,
    pub(super) discriminant: Option<NodeRef>,
    pub(super) operator: NodeRef,
    pub(super) value: NodeRef,
    pub(super) comparison: SourceTypeofComparison,
    pub(super) strict: bool,
    pub(super) operand_on_left: bool,
}

/// Source-ordered declarations and expressions before two returning paths.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) leading: Vec<SourceLocalDeclarationSyntax>,
    pub(super) leading_statements: Vec<SourceLinearFunctionStatementSyntax>,
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
    Throw {
        statement: NodeRef,
        expression: NodeRef,
    },
}

/// Direct property guard and RHS call syntax, before member and flow checks.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceLinearLogicalStatementSyntax {
    pub(super) container: NodeRef,
    pub(super) statement: NodeRef,
    pub(super) expression: NodeRef,
    pub(super) left: NodeRef,
    pub(super) left_receiver: NodeRef,
    pub(super) left_name: NodeRef,
    pub(super) operator: NodeRef,
    pub(super) right: NodeRef,
    pub(super) callee: NodeRef,
    pub(super) right_receiver: NodeRef,
    pub(super) right_name: NodeRef,
    pub(super) arguments: Vec<NodeRef>,
}

/// One function-owned enum, including the binder's reachability classification.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceLocalEnumStatementSyntax {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) is_const: bool,
    pub(super) unreachable: bool,
}

/// Ordered local statements with a final return or a throw and unreachable expressions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceLinearFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) locals: Vec<SourceLocalDeclarationSyntax>,
    pub(super) statements: Vec<SourceLinearFunctionStatementSyntax>,
    pub(super) return_statement: Option<NodeRef>,
    pub(super) return_expression: Option<NodeRef>,
    pub(super) unreachable_ranges: Vec<CanonicalCheckerDiagnosticRange>,
}

/// One source-owned statement list shared by functions and arrows.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceCallableStatementListSyntax {
    pub(super) callable: SourceCallablePlan,
    pub(super) statements: Vec<SourceCallableStatementSyntax>,
    pub(super) has_implicit_return: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableStatementSyntax {
    Leaf(SourceLinearFunctionStatementSyntax),
    Empty(NodeRef),
    Block {
        block: NodeRef,
        statements: Vec<Self>,
    },
    If(Box<SourceCallableIfSyntax>),
    Return {
        statement: NodeRef,
        expression: Option<NodeRef>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceCallableIfSyntax {
    pub(super) control: SourceControlIfSyntax,
    pub(super) condition_identifier: Option<NodeRef>,
    pub(super) typeof_condition: Option<SourceTypeofConditionSyntax>,
    pub(super) equality_condition: Option<SourceEqualityConditionSyntax>,
    pub(super) then_statements: Vec<SourceCallableStatementSyntax>,
    pub(super) else_statements: Vec<SourceCallableStatementSyntax>,
}

impl SourceCallableStatementListSyntax {
    /// Returns only the lexical scope retained by the complete source walk.
    pub(super) fn statement_scope(&self, wanted: NodeRef) -> Option<NodeRef> {
        self.find_statement_scope(wanted, true)
    }

    /// Local writes remain limited to the list and its unconditional blocks.
    pub(super) fn linear_statement_scope(&self, wanted: NodeRef) -> Option<NodeRef> {
        self.find_statement_scope(wanted, false)
    }

    fn find_statement_scope(&self, wanted: NodeRef, include_branches: bool) -> Option<NodeRef> {
        let mut pending = self
            .statements
            .iter()
            .map(|statement| (statement, self.callable.declaration))
            .collect::<Vec<_>>();
        while let Some((statement, scope)) = pending.pop() {
            let node = match statement {
                SourceCallableStatementSyntax::Leaf(
                    SourceLinearFunctionStatementSyntax::Local(local),
                ) => local.statement,
                SourceCallableStatementSyntax::Leaf(
                    SourceLinearFunctionStatementSyntax::Expression { statement, .. },
                )
                | SourceCallableStatementSyntax::Return { statement, .. } => *statement,
                SourceCallableStatementSyntax::Empty(node) => *node,
                SourceCallableStatementSyntax::Block { block, statements } => {
                    pending.extend(statements.iter().map(|statement| (statement, *block)));
                    *block
                }
                SourceCallableStatementSyntax::If(branch) => {
                    if include_branches {
                        pending.extend(
                            branch
                                .then_statements
                                .iter()
                                .map(|statement| (statement, scope)),
                        );
                        pending.extend(
                            branch
                                .else_statements
                                .iter()
                                .map(|statement| (statement, scope)),
                        );
                    }
                    branch.control.statement
                }
                SourceCallableStatementSyntax::Leaf(_) => return None,
            };
            if node == wanted {
                return Some(scope);
            }
        }
        None
    }

    pub(super) fn expression_scope(&self, wanted: NodeRef) -> Option<NodeRef> {
        let mut pending = self.statements.iter().collect::<Vec<_>>();
        while let Some(statement) = pending.pop() {
            match statement {
                SourceCallableStatementSyntax::Leaf(
                    SourceLinearFunctionStatementSyntax::Expression {
                        statement,
                        expression,
                    },
                ) if *expression == wanted => return self.statement_scope(*statement),
                SourceCallableStatementSyntax::Block { statements, .. } => {
                    pending.extend(statements)
                }
                SourceCallableStatementSyntax::If(branch) => {
                    pending.extend(&branch.then_statements);
                    pending.extend(&branch.else_statements);
                }
                _ => {}
            }
        }
        None
    }
}

/// One initialized lexical declaration or expression inside a loop body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SourceLoopFunctionStatementSyntax {
    Local(SourceLocalDeclarationSyntax),
    Loop(Box<SourceLoopFunctionStatementsSyntax>),
    Expression {
        statement: NodeRef,
        expression: NodeRef,
    },
    ConditionalJump {
        statement: NodeRef,
        condition: NodeRef,
        jump: NodeRef,
    },
    ConditionalReturn {
        statement: NodeRef,
        condition: NodeRef,
        returned: NodeRef,
        expression: Option<NodeRef>,
    },
}

/// One function-owned lexical `for`, `while`, or `do...while` block.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceLoopFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) control: SourceControlLoopSyntax,
    pub(super) labels: Vec<NodeRef>,
    pub(super) initializers: Vec<SourceLocalDeclarationSyntax>,
    pub(super) locals: Vec<SourceLocalDeclarationSyntax>,
    pub(super) statements: Vec<SourceLoopFunctionStatementSyntax>,
    pub(super) trailing_statements: Vec<SourceForInBodyStatementSyntax>,
}

/// One binder-owned shorthand, renamed, or static-computed switch binding.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceSwitchObjectBindingElementSyntax {
    pub(super) element: NodeRef,
    pub(super) property: NodeRef,
    pub(super) computed_key: Option<NodeRef>,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

/// One `const { kind, value } = source` immediately before its switch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceSwitchObjectBindingSyntax {
    pub(super) statement: NodeRef,
    pub(super) initializer: NodeRef,
    pub(super) elements: Vec<SourceSwitchObjectBindingElementSyntax>,
}

/// One named array binding, with optional omissions, before a switch-clause return.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceSwitchArrayBindingSyntax {
    pub(super) statement: NodeRef,
    pub(super) pattern: NodeRef,
    pub(super) element: NodeRef,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) initializer: NodeRef,
}

/// One value return owned directly by a grouped switch clause.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceSwitchReturnSyntax {
    pub(super) clause: NodeRef,
    pub(super) statement: NodeRef,
    pub(super) expression: NodeRef,
    pub(super) binding: Option<SourceSwitchArrayBindingSyntax>,
}

/// One function-body switch with optional correlated bindings and exhaustive returns.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceSwitchFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) leading: Option<SourceSwitchObjectBindingSyntax>,
    pub(super) switch: SourceControlSwitchSyntax,
    pub(super) returns: Vec<SourceSwitchReturnSyntax>,
    /// A no-default edge that still requires canonical constraint coverage proof.
    pub(super) no_match_flow: Option<FlowRef>,
}

/// One direct call retained from a reachable or unreachable switch clause.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceVoidSwitchCallSyntax {
    pub(super) statement: NodeRef,
    pub(super) expression: NodeRef,
    pub(super) unreachable: bool,
}

/// An inferred-void string switch containing bare returns and direct calls.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceVoidSwitchFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) switch: SourceControlSwitchSyntax,
    pub(super) returns: Vec<NodeRef>,
    pub(super) calls: Vec<SourceVoidSwitchCallSyntax>,
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

/// One fallthrough arm containing source-ordered locals and expressions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceFallthroughBranchSyntax {
    pub(super) block: Option<NodeRef>,
    pub(super) locals: Vec<SourceLocalDeclarationSyntax>,
    pub(super) statements: Vec<SourceLinearFunctionStatementSyntax>,
}

/// The exact joined `if` and its original condition nodes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceJoinedIfSyntax {
    pub(super) statement: NodeRef,
    pub(super) condition: NodeRef,
    /// The narrowed identifier when available, otherwise the condition root.
    pub(super) condition_identifier: NodeRef,
    pub(super) typeof_condition: Option<SourceTypeofConditionSyntax>,
    pub(super) equality_condition: Option<SourceEqualityConditionSyntax>,
    pub(super) then_branch: SourceFallthroughBranchSyntax,
    pub(super) else_branch: SourceFallthroughBranchSyntax,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PlannedConditionSyntax {
    identifier: NodeRef,
    typeof_condition: Option<SourceTypeofConditionSyntax>,
    equality_condition: Option<SourceEqualityConditionSyntax>,
}

/// Complete source-ordered syntax for the first post-`if` join vertical.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceJoinedFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) leading: Vec<SourceLocalDeclarationSyntax>,
    pub(super) leading_statements: Vec<SourceLinearFunctionStatementSyntax>,
    pub(super) joined_if: SourceJoinedIfSyntax,
    pub(super) trailing: Vec<SourceLocalDeclarationSyntax>,
    pub(super) trailing_statements: Vec<SourceLinearFunctionStatementSyntax>,
    pub(super) return_statement: NodeRef,
    pub(super) return_expression: NodeRef,
}

/// Valid source forms intentionally outside the first post-`if` join slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceJoinedFunctionStatementsUnsupported {
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
        statement_scope: None,
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

/// Uses the binder's loop scope. Expression support remains in the source checker.
#[allow(clippy::too_many_lines)]
pub(super) fn plan_source_for_statement_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    root: NodeRef,
) -> Result<SourceForStatementSyntax, SourceFunctionStatementsError> {
    let source = bound.source_file();
    let mut statement = root;
    let mut parent = source;
    let mut labels = Vec::new();
    let mut visited = HashSet::new();
    while control_statement_node(arena, bound, statement)?.kind == SyntaxKind::LabeledStatement {
        if !visited.insert(statement) {
            return Err(unsupported_control_statement(
                statement,
                SyntaxKind::LabeledStatement,
            ));
        }
        let NodeData::LabeledStatement(labeled) =
            &control_statement_node(arena, bound, statement)?.data
        else {
            return Err(unsupported_control_statement(
                statement,
                SyntaxKind::LabeledStatement,
            ));
        };
        labels.push(NodeRef::new(statement.arena, statement.file, labeled.label));
        let child = validate_labeled_statement(arena, bound, statement, parent)?;
        parent = statement;
        statement = child;
    }
    let control = plan_source_control_loop_syntax(arena, bound, statement, parent)?;
    if control.kind != SourceControlLoopKind::For
        || bound.container(statement) != Some(source)
        || bound.block_scope_container(statement) != Some(source)
    {
        return Err(unsupported_control_statement(
            statement,
            control_statement_node(arena, bound, statement)?.kind,
        ));
    }
    for child in control.ordered_nodes() {
        if bound.block_scope_container(child) != Some(statement) {
            return Err(
                SourceFunctionStatementsInvariant::InvalidBlockScopeContainer {
                    node: child,
                    expected: statement,
                    actual: bound.block_scope_container(child),
                }
                .into(),
            );
        }
    }
    let initializers = match control.initializer {
        Some(list)
            if control_statement_node(arena, bound, list)?.kind
                == SyntaxKind::VariableDeclarationList =>
        {
            plan_source_loop_declaration_list(
                arena, bound, store, statement, statement, list, true,
            )?
        }
        _ => Vec::new(),
    };
    let body = control_statement_node(arena, bound, control.body)?;
    if let NodeData::EmptyStatement(empty) = &body.data
        && body.kind == SyntaxKind::EmptyStatement
        && body.flags.0 == 0
        && empty.flow_node.is_none()
    {
        return Ok(SourceForStatementSyntax {
            control,
            initializers,
            statements: Vec::new(),
            terminal_jump: None,
        });
    }
    let NodeData::Block(block) = &body.data else {
        return Err(unsupported_control_statement(control.body, body.kind));
    };
    if body.kind != SyntaxKind::Block
        || body.flags.0 != 0
        || block.flow_node.is_some()
        || block.next_container.is_some()
        || block.statements.has_trailing_comma
        || block.statements.range.start < body.range.start
        || block.statements.range.end > body.range.end
        || block.facts != 0
    {
        return Err(unsupported_control_statement(control.body, body.kind));
    }
    let mut statements = Vec::new();
    let mut terminal_jump = None;
    let mut previous_end = block.statements.range.start;
    for (index, node) in block.statements.nodes.iter().enumerate() {
        let current = NodeRef::new(statement.arena, statement.file, *node);
        validate_control_statement_child(arena, bound, control.body, current, source)?;
        let record = control_statement_node(arena, bound, current)?;
        if record.flags.0 != 0
            || record.range.start < previous_end
            || record.range.end > block.statements.range.end
            || bound.block_scope_container(current) != Some(control.body)
        {
            return Err(unsupported_control_statement(current, record.kind));
        }
        previous_end = record.range.end;
        match &record.data {
            NodeData::VariableStatement(variable)
                if record.kind == SyntaxKind::VariableStatement =>
            {
                if variable.modifiers.is_some()
                    || variable.flow_node.is_some()
                    || variable.facts != 0
                {
                    return Err(unsupported_control_statement(current, record.kind));
                }
                let list = NodeRef::new(current.arena, current.file, variable.declaration_list);
                statements.extend(
                    plan_source_loop_declaration_list(
                        arena,
                        bound,
                        store,
                        control.body,
                        current,
                        list,
                        false,
                    )?
                    .into_iter()
                    .map(SourceCapturedIterationStatementSyntax::Local),
                );
            }
            NodeData::ExpressionStatement(expression)
                if record.kind == SyntaxKind::ExpressionStatement
                    && expression.flow_node.is_none() =>
            {
                let expression = NodeRef::new(current.arena, current.file, expression.expression);
                validate_control_statement_child(arena, bound, current, expression, source)?;
                if bound.block_scope_container(expression) != Some(control.body) {
                    return Err(unsupported_control_statement(
                        expression,
                        control_statement_node(arena, bound, expression)?.kind,
                    ));
                }
                statements.push(SourceCapturedIterationStatementSyntax::Expression(
                    expression,
                ));
            }
            NodeData::IfStatement(_) if record.kind == SyntaxKind::IfStatement => {
                let (condition, jump) = plan_captured_iteration_conditional_jump(
                    arena,
                    bound,
                    current,
                    control.body,
                    &labels,
                )?;
                statements.push(SourceCapturedIterationStatementSyntax::ConditionalJump {
                    condition,
                    jump,
                });
            }
            NodeData::EmptyStatement(empty)
                if record.kind == SyntaxKind::EmptyStatement && empty.flow_node.is_none() => {}
            NodeData::BreakStatement(_) | NodeData::ContinueStatement(_)
                if index + 1 == block.statements.nodes.len() =>
            {
                validate_source_iteration_jump(
                    arena,
                    bound,
                    current,
                    control.body,
                    control.body,
                    &labels,
                )?;
                terminal_jump = Some(current);
            }
            _ => return Err(unsupported_control_statement(current, record.kind)),
        }
    }
    Ok(SourceForStatementSyntax {
        control,
        initializers,
        statements,
        terminal_jump,
    })
}

/// Proves one canonical top-level iteration binding and its actual assignment flow.
pub(super) fn plan_source_for_of_statement_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<SourceForOfStatementSyntax, SourceFunctionStatementsError> {
    let source = bound.source_file();
    let control = plan_source_control_loop_syntax(arena, bound, statement, source)?;
    if control.kind != SourceControlLoopKind::ForOf {
        return Err(unsupported_control_statement(
            statement,
            SyntaxKind::ForOfStatement,
        ));
    }

    let list =
        control
            .initializer
            .ok_or(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                statement,
            ))?;
    let list_record = control_statement_node(arena, bound, list)?;
    let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
        return Err(unsupported_control_statement(list, list_record.kind));
    };
    let [declaration] = declarations.declarations.nodes.as_slice() else {
        return Err(unsupported_control_statement(list, list_record.kind));
    };
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || list_record.flags.0 != NODE_FLAG_CONST
        || list_record.parent != Some(statement.node)
        || declarations.declarations.has_trailing_comma
        || declarations.declarations.range.start <= list_record.range.start
        || declarations.declarations.range.end != list_record.range.end
        || declarations.facts != 0
        || bound.container(list) != Some(source)
        || bound.block_scope_container(list) != Some(statement)
    {
        return Err(unsupported_control_statement(list, list_record.kind));
    }

    let declaration = NodeRef::new(list.arena, list.file, *declaration);
    let declaration_record = control_statement_node(arena, bound, declaration)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(unsupported_control_statement(
            declaration,
            declaration_record.kind,
        ));
    };
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || declaration_record.parent != Some(list.node)
        || declaration_record.range != declarations.declarations.range
        || variable.exclamation_token.is_some()
        || variable.initializer.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.type_.is_some()
        || variable.facts != 0
        || bound.container(declaration) != Some(source)
        || bound.block_scope_container(declaration) != Some(statement)
    {
        return Err(unsupported_control_statement(
            declaration,
            declaration_record.kind,
        ));
    }

    let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let name_record = control_statement_node(arena, bound, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported_control_statement(name, name_record.kind));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || bound.container(name) != Some(source)
        || bound.block_scope_container(name) != Some(statement)
    {
        return Err(unsupported_control_statement(name, name_record.kind));
    }
    let symbol = plan_top_level_variable(
        bound,
        store,
        declaration,
        name,
        &identifier.text,
        VariableBindingKind::Const,
        false,
    )?;
    let locals = bound
        .locals(statement)
        .ok_or(SourceFunctionStatementsInvariant::MissingLocals(statement))?;
    let actual = store
        .symbol_table(locals)
        .and_then(|locals| locals.get_source(&identifier.text));
    if actual != Some(symbol) {
        return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
            declaration,
            scope: statement,
            expected: symbol,
            actual,
        }
        .into());
    }

    let body_record = control_statement_node(arena, bound, control.body)?;
    let NodeData::Block(body) = &body_record.data else {
        return Err(unsupported_control_statement(
            control.body,
            body_record.kind,
        ));
    };
    let [body_statement] = body.statements.nodes.as_slice() else {
        return Err(unsupported_control_statement(
            control.body,
            body_record.kind,
        ));
    };
    if body_record.kind != SyntaxKind::Block
        || body_record.flags.0 != 0
        || body_record.parent != Some(statement.node)
        || body.flow_node.is_some()
        || body.next_container.is_some()
        || body.statements.has_trailing_comma
        || body.facts != 0
        || bound.container(control.body) != Some(source)
        || bound.block_scope_container(control.body) != Some(statement)
    {
        return Err(unsupported_control_statement(
            control.body,
            body_record.kind,
        ));
    }

    let body_statement = NodeRef::new(control.body.arena, control.body.file, *body_statement);
    let body_statement_record = control_statement_node(arena, bound, body_statement)?;
    let NodeData::ExpressionStatement(expression) = &body_statement_record.data else {
        return Err(unsupported_control_statement(
            body_statement,
            body_statement_record.kind,
        ));
    };
    if body_statement_record.kind != SyntaxKind::ExpressionStatement
        || body_statement_record.flags.0 != 0
        || body_statement_record.parent != Some(control.body.node)
        || expression.flow_node.is_some()
        || bound.container(body_statement) != Some(source)
        || bound.block_scope_container(body_statement) != Some(control.body)
    {
        return Err(unsupported_control_statement(
            body_statement,
            body_statement_record.kind,
        ));
    }

    let call = NodeRef::new(
        body_statement.arena,
        body_statement.file,
        expression.expression,
    );
    let call_record = control_statement_node(arena, bound, call)?;
    if call_record.flags.0 != 0
        || call_record.parent != Some(body_statement.node)
        || bound.container(call) != Some(source)
        || bound.block_scope_container(call) != Some(control.body)
    {
        return Err(unsupported_control_statement(call, call_record.kind));
    }
    let reads = match &call_record.data {
        NodeData::CallExpression(call_data) if call_record.kind == SyntaxKind::CallExpression => {
            let [argument] = call_data.arguments.nodes.as_slice() else {
                return Err(unsupported_control_statement(call, call_record.kind));
            };
            if call_data.question_dot_token.is_some()
                || call_data.symbol.is_some()
                || call_data.type_arguments.is_some()
                || call_data.arguments.has_trailing_comma
                || call_data.facts != 0
            {
                return Err(unsupported_control_statement(call, call_record.kind));
            }
            let callee = NodeRef::new(call.arena, call.file, call_data.expression);
            let callee_record = control_statement_node(arena, bound, callee)?;
            let NodeData::Identifier(callee_name) = &callee_record.data else {
                return Err(unsupported_control_statement(callee, callee_record.kind));
            };
            let argument = NodeRef::new(call.arena, call.file, *argument);
            let argument_record = control_statement_node(arena, bound, argument)?;
            let NodeData::Identifier(argument_name) = &argument_record.data else {
                return Err(unsupported_control_statement(
                    argument,
                    argument_record.kind,
                ));
            };
            if callee_record.kind != SyntaxKind::Identifier
                || callee_record.flags.0 != 0
                || callee_record.parent != Some(call.node)
                || callee_name.flow_node.is_some()
                || callee_name.text.is_empty()
                || argument_record.kind != SyntaxKind::Identifier
                || argument_record.flags.0 != 0
                || argument_record.parent != Some(call.node)
                || argument_name.flow_node.is_some()
                || argument_name.text != identifier.text
                || bound.container(callee) != Some(source)
                || bound.container(argument) != Some(source)
                || bound.block_scope_container(callee) != Some(control.body)
                || bound.block_scope_container(argument) != Some(control.body)
            {
                return Err(unsupported_control_statement(call, call_record.kind));
            }
            vec![callee, argument]
        }
        NodeData::PropertyAccessExpression(property)
            if call_record.kind == SyntaxKind::PropertyAccessExpression =>
        {
            let receiver = NodeRef::new(call.arena, call.file, property.expression);
            let receiver_record = control_statement_node(arena, bound, receiver)?;
            let NodeData::Identifier(receiver_name) = &receiver_record.data else {
                return Err(unsupported_control_statement(
                    receiver,
                    receiver_record.kind,
                ));
            };
            let property_name = NodeRef::new(call.arena, call.file, property.name);
            let property_record = control_statement_node(arena, bound, property_name)?;
            let NodeData::Identifier(property_identifier) = &property_record.data else {
                return Err(unsupported_control_statement(
                    property_name,
                    property_record.kind,
                ));
            };
            if property.flow_node.is_some()
                || property.question_dot_token.is_some()
                || property.facts != 0
                || receiver_record.kind != SyntaxKind::Identifier
                || receiver_record.flags.0 != 0
                || receiver_record.parent != Some(call.node)
                || receiver_name.flow_node.is_some()
                || receiver_name.text != identifier.text
                || property_record.kind != SyntaxKind::Identifier
                || property_record.flags.0 != 0
                || property_record.parent != Some(call.node)
                || property_identifier.flow_node.is_some()
                || property_identifier.text.is_empty()
                || bound.container(receiver) != Some(source)
                || bound.container(property_name) != Some(source)
                || bound.block_scope_container(receiver) != Some(control.body)
                || bound.block_scope_container(property_name) != Some(control.body)
            {
                return Err(unsupported_control_statement(call, call_record.kind));
            }
            vec![receiver]
        }
        _ => return Err(unsupported_control_statement(call, call_record.kind)),
    };

    let graph = bound.flow_graph();
    let binding_flow = bound.flow_at(body_statement).ok_or(
        SourceFunctionStatementsInvariant::InvalidFlowContainer {
            node: body_statement,
            expected: source,
            actual: bound.flow_container(body_statement),
        },
    )?;
    let binding_node = graph.nodes().get(binding_flow).ok_or(
        SourceFunctionStatementsInvariant::InvalidFlowContainer {
            node: body_statement,
            expected: source,
            actual: bound.flow_container(body_statement),
        },
    )?;
    if joined_semantic_flow_flags(binding_node.flags) != FlowFlags::ASSIGNMENT.bits()
        || binding_node.payload != Some(FlowNodePayload::Ast(declaration))
        || binding_node.antecedent.is_none()
        || !binding_node.antecedents.is_empty()
        || bound.flow_container(body_statement) != Some(source)
        || reads.iter().any(|read| {
            bound.flow_container(*read) != Some(source)
                || bound.flow_at(*read) != Some(binding_flow)
        })
    {
        return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
            node: body_statement,
            expected: source,
            actual: bound.flow_container(body_statement),
        }
        .into());
    }

    Ok(SourceForOfStatementSyntax {
        control,
        declaration,
        name,
        symbol,
        body_statement,
        call,
        binding_flow,
    })
}

/// Proves one top-level string key and every direct expression in its body.
pub(super) fn plan_source_for_in_statement_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<SourceForInStatementSyntax, SourceFunctionStatementsError> {
    let source = bound.source_file();
    plan_source_scoped_iteration_statement_syntax(
        arena,
        bound,
        store,
        statement,
        (source, source),
        SourceControlLoopKind::ForIn,
        None,
    )
}

/// Proves one labeled top-level string key and its direct expression statements.
pub(super) fn plan_source_labeled_for_in_statement_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
    parent: NodeRef,
) -> Result<SourceForInStatementSyntax, SourceFunctionStatementsError> {
    plan_source_scoped_iteration_statement_syntax(
        arena,
        bound,
        store,
        statement,
        (parent, bound.source_file()),
        SourceControlLoopKind::ForIn,
        None,
    )
}

/// Proves one function-owned `for...in` body and its lexical iteration binding.
pub(super) fn plan_source_function_for_in_statement_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    callable: &SourceCallablePlan,
) -> Result<SourceForInStatementSyntax, SourceFunctionStatementsError> {
    SyntaxPlanner {
        arena,
        bound,
        store,
        callable,
        statement_scope: None,
    }
    .plan_for_in()
}

/// Proves one function or arrow `for...of` body and its lexical iteration binding.
pub(super) fn plan_source_function_for_of_statement_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    callable: &SourceCallablePlan,
) -> Result<SourceForInStatementSyntax, SourceFunctionStatementsError> {
    SyntaxPlanner {
        arena,
        bound,
        store,
        callable,
        statement_scope: None,
    }
    .plan_for_of()
}

#[allow(clippy::too_many_lines)] // The loop, binding, body, and flow share one binder contract.
fn plan_source_scoped_iteration_statement_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
    parent_and_container: (NodeRef, NodeRef),
    expected_kind: SourceControlLoopKind,
    callable: Option<&SourceCallablePlan>,
) -> Result<SourceForInStatementSyntax, SourceFunctionStatementsError> {
    let (parent, container) = parent_and_container;
    let control = plan_source_control_loop_syntax(arena, bound, statement, parent)?;
    if control.kind != expected_kind
        || !matches!(
            expected_kind,
            SourceControlLoopKind::ForIn | SourceControlLoopKind::ForOf
        )
    {
        return Err(unsupported_control_statement(
            statement,
            if expected_kind == SourceControlLoopKind::ForOf {
                SyntaxKind::ForOfStatement
            } else {
                SyntaxKind::ForInStatement
            },
        ));
    }
    if bound.container(statement) != Some(container) {
        return Err(SourceFunctionStatementsInvariant::InvalidContainer {
            node: statement,
            expected: container,
            actual: bound.container(statement),
        }
        .into());
    }

    let list =
        control
            .initializer
            .ok_or(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                statement,
            ))?;
    let list_record = control_statement_node(arena, bound, list)?;
    let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
        return Err(unsupported_control_statement(list, list_record.kind));
    };
    let binding = match list_record.flags.0 {
        NODE_FLAG_LET => VariableBindingKind::Let,
        NODE_FLAG_CONST => VariableBindingKind::Const,
        _ => return Err(unsupported_control_statement(list, list_record.kind)),
    };
    let [declaration] = declarations.declarations.nodes.as_slice() else {
        return Err(unsupported_control_statement(list, list_record.kind));
    };
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || list_record.parent != Some(statement.node)
        || declarations.declarations.has_trailing_comma
        || declarations.declarations.range.start <= list_record.range.start
        || declarations.declarations.range.end != list_record.range.end
        || declarations.facts != 0
        || bound.container(list) != Some(container)
        || bound.block_scope_container(list) != Some(statement)
    {
        return Err(unsupported_control_statement(list, list_record.kind));
    }

    let declaration = NodeRef::new(list.arena, list.file, *declaration);
    let declaration_record = control_statement_node(arena, bound, declaration)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(unsupported_control_statement(
            declaration,
            declaration_record.kind,
        ));
    };
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || declaration_record.parent != Some(list.node)
        || declaration_record.range != declarations.declarations.range
        || variable.exclamation_token.is_some()
        || variable.initializer.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.type_.is_some()
        || variable.facts != 0
        || bound.container(declaration) != Some(container)
        || bound.block_scope_container(declaration) != Some(statement)
    {
        return Err(unsupported_control_statement(
            declaration,
            declaration_record.kind,
        ));
    }

    let locals = bound
        .locals(statement)
        .ok_or(SourceFunctionStatementsInvariant::MissingLocals(statement))?;
    let pattern = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let pattern_record = control_statement_node(arena, bound, pattern)?;
    let bindings = match &pattern_record.data {
        NodeData::Identifier(identifier) if pattern_record.kind == SyntaxKind::Identifier => {
            if pattern_record.flags.0 != 0
                || pattern_record.parent != Some(declaration.node)
                || identifier.flow_node.is_some()
                || identifier.text.is_empty()
                || bound.container(pattern) != Some(container)
                || bound.block_scope_container(pattern) != Some(statement)
            {
                return Err(unsupported_control_statement(pattern, pattern_record.kind));
            }
            let symbol = plan_top_level_variable(
                bound,
                store,
                declaration,
                pattern,
                &identifier.text,
                binding,
                false,
            )?;
            let actual = store
                .symbol_table(locals)
                .and_then(|locals| locals.get_source(&identifier.text));
            if actual != Some(symbol) {
                return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                    declaration,
                    scope: statement,
                    expected: symbol,
                    actual,
                }
                .into());
            }
            vec![SourceIterationBindingSyntax {
                declaration,
                name: pattern,
                symbol,
            }]
        }
        NodeData::BindingPattern(elements)
            if expected_kind == SourceControlLoopKind::ForOf
                && pattern_record.kind == SyntaxKind::ArrayBindingPattern =>
        {
            if pattern_record.flags.0 != 0
                || pattern_record.parent != Some(declaration.node)
                || elements.elements.has_trailing_comma
                || elements.elements.nodes.is_empty()
                || elements.elements.range != pattern_record.range
                || elements.facts != 0
                || bound.container(pattern) != Some(container)
                || bound.block_scope_container(pattern) != Some(statement)
                || bound.symbol(declaration).is_some()
            {
                return Err(unsupported_control_statement(pattern, pattern_record.kind));
            }
            let mut bindings = Vec::with_capacity(elements.elements.nodes.len());
            for &element in &elements.elements.nodes {
                let element = NodeRef::new(pattern.arena, pattern.file, element);
                let record = control_statement_node(arena, bound, element)?;
                let NodeData::BindingElement(data) = &record.data else {
                    return Err(unsupported_control_statement(element, record.kind));
                };
                if record.kind != SyntaxKind::BindingElement
                    || record.flags.0 != 0
                    || record.parent != Some(pattern.node)
                    || data.dot_dot_dot_token.is_some()
                    || data.flow_node.is_some()
                    || data.initializer.is_some()
                    || data.local_symbol.is_some()
                    || data.property_name.is_some()
                    || data.symbol.is_some()
                    || data.facts != 0
                    || bound.container(element) != Some(container)
                    || bound.block_scope_container(element) != Some(statement)
                {
                    return Err(unsupported_control_statement(element, record.kind));
                }
                let name = data
                    .name
                    .map(|node| NodeRef::new(element.arena, element.file, node))
                    .ok_or(SourceFunctionStatementsError::Unsupported(
                        SourceFunctionStatementsUnsupported::Syntax {
                            node: element,
                            kind: record.kind,
                            role: SourceFunctionStatementsRole::LocalName,
                        },
                    ))?;
                let name_record = control_statement_node(arena, bound, name)?;
                let NodeData::Identifier(identifier) = &name_record.data else {
                    return Err(unsupported_control_statement(name, name_record.kind));
                };
                if name_record.kind != SyntaxKind::Identifier
                    || name_record.flags.0 != 0
                    || name_record.parent != Some(element.node)
                    || identifier.flow_node.is_some()
                    || identifier.text.is_empty()
                    || bound.container(name) != Some(container)
                    || bound.block_scope_container(name) != Some(statement)
                {
                    return Err(unsupported_control_statement(name, name_record.kind));
                }
                let symbol = plan_top_level_variable(
                    bound,
                    store,
                    element,
                    name,
                    &identifier.text,
                    binding,
                    false,
                )?;
                let actual = store
                    .symbol_table(locals)
                    .and_then(|locals| locals.get_source(&identifier.text));
                if actual != Some(symbol) {
                    return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                        declaration: element,
                        scope: statement,
                        expected: symbol,
                        actual,
                    }
                    .into());
                }
                bindings.push(SourceIterationBindingSyntax {
                    declaration: element,
                    name,
                    symbol,
                });
            }
            bindings
        }
        _ => return Err(unsupported_control_statement(pattern, pattern_record.kind)),
    };
    let first_binding = bindings
        .first()
        .copied()
        .ok_or(SourceFunctionStatementsInvariant::MissingLocals(statement))?;
    let name = first_binding.name;
    let symbol = first_binding.symbol;

    let body_record = control_statement_node(arena, bound, control.body)?;
    let NodeData::Block(body) = &body_record.data else {
        return Err(unsupported_control_statement(
            control.body,
            body_record.kind,
        ));
    };
    if body_record.kind != SyntaxKind::Block
        || body_record.flags.0 != 0
        || body_record.parent != Some(statement.node)
        || body.flow_node.is_some()
        || body.next_container.is_some()
        || body.statements.has_trailing_comma
        || body.facts != 0
        || bound.container(control.body) != Some(container)
        || bound.block_scope_container(control.body) != Some(statement)
    {
        return Err(unsupported_control_statement(
            control.body,
            body_record.kind,
        ));
    }

    let mut body_statements = Vec::with_capacity(body.statements.nodes.len());
    let mut locals = Vec::new();
    let mut statements = Vec::with_capacity(body.statements.nodes.len());
    let mut previous = None;
    for node in &body.statements.nodes {
        let body_statement = NodeRef::new(control.body.arena, control.body.file, *node);
        let record = control_statement_node(arena, bound, body_statement)?;
        if record.flags.0 != 0
            || record.parent != Some(control.body.node)
            || bound.container(body_statement) != Some(container)
            || bound.block_scope_container(body_statement) != Some(control.body)
            || previous.is_some_and(|end| record.range.start < end)
        {
            return Err(unsupported_control_statement(body_statement, record.kind));
        }
        match &record.data {
            NodeData::ExpressionStatement(expression)
                if record.kind == SyntaxKind::ExpressionStatement
                    && expression.flow_node.is_none() =>
            {
                let expression = NodeRef::new(
                    body_statement.arena,
                    body_statement.file,
                    expression.expression,
                );
                let expression_record = control_statement_node(arena, bound, expression)?;
                if expression_record.parent != Some(body_statement.node)
                    || expression_record.range.start < record.range.start
                    || expression_record.range.end > record.range.end
                    || bound.container(expression) != Some(container)
                    || bound.block_scope_container(expression) != Some(control.body)
                {
                    return Err(unsupported_control_statement(
                        expression,
                        expression_record.kind,
                    ));
                }
                body_statements.push(SourceForInBodyStatementSyntax {
                    statement: body_statement,
                    expression,
                });
                statements.push(SourceLoopFunctionStatementSyntax::Expression {
                    statement: body_statement,
                    expression,
                });
            }
            NodeData::VariableStatement(_) if record.kind == SyntaxKind::VariableStatement => {
                let Some(callable) = callable.filter(|callable| callable.declaration == container)
                else {
                    return Err(unsupported_control_statement(body_statement, record.kind));
                };
                let declarations = SyntaxPlanner {
                    arena,
                    bound,
                    store,
                    callable,
                    statement_scope: None,
                }
                .plan_local_statement(body_statement, control.body, container)?;
                statements.extend(
                    declarations
                        .iter()
                        .copied()
                        .map(SourceLoopFunctionStatementSyntax::Local),
                );
                locals.extend(declarations);
            }
            _ => return Err(unsupported_control_statement(body_statement, record.kind)),
        }
        previous = Some(record.range.end);
    }

    let binding_flow = if let Some(first) = statements.first() {
        let first = match first {
            SourceLoopFunctionStatementSyntax::Local(local) => local.name,
            SourceLoopFunctionStatementSyntax::Loop(nested) => nested.control.statement,
            SourceLoopFunctionStatementSyntax::Expression { statement, .. }
            | SourceLoopFunctionStatementSyntax::ConditionalJump { statement, .. }
            | SourceLoopFunctionStatementSyntax::ConditionalReturn { statement, .. } => *statement,
        };
        let flow = bound.flow_at(first).ok_or(
            SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: first,
                expected: container,
                actual: bound.flow_container(first),
            },
        )?;
        let assignment = bound.flow_graph().nodes().get(flow).ok_or(
            SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: first,
                expected: container,
                actual: bound.flow_container(first),
            },
        )?;
        if joined_semantic_flow_flags(assignment.flags) != FlowFlags::ASSIGNMENT.bits()
            || assignment.payload
                != bindings
                    .last()
                    .map(|binding| FlowNodePayload::Ast(binding.declaration))
            || assignment.antecedent.is_none()
            || !assignment.antecedents.is_empty()
            || bound.flow_container(first) != Some(container)
        {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: first,
                expected: container,
                actual: bound.flow_container(first),
            }
            .into());
        }
        Some(flow)
    } else {
        None
    };

    Ok(SourceForInStatementSyntax {
        control,
        declaration,
        name,
        symbol,
        binding,
        bindings,
        body_statements,
        locals,
        statements,
        trailing_statements: Vec::new(),
        binding_flow,
    })
}

/// Proves the narrow iteration/captured-callable shape used by unused analysis.
#[allow(clippy::too_many_lines)] // Binding, nested callable, and flow form one atomic proof.
pub(super) fn plan_source_unused_iteration_statement_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<SourceUnusedIterationStatementSyntax, SourceFunctionStatementsError> {
    let source = bound.source_file();
    let control = plan_source_control_loop_syntax(arena, bound, statement, source)?;
    if !matches!(
        control.kind,
        SourceControlLoopKind::ForIn | SourceControlLoopKind::ForOf
    ) {
        return Err(unsupported_control_statement(
            statement,
            control_statement_node(arena, bound, statement)?.kind,
        ));
    }
    let list =
        control
            .initializer
            .ok_or(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                statement,
            ))?;
    let list_record = control_statement_node(arena, bound, list)?;
    let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
        return Err(unsupported_control_statement(list, list_record.kind));
    };
    let binding = match list_record.flags.0 {
        NODE_FLAG_LET => VariableBindingKind::Let,
        NODE_FLAG_CONST => VariableBindingKind::Const,
        _ => return Err(unsupported_control_statement(list, list_record.kind)),
    };
    let [binding_declaration] = declarations.declarations.nodes.as_slice() else {
        return Err(unsupported_control_statement(list, list_record.kind));
    };
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || list_record.parent != Some(statement.node)
        || declarations.declarations.has_trailing_comma
        || declarations.declarations.range.start <= list_record.range.start
        || declarations.declarations.range.end != list_record.range.end
        || declarations.facts != 0
        || bound.container(list) != Some(source)
        || bound.block_scope_container(list) != Some(statement)
    {
        return Err(unsupported_control_statement(list, list_record.kind));
    }
    let binding_declaration = NodeRef::new(list.arena, list.file, *binding_declaration);
    let declaration_record = control_statement_node(arena, bound, binding_declaration)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(unsupported_control_statement(
            binding_declaration,
            declaration_record.kind,
        ));
    };
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || declaration_record.parent != Some(list.node)
        || declaration_record.range != declarations.declarations.range
        || variable.exclamation_token.is_some()
        || variable.initializer.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.type_.is_some()
        || variable.facts != 0
        || bound.container(binding_declaration) != Some(source)
        || bound.block_scope_container(binding_declaration) != Some(statement)
    {
        return Err(unsupported_control_statement(
            binding_declaration,
            declaration_record.kind,
        ));
    }
    let binding_target = NodeRef::new(
        binding_declaration.arena,
        binding_declaration.file,
        variable.name,
    );
    let target_record = control_statement_node(arena, bound, binding_target)?;
    let (binding_element, binding_name, symbol_declaration) = match &target_record.data {
        NodeData::Identifier(_)
            if target_record.kind == SyntaxKind::Identifier
                && target_record.parent == Some(binding_declaration.node) =>
        {
            (None, binding_target, binding_declaration)
        }
        NodeData::BindingPattern(pattern)
            if control.kind == SourceControlLoopKind::ForOf
                && target_record.kind == SyntaxKind::ObjectBindingPattern
                && target_record.flags.0 == 0
                && target_record.parent == Some(binding_declaration.node)
                && pattern.elements.range == target_record.range
                && !pattern.elements.has_trailing_comma
                && pattern.facts == 0 =>
        {
            let [element] = pattern.elements.nodes.as_slice() else {
                return Err(unsupported_control_statement(
                    binding_target,
                    target_record.kind,
                ));
            };
            let element = NodeRef::new(binding_target.arena, binding_target.file, *element);
            let element_record = control_statement_node(arena, bound, element)?;
            let NodeData::BindingElement(binding_element) = &element_record.data else {
                return Err(unsupported_control_statement(element, element_record.kind));
            };
            let name = binding_element
                .name
                .map(|node| NodeRef::new(element.arena, element.file, node))
                .ok_or_else(|| unsupported_control_statement(element, element_record.kind))?;
            if element_record.kind != SyntaxKind::BindingElement
                || element_record.flags.0 != 0
                || element_record.parent != Some(binding_target.node)
                || binding_element.dot_dot_dot_token.is_some()
                || binding_element.flow_node.is_some()
                || binding_element.initializer.is_some()
                || binding_element.local_symbol.is_some()
                || binding_element.property_name.is_some()
                || binding_element.symbol.is_some()
                || binding_element.facts != 0
                || bound.container(element) != Some(source)
                || bound.block_scope_container(element) != Some(statement)
            {
                return Err(unsupported_control_statement(element, element_record.kind));
            }
            (Some(element), name, element)
        }
        _ => {
            return Err(unsupported_control_statement(
                binding_target,
                target_record.kind,
            ));
        }
    };
    let binding_name_record = control_statement_node(arena, bound, binding_name)?;
    let NodeData::Identifier(binding_identifier) = &binding_name_record.data else {
        return Err(unsupported_control_statement(
            binding_name,
            binding_name_record.kind,
        ));
    };
    if binding_name_record.kind != SyntaxKind::Identifier
        || binding_name_record.flags.0 != 0
        || binding_name_record.parent != Some(symbol_declaration.node)
        || binding_identifier.flow_node.is_some()
        || binding_identifier.text.is_empty()
        || bound.container(binding_name) != Some(source)
        || bound.block_scope_container(binding_name) != Some(statement)
    {
        return Err(unsupported_control_statement(
            binding_name,
            binding_name_record.kind,
        ));
    }
    let binding_symbol = plan_top_level_variable(
        bound,
        store,
        symbol_declaration,
        binding_name,
        &binding_identifier.text,
        binding,
        false,
    )?;
    let loop_locals = bound
        .locals(statement)
        .ok_or(SourceFunctionStatementsInvariant::MissingLocals(statement))?;
    let actual = store
        .symbol_table(loop_locals)
        .and_then(|locals| locals.get_source(&binding_identifier.text));
    if actual != Some(binding_symbol) {
        return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
            declaration: symbol_declaration,
            scope: statement,
            expected: binding_symbol,
            actual,
        }
        .into());
    }

    let body_record = control_statement_node(arena, bound, control.body)?;
    let NodeData::Block(body) = &body_record.data else {
        return Err(unsupported_control_statement(
            control.body,
            body_record.kind,
        ));
    };
    let [local_statement] = body.statements.nodes.as_slice() else {
        return Err(unsupported_control_statement(
            control.body,
            body_record.kind,
        ));
    };
    if body_record.kind != SyntaxKind::Block
        || body_record.flags.0 != 0
        || body_record.parent != Some(statement.node)
        || body.flow_node.is_some()
        || body.next_container.is_some()
        || body.statements.has_trailing_comma
        || body.facts != 0
        || bound.container(control.body) != Some(source)
        || bound.block_scope_container(control.body) != Some(statement)
    {
        return Err(unsupported_control_statement(
            control.body,
            body_record.kind,
        ));
    }
    let local_statement = NodeRef::new(control.body.arena, control.body.file, *local_statement);
    let local_record = control_statement_node(arena, bound, local_statement)?;
    if local_record.flags.0 != 0
        || local_record.parent != Some(control.body.node)
        || bound.container(local_statement) != Some(source)
        || bound.block_scope_container(local_statement) != Some(control.body)
    {
        return Err(unsupported_control_statement(
            local_statement,
            local_record.kind,
        ));
    }

    let (local_kind, local_declaration, local_name, callable) = match &local_record.data {
        NodeData::FunctionDeclaration(function)
            if local_record.kind == SyntaxKind::FunctionDeclaration =>
        {
            let name = function
                .name
                .map(|node| NodeRef::new(local_statement.arena, local_statement.file, node))
                .ok_or_else(|| unsupported_control_statement(local_statement, local_record.kind))?;
            if function.asterisk_token.is_some()
                || function.body.is_none()
                || function.end_flow_node.is_some()
                || function.flow_node.is_some()
                || function.full_signature.is_some()
                || function.local_symbol.is_some()
                || function.next_container.is_some()
                || !function.parameters.nodes.is_empty()
                || function.parameters.has_trailing_comma
                || function.return_flow_node.is_some()
                || function.symbol.is_some()
                || function.type_.is_some()
                || function.type_parameters.is_some()
                || function.facts != 0
                || function.modifiers.is_some()
            {
                return Err(unsupported_control_statement(
                    local_statement,
                    local_record.kind,
                ));
            }
            (
                SourceUnusedIterationDeclarationKind::Function,
                local_statement,
                name,
                local_statement,
            )
        }
        NodeData::VariableStatement(variable_statement)
            if local_record.kind == SyntaxKind::VariableStatement =>
        {
            if variable_statement.flow_node.is_some()
                || variable_statement.modifiers.is_some()
                || variable_statement.facts != 0
            {
                return Err(unsupported_control_statement(
                    local_statement,
                    local_record.kind,
                ));
            }
            let local_list = NodeRef::new(
                local_statement.arena,
                local_statement.file,
                variable_statement.declaration_list,
            );
            let local_list_record = control_statement_node(arena, bound, local_list)?;
            let NodeData::VariableDeclarationList(locals) = &local_list_record.data else {
                return Err(unsupported_control_statement(
                    local_list,
                    local_list_record.kind,
                ));
            };
            let [local_declaration] = locals.declarations.nodes.as_slice() else {
                return Err(unsupported_control_statement(
                    local_list,
                    local_list_record.kind,
                ));
            };
            if local_list_record.kind != SyntaxKind::VariableDeclarationList
                || local_list_record.flags.0 != NODE_FLAG_LET
                || local_list_record.parent != Some(local_statement.node)
                || locals.declarations.range != local_list_record.range
                || locals.declarations.has_trailing_comma
                || locals.facts != 0
                || bound.container(local_list) != Some(source)
                || bound.block_scope_container(local_list) != Some(control.body)
            {
                return Err(unsupported_control_statement(
                    local_list,
                    local_list_record.kind,
                ));
            }
            let local_declaration =
                NodeRef::new(local_list.arena, local_list.file, *local_declaration);
            let declaration_record = control_statement_node(arena, bound, local_declaration)?;
            let NodeData::VariableDeclaration(local_variable) = &declaration_record.data else {
                return Err(unsupported_control_statement(
                    local_declaration,
                    declaration_record.kind,
                ));
            };
            let callable = local_variable
                .initializer
                .map(|node| NodeRef::new(local_declaration.arena, local_declaration.file, node))
                .ok_or_else(|| {
                    unsupported_control_statement(local_declaration, declaration_record.kind)
                })?;
            if declaration_record.kind != SyntaxKind::VariableDeclaration
                || declaration_record.flags.0 != 0
                || declaration_record.parent != Some(local_list.node)
                || local_variable.exclamation_token.is_some()
                || local_variable.local_symbol.is_some()
                || local_variable.symbol.is_some()
                || local_variable.type_.is_some()
                || local_variable.facts != 0
                || bound.container(local_declaration) != Some(source)
                || bound.block_scope_container(local_declaration) != Some(control.body)
            {
                return Err(unsupported_control_statement(
                    local_declaration,
                    declaration_record.kind,
                ));
            }
            let name = NodeRef::new(
                local_declaration.arena,
                local_declaration.file,
                local_variable.name,
            );
            (
                SourceUnusedIterationDeclarationKind::ArrowVariable,
                local_declaration,
                name,
                callable,
            )
        }
        _ => {
            return Err(unsupported_control_statement(
                local_statement,
                local_record.kind,
            ));
        }
    };

    let local_name_record = control_statement_node(arena, bound, local_name)?;
    let NodeData::Identifier(local_identifier) = &local_name_record.data else {
        return Err(unsupported_control_statement(
            local_name,
            local_name_record.kind,
        ));
    };
    if local_name_record.kind != SyntaxKind::Identifier
        || local_name_record.flags.0 != 0
        || local_name_record.parent != Some(local_declaration.node)
        || local_identifier.flow_node.is_some()
        || local_identifier.text.is_empty()
    {
        return Err(unsupported_control_statement(
            local_name,
            local_name_record.kind,
        ));
    }
    let local_symbol = bound
        .symbol(local_declaration)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(SourceFunctionStatementsInvariant::MissingLocals(
            control.body,
        ))?;
    let expected_flags = match local_kind {
        SourceUnusedIterationDeclarationKind::Function => SymbolFlags::FUNCTION,
        SourceUnusedIterationDeclarationKind::ArrowVariable => SymbolFlags::BLOCK_SCOPED_VARIABLE,
    };
    let local_owner =
        store
            .symbol(local_symbol)
            .ok_or(SourceFunctionStatementsInvariant::MissingLocals(
                control.body,
            ))?;
    let locals =
        bound
            .locals(control.body)
            .ok_or(SourceFunctionStatementsInvariant::MissingLocals(
                control.body,
            ))?;
    let actual = store
        .symbol_table(locals)
        .and_then(|locals| locals.get_source(&local_identifier.text));
    if local_owner.flags() != expected_flags
        || local_owner.check_flags() != CheckFlags::NONE
        || local_owner.name().as_utf8() != Some(local_identifier.text.as_str())
        || local_owner.declarations() != Some(&[local_declaration])
        || local_owner.value_declaration() != Some(local_declaration)
        || local_owner.parent().is_some()
        || local_owner.export_symbol().is_some()
        || actual != Some(local_symbol)
    {
        return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
            declaration: local_declaration,
            scope: control.body,
            expected: local_symbol,
            actual,
        }
        .into());
    }

    let callable_record = control_statement_node(arena, bound, callable)?;
    let callable_body = match &callable_record.data {
        NodeData::FunctionDeclaration(function)
            if local_kind == SourceUnusedIterationDeclarationKind::Function =>
        {
            function.body
        }
        NodeData::ArrowFunction(arrow)
            if local_kind == SourceUnusedIterationDeclarationKind::ArrowVariable
                && callable_record.kind == SyntaxKind::ArrowFunction
                && callable_record.flags.0 == 0
                && callable_record.parent == Some(local_declaration.node)
                && arrow.asterisk_token.is_none()
                && arrow.end_flow_node.is_none()
                && arrow.flow_node.is_none()
                && arrow.full_signature.is_none()
                && arrow.next_container.is_none()
                && arrow.parameters.nodes.is_empty()
                && !arrow.parameters.has_trailing_comma
                && arrow.symbol.is_none()
                && arrow.type_.is_none()
                && arrow.type_parameters.is_none()
                && arrow.facts == 0
                && arrow.modifiers.is_none() =>
        {
            Some(arrow.body)
        }
        _ => {
            return Err(unsupported_control_statement(
                callable,
                callable_record.kind,
            ));
        }
    }
    .map(|node| NodeRef::new(callable.arena, callable.file, node))
    .ok_or_else(|| unsupported_control_statement(callable, callable_record.kind))?;
    let callable_symbol = bound
        .symbol(callable)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(SourceFunctionStatementsInvariant::MissingLocals(callable))?;
    if local_kind == SourceUnusedIterationDeclarationKind::Function
        && callable_symbol != local_symbol
        || local_kind == SourceUnusedIterationDeclarationKind::ArrowVariable
            && callable_symbol == local_symbol
    {
        return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(callable).into());
    }

    let callable_body_record = control_statement_node(arena, bound, callable_body)?;
    let NodeData::Block(callable_block) = &callable_body_record.data else {
        return Err(unsupported_control_statement(
            callable_body,
            callable_body_record.kind,
        ));
    };
    let [capture_statement] = callable_block.statements.nodes.as_slice() else {
        return Err(unsupported_control_statement(
            callable_body,
            callable_body_record.kind,
        ));
    };
    if callable_body_record.kind != SyntaxKind::Block
        || callable_body_record.flags.0 != 0
        || callable_body_record.parent != Some(callable.node)
        || callable_block.flow_node.is_some()
        || callable_block.next_container.is_some()
        || callable_block.statements.has_trailing_comma
        || callable_block.facts != 0
        || bound.container(callable_body) != Some(callable)
        || bound.block_scope_container(callable_body) != Some(callable)
    {
        return Err(unsupported_control_statement(
            callable_body,
            callable_body_record.kind,
        ));
    }
    let capture_statement =
        NodeRef::new(callable_body.arena, callable_body.file, *capture_statement);
    let capture_statement_record = control_statement_node(arena, bound, capture_statement)?;
    let NodeData::ExpressionStatement(expression) = &capture_statement_record.data else {
        return Err(unsupported_control_statement(
            capture_statement,
            capture_statement_record.kind,
        ));
    };
    let capture = NodeRef::new(
        capture_statement.arena,
        capture_statement.file,
        expression.expression,
    );
    let capture_record = control_statement_node(arena, bound, capture)?;
    let NodeData::Identifier(captured) = &capture_record.data else {
        return Err(unsupported_control_statement(capture, capture_record.kind));
    };
    let start = bound.flow_graph().container_start(callable).ok_or(
        SourceFunctionStatementsInvariant::MissingFlowStart(callable),
    )?;
    if capture_statement_record.kind != SyntaxKind::ExpressionStatement
        || capture_statement_record.flags.0 != 0
        || capture_statement_record.parent != Some(callable_body.node)
        || expression.flow_node.is_some()
        || capture_record.kind != SyntaxKind::Identifier
        || capture_record.flags.0 != 0
        || capture_record.parent != Some(capture_statement.node)
        || captured.flow_node.is_some()
        || captured.text != binding_identifier.text
        || bound.container(capture_statement) != Some(callable)
        || bound.container(capture) != Some(callable)
        || bound.block_scope_container(capture_statement) != Some(callable)
        || bound.block_scope_container(capture) != Some(callable)
        || bound.flow_graph().container_is_complete(callable) != Some(true)
        || bound.flow_container(capture_statement) != Some(callable)
        || bound.flow_container(capture) != Some(callable)
        || bound.flow_at(capture_statement) != Some(start)
        || bound.flow_at(capture) != Some(start)
        || bound
            .flow_graph()
            .nodes()
            .iter()
            .filter(|node| {
                joined_semantic_flow_flags(node.flags) == FlowFlags::ASSIGNMENT.bits()
                    && node.payload == Some(FlowNodePayload::Ast(symbol_declaration))
            })
            .count()
            != 1
    {
        return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
            node: capture_statement,
            expected: callable,
            actual: bound.flow_container(capture_statement),
        }
        .into());
    }

    Ok(SourceUnusedIterationStatementSyntax {
        control,
        binding,
        binding_declaration,
        binding_element,
        binding_name,
        binding_symbol,
        local_kind,
        local_statement,
        local_declaration,
        local_name,
        local_symbol,
        callable,
        callable_symbol,
        capture_statement,
        capture,
    })
}

/// Authenticates a top-level lexical loop, its captures, labels, and conditional jumps.
#[allow(clippy::too_many_lines)] // The loop, captured callable, and binder scopes form one proof.
pub(super) fn plan_source_captured_iteration_statement_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<SourceCapturedIterationSyntax, SourceFunctionStatementsError> {
    let source = bound.source_file();
    let mut labels = Vec::new();
    let mut iteration = statement;
    let mut parent = source;
    while control_statement_node(arena, bound, iteration)?.kind == SyntaxKind::LabeledStatement {
        let record = control_statement_node(arena, bound, iteration)?;
        let NodeData::LabeledStatement(labeled) = &record.data else {
            return Err(unsupported_control_statement(iteration, record.kind));
        };
        let label = NodeRef::new(iteration.arena, iteration.file, labeled.label);
        let next = validate_labeled_statement(arena, bound, iteration, parent)?;
        labels.push(label);
        parent = iteration;
        iteration = next;
    }
    let statement = iteration;
    let control = plan_source_control_loop_syntax(arena, bound, statement, parent)?;
    if !matches!(
        control.kind,
        SourceControlLoopKind::For | SourceControlLoopKind::ForIn | SourceControlLoopKind::ForOf
    ) {
        return Err(unsupported_control_statement(
            statement,
            control_statement_node(arena, bound, statement)?.kind,
        ));
    }

    let list =
        control
            .initializer
            .ok_or(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                statement,
            ))?;
    let list_record = control_statement_node(arena, bound, list)?;
    let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
        return Err(unsupported_control_statement(list, list_record.kind));
    };
    let binding = match list_record.flags.0 {
        NODE_FLAG_LET => VariableBindingKind::Let,
        NODE_FLAG_CONST => VariableBindingKind::Const,
        _ => return Err(unsupported_control_statement(list, list_record.kind)),
    };
    let Some((&declaration, additional_declarations)) =
        declarations.declarations.nodes.split_first()
    else {
        return Err(unsupported_control_statement(list, list_record.kind));
    };
    if !additional_declarations.is_empty() && control.kind != SourceControlLoopKind::For {
        return Err(unsupported_control_statement(list, list_record.kind));
    }
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || list_record.parent != Some(statement.node)
        || declarations.declarations.has_trailing_comma
        || declarations.declarations.range.start <= list_record.range.start
        || declarations.declarations.range.end != list_record.range.end
        || declarations.facts != 0
        || bound.container(list) != Some(source)
        || bound.block_scope_container(list) != Some(statement)
    {
        return Err(unsupported_control_statement(list, list_record.kind));
    }

    let declaration = NodeRef::new(list.arena, list.file, declaration);
    let declaration_record = control_statement_node(arena, bound, declaration)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(unsupported_control_statement(
            declaration,
            declaration_record.kind,
        ));
    };
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || declaration_record.parent != Some(list.node)
        || variable.exclamation_token.is_some()
        || variable.initializer.is_some() != (control.kind == SourceControlLoopKind::For)
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.type_.is_some()
        || variable.facts != 0
        || bound.container(declaration) != Some(source)
        || bound.block_scope_container(declaration) != Some(statement)
    {
        return Err(unsupported_control_statement(
            declaration,
            declaration_record.kind,
        ));
    }
    let initializer = variable
        .initializer
        .map(|initializer| NodeRef::new(declaration.arena, declaration.file, initializer));
    if let Some(initializer) = initializer {
        let record = control_statement_node(arena, bound, initializer)?;
        if record.parent != Some(declaration.node)
            || record.flags.0 != 0
            || bound.container(initializer) != Some(source)
            || bound.block_scope_container(initializer) != Some(statement)
        {
            return Err(unsupported_control_statement(initializer, record.kind));
        }
    }

    let name_or_pattern = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let pattern_record = control_statement_node(arena, bound, name_or_pattern)?;
    let (binding_declaration, name, destructured) = match &pattern_record.data {
        NodeData::Identifier(_) if pattern_record.kind == SyntaxKind::Identifier => {
            (declaration, name_or_pattern, false)
        }
        NodeData::BindingPattern(pattern)
            if control.kind == SourceControlLoopKind::ForOf
                && pattern_record.kind == SyntaxKind::ObjectBindingPattern =>
        {
            let [element] = pattern.elements.nodes.as_slice() else {
                return Err(unsupported_control_statement(
                    name_or_pattern,
                    pattern_record.kind,
                ));
            };
            if pattern_record.flags.0 != 0
                || pattern_record.parent != Some(declaration.node)
                || pattern.elements.has_trailing_comma
                || pattern.facts != 0
                || bound.container(name_or_pattern) != Some(source)
                || bound.block_scope_container(name_or_pattern) != Some(statement)
                || bound.symbol(declaration).is_some()
            {
                return Err(unsupported_control_statement(
                    name_or_pattern,
                    pattern_record.kind,
                ));
            }
            let element = NodeRef::new(name_or_pattern.arena, name_or_pattern.file, *element);
            let element_record = control_statement_node(arena, bound, element)?;
            let NodeData::BindingElement(binding_element) = &element_record.data else {
                return Err(unsupported_control_statement(element, element_record.kind));
            };
            let name = binding_element
                .name
                .map(|name| NodeRef::new(element.arena, element.file, name))
                .ok_or(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                    element,
                ))?;
            if element_record.kind != SyntaxKind::BindingElement
                || element_record.flags.0 != 0
                || element_record.parent != Some(name_or_pattern.node)
                || binding_element.dot_dot_dot_token.is_some()
                || binding_element.flow_node.is_some()
                || binding_element.initializer.is_some()
                || binding_element.local_symbol.is_some()
                || binding_element.property_name.is_some()
                || binding_element.symbol.is_some()
                || binding_element.facts != 0
                || bound.container(element) != Some(source)
                || bound.block_scope_container(element) != Some(statement)
            {
                return Err(unsupported_control_statement(element, element_record.kind));
            }
            (element, name, true)
        }
        _ => {
            return Err(unsupported_control_statement(
                name_or_pattern,
                pattern_record.kind,
            ));
        }
    };
    let name_record = control_statement_node(arena, bound, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported_control_statement(name, name_record.kind));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(binding_declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || bound.container(name) != Some(source)
        || bound.block_scope_container(name) != Some(statement)
    {
        return Err(unsupported_control_statement(name, name_record.kind));
    }
    let symbol = plan_top_level_variable(
        bound,
        store,
        binding_declaration,
        name,
        &identifier.text,
        binding,
        false,
    )?;
    let locals = bound
        .locals(statement)
        .ok_or(SourceFunctionStatementsInvariant::MissingLocals(statement))?;
    let actual = store
        .symbol_table(locals)
        .and_then(|locals| locals.get_source(&identifier.text));
    if actual != Some(symbol) {
        return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
            declaration: binding_declaration,
            scope: statement,
            expected: symbol,
            actual,
        }
        .into());
    }
    let mut additional_bindings = Vec::with_capacity(additional_declarations.len());
    for declaration in additional_declarations {
        additional_bindings.push(plan_captured_iteration_additional_binding(
            arena,
            bound,
            store,
            statement,
            list,
            NodeRef::new(list.arena, list.file, *declaration),
            binding,
        )?);
    }

    let body_record = control_statement_node(arena, bound, control.body)?;
    let NodeData::Block(body) = &body_record.data else {
        return Err(unsupported_control_statement(
            control.body,
            body_record.kind,
        ));
    };
    if body_record.kind != SyntaxKind::Block
        || body_record.flags.0 != 0
        || body_record.parent != Some(statement.node)
        || body.flow_node.is_some()
        || body.next_container.is_some()
        || body.statements.has_trailing_comma
        || body.facts != 0
        || bound.container(control.body) != Some(source)
        || bound.block_scope_container(control.body) != Some(statement)
    {
        return Err(unsupported_control_statement(
            control.body,
            body_record.kind,
        ));
    }
    if body.statements.nodes.is_empty() {
        return Err(unsupported_control_statement(
            control.body,
            body_record.kind,
        ));
    }
    let body_statement = body.statements.nodes[0];
    let body_statement = NodeRef::new(control.body.arena, control.body.file, body_statement);
    let statement_record = control_statement_node(arena, bound, body_statement)?;
    if statement_record.parent != Some(control.body.node)
        || statement_record.flags.0 != 0
        || bound.container(body_statement) != Some(source)
        || bound.block_scope_container(body_statement) != Some(control.body)
    {
        return Err(unsupported_control_statement(
            body_statement,
            statement_record.kind,
        ));
    }

    let body = match &statement_record.data {
        NodeData::FunctionDeclaration(function)
            if statement_record.kind == SyntaxKind::FunctionDeclaration
                && body.statements.nodes.len() == 1 =>
        {
            let local_name = function
                .name
                .map(|name| NodeRef::new(body_statement.arena, body_statement.file, name))
                .ok_or(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                    body_statement,
                ))?;
            let local_symbol = bound.symbol(body_statement).ok_or(
                SourceFunctionStatementsInvariant::MissingLocals(body_statement),
            )?;
            validate_captured_iteration_local_name(
                arena,
                bound,
                store,
                control.body,
                body_statement,
                local_name,
                local_symbol,
            )?;
            if function.modifiers.is_some()
                || function.asterisk_token.is_some()
                || function.type_parameters.is_some()
                || !function.parameters.nodes.is_empty()
                || function.parameters.has_trailing_comma
                || function.type_.is_some()
                || function.facts != 0
            {
                return Err(unsupported_control_statement(
                    body_statement,
                    statement_record.kind,
                ));
            }
            let function_body = function
                .body
                .map(|body| NodeRef::new(body_statement.arena, body_statement.file, body))
                .ok_or(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                    body_statement,
                ))?;
            let read = captured_iteration_callable_read(
                arena,
                bound,
                body_statement,
                function_body,
                &identifier.text,
            )?;
            SourceCapturedIterationBodySyntax::Function {
                declaration: body_statement,
                name: local_name,
                symbol: local_symbol,
                read,
            }
        }
        NodeData::VariableStatement(variable_statement)
            if statement_record.kind == SyntaxKind::VariableStatement
                && body.statements.nodes.len() == 1 =>
        {
            if variable_statement.modifiers.is_some()
                || variable_statement.flow_node.is_some()
                || variable_statement.facts != 0
            {
                return Err(unsupported_control_statement(
                    body_statement,
                    statement_record.kind,
                ));
            }
            let local_list = NodeRef::new(
                body_statement.arena,
                body_statement.file,
                variable_statement.declaration_list,
            );
            let local_list_record = control_statement_node(arena, bound, local_list)?;
            let NodeData::VariableDeclarationList(local_declarations) = &local_list_record.data
            else {
                return Err(unsupported_control_statement(
                    local_list,
                    local_list_record.kind,
                ));
            };
            let local_binding = match local_list_record.flags.0 {
                NODE_FLAG_LET => VariableBindingKind::Let,
                NODE_FLAG_CONST => VariableBindingKind::Const,
                _ => {
                    return Err(unsupported_control_statement(
                        local_list,
                        local_list_record.kind,
                    ));
                }
            };
            let [local_declaration] = local_declarations.declarations.nodes.as_slice() else {
                return Err(unsupported_control_statement(
                    local_list,
                    local_list_record.kind,
                ));
            };
            if local_list_record.kind != SyntaxKind::VariableDeclarationList
                || local_list_record.parent != Some(body_statement.node)
                || local_declarations.declarations.has_trailing_comma
                || local_declarations.facts != 0
                || bound.container(local_list) != Some(source)
                || bound.block_scope_container(local_list) != Some(control.body)
            {
                return Err(unsupported_control_statement(
                    local_list,
                    local_list_record.kind,
                ));
            }
            let local_declaration =
                NodeRef::new(local_list.arena, local_list.file, *local_declaration);
            let local_record = control_statement_node(arena, bound, local_declaration)?;
            let NodeData::VariableDeclaration(local) = &local_record.data else {
                return Err(unsupported_control_statement(
                    local_declaration,
                    local_record.kind,
                ));
            };
            let local_name =
                NodeRef::new(local_declaration.arena, local_declaration.file, local.name);
            let arrow = local
                .initializer
                .map(|arrow| NodeRef::new(local_declaration.arena, local_declaration.file, arrow))
                .ok_or(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                    local_declaration,
                ))?;
            if local_record.kind != SyntaxKind::VariableDeclaration
                || local_record.flags.0 != 0
                || local_record.parent != Some(local_list.node)
                || local.exclamation_token.is_some()
                || local.local_symbol.is_some()
                || local.symbol.is_some()
                || local.type_.is_some()
                || local.facts != 0
                || bound.container(local_declaration) != Some(source)
                || bound.block_scope_container(local_declaration) != Some(control.body)
            {
                return Err(unsupported_control_statement(
                    local_declaration,
                    local_record.kind,
                ));
            }
            let local_name_record = control_statement_node(arena, bound, local_name)?;
            let NodeData::Identifier(local_identifier) = &local_name_record.data else {
                return Err(unsupported_control_statement(
                    local_name,
                    local_name_record.kind,
                ));
            };
            let local_symbol = plan_top_level_variable(
                bound,
                store,
                local_declaration,
                local_name,
                &local_identifier.text,
                local_binding,
                false,
            )?;
            validate_captured_iteration_local_name(
                arena,
                bound,
                store,
                control.body,
                local_declaration,
                local_name,
                local_symbol,
            )?;

            let arrow_record = control_statement_node(arena, bound, arrow)?;
            let NodeData::ArrowFunction(arrow_data) = &arrow_record.data else {
                return Err(unsupported_control_statement(arrow, arrow_record.kind));
            };
            if arrow_record.kind != SyntaxKind::ArrowFunction
                || arrow_record.flags.0 != 0
                || arrow_record.parent != Some(local_declaration.node)
                || arrow_data.asterisk_token.is_some()
                || arrow_data.modifiers.is_some()
                || arrow_data.type_parameters.is_some()
                || arrow_data.type_.is_some()
                || !arrow_data.parameters.nodes.is_empty()
                || arrow_data.parameters.has_trailing_comma
                || arrow_data.facts != 0
                || bound.container(arrow) != Some(source)
                || bound.block_scope_container(arrow) != Some(control.body)
            {
                return Err(unsupported_control_statement(arrow, arrow_record.kind));
            }
            let arrow_body = NodeRef::new(arrow.arena, arrow.file, arrow_data.body);
            let read = captured_iteration_callable_read(
                arena,
                bound,
                arrow,
                arrow_body,
                &identifier.text,
            )?;
            SourceCapturedIterationBodySyntax::ArrowVariable {
                declaration: local_declaration,
                name: local_name,
                symbol: local_symbol,
                binding: local_binding,
                arrow,
                read,
            }
        }
        NodeData::ExpressionStatement(_) | NodeData::VariableStatement(_) => {
            let statements = plan_captured_iteration_control_flow(
                arena,
                bound,
                store,
                &control,
                &body.statements.nodes,
                &labels,
            )?;
            SourceCapturedIterationBodySyntax::ControlFlow(statements)
        }
        _ => {
            return Err(unsupported_control_statement(
                body_statement,
                statement_record.kind,
            ));
        }
    };

    Ok(SourceCapturedIterationSyntax {
        labels,
        control,
        binding: SourceCapturedIterationBindingSyntax {
            declaration: binding_declaration,
            name,
            symbol,
            binding,
            initializer,
            destructured,
        },
        additional_bindings,
        body,
    })
}

#[allow(clippy::too_many_arguments)] // Each initializer must remain tied to its loop-owned table.
fn plan_captured_iteration_additional_binding(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
    list: NodeRef,
    declaration: NodeRef,
    binding: VariableBindingKind,
) -> Result<SourceCapturedIterationBindingSyntax, SourceFunctionStatementsError> {
    let source = bound.source_file();
    let record = control_statement_node(arena, bound, declaration)?;
    let NodeData::VariableDeclaration(variable) = &record.data else {
        return Err(unsupported_control_statement(declaration, record.kind));
    };
    let Some(initializer) = variable
        .initializer
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
    else {
        return Err(unsupported_control_statement(declaration, record.kind));
    };
    if record.kind != SyntaxKind::VariableDeclaration
        || record.flags.0 != 0
        || record.parent != Some(list.node)
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.type_.is_some()
        || variable.facts != 0
        || bound.container(declaration) != Some(source)
        || bound.block_scope_container(declaration) != Some(statement)
    {
        return Err(unsupported_control_statement(declaration, record.kind));
    }

    let initializer_record = control_statement_node(arena, bound, initializer)?;
    if initializer_record.flags.0 != 0
        || initializer_record.parent != Some(declaration.node)
        || bound.container(initializer) != Some(source)
        || bound.block_scope_container(initializer) != Some(statement)
    {
        return Err(unsupported_control_statement(
            initializer,
            initializer_record.kind,
        ));
    }

    let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let name_record = control_statement_node(arena, bound, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported_control_statement(name, name_record.kind));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || bound.container(name) != Some(source)
        || bound.block_scope_container(name) != Some(statement)
    {
        return Err(unsupported_control_statement(name, name_record.kind));
    }
    let symbol = plan_top_level_variable(
        bound,
        store,
        declaration,
        name,
        &identifier.text,
        binding,
        false,
    )?;
    let actual = bound
        .locals(statement)
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get_source(&identifier.text));
    if actual != Some(symbol) {
        return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
            declaration,
            scope: statement,
            expected: symbol,
            actual,
        }
        .into());
    }

    Ok(SourceCapturedIterationBindingSyntax {
        declaration,
        name,
        symbol,
        binding,
        initializer: Some(initializer),
        destructured: false,
    })
}

/// Authenticates top-level block locals and closures without an iteration binding.
pub(super) fn plan_source_captured_block_loop_statement_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<SourceCapturedBlockLoopSyntax, SourceFunctionStatementsError> {
    let source = bound.source_file();
    let control = plan_source_control_loop_syntax(arena, bound, statement, source)?;
    if !matches!(
        control.kind,
        SourceControlLoopKind::While | SourceControlLoopKind::DoWhile
    ) || control.condition.is_none()
    {
        return Err(unsupported_control_statement(
            statement,
            control_statement_node(arena, bound, statement)?.kind,
        ));
    }

    let record = control_statement_node(arena, bound, control.body)?;
    let NodeData::Block(body) = &record.data else {
        return Err(unsupported_control_statement(control.body, record.kind));
    };
    if record.kind != SyntaxKind::Block
        || record.flags.0 != 0
        || record.parent != Some(statement.node)
        || body.flow_node.is_some()
        || body.next_container.is_some()
        || body.statements.has_trailing_comma
        || body.statements.nodes.is_empty()
        || body.facts != 0
        || bound.container(control.body) != Some(source)
        || bound.block_scope_container(control.body) != Some(source)
    {
        return Err(unsupported_control_statement(control.body, record.kind));
    }

    let statements = plan_captured_iteration_control_flow(
        arena,
        bound,
        store,
        &control,
        &body.statements.nodes,
        &[],
    )?;
    if !statements
        .iter()
        .any(|statement| matches!(statement, SourceCapturedIterationStatementSyntax::Local(_)))
    {
        return Err(unsupported_control_statement(control.body, record.kind));
    }
    for statement in &statements {
        if let SourceCapturedIterationStatementSyntax::Local(local) = statement
            && (bound.flow_container(local.name) != Some(source)
                || bound.flow_at(local.name).is_none())
        {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: local.name,
                expected: source,
                actual: bound.flow_container(local.name),
            }
            .into());
        }
    }

    Ok(SourceCapturedBlockLoopSyntax {
        control,
        statements,
    })
}

fn plan_captured_iteration_control_flow(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    control: &SourceControlLoopSyntax,
    nodes: &[NodeId],
    labels: &[NodeRef],
) -> Result<Vec<SourceCapturedIterationStatementSyntax>, SourceFunctionStatementsError> {
    let source = bound.source_file();
    let mut statements = Vec::with_capacity(nodes.len());
    let mut captures = 0usize;
    for node in nodes {
        let statement = NodeRef::new(control.body.arena, control.body.file, *node);
        let record = control_statement_node(arena, bound, statement)?;
        if record.flags.0 != 0
            || record.parent != Some(control.body.node)
            || bound.container(statement) != Some(source)
            || bound.block_scope_container(statement) != Some(control.body)
        {
            return Err(unsupported_control_statement(statement, record.kind));
        }
        match &record.data {
            NodeData::VariableStatement(_) if record.kind == SyntaxKind::VariableStatement => {
                statements.extend(
                    plan_captured_iteration_local_statement(
                        arena,
                        bound,
                        store,
                        control.body,
                        statement,
                    )?
                    .into_iter()
                    .map(SourceCapturedIterationStatementSyntax::Local),
                );
            }
            NodeData::ExpressionStatement(expression)
                if record.kind == SyntaxKind::ExpressionStatement
                    && expression.flow_node.is_none() =>
            {
                let expression =
                    NodeRef::new(statement.arena, statement.file, expression.expression);
                let expression_record = control_statement_node(arena, bound, expression)?;
                if expression_record.flags.0 != 0
                    || expression_record.parent != Some(statement.node)
                    || bound.container(expression) != Some(source)
                    || bound.block_scope_container(expression) != Some(control.body)
                {
                    return Err(unsupported_control_statement(
                        expression,
                        expression_record.kind,
                    ));
                }

                let mut closure = expression;
                loop {
                    let closure_record = control_statement_node(arena, bound, closure)?;
                    let NodeData::ParenthesizedExpression(parenthesized) = &closure_record.data
                    else {
                        break;
                    };
                    if closure_record.kind != SyntaxKind::ParenthesizedExpression
                        || closure_record.flags.0 != 0
                    {
                        return Err(unsupported_control_statement(closure, closure_record.kind));
                    }
                    let child = NodeRef::new(closure.arena, closure.file, parenthesized.expression);
                    let child_record = control_statement_node(arena, bound, child)?;
                    if child_record.parent != Some(closure.node)
                        || bound.container(child) != Some(source)
                        || bound.block_scope_container(child) != Some(control.body)
                    {
                        return Err(unsupported_control_statement(child, child_record.kind));
                    }
                    closure = child;
                }
                let kind = control_statement_node(arena, bound, closure)?.kind;
                if !matches!(
                    kind,
                    SyntaxKind::FunctionExpression | SyntaxKind::ArrowFunction
                ) {
                    return Err(unsupported_control_statement(closure, kind));
                }
                captures += 1;
                statements.push(SourceCapturedIterationStatementSyntax::Expression(
                    expression,
                ));
            }
            NodeData::IfStatement(_) if record.kind == SyntaxKind::IfStatement => {
                let (condition, jump) = plan_captured_iteration_conditional_jump(
                    arena,
                    bound,
                    statement,
                    control.body,
                    labels,
                )?;
                statements.push(SourceCapturedIterationStatementSyntax::ConditionalJump {
                    condition,
                    jump,
                });
            }
            _ => return Err(unsupported_control_statement(statement, record.kind)),
        }
    }
    if captures == 0 {
        return Err(unsupported_control_statement(
            control.body,
            SyntaxKind::Block,
        ));
    }
    Ok(statements)
}

fn plan_captured_iteration_local_statement(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    scope: NodeRef,
    statement: NodeRef,
) -> Result<Vec<SourceLocalDeclarationSyntax>, SourceFunctionStatementsError> {
    let source = bound.source_file();
    let record = control_statement_node(arena, bound, statement)?;
    let NodeData::VariableStatement(variable_statement) = &record.data else {
        return Err(unsupported_control_statement(statement, record.kind));
    };
    if record.kind != SyntaxKind::VariableStatement
        || record.flags.0 != 0
        || record.parent != Some(scope.node)
        || variable_statement.modifiers.is_some()
        || variable_statement.flow_node.is_some()
        || variable_statement.facts != 0
        || bound.container(statement) != Some(source)
        || bound.block_scope_container(statement) != Some(scope)
    {
        return Err(unsupported_control_statement(statement, record.kind));
    }

    let list = NodeRef::new(
        statement.arena,
        statement.file,
        variable_statement.declaration_list,
    );
    plan_source_loop_declaration_list(arena, bound, store, scope, statement, list, false)
}

#[allow(clippy::too_many_arguments)]
fn plan_source_loop_declaration_list(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    scope: NodeRef,
    statement: NodeRef,
    list: NodeRef,
    allow_var: bool,
) -> Result<Vec<SourceLocalDeclarationSyntax>, SourceFunctionStatementsError> {
    let source = bound.source_file();
    let in_header =
        control_statement_node(arena, bound, statement)?.kind == SyntaxKind::ForStatement;
    let list_record = control_statement_node(arena, bound, list)?;
    let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
        return Err(unsupported_control_statement(list, list_record.kind));
    };
    let binding = match list_record.flags.0 {
        0 if allow_var => VariableBindingKind::Var,
        NODE_FLAG_LET => VariableBindingKind::Let,
        NODE_FLAG_CONST => VariableBindingKind::Const,
        _ => return Err(unsupported_control_statement(list, list_record.kind)),
    };
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || list_record.parent != Some(statement.node)
        || if in_header {
            declarations.declarations.range.start <= list_record.range.start
                || declarations.declarations.range.end != list_record.range.end
        } else {
            declarations.declarations.range != list_record.range
        }
        || declarations.declarations.has_trailing_comma
        || declarations.declarations.nodes.is_empty()
        || declarations.facts != 0
        || bound.container(list) != Some(source)
        || bound.block_scope_container(list) != Some(scope)
    {
        return Err(unsupported_control_statement(list, list_record.kind));
    }

    let mut locals = Vec::with_capacity(declarations.declarations.nodes.len());
    let mut previous_end = declarations.declarations.range.start;
    for declaration in &declarations.declarations.nodes {
        let declaration = NodeRef::new(list.arena, list.file, *declaration);
        let declaration_record = control_statement_node(arena, bound, declaration)?;
        if in_header {
            validate_control_statement_child(arena, bound, list, declaration, source)?;
            if declaration_record.range.start < previous_end
                || declaration_record.range.end > declarations.declarations.range.end
            {
                return Err(unsupported_control_statement(
                    declaration,
                    declaration_record.kind,
                ));
            }
            previous_end = declaration_record.range.end;
        }
        let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
            return Err(unsupported_control_statement(
                declaration,
                declaration_record.kind,
            ));
        };
        if declaration_record.kind != SyntaxKind::VariableDeclaration
            || declaration_record.flags.0 != 0
            || declaration_record.parent != Some(list.node)
            || variable.exclamation_token.is_some()
            || variable.local_symbol.is_some()
            || variable.symbol.is_some()
            || variable.facts != 0
            || bound.container(declaration) != Some(source)
            || bound.block_scope_container(declaration) != Some(scope)
        {
            return Err(unsupported_control_statement(
                declaration,
                declaration_record.kind,
            ));
        }

        let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
        let name_record = control_statement_node(arena, bound, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(unsupported_control_statement(name, name_record.kind));
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(declaration.node)
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
            || bound.container(name) != Some(source)
            || bound.block_scope_container(name) != Some(scope)
        {
            return Err(unsupported_control_statement(name, name_record.kind));
        }

        let type_node = variable
            .type_
            .map(|node| NodeRef::new(declaration.arena, declaration.file, node));
        if let Some(type_node) = type_node {
            let record = control_statement_node(arena, bound, type_node)?;
            if record.parent != Some(declaration.node)
                || bound.container(type_node) != Some(source)
                || bound.block_scope_container(type_node) != Some(scope)
            {
                return Err(unsupported_control_statement(type_node, record.kind));
            }
        }
        let initializer = variable
            .initializer
            .map(|node| NodeRef::new(declaration.arena, declaration.file, node));
        match initializer {
            Some(initializer) => {
                let record = control_statement_node(arena, bound, initializer)?;
                if record.parent != Some(declaration.node)
                    || bound.container(initializer) != Some(source)
                    || bound.block_scope_container(initializer) != Some(scope)
                {
                    return Err(unsupported_control_statement(initializer, record.kind));
                }
            }
            None if binding.is_const() => {
                return Err(unsupported_control_statement(
                    declaration,
                    declaration_record.kind,
                ));
            }
            None => {}
        }

        let symbol = plan_top_level_variable(
            bound,
            store,
            declaration,
            name,
            &identifier.text,
            binding,
            false,
        )?;
        validate_captured_iteration_local_name(
            arena,
            bound,
            store,
            if binding == VariableBindingKind::Var {
                source
            } else {
                scope
            },
            declaration,
            name,
            symbol,
        )?;
        locals.push(SourceLocalDeclarationSyntax {
            statement,
            list,
            declaration,
            name,
            symbol,
            binding,
            type_node,
            initializer,
        });
    }

    Ok(locals)
}

fn plan_captured_iteration_conditional_jump(
    arena: &NodeArena,
    bound: &BoundFile,
    statement: NodeRef,
    parent: NodeRef,
    labels: &[NodeRef],
) -> Result<(NodeRef, NodeRef), SourceFunctionStatementsError> {
    let source = bound.source_file();
    let control = plan_source_control_if_syntax(arena, bound, statement, parent)?;
    if control.else_statement.is_some()
        || !control.nested_export_diagnostics.is_empty()
        || bound.block_scope_container(control.condition) != Some(parent)
    {
        return Err(unsupported_control_statement(
            statement,
            SyntaxKind::IfStatement,
        ));
    }

    let branch = control_statement_node(arena, bound, control.then_statement)?;
    let (jump, scope, expected_parent) = if let NodeData::Block(block) = &branch.data {
        let [jump] = block.statements.nodes.as_slice() else {
            return Err(unsupported_control_statement(
                control.then_statement,
                branch.kind,
            ));
        };
        if branch.kind != SyntaxKind::Block
            || branch.flags.0 != 0
            || branch.parent != Some(statement.node)
            || block.flow_node.is_some()
            || block.next_container.is_some()
            || block.statements.has_trailing_comma
            || block.facts != 0
            || bound.container(control.then_statement) != Some(source)
            || bound.block_scope_container(control.then_statement) != Some(parent)
        {
            return Err(unsupported_control_statement(
                control.then_statement,
                branch.kind,
            ));
        }
        (
            NodeRef::new(
                control.then_statement.arena,
                control.then_statement.file,
                *jump,
            ),
            control.then_statement,
            control.then_statement,
        )
    } else {
        (control.then_statement, parent, statement)
    };
    validate_source_iteration_jump(arena, bound, jump, expected_parent, scope, labels)?;
    Ok((control.condition, jump))
}

fn validate_source_iteration_jump(
    arena: &NodeArena,
    bound: &BoundFile,
    jump: NodeRef,
    expected_parent: NodeRef,
    scope: NodeRef,
    labels: &[NodeRef],
) -> Result<(), SourceFunctionStatementsError> {
    let source = bound.source_file();
    let record = control_statement_node(arena, bound, jump)?;
    let (label, flow_node) = match &record.data {
        NodeData::BreakStatement(jump) if record.kind == SyntaxKind::BreakStatement => {
            (jump.label, jump.flow_node)
        }
        NodeData::ContinueStatement(jump) if record.kind == SyntaxKind::ContinueStatement => {
            (jump.label, jump.flow_node)
        }
        _ => return Err(unsupported_control_statement(jump, record.kind)),
    };
    if record.flags.0 != 0
        || record.parent != Some(expected_parent.node)
        || flow_node.is_some()
        || bound.container(jump) != Some(source)
        || bound.block_scope_container(jump) != Some(scope)
        || bound.flow_container(jump) != Some(source)
        || bound.flow_at(jump).is_none()
    {
        return Err(unsupported_control_statement(jump, record.kind));
    }
    if let Some(label) = label {
        let label = NodeRef::new(jump.arena, jump.file, label);
        let label_record = control_statement_node(arena, bound, label)?;
        let NodeData::Identifier(identifier) = &label_record.data else {
            return Err(unsupported_control_statement(label, label_record.kind));
        };
        if label_record.kind != SyntaxKind::Identifier
            || label_record.flags.0 != 0
            || label_record.parent != Some(jump.node)
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
            || bound.container(label) != Some(source)
            || bound.block_scope_container(label) != Some(scope)
            || !labels.iter().any(|candidate| {
                matches!(
                    control_statement_node(arena, bound, *candidate).map(|node| &node.data),
                    Ok(NodeData::Identifier(name)) if name.text == identifier.text
                )
            })
        {
            return Err(unsupported_control_statement(label, label_record.kind));
        }
    }
    Ok(())
}

fn validate_captured_iteration_local_name(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    scope: NodeRef,
    declaration: NodeRef,
    name: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(), SourceFunctionStatementsError> {
    let record = control_statement_node(arena, bound, name)?;
    let NodeData::Identifier(identifier) = &record.data else {
        return Err(unsupported_control_statement(name, record.kind));
    };
    if record.kind != SyntaxKind::Identifier
        || record.flags.0 != 0
        || record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || bound.symbol(declaration) != Some(symbol)
    {
        return Err(unsupported_control_statement(name, record.kind));
    }
    let locals = bound
        .locals(scope)
        .ok_or(SourceFunctionStatementsInvariant::MissingLocals(scope))?;
    let actual = store
        .symbol_table(locals)
        .and_then(|locals| locals.get_source(&identifier.text));
    if actual != Some(symbol) {
        return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
            declaration,
            scope,
            expected: symbol,
            actual,
        }
        .into());
    }
    Ok(())
}

fn captured_iteration_callable_read(
    arena: &NodeArena,
    bound: &BoundFile,
    callable: NodeRef,
    body: NodeRef,
    expected: &str,
) -> Result<NodeRef, SourceFunctionStatementsError> {
    let body_record = control_statement_node(arena, bound, body)?;
    let NodeData::Block(block) = &body_record.data else {
        return Err(unsupported_control_statement(body, body_record.kind));
    };
    let [statement] = block.statements.nodes.as_slice() else {
        return Err(unsupported_control_statement(body, body_record.kind));
    };
    if body_record.kind != SyntaxKind::Block
        || body_record.flags.0 != 0
        || body_record.parent != Some(callable.node)
        || block.flow_node.is_some()
        || block.next_container.is_some()
        || block.statements.has_trailing_comma
        || block.facts != 0
        || bound.container(body) != Some(callable)
        || bound.block_scope_container(body) != Some(callable)
    {
        return Err(unsupported_control_statement(body, body_record.kind));
    }
    let statement = NodeRef::new(body.arena, body.file, *statement);
    let statement_record = control_statement_node(arena, bound, statement)?;
    let NodeData::ExpressionStatement(expression) = &statement_record.data else {
        return Err(unsupported_control_statement(
            statement,
            statement_record.kind,
        ));
    };
    if statement_record.kind != SyntaxKind::ExpressionStatement
        || statement_record.flags.0 != 0
        || statement_record.parent != Some(body.node)
        || expression.flow_node.is_some()
        || bound.container(statement) != Some(callable)
        || bound.block_scope_container(statement) != Some(callable)
    {
        return Err(unsupported_control_statement(
            statement,
            statement_record.kind,
        ));
    }
    let read = NodeRef::new(statement.arena, statement.file, expression.expression);
    let record = control_statement_node(arena, bound, read)?;
    let NodeData::Identifier(identifier) = &record.data else {
        return Err(unsupported_control_statement(read, record.kind));
    };
    if record.kind != SyntaxKind::Identifier
        || record.flags.0 != 0
        || record.parent != Some(statement.node)
        || identifier.flow_node.is_some()
        || identifier.text != expected
        || bound.container(read) != Some(callable)
        || bound.block_scope_container(read) != Some(callable)
        || bound.flow_container(read) != Some(callable)
    {
        return Err(unsupported_control_statement(read, record.kind));
    }
    Ok(read)
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
                    | SyntaxKind::FunctionDeclaration
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

/// Proves syntax only. The flow planner authenticates the detached logical rows.
#[allow(clippy::too_many_lines)] // Keep the complete source statement proof before any query.
pub(super) fn plan_source_linear_logical_statement_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    statement: NodeRef,
    container: NodeRef,
) -> Result<SourceLinearLogicalStatementSyntax, SourceFunctionStatementsError> {
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || !container.is_for(arena.id(), bound.file_id())
    {
        return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(container).into());
    }
    let reject = || unsupported_control_statement(statement, SyntaxKind::ExpressionStatement);
    if bound
        .source_facts()
        .is_none_or(|facts| facts.is_javascript_file() || facts.is_declaration_file())
    {
        return Err(reject());
    }
    let reference = |node| NodeRef::new(container.arena, container.file, node);
    let callable = control_statement_node(arena, bound, container)?;
    let body = match &callable.data {
        NodeData::FunctionDeclaration(function)
            if callable.kind == SyntaxKind::FunctionDeclaration =>
        {
            reference(function.body.ok_or_else(reject)?)
        }
        NodeData::ArrowFunction(function) if callable.kind == SyntaxKind::ArrowFunction => {
            reference(function.body)
        }
        _ => return Err(reject()),
    };
    let body_record = linear_logical_statement_child(arena, bound, body, container, container)?;
    let NodeData::Block(block) = &body_record.data else {
        return Err(reject());
    };
    if body_record.kind != SyntaxKind::Block
        || block.flow_node.is_some()
        || block.next_container.is_some()
        || block.facts != 0
        || block.statements.has_trailing_comma
        || block
            .statements
            .nodes
            .iter()
            .filter(|node| **node == statement.node)
            .count()
            != 1
    {
        return Err(reject());
    }
    let record = linear_logical_statement_child(arena, bound, statement, body, container)?;
    let NodeData::ExpressionStatement(data) = &record.data else {
        return Err(reject());
    };
    if record.kind != SyntaxKind::ExpressionStatement
        || data.flow_node.is_some()
        || bound.flow_container(statement) != Some(container)
        || bound.flow_graph().is_unreachable(statement) != Some(false)
    {
        return Err(reject());
    }
    let expression = reference(data.expression);
    let record = linear_logical_statement_child(arena, bound, expression, statement, container)?;
    let NodeData::BinaryExpression(binary) = &record.data else {
        return Err(reject());
    };
    if record.kind != SyntaxKind::BinaryExpression
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.facts != 0
        || binary.modifiers.is_some()
    {
        return Err(reject());
    }
    let left = reference(binary.left);
    let operator = reference(binary.operator_token);
    let right = reference(binary.right);
    let token = linear_logical_statement_child(arena, bound, operator, expression, container)?;
    if token.kind != SyntaxKind::AmpersandAmpersandToken
        || !matches!(token.data, NodeData::Token(_))
        || arena.source_text().and_then(|source| {
            source.get(token.range.start.get() as usize..token.range.end.get() as usize)
        }) != Some("&&")
    {
        return Err(reject());
    }
    let (left_receiver, left_name) =
        linear_logical_property_parts(arena, bound, left, expression, container)?;
    let call_record = linear_logical_statement_child(arena, bound, right, expression, container)?;
    let NodeData::CallExpression(call) = &call_record.data else {
        return Err(reject());
    };
    if call_record.kind != SyntaxKind::CallExpression
        || call.question_dot_token.is_some()
        || call.type_arguments.is_some()
        || call.symbol.is_some()
        || call.facts != 0
        || call.arguments.has_trailing_comma
        || control_statement_node(arena, bound, left)?.range.end > token.range.start
        || token.range.end > call_record.range.start
    {
        return Err(reject());
    }
    let callee = reference(call.expression);
    let (right_receiver, right_name) =
        linear_logical_property_parts(arena, bound, callee, right, container)?;
    let name_text = |node: NodeRef| match &arena.get(node.node)?.data {
        NodeData::Identifier(identifier) => Some(identifier.text.as_str()),
        _ => None,
    };
    if name_text(left_receiver) != name_text(right_receiver)
        || name_text(left_name) != name_text(right_name)
        || matches!(name_text(right_name), Some("push" | "unshift"))
    {
        return Err(reject());
    }
    let callee_record = control_statement_node(arena, bound, callee)?;
    if call.arguments.range.start < callee_record.range.end
        || call.arguments.range.end > call_record.range.end
    {
        return Err(reject());
    }
    let mut arguments = Vec::with_capacity(call.arguments.nodes.len());
    let mut previous_end = call.arguments.range.start;
    for argument in &call.arguments.nodes {
        let argument = reference(*argument);
        let record = linear_logical_statement_child(arena, bound, argument, right, container)?;
        if !matches!(
            record.kind,
            SyntaxKind::Identifier
                | SyntaxKind::NumericLiteral
                | SyntaxKind::BigIntLiteral
                | SyntaxKind::StringLiteral
                | SyntaxKind::NoSubstitutionTemplateLiteral
                | SyntaxKind::TrueKeyword
                | SyntaxKind::FalseKeyword
                | SyntaxKind::NullKeyword
        ) || matches!(&record.data, NodeData::Identifier(identifier)
            if identifier.text.is_empty() || identifier.flow_node.is_some())
            || record.range.start < previous_end
            || record.range.end > call.arguments.range.end
        {
            return Err(reject());
        }
        previous_end = record.range.end;
        arguments.push(argument);
    }
    Ok(SourceLinearLogicalStatementSyntax {
        container,
        statement,
        expression,
        left,
        left_receiver,
        left_name,
        operator,
        right,
        callee,
        right_receiver,
        right_name,
        arguments,
    })
}

fn linear_logical_statement_child<'arena>(
    arena: &'arena NodeArena,
    bound: &BoundFile,
    node: NodeRef,
    parent: NodeRef,
    container: NodeRef,
) -> Result<&'arena Node, SourceFunctionStatementsError> {
    let record = control_statement_node(arena, bound, node)?;
    if record.parent != Some(parent.node) {
        return Err(SourceFunctionStatementsInvariant::InvalidParent {
            node,
            expected: Some(parent.node),
            actual: record.parent,
        }
        .into());
    }
    if !range_contains(
        control_statement_node(arena, bound, parent)?.range,
        record.range,
    ) {
        return Err(SourceFunctionStatementsInvariant::InvalidRange { node, parent }.into());
    }
    if bound.container(node) != Some(container) {
        return Err(SourceFunctionStatementsInvariant::InvalidContainer {
            node,
            expected: container,
            actual: bound.container(node),
        }
        .into());
    }
    if bound.block_scope_container(node) != Some(container) {
        return Err(
            SourceFunctionStatementsInvariant::InvalidBlockScopeContainer {
                node,
                expected: container,
                actual: bound.block_scope_container(node),
            }
            .into(),
        );
    }
    if record.flags.0 != 0 {
        return Err(unsupported_control_statement(node, record.kind));
    }
    Ok(record)
}

fn linear_logical_property_parts(
    arena: &NodeArena,
    bound: &BoundFile,
    node: NodeRef,
    parent: NodeRef,
    container: NodeRef,
) -> Result<(NodeRef, NodeRef), SourceFunctionStatementsError> {
    let reject = || unsupported_control_statement(node, SyntaxKind::PropertyAccessExpression);
    let record = linear_logical_statement_child(arena, bound, node, parent, container)?;
    let NodeData::PropertyAccessExpression(access) = &record.data else {
        return Err(reject());
    };
    if record.kind != SyntaxKind::PropertyAccessExpression
        || access.question_dot_token.is_some()
        || access.flow_node.is_some()
        || access.facts != 0
    {
        return Err(reject());
    }
    let receiver = NodeRef::new(node.arena, node.file, access.expression);
    let name = NodeRef::new(node.arena, node.file, access.name);
    for child in [receiver, name] {
        let record = linear_logical_statement_child(arena, bound, child, node, container)?;
        if !matches!(&record.data, NodeData::Identifier(identifier)
            if record.kind == SyntaxKind::Identifier
                && !identifier.text.is_empty()
                && identifier.flow_node.is_none())
        {
            return Err(reject());
        }
    }
    if control_statement_node(arena, bound, receiver)?.range.end
        > control_statement_node(arena, bound, name)?.range.start
    {
        return Err(SourceFunctionStatementsInvariant::InvalidOrder {
            previous: receiver,
            next: name,
        }
        .into());
    }
    Ok((receiver, name))
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
        statement_scope: None,
    }
    .plan_linear()
}

/// Proves one function-owned lexical `for`, `while`, or `do...while` body.
pub(super) fn plan_source_loop_function_statements_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    callable: &SourceCallablePlan,
) -> Result<SourceLoopFunctionStatementsSyntax, SourceFunctionStatementsError> {
    SyntaxPlanner {
        arena,
        bound,
        store,
        callable,
        statement_scope: None,
    }
    .plan_loop()
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
        statement_scope: None,
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
        statement_scope: None,
    }
    .plan_switch()
}

/// Proves a string switch with bare returns and grouped unreachable calls.
pub(super) fn plan_source_void_switch_function_statements_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    callable: &SourceCallablePlan,
) -> Result<SourceVoidSwitchFunctionStatementsSyntax, SourceFunctionStatementsError> {
    SyntaxPlanner {
        arena,
        bound,
        store,
        callable,
        statement_scope: None,
    }
    .plan_void_switch()
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
        statement_scope: None,
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
        statement_scope: None,
    }
    .plan_joined()
}

/// Proves the common synchronous statement grammar without publishing state.
pub(super) fn plan_source_callable_statement_list_syntax(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    callable: &SourceCallablePlan,
) -> Result<SourceCallableStatementListSyntax, SourceFunctionStatementsError> {
    SyntaxPlanner {
        arena,
        bound,
        store,
        callable,
        statement_scope: None,
    }
    .plan_callable_statement_list()
}

struct SyntaxPlanner<'a> {
    arena: &'a NodeArena,
    bound: &'a BoundFile,
    store: &'a CanonicalTypeMapperStore,
    callable: &'a SourceCallablePlan,
    /// Set only while walking an authenticated common statement list.
    statement_scope: Option<NodeRef>,
}

impl SyntaxPlanner<'_> {
    fn plan_callable_statement_list(
        &self,
    ) -> Result<SourceCallableStatementListSyntax, SourceFunctionStatementsError> {
        let declaration = self.callable.declaration;
        if !declaration.is_for(self.arena.id(), self.bound.file_id())
            || self.bound.node_arena_id() != self.arena.id()
            || self.bound.node_arena_revision() != self.arena.revision()
        {
            return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(declaration).into());
        }
        let record = self.node(declaration)?;
        if self.callable.is_async
            || !self.callable.type_parameters.is_empty()
            || self.callable.type_predicate.is_some()
            || self
                .bound
                .source_facts()
                .is_none_or(|facts| facts.is_javascript_file() || facts.is_declaration_file())
        {
            return Err(self.unsupported(
                declaration,
                record.kind,
                SourceFunctionStatementsRole::Callable,
            ));
        }
        match &record.data {
            NodeData::FunctionDeclaration(function)
                if record.kind == SyntaxKind::FunctionDeclaration
                    && self.callable.family == SourceCallableFamily::FunctionDeclaration
                    && function.body == Some(self.callable.body.node)
                    && function.type_
                        == self.callable.return_type.type_node().map(|node| node.node)
                    && function.type_parameters.is_none()
                    && function.asterisk_token.is_none() =>
            {
                if self.bound.symbol(declaration) != Some(self.callable.owner_symbol)
                    || !function
                        .parameters
                        .nodes
                        .iter()
                        .copied()
                        .map(|node| self.reference(node))
                        .eq(self
                            .callable
                            .all_parameters()
                            .map(|parameter| parameter.declaration))
                    || self.callable.all_parameters().any(|parameter| {
                        !source_parameter_declarations_are_exact(
                            self.store,
                            declaration,
                            parameter.declaration,
                            parameter.symbol,
                        )
                    })
                {
                    return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                        declaration,
                    )
                    .into());
                }
            }
            NodeData::ArrowFunction(arrow)
                if record.kind == SyntaxKind::ArrowFunction
                    && self.callable.family == SourceCallableFamily::ArrowFunction
                    && arrow.type_parameters.is_none()
                    && arrow.modifiers.is_none()
                    && arrow.asterisk_token.is_none() =>
            {
                self.validate_for_of_arrow_callable()?
            }
            NodeData::FunctionExpression(function)
                if record.kind == SyntaxKind::FunctionExpression
                    && self.callable.family == SourceCallableFamily::ArrowFunction
                    && function.body == self.callable.body.node
                    && function.type_
                        == self.callable.return_type.type_node().map(|node| node.node)
                    && function.type_parameters.is_none()
                    && function.modifiers.is_none()
                    && function.asterisk_token.is_none() =>
            {
                if self.bound.symbol(declaration) != Some(self.callable.owner_symbol)
                    || !function
                        .parameters
                        .nodes
                        .iter()
                        .copied()
                        .map(|node| self.reference(node))
                        .eq(self
                            .callable
                            .all_parameters()
                            .map(|parameter| parameter.declaration))
                    || self.callable.all_parameters().any(|parameter| {
                        !source_parameter_declarations_are_exact(
                            self.store,
                            declaration,
                            parameter.declaration,
                            parameter.symbol,
                        )
                    })
                {
                    return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                        declaration,
                    )
                    .into());
                }
            }
            _ => {
                return Err(self.unsupported(
                    declaration,
                    record.kind,
                    SourceFunctionStatementsRole::Callable,
                ));
            }
        }
        let body = self.callable.body;
        self.validate_range(body, declaration)?;
        let nodes = self.plan_body(body, declaration)?;
        let statements = self.plan_callable_list(&nodes, body, declaration, 0)?;
        let flow = self.bound.flow_graph();
        if flow.container_is_complete(declaration) != Some(true) {
            return Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::IncompleteFlow(declaration),
            ));
        }
        if flow.container_start(declaration).is_none() {
            return Err(SourceFunctionStatementsInvariant::MissingFlowStart(declaration).into());
        }
        if flow.container_return(declaration).is_some() {
            return Err(
                SourceFunctionStatementsInvariant::UnexpectedReturnFlow(declaration).into(),
            );
        }
        Ok(SourceCallableStatementListSyntax {
            callable: self.callable.clone(),
            statements,
            has_implicit_return: flow.container_end(declaration).is_some(),
        })
    }

    fn plan_callable_list(
        &self,
        nodes: &[NodeId],
        parent: NodeRef,
        scope: NodeRef,
        depth: usize,
    ) -> Result<Vec<SourceCallableStatementSyntax>, SourceFunctionStatementsError> {
        if depth >= MAX_CALLABLE_STATEMENT_DEPTH {
            return Err(self.unsupported(
                parent,
                self.node(parent)?.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }
        let planner = SyntaxPlanner {
            arena: self.arena,
            bound: self.bound,
            store: self.store,
            callable: self.callable,
            statement_scope: Some(scope),
        };
        let mut statements = Vec::new();
        for &node in nodes {
            let statement = self.reference(node);
            if self.bound.flow_graph().is_unreachable(statement) == Some(true) {
                return Err(self.unsupported(
                    statement,
                    self.node(statement)?.kind,
                    SourceFunctionStatementsRole::BodyStatement,
                ));
            }
            statements.extend(planner.plan_callable_statement(statement, parent, scope, depth)?);
        }
        Ok(statements)
    }

    fn plan_callable_statement(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        scope: NodeRef,
        depth: usize,
    ) -> Result<Vec<SourceCallableStatementSyntax>, SourceFunctionStatementsError> {
        let callable = self.callable.declaration;
        let kind = self.node(statement)?.kind;
        let result = match kind {
            SyntaxKind::VariableStatement => {
                return self
                    .plan_local_statement(statement, parent, callable)
                    .map(|locals| {
                        locals
                            .into_iter()
                            .map(|local| {
                                SourceCallableStatementSyntax::Leaf(
                                    SourceLinearFunctionStatementSyntax::Local(local),
                                )
                            })
                            .collect()
                    });
            }
            SyntaxKind::ExpressionStatement => {
                let expression =
                    self.plan_linear_expression_statement(statement, parent, callable, false)?;
                SourceCallableStatementSyntax::Leaf(
                    SourceLinearFunctionStatementSyntax::Expression {
                        statement,
                        expression,
                    },
                )
            }
            SyntaxKind::EmptyStatement => {
                self.validate_empty_statement(statement, parent, callable)?;
                SourceCallableStatementSyntax::Empty(statement)
            }
            SyntaxKind::ReturnStatement => SourceCallableStatementSyntax::Return {
                statement,
                expression: self.plan_linear_return(statement, parent, callable)?,
            },
            SyntaxKind::Block => {
                let record = self.node(statement)?;
                let NodeData::Block(block) = &record.data else {
                    return Err(self.unsupported(
                        statement,
                        kind,
                        SourceFunctionStatementsRole::BranchBlock,
                    ));
                };
                if record.flags.0 != 0
                    || record.parent != Some(parent.node)
                    || block.flow_node.is_some()
                    || block.next_container.is_some()
                    || block.statements.has_trailing_comma
                    || block.facts != 0
                {
                    return Err(self.unsupported(
                        statement,
                        kind,
                        SourceFunctionStatementsRole::BranchBlock,
                    ));
                }
                self.validate_range(statement, parent)?;
                self.validate_container(statement, callable)?;
                self.validate_block_scope_container(statement, scope)?;
                self.validate_node_list(
                    statement,
                    block.statements.range,
                    &block.statements.nodes,
                )?;
                SourceCallableStatementSyntax::Block {
                    block: statement,
                    statements: self.plan_callable_list(
                        &block.statements.nodes,
                        statement,
                        statement,
                        depth + 1,
                    )?,
                }
            }
            SyntaxKind::IfStatement => SourceCallableStatementSyntax::If(Box::new(
                self.plan_callable_if(statement, parent, scope, depth)?,
            )),
            _ => {
                return Err(self.unsupported(
                    statement,
                    kind,
                    SourceFunctionStatementsRole::BodyStatement,
                ));
            }
        };
        Ok(vec![result])
    }

    fn plan_callable_if(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        scope: NodeRef,
        depth: usize,
    ) -> Result<SourceCallableIfSyntax, SourceFunctionStatementsError> {
        let control = plan_source_control_if_syntax(self.arena, self.bound, statement, parent)?;
        if !control.nested_export_diagnostics.is_empty() {
            return Err(self.unsupported(
                statement,
                SyntaxKind::IfStatement,
                SourceFunctionStatementsRole::IfStatement,
            ));
        }
        if self.node(control.then_statement)?.kind == SyntaxKind::EmptyStatement {
            return Err(self.unsupported(
                control.then_statement,
                SyntaxKind::EmptyStatement,
                SourceFunctionStatementsRole::BranchBlock,
            ));
        }
        self.validate_container(statement, self.callable.declaration)?;
        self.validate_block_scope_container(statement, scope)?;
        let condition = match self.plan_condition(control.condition, self.callable.declaration) {
            Ok(condition) => Some(condition),
            Err(error @ SourceFunctionStatementsError::Unsupported(_))
                if self.condition_requires_narrowing(control.condition)? =>
            {
                return Err(error);
            }
            Err(SourceFunctionStatementsError::Unsupported(_)) => None,
            Err(error) => return Err(error),
        };
        let then_statements =
            self.plan_callable_list(&[control.then_statement.node], statement, scope, depth + 1)?;
        let else_statements = control
            .else_statement
            .map(|branch| self.plan_callable_list(&[branch.node], statement, scope, depth + 1))
            .transpose()?
            .unwrap_or_default();
        Ok(SourceCallableIfSyntax {
            control,
            condition_identifier: condition.map(|condition| condition.identifier),
            typeof_condition: condition.and_then(|condition| condition.typeof_condition),
            equality_condition: condition.and_then(|condition| condition.equality_condition),
            then_statements,
            else_statements,
        })
    }

    fn plan_void_switch(
        &self,
    ) -> Result<SourceVoidSwitchFunctionStatementsSyntax, SourceFunctionStatementsError> {
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
        let Some(annotation) = parameter.explicit_type_node() else {
            return Err(self.unsupported(
                parameter.declaration,
                self.node(parameter.declaration)?.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        };
        let annotation_record = self.node(annotation)?;
        if annotation_record.kind != SyntaxKind::StringKeyword
            || annotation_record.flags.0 != 0
            || annotation_record.parent != Some(parameter.declaration.node)
            || self.bound.symbol(parameter.declaration) != Some(parameter.symbol)
        {
            return Err(self.unsupported(
                annotation,
                annotation_record.kind,
                SourceFunctionStatementsRole::Condition,
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
        let NodeData::Identifier(identifier) = &discriminant.data else {
            return Err(self.unsupported(
                switch.expression,
                discriminant.kind,
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
        if discriminant.kind != SyntaxKind::Identifier
            || discriminant.flags.0 != 0
            || identifier.flow_node.is_some()
            || identifier.text != parameter_identifier.text
            || parameter_name_record.kind != SyntaxKind::Identifier
            || parameter_name_record.parent != Some(parameter.declaration.node)
        {
            return Err(self.unsupported(
                switch.expression,
                discriminant.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        }

        let graph = self.bound.flow_graph();
        let start = graph.container_start(declaration).ok_or(
            SourceFunctionStatementsInvariant::MissingFlowStart(declaration),
        )?;
        if graph.container_is_complete(declaration) != Some(true)
            || graph.container_end(declaration).is_none()
            || self.switch_flow_at(switch.statement, declaration)? != start
            || self.switch_flow_at(switch.expression, declaration)? != start
        {
            return Err(Self::incomplete_switch_flow(switch.statement));
        }

        let mut returns = Vec::new();
        let mut calls = Vec::new();
        let mut has_default = false;
        for clause in &switch.clauses {
            self.validate_block_scope_container(clause.clause, switch.case_block)?;
            if let Some(case) = clause.expression {
                self.validate_block_scope_container(case, switch.case_block)?;
                let record = self.node(case)?;
                let NodeData::StringLiteral(literal) = &record.data else {
                    return Err(self.unsupported(
                        case,
                        record.kind,
                        SourceFunctionStatementsRole::Condition,
                    ));
                };
                if record.kind != SyntaxKind::StringLiteral
                    || record.flags.0 != 0
                    || literal.token_flags.0 != 0
                {
                    return Err(self.unsupported(
                        case,
                        record.kind,
                        SourceFunctionStatementsRole::Condition,
                    ));
                }
            } else if has_default {
                return Err(self.unsupported(
                    clause.clause,
                    self.node(clause.clause)?.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            } else {
                has_default = true;
            }

            for statement in &clause.statements {
                self.validate_block_scope_container(*statement, switch.case_block)?;
                let unreachable = graph.is_unreachable(*statement).ok_or(
                    SourceFunctionStatementsInvariant::InvalidFlowContainer {
                        node: *statement,
                        expected: declaration,
                        actual: self.bound.flow_container(*statement),
                    },
                )?;
                if self.bound.flow_container(*statement) != Some(declaration)
                    || !unreachable && self.bound.flow_at(*statement).is_none()
                {
                    return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                        node: *statement,
                        expected: declaration,
                        actual: self.bound.flow_container(*statement),
                    }
                    .into());
                }

                let record = self.node(*statement)?;
                match &record.data {
                    NodeData::ReturnStatement(returned)
                        if record.kind == SyntaxKind::ReturnStatement
                            && record.flags.0 == 0
                            && record.parent == Some(clause.clause.node)
                            && returned.expression.is_none()
                            && returned.flow_node.is_none()
                            && returned.facts == 0
                            && !unreachable =>
                    {
                        returns.push(*statement);
                    }
                    NodeData::ExpressionStatement(expression)
                        if record.kind == SyntaxKind::ExpressionStatement
                            && record.flags.0 == 0
                            && record.parent == Some(clause.clause.node)
                            && expression.flow_node.is_none() =>
                    {
                        let call = self.reference(expression.expression);
                        self.validate_parent(
                            call,
                            Some(statement.node),
                            SourceFunctionStatementsRole::BranchStatement,
                        )?;
                        self.validate_range(call, *statement)?;
                        self.validate_container(call, declaration)?;
                        self.validate_block_scope_container(call, switch.case_block)?;
                        let call_record = self.node(call)?;
                        let NodeData::CallExpression(call_data) = &call_record.data else {
                            return Err(self.unsupported(
                                call,
                                call_record.kind,
                                SourceFunctionStatementsRole::BranchStatement,
                            ));
                        };
                        let [argument] = call_data.arguments.nodes.as_slice() else {
                            return Err(self.unsupported(
                                call,
                                call_record.kind,
                                SourceFunctionStatementsRole::BranchStatement,
                            ));
                        };
                        let argument = self.reference(*argument);
                        let argument_record = self.node(argument)?;
                        if call_record.kind != SyntaxKind::CallExpression
                            || call_record.flags.0 != 0
                            || call_data.question_dot_token.is_some()
                            || call_data.symbol.is_some()
                            || call_data.type_arguments.is_some()
                            || call_data.arguments.has_trailing_comma
                            || call_data.facts != 0
                            || argument_record.kind != SyntaxKind::StringLiteral
                            || argument_record.flags.0 != 0
                            || argument_record.parent != Some(call.node)
                        {
                            return Err(self.unsupported(
                                call,
                                call_record.kind,
                                SourceFunctionStatementsRole::BranchStatement,
                            ));
                        }
                        self.validate_container(argument, declaration)?;
                        self.validate_block_scope_container(argument, switch.case_block)?;
                        calls.push(SourceVoidSwitchCallSyntax {
                            statement: *statement,
                            expression: call,
                            unreachable,
                        });
                    }
                    _ => {
                        return Err(self.unsupported(
                            *statement,
                            record.kind,
                            SourceFunctionStatementsRole::BranchStatement,
                        ));
                    }
                }
            }
        }
        if returns.is_empty() || calls.is_empty() {
            return Err(self.unsupported(
                switch.statement,
                SyntaxKind::SwitchStatement,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }

        Ok(SourceVoidSwitchFunctionStatementsSyntax {
            body,
            switch,
            returns,
            calls,
        })
    }

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
        if condition.identifier != control.condition
            || condition.typeof_condition.is_some()
            || condition.equality_condition.is_some()
        {
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
        let (leading, switch_id) = match statements.as_slice() {
            [switch] => (None, *switch),
            [binding, switch] => (
                Some(self.plan_switch_object_binding(
                    self.reference(*binding),
                    body,
                    declaration,
                )?),
                *switch,
            ),
            _ => {
                let statement = statements
                    .first()
                    .copied()
                    .map_or(body, |node| self.reference(node));
                return Err(self.unsupported(
                    statement,
                    self.node(statement)?.kind,
                    SourceFunctionStatementsRole::BodyStatement,
                ));
            }
        };
        let switch = plan_source_control_switch_syntax(
            self.arena,
            self.bound,
            self.reference(switch_id),
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
        if let Some(binding) = &leading
            && !binding.elements.iter().any(|element| {
                self.node(element.name).is_ok_and(|record| {
                    matches!(&record.data, NodeData::Identifier(name) if name.text == identifier.text)
                })
            })
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
        let no_match_flow =
            self.validate_switch_flow(&switch, &returns, has_default, leading.as_ref())?;

        Ok(SourceSwitchFunctionStatementsSyntax {
            body,
            leading,
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
        leading: Option<&SourceSwitchObjectBindingSyntax>,
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
        if let Some(binding) = leading {
            let mut current = switch_flow;
            for element in binding.elements.iter().rev() {
                let assignment = flow
                    .nodes()
                    .get(current)
                    .ok_or_else(|| Self::incomplete_switch_flow(element.element))?;
                if joined_semantic_flow_flags(assignment.flags) != FlowFlags::ASSIGNMENT.bits()
                    || assignment.payload != Some(FlowNodePayload::Ast(element.element))
                    || !assignment.antecedents.is_empty()
                {
                    return Err(Self::incomplete_switch_flow(element.element));
                }
                current = assignment
                    .antecedent
                    .ok_or_else(|| Self::incomplete_switch_flow(element.element))?;
            }
            if current != start {
                return Err(Self::incomplete_switch_flow(binding.statement));
            }
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
            let mut return_flow = self.switch_flow_at(value.statement, declaration)?;
            if let Some(binding) = value.binding {
                let assignment = flow
                    .nodes()
                    .get(return_flow)
                    .ok_or_else(|| Self::incomplete_switch_flow(binding.statement))?;
                if joined_semantic_flow_flags(assignment.flags) != FlowFlags::ASSIGNMENT.bits()
                    || assignment.payload != Some(FlowNodePayload::Ast(binding.element))
                    || !assignment.antecedents.is_empty()
                {
                    return Err(Self::incomplete_switch_flow(binding.statement));
                }
                return_flow = assignment
                    .antecedent
                    .ok_or_else(|| Self::incomplete_switch_flow(binding.statement))?;
                if self.switch_flow_at(binding.statement, declaration)? != return_flow {
                    return Err(Self::incomplete_switch_flow(binding.statement));
                }
            }
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

    fn plan_switch_object_binding(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<SourceSwitchObjectBindingSyntax, SourceFunctionStatementsError> {
        let (pattern, elements, initializer) = self.plan_switch_binding_declaration(
            statement,
            parent,
            callable,
            callable,
            SyntaxKind::ObjectBindingPattern,
        )?;
        if elements.len() < 2 {
            return Err(self.unsupported(
                pattern,
                SyntaxKind::ObjectBindingPattern,
                SourceFunctionStatementsRole::LocalName,
            ));
        }
        let mut names = HashSet::with_capacity(elements.len());
        let mut bindings = Vec::with_capacity(elements.len());
        for element in elements {
            let binding = self.plan_switch_binding_element(element, pattern, callable, callable)?;
            if !names.insert(binding.symbol) {
                return Err(self.unsupported(
                    element,
                    SyntaxKind::BindingElement,
                    SourceFunctionStatementsRole::LocalName,
                ));
            }
            bindings.push(binding);
        }
        Ok(SourceSwitchObjectBindingSyntax {
            statement,
            initializer,
            elements: bindings,
        })
    }

    fn plan_switch_array_binding(
        &self,
        statement: NodeRef,
        clause: NodeRef,
        scope: NodeRef,
        callable: NodeRef,
    ) -> Result<SourceSwitchArrayBindingSyntax, SourceFunctionStatementsError> {
        let (pattern, elements, initializer) = self.plan_switch_binding_declaration(
            statement,
            clause,
            scope,
            callable,
            SyntaxKind::ArrayBindingPattern,
        )?;
        let mut named = None;
        for element in elements {
            let record = self.node(element)?;
            if matches!(&record.data, NodeData::OmittedExpression(_)) {
                if record.kind != SyntaxKind::OmittedExpression
                    || record.flags.0 != 0
                    || record.range.start != record.range.end
                    || self.bound.symbol(element).is_some()
                    || self.bound.local_symbol(element).is_some()
                {
                    return Err(self.unsupported(
                        element,
                        record.kind,
                        SourceFunctionStatementsRole::LocalName,
                    ));
                }
                self.validate_parent(
                    element,
                    Some(pattern.node),
                    SourceFunctionStatementsRole::LocalName,
                )?;
                self.validate_range(element, pattern)?;
                self.validate_container(element, callable)?;
                self.validate_block_scope_container(element, scope)?;
                continue;
            }
            if named.replace(element).is_some() {
                return Err(self.unsupported(
                    pattern,
                    SyntaxKind::ArrayBindingPattern,
                    SourceFunctionStatementsRole::LocalName,
                ));
            }
        }
        let element = named.ok_or_else(|| {
            self.unsupported(
                pattern,
                SyntaxKind::ArrayBindingPattern,
                SourceFunctionStatementsRole::LocalName,
            )
        })?;
        let binding = self.plan_switch_binding_element(element, pattern, scope, callable)?;
        Ok(SourceSwitchArrayBindingSyntax {
            statement,
            pattern,
            element: binding.element,
            name: binding.name,
            symbol: binding.symbol,
            initializer,
        })
    }

    fn plan_switch_binding_declaration(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        scope: NodeRef,
        callable: NodeRef,
        pattern_kind: SyntaxKind,
    ) -> Result<(NodeRef, Vec<NodeRef>, NodeRef), SourceFunctionStatementsError> {
        let record = self.node(statement)?;
        let NodeData::VariableStatement(variable_statement) = &record.data else {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::LocalStatement,
            ));
        };
        if record.kind != SyntaxKind::VariableStatement
            || record.flags.0 != 0
            || record.parent != Some(parent.node)
            || variable_statement.modifiers.is_some()
            || variable_statement.flow_node.is_some()
            || variable_statement.facts != 0
        {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::LocalStatement,
            ));
        }
        self.validate_range(statement, parent)?;
        self.validate_container(statement, callable)?;
        self.validate_block_scope_container(statement, scope)?;

        let list = self.reference(variable_statement.declaration_list);
        let list_record = self.node(list)?;
        let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
            return Err(self.unsupported(
                list,
                list_record.kind,
                SourceFunctionStatementsRole::LocalDeclarationList,
            ));
        };
        let [declaration] = declarations.declarations.nodes.as_slice() else {
            return Err(self.unsupported(
                list,
                list_record.kind,
                SourceFunctionStatementsRole::LocalDeclarationList,
            ));
        };
        if list_record.kind != SyntaxKind::VariableDeclarationList
            || list_record.flags.0 != NODE_FLAG_CONST
            || list_record.parent != Some(statement.node)
            || declarations.declarations.range != list_record.range
            || declarations.declarations.has_trailing_comma
            || declarations.facts != 0
        {
            return Err(self.unsupported(
                list,
                list_record.kind,
                SourceFunctionStatementsRole::LocalDeclarationList,
            ));
        }
        self.validate_range(list, statement)?;
        self.validate_container(list, callable)?;
        self.validate_block_scope_container(list, scope)?;

        let declaration = self.reference(*declaration);
        let declaration_record = self.node(declaration)?;
        let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
            return Err(self.unsupported(
                declaration,
                declaration_record.kind,
                SourceFunctionStatementsRole::LocalDeclaration,
            ));
        };
        if declaration_record.kind != SyntaxKind::VariableDeclaration
            || declaration_record.flags.0 != 0
            || declaration_record.parent != Some(list.node)
            || variable.exclamation_token.is_some()
            || variable.local_symbol.is_some()
            || variable.symbol.is_some()
            || variable.type_.is_some()
            || variable.facts != 0
            || self.bound.symbol(declaration).is_some()
        {
            return Err(self.unsupported(
                declaration,
                declaration_record.kind,
                SourceFunctionStatementsRole::LocalDeclaration,
            ));
        }
        self.validate_range(declaration, list)?;
        self.validate_container(declaration, callable)?;
        self.validate_block_scope_container(declaration, scope)?;

        let pattern = self.reference(variable.name);
        let pattern_record = self.node(pattern)?;
        let NodeData::BindingPattern(bindings) = &pattern_record.data else {
            return Err(self.unsupported(
                pattern,
                pattern_record.kind,
                SourceFunctionStatementsRole::LocalName,
            ));
        };
        if pattern_record.kind != pattern_kind
            || pattern_record.flags.0 != 0
            || pattern_record.parent != Some(declaration.node)
            || bindings.elements.nodes.is_empty()
            || bindings.elements.has_trailing_comma
                && pattern_kind != SyntaxKind::ArrayBindingPattern
            || bindings.elements.range != pattern_record.range
            || bindings.facts != 0
        {
            return Err(self.unsupported(
                pattern,
                pattern_record.kind,
                SourceFunctionStatementsRole::LocalName,
            ));
        }
        self.validate_range(pattern, declaration)?;
        self.validate_container(pattern, callable)?;
        self.validate_block_scope_container(pattern, scope)?;

        let initializer = variable
            .initializer
            .map(|node| self.reference(node))
            .ok_or(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::MissingInitializer(declaration),
            ))?;
        let initializer_record = self.node(initializer)?;
        let NodeData::Identifier(identifier) = &initializer_record.data else {
            return Err(self.unsupported(
                initializer,
                initializer_record.kind,
                SourceFunctionStatementsRole::LocalInitializer,
            ));
        };
        if initializer_record.kind != SyntaxKind::Identifier
            || initializer_record.flags.0 != 0
            || initializer_record.parent != Some(declaration.node)
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
        {
            return Err(self.unsupported(
                initializer,
                initializer_record.kind,
                SourceFunctionStatementsRole::LocalInitializer,
            ));
        }
        self.validate_range(initializer, declaration)?;
        self.validate_order(pattern, initializer)?;
        self.validate_container(initializer, callable)?;
        self.validate_block_scope_container(initializer, scope)?;

        Ok((
            pattern,
            bindings
                .elements
                .nodes
                .iter()
                .map(|node| self.reference(*node))
                .collect(),
            initializer,
        ))
    }

    fn plan_switch_binding_element(
        &self,
        element: NodeRef,
        pattern: NodeRef,
        scope: NodeRef,
        callable: NodeRef,
    ) -> Result<SourceSwitchObjectBindingElementSyntax, SourceFunctionStatementsError> {
        let record = self.node(element)?;
        let NodeData::BindingElement(binding) = &record.data else {
            return Err(self.unsupported(
                element,
                record.kind,
                SourceFunctionStatementsRole::LocalName,
            ));
        };
        if record.kind != SyntaxKind::BindingElement
            || record.flags.0 != 0
            || record.parent != Some(pattern.node)
            || binding.dot_dot_dot_token.is_some()
            || binding.flow_node.is_some()
            || binding.initializer.is_some()
            || binding.local_symbol.is_some()
            || binding.symbol.is_some()
            || binding.facts != 0
        {
            return Err(self.unsupported(
                element,
                record.kind,
                SourceFunctionStatementsRole::LocalName,
            ));
        }
        self.validate_range(element, pattern)?;
        self.validate_container(element, callable)?;
        self.validate_block_scope_container(element, scope)?;

        let name = binding.name.map(|node| self.reference(node)).ok_or(
            SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::Syntax {
                    node: element,
                    kind: record.kind,
                    role: SourceFunctionStatementsRole::LocalName,
                },
            ),
        )?;
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
            || name_record.parent != Some(element.node)
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
        {
            return Err(self.unsupported(
                name,
                name_record.kind,
                SourceFunctionStatementsRole::LocalName,
            ));
        }
        self.validate_range(name, element)?;
        self.validate_container(name, callable)?;
        self.validate_block_scope_container(name, scope)?;

        let property = binding
            .property_name
            .map_or(name, |property| self.reference(property));
        let computed_key = if property == name {
            None
        } else {
            if self.node(pattern)?.kind != SyntaxKind::ObjectBindingPattern {
                return Err(self.unsupported(
                    property,
                    self.node(property)?.kind,
                    SourceFunctionStatementsRole::LocalName,
                ));
            }
            let record = self.node(property)?;
            self.validate_parent(
                property,
                Some(element.node),
                SourceFunctionStatementsRole::LocalName,
            )?;
            self.validate_range(property, element)?;
            self.validate_order(property, name)?;
            self.validate_container(property, callable)?;
            self.validate_block_scope_container(property, scope)?;
            if record.flags.0 != 0 {
                return Err(self.unsupported(
                    property,
                    record.kind,
                    SourceFunctionStatementsRole::LocalName,
                ));
            }
            match &record.data {
                NodeData::Identifier(property_name)
                    if record.kind == SyntaxKind::Identifier
                        && property_name.flow_node.is_none()
                        && !property_name.text.is_empty() =>
                {
                    None
                }
                NodeData::StringLiteral(literal)
                    if record.kind == SyntaxKind::StringLiteral && literal.token_flags.0 == 0 =>
                {
                    None
                }
                NodeData::NumericLiteral(literal)
                    if record.kind == SyntaxKind::NumericLiteral && literal.token_flags.0 == 0 =>
                {
                    None
                }
                NodeData::ComputedPropertyName(computed)
                    if record.kind == SyntaxKind::ComputedPropertyName && computed.facts == 0 =>
                {
                    let key = self.reference(computed.expression);
                    self.validate_parent(
                        key,
                        Some(property.node),
                        SourceFunctionStatementsRole::LocalName,
                    )?;
                    self.validate_range(key, property)?;
                    self.validate_container(key, callable)?;
                    self.validate_block_scope_container(key, scope)?;
                    let key_record = self.node(key)?;
                    let valid = match &key_record.data {
                        NodeData::StringLiteral(literal)
                            if key_record.kind == SyntaxKind::StringLiteral =>
                        {
                            literal.token_flags.0 == 0
                        }
                        NodeData::NumericLiteral(literal)
                            if key_record.kind == SyntaxKind::NumericLiteral =>
                        {
                            literal.token_flags.0 == 0
                        }
                        NodeData::NoSubstitutionTemplateLiteral(literal)
                            if key_record.kind == SyntaxKind::NoSubstitutionTemplateLiteral =>
                        {
                            literal.token_flags.0 == 0 && literal.template_flags.0 == 0
                        }
                        _ => false,
                    };
                    if key_record.flags.0 != 0 || !valid {
                        return Err(self.unsupported(
                            key,
                            key_record.kind,
                            SourceFunctionStatementsRole::LocalName,
                        ));
                    }
                    Some(key)
                }
                _ => {
                    return Err(self.unsupported(
                        property,
                        record.kind,
                        SourceFunctionStatementsRole::LocalName,
                    ));
                }
            }
        };

        let symbol = plan_top_level_variable(
            self.bound,
            self.store,
            element,
            name,
            &identifier.text,
            VariableBindingKind::Const,
            false,
        )?;
        let actual = self
            .bound
            .locals(scope)
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&identifier.text));
        if actual != Some(symbol) {
            return Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                declaration: element,
                scope,
                expected: symbol,
                actual,
            }
            .into());
        }
        Ok(SourceSwitchObjectBindingElementSyntax {
            element,
            property,
            computed_key,
            name,
            symbol,
        })
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
                [binding, statement] if clause.expression.is_none() => {
                    let binding = self.plan_switch_array_binding(
                        *binding,
                        clause.clause,
                        switch.case_block,
                        declaration,
                    )?;
                    let mut value = self.plan_switch_return(
                        clause.clause,
                        *statement,
                        switch.case_block,
                        declaration,
                    )?;
                    value.binding = Some(binding);
                    returns.push(value);
                }
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
        self.validate_switch_return_expression(expression, callable, scope)?;
        Ok(SourceSwitchReturnSyntax {
            clause,
            statement,
            expression,
            binding: None,
        })
    }

    fn validate_switch_return_expression(
        &self,
        expression: NodeRef,
        callable: NodeRef,
        scope: NodeRef,
    ) -> Result<(), SourceFunctionStatementsError> {
        let record = self.node(expression)?;
        match &record.data {
            NodeData::Identifier(identifier)
                if record.kind == SyntaxKind::Identifier
                    && record.flags.0 == 0
                    && identifier.flow_node.is_none()
                    && !identifier.text.is_empty() =>
            {
                Ok(())
            }
            NodeData::ElementAccessExpression(access)
                if record.kind == SyntaxKind::ElementAccessExpression
                    && record.flags.0 == 0
                    && access.question_dot_token.is_none()
                    && access.flow_node.is_none()
                    && access.facts == 0 =>
            {
                let receiver = self.reference(access.expression);
                let index = self.reference(access.argument_expression);
                for child in [receiver, index] {
                    self.validate_parent(
                        child,
                        Some(expression.node),
                        SourceFunctionStatementsRole::ReturnExpression,
                    )?;
                    self.validate_range(child, expression)?;
                    self.validate_container(child, callable)?;
                    self.validate_block_scope_container(child, scope)?;
                }
                self.validate_order(receiver, index)?;
                let receiver_record = self.node(receiver)?;
                let NodeData::Identifier(identifier) = &receiver_record.data else {
                    return Err(self.unsupported(
                        receiver,
                        receiver_record.kind,
                        SourceFunctionStatementsRole::ReturnExpression,
                    ));
                };
                if receiver_record.kind != SyntaxKind::Identifier
                    || receiver_record.flags.0 != 0
                    || identifier.flow_node.is_some()
                    || identifier.text.is_empty()
                {
                    return Err(self.unsupported(
                        receiver,
                        receiver_record.kind,
                        SourceFunctionStatementsRole::ReturnExpression,
                    ));
                }
                let index_record = self.node(index)?;
                let NodeData::NumericLiteral(literal) = &index_record.data else {
                    return Err(self.unsupported(
                        index,
                        index_record.kind,
                        SourceFunctionStatementsRole::ReturnExpression,
                    ));
                };
                if index_record.kind != SyntaxKind::NumericLiteral
                    || index_record.flags.0 != 0
                    || literal.token_flags.0 != 0
                {
                    return Err(self.unsupported(
                        index,
                        index_record.kind,
                        SourceFunctionStatementsRole::ReturnExpression,
                    ));
                }
                Ok(())
            }
            _ => self.validate_switch_literal(
                expression,
                SourceFunctionStatementsRole::ReturnExpression,
            ),
        }
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
        let record = self.node(declaration)?;
        let expected_return = self
            .callable
            .return_type
            .type_node()
            .map(|type_node| type_node.node);
        let valid_callable = match &record.data {
            NodeData::FunctionDeclaration(function) => {
                self.callable.family == SourceCallableFamily::FunctionDeclaration
                    && record.kind == SyntaxKind::FunctionDeclaration
                    && function.body == Some(self.callable.body.node)
                    && function.type_ == expected_return
            }
            NodeData::ArrowFunction(function) => {
                self.callable.family == SourceCallableFamily::ArrowFunction
                    && record.kind == SyntaxKind::ArrowFunction
                    && function.body == self.callable.body.node
                    && function.type_ == expected_return
            }
            NodeData::MethodDeclaration(method) => {
                self.callable.family == SourceCallableFamily::ObjectLiteralMethod
                    && record.kind == SyntaxKind::MethodDeclaration
                    && method.body == Some(self.callable.body.node)
                    && method.type_ == expected_return
                    && self.store.source_object_literal_method_owner_is_exact(
                        declaration,
                        self.callable.owner_symbol,
                    )
            }
            _ => false,
        };
        if !valid_callable {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        }

        let body = self.callable.body;
        self.validate_range(body, declaration)?;
        let body_statements = self.plan_body(body, declaration)?;
        let mut locals = Vec::new();
        let mut statements = Vec::new();
        let mut return_statement = None;
        let mut return_expression = None;
        let mut has_throw = false;
        for (index, statement_id) in body_statements.iter().copied().enumerate() {
            let statement = self.reference(statement_id);
            if has_throw
                && !matches!(
                    self.node(statement)?.kind,
                    SyntaxKind::ExpressionStatement | SyntaxKind::ThrowStatement
                )
            {
                return Err(self.unsupported(
                    statement,
                    self.node(statement)?.kind,
                    SourceFunctionStatementsRole::BodyStatement,
                ));
            }
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
                        self.plan_linear_expression_statement(statement, body, declaration, true)?;
                    statements.push(SourceLinearFunctionStatementSyntax::Expression {
                        statement,
                        expression,
                    });
                }
                SyntaxKind::ThrowStatement
                    if self.callable.family == SourceCallableFamily::FunctionDeclaration =>
                {
                    let expression = self.plan_linear_throw(statement, body, declaration)?;
                    statements.push(SourceLinearFunctionStatementSyntax::Throw {
                        statement,
                        expression,
                    });
                    has_throw = true;
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
        if (return_statement.is_some() || has_throw) && flow.container_end(declaration).is_some() {
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
            unreachable_ranges: if has_throw {
                let body_statements = body_statements
                    .iter()
                    .map(|statement| self.reference(*statement))
                    .collect::<Vec<_>>();
                switch_clause_unreachable_ranges(self.arena, self.bound, body, &body_statements)?
            } else {
                Vec::new()
            },
        })
    }

    fn plan_for_in(&self) -> Result<SourceForInStatementSyntax, SourceFunctionStatementsError> {
        self.plan_iteration(SourceControlLoopKind::ForIn)
    }

    fn plan_for_of(&self) -> Result<SourceForInStatementSyntax, SourceFunctionStatementsError> {
        self.plan_iteration(SourceControlLoopKind::ForOf)
    }

    fn plan_iteration(
        &self,
        expected_kind: SourceControlLoopKind,
    ) -> Result<SourceForInStatementSyntax, SourceFunctionStatementsError> {
        let declaration = self.callable.declaration;
        if !declaration.is_for(self.arena.id(), self.bound.file_id())
            || self.bound.node_arena_id() != self.arena.id()
            || self.bound.node_arena_revision() != self.arena.revision()
        {
            return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(declaration).into());
        }
        let record = self.node(declaration)?;
        match (&record.data, self.callable.family) {
            (
                NodeData::FunctionDeclaration(function),
                SourceCallableFamily::FunctionDeclaration,
            ) => {
                if record.kind != SyntaxKind::FunctionDeclaration
                    || function.body != Some(self.callable.body.node)
                    || function.type_
                        != self
                            .callable
                            .return_type
                            .type_node()
                            .map(|type_node| type_node.node)
                {
                    return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(
                        declaration,
                    )
                    .into());
                }
            }
            (NodeData::ArrowFunction(_), SourceCallableFamily::ArrowFunction)
                if expected_kind == SourceControlLoopKind::ForOf =>
            {
                self.validate_for_of_arrow_callable()?;
            }
            _ => {
                return Err(self.unsupported(
                    declaration,
                    record.kind,
                    SourceFunctionStatementsRole::Callable,
                ));
            }
        }

        let body = self.callable.body;
        self.validate_range(body, declaration)?;
        let statements = self.plan_body(body, declaration)?;
        let Some((&statement, trailing)) = statements.split_first() else {
            return Err(self.unsupported(
                body,
                SyntaxKind::Block,
                SourceFunctionStatementsRole::FunctionBody,
            ));
        };
        let statement = self.reference(statement);
        let expected_syntax = match expected_kind {
            SourceControlLoopKind::ForIn => SyntaxKind::ForInStatement,
            SourceControlLoopKind::ForOf => SyntaxKind::ForOfStatement,
            _ => {
                return Err(self.unsupported(
                    statement,
                    self.node(statement)?.kind,
                    SourceFunctionStatementsRole::BodyStatement,
                ));
            }
        };
        if self.node(statement)?.kind != expected_syntax {
            return Err(self.unsupported(
                statement,
                self.node(statement)?.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }
        self.validate_block_scope_container(statement, declaration)?;

        let mut syntax = plan_source_scoped_iteration_statement_syntax(
            self.arena,
            self.bound,
            self.store,
            statement,
            (body, declaration),
            expected_kind,
            Some(self.callable),
        )?;
        syntax.trailing_statements =
            self.plan_loop_trailing_statements(trailing, body, declaration, &syntax.locals)?;
        let graph = self.bound.flow_graph();
        let start = graph.container_start(declaration).ok_or(
            SourceFunctionStatementsInvariant::MissingFlowStart(declaration),
        )?;
        if self.bound.flow_container(statement) != Some(declaration)
            || self.bound.flow_at(statement) != Some(start)
        {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: statement,
                expected: declaration,
                actual: self.bound.flow_container(statement),
            }
            .into());
        }
        if graph.container_return(declaration).is_some() {
            return Err(
                SourceFunctionStatementsInvariant::UnexpectedReturnFlow(declaration).into(),
            );
        }
        Ok(syntax)
    }

    fn validate_for_of_arrow_callable(&self) -> Result<(), SourceFunctionStatementsError> {
        let declaration = self.callable.declaration;
        let record = self.node(declaration)?;
        let NodeData::ArrowFunction(arrow) = &record.data else {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        };
        let owner = self.store.symbol(self.callable.owner_symbol).ok_or(
            SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration),
        )?;
        if record.kind != SyntaxKind::ArrowFunction
            || self.reference(arrow.body) != self.callable.body
            || arrow.type_.map(|node| self.reference(node)) != self.callable.return_type.type_node()
            || self.bound.symbol(declaration) != Some(self.callable.owner_symbol)
            || owner.flags() != SymbolFlags::FUNCTION
            || owner.check_flags() != CheckFlags::NONE
            || owner.declarations() != Some(&[declaration])
            || owner.value_declaration() != Some(declaration)
            || owner.parent().is_some()
            || self.callable.owner_parent.is_some()
            || self.callable.export_local.is_some()
            || arrow.parameters.nodes.len() != self.callable.parameters.len()
        {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        }
        for (&parameter, planned) in arrow.parameters.nodes.iter().zip(&self.callable.parameters) {
            let parameter = self.reference(parameter);
            let parameter_record = self.node(parameter)?;
            if parameter != planned.declaration
                || parameter_record.kind != SyntaxKind::Parameter
                || parameter_record.parent != Some(declaration.node)
                || self.bound.symbol(parameter) != Some(planned.symbol)
                || !source_parameter_declarations_are_exact(
                    self.store,
                    declaration,
                    parameter,
                    planned.symbol,
                )
            {
                return Err(
                    SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into(),
                );
            }
            self.validate_container(parameter, declaration)?;
        }
        Ok(())
    }

    fn plan_loop(
        &self,
    ) -> Result<SourceLoopFunctionStatementsSyntax, SourceFunctionStatementsError> {
        let declaration = self.callable.declaration;
        if !declaration.is_for(self.arena.id(), self.bound.file_id())
            || self.bound.node_arena_id() != self.arena.id()
            || self.bound.node_arena_revision() != self.arena.revision()
        {
            return Err(SourceFunctionStatementsInvariant::BoundSourceMismatch(declaration).into());
        }
        let record = self.node(declaration)?;
        let valid_callable = match &record.data {
            NodeData::FunctionDeclaration(function) => {
                self.callable.family == SourceCallableFamily::FunctionDeclaration
                    && record.kind == SyntaxKind::FunctionDeclaration
                    && function.body == Some(self.callable.body.node)
                    && function.type_
                        == self
                            .callable
                            .return_type
                            .type_node()
                            .map(|type_node| type_node.node)
            }
            NodeData::FunctionExpression(function) => {
                self.callable.family == SourceCallableFamily::ArrowFunction
                    && record.kind == SyntaxKind::FunctionExpression
                    && function.body == self.callable.body.node
                    && function.name.is_none()
                    && function.parameters.nodes.is_empty()
                    && function.type_.is_none()
            }
            _ => false,
        };
        if !valid_callable {
            return Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into());
        }

        let body = self.callable.body;
        self.validate_range(body, declaration)?;
        let body_statements = self.plan_body(body, declaration)?;
        let Some((&statement, trailing)) = body_statements.split_first() else {
            return Err(self.unsupported(
                body,
                SyntaxKind::Block,
                SourceFunctionStatementsRole::FunctionBody,
            ));
        };
        let mut statement = self.reference(statement);
        let mut parent = body;
        let mut labels = Vec::new();
        while self.node(statement)?.kind == SyntaxKind::LabeledStatement {
            let record = self.node(statement)?;
            let NodeData::LabeledStatement(labeled) = &record.data else {
                return Err(self.unsupported(
                    statement,
                    record.kind,
                    SourceFunctionStatementsRole::BodyStatement,
                ));
            };
            let label = self.reference(labeled.label);
            let child = validate_labeled_statement(self.arena, self.bound, statement, parent)?;
            labels.push(label);
            parent = statement;
            statement = child;
        }
        let kind = self.node(statement)?.kind;
        if !matches!(
            kind,
            SyntaxKind::ForStatement | SyntaxKind::WhileStatement | SyntaxKind::DoStatement
        ) {
            return Err(self.unsupported(
                statement,
                kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }

        let control = plan_source_control_loop_syntax(self.arena, self.bound, statement, parent)?;
        self.validate_block_scope_container(statement, declaration)?;
        let initializers = if control.kind == SourceControlLoopKind::For {
            self.plan_classic_loop_initializers(&control, declaration)?
        } else {
            Vec::new()
        };
        let loop_scope = if control.kind == SourceControlLoopKind::For {
            statement
        } else {
            declaration
        };
        let Some(condition) = control.condition else {
            return Err(self.unsupported(statement, kind, SourceFunctionStatementsRole::Condition));
        };
        self.validate_block_scope_container(condition, loop_scope)?;
        if let Some(incrementor) = control.incrementor {
            self.validate_classic_loop_incrementor(
                incrementor,
                statement,
                declaration,
                &initializers,
            )?;
        }

        let loop_body = self.node(control.body)?;
        let NodeData::Block(block) = &loop_body.data else {
            return Err(self.unsupported(
                control.body,
                loop_body.kind,
                SourceFunctionStatementsRole::BranchBlock,
            ));
        };
        if loop_body.kind != SyntaxKind::Block
            || loop_body.flags.0 != 0
            || loop_body.parent != Some(statement.node)
            || block.flow_node.is_some()
            || block.next_container.is_some()
            || block.statements.has_trailing_comma
            || block.facts != 0
        {
            return Err(self.unsupported(
                control.body,
                loop_body.kind,
                SourceFunctionStatementsRole::BranchBlock,
            ));
        }
        self.validate_range(control.body, statement)?;
        self.validate_container(control.body, declaration)?;
        self.validate_block_scope_container(control.body, loop_scope)?;
        self.validate_node_list(
            control.body,
            block.statements.range,
            &block.statements.nodes,
        )?;

        let mut locals = Vec::new();
        let mut statements = Vec::new();
        for &node in &block.statements.nodes {
            let statement = self.reference(node);
            match self.node(statement)?.kind {
                SyntaxKind::VariableStatement => {
                    let declarations =
                        self.plan_local_statement(statement, control.body, declaration)?;
                    statements.extend(
                        declarations
                            .iter()
                            .copied()
                            .map(SourceLoopFunctionStatementSyntax::Local),
                    );
                    locals.extend(declarations);
                }
                SyntaxKind::ExpressionStatement => {
                    let expression =
                        self.plan_loop_expression_statement(statement, control.body, declaration)?;
                    statements.push(SourceLoopFunctionStatementSyntax::Expression {
                        statement,
                        expression,
                    });
                }
                SyntaxKind::LabeledStatement
                | SyntaxKind::ForStatement
                | SyntaxKind::WhileStatement
                | SyntaxKind::DoStatement => {
                    let nested = self.plan_nested_loop_statement(
                        statement,
                        control.body,
                        declaration,
                        &labels,
                        1,
                    )?;
                    statements.push(SourceLoopFunctionStatementSyntax::Loop(Box::new(nested)));
                }
                SyntaxKind::IfStatement => {
                    statements.push(self.plan_loop_conditional_statement(
                        statement,
                        control.body,
                        declaration,
                        &labels,
                    )?);
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

        let graph = self.bound.flow_graph();
        let start = graph.container_start(declaration).ok_or(
            SourceFunctionStatementsInvariant::MissingFlowStart(declaration),
        )?;
        if self.bound.flow_container(control.statement) != Some(declaration)
            || self.bound.flow_at(control.statement) != Some(start)
        {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: control.statement,
                expected: declaration,
                actual: self.bound.flow_container(control.statement),
            }
            .into());
        }
        if graph.container_return(declaration).is_some() {
            return Err(
                SourceFunctionStatementsInvariant::UnexpectedReturnFlow(declaration).into(),
            );
        }
        if let Some(first) = statements.first() {
            let first = match first {
                SourceLoopFunctionStatementSyntax::Local(local) => local.name,
                SourceLoopFunctionStatementSyntax::Loop(nested) => nested.control.statement,
                SourceLoopFunctionStatementSyntax::Expression { statement, .. }
                | SourceLoopFunctionStatementSyntax::ConditionalJump { statement, .. }
                | SourceLoopFunctionStatementSyntax::ConditionalReturn { statement, .. } => {
                    *statement
                }
            };
            let body_flow = self.bound.flow_at(first).ok_or(
                SourceFunctionStatementsInvariant::InvalidFlowContainer {
                    node: first,
                    expected: declaration,
                    actual: self.bound.flow_container(first),
                },
            )?;
            let entry = graph.nodes().get(body_flow).ok_or(
                SourceFunctionStatementsInvariant::InvalidFlowContainer {
                    node: first,
                    expected: declaration,
                    actual: self.bound.flow_container(first),
                },
            )?;
            let loop_flow = if matches!(
                control.kind,
                SourceControlLoopKind::While | SourceControlLoopKind::For
            ) && joined_semantic_flow_flags(entry.flags)
                == FlowFlags::TRUE_CONDITION.bits()
            {
                if entry.payload != Some(FlowNodePayload::Ast(condition))
                    || !entry.antecedents.is_empty()
                {
                    return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                        node: first,
                        expected: declaration,
                        actual: self.bound.flow_container(first),
                    }
                    .into());
                }
                entry
                    .antecedent
                    .ok_or(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                        node: first,
                        expected: declaration,
                        actual: self.bound.flow_container(first),
                    })?
            } else {
                body_flow
            };
            let loop_entry = graph.nodes().get(loop_flow).ok_or(
                SourceFunctionStatementsInvariant::InvalidFlowContainer {
                    node: first,
                    expected: declaration,
                    actual: self.bound.flow_container(first),
                },
            )?;
            if joined_semantic_flow_flags(loop_entry.flags) != FlowFlags::LOOP_LABEL.bits()
                || loop_entry.payload.is_some()
                || loop_entry.antecedent.is_some()
                || loop_entry.antecedents.len() < 2
                || loop_entry.antecedents[0] == loop_entry.antecedents[1]
            {
                return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                    node: first,
                    expected: declaration,
                    actual: self.bound.flow_container(first),
                }
                .into());
            }
            let mut initializer_flow = loop_entry.antecedents[0];
            for initializer in initializers.iter().rev() {
                let assignment = graph.nodes().get(initializer_flow).ok_or(
                    SourceFunctionStatementsInvariant::InvalidFlowContainer {
                        node: initializer.name,
                        expected: declaration,
                        actual: self.bound.flow_container(initializer.name),
                    },
                )?;
                if joined_semantic_flow_flags(assignment.flags) != FlowFlags::ASSIGNMENT.bits()
                    || assignment.payload != Some(FlowNodePayload::Ast(initializer.declaration))
                    || !assignment.antecedents.is_empty()
                {
                    return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                        node: initializer.name,
                        expected: declaration,
                        actual: self.bound.flow_container(initializer.name),
                    }
                    .into());
                }
                initializer_flow = assignment.antecedent.ok_or(
                    SourceFunctionStatementsInvariant::InvalidFlowContainer {
                        node: initializer.name,
                        expected: declaration,
                        actual: self.bound.flow_container(initializer.name),
                    },
                )?;
            }
            if initializer_flow != start {
                return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                    node: first,
                    expected: declaration,
                    actual: self.bound.flow_container(first),
                }
                .into());
            }
        }
        for local in initializers.iter().chain(&locals) {
            if self.bound.flow_container(local.name) != Some(declaration)
                || self.bound.flow_at(local.name).is_none()
            {
                return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                    node: local.name,
                    expected: declaration,
                    actual: self.bound.flow_container(local.name),
                }
                .into());
            }
        }
        let trailing_statements =
            self.plan_loop_trailing_statements(trailing, body, declaration, &locals)?;

        Ok(SourceLoopFunctionStatementsSyntax {
            body,
            control,
            labels,
            initializers,
            locals,
            statements,
            trailing_statements,
        })
    }

    fn plan_nested_loop_statement(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
        outer_labels: &[NodeRef],
        depth: usize,
    ) -> Result<SourceLoopFunctionStatementsSyntax, SourceFunctionStatementsError> {
        if depth >= MAX_NESTED_CAPTURED_LOOPS {
            return Err(self.unsupported(
                statement,
                self.node(statement)?.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }

        let mut statement = statement;
        let mut expected_parent = parent;
        let mut labels = outer_labels.to_vec();
        while self.node(statement)?.kind == SyntaxKind::LabeledStatement {
            let record = self.node(statement)?;
            let NodeData::LabeledStatement(labeled) = &record.data else {
                return Err(self.unsupported(
                    statement,
                    record.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            };
            let label = self.reference(labeled.label);
            let child =
                validate_labeled_statement(self.arena, self.bound, statement, expected_parent)?;
            labels.push(label);
            expected_parent = statement;
            statement = child;
        }

        let kind = self.node(statement)?.kind;
        if !matches!(
            kind,
            SyntaxKind::ForStatement | SyntaxKind::WhileStatement | SyntaxKind::DoStatement
        ) {
            return Err(self.unsupported(
                statement,
                kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }
        let control =
            plan_source_control_loop_syntax(self.arena, self.bound, statement, expected_parent)?;
        self.validate_block_scope_container(statement, parent)?;
        let initializers = if control.kind == SourceControlLoopKind::For {
            self.plan_classic_loop_initializers(&control, callable)?
        } else {
            Vec::new()
        };
        let loop_scope = if control.kind == SourceControlLoopKind::For {
            statement
        } else {
            parent
        };
        let condition = control.condition.ok_or_else(|| {
            self.unsupported(statement, kind, SourceFunctionStatementsRole::Condition)
        })?;
        self.validate_block_scope_container(condition, loop_scope)?;
        if let Some(incrementor) = control.incrementor {
            self.validate_classic_loop_incrementor(
                incrementor,
                statement,
                callable,
                &initializers,
            )?;
        }

        let record = self.node(control.body)?;
        let NodeData::Block(block) = &record.data else {
            return Err(self.unsupported(
                control.body,
                record.kind,
                SourceFunctionStatementsRole::BranchBlock,
            ));
        };
        if record.kind != SyntaxKind::Block
            || record.flags.0 != 0
            || record.parent != Some(statement.node)
            || block.flow_node.is_some()
            || block.next_container.is_some()
            || block.statements.has_trailing_comma
            || block.facts != 0
        {
            return Err(self.unsupported(
                control.body,
                record.kind,
                SourceFunctionStatementsRole::BranchBlock,
            ));
        }
        self.validate_range(control.body, statement)?;
        self.validate_container(control.body, callable)?;
        self.validate_block_scope_container(control.body, loop_scope)?;
        self.validate_node_list(
            control.body,
            block.statements.range,
            &block.statements.nodes,
        )?;

        let mut locals = Vec::new();
        let mut statements = Vec::new();
        for node in &block.statements.nodes {
            let statement = self.reference(*node);
            match self.node(statement)?.kind {
                SyntaxKind::VariableStatement => {
                    let declarations =
                        self.plan_local_statement(statement, control.body, callable)?;
                    statements.extend(
                        declarations
                            .iter()
                            .copied()
                            .map(SourceLoopFunctionStatementSyntax::Local),
                    );
                    locals.extend(declarations);
                }
                SyntaxKind::ExpressionStatement => {
                    let expression =
                        self.plan_loop_expression_statement(statement, control.body, callable)?;
                    statements.push(SourceLoopFunctionStatementSyntax::Expression {
                        statement,
                        expression,
                    });
                }
                SyntaxKind::LabeledStatement
                | SyntaxKind::ForStatement
                | SyntaxKind::WhileStatement
                | SyntaxKind::DoStatement => {
                    let nested = self.plan_nested_loop_statement(
                        statement,
                        control.body,
                        callable,
                        &labels,
                        depth + 1,
                    )?;
                    statements.push(SourceLoopFunctionStatementSyntax::Loop(Box::new(nested)));
                }
                SyntaxKind::IfStatement => {
                    statements.push(self.plan_loop_conditional_statement(
                        statement,
                        control.body,
                        callable,
                        &labels,
                    )?);
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

        if self.bound.flow_container(control.statement) != Some(callable)
            || self.bound.flow_at(control.statement).is_none()
        {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: control.statement,
                expected: callable,
                actual: self.bound.flow_container(control.statement),
            }
            .into());
        }
        for local in initializers.iter().chain(&locals) {
            if self.bound.flow_container(local.name) != Some(callable)
                || self.bound.flow_at(local.name).is_none()
            {
                return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                    node: local.name,
                    expected: callable,
                    actual: self.bound.flow_container(local.name),
                }
                .into());
            }
        }

        Ok(SourceLoopFunctionStatementsSyntax {
            body: self.callable.body,
            control,
            labels,
            initializers,
            locals,
            statements,
            trailing_statements: Vec::new(),
        })
    }

    fn plan_loop_conditional_statement(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
        labels: &[NodeRef],
    ) -> Result<SourceLoopFunctionStatementSyntax, SourceFunctionStatementsError> {
        let control = plan_source_control_if_syntax(self.arena, self.bound, statement, parent)?;
        if control.else_statement.is_some() || !control.nested_export_diagnostics.is_empty() {
            return Err(self.unsupported(
                statement,
                SyntaxKind::IfStatement,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }

        let branch = self.node(control.then_statement)?;
        let (returned, scope) = if let NodeData::Block(block) = &branch.data {
            let [returned] = block.statements.nodes.as_slice() else {
                return Err(self.unsupported(
                    control.then_statement,
                    branch.kind,
                    SourceFunctionStatementsRole::BranchBlock,
                ));
            };
            (self.reference(*returned), control.then_statement)
        } else {
            (control.then_statement, parent)
        };

        if self.node(returned)?.kind != SyntaxKind::ReturnStatement {
            let (condition, jump) =
                self.plan_loop_conditional_jump(statement, parent, callable, labels)?;
            return Ok(SourceLoopFunctionStatementSyntax::ConditionalJump {
                statement,
                condition,
                jump,
            });
        }

        self.validate_block_scope_container(statement, parent)?;
        self.validate_block_scope_container(control.condition, parent)?;
        if scope != parent {
            let record = self.node(scope)?;
            let NodeData::Block(block) = &record.data else {
                return Err(self.unsupported(
                    scope,
                    record.kind,
                    SourceFunctionStatementsRole::BranchBlock,
                ));
            };
            if record.kind != SyntaxKind::Block
                || record.flags.0 != 0
                || record.parent != Some(statement.node)
                || block.flow_node.is_some()
                || block.next_container.is_some()
                || block.statements.has_trailing_comma
                || block.facts != 0
            {
                return Err(self.unsupported(
                    scope,
                    record.kind,
                    SourceFunctionStatementsRole::BranchBlock,
                ));
            }
            self.validate_range(scope, statement)?;
            self.validate_container(scope, callable)?;
            self.validate_block_scope_container(scope, parent)?;
            self.validate_node_list(scope, block.statements.range, &block.statements.nodes)?;
        }

        let record = self.node(returned)?;
        let NodeData::ReturnStatement(value) = &record.data else {
            return Err(self.unsupported(
                returned,
                record.kind,
                SourceFunctionStatementsRole::ReturnStatement,
            ));
        };
        let expected_parent = if scope == parent { statement } else { scope };
        if record.flags.0 != 0
            || record.parent != Some(expected_parent.node)
            || value.flow_node.is_some()
            || value.facts != 0
        {
            return Err(self.unsupported(
                returned,
                record.kind,
                SourceFunctionStatementsRole::ReturnStatement,
            ));
        }
        self.validate_range(returned, expected_parent)?;
        self.validate_container(returned, callable)?;
        self.validate_block_scope_container(returned, scope)?;
        if self.bound.flow_container(returned) != Some(callable)
            || self.bound.flow_at(returned).is_none()
        {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: returned,
                expected: callable,
                actual: self.bound.flow_container(returned),
            }
            .into());
        }

        let expression = value.expression.map(|node| self.reference(node));
        if let Some(expression) = expression {
            self.validate_parent(
                expression,
                Some(returned.node),
                SourceFunctionStatementsRole::ReturnExpression,
            )?;
            self.validate_range(expression, returned)?;
            self.validate_container(expression, callable)?;
            self.validate_block_scope_container(expression, scope)?;
        }

        Ok(SourceLoopFunctionStatementSyntax::ConditionalReturn {
            statement,
            condition: control.condition,
            returned,
            expression,
        })
    }

    fn plan_loop_trailing_statements(
        &self,
        trailing: &[NodeId],
        body: NodeRef,
        callable: NodeRef,
        locals: &[SourceLocalDeclarationSyntax],
    ) -> Result<Vec<SourceForInBodyStatementSyntax>, SourceFunctionStatementsError> {
        if trailing.is_empty() {
            return Ok(Vec::new());
        }
        if !locals
            .iter()
            .any(|local| local.binding == VariableBindingKind::Var)
        {
            return Err(self.unsupported(
                body,
                SyntaxKind::Block,
                SourceFunctionStatementsRole::FunctionBody,
            ));
        }

        let mut statements = Vec::with_capacity(trailing.len());
        for statement in trailing {
            let statement = self.reference(*statement);
            let expression =
                self.plan_linear_expression_statement(statement, body, callable, false)?;
            if self.bound.flow_container(statement) != Some(callable)
                || self.bound.flow_at(statement).is_none()
            {
                return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                    node: statement,
                    expected: callable,
                    actual: self.bound.flow_container(statement),
                }
                .into());
            }
            statements.push(SourceForInBodyStatementSyntax {
                statement,
                expression,
            });
        }
        Ok(statements)
    }

    fn plan_loop_conditional_jump(
        &self,
        statement: NodeRef,
        parent: NodeRef,
        callable: NodeRef,
        labels: &[NodeRef],
    ) -> Result<(NodeRef, NodeRef), SourceFunctionStatementsError> {
        let control = plan_source_control_if_syntax(self.arena, self.bound, statement, parent)?;
        if control.else_statement.is_some() || !control.nested_export_diagnostics.is_empty() {
            return Err(self.unsupported(
                statement,
                SyntaxKind::IfStatement,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }
        self.validate_block_scope_container(statement, parent)?;
        self.validate_block_scope_container(control.condition, parent)?;

        let branch = self.node(control.then_statement)?;
        let (jump, scope) = if let NodeData::Block(block) = &branch.data {
            let [jump] = block.statements.nodes.as_slice() else {
                return Err(self.unsupported(
                    control.then_statement,
                    branch.kind,
                    SourceFunctionStatementsRole::BranchBlock,
                ));
            };
            if branch.kind != SyntaxKind::Block
                || branch.flags.0 != 0
                || branch.parent != Some(statement.node)
                || block.flow_node.is_some()
                || block.next_container.is_some()
                || block.statements.has_trailing_comma
                || block.facts != 0
            {
                return Err(self.unsupported(
                    control.then_statement,
                    branch.kind,
                    SourceFunctionStatementsRole::BranchBlock,
                ));
            }
            self.validate_range(control.then_statement, statement)?;
            self.validate_container(control.then_statement, callable)?;
            self.validate_block_scope_container(control.then_statement, parent)?;
            self.validate_node_list(
                control.then_statement,
                block.statements.range,
                &block.statements.nodes,
            )?;
            (self.reference(*jump), control.then_statement)
        } else {
            (control.then_statement, parent)
        };
        let record = self.node(jump)?;
        let (label, flow_node) = match &record.data {
            NodeData::BreakStatement(data) if record.kind == SyntaxKind::BreakStatement => {
                (data.label, data.flow_node)
            }
            NodeData::ContinueStatement(data) if record.kind == SyntaxKind::ContinueStatement => {
                (data.label, data.flow_node)
            }
            _ => {
                return Err(self.unsupported(
                    jump,
                    record.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            }
        };
        let expected_parent = if scope == parent { statement } else { scope };
        if record.flags.0 != 0 || record.parent != Some(expected_parent.node) || flow_node.is_some()
        {
            return Err(self.unsupported(
                jump,
                record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }
        self.validate_range(jump, expected_parent)?;
        self.validate_container(jump, callable)?;
        self.validate_block_scope_container(jump, scope)?;
        if let Some(label) = label {
            let label = self.reference(label);
            let label_record = self.node(label)?;
            let NodeData::Identifier(identifier) = &label_record.data else {
                return Err(self.unsupported(
                    label,
                    label_record.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            };
            if label_record.kind != SyntaxKind::Identifier
                || label_record.flags.0 != 0
                || label_record.parent != Some(jump.node)
                || identifier.flow_node.is_some()
                || identifier.text.is_empty()
                || !labels.iter().any(|candidate| {
                    self.node(*candidate).is_ok_and(|candidate| {
                        matches!(
                            &candidate.data,
                            NodeData::Identifier(name) if name.text == identifier.text
                        )
                    })
                })
            {
                return Err(self.unsupported(
                    label,
                    label_record.kind,
                    SourceFunctionStatementsRole::BranchStatement,
                ));
            }
            self.validate_range(label, jump)?;
            self.validate_container(label, callable)?;
            self.validate_block_scope_container(label, scope)?;
        }
        if self.bound.flow_container(jump) != Some(callable) || self.bound.flow_at(jump).is_none() {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: jump,
                expected: callable,
                actual: self.bound.flow_container(jump),
            }
            .into());
        }
        Ok((control.condition, jump))
    }

    fn plan_classic_loop_initializers(
        &self,
        control: &SourceControlLoopSyntax,
        callable: NodeRef,
    ) -> Result<Vec<SourceLocalDeclarationSyntax>, SourceFunctionStatementsError> {
        let list = control
            .initializer
            .ok_or(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::Syntax {
                    node: control.statement,
                    kind: SyntaxKind::ForStatement,
                    role: SourceFunctionStatementsRole::LocalDeclarationList,
                },
            ))?;
        let record = self.node(list)?;
        let NodeData::VariableDeclarationList(data) = &record.data else {
            return Err(self.unsupported(
                list,
                record.kind,
                SourceFunctionStatementsRole::LocalDeclarationList,
            ));
        };
        let binding = match record.flags.0 {
            NODE_FLAG_LET => VariableBindingKind::Let,
            NODE_FLAG_CONST => VariableBindingKind::Const,
            _ => {
                return Err(SourceFunctionStatementsError::Unsupported(
                    SourceFunctionStatementsUnsupported::BindingKind(list),
                ));
            }
        };
        if record.kind != SyntaxKind::VariableDeclarationList
            || record.parent != Some(control.statement.node)
            || data.declarations.has_trailing_comma
            || data.declarations.nodes.is_empty()
            || data.declarations.range.start <= record.range.start
            || data.declarations.range.end != record.range.end
            || data.facts != 0
        {
            return Err(self.unsupported(
                list,
                record.kind,
                SourceFunctionStatementsRole::LocalDeclarationList,
            ));
        }
        self.validate_range(list, control.statement)?;
        self.validate_container(list, callable)?;
        self.validate_block_scope_container(list, control.statement)?;
        self.validate_node_list(list, data.declarations.range, &data.declarations.nodes)?;

        data.declarations
            .nodes
            .iter()
            .map(|declaration| {
                self.plan_local_declaration(
                    control.statement,
                    list,
                    self.reference(*declaration),
                    callable,
                    control.statement,
                    binding,
                    false,
                )
            })
            .collect()
    }

    fn validate_classic_loop_incrementor(
        &self,
        incrementor: NodeRef,
        statement: NodeRef,
        callable: NodeRef,
        initializers: &[SourceLocalDeclarationSyntax],
    ) -> Result<(), SourceFunctionStatementsError> {
        let record = self.node(incrementor)?;
        let (operand, operator) = match &record.data {
            NodeData::PrefixUnaryExpression(data)
                if record.kind == SyntaxKind::PrefixUnaryExpression =>
            {
                (self.reference(data.operand), data.operator)
            }
            NodeData::PostfixUnaryExpression(data)
                if record.kind == SyntaxKind::PostfixUnaryExpression =>
            {
                (self.reference(data.operand), data.operator)
            }
            _ => {
                return Err(self.unsupported(
                    incrementor,
                    record.kind,
                    SourceFunctionStatementsRole::BodyStatement,
                ));
            }
        };
        if record.flags.0 != 0
            || record.parent != Some(statement.node)
            || !matches!(
                operator,
                SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken
            )
        {
            return Err(self.unsupported(
                incrementor,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        }
        self.validate_range(incrementor, statement)?;
        self.validate_container(incrementor, callable)?;
        self.validate_block_scope_container(incrementor, statement)?;

        let operand_record = self.node(operand)?;
        let NodeData::Identifier(identifier) = &operand_record.data else {
            return Err(self.unsupported(
                operand,
                operand_record.kind,
                SourceFunctionStatementsRole::LocalName,
            ));
        };
        if operand_record.kind != SyntaxKind::Identifier
            || operand_record.flags.0 != 0
            || operand_record.parent != Some(incrementor.node)
            || identifier.text.is_empty()
            || identifier.flow_node.is_some()
        {
            return Err(self.unsupported(
                operand,
                operand_record.kind,
                SourceFunctionStatementsRole::LocalName,
            ));
        }
        self.validate_range(operand, incrementor)?;
        self.validate_container(operand, callable)?;
        self.validate_block_scope_container(operand, statement)?;
        let symbol = self
            .bound
            .locals(statement)
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&identifier.text));
        if !initializers.iter().any(|initializer| {
            Some(initializer.symbol) == symbol && initializer.binding == VariableBindingKind::Let
        }) {
            return Err(self.unsupported(
                operand,
                operand_record.kind,
                SourceFunctionStatementsRole::LocalName,
            ));
        }
        Ok(())
    }

    fn plan_loop_expression_statement(
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
                SourceFunctionStatementsRole::BranchStatement,
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
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }
        self.validate_range(statement, parent)?;
        self.validate_container(statement, callable)?;
        self.validate_block_scope_container(statement, parent)?;

        let expression = self.reference(data.expression);
        let expression_record = self.node(expression)?;
        if expression_record.flags.0 != 0 {
            return Err(self.unsupported(
                expression,
                expression_record.kind,
                SourceFunctionStatementsRole::BranchStatement,
            ));
        }
        self.validate_parent(
            expression,
            Some(statement.node),
            SourceFunctionStatementsRole::BranchStatement,
        )?;
        self.validate_range(expression, statement)?;
        self.validate_container(expression, callable)?;
        self.validate_block_scope_container(expression, parent)?;

        if self.bound.flow_container(statement) != Some(callable)
            || self.bound.flow_at(statement).is_none()
        {
            return Err(SourceFunctionStatementsInvariant::InvalidFlowContainer {
                node: statement,
                expected: callable,
                actual: self.bound.flow_container(statement),
            }
            .into());
        }
        Ok(expression)
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
        allow_logical: bool,
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
                let immediate_async_arrow = match &callee_record.data {
                    NodeData::ParenthesizedExpression(parenthesized)
                        if callee_record.kind == SyntaxKind::ParenthesizedExpression
                            && call.arguments.nodes.is_empty()
                            && !call.arguments.has_trailing_comma
                            && call.type_arguments.is_none() =>
                    {
                        let arrow = self.reference(parenthesized.expression);
                        let arrow_record = self.node(arrow)?;
                        matches!(
                            &arrow_record.data,
                            NodeData::ArrowFunction(function)
                                if arrow_record.kind == SyntaxKind::ArrowFunction
                                    && arrow_record.flags.0 == 0
                                    && arrow_record.parent == Some(callee.node)
                                    && function.parameters.nodes.is_empty()
                                    && !function.parameters.has_trailing_comma
                                    && function.type_parameters.is_none()
                                    && function.type_.is_none()
                                    && function.modifiers.as_ref().is_some_and(|modifiers| {
                                        matches!(modifiers.list.nodes.as_slice(), [modifier]
                                            if self.arena.get(*modifier).is_some_and(|record| {
                                                record.kind == SyntaxKind::AsyncKeyword
                                                    && record.flags.0 == 0
                                                    && record.parent == Some(arrow.node)
                                                    && matches!(record.data, NodeData::Token(_))
                                            }))
                                    })
                        )
                    }
                    _ => false,
                };
                if !matches!(
                    callee_record.kind,
                    SyntaxKind::Identifier | SyntaxKind::PropertyAccessExpression
                ) && !immediate_async_arrow
                    && !super::source_calls::is_immediately_invoked_source_callable(
                        self.arena, expression,
                    )
                    || callee_record.flags.0 != 0
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
                if allow_logical
                    && self.node(self.reference(binary.operator_token))?.kind
                        == SyntaxKind::AmpersandAmpersandToken
                {
                    plan_source_linear_logical_statement_syntax(
                        self.arena, self.bound, statement, callable,
                    )?;
                } else {
                    self.validate_linear_assignment_expression(expression, callable)?;
                }
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

    fn plan_linear_throw(
        &self,
        statement: NodeRef,
        body: NodeRef,
        callable: NodeRef,
    ) -> Result<NodeRef, SourceFunctionStatementsError> {
        let record = self.node(statement)?;
        let NodeData::ThrowStatement(thrown) = &record.data else {
            return Err(self.unsupported(
                statement,
                record.kind,
                SourceFunctionStatementsRole::BodyStatement,
            ));
        };
        if record.kind != SyntaxKind::ThrowStatement
            || record.flags.0 != 0
            || record.parent != Some(body.node)
            || thrown.flow_node.is_some()
            || thrown.facts != 0
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
        let expression = self.reference(thrown.expression);
        self.validate_parent(
            expression,
            Some(statement.node),
            SourceFunctionStatementsRole::BodyStatement,
        )?;
        self.validate_range(expression, statement)?;
        self.validate_container(expression, callable)?;
        self.validate_block_scope_container(expression, callable)?;
        Ok(expression)
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
        if let Some(scope) = self.statement_scope {
            return Ok(scope);
        }
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

    fn is_function_owned_loop_body(
        &self,
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<bool, SourceFunctionStatementsError> {
        let block = self.node(parent)?;
        if block.kind != SyntaxKind::Block {
            return Ok(false);
        }
        let Some(iteration) = block.parent.map(|node| self.reference(node)) else {
            return Ok(false);
        };
        Ok(matches!(
            self.node(iteration)?.kind,
            SyntaxKind::ForStatement
                | SyntaxKind::ForInStatement
                | SyntaxKind::ForOfStatement
                | SyntaxKind::WhileStatement
                | SyntaxKind::DoStatement
        ) && self.bound.container(iteration) == Some(callable)
            && self.bound.container(parent) == Some(callable))
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
        let Some(if_index) = statements.iter().position(|statement| {
            self.arena
                .get(*statement)
                .is_some_and(|record| record.kind == SyntaxKind::IfStatement)
        }) else {
            return Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::MissingFinalIf(body),
            ));
        };

        let (leading, leading_statements) =
            self.plan_return_prefix(&statements[..if_index], body, declaration)?;

        let final_if = self.plan_final_if(
            self.reference(statements[if_index]),
            body,
            declaration,
            &statements[if_index + 1..],
        )?;
        self.validate_flow(&final_if)?;

        Ok(SourceFunctionStatementsSyntax {
            body,
            leading,
            leading_statements,
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
        let loop_body = self.is_function_owned_loop_body(parent, callable)?;
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
            0 if self.is_straight_line_variable_parent(parent)? || loop_body => {
                VariableBindingKind::Var
            }
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
                loop_body,
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
        allow_uninitialized: bool,
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
        let initializer = variable.initializer.map(|node| self.reference(node));
        match initializer {
            Some(initializer) => {
                self.validate_parent(
                    initializer,
                    Some(declaration.node),
                    SourceFunctionStatementsRole::LocalInitializer,
                )?;
                self.validate_range(initializer, declaration)?;
                self.validate_order(type_node.unwrap_or(name), initializer)?;
                self.validate_container(initializer, callable)?;
                self.validate_block_scope_container(initializer, expected_scope)?;
            }
            None if binding.is_const() || !allow_uninitialized && type_node.is_none() => {
                return Err(SourceFunctionStatementsError::Unsupported(
                    SourceFunctionStatementsUnsupported::MissingInitializer(declaration),
                ));
            }
            None => {}
        }

        self.validate_container(declaration, callable)?;
        self.validate_block_scope_container(declaration, expected_scope)?;
        let parameter = self.callable.parameters.iter().find(|parameter| {
            binding == VariableBindingKind::Var
                && self.bound.symbol(declaration) == Some(parameter.symbol)
                && source_parameter_declarations_are_exact(
                    self.store,
                    callable,
                    parameter.declaration,
                    parameter.symbol,
                )
        });
        let symbol = if let Some(parameter) = parameter {
            if self.bound.local_symbol(declaration).is_some()
                || self
                    .store
                    .symbol(parameter.symbol)
                    .is_none_or(|symbol| symbol.name().as_utf8() != Some(name_text.as_str()))
            {
                return Err(
                    SourceFunctionStatementsInvariant::InvalidCallableEdge(declaration).into(),
                );
            }
            parameter.symbol
        } else {
            plan_top_level_variable(
                self.bound,
                self.store,
                declaration,
                name,
                &name_text,
                binding,
                false,
            )?
        };
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
        trailing: &[NodeId],
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
        let condition_syntax = match self.plan_condition(condition, callable) {
            Ok(condition) => Some(condition),
            Err(error @ SourceFunctionStatementsError::Unsupported(_))
                if self.condition_requires_narrowing(condition)? =>
            {
                return Err(error);
            }
            Err(SourceFunctionStatementsError::Unsupported(_)) => None,
            Err(error) => return Err(error),
        };

        let then_block = control.then_statement;
        self.validate_range(then_block, statement)?;
        self.validate_order(condition, then_block)?;
        let then_branch = self.plan_branch(then_block, statement, callable)?;
        let else_branch = match (control.else_statement, trailing) {
            (Some(else_block), []) => {
                self.validate_range(else_block, statement)?;
                self.validate_order(then_block, else_block)?;
                self.plan_branch(else_block, statement, callable)?
            }
            (None, [first, ..]) => {
                self.validate_order(statement, self.reference(*first))?;
                self.plan_return_sequence(trailing, body, callable)?
            }
            _ => {
                return Err(SourceFunctionStatementsError::Unsupported(
                    SourceFunctionStatementsUnsupported::MissingElse(statement),
                ));
            }
        };

        Ok(SourceFinalIfSyntax {
            statement,
            condition,
            condition_identifier: condition_syntax.map(|condition| condition.identifier),
            typeof_condition: condition_syntax.and_then(|condition| condition.typeof_condition),
            equality_condition: condition_syntax.and_then(|condition| condition.equality_condition),
            then_branch,
            else_branch,
        })
    }

    fn condition_requires_narrowing(
        &self,
        condition: NodeRef,
    ) -> Result<bool, SourceFunctionStatementsError> {
        match &self.node(condition)?.data {
            NodeData::ParenthesizedExpression(parenthesized) => {
                self.condition_requires_narrowing(self.reference(parenthesized.expression))
            }
            NodeData::BinaryExpression(binary) => Ok(matches!(
                self.node(self.reference(binary.operator_token))?.kind,
                SyntaxKind::EqualsEqualsToken
                    | SyntaxKind::ExclamationEqualsToken
                    | SyntaxKind::EqualsEqualsEqualsToken
                    | SyntaxKind::ExclamationEqualsEqualsToken
                    | SyntaxKind::InKeyword
                    | SyntaxKind::InstanceOfKeyword
            )),
            _ => Ok(false),
        }
    }

    fn plan_condition(
        &self,
        condition: NodeRef,
        callable: NodeRef,
    ) -> Result<PlannedConditionSyntax, SourceFunctionStatementsError> {
        if self.node(condition)?.kind == SyntaxKind::BinaryExpression {
            let record = self.node(condition)?;
            let NodeData::BinaryExpression(binary) = &record.data else {
                return Err(self.unsupported(
                    condition,
                    record.kind,
                    SourceFunctionStatementsRole::Condition,
                ));
            };
            let left = self.node(self.reference(binary.left))?.kind;
            let right = self.node(self.reference(binary.right))?.kind;
            return if matches!(left, SyntaxKind::TypeOfExpression)
                || matches!(right, SyntaxKind::TypeOfExpression)
            {
                self.plan_typeof_condition(condition, callable)
            } else {
                self.plan_equality_condition(condition, callable)
            };
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
                        equality_condition: None,
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
            equality_condition: None,
        })
    }

    fn plan_equality_condition(
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
        for node in [left, operator, right] {
            self.validate_parent(
                node,
                Some(condition.node),
                SourceFunctionStatementsRole::Condition,
            )?;
            self.validate_range(node, condition)?;
            self.validate_container(node, callable)?;
            self.validate_block_scope_container(node, callable)?;
        }
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
        let (comparison, strict) = match operator_record.kind {
            SyntaxKind::EqualsEqualsEqualsToken => (SourceTypeofComparison::Equal, true),
            SyntaxKind::ExclamationEqualsEqualsToken => (SourceTypeofComparison::NotEqual, true),
            SyntaxKind::EqualsEqualsToken => (SourceTypeofComparison::Equal, false),
            SyntaxKind::ExclamationEqualsToken => (SourceTypeofComparison::NotEqual, false),
            _ => {
                return Err(self.unsupported(
                    operator,
                    operator_record.kind,
                    SourceFunctionStatementsRole::Condition,
                ));
            }
        };

        let left_value = self.equality_condition_value(left)?;
        let right_value = self.equality_condition_value(right)?;
        let (operand, value, operand_on_left) = match (left_value, right_value) {
            (false, true) => (left, right, true),
            (true, false) => (right, left, false),
            _ => {
                return Err(self.unsupported(
                    condition,
                    record.kind,
                    SourceFunctionStatementsRole::Condition,
                ));
            }
        };
        if !strict
            && !matches!(
                self.node(value)?.kind,
                SyntaxKind::NullKeyword | SyntaxKind::Identifier
            )
        {
            return Err(self.unsupported(
                operator,
                operator_record.kind,
                SourceFunctionStatementsRole::Condition,
            ));
        }

        let operand_record = self.node(operand)?;
        let (identifier, discriminant) = match &operand_record.data {
            NodeData::Identifier(identifier)
                if operand_record.kind == SyntaxKind::Identifier
                    && operand_record.flags.0 == 0
                    && identifier.flow_node.is_none()
                    && !identifier.text.is_empty() =>
            {
                (operand, None)
            }
            NodeData::PropertyAccessExpression(access)
                if operand_record.kind == SyntaxKind::PropertyAccessExpression
                    && operand_record.flags.0 == 0
                    && access.flow_node.is_none()
                    && access.question_dot_token.is_none()
                    && access.facts == 0 =>
            {
                let identifier = self.reference(access.expression);
                let name = self.reference(access.name);
                for node in [identifier, name] {
                    self.validate_parent(
                        node,
                        Some(operand.node),
                        SourceFunctionStatementsRole::Condition,
                    )?;
                    self.validate_range(node, operand)?;
                    self.validate_container(node, callable)?;
                    self.validate_block_scope_container(node, callable)?;
                }
                self.validate_order(identifier, name)?;
                let identifier_record = self.node(identifier)?;
                let name_record = self.node(name)?;
                if !matches!(&identifier_record.data, NodeData::Identifier(identifier)
                    if identifier_record.kind == SyntaxKind::Identifier
                        && identifier_record.flags.0 == 0
                        && identifier.flow_node.is_none()
                        && !identifier.text.is_empty())
                    || !matches!(&name_record.data, NodeData::Identifier(name)
                        if name_record.kind == SyntaxKind::Identifier
                            && name_record.flags.0 == 0
                            && name.flow_node.is_none()
                            && !name.text.is_empty())
                {
                    return Err(self.unsupported(
                        operand,
                        operand_record.kind,
                        SourceFunctionStatementsRole::Condition,
                    ));
                }
                (identifier, Some(operand))
            }
            _ => {
                return Err(self.unsupported(
                    operand,
                    operand_record.kind,
                    SourceFunctionStatementsRole::Condition,
                ));
            }
        };

        Ok(PlannedConditionSyntax {
            identifier,
            typeof_condition: None,
            equality_condition: Some(SourceEqualityConditionSyntax {
                operand,
                identifier,
                discriminant,
                operator,
                value,
                comparison,
                strict,
                operand_on_left,
            }),
        })
    }

    fn equality_condition_value(
        &self,
        value: NodeRef,
    ) -> Result<bool, SourceFunctionStatementsError> {
        let record = self.node(value)?;
        if record.flags.0 != 0 {
            return Ok(false);
        }
        Ok(match &record.data {
            NodeData::Identifier(identifier) => {
                record.kind == SyntaxKind::Identifier
                    && identifier.flow_node.is_none()
                    && identifier.text == "undefined"
            }
            NodeData::KeywordExpression(keyword) => {
                matches!(
                    record.kind,
                    SyntaxKind::NullKeyword | SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword
                ) && keyword.flow_node.is_none()
            }
            NodeData::StringLiteral(literal) => {
                record.kind == SyntaxKind::StringLiteral && literal.token_flags.0 == 0
            }
            NodeData::NoSubstitutionTemplateLiteral(literal) => {
                record.kind == SyntaxKind::NoSubstitutionTemplateLiteral
                    && literal.token_flags.0 == 0
                    && literal.template_flags.0 == 0
            }
            NodeData::NumericLiteral(literal) => {
                record.kind == SyntaxKind::NumericLiteral && literal.token_flags.0 == 0
            }
            NodeData::BigIntLiteral(literal) => {
                record.kind == SyntaxKind::BigIntLiteral && literal.token_flags.0 == 0
            }
            _ => false,
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
                statements: Vec::new(),
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

        self.plan_return_sequence(&block_data.statements.nodes, block, callable)
    }

    fn plan_return_sequence(
        &self,
        statements: &[NodeId],
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<SourceReturnBranchSyntax, SourceFunctionStatementsError> {
        let Some((&return_id, local_statement_ids)) = statements.split_last() else {
            return Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::MissingReturn(parent),
            ));
        };
        let (locals, statements) =
            self.plan_return_prefix(local_statement_ids, parent, callable)?;

        let return_statement = self.reference(return_id);
        let return_record = self.node(return_statement)?;
        let NodeData::ReturnStatement(return_data) = &return_record.data else {
            return Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::MissingReturn(return_statement),
            ));
        };
        if return_record.kind != SyntaxKind::ReturnStatement
            || return_record.flags.0 != 0
            || return_record.parent != Some(parent.node)
            || return_data.flow_node.is_some()
            || return_data.facts != 0
        {
            return Err(self.unsupported(
                return_statement,
                return_record.kind,
                SourceFunctionStatementsRole::ReturnStatement,
            ));
        }
        self.validate_range(return_statement, parent)?;
        self.validate_container(return_statement, callable)?;
        let scope = self.statement_lexical_scope(parent, callable)?;
        self.validate_block_scope_container(return_statement, scope)?;
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
        self.validate_block_scope_container(return_expression, scope)?;

        Ok(SourceReturnBranchSyntax {
            block: Some(parent),
            locals,
            statements,
            return_statement,
            return_expression,
        })
    }

    fn plan_return_prefix(
        &self,
        nodes: &[NodeId],
        parent: NodeRef,
        callable: NodeRef,
    ) -> Result<
        (
            Vec<SourceLocalDeclarationSyntax>,
            Vec<SourceLinearFunctionStatementSyntax>,
        ),
        SourceFunctionStatementsError,
    > {
        let mut locals = Vec::new();
        let mut statements = Vec::new();
        for &node in nodes {
            let statement = self.reference(node);
            if self.node(statement)?.kind == SyntaxKind::ExpressionStatement {
                let expression = if parent == self.callable.body {
                    self.plan_linear_expression_statement(statement, parent, callable, false)?
                } else {
                    self.plan_loop_expression_statement(statement, parent, callable)?
                };
                statements.push(SourceLinearFunctionStatementSyntax::Expression {
                    statement,
                    expression,
                });
            } else {
                for local in self.plan_local_or_block_statement(statement, parent, callable)? {
                    locals.push(local);
                    statements.push(SourceLinearFunctionStatementSyntax::Local(local));
                }
            }
        }
        Ok((locals, statements))
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
        let expected = if expected == self.callable.declaration {
            self.statement_scope.unwrap_or(expected)
        } else {
            expected
        };
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

        let (leading, leading_statements) =
            self.plan_return_prefix(&preceding[..if_index], body, declaration)?;
        let joined_if =
            self.plan_joined_if(self.reference(preceding[if_index]), body, declaration)?;
        let (trailing, trailing_statements) =
            self.plan_return_prefix(&preceding[if_index + 1..], body, declaration)?;
        let return_expression = self.plan_joined_return(return_statement, body, declaration)?;

        let syntax = SourceJoinedFunctionStatementsSyntax {
            body,
            leading,
            leading_statements,
            joined_if,
            trailing,
            trailing_statements,
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
        let condition_syntax = match self.plan_condition(condition, callable) {
            Ok(condition) => Some(condition),
            Err(error @ SourceFunctionStatementsError::Unsupported(_))
                if self.condition_requires_narrowing(condition)? =>
            {
                return Err(error.into());
            }
            Err(SourceFunctionStatementsError::Unsupported(_)) => None,
            Err(error) => return Err(error.into()),
        };

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
                statements: Vec::new(),
            }
        };

        Ok(SourceJoinedIfSyntax {
            statement,
            condition,
            condition_identifier: condition_syntax.map_or(condition, |syntax| syntax.identifier),
            typeof_condition: condition_syntax.and_then(|syntax| syntax.typeof_condition),
            equality_condition: condition_syntax.and_then(|syntax| syntax.equality_condition),
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

        let (locals, statements) =
            self.plan_return_prefix(&block_data.statements.nodes, block, callable)?;
        Ok(SourceFallthroughBranchSyntax {
            block: Some(block),
            locals,
            statements,
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

        // Calls and general conditions are validated by the shared source flow plan.
        if syntax
            .leading_statements
            .iter()
            .chain(&syntax.joined_if.then_branch.statements)
            .chain(&syntax.joined_if.else_branch.statements)
            .chain(&syntax.trailing_statements)
            .any(|statement| !matches!(statement, SourceLinearFunctionStatementSyntax::Local(_)))
            || syntax.joined_if.typeof_condition.is_none()
                && syntax.joined_if.equality_condition.is_none()
                && self.node(syntax.joined_if.condition_identifier)?.kind != SyntaxKind::Identifier
        {
            return Ok(());
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

        fn loop_plan(
            &self,
        ) -> Result<SourceLoopFunctionStatementsSyntax, SourceFunctionStatementsError> {
            let callable = self.callable();
            plan_source_loop_function_statements_syntax(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                &callable,
            )
        }

        fn for_in_plan(&self) -> Result<SourceForInStatementSyntax, SourceFunctionStatementsError> {
            let callable = self.callable();
            plan_source_function_for_in_statement_syntax(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                &callable,
            )
        }

        fn for_of_plan(&self) -> Result<SourceForInStatementSyntax, SourceFunctionStatementsError> {
            let callable = self.callable();
            plan_source_function_for_of_statement_syntax(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                &callable,
            )
        }

        fn variable_arrow(&self, name: &str) -> NodeRef {
            self.parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) =
                        &self.parsed.arena.get(variable.name)?.data
                    else {
                        return None;
                    };
                    let initializer = variable.initializer?;
                    (identifier.text == name
                        && self.parsed.arena.get(initializer)?.kind == SyntaxKind::ArrowFunction)
                        .then_some(NodeRef::new(self.parsed.arena.id(), self.file, initializer))
                })
                .expect("expected the named variable's actual arrow initializer")
        }

        fn arrow_callable(&self, name: &str) -> SourceCallablePlan {
            let declaration = self.variable_arrow(name);
            let owner = self.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&self.parsed.arena, &self.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            plan_source_callable(&self.store, &host, declaration, owner, None).unwrap()
        }

        fn for_of_callable_plan(
            &self,
            callable: &SourceCallablePlan,
        ) -> Result<SourceForInStatementSyntax, SourceFunctionStatementsError> {
            plan_source_function_for_of_statement_syntax(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                callable,
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
    fn loop_body_authenticates_lexical_locals_and_expression_order() {
        for (index, (source, expected_kind, expected_binding)) in [
            (
                concat!(
                    "function repeat(flag: boolean): void { ",
                    "while (flag) { let value = 1; consume(value); capture(() => value); } ",
                    "}",
                ),
                SourceControlLoopKind::While,
                VariableBindingKind::Let,
            ),
            (
                concat!(
                    "function repeat(flag: boolean) { ",
                    "do { const value = 1; consume(value); capture(() => value); } while (flag); ",
                    "}",
                ),
                SourceControlLoopKind::DoWhile,
                VariableBindingKind::Const,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_450 + u32::try_from(index).unwrap()));
            let syntax = fixture.loop_plan().unwrap();
            assert_eq!(syntax.control.kind, expected_kind);
            assert_eq!(syntax.locals.len(), 1);
            let [
                SourceLoopFunctionStatementSyntax::Local(local),
                SourceLoopFunctionStatementSyntax::Expression {
                    statement: first,
                    expression: first_expression,
                },
                SourceLoopFunctionStatementSyntax::Expression {
                    statement: second,
                    expression: second_expression,
                },
            ] = syntax.statements.as_slice()
            else {
                panic!("expected one lexical declaration and two ordered calls")
            };
            assert_eq!(*local, syntax.locals[0]);
            assert_eq!(local.binding, expected_binding);
            assert_eq!(
                fixture.bound.block_scope_container(local.declaration),
                Some(syntax.control.body),
            );
            assert_eq!(
                fixture
                    .bound
                    .locals(syntax.control.body)
                    .and_then(|locals| fixture.store.symbol_table(locals))
                    .and_then(|locals| locals.get_source("value")),
                Some(local.symbol),
            );
            for (statement, expression) in
                [(*first, *first_expression), (*second, *second_expression)]
            {
                assert_eq!(
                    fixture.bound.flow_container(statement),
                    Some(fixture.declaration()),
                );
                assert_eq!(
                    fixture.bound.block_scope_container(expression),
                    Some(syntax.control.body),
                );
            }
        }
    }

    #[test]
    fn classic_for_loops_authenticate_initializer_scopes_and_incrementors() {
        for (index, (source, binding, initializer_count, has_incrementor)) in [
            (
                concat!(
                    "function count(): void { ",
                    "for (let index = 0; index < 3; ++index) { ",
                    "const saved = index; (() => index); ",
                    "} }",
                ),
                VariableBindingKind::Let,
                1usize,
                true,
            ),
            (
                concat!(
                    "function count(): void { ",
                    "for (const first = 0, second = 1; first < second;) { ",
                    "const saved = first; (() => second); ",
                    "} }",
                ),
                VariableBindingKind::Const,
                2,
                false,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_480 + u32::try_from(index).unwrap()));
            let syntax = fixture.loop_plan().unwrap();
            assert_eq!(syntax.control.kind, SourceControlLoopKind::For);
            assert_eq!(syntax.initializers.len(), initializer_count);
            assert_eq!(syntax.control.incrementor.is_some(), has_incrementor);
            assert_eq!(syntax.locals.len(), 1);
            for initializer in &syntax.initializers {
                assert_eq!(initializer.binding, binding);
                assert_eq!(
                    fixture.bound.block_scope_container(initializer.declaration),
                    Some(syntax.control.statement),
                );
            }
            assert_eq!(
                fixture.bound.block_scope_container(syntax.control.body),
                Some(syntax.control.statement),
            );
        }
    }

    #[test]
    fn classic_for_loops_reject_unproven_initializers_and_incrementors() {
        for (index, source) in [
            "function count() { for (var index = 0; index < 1; ++index) {} }",
            "function count() { for (let index; index < 1; ++index) {} }",
            "function count(flag: boolean) { for (; flag;) {} }",
            "function count() { for (let index = 0;; ++index) {} }",
            "function count() { for (const index = 0; index < 1; ++index) {} }",
            "function count() { for (let index = 0; index < 1; index += 1) {} }",
            "function count() { for (let [index] = [0]; index < 1; ++index) {} }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_482 + u32::try_from(index).unwrap()));
            assert!(
                matches!(
                    fixture.loop_plan(),
                    Err(SourceFunctionStatementsError::Unsupported(_)),
                ),
                "unexpectedly admitted unsupported classic loop: {source}",
            );
        }
    }

    #[test]
    fn labeled_loops_authenticate_break_and_continue_targets() {
        let fixture = JoinedFixture::new(
            concat!(
                "function count(limit: number): void { ",
                "outer: for (let index = 0; index < limit; ++index) { ",
                "(() => index); ",
                "if (index === 1) { continue; } ",
                "if (index === 2) { continue outer; } ",
                "if (index === 3) { break; } ",
                "if (index === 4) { break outer; } ",
                "} }",
            ),
            FileId::new(1_490),
        );
        let syntax = fixture.loop_plan().unwrap();
        assert_eq!(syntax.labels.len(), 1);
        let label = fixture.parsed.arena.get(syntax.labels[0].node).unwrap();
        assert!(matches!(&label.data, NodeData::Identifier(name) if name.text == "outer"));
        assert_eq!(
            syntax
                .statements
                .iter()
                .filter(|statement| {
                    matches!(
                        statement,
                        SourceLoopFunctionStatementSyntax::ConditionalJump { .. }
                    )
                })
                .count(),
            4,
        );
        for statement in &syntax.statements {
            let SourceLoopFunctionStatementSyntax::ConditionalJump { jump, .. } = statement else {
                continue;
            };
            assert_eq!(
                fixture.bound.flow_container(*jump),
                Some(fixture.declaration()),
            );
        }
    }

    #[test]
    fn nested_labeled_loops_authenticate_outer_jumps_and_conditional_returns() {
        let fixture = JoinedFixture::new(
            concat!(
                "function nested() { ",
                "outer: for (let outerValue = 0; outerValue < 1; ++outerValue) { ",
                "middle: for (const value = 0; value < 1;) { ",
                "inner: for (let item = 0; item < 1; ++item) { ",
                "(function () { return value + item; }); (() => value + item); ",
                "if (item == 1) { break middle; } ",
                "if (value == 2) { continue outer; } ",
                "if (value == 2) { return 'nested'; } ",
                "if (value == 3) { return; } ",
                "} ",
                "if (value == 1) { continue outer; } ",
                "} } }",
            ),
            FileId::new(1_498),
        );

        let syntax = fixture.loop_plan().unwrap();
        let [SourceLoopFunctionStatementSyntax::Loop(middle)] = syntax.statements.as_slice() else {
            panic!("expected one nested middle loop")
        };
        let SourceLoopFunctionStatementSyntax::Loop(inner) = &middle.statements[0] else {
            panic!("expected one nested inner loop")
        };
        assert_eq!(middle.labels.len(), 2);
        assert_eq!(inner.labels.len(), 3);
        assert_eq!(
            inner
                .statements
                .iter()
                .filter(|statement| matches!(
                    statement,
                    SourceLoopFunctionStatementSyntax::ConditionalReturn { .. }
                ))
                .count(),
            2,
        );
    }

    #[test]
    fn labeled_loops_reject_unknown_jump_targets_and_other_branches() {
        for (index, source) in [
            "function count(flag: boolean) { outer: while (flag) { if (flag) break missing; } }",
            "function count(flag: boolean) { while (flag) { if (flag) continue missing; } }",
            "function count(flag: boolean) { while (flag) { if (flag) break; else continue; } }",
            "function count(flag: boolean) { while (flag) { if (flag) { consume(); break; } } }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_491 + u32::try_from(index).unwrap()));
            assert!(
                matches!(
                    fixture.loop_plan(),
                    Err(SourceFunctionStatementsError::Unsupported(_)),
                ),
                "unexpectedly admitted unsupported labeled loop: {source}",
            );
        }
    }

    #[test]
    fn loop_body_rejects_nonlexical_bindings_and_unsupported_statements() {
        for (index, source) in [
            "function repeat(flag: boolean) { while (flag) consume(flag); }",
            "function repeat(flag: boolean) { while (flag) { return; } }",
            "function repeat(flag: boolean) { while (flag) {} consume(flag); }",
            "function repeat(flag: boolean) { for (; flag;) {} }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_452 + u32::try_from(index).unwrap()));
            assert!(
                matches!(
                    fixture.loop_plan(),
                    Err(SourceFunctionStatementsError::Unsupported(_)),
                ),
                "unexpectedly admitted unsupported loop body: {source}",
            );
        }
    }

    #[test]
    fn function_for_in_authenticates_loop_owned_keys_and_captured_closures() {
        let fixture = JoinedFixture::new(
            concat!(
                "function iterate(value: object): void { ",
                "for (let key in value) { ",
                "consume(key); (() => key); (function () { return key; }); ",
                "} }",
            ),
            FileId::new(1_470),
        );
        let syntax = fixture.for_in_plan().unwrap();
        let callable = fixture.declaration();
        assert_eq!(syntax.control.kind, SourceControlLoopKind::ForIn);
        assert_eq!(syntax.binding, VariableBindingKind::Let);
        assert_eq!(syntax.body_statements.len(), 3);
        assert_eq!(fixture.bound.container(syntax.declaration), Some(callable));
        assert_eq!(
            fixture.bound.block_scope_container(syntax.declaration),
            Some(syntax.control.statement),
        );
        assert_eq!(
            fixture
                .bound
                .locals(syntax.control.statement)
                .and_then(|locals| fixture.store.symbol_table(locals))
                .and_then(|locals| locals.get_source("key")),
            Some(syntax.symbol),
        );
        let first = syntax.body_statements.first().unwrap();
        assert_eq!(
            fixture.bound.flow_container(first.statement),
            Some(callable),
        );
        assert_eq!(fixture.bound.flow_at(first.statement), syntax.binding_flow);
    }

    #[test]
    fn function_for_in_rejects_unproven_bindings_and_body_statements() {
        for (index, source) in [
            "function iterate(value: object) { for (var key in value) {} }",
            "function iterate(value: object) { for (let key in value) consume(key); }",
            "function iterate(value: object) { for (const key in value) {} consume(value); }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_471 + u32::try_from(index).unwrap()));
            assert!(
                matches!(
                    fixture.for_in_plan(),
                    Err(SourceFunctionStatementsError::Unsupported(_)),
                ),
                "unexpectedly admitted unsupported function for-in: {source}",
            );
        }
    }

    #[test]
    fn function_iterations_authenticate_ordered_locals_and_captured_closures() {
        for (index, (source, kind, binding)) in [
            (
                concat!(
                    "function iterate(values: number[]) { ",
                    "for (let value of values) { ",
                    "const saved = value; (() => saved); (function () { return saved; }); ",
                    "} }",
                ),
                SourceControlLoopKind::ForOf,
                VariableBindingKind::Const,
            ),
            (
                concat!(
                    "function iterate(values: object) { ",
                    "for (const value in values) { ",
                    "let saved = value; (() => saved); ",
                    "} }",
                ),
                SourceControlLoopKind::ForIn,
                VariableBindingKind::Let,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_520 + u32::try_from(index).unwrap()));
            let syntax = match kind {
                SourceControlLoopKind::ForIn => fixture.for_in_plan().unwrap(),
                SourceControlLoopKind::ForOf => fixture.for_of_plan().unwrap(),
                _ => unreachable!("fixture contains a lexical iteration"),
            };
            let [local] = syntax.locals.as_slice() else {
                panic!("expected one authenticated iteration-local binding")
            };
            assert_eq!(local.binding, binding);
            assert!(matches!(
                syntax.statements.first(),
                Some(SourceLoopFunctionStatementSyntax::Local(first)) if first == local
            ));
            assert_eq!(
                fixture
                    .bound
                    .locals(syntax.control.body)
                    .and_then(|locals| fixture.store.symbol_table(locals))
                    .and_then(|locals| locals.get_source("saved")),
                Some(local.symbol),
            );
            assert_eq!(fixture.bound.flow_at(local.name), syntax.binding_flow);
        }
    }

    #[test]
    fn function_loops_authenticate_hoisted_vars_and_post_loop_reads() {
        for (index, (source, kind)) in [
            (
                concat!(
                    "function iterate(values: string[]) { ",
                    "for (let value of values) { var saved = value; (() => saved); } ",
                    "consume(saved); }",
                ),
                SourceControlLoopKind::ForOf,
            ),
            (
                concat!(
                    "function iterate(values: object) { ",
                    "for (let value in values) { var saved = value; (() => saved); } ",
                    "consume(saved); }",
                ),
                SourceControlLoopKind::ForIn,
            ),
            (
                concat!(
                    "function iterate() { ",
                    "for (let value = 0; value < 1; ++value) { ",
                    "var saved = value; (() => saved); } consume(saved); }",
                ),
                SourceControlLoopKind::For,
            ),
            (
                concat!(
                    "function iterate(flag: boolean) { ",
                    "while (flag) { var saved = 1; (() => saved); } consume(saved); }",
                ),
                SourceControlLoopKind::While,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_530 + u32::try_from(index).unwrap()));
            let (local, trailing) = match kind {
                SourceControlLoopKind::ForIn => {
                    let syntax = fixture.for_in_plan().unwrap();
                    (syntax.locals[0], syntax.trailing_statements)
                }
                SourceControlLoopKind::ForOf => {
                    let syntax = fixture.for_of_plan().unwrap();
                    (syntax.locals[0], syntax.trailing_statements)
                }
                SourceControlLoopKind::For | SourceControlLoopKind::While => {
                    let syntax = fixture.loop_plan().unwrap();
                    (syntax.locals[0], syntax.trailing_statements)
                }
                SourceControlLoopKind::DoWhile => unreachable!("fixture selects another loop"),
            };
            assert_eq!(local.binding, VariableBindingKind::Var);
            assert_eq!(trailing.len(), 1);
            assert_eq!(
                fixture
                    .bound
                    .locals(fixture.declaration())
                    .and_then(|locals| fixture.store.symbol_table(locals))
                    .and_then(|locals| locals.get_source("saved")),
                Some(local.symbol),
            );
        }
    }

    #[test]
    fn function_iteration_locals_reject_forged_function_scoped_symbols() {
        let mut fixture = JoinedFixture::new(
            concat!(
                "function iterate(values: string[]) { ",
                "for (let value of values) { var saved = value; (() => saved); } ",
                "consume(saved); }",
            ),
            FileId::new(1_534),
        );
        let syntax = fixture.for_of_plan().unwrap();
        let [saved] = syntax.locals.as_slice() else {
            panic!("expected one function-scoped iteration local")
        };
        let saved = *saved;
        let callable = fixture.declaration();
        let locals = fixture.bound.locals(callable).unwrap();
        assert_eq!(
            fixture
                .store
                .insert_symbol(locals, EscapedName::source("saved"), syntax.symbol),
            Some(Some(saved.symbol)),
        );

        assert_eq!(
            fixture.for_of_plan(),
            Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                declaration: saved.declaration,
                scope: callable,
                expected: saved.symbol,
                actual: Some(syntax.symbol),
            }
            .into()),
        );
    }

    #[test]
    fn function_loop_bodies_authenticate_uninitialized_let_and_var_bindings() {
        for (index, (source, iteration)) in [
            (
                concat!(
                    "function iterate(flag: boolean) { ",
                    "while (flag) { let first, second; var saved; (() => first + second); } ",
                    "consume(saved); }",
                ),
                false,
            ),
            (
                concat!(
                    "function iterate(values: string[]) { ",
                    "for (let value of values) { let saved; var retained; (() => saved); } ",
                    "consume(retained); }",
                ),
                true,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_535 + u32::try_from(index).unwrap()));
            let locals = if iteration {
                fixture.for_of_plan().unwrap().locals
            } else {
                fixture.loop_plan().unwrap().locals
            };
            assert!(locals.iter().all(|local| local.initializer.is_none()));
            assert!(
                locals
                    .iter()
                    .any(|local| local.binding == VariableBindingKind::Let)
            );
            assert!(
                locals
                    .iter()
                    .any(|local| local.binding == VariableBindingKind::Var)
            );
        }
    }

    #[test]
    fn function_for_of_authenticates_lexical_bindings_and_captured_closures() {
        for (index, (source, binding)) in [
            (
                concat!(
                    "function iterate(value: string): void { ",
                    "for (let item of value) { ",
                    "consume(item); (() => item); (function () { return item; }); ",
                    "} }",
                ),
                VariableBindingKind::Let,
            ),
            (
                concat!(
                    "function iterate(value: string): void { ",
                    "for (const item of value) { (() => item); } ",
                    "}",
                ),
                VariableBindingKind::Const,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_500 + u32::try_from(index).unwrap()));
            let syntax = fixture.for_of_plan().unwrap();
            assert_eq!(syntax.control.kind, SourceControlLoopKind::ForOf);
            assert_eq!(syntax.binding, binding);
            assert_eq!(
                fixture.bound.container(syntax.declaration),
                Some(fixture.declaration()),
            );
            assert_eq!(
                fixture
                    .bound
                    .locals(syntax.control.statement)
                    .and_then(|locals| fixture.store.symbol_table(locals))
                    .and_then(|locals| locals.get_source("item")),
                Some(syntax.symbol),
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the source, lexical owners, and flow in one control.
    fn arrow_for_of_keeps_lexical_parameters_and_the_logical_observer_call() {
        let fixture = JoinedFixture::new(
            concat!(
                "type Observer<T> = { next: (value: T) => void; };\n",
                "const make = <T>() => {\n",
                "  let _observers: Observer<T>[] = [];\n",
                "  const next = (value: T) => {\n",
                "    for (const observer of _observers) {\n",
                "      observer.next && observer.next(value);\n",
                "    }\n",
                "  };\n",
                "};\n",
            ),
            FileId::new(1_540),
        );
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.mapper_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        let callable = fixture.arrow_callable("next");
        let outer = fixture.variable_arrow("make");
        assert_eq!(callable.family, SourceCallableFamily::ArrowFunction);
        assert!(callable.type_parameters.is_empty());
        assert!(callable.return_type.is_inferred());
        assert_ne!(fixture.bound.symbol(outer), Some(callable.owner_symbol));
        assert_eq!(fixture.bound.container(callable.declaration), Some(outer));
        let [parameter] = callable.parameters.as_slice() else {
            panic!("expected the inner arrow's value parameter")
        };
        assert_eq!(
            fixture.bound.container(parameter.declaration),
            Some(callable.declaration),
        );
        assert_eq!(
            fixture.bound.symbol(parameter.declaration),
            Some(parameter.symbol)
        );
        let annotation = parameter.explicit_type_node().unwrap();
        let NodeData::TypeReferenceNode(reference) =
            &fixture.parsed.arena.get(annotation.node).unwrap().data
        else {
            panic!("expected the unchanged T annotation")
        };
        let NodeData::Identifier(name) =
            &fixture.parsed.arena.get(reference.type_name).unwrap().data
        else {
            panic!("expected the outer type parameter name")
        };
        assert_eq!(name.text, "T");
        assert!(fixture.store.type_node_links(annotation).is_none());
        assert!(fixture.store.value_symbol_links(parameter.symbol).is_none());

        let syntax = fixture.for_of_callable_plan(&callable).unwrap();
        assert_eq!(syntax.control.kind, SourceControlLoopKind::ForOf);
        assert_eq!(syntax.binding, VariableBindingKind::Const);
        assert_eq!(syntax.bindings.len(), 1);
        assert_eq!(
            fixture.bound.container(syntax.declaration),
            Some(callable.declaration)
        );
        assert_eq!(
            fixture
                .bound
                .locals(syntax.control.statement)
                .and_then(|locals| fixture.store.symbol_table(locals))
                .and_then(|locals| locals.get_source("observer")),
            Some(syntax.symbol),
        );
        let [body] = syntax.body_statements.as_slice() else {
            panic!("expected the original logical observer call")
        };
        let expression = fixture.parsed.arena.get(body.expression.node).unwrap();
        let NodeData::BinaryExpression(binary) = &expression.data else {
            panic!("expected observer.next && observer.next(value)")
        };
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(binary.operator_token)
                .unwrap()
                .kind,
            SyntaxKind::AmpersandAmpersandToken,
        );
        assert_eq!(
            fixture.parsed.arena.get(binary.left).unwrap().kind,
            SyntaxKind::PropertyAccessExpression
        );
        assert_eq!(
            fixture.parsed.arena.get(binary.right).unwrap().kind,
            SyntaxKind::CallExpression
        );
        assert_eq!(
            fixture.bound.container(body.expression),
            Some(callable.declaration),
        );
        assert_eq!(
            fixture.bound.flow_container(body.statement),
            Some(callable.declaration),
        );
        let graph = fixture.bound.flow_graph();
        assert_eq!(
            fixture.bound.flow_at(syntax.control.statement),
            graph.container_start(callable.declaration),
        );
        let binding_flow = syntax.binding_flow.unwrap();
        assert_eq!(fixture.bound.flow_at(body.statement), Some(binding_flow));
        assert_eq!(
            graph.nodes().get(binding_flow).unwrap().payload,
            Some(FlowNodePayload::Ast(syntax.declaration)),
        );
        assert!(syntax.locals.is_empty());
        assert!(syntax.trailing_statements.is_empty());
        assert_eq!(fixture.for_of_callable_plan(&callable).unwrap(), syntax);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn arrow_for_of_rejects_other_callable_owners_and_parameter_lists() {
        let fixture = JoinedFixture::new(
            concat!(
                "const first = (values: string, saved: number): void => {\n",
                "  for (let item of values) { consume(item, saved); }\n",
                "};\n",
                "const second = (values: string, saved: number): void => {\n",
                "  for (let item of values) { consume(item, saved); }\n",
                "};\n",
            ),
            FileId::new(1_541),
        );
        let first = fixture.arrow_callable("first");
        let second = fixture.arrow_callable("second");
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.mapper_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        let syntax = fixture.for_of_callable_plan(&first).unwrap();
        assert_eq!(syntax.binding, VariableBindingKind::Let);
        let expected =
            Err(SourceFunctionStatementsInvariant::InvalidCallableEdge(first.declaration).into());
        let mut wrong_owner = first.clone();
        wrong_owner.owner_symbol = second.owner_symbol;
        assert_eq!(fixture.for_of_callable_plan(&wrong_owner), expected);
        let mut wrong_body = first.clone();
        wrong_body.body = second.body;
        assert_eq!(fixture.for_of_callable_plan(&wrong_body), expected);
        let mut wrong_return = first.clone();
        wrong_return.return_type = second.return_type;
        assert_eq!(fixture.for_of_callable_plan(&wrong_return), expected);
        let mut wrong_parameters = first.clone();
        wrong_parameters.parameters = second.parameters.clone();
        assert_eq!(fixture.for_of_callable_plan(&wrong_parameters), expected);
        let mut wrong_symbol = first.clone();
        wrong_symbol.parameters[0].symbol = second.parameters[0].symbol;
        assert_eq!(fixture.for_of_callable_plan(&wrong_symbol), expected);
        let mut wrong_order = first.clone();
        wrong_order.parameters.swap(0, 1);
        assert_eq!(fixture.for_of_callable_plan(&wrong_order), expected);
        let mut missing_parameter = first.clone();
        missing_parameter.parameters.truncate(1);
        assert_eq!(fixture.for_of_callable_plan(&missing_parameter), expected);
        let mut wrong_parent = first.clone();
        wrong_parent.owner_parent = Some(second.owner_symbol);
        assert_eq!(fixture.for_of_callable_plan(&wrong_parent), expected);
        assert_eq!(fixture.for_of_callable_plan(&first).unwrap(), syntax);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn arrow_for_of_does_not_admit_arrow_for_in() {
        let fixture = JoinedFixture::new(
            "const iterate = (values: object) => { for (const key in values) { consume(key); } };",
            FileId::new(1_542),
        );
        let callable = fixture.arrow_callable("iterate");
        assert_eq!(
            plan_source_function_for_in_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                &callable,
            ),
            Err(SourceFunctionStatementsError::Unsupported(
                SourceFunctionStatementsUnsupported::Syntax {
                    node: callable.declaration,
                    kind: SyntaxKind::ArrowFunction,
                    role: SourceFunctionStatementsRole::Callable,
                },
            )),
        );
    }

    #[test]
    fn function_for_of_authenticates_array_destructuring_bindings() {
        let fixture = JoinedFixture::new(
            concat!(
                "function iterate(value: any): void { ",
                "for (const [first, second] of value) { ",
                "consume(first); (() => second); ",
                "} }",
            ),
            FileId::new(1_510),
        );
        let syntax = fixture.for_of_plan().unwrap();
        assert_eq!(syntax.control.kind, SourceControlLoopKind::ForOf);
        assert_eq!(syntax.bindings.len(), 2);
        assert!(fixture.bound.symbol(syntax.declaration).is_none());
        for (binding, expected) in syntax.bindings.iter().zip(["first", "second"]) {
            assert_eq!(
                fixture.bound.block_scope_container(binding.declaration),
                Some(syntax.control.statement),
            );
            assert_eq!(
                fixture.bound.symbol(binding.declaration),
                Some(binding.symbol)
            );
            assert_eq!(
                fixture
                    .bound
                    .locals(syntax.control.statement)
                    .and_then(|locals| fixture.store.symbol_table(locals))
                    .and_then(|locals| locals.get_source(expected)),
                Some(binding.symbol),
            );
        }
        let flow = fixture
            .bound
            .flow_graph()
            .nodes()
            .get(syntax.binding_flow.unwrap())
            .unwrap();
        assert_eq!(
            flow.payload,
            Some(FlowNodePayload::Ast(syntax.bindings[1].declaration)),
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
    fn linear_logical_statements_retain_exact_source_operands_without_queries() {
        for (index, argument) in ["value", "1", "\"text\"", "true", "null", "undefined"]
            .into_iter()
            .enumerate()
        {
            let fixture = JoinedFixture::new(
                &format!(
                    "function emit(receiver: unknown, value: unknown): void {{ \
                     receiver.send && receiver.send({argument}); }}"
                ),
                FileId::new(1_550 + u32::try_from(index).unwrap()),
            );
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            let linear = fixture.linear_plan().unwrap();
            let [
                SourceLinearFunctionStatementSyntax::Expression {
                    statement,
                    expression,
                },
            ] = linear.statements.as_slice()
            else {
                panic!("the original body has one logical expression statement")
            };
            let syntax = plan_source_linear_logical_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                *statement,
                fixture.declaration(),
            )
            .unwrap();
            assert_eq!(syntax.expression, *expression);
            assert_eq!(syntax.arguments.len(), 1);
            assert_ne!(syntax.left_receiver, syntax.right_receiver);
            assert_ne!(syntax.left_name, syntax.right_name);
            assert_eq!(
                fixture.bound.flow_at(syntax.statement),
                fixture.bound.flow_graph().container_start(syntax.container)
            );
            assert!(fixture.bound.flow_at(syntax.right).is_none());
            assert_eq!(fixture.linear_plan(), Ok(linear));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before
            );
        }
    }

    #[test]
    fn linear_logical_statements_reject_other_reference_and_effect_shapes() {
        for (index, expression) in [
            "receiver.send || receiver.send(value)",
            "receiver.send ?? receiver.send(value)",
            "receiver.send && other.send(value)",
            "receiver.send && receiver.other(value)",
            "receiver?.send && receiver.send(value)",
            "receiver.send && receiver.send?.(value)",
            "receiver.send && receiver.send(other(value))",
            "receiver.send && (value = 1)",
            "receiver.push && receiver.push(value)",
            "(receiver.send && receiver.send(value))",
            "receiver.send && receiver.send(value) && receiver.send(value)",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = JoinedFixture::new(
                &format!(
                    "function emit(receiver: unknown, other: unknown, value: unknown): void {{ \
                     {expression}; }}"
                ),
                FileId::new(1_560 + u32::try_from(index).unwrap()),
            );
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            for _ in 0..2 {
                assert!(matches!(
                    fixture.linear_plan(),
                    Err(SourceFunctionStatementsError::Unsupported(_))
                ));
                assert_eq!(
                    (
                        fixture.store.type_len(),
                        fixture.store.signature_len(),
                        fixture.store.checker_link_allocated_lengths(),
                    ),
                    before
                );
            }
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
    fn linear_body_retains_throw_and_grouped_unreachable_calls() {
        let source = "function fail() { throw 0; log(1); log(2); }";
        let fixture = JoinedFixture::new(source, FileId::new(1_295));
        let syntax = fixture.linear_plan().unwrap();
        let [
            SourceLinearFunctionStatementSyntax::Throw {
                statement: thrown, ..
            },
            SourceLinearFunctionStatementSyntax::Expression {
                statement: first, ..
            },
            SourceLinearFunctionStatementSyntax::Expression {
                statement: second, ..
            },
        ] = syntax.statements.as_slice()
        else {
            panic!("expected the throw and both calls in source order")
        };
        assert_eq!(
            fixture.bound.flow_graph().is_unreachable(*thrown),
            Some(false)
        );
        for call in [*first, *second] {
            assert_eq!(fixture.bound.flow_graph().is_unreachable(call), Some(true));
            assert!(fixture.bound.flow_at(call).is_none());
        }
        let [range] = syntax.unreachable_ranges.as_slice() else {
            panic!("expected one grouped unreachable range")
        };
        let range = range.range();
        assert_eq!(
            &source[usize::try_from(range.start.get()).unwrap()
                ..usize::try_from(range.end.get()).unwrap()],
            "log(1); log(2);",
        );
        assert!(syntax.return_statement.is_none());
        assert!(syntax.return_expression.is_none());
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
    fn for_of_syntax_authenticates_iteration_symbols_and_assignment_flow() {
        for (index, source) in [
            "for (const item of [1, 2, 3]) { log(item); }",
            "for (const item of text) { log(item); }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_390 + u32::try_from(index).unwrap()));
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ForOfStatement).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();

            let syntax = plan_source_for_of_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
            )
            .unwrap();

            assert_eq!(syntax.control.kind, SourceControlLoopKind::ForOf);
            assert_eq!(
                fixture.bound.symbol(syntax.declaration),
                Some(syntax.symbol)
            );
            let declaration_range = fixture
                .parsed
                .arena
                .get(syntax.declaration.node)
                .unwrap()
                .range;
            let list_range = fixture
                .parsed
                .arena
                .get(syntax.control.initializer.unwrap().node)
                .unwrap()
                .range;
            assert!(list_range.start < declaration_range.start);
            assert_eq!(list_range.end, declaration_range.end);
            assert_eq!(
                fixture.parsed.arena.get(syntax.name.node).unwrap().kind,
                SyntaxKind::Identifier,
            );
            assert_eq!(
                fixture.bound.flow_at(syntax.body_statement),
                Some(syntax.binding_flow)
            );
            let assignment = fixture
                .bound
                .flow_graph()
                .nodes()
                .get(syntax.binding_flow)
                .unwrap();
            assert!(assignment.flags.contains(FlowFlags::ASSIGNMENT));
            assert_eq!(
                assignment.payload,
                Some(FlowNodePayload::Ast(syntax.declaration))
            );
            let NodeData::CallExpression(call) =
                &fixture.parsed.arena.get(syntax.call.node).unwrap().data
            else {
                panic!("expected one loop-body call")
            };
            let callee = NodeRef::new(fixture.parsed.arena.id(), fixture.file, call.expression);
            let argument = NodeRef::new(
                fixture.parsed.arena.id(),
                fixture.file,
                call.arguments.nodes[0],
            );
            assert_eq!(fixture.bound.flow_at(callee), Some(syntax.binding_flow));
            assert_eq!(fixture.bound.flow_at(argument), Some(syntax.binding_flow));
            assert!(fixture.bound.flow_at(syntax.call).is_none());
        }
    }

    #[test]
    fn for_of_syntax_authenticates_direct_iteration_property_reads() {
        let fixture = JoinedFixture::new(
            "for (const item of values) { item.value; }",
            FileId::new(1_460),
        );
        let statement = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ForOfStatement).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();

        let syntax = plan_source_for_of_statement_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            statement,
        )
        .unwrap();

        let NodeData::PropertyAccessExpression(property) =
            &fixture.parsed.arena.get(syntax.call.node).unwrap().data
        else {
            panic!("expected one authenticated iteration property read")
        };
        let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, property.expression);
        assert_eq!(fixture.bound.flow_at(receiver), Some(syntax.binding_flow));
    }

    #[test]
    fn captured_iteration_syntax_authenticates_loop_local_callables() {
        for (index, (source, kind, destructured, arrow)) in [
            (
                "for (let x of [1, 2]) { function f() { x; } }",
                SourceControlLoopKind::ForOf,
                false,
                false,
            ),
            (
                "for (let x of [1, 2]) { let f = () => { x; }; }",
                SourceControlLoopKind::ForOf,
                false,
                true,
            ),
            (
                "for (const x in { a: 1 }) { function f() { x; } }",
                SourceControlLoopKind::ForIn,
                false,
                false,
            ),
            (
                "for (let { x } of [{ x: 1 }]) { let f = () => { x; }; }",
                SourceControlLoopKind::ForOf,
                true,
                true,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_470 + u32::try_from(index).unwrap()));
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(
                        record.kind,
                        SyntaxKind::ForInStatement | SyntaxKind::ForOfStatement
                    )
                    .then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();

            let syntax = plan_source_captured_iteration_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
            )
            .unwrap();

            assert_eq!(syntax.control.kind, kind);
            assert_eq!(syntax.binding.destructured, destructured);
            assert_eq!(
                matches!(
                    syntax.body,
                    SourceCapturedIterationBodySyntax::ArrowVariable { .. }
                ),
                arrow,
            );
        }
    }

    #[test]
    fn captured_iteration_syntax_rejects_forged_loop_local_symbols() {
        let mut fixture = JoinedFixture::new(
            "for (let item of [1]) { let retained = () => { item; }; }",
            FileId::new(1_474),
        );
        let statement = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ForOfStatement).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let syntax = plan_source_captured_iteration_statement_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            statement,
        )
        .unwrap();
        let SourceCapturedIterationBodySyntax::ArrowVariable {
            declaration,
            symbol,
            ..
        } = syntax.body
        else {
            panic!("expected one authenticated loop-local arrow")
        };
        let locals = fixture.bound.locals(syntax.control.body).unwrap();
        assert_eq!(
            fixture.store.insert_symbol(
                locals,
                EscapedName::source("retained"),
                syntax.binding.symbol,
            ),
            Some(Some(symbol)),
        );

        assert_eq!(
            plan_source_captured_iteration_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
            ),
            Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                declaration,
                scope: syntax.control.body,
                expected: symbol,
                actual: Some(syntax.binding.symbol),
            }
            .into()),
        );
    }

    #[test]
    fn captured_iterations_authenticate_ordered_body_locals_and_standalone_closures() {
        for (index, source) in [
            concat!(
                "for (let index = 0; index < 2; ++index) { ",
                "let saved = index; (function () { return saved; }); (() => saved); }",
            ),
            concat!(
                "for (const item of [1]) { ",
                "const saved = item; (() => saved); }",
            ),
            concat!(
                "for (let key in { first: 1 }) { ",
                "let first, second; (() => first + second + key); }",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_540 + u32::try_from(index).unwrap()));
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(
                        record.kind,
                        SyntaxKind::ForStatement
                            | SyntaxKind::ForInStatement
                            | SyntaxKind::ForOfStatement
                    )
                    .then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let syntax = plan_source_captured_iteration_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
            )
            .unwrap();
            let SourceCapturedIterationBodySyntax::ControlFlow(statements) = syntax.body else {
                panic!("expected ordered top-level iteration locals and closures")
            };
            assert!(matches!(
                statements.first(),
                Some(SourceCapturedIterationStatementSyntax::Local(_))
            ));
            assert!(statements.iter().any(|statement| matches!(
                statement,
                SourceCapturedIterationStatementSyntax::Expression(_)
            )));
            for statement in statements {
                if let SourceCapturedIterationStatementSyntax::Local(local) = statement {
                    assert_eq!(
                        fixture.bound.block_scope_container(local.declaration),
                        Some(syntax.control.body),
                    );
                }
            }
        }
    }

    #[test]
    fn captured_block_loops_authenticate_top_level_locals_and_closures() {
        for (index, (source, kind)) in [
            (
                concat!(
                    "while (1 === 1) { ",
                    "let first, second; ",
                    "(function () { return first + second; }); (() => first + second); }",
                ),
                SourceControlLoopKind::While,
            ),
            (
                concat!(
                    "do { const value = 1; ",
                    "(function () { return value; }); (() => value); } while (1 === 1);",
                ),
                SourceControlLoopKind::DoWhile,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_545 + u32::try_from(index).unwrap()));
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(
                        record.kind,
                        SyntaxKind::WhileStatement | SyntaxKind::DoStatement
                    )
                    .then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let syntax = plan_source_captured_block_loop_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
            )
            .unwrap();
            assert_eq!(syntax.control.kind, kind);
            assert!(matches!(
                syntax.statements.first(),
                Some(SourceCapturedIterationStatementSyntax::Local(_))
            ));
            assert_eq!(
                syntax
                    .statements
                    .iter()
                    .filter(|statement| matches!(
                        statement,
                        SourceCapturedIterationStatementSyntax::Expression(_)
                    ))
                    .count(),
                2,
            );
        }
    }

    #[test]
    fn labeled_captured_iterations_authenticate_standalone_closures_and_jumps() {
        let fixture = JoinedFixture::new(
            concat!(
                "outer: inner: for (let value of [1, 2]) { ",
                "(function () { return value; }); (() => value); ",
                "if (value === 1) { break; } ",
                "if (value === 1) { break outer; } ",
                "if (value === 2) { continue; } ",
                "if (value === 2) { continue inner; } ",
                "}",
            ),
            FileId::new(1_480),
        );
        let source = fixture
            .parsed
            .arena
            .get(fixture.parsed.source_file)
            .unwrap();
        let NodeData::SourceFile(source) = &source.data else {
            panic!("expected a source root")
        };
        let root = NodeRef::new(
            fixture.parsed.arena.id(),
            fixture.file,
            source.statements.nodes[0],
        );

        let syntax = plan_source_captured_iteration_statement_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            root,
        )
        .unwrap();

        assert_eq!(syntax.labels.len(), 2);
        assert_eq!(syntax.control.kind, SourceControlLoopKind::ForOf);
        let SourceCapturedIterationBodySyntax::ControlFlow(statements) = syntax.body else {
            panic!("expected standalone closures and conditional jumps")
        };
        assert_eq!(statements.len(), 6);
        assert_eq!(
            statements
                .iter()
                .filter(|statement| matches!(
                    statement,
                    SourceCapturedIterationStatementSyntax::ConditionalJump { .. }
                ))
                .count(),
            4,
        );
    }

    #[test]
    fn labeled_captured_iterations_reject_foreign_jump_targets_and_other_bodies() {
        for (index, source) in [
            "outer: for (let value of [1]) { (() => value); if (value) { break missing; } }",
            "outer: for (let value of [1]) { (() => value); if (value) { continue missing; } }",
            "outer: for (let value of [1]) { (() => value); if (value) { break; } else { continue; } }",
            "outer: for (let value of [1]) { consume(value); if (value) { break outer; } }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_481 + u32::try_from(index).unwrap()));
            let root = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::LabeledStatement
                        && record.parent == Some(fixture.parsed.source_file))
                    .then_some(NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
                })
                .unwrap();
            assert!(
                matches!(
                    plan_source_captured_iteration_statement_syntax(
                        &fixture.parsed.arena,
                        &fixture.bound,
                        &fixture.store,
                        root,
                    ),
                    Err(SourceFunctionStatementsError::Unsupported(_)),
                ),
                "unexpectedly admitted unsupported labeled iteration: {source}",
            );
        }
    }

    #[test]
    fn labeled_captured_iterations_authenticate_classic_initializer_and_updates() {
        for (index, source) in [
            concat!(
                "outer: for (let value = 0; value < 2; ++value) { ",
                "(function () { return value; }); (() => value); ",
                "if (value === 1) { continue outer; } }",
            ),
            concat!(
                "outer: for (const value = 0; value < 1;) { ",
                "(function () { return value; }); (() => value); ",
                "if (value == 1) { break outer; } }",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_485 + u32::try_from(index).unwrap()));
            let root = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::LabeledStatement
                        && record.parent == Some(fixture.parsed.source_file))
                    .then_some(NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
                })
                .unwrap();

            let syntax = plan_source_captured_iteration_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                root,
            )
            .unwrap();

            assert_eq!(syntax.control.kind, SourceControlLoopKind::For);
            assert!(syntax.binding.initializer.is_some());
            assert_eq!(syntax.control.incrementor.is_some(), index == 0);
        }
    }

    #[test]
    fn captured_classic_iterations_authenticate_multiple_ordered_bindings() {
        for (index, (source, binding)) in [
            (
                concat!(
                    "for (let first = 0, second = 1; first < second; ++first) { ",
                    "(function () { return first + second; }); (() => first + second); }",
                ),
                VariableBindingKind::Let,
            ),
            (
                concat!(
                    "for (const first = 0, second = 1; first < second;) { ",
                    "(function () { return first + second; }); (() => first + second); }",
                ),
                VariableBindingKind::Const,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_550 + u32::try_from(index).unwrap()));
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ForStatement).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let syntax = plan_source_captured_iteration_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
            )
            .unwrap();
            let [additional] = syntax.additional_bindings.as_slice() else {
                panic!("expected the second loop-owned initializer")
            };
            assert_eq!(syntax.binding.binding, binding);
            assert_eq!(additional.binding, binding);
            assert_ne!(syntax.binding.symbol, additional.symbol);
            assert_eq!(
                fixture
                    .bound
                    .locals(statement)
                    .and_then(|locals| fixture.store.symbol_table(locals))
                    .and_then(|locals| locals.get_source("second")),
                Some(additional.symbol),
            );
        }
    }

    #[test]
    fn for_in_syntax_authenticates_lexical_keys_and_body_assignment_flow() {
        for (index, (source, binding, statements)) in [
            (
                "for (let key in {}) { log(key); capture(() => key); }",
                VariableBindingKind::Let,
                2usize,
            ),
            (
                "for (const key in value) { log(key); }",
                VariableBindingKind::Const,
                1,
            ),
            ("for (const key in value) {}", VariableBindingKind::Const, 0),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_420 + u32::try_from(index).unwrap()));
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ForInStatement).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();

            let syntax = plan_source_for_in_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
            )
            .unwrap();

            assert_eq!(syntax.control.kind, SourceControlLoopKind::ForIn);
            assert_eq!(syntax.binding, binding);
            assert_eq!(syntax.body_statements.len(), statements);
            assert_eq!(
                fixture.bound.symbol(syntax.declaration),
                Some(syntax.symbol)
            );
            assert_eq!(
                fixture
                    .bound
                    .locals(statement)
                    .and_then(|locals| fixture.store.symbol_table(locals))
                    .and_then(|locals| locals.get_source("key")),
                Some(syntax.symbol),
            );
            if let Some(first) = syntax.body_statements.first() {
                let flow = syntax.binding_flow.unwrap();
                assert_eq!(fixture.bound.flow_at(first.statement), Some(flow));
                let assignment = fixture.bound.flow_graph().nodes().get(flow).unwrap();
                assert_eq!(
                    assignment.payload,
                    Some(FlowNodePayload::Ast(syntax.declaration)),
                );
            } else {
                assert!(syntax.binding_flow.is_none());
            }
        }
    }

    #[test]
    fn unused_iteration_syntax_authenticates_nested_callables_and_object_bindings() {
        for (index, source, kind, local_kind, destructured) in [
            (
                0_u32,
                "for (let x of [1, 2]) { function f() { x; } }",
                SourceControlLoopKind::ForOf,
                SourceUnusedIterationDeclarationKind::Function,
                false,
            ),
            (
                1,
                "for (let x of [1, 2]) { let f = () => { x; }; }",
                SourceControlLoopKind::ForOf,
                SourceUnusedIterationDeclarationKind::ArrowVariable,
                false,
            ),
            (
                2,
                "for (const x in { a: 1 }) { function f() { x; } }",
                SourceControlLoopKind::ForIn,
                SourceUnusedIterationDeclarationKind::Function,
                false,
            ),
            (
                3,
                "for (let { x } of [{ x: 1 }]) { let f = () => { x; }; }",
                SourceControlLoopKind::ForOf,
                SourceUnusedIterationDeclarationKind::ArrowVariable,
                true,
            ),
            (
                4,
                "for (const { x } of [{ x: 1 }]) { function f() { x; } }",
                SourceControlLoopKind::ForOf,
                SourceUnusedIterationDeclarationKind::Function,
                true,
            ),
        ] {
            let fixture = JoinedFixture::new(source, FileId::new(1_500 + index));
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(
                        record.kind,
                        SyntaxKind::ForInStatement | SyntaxKind::ForOfStatement
                    )
                    .then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();

            let syntax = plan_source_unused_iteration_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
            )
            .unwrap();

            assert_eq!(syntax.control.kind, kind);
            assert_eq!(syntax.local_kind, local_kind);
            assert_eq!(syntax.binding_element.is_some(), destructured);
            assert_eq!(
                fixture
                    .bound
                    .symbol(syntax.binding_element.unwrap_or(syntax.binding_declaration)),
                Some(syntax.binding_symbol),
            );
            assert_eq!(
                fixture.bound.symbol(syntax.local_declaration),
                Some(syntax.local_symbol),
            );
            assert_eq!(
                fixture.bound.symbol(syntax.callable),
                Some(syntax.callable_symbol),
            );
            assert_eq!(
                fixture.bound.flow_at(syntax.capture),
                fixture.bound.flow_graph().container_start(syntax.callable),
            );
        }
    }

    #[test]
    fn unused_iteration_syntax_rejects_unproven_bindings_and_captures() {
        for (index, source) in [
            "for (var x of [1]) { function f() { x; } }",
            "for (let { x, y } of [{ x: 1, y: 2 }]) { function f() { x; } }",
            "for (let x of [1]) { function f() { other; } }",
            "for (let x of [1]) { function f(value: number) { x; } }",
            "for (let x of [1]) { const f = () => { x; }; }",
            "for (let x of [1]) { let f = () => { x; x; }; }",
            "for (let x in {}) { function f() { x; } function g() { x; } }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_510 + u32::try_from(index).unwrap()));
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(
                        record.kind,
                        SyntaxKind::ForInStatement | SyntaxKind::ForOfStatement
                    )
                    .then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();

            assert!(
                matches!(
                    plan_source_unused_iteration_statement_syntax(
                        &fixture.parsed.arena,
                        &fixture.bound,
                        &fixture.store,
                        statement,
                    ),
                    Err(SourceFunctionStatementsError::Unsupported(_)
                        | SourceFunctionStatementsError::Invariant(_)),
                ),
                "unexpectedly admitted unsupported unused-iteration shape: {source}",
            );
        }
    }

    #[test]
    fn labeled_for_in_syntax_authenticates_lexical_keys_and_direct_expression_bodies() {
        for (index, (source, expected_binding)) in [
            (
                "outer: for (let key in {}) { (() => key); }",
                VariableBindingKind::Let,
            ),
            (
                "outer: inner: for (const key in value) { (function () { return key; }); }",
                VariableBindingKind::Const,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_441 + u32::try_from(index).unwrap()));
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ForInStatement).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let parent = NodeRef::new(
                fixture.parsed.arena.id(),
                fixture.file,
                fixture
                    .parsed
                    .arena
                    .get(statement.node)
                    .unwrap()
                    .parent
                    .unwrap(),
            );

            let syntax = plan_source_labeled_for_in_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
                parent,
            )
            .unwrap();

            assert_eq!(syntax.control.kind, SourceControlLoopKind::ForIn);
            assert_eq!(syntax.binding, expected_binding);
            assert_eq!(syntax.body_statements.len(), 1);
            assert_eq!(
                fixture.bound.symbol(syntax.declaration),
                Some(syntax.symbol)
            );
            assert_eq!(
                fixture.bound.flow_at(syntax.body_statements[0].statement),
                syntax.binding_flow,
            );
            assert!(
                plan_source_for_in_statement_syntax(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    &fixture.store,
                    statement,
                )
                .is_err()
            );
        }
    }

    #[test]
    fn for_in_syntax_rejects_nonlexical_bindings_and_unsupported_bodies() {
        for (index, source) in [
            "for (var key in value) { log(key); }",
            "for (let key: string in value) { log(key); }",
            "for (const [key] in value) { log(key); }",
            "for (let key in value) log(key);",
            "for (const key in value) { let nested = key; }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_430 + u32::try_from(index).unwrap()));
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ForInStatement).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();

            assert!(
                matches!(
                    plan_source_for_in_statement_syntax(
                        &fixture.parsed.arena,
                        &fixture.bound,
                        &fixture.store,
                        statement,
                    ),
                    Err(SourceFunctionStatementsError::Unsupported(_)),
                ),
                "unexpectedly admitted for-in loop: {source}",
            );
        }
    }

    #[test]
    fn for_in_syntax_rejects_forged_loop_scope_symbols() {
        let mut fixture = JoinedFixture::new(
            "const other = 1; for (let key in {}) { log(key); }",
            FileId::new(1_440),
        );
        let statement = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ForInStatement).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let syntax = plan_source_for_in_statement_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            statement,
        )
        .unwrap();
        let other = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &fixture.parsed.arena.get(variable.name)?.data
                else {
                    return None;
                };
                (name.text == "other").then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let other_symbol = fixture.bound.symbol(other).unwrap();
        let locals = fixture.bound.locals(statement).unwrap();
        assert_eq!(
            fixture
                .store
                .insert_symbol(locals, EscapedName::source("key"), other_symbol),
            Some(Some(syntax.symbol)),
        );

        assert_eq!(
            plan_source_for_in_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
            ),
            Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                declaration: syntax.declaration,
                scope: statement,
                expected: syntax.symbol,
                actual: Some(other_symbol),
            }
            .into()),
        );
    }

    #[test]
    fn for_of_syntax_rejects_other_bindings_and_loop_bodies() {
        for (index, source) in [
            "for (let item of values) { log(item); }",
            "for (var item of values) { log(item); }",
            "for (const item: number of values) { log(item); }",
            "for (const [item] of values) { log(item); }",
            "for (const item of values) log(item);",
            "for (const item of values) { log(); }",
            "for (const item of values) { log(other); }",
            "for (const item of values) { log(item); log(item); }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_400 + u32::try_from(index).unwrap()));
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ForOfStatement).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();

            assert!(
                matches!(
                    plan_source_for_of_statement_syntax(
                        &fixture.parsed.arena,
                        &fixture.bound,
                        &fixture.store,
                        statement,
                    ),
                    Err(SourceFunctionStatementsError::Unsupported(_)),
                ),
                "unexpectedly admitted for-of loop: {source}",
            );
        }
    }

    #[test]
    fn ordinary_for_syntax_authenticates_initializer_scopes_and_terminal_jumps() {
        for (keyword, binding) in [
            ("let", VariableBindingKind::Let),
            ("var", VariableBindingKind::Var),
        ] {
            let mut fixture = JoinedFixture::new(
                &format!(
                    "const other = 1; for ({keyword} index = 0; index < 2; ++index) {{ const copy = index; continue; }}"
                ),
                FileId::new(9_203),
            );
            let statement = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ForStatement).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let syntax = plan_source_for_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
            )
            .unwrap();
            let [initializer] = syntax.initializers.as_slice() else {
                panic!("expected one loop initializer")
            };
            assert_eq!(initializer.binding, binding);
            assert_eq!(
                fixture.bound.block_scope_container(initializer.declaration),
                Some(statement)
            );
            assert_eq!(syntax.statements.len(), 1);
            let jump = syntax.terminal_jump.unwrap();
            assert_eq!(
                fixture.parsed.arena.get(jump.node).unwrap().kind,
                SyntaxKind::ContinueStatement
            );
            assert_eq!(
                fixture.bound.flow_container(jump),
                Some(fixture.bound.source_file())
            );
            let scope = if binding == VariableBindingKind::Var {
                fixture.bound.source_file()
            } else {
                statement
            };
            let source_locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
            let other = fixture
                .store
                .symbol_table(source_locals)
                .unwrap()
                .get_source("other")
                .unwrap();
            let locals = fixture.bound.locals(scope).unwrap();
            assert_eq!(
                fixture
                    .store
                    .insert_symbol(locals, EscapedName::source("index"), other),
                Some(Some(initializer.symbol))
            );
            for _ in 0..2 {
                assert_eq!(
                    plan_source_for_statement_syntax(
                        &fixture.parsed.arena,
                        &fixture.bound,
                        &fixture.store,
                        statement
                    ),
                    Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                        declaration: initializer.declaration,
                        scope,
                        expected: initializer.symbol,
                        actual: Some(other),
                    }
                    .into())
                );
            }
        }
    }

    #[test]
    fn ordinary_for_syntax_keeps_labels_and_rejects_foreign_jump_targets() {
        for (label, admitted) in [("outer", true), ("missing", false)] {
            let fixture = JoinedFixture::new(
                &format!("outer: for (;;) {{ if (done) {{ continue {label}; }} break outer; }}"),
                FileId::new(9_204),
            );
            let root = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::LabeledStatement).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let result = plan_source_for_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                root,
            );
            if admitted {
                let syntax = result.unwrap();
                assert!(syntax.initializers.is_empty());
                assert!(syntax.control.condition.is_none());
                assert!(syntax.control.incrementor.is_none());
                assert!(matches!(
                    syntax.statements.as_slice(),
                    [SourceCapturedIterationStatementSyntax::ConditionalJump { .. }]
                ));
                assert!(syntax.terminal_jump.is_some());
            } else {
                assert!(matches!(
                    result,
                    Err(SourceFunctionStatementsError::Unsupported(_))
                ));
            }
        }
    }

    #[test]
    fn for_of_syntax_rejects_forged_loop_scope_symbols() {
        let mut fixture = JoinedFixture::new(
            "const other = 1; for (const item of values) { log(item); }",
            FileId::new(1_410),
        );
        let statement = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ForOfStatement).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let syntax = plan_source_for_of_statement_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            statement,
        )
        .unwrap();
        let other = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &fixture.parsed.arena.get(variable.name)?.data
                else {
                    return None;
                };
                (name.text == "other").then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let other_symbol = fixture.bound.symbol(other).unwrap();
        let locals = fixture.bound.locals(statement).unwrap();
        assert_eq!(
            fixture
                .store
                .insert_symbol(locals, EscapedName::source("item"), other_symbol),
            Some(Some(syntax.symbol)),
        );

        assert_eq!(
            plan_source_for_of_statement_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
            ),
            Err(SourceFunctionStatementsInvariant::LocalTableMismatch {
                declaration: syntax.declaration,
                scope: statement,
                expected: syntax.symbol,
                actual: Some(other_symbol),
            }
            .into()),
        );
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
    fn void_switch_authenticates_bare_returns_and_grouped_unreachable_calls() {
        for (index, source, reachability, expected_range) in [
            (
                0_u32,
                concat!(
                    "function choose(value: string) {\n",
                    "  switch (value) {\n",
                    "    case 'first':\n",
                    "      return;\n",
                    "      console.log('one');\n",
                    "      console.log('two');\n",
                    "    case 'second':\n",
                    "      console.log('three');\n",
                    "  }\n",
                    "}\n",
                ),
                [true, true, false, false],
                "console.log('one');\n      console.log('two');",
            ),
            (
                1,
                concat!(
                    "function choose(value: string) {\n",
                    "  switch (value) {\n",
                    "    case 'first':\n",
                    "      console.log('one');\n",
                    "    default:\n",
                    "      return;\n",
                    "      console.log('two');\n",
                    "      console.log('three');\n",
                    "    case 'second':\n",
                    "      console.log('four');\n",
                    "  }\n",
                    "}\n",
                ),
                [false, true, true, false],
                "console.log('two');\n      console.log('three');",
            ),
        ] {
            let fixture = JoinedFixture::new(source, FileId::new(1_420 + index));
            let callable = fixture.callable();

            let syntax = plan_source_void_switch_function_statements_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                &callable,
            )
            .unwrap();

            assert_eq!(syntax.body, callable.body);
            assert_eq!(syntax.returns.len(), 1);
            assert_eq!(
                syntax
                    .calls
                    .iter()
                    .map(|call| call.unreachable)
                    .collect::<Vec<_>>(),
                reachability
                    .into_iter()
                    .take(syntax.calls.len())
                    .collect::<Vec<_>>(),
            );
            for call in &syntax.calls {
                assert_eq!(
                    fixture.bound.flow_graph().is_unreachable(call.statement),
                    Some(call.unreachable),
                );
            }
            let ranges = syntax
                .switch
                .clauses
                .iter()
                .flat_map(|clause| clause.unreachable_ranges.iter())
                .collect::<Vec<_>>();
            let [range] = ranges.as_slice() else {
                panic!("expected one grouped unreachable range")
            };
            let range = range.range();
            let start = usize::try_from(range.start.get()).unwrap();
            let end = usize::try_from(range.end.get()).unwrap();
            assert_eq!(source.get(start..end), Some(expected_range));
        }
    }

    #[test]
    fn void_switch_rejects_other_returns_cases_and_call_arguments() {
        for (index, source) in [
            "function choose(value: number) { switch (value) { case 'first': return; case 'second': log('x'); } }",
            "function choose(value: string) { switch (value) { case 'first': return value; case 'second': log('x'); } }",
            "function choose(value: string) { switch (value) { case 1: return; case 'second': log('x'); } }",
            "function choose(value: string) { switch (value) { case 'first': return; case 'second': log(value); } }",
            "function choose(value: string) { switch (value) { case 'first': return; case 'second': value; } }",
            "function choose(value: string) { switch (value) { case 'first': log('x'); } }",
            "function choose(value: string) { switch (value) { case 'first': return; } }",
            "function choose(value: string, other: string) { switch (other) { case 'first': return; case 'second': log('x'); } }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_430 + u32::try_from(index).unwrap()));
            let callable = fixture.callable();

            assert!(
                matches!(
                    plan_source_void_switch_function_statements_syntax(
                        &fixture.parsed.arena,
                        &fixture.bound,
                        &fixture.store,
                        &callable,
                    ),
                    Err(SourceFunctionStatementsError::Unsupported(_)),
                ),
                "unexpectedly admitted void switch: {source}",
            );
        }
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
    fn function_switch_authenticates_correlated_bindings_and_default_array_destructuring() {
        let fixture = JoinedFixture::new(
            concat!(
                "function choose(input: any): number { ",
                "const { kind, values } = input; ",
                "switch (kind) { ",
                "case 'first': return values[0]; ",
                "case 'second': return 1; ",
                "default: const [missing] = values; return values; ",
                "} }",
            ),
            FileId::new(1_340),
        );
        let callable = fixture.callable();
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.mapper_len(),
        );

        let syntax = plan_source_switch_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();

        let leading = syntax.leading.as_ref().unwrap();
        assert_eq!(leading.elements.len(), 2);
        for element in &leading.elements {
            assert_eq!(fixture.bound.symbol(element.element), Some(element.symbol));
            assert_eq!(
                fixture.bound.block_scope_container(element.element),
                Some(callable.declaration),
            );
        }
        assert_eq!(syntax.returns.len(), 3);
        assert!(
            syntax.returns[..2]
                .iter()
                .all(|value| value.binding.is_none())
        );
        let default = syntax.returns[2].binding.unwrap();
        assert_eq!(fixture.bound.symbol(default.element), Some(default.symbol));
        assert_eq!(
            fixture.bound.block_scope_container(default.element),
            Some(syntax.switch.case_block),
        );
        assert_eq!(
            plan_source_switch_function_statements_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                &callable,
            ),
            Ok(syntax),
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
    fn function_switch_authenticates_renamed_and_static_computed_binding_properties() {
        for (index, (pattern, computed_count)) in [
            ("{ kind: tag, values: items }", 0_usize),
            ("{ 'kind': tag, values: items }", 0),
            ("{ ['kind']: tag, [`values`]: items }", 2),
            ("{ [0]: tag, ['values']: items }", 2),
        ]
        .into_iter()
        .enumerate()
        {
            let source = format!(
                "function choose(input: any): number {{ \
                 const {pattern} = input; \
                 switch (tag) {{ \
                 case 'first': return items[0]; \
                 default: const [missing] = items; return items; \
                 }} }}",
            );
            let fixture =
                JoinedFixture::new(&source, FileId::new(1_350 + u32::try_from(index).unwrap()));
            let callable = fixture.callable();
            let syntax = plan_source_switch_function_statements_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                &callable,
            )
            .unwrap_or_else(|error| panic!("{pattern}: {error:?}"));
            let leading = syntax.leading.as_ref().unwrap();
            assert_eq!(leading.elements.len(), 2, "{pattern}");
            assert_eq!(
                leading
                    .elements
                    .iter()
                    .filter(|element| element.computed_key.is_some())
                    .count(),
                computed_count,
                "{pattern}",
            );
            for element in &leading.elements {
                assert_eq!(fixture.bound.symbol(element.element), Some(element.symbol));
                assert_eq!(
                    fixture
                        .parsed
                        .arena
                        .get(element.property.node)
                        .unwrap()
                        .parent,
                    Some(element.element.node),
                );
                if let Some(key) = element.computed_key {
                    assert_eq!(
                        fixture.parsed.arena.get(key.node).unwrap().parent,
                        Some(element.property.node),
                    );
                }
            }
        }
    }

    #[test]
    fn function_switch_authenticates_omitted_default_array_binding_positions() {
        for (index, (pattern, position)) in [
            ("[, missing]", 1_usize),
            ("[, , missing,]", 2),
            ("[, missing, ,]", 1),
            ("[missing,]", 0),
        ]
        .into_iter()
        .enumerate()
        {
            let source = format!(
                "function choose(input: any): number {{ \
                 const {{ kind: tag, values: items }} = input; \
                 switch (tag) {{ \
                 case 'first': return items[0]; \
                 default: const {pattern} = items; return items; \
                 }} }}",
            );
            let fixture =
                JoinedFixture::new(&source, FileId::new(1_360 + u32::try_from(index).unwrap()));
            let callable = fixture.callable();
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.mapper_len(),
            );

            let syntax = plan_source_switch_function_statements_syntax(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                &callable,
            )
            .unwrap_or_else(|error| panic!("{pattern}: {error:?}"));

            let binding = syntax.returns.last().unwrap().binding.unwrap();
            let NodeData::BindingPattern(elements) =
                &fixture.parsed.arena.get(binding.pattern.node).unwrap().data
            else {
                panic!("expected the authenticated default array pattern")
            };
            assert_eq!(elements.elements.nodes[position], binding.element.node);
            assert_eq!(fixture.bound.symbol(binding.element), Some(binding.symbol));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.mapper_len(),
                ),
                before,
                "{pattern}",
            );
        }
    }

    #[test]
    fn function_switch_rejects_unproven_correlated_binding_shapes() {
        for (index, source) in [
            concat!(
                "function choose(input: any): number { ",
                "const { [input]: tag, values } = input; ",
                "switch (tag) { default: return 1; } }",
            ),
            concat!(
                "function choose(input: any): number { ",
                "let { kind, values } = input; ",
                "switch (kind) { default: return 1; } }",
            ),
            concat!(
                "function choose(input: any): number { ",
                "const { kind, values } = input; ",
                "switch (kind) { default: const [first, second] = values; return 1; } }",
            ),
            concat!(
                "function choose(input: any): number { ",
                "const { kind, values } = input; ",
                "switch (kind) { default: const [,] = values; return 1; } }",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                JoinedFixture::new(source, FileId::new(1_341 + u32::try_from(index).unwrap()));
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
            "function f(level) { switch (level) { default: return level + 1; } }",
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
    fn joined_equality_syntax_authenticates_nullish_and_discriminant_operands() {
        for (index, (parameter, condition, comparison, strict, operand_on_left, discriminant)) in [
            (
                "string | null | undefined",
                "value !== null",
                SourceTypeofComparison::NotEqual,
                true,
                true,
                false,
            ),
            (
                "string | null | undefined",
                "null === value",
                SourceTypeofComparison::Equal,
                true,
                false,
                false,
            ),
            (
                "string | null | undefined",
                "value == null",
                SourceTypeofComparison::Equal,
                false,
                true,
                false,
            ),
            (
                "string | null | undefined",
                "undefined != value",
                SourceTypeofComparison::NotEqual,
                false,
                false,
                false,
            ),
            (
                "Choice",
                "value.kind === \"ready\"",
                SourceTypeofComparison::Equal,
                true,
                true,
                true,
            ),
            (
                "Choice",
                "false !== value.active",
                SourceTypeofComparison::NotEqual,
                true,
                false,
                true,
            ),
            (
                "string",
                "value === `ready`",
                SourceTypeofComparison::Equal,
                true,
                true,
                false,
            ),
            (
                "number",
                "1 !== value",
                SourceTypeofComparison::NotEqual,
                true,
                false,
                false,
            ),
            (
                "bigint",
                "value === 1n",
                SourceTypeofComparison::Equal,
                true,
                true,
                false,
            ),
            (
                "boolean",
                "value === true",
                SourceTypeofComparison::Equal,
                true,
                true,
                false,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let source = format!(
                "type Choice = {{ kind: \"ready\"; active: true }} | {{ kind: \"waiting\"; active: false }};\nfunction narrowed(value: {parameter}): {parameter} {{\n  if ({condition}) {{\n    const selected: {parameter} = value;\n  }} else {{\n    const rejected: {parameter} = value;\n  }}\n  return value;\n}}\n"
            );
            let fixture =
                JoinedFixture::new(&source, FileId::new(1_380 + u32::try_from(index).unwrap()));
            let syntax = fixture.plan().unwrap();
            let equality = syntax
                .joined_if
                .equality_condition
                .expect("expected an authenticated equality condition");

            assert!(syntax.joined_if.typeof_condition.is_none());
            assert_eq!(equality.identifier, syntax.joined_if.condition_identifier);
            assert_eq!(equality.comparison, comparison);
            assert_eq!(equality.strict, strict);
            assert_eq!(equality.operand_on_left, operand_on_left);
            assert_eq!(equality.discriminant.is_some(), discriminant);
            if discriminant {
                assert_eq!(equality.discriminant, Some(equality.operand));
            }

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
    fn joined_equality_syntax_rejects_loose_literals_and_unproven_operands() {
        for (index, condition) in [
            "value == \"ready\"",
            "value != true",
            "value.kind == \"ready\"",
            "(value) === null",
            "value?.kind === \"ready\"",
            "value.other.kind === \"ready\"",
            "value.kind() === \"ready\"",
            "value === other",
            "null === undefined",
        ]
        .into_iter()
        .enumerate()
        {
            let source = format!(
                "function narrowed(value: string | null): string | null {{ if ({condition}) {{}} else {{}} return value; }}"
            );
            let fixture =
                JoinedFixture::new(&source, FileId::new(1_390 + u32::try_from(index).unwrap()));
            assert!(
                matches!(
                    fixture.plan(),
                    Err(SourceJoinedFunctionStatementsError::Statements(
                        SourceFunctionStatementsError::Unsupported(
                            SourceFunctionStatementsUnsupported::Syntax {
                                role: SourceFunctionStatementsRole::Condition,
                                ..
                            },
                        ),
                    )),
                ),
                "unexpectedly accepted {condition}",
            );
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
    fn final_if_accepts_inferred_functions_without_losing_branch_scope() {
        let fixture = JoinedFixture::new(
            concat!(
                "function infer(value: string | undefined) {\n",
                "  const before: string | undefined = value;\n",
                "  if (value) {\n",
                "    const selected: string = value;\n",
                "    return selected;\n",
                "  } else {\n",
                "    const fallback = 1;\n",
                "    return fallback;\n",
                "  }\n",
                "}\n",
            ),
            FileId::new(1_360),
        );
        let callable = fixture.callable();
        assert!(callable.return_type.is_inferred());
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.mapper_len(),
        );

        let first = plan_source_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();
        let second = plan_source_function_statements_syntax(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            &callable,
        )
        .unwrap();

        assert_eq!(first, second);
        assert_eq!(first.leading.len(), 1);
        assert_eq!(first.final_if.then_branch.locals.len(), 1);
        assert_eq!(first.final_if.else_branch.locals.len(), 1);
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
