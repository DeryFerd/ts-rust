//! Exact syntax and binder proof for the first function-statement vertical.
//!
//! This leaf admits two additive annotated-function shapes. The first contains
//! initialized identifier-named `let`/`const` declarations followed by one
//! final two-arm `if`, with a value return in each arm. The second contains one
//! two-arm fallthrough `if` between leading and trailing declarations, followed
//! by one final value return. It deliberately stops before expression planning,
//! lexical admission-set mutation, flow narrowing, or checking. Those
//! operations remain source-dispatch responsibilities.

use std::collections::HashSet;

use ts_ast::{
    FlowFlags, FlowNode, FlowNodePayload, FlowRef, Node, NodeArena, NodeData, NodeId, NodeRef,
    SyntaxKind,
};
use ts_binder::{BoundFile, SemanticSymbolId};

use super::{
    CanonicalTypeMapperStore,
    source_callables::{SourceCallableFamily, SourceCallablePlan},
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

/// One exact block arm ending in a value-returning `return`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceReturnBranchSyntax {
    pub(super) block: NodeRef,
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
    pub(super) then_branch: SourceReturnBranchSyntax,
    pub(super) else_branch: SourceReturnBranchSyntax,
}

/// Complete source-ordered syntax for the first closed function-body vertical.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceFunctionStatementsSyntax {
    pub(super) body: NodeRef,
    pub(super) leading: Vec<SourceLocalDeclarationSyntax>,
    pub(super) final_if: SourceFinalIfSyntax,
}

/// One fallthrough block arm containing initialized locals only.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceFallthroughBranchSyntax {
    pub(super) block: NodeRef,
    pub(super) locals: Vec<SourceLocalDeclarationSyntax>,
}

/// The exact joined `if` and its unwrapped direct identifier condition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceJoinedIfSyntax {
    pub(super) statement: NodeRef,
    pub(super) condition: NodeRef,
    pub(super) condition_identifier: NodeRef,
    pub(super) then_branch: SourceFallthroughBranchSyntax,
    pub(super) else_branch: SourceFallthroughBranchSyntax,
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
    MissingElse(NodeRef),
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
            leading.extend(self.plan_local_statement(statement, body, declaration)?);
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

        let condition = self.reference(if_statement.expression);
        self.validate_parent(
            condition,
            Some(statement.node),
            SourceFunctionStatementsRole::Condition,
        )?;
        self.validate_range(condition, statement)?;
        let condition_identifier = self.plan_condition(condition, callable)?;

        let then_block = self.reference(if_statement.then_statement);
        let else_block = if_statement
            .else_statement
            .map(|node| self.reference(node))
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
            condition_identifier,
            then_branch,
            else_branch,
        })
    }

    fn plan_condition(
        &self,
        condition: NodeRef,
        callable: NodeRef,
    ) -> Result<NodeRef, SourceFunctionStatementsError> {
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
                    return Ok(current);
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

    fn plan_branch(
        &self,
        block: NodeRef,
        if_statement: NodeRef,
        callable: NodeRef,
    ) -> Result<SourceReturnBranchSyntax, SourceFunctionStatementsError> {
        let record = self.node(block)?;
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
            locals.extend(self.plan_local_statement(
                self.reference(statement_id),
                block,
                callable,
            )?);
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
            block,
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
            leading.extend(self.plan_local_statement(
                self.reference(statement_id),
                body,
                declaration,
            )?);
        }
        let joined_if =
            self.plan_joined_if(self.reference(preceding[if_index]), body, declaration)?;
        let mut trailing = Vec::new();
        for &statement_id in &preceding[if_index + 1..] {
            trailing.extend(self.plan_local_statement(
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

        let condition = self.reference(if_statement.expression);
        self.validate_parent(
            condition,
            Some(statement.node),
            SourceFunctionStatementsRole::Condition,
        )?;
        self.validate_range(condition, statement)?;
        let condition_identifier = self.plan_condition(condition, callable)?;

        let then_block = self.reference(if_statement.then_statement);
        let else_block = if_statement
            .else_statement
            .map(|node| self.reference(node))
            .ok_or(SourceJoinedFunctionStatementsError::Unsupported(
                SourceJoinedFunctionStatementsUnsupported::MissingElse(statement),
            ))?;
        self.validate_range(then_block, statement)?;
        self.validate_range(else_block, statement)?;
        self.validate_order(condition, then_block)?;
        self.validate_order(then_block, else_block)?;

        Ok(SourceJoinedIfSyntax {
            statement,
            condition,
            condition_identifier,
            then_branch: self.plan_fallthrough_branch(then_block, statement, callable)?,
            else_branch: self.plan_fallthrough_branch(else_block, statement, callable)?,
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
            locals.extend(self.plan_local_statement(
                self.reference(statement_id),
                block,
                callable,
            )?);
        }
        Ok(SourceFallthroughBranchSyntax { block, locals })
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
    fn joined_shape_rejects_missing_else_returns_and_nested_control() {
        let no_else = JoinedFixture::new(
            "function f(value: boolean): boolean { if (value) {} return value; }",
            FileId::new(1_210),
        );
        assert!(matches!(
            no_else.plan(),
            Err(SourceJoinedFunctionStatementsError::Unsupported(
                SourceJoinedFunctionStatementsUnsupported::MissingElse(_),
            )),
        ));

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
