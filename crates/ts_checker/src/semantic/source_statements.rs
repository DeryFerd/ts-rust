//! Exact syntax and binder proof for the first function-statement vertical.
//!
//! This leaf admits one annotated function declaration whose block contains
//! initialized identifier-named `let`/`const` declarations followed by one
//! final two-arm `if`. Each arm is a block containing optional declarations
//! followed by exactly one value-returning `return`. It deliberately stops
//! before expression planning, lexical admission-set mutation, flow narrowing,
//! or checking. Those operations remain source-dispatch responsibilities.

use std::collections::HashSet;

use ts_ast::{Node, NodeArena, NodeData, NodeId, NodeRef, SyntaxKind};
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
        SourceFunctionStatementsError::Unsupported(SourceFunctionStatementsUnsupported::Syntax {
            node,
            kind,
            role,
        })
    }
}

fn range_contains(parent: ts_core::TextRange, child: ts_core::TextRange) -> bool {
    parent.start <= parent.end
        && child.start <= child.end
        && child.start >= parent.start
        && child.end <= parent.end
}
