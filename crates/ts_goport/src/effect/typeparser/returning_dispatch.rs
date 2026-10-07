//! Port of Effect-TS/tsgo `internal/typeparser/returning_dispatch.go`.

use crate::effect::typeparser::*;
use crate::prelude::*;

/// Go `DispatchConditionKind`: identifies how one result-producing branch is
/// selected.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum DispatchConditionKind {
    /// Go `DispatchConditionPredicate`: a boolean condition from an if or
    /// conditional expression.
    Predicate = 0,
    /// Go `DispatchConditionSwitchCase`: compares Subject, the switch
    /// discriminant, with Value, the case expression.
    SwitchCase = 1,
}

/// Go `DispatchCondition`: preserves the source nodes that select one
/// branch. Predicate conditions set Subject to the condition expression and
/// leave Value nil. Switch cases set Subject to the shared discriminant and
/// Value to the case expression. Source is the predicate expression or case
/// clause used for diagnostics. TagSubject and TagValue are populated when
/// the condition has the syntactic shape of an equality dispatch on a `_tag`
/// property.
#[derive(Clone, Copy, Debug)]
pub struct DispatchCondition {
    pub kind: DispatchConditionKind,
    pub source: Node,
    pub subject: Node,
    pub value: Node,
    pub tag_subject: Node,
    pub tag_value: Node,
}

/// Go `ResultDispatchBranch`: one source-ordered branch in a decoded
/// result-producing expression or block.
#[derive(Clone, Copy, Debug)]
pub struct ResultDispatchBranch {
    pub condition: DispatchCondition,
    pub result: Node,
}

/// Go `ResultDispatch`: an ordered, first-match result dispatch with an
/// optional fallback.
#[derive(Clone, Debug)]
pub struct ResultDispatch {
    pub node: Node,
    pub branches: Vec<ResultDispatchBranch>,
    pub fallback: Node,
}

/// Go `ParsedReturningDispatch`: a decoded arrow function or function
/// expression whose body consists entirely of result-producing branches.
/// PORT: Go `Dispatch` is a `*ResultDispatch` that `ParseReturningDispatch`
/// always sets.
#[derive(Clone, Debug)]
pub struct ParsedReturningDispatch {
    pub node: Node,
    pub params: Vec<Node>,
    pub body: Node,
    pub dispatch: Rc<ResultDispatch>,
}

/// Go `resultDispatchSyntax`.
/// PORT: the Go `*resultDispatchSyntax` results of this file are
/// `Option<ResultDispatchSyntax>`; no caller shares them.
#[derive(Clone, Debug, Default)]
pub struct ResultDispatchSyntax {
    pub branches: Vec<ResultDispatchBranch>,
    pub fallback: Node,
}

/// Go `ParseResultDispatch`: decodes a result-producing conditional
/// expression or block into source-ordered branches and an optional
/// fallback. False-arm conditional chains are flattened; conditionals in a
/// true arm are rejected.
pub fn parse_result_dispatch(node: Node) -> Option<Rc<ResultDispatch>> {
    if node.is_nil() {
        return None;
    }
    let syntax = parse_result_dispatch_body(node)?;
    if syntax.branches.is_empty() {
        return None;
    }
    Some(Rc::new(ResultDispatch {
        node,
        branches: syntax.branches,
        fallback: syntax.fallback,
    }))
}

/// Go `ParseReturningDispatch`: decodes an arrow function or function
/// expression into source-ordered result branches and an optional fallback.
/// It recognizes conditional expressions, returned conditional expressions,
/// if/else-if, sequential returning if statements, and returning switch
/// cases.
pub fn parse_returning_dispatch(node: Node) -> Option<Rc<ParsedReturningDispatch>> {
    let node = unwrap_result_dispatch_expression(node);
    if node.is_nil()
        || (node.kind() != SyntaxKind::ArrowFunction
            && node.kind() != SyntaxKind::FunctionExpression)
    {
        return None;
    }
    let type_parameters = get_function_like_type_parameters(node);
    if type_parameters.is_some() && !type_parameters.nodes().is_empty() {
        return None;
    }
    let body = get_function_like_body(node);
    if body.is_nil() {
        return None;
    }

    let dispatch = parse_result_dispatch(body)?;
    let parameters = get_function_like_parameters(node);
    let mut params: Vec<Node> = Vec::new();
    if parameters.is_some() {
        params = parameters.nodes().to_vec();
    }
    Some(Rc::new(ParsedReturningDispatch {
        node,
        params,
        body,
        dispatch,
    }))
}

fn parse_result_dispatch_body(node: Node) -> Option<ResultDispatchSyntax> {
    let node = unwrap_result_dispatch_expression(node);
    if node.is_nil() {
        return None;
    }
    match node.kind() {
        SyntaxKind::Block => parse_result_dispatch_block(node),
        SyntaxKind::ConditionalExpression => parse_result_dispatch_conditional(node),
        _ => None,
    }
}

fn parse_result_dispatch_block(node: Node) -> Option<ResultDispatchSyntax> {
    if node.is_nil() || node.kind() != SyntaxKind::Block {
        return None;
    }
    // PORT: Go `block.Statements == nil` reads as an empty list here.
    let statements = node.statements().to_vec();
    if statements.is_empty() {
        return None;
    }
    if statements.len() == 1 && statements[0].is_some() {
        match statements[0].kind() {
            SyntaxKind::SwitchStatement => return parse_result_dispatch_switch(statements[0]),
            SyntaxKind::IfStatement => return parse_result_dispatch_if_else(statements[0]),
            SyntaxKind::ReturnStatement => {
                let expression = statements[0].expression();
                if expression.is_nil() {
                    return None;
                }
                return parse_result_dispatch_conditional(expression);
            }
            _ => {}
        }
    }
    parse_result_dispatch_sequential_ifs(&statements)
}

fn parse_result_dispatch_switch(node: Node) -> Option<ResultDispatchSyntax> {
    if node.is_nil() || node.kind() != SyntaxKind::SwitchStatement {
        return None;
    }
    let statement_expression = node.expression();
    let case_block = node.case_block();
    if statement_expression.is_nil()
        || case_block.is_nil()
        || case_block.kind() != SyntaxKind::CaseBlock
    {
        return None;
    }
    let clauses = case_block.clauses();
    if clauses.is_nil() {
        return None;
    }

    let clause_nodes = clauses.nodes().to_vec();
    let mut dispatch = ResultDispatchSyntax::default();
    for (index, clause_node) in clause_nodes.iter().copied().enumerate() {
        if clause_node.is_nil()
            || (clause_node.kind() != SyntaxKind::CaseClause
                && clause_node.kind() != SyntaxKind::DefaultClause)
        {
            return None;
        }
        // PORT: Go `clause.Statements == nil` returns nil; the port reads it
        // as an empty list, which `singleResultDispatchReturn` also rejects.
        let result = single_result_dispatch_return(&clause_node.statements().to_vec());
        if result.is_nil() {
            return None;
        }

        if clause_node.kind() == SyntaxKind::DefaultClause {
            if index != clause_nodes.len() - 1 || dispatch.fallback.is_some() {
                return None;
            }
            dispatch.fallback = result;
            continue;
        }
        let clause_expression = clause_node.expression();
        if clause_expression.is_nil() {
            return None;
        }
        dispatch.branches.push(ResultDispatchBranch {
            condition: new_dispatch_condition(
                DispatchConditionKind::SwitchCase,
                clause_node,
                statement_expression,
                clause_expression,
            ),
            result,
        });
    }
    if dispatch.branches.is_empty() {
        return None;
    }
    Some(dispatch)
}

fn parse_result_dispatch_conditional(node: Node) -> Option<ResultDispatchSyntax> {
    let node = unwrap_result_dispatch_expression(node);
    if node.is_nil() || node.kind() != SyntaxKind::ConditionalExpression {
        return None;
    }

    let mut dispatch = ResultDispatchSyntax::default();
    let mut current = node;
    while current.is_some() && current.kind() == SyntaxKind::ConditionalExpression {
        let condition = current.condition();
        let conditional_when_true = current.when_true();
        let conditional_when_false = current.when_false();
        if condition.is_nil() || conditional_when_true.is_nil() || conditional_when_false.is_nil() {
            return None;
        }
        let when_true = unwrap_result_dispatch_expression(conditional_when_true);
        if when_true.is_nil() || when_true.kind() == SyntaxKind::ConditionalExpression {
            return None;
        }
        dispatch.branches.push(ResultDispatchBranch {
            condition: new_dispatch_condition(
                DispatchConditionKind::Predicate,
                condition,
                condition,
                Node::NIL,
            ),
            result: conditional_when_true,
        });

        let when_false = unwrap_result_dispatch_expression(conditional_when_false);
        if when_false.is_some() && when_false.kind() == SyntaxKind::ConditionalExpression {
            current = when_false;
            continue;
        }
        dispatch.fallback = conditional_when_false;
        current = Node::NIL;
    }
    if dispatch.branches.is_empty() || dispatch.fallback.is_nil() {
        return None;
    }
    Some(dispatch)
}

fn parse_result_dispatch_if_else(node: Node) -> Option<ResultDispatchSyntax> {
    if node.is_nil() || node.kind() != SyntaxKind::IfStatement {
        return None;
    }
    let mut dispatch = ResultDispatchSyntax::default();
    let mut current = node;
    while current.is_some() && current.kind() == SyntaxKind::IfStatement {
        let statement_expression = current.expression();
        let then_statement = current.then_statement();
        let else_statement = current.else_statement();
        if statement_expression.is_nil() || then_statement.is_nil() {
            return None;
        }
        let result = single_result_dispatch_embedded_return(then_statement);
        if result.is_nil() {
            return None;
        }
        dispatch.branches.push(ResultDispatchBranch {
            condition: new_dispatch_condition(
                DispatchConditionKind::Predicate,
                statement_expression,
                statement_expression,
                Node::NIL,
            ),
            result,
        });

        if else_statement.is_nil() {
            current = Node::NIL;
            continue;
        }
        if else_statement.kind() == SyntaxKind::IfStatement {
            current = else_statement;
            continue;
        }
        dispatch.fallback = single_result_dispatch_embedded_return(else_statement);
        if dispatch.fallback.is_nil() {
            return None;
        }
        current = Node::NIL;
    }
    if dispatch.branches.is_empty() {
        return None;
    }
    Some(dispatch)
}

fn parse_result_dispatch_sequential_ifs(statements: &[Node]) -> Option<ResultDispatchSyntax> {
    if statements.is_empty() {
        return None;
    }
    let mut dispatch = ResultDispatchSyntax::default();
    let mut branch_statements = statements;
    let last = statements[statements.len() - 1];
    if last.is_some() && last.kind() == SyntaxKind::ReturnStatement {
        let returned_expression = last.expression();
        if returned_expression.is_nil() {
            return None;
        }
        dispatch.fallback = returned_expression;
        branch_statements = &statements[..statements.len() - 1];
    }
    if branch_statements.is_empty() {
        return None;
    }

    for node in branch_statements.iter().copied() {
        if node.is_nil() || node.kind() != SyntaxKind::IfStatement {
            return None;
        }
        let statement_expression = node.expression();
        let then_statement = node.then_statement();
        if statement_expression.is_nil()
            || then_statement.is_nil()
            || node.else_statement().is_some()
        {
            return None;
        }
        let result = single_result_dispatch_embedded_return(then_statement);
        if result.is_nil() {
            return None;
        }
        dispatch.branches.push(ResultDispatchBranch {
            condition: new_dispatch_condition(
                DispatchConditionKind::Predicate,
                statement_expression,
                statement_expression,
                Node::NIL,
            ),
            result,
        });
    }
    Some(dispatch)
}

fn new_dispatch_condition(
    kind: DispatchConditionKind,
    source: Node,
    subject: Node,
    value: Node,
) -> DispatchCondition {
    let mut condition = DispatchCondition {
        kind,
        source,
        subject,
        value,
        tag_subject: Node::NIL,
        tag_value: Node::NIL,
    };
    (condition.tag_subject, condition.tag_value) = dispatch_condition_tag_nodes(condition);
    condition
}

fn dispatch_condition_tag_nodes(condition: DispatchCondition) -> (Node, Node) {
    match condition.kind {
        DispatchConditionKind::Predicate => parse_tag_match(condition.subject),
        DispatchConditionKind::SwitchCase => {
            let (subject, ok) = dispatch_tag_subject(condition.subject);
            if ok {
                return (subject, condition.value);
            }
            (Node::NIL, Node::NIL)
        }
    }
}

/// Go `ParseTagMatch`: decodes a positive equality comparison whose one
/// operand is a `_tag` property access. It returns the value owning `_tag`
/// and the expression compared with it, independent of operand order.
pub fn parse_tag_match(node: Node) -> (Node, Node) {
    let predicate = unwrap_result_dispatch_expression(node);
    if predicate.is_nil() || predicate.kind() != SyntaxKind::BinaryExpression {
        return (Node::NIL, Node::NIL);
    }
    let left = predicate.left();
    let right = predicate.right();
    let operator_token = predicate.operator_token();
    if left.is_nil()
        || right.is_nil()
        || operator_token.is_nil()
        || (operator_token.kind() != SyntaxKind::EqualsEqualsToken
            && operator_token.kind() != SyntaxKind::EqualsEqualsEqualsToken)
    {
        return (Node::NIL, Node::NIL);
    }

    let (subject, ok) = dispatch_tag_subject(left);
    if ok {
        return (subject, unwrap_result_dispatch_expression(right));
    }
    let (subject, ok) = dispatch_tag_subject(right);
    if ok {
        return (subject, unwrap_result_dispatch_expression(left));
    }
    (Node::NIL, Node::NIL)
}

fn dispatch_tag_subject(node: Node) -> (Node, bool) {
    let node = unwrap_result_dispatch_expression(node);
    if node.is_nil() || node.kind() != SyntaxKind::PropertyAccessExpression {
        return (Node::NIL, false);
    }
    let access_expression = node.expression();
    let access_name = node.name();
    if access_expression.is_nil() || access_name.is_nil() || access_name.text() != "_tag" {
        return (Node::NIL, false);
    }
    (unwrap_result_dispatch_expression(access_expression), true)
}

fn single_result_dispatch_embedded_return(statement: Node) -> Node {
    if statement.is_nil() {
        return Node::NIL;
    }
    if statement.kind() == SyntaxKind::ReturnStatement {
        return statement.expression();
    }
    if statement.kind() != SyntaxKind::Block {
        return Node::NIL;
    }
    // PORT: Go `block.Statements == nil` returns nil; the port reads it as
    // an empty list, which `singleResultDispatchReturn` also rejects.
    single_result_dispatch_return(&statement.statements().to_vec())
}

fn single_result_dispatch_return(statements: &[Node]) -> Node {
    if statements.len() != 1
        || statements[0].is_nil()
        || statements[0].kind() != SyntaxKind::ReturnStatement
    {
        return Node::NIL;
    }
    statements[0].expression()
}

/// Go `unwrapResultDispatchExpression`.
pub fn unwrap_result_dispatch_expression(node: Node) -> Node {
    let mut node = node;
    while node.is_some() {
        match node.kind() {
            SyntaxKind::ParenthesizedExpression
            | SyntaxKind::SatisfiesExpression
            | SyntaxKind::AsExpression
            | SyntaxKind::NonNullExpression
            | SyntaxKind::TypeAssertionExpression => {
                node = node.expression();
            }
            _ => return node,
        }
    }
    Node::NIL
}
