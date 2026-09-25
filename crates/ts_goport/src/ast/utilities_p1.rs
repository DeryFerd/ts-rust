//! Port of typescript-go `internal/ast/utilities.go` lines 1-905.

use crate::prelude::*;

// Atomic ids

// PORT: Go keeps `nextNodeId`/`nextSymbolId` as process-wide atomics and
// stores the lazily assigned id on the node or symbol. Our AST and symbol
// arena entries have no id slot, so the lazily assigned ids live in
// thread-local maps keyed by handle. Ids are still assigned on first request
// in request order, like Go.
thread_local! {
    static NEXT_NODE_ID: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static NEXT_SYMBOL_ID: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static NODE_IDS: RefCell<FxHashMap<Node, u64>> = RefCell::new(FxHashMap::default());
    // Dense: indexed by `SymbolId::index()`; 0 means no id yet (Go ids start at 1).
    static SYMBOL_IDS: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
}

/// The node and symbol ids of one thread (see `id_seed`).
#[derive(Clone, Debug, Default)]
pub struct IdSeed {
    next_node_id: u64,
    next_symbol_id: u64,
    node_ids: FxHashMap<Node, u64>,
    symbol_ids: Vec<u64>,
}

/// The ids assigned on this thread so far. A checker worker starts from
/// the ids of the loading thread (`install_id_seed`), so a node or symbol
/// that got an id before the checkers started keeps it on every thread.
// PORT: Go shares one atomic counter between checker goroutines, so ids
// that checkers assign race. Here each checker thread counts on its own
// from the same start, which keeps its ids deterministic.
#[must_use]
pub fn id_seed() -> IdSeed {
    IdSeed {
        next_node_id: NEXT_NODE_ID.with(std::cell::Cell::get),
        next_symbol_id: NEXT_SYMBOL_ID.with(std::cell::Cell::get),
        node_ids: NODE_IDS.with(|ids| ids.borrow().clone()),
        symbol_ids: SYMBOL_IDS.with(|ids| ids.borrow().clone()),
    }
}

/// The next node and symbol ids of this thread.
#[must_use]
pub fn next_ids() -> (u64, u64) {
    (
        NEXT_NODE_ID.with(std::cell::Cell::get),
        NEXT_SYMBOL_ID.with(std::cell::Cell::get),
    )
}

/// Makes `seed` the id state of this thread.
pub fn install_id_seed(seed: IdSeed) {
    NEXT_NODE_ID.with(|next| next.set(seed.next_node_id));
    NEXT_SYMBOL_ID.with(|next| next.set(seed.next_symbol_id));
    NODE_IDS.with(|ids| *ids.borrow_mut() = seed.node_ids);
    SYMBOL_IDS.with(|ids| *ids.borrow_mut() = seed.symbol_ids);
}

// Go: ast/utilities.go:22 GetNodeId
// PORT: Go `ast.NodeId` is a `uint64`; returned here as `u64`.
pub fn get_node_id(node: Node) -> u64 {
    NODE_IDS.with(|ids| {
        let mut ids = ids.borrow_mut();
        if let Some(id) = ids.get(&node) {
            return *id;
        }
        let id = NEXT_NODE_ID.with(|next| {
            let id = next.get() + 1;
            next.set(id);
            id
        });
        ids.insert(node, id);
        id
    })
}

// Go: ast/utilities.go:34 GetSymbolId
// PORT: Go `ast.SymbolId` is a `uint64`; returned here as `u64`. The arena
// parameter follows the contract rule for `ast` functions that take a symbol.
pub fn get_symbol_id(symbols: &SymbolArena, symbol: SymbolId) -> u64 {
    let _ = symbols;
    SYMBOL_IDS.with(|ids| {
        let mut ids = ids.borrow_mut();
        let index = symbol.index();
        if index >= ids.len() {
            ids.resize(index + 1, 0);
        }
        if ids[index] != 0 {
            return ids[index];
        }
        let id = NEXT_SYMBOL_ID.with(|next| {
            let id = next.get() + 1;
            next.set(id);
            id
        });
        ids[index] = id;
        id
    })
}

// Go: ast/utilities.go:46 GetSymbolTable
// PORT: Go takes `*SymbolTable` and allocates the map in place. The arena
// must be mutable to allocate a table.
pub fn get_symbol_table(symbols: &mut SymbolArena, data: &mut SymbolTable) -> SymbolTable {
    if data.is_nil() {
        *data = symbols.new_table();
    }
    *data
}

// Go: ast/utilities.go:53 GetMembers
pub fn get_members(symbols: &mut SymbolArena, symbol: SymbolId) -> SymbolTable {
    let mut members = symbols.sym(symbol).members;
    let table = get_symbol_table(symbols, &mut members);
    symbols.sym_mut(symbol).members = members;
    table
}

// Go: ast/utilities.go:57 GetExports
pub fn get_exports(symbols: &mut SymbolArena, symbol: SymbolId) -> SymbolTable {
    let mut exports = symbols.sym(symbol).exports;
    let table = get_symbol_table(symbols, &mut exports);
    symbols.sym_mut(symbol).exports = exports;
    table
}

// Go: ast/utilities.go:61 GetLocals
// PORT: Go writes `container.LocalsContainerData().Locals`. Installed binder
// data (`n.bind()`) is immutable, so the binder passes the mutable per-node
// bind data of the file it is binding, indexed by `NodeId::index()`.
pub fn get_locals(
    symbols: &mut SymbolArena,
    node_bind: &mut [NodeBindData],
    container: Node,
) -> SymbolTable {
    let index = container.node_id().index();
    let mut locals = node_bind[index].locals;
    let table = get_symbol_table(symbols, &mut locals);
    node_bind[index].locals = locals;
    table
}

// Determines if a node is missing (either `nil` or empty)
// Go: ast/utilities.go:66 NodeIsMissing
pub fn node_is_missing(node: Node) -> bool {
    node.is_nil()
        || node.loc().pos() == node.loc().end()
            && node.loc().pos() >= 0
            && node.kind() != SyntaxKind::EndOfFile
}

// Determines if a node is present
// Go: ast/utilities.go:71 NodeIsPresent
pub fn node_is_present(node: Node) -> bool {
    !node_is_missing(node)
}

// Determines if a node contains synthetic positions
// Go: ast/utilities.go:76 NodeIsSynthesized
pub fn node_is_synthesized(node: Node) -> bool {
    position_is_synthesized(node.loc().pos()) || position_is_synthesized(node.loc().end())
}

// Go: ast/utilities.go:80 RangeIsSynthesized
pub fn range_is_synthesized(loc: TextRange) -> bool {
    position_is_synthesized(loc.pos()) || position_is_synthesized(loc.end())
}

// Determines whether a position is synthetic
// Go: ast/utilities.go:85 PositionIsSynthesized
pub fn position_is_synthesized(pos: i32) -> bool {
    pos < 0
}

// Go: ast/utilities.go:89 FindLastVisibleNode
pub fn find_last_visible_node(nodes: &[Node]) -> Node {
    let mut from_end = 1usize;
    while from_end <= nodes.len()
        && nodes[nodes.len() - from_end]
            .flags()
            .intersects(NodeFlags::REPARSED)
    {
        from_end += 1;
    }
    if from_end <= nodes.len() {
        return nodes[nodes.len() - from_end];
    }
    Node::NIL
}

// Go: ast/utilities.go:100 NodeKindIs
pub fn node_kind_is(node: Node, kinds: &[SyntaxKind]) -> bool {
    kinds.contains(&node.kind())
}

// Go: ast/utilities.go:104 IsModifier
pub fn is_modifier(node: Node) -> bool {
    is_modifier_kind(node.kind())
}

// Go: ast/utilities.go:108 IsModifierLike
pub fn is_modifier_like(node: Node) -> bool {
    is_modifier(node) || is_decorator(node)
}

// Go: ast/utilities.go:112 IsCompoundAssignment
pub fn is_compound_assignment(token: SyntaxKind) -> bool {
    (token as u16) >= (SyntaxKind::FIRST_COMPOUND_ASSIGNMENT as u16)
        && (token as u16) <= (SyntaxKind::LAST_COMPOUND_ASSIGNMENT as u16)
}

// Go: ast/utilities.go:116 IsAssignmentExpression
pub fn is_assignment_expression(node: Node, exclude_compound_assignment: bool) -> bool {
    if node.kind() == SyntaxKind::BinaryExpression {
        let operator = node.operator_token().kind();
        return (operator == SyntaxKind::EqualsToken
            || !exclude_compound_assignment && is_assignment_operator(operator))
            && is_left_hand_side_expression(node.left());
    }
    false
}

// Go: ast/utilities.go:125 GetRightMostAssignedExpression
pub fn get_right_most_assigned_expression(node: Node) -> Node {
    let mut node = node;
    while is_assignment_expression(node, false /*excludeCompoundAssignment*/) {
        node = node.right();
    }
    node
}

// Go: ast/utilities.go:132 IsDestructuringAssignment
pub fn is_destructuring_assignment(node: Node) -> bool {
    if is_assignment_expression(node, true /*excludeCompoundAssignment*/) {
        let kind = node.left().kind();
        return kind == SyntaxKind::ObjectLiteralExpression
            || kind == SyntaxKind::ArrayLiteralExpression;
    }
    false
}

// Go: ast/utilities.go:140 IsObjectBindingOrAssignmentElement
pub fn is_object_binding_or_assignment_element(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::BindingElement
            | SyntaxKind::PropertyAssignment
            | SyntaxKind::ShorthandPropertyAssignment
            | SyntaxKind::SpreadAssignment
    )
}

// Go: ast/utilities.go:151 IsArrayBindingOrAssignmentElement
pub fn is_array_binding_or_assignment_element(node: Node) -> bool {
    match node.kind() {
        SyntaxKind::BindingElement
        | SyntaxKind::OmittedExpression
        | SyntaxKind::SpreadElement
        | SyntaxKind::ArrayLiteralExpression
        | SyntaxKind::ObjectLiteralExpression
        | SyntaxKind::Identifier
        | SyntaxKind::PropertyAccessExpression
        | SyntaxKind::ElementAccessExpression => return true,
        _ => {}
    }
    is_assignment_expression(node, true /*excludeCompoundAssignment*/)
}

// Go: ast/utilities.go:166 IsBindingPattern
pub fn is_binding_pattern(node: Node) -> bool {
    node.kind() == SyntaxKind::ObjectBindingPattern
        || node.kind() == SyntaxKind::ArrayBindingPattern
}

// Go: ast/utilities.go:170 IsForInOrOfStatement
pub fn is_for_in_or_of_statement(node: Node) -> bool {
    node.is_some()
        && (node.kind() == SyntaxKind::ForInStatement || node.kind() == SyntaxKind::ForOfStatement)
}

// A node is an assignment target if it is on the left hand side of an '=' token, if it is parented by a property
// assignment in an object literal that is an assignment target, or if it is parented by an array literal that is
// an assignment target. Examples include 'a = xxx', '{ p: a } = xxx', '[{ a }] = xxx'.
// (Note that `p` is not a target in the above examples, only `a`.)
// Go: ast/utilities.go:178 IsAssignmentTarget
pub fn is_assignment_target(node: Node) -> bool {
    get_assignment_target(node).is_some()
}

// Returns the BinaryExpression, PrefixUnaryExpression, PostfixUnaryExpression, or ForInOrOfStatement that references
// the given node as an assignment target
// Go: ast/utilities.go:184 GetAssignmentTarget
pub fn get_assignment_target(node: Node) -> Node {
    let mut node = node;
    loop {
        let parent = node.parent();
        match parent.kind() {
            SyntaxKind::BinaryExpression => {
                if is_assignment_operator(parent.operator_token().kind()) && parent.left() == node {
                    return parent;
                }
                return Node::NIL;
            }
            SyntaxKind::PrefixUnaryExpression => {
                if parent.operator() == SyntaxKind::PlusPlusToken
                    || parent.operator() == SyntaxKind::MinusMinusToken
                {
                    return parent;
                }
                return Node::NIL;
            }
            SyntaxKind::PostfixUnaryExpression => {
                if parent.operator() == SyntaxKind::PlusPlusToken
                    || parent.operator() == SyntaxKind::MinusMinusToken
                {
                    return parent;
                }
                return Node::NIL;
            }
            SyntaxKind::ForInStatement | SyntaxKind::ForOfStatement => {
                if parent.initializer() == node {
                    return parent;
                }
                return Node::NIL;
            }
            SyntaxKind::ParenthesizedExpression
            | SyntaxKind::ArrayLiteralExpression
            | SyntaxKind::SpreadElement
            | SyntaxKind::NonNullExpression => {
                node = parent;
            }
            SyntaxKind::SpreadAssignment => {
                node = parent.parent();
            }
            SyntaxKind::ShorthandPropertyAssignment => {
                if parent.name() != node {
                    return Node::NIL;
                }
                node = parent.parent();
            }
            SyntaxKind::PropertyAssignment => {
                if parent.name() == node {
                    return Node::NIL;
                }
                node = parent.parent();
            }
            _ => return Node::NIL,
        }
    }
}

// Go: ast/utilities.go:228 IsLogicalBinaryOperator
pub fn is_logical_binary_operator(token: SyntaxKind) -> bool {
    token == SyntaxKind::BarBarToken || token == SyntaxKind::AmpersandAmpersandToken
}

// Go: ast/utilities.go:232 IsLogicalOrCoalescingBinaryOperator
pub fn is_logical_or_coalescing_binary_operator(token: SyntaxKind) -> bool {
    is_logical_binary_operator(token) || token == SyntaxKind::QuestionQuestionToken
}

// Go: ast/utilities.go:236 IsLogicalOrCoalescingBinaryExpression
pub fn is_logical_or_coalescing_binary_expression(expr: Node) -> bool {
    is_binary_expression(expr)
        && is_logical_or_coalescing_binary_operator(expr.operator_token().kind())
}

// Go: ast/utilities.go:240 IsLogicalOrCoalescingAssignmentExpression
pub fn is_logical_or_coalescing_assignment_expression(expr: Node) -> bool {
    is_binary_expression(expr)
        && is_logical_or_coalescing_assignment_operator(expr.operator_token().kind())
}

// Go: ast/utilities.go:244 IsLogicalExpression
pub fn is_logical_expression(node: Node) -> bool {
    let mut node = node;
    loop {
        if node.kind() == SyntaxKind::ParenthesizedExpression {
            node = node.expression();
        } else if node.kind() == SyntaxKind::PrefixUnaryExpression
            && node.operator() == SyntaxKind::ExclamationToken
        {
            node = node.operand();
        } else {
            return is_logical_or_coalescing_binary_expression(node);
        }
    }
}

// Go: ast/utilities.go:256 IsAccessor
pub fn is_accessor(node: Node) -> bool {
    node.kind() == SyntaxKind::GetAccessor || node.kind() == SyntaxKind::SetAccessor
}

// Go: ast/utilities.go:260 IsPropertyNameLiteral
pub fn is_property_name_literal(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::Identifier
            | SyntaxKind::StringLiteral
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::NumericLiteral
    )
}

// Go: ast/utilities.go:271 IsMemberName
pub fn is_member_name(node: Node) -> bool {
    node.kind() == SyntaxKind::Identifier || node.kind() == SyntaxKind::PrivateIdentifier
}

// Go: ast/utilities.go:275 IsEntityName
pub fn is_entity_name(node: Node) -> bool {
    node.kind() == SyntaxKind::Identifier || node.kind() == SyntaxKind::QualifiedName
}

// Go: ast/utilities.go:279 IsPropertyName
pub fn is_property_name(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::Identifier
            | SyntaxKind::PrivateIdentifier
            | SyntaxKind::StringLiteral
            | SyntaxKind::NumericLiteral
            | SyntaxKind::ComputedPropertyName
    )
}

// Return true if the given identifier is classified as an IdentifierName by inspecting the parent of the node
// Go: ast/utilities.go:292 IsIdentifierName
pub fn is_identifier_name(node: Node) -> bool {
    let parent = node.parent();
    match parent.kind() {
        SyntaxKind::PropertyDeclaration
        | SyntaxKind::PropertySignature
        | SyntaxKind::MethodDeclaration
        | SyntaxKind::MethodSignature
        | SyntaxKind::GetAccessor
        | SyntaxKind::SetAccessor
        | SyntaxKind::EnumMember
        | SyntaxKind::PropertyAssignment
        | SyntaxKind::PropertyAccessExpression => parent.name() == node,
        SyntaxKind::QualifiedName => parent.right() == node,
        SyntaxKind::BindingElement => parent.property_name() == node,
        SyntaxKind::ImportSpecifier => parent.property_name() == node,
        SyntaxKind::ExportSpecifier
        | SyntaxKind::JsxAttribute
        | SyntaxKind::JsxSelfClosingElement
        | SyntaxKind::JsxOpeningElement
        | SyntaxKind::JsxClosingElement => true,
        _ => false,
    }
}

// Go: ast/utilities.go:310 IsPushOrUnshiftIdentifier
pub fn is_push_or_unshift_identifier(node: Node) -> bool {
    let text = node.text();
    text == "push" || text == "unshift"
}

// Go: ast/utilities.go:315 IsBooleanLiteral
pub fn is_boolean_literal(node: Node) -> bool {
    node.kind() == SyntaxKind::TrueKeyword || node.kind() == SyntaxKind::FalseKeyword
}

// Go: ast/utilities.go:319 IsLiteralExpression
pub fn is_literal_expression(node: Node) -> bool {
    is_literal_kind(node.kind())
}

// Go: ast/utilities.go:323 IsStringLiteralLike
pub fn is_string_literal_like(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::StringLiteral | SyntaxKind::NoSubstitutionTemplateLiteral
    )
}

// Go: ast/utilities.go:331 IsStringOrNumericLiteralLike
pub fn is_string_or_numeric_literal_like(node: Node) -> bool {
    is_string_literal_like(node) || is_numeric_literal(node)
}

// Go: ast/utilities.go:335 IsSignedNumericLiteral
pub fn is_signed_numeric_literal(node: Node) -> bool {
    if node.kind() == SyntaxKind::PrefixUnaryExpression {
        return (node.operator() == SyntaxKind::PlusToken
            || node.operator() == SyntaxKind::MinusToken)
            && is_numeric_literal(node.operand());
    }
    false
}

// Determines if a node is part of an OptionalChain
// Go: ast/utilities.go:344 IsOptionalChain
pub fn is_optional_chain(node: Node) -> bool {
    if node.flags().intersects(NodeFlags::OPTIONAL_CHAIN) {
        match node.kind() {
            SyntaxKind::PropertyAccessExpression
            | SyntaxKind::ElementAccessExpression
            | SyntaxKind::CallExpression
            | SyntaxKind::NonNullExpression => return true,
            _ => {}
        }
    }
    false
}

// Go: ast/utilities.go:357 getQuestionDotToken
fn get_question_dot_token(node: Node) -> Node {
    node.question_dot_token()
}

// Determines if node is the root expression of an OptionalChain
// Go: ast/utilities.go:362 IsOptionalChainRoot
pub fn is_optional_chain_root(node: Node) -> bool {
    is_optional_chain(node)
        && !is_non_null_expression(node)
        && get_question_dot_token(node).is_some()
}

// Determines whether a node is the outermost `OptionalChain` in an ECMAScript `OptionalExpression`:
//
//  1. For `a?.b.c`, the outermost chain is `a?.b.c` (`c` is the end of the chain starting at `a?.`)
//  2. For `a?.b!`, the outermost chain is `a?.b` (`b` is the end of the chain starting at `a?.`)
//  3. For `(a?.b.c).d`, the outermost chain is `a?.b.c` (`c` is the end of the chain starting at `a?.` since parens end the chain)
//  4. For `a?.b.c?.d`, both `a?.b.c` and `a?.b.c?.d` are outermost (`c` is the end of the chain starting at `a?.`, and `d` is
//     the end of the chain starting at `c?.`)
//  5. For `a?.(b?.c).d`, both `b?.c` and `a?.(b?.c)d` are outermost (`c` is the end of the chain starting at `b`, and `d` is
//     the end of the chain starting at `a?.`)
// Go: ast/utilities.go:375 IsOutermostOptionalChain
pub fn is_outermost_optional_chain(node: Node) -> bool {
    let parent = node.parent();
    !is_optional_chain(parent) || // cases 1, 2, and 3
        is_optional_chain_root(parent) || // case 4
        node != parent.expression() // case 5
}

// Determines whether a node is the expression preceding an optional chain (i.e. `a` in `a?.b`).
// Go: ast/utilities.go:383 IsExpressionOfOptionalChainRoot
pub fn is_expression_of_optional_chain_root(node: Node) -> bool {
    is_optional_chain_root(node.parent()) && node.parent().expression() == node
}

// Go: ast/utilities.go:387 IsNullishCoalesce
pub fn is_nullish_coalesce(node: Node) -> bool {
    node.kind() == SyntaxKind::BinaryExpression
        && node.operator_token().kind() == SyntaxKind::QuestionQuestionToken
}

// Go: ast/utilities.go:391 IsAssertionExpression
pub fn is_assertion_expression(node: Node) -> bool {
    let kind = node.kind();
    kind == SyntaxKind::TypeAssertionExpression || kind == SyntaxKind::AsExpression
}

// Go: ast/utilities.go:396 isLeftHandSideExpressionKind
fn is_left_hand_side_expression_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::PropertyAccessExpression
            | SyntaxKind::ElementAccessExpression
            | SyntaxKind::NewExpression
            | SyntaxKind::CallExpression
            | SyntaxKind::JsxElement
            | SyntaxKind::JsxSelfClosingElement
            | SyntaxKind::JsxFragment
            | SyntaxKind::TaggedTemplateExpression
            | SyntaxKind::ArrayLiteralExpression
            | SyntaxKind::ParenthesizedExpression
            | SyntaxKind::ObjectLiteralExpression
            | SyntaxKind::ClassExpression
            | SyntaxKind::FunctionExpression
            | SyntaxKind::Identifier
            | SyntaxKind::PrivateIdentifier
            | SyntaxKind::RegularExpressionLiteral
            | SyntaxKind::NumericLiteral
            | SyntaxKind::BigIntLiteral
            | SyntaxKind::StringLiteral
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::TemplateExpression
            | SyntaxKind::FalseKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::ThisKeyword
            | SyntaxKind::TrueKeyword
            | SyntaxKind::SuperKeyword
            | SyntaxKind::NonNullExpression
            | SyntaxKind::ExpressionWithTypeArguments
            | SyntaxKind::MetaProperty
            | SyntaxKind::ImportKeyword
            | SyntaxKind::MissingDeclaration
    )
}

// Determines whether a node is a LeftHandSideExpression based only on its kind.
// Go: ast/utilities.go:411 IsLeftHandSideExpression
pub fn is_left_hand_side_expression(node: Node) -> bool {
    is_left_hand_side_expression_kind(skip_partially_emitted_expressions(node).kind())
}

// Go: ast/utilities.go:415 isUnaryExpressionKind
fn is_unary_expression_kind(kind: SyntaxKind) -> bool {
    match kind {
        SyntaxKind::PrefixUnaryExpression
        | SyntaxKind::PostfixUnaryExpression
        | SyntaxKind::DeleteExpression
        | SyntaxKind::TypeOfExpression
        | SyntaxKind::VoidExpression
        | SyntaxKind::AwaitExpression
        | SyntaxKind::TypeAssertionExpression => true,
        _ => is_left_hand_side_expression_kind(kind),
    }
}

// Determines whether a node is a UnaryExpression based only on its kind.
// Go: ast/utilities.go:430 IsUnaryExpression
pub fn is_unary_expression(node: Node) -> bool {
    is_unary_expression_kind(skip_partially_emitted_expressions(node).kind())
}

// Go: ast/utilities.go:434 isExpressionKind
fn is_expression_kind(kind: SyntaxKind) -> bool {
    match kind {
        SyntaxKind::ConditionalExpression
        | SyntaxKind::YieldExpression
        | SyntaxKind::ArrowFunction
        | SyntaxKind::BinaryExpression
        | SyntaxKind::SpreadElement
        | SyntaxKind::AsExpression
        | SyntaxKind::OmittedExpression
        | SyntaxKind::PartiallyEmittedExpression
        | SyntaxKind::SatisfiesExpression => true,
        _ => is_unary_expression_kind(kind),
    }
}

// Determines whether a node is an expression based only on its kind.
// Go: ast/utilities.go:451 IsExpression
pub fn is_expression(node: Node) -> bool {
    is_expression_kind(skip_partially_emitted_expressions(node).kind())
}

// Go: ast/utilities.go:455 IsCommaExpression
pub fn is_comma_expression(node: Node) -> bool {
    node.kind() == SyntaxKind::BinaryExpression
        && node.operator_token().kind() == SyntaxKind::CommaToken
}

// Go: ast/utilities.go:459 IsCommaSequence
pub fn is_comma_sequence(node: Node) -> bool {
    is_comma_expression(node)
}

// Go: ast/utilities.go:463 IsIterationStatement
pub fn is_iteration_statement(node: Node, look_in_labeled_statements: bool) -> bool {
    match node.kind() {
        SyntaxKind::ForStatement
        | SyntaxKind::ForInStatement
        | SyntaxKind::ForOfStatement
        | SyntaxKind::DoStatement
        | SyntaxKind::WhileStatement => true,
        SyntaxKind::LabeledStatement => {
            look_in_labeled_statements
                && is_iteration_statement(node.statement(), look_in_labeled_statements)
        }
        _ => false,
    }
}

// Determines if a node is a property or element access expression
// Go: ast/utilities.go:479 IsAccessExpression
pub fn is_access_expression(node: Node) -> bool {
    node.kind() == SyntaxKind::PropertyAccessExpression
        || node.kind() == SyntaxKind::ElementAccessExpression
}

// Go: ast/utilities.go:483 isFunctionLikeDeclarationKind
fn is_function_like_declaration_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::FunctionDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::Constructor
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ArrowFunction
    )
}

// Determines if a node is function-like (but is not a signature declaration)
// Go: ast/utilities.go:498 IsFunctionLikeDeclaration
pub fn is_function_like_declaration(node: Node) -> bool {
    // TODO(rbuckton): Move `node != nil` test to call sites
    node.is_some() && is_function_like_declaration_kind(node.kind())
}

// Go: ast/utilities.go:503 IsFunctionLikeKind
pub fn is_function_like_kind(kind: SyntaxKind) -> bool {
    match kind {
        SyntaxKind::MethodSignature
        | SyntaxKind::CallSignature
        | SyntaxKind::JsDocSignature
        | SyntaxKind::ConstructSignature
        | SyntaxKind::IndexSignature
        | SyntaxKind::FunctionType
        | SyntaxKind::ConstructorType => true,
        _ => is_function_like_declaration_kind(kind),
    }
}

// Determines if a node is function- or signature-like.
// Go: ast/utilities.go:518 IsFunctionLike
pub fn is_function_like(node: Node) -> bool {
    // TODO(rbuckton): Move `node != nil` test to call sites
    node.is_some() && is_function_like_kind(node.kind())
}

// Go: ast/utilities.go:523 IsFunctionLikeOrClassStaticBlockDeclaration
pub fn is_function_like_or_class_static_block_declaration(node: Node) -> bool {
    node.is_some() && (is_function_like(node) || is_class_static_block_declaration(node))
}

// Go: ast/utilities.go:527 IsFunctionOrSourceFile
pub fn is_function_or_source_file(node: Node) -> bool {
    is_function_like(node) || is_source_file(node)
}

// Go: ast/utilities.go:531 IsClassLike
pub fn is_class_like(node: Node) -> bool {
    node.kind() == SyntaxKind::ClassDeclaration || node.kind() == SyntaxKind::ClassExpression
}

// Go: ast/utilities.go:535 IsClassOrInterfaceLike
pub fn is_class_or_interface_like(node: Node) -> bool {
    node.kind() == SyntaxKind::ClassDeclaration
        || node.kind() == SyntaxKind::ClassExpression
        || node.kind() == SyntaxKind::InterfaceDeclaration
}

// Go: ast/utilities.go:539 IsClassElement
pub fn is_class_element(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::Constructor
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::IndexSignature
            | SyntaxKind::ClassStaticBlockDeclaration
            | SyntaxKind::SemicolonClassElement
    )
}

// Go: ast/utilities.go:554 IsMethodOrAccessor
pub fn is_method_or_accessor(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::MethodDeclaration | SyntaxKind::GetAccessor | SyntaxKind::SetAccessor
    )
}

// Go: ast/utilities.go:562 IsPrivateIdentifierClassElementDeclaration
pub fn is_private_identifier_class_element_declaration(node: Node) -> bool {
    (is_property_declaration(node) || is_method_or_accessor(node))
        && is_private_identifier(node.name())
}

// Go: ast/utilities.go:566 IsObjectLiteralOrClassExpressionMethodOrAccessor
pub fn is_object_literal_or_class_expression_method_or_accessor(node: Node) -> bool {
    let kind = node.kind();
    (kind == SyntaxKind::MethodDeclaration
        || kind == SyntaxKind::GetAccessor
        || kind == SyntaxKind::SetAccessor)
        && (node.parent().kind() == SyntaxKind::ObjectLiteralExpression
            || node.parent().kind() == SyntaxKind::ClassExpression)
}

// Go: ast/utilities.go:572 IsTypeElement
pub fn is_type_element(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::ConstructSignature
            | SyntaxKind::CallSignature
            | SyntaxKind::PropertySignature
            | SyntaxKind::MethodSignature
            | SyntaxKind::IndexSignature
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::NotEmittedTypeElement
    )
}

// Go: ast/utilities.go:587 IsObjectLiteralElement
pub fn is_object_literal_element(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::PropertyAssignment
            | SyntaxKind::ShorthandPropertyAssignment
            | SyntaxKind::SpreadAssignment
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
    )
}

// Go: ast/utilities.go:600 IsObjectLiteralMethod
pub fn is_object_literal_method(node: Node) -> bool {
    node.is_some()
        && node.kind() == SyntaxKind::MethodDeclaration
        && node.parent().kind() == SyntaxKind::ObjectLiteralExpression
}

// Go: ast/utilities.go:604 IsAutoAccessorPropertyDeclaration
pub fn is_auto_accessor_property_declaration(node: Node) -> bool {
    is_property_declaration(node) && has_accessor_modifier(node)
}

// Go: ast/utilities.go:608 IsParameterPropertyDeclaration
pub fn is_parameter_property_declaration(node: Node, parent: Node) -> bool {
    is_parameter_declaration(node)
        && has_syntactic_modifier(node, ModifierFlags::PARAMETER_PROPERTY_MODIFIER)
        && parent.kind() == SyntaxKind::Constructor
}

// Go: ast/utilities.go:612 IsJsxChild
pub fn is_jsx_child(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::JsxElement
            | SyntaxKind::JsxExpression
            | SyntaxKind::JsxSelfClosingElement
            | SyntaxKind::JsxText
            | SyntaxKind::JsxFragment
    )
}

// Go: ast/utilities.go:624 IsJsxAttributeLike
pub fn is_jsx_attribute_like(node: Node) -> bool {
    is_jsx_attribute(node) || is_jsx_spread_attribute(node)
}

// Go: ast/utilities.go:628 isDeclarationStatementKind
fn is_declaration_statement_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::FunctionDeclaration
            | SyntaxKind::MissingDeclaration
            | SyntaxKind::ClassDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::TypeAliasDeclaration
            | SyntaxKind::JsTypeAliasDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::ModuleDeclaration
            | SyntaxKind::ImportDeclaration
            | SyntaxKind::JsImportDeclaration
            | SyntaxKind::ImportEqualsDeclaration
            | SyntaxKind::ExportDeclaration
            | SyntaxKind::ExportAssignment
            | SyntaxKind::NamespaceExportDeclaration
    )
}

// Determines whether a node is a DeclarationStatement. Ideally this does not use Parent pointers, but it may use them
// to rule out a Block node that is part of `try` or `catch` or is the Block-like body of a function.
//
// NOTE: ECMA262 would just call this a Declaration
// Go: ast/utilities.go:653 IsDeclarationStatement
pub fn is_declaration_statement(node: Node) -> bool {
    is_declaration_statement_kind(node.kind())
}

// Go: ast/utilities.go:657 isStatementKindButNotDeclarationKind
fn is_statement_kind_but_not_declaration_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::BreakStatement
            | SyntaxKind::ContinueStatement
            | SyntaxKind::DebuggerStatement
            | SyntaxKind::DoStatement
            | SyntaxKind::ExpressionStatement
            | SyntaxKind::EmptyStatement
            | SyntaxKind::ForInStatement
            | SyntaxKind::ForOfStatement
            | SyntaxKind::ForStatement
            | SyntaxKind::IfStatement
            | SyntaxKind::LabeledStatement
            | SyntaxKind::ReturnStatement
            | SyntaxKind::SwitchStatement
            | SyntaxKind::ThrowStatement
            | SyntaxKind::TryStatement
            | SyntaxKind::VariableStatement
            | SyntaxKind::WhileStatement
            | SyntaxKind::WithStatement
            | SyntaxKind::NotEmittedStatement
    )
}

// Determines whether a node is a Statement that is not also a Declaration. Ideally this does not use Parent pointers,
// but it may use them to rule out a Block node that is part of `try` or `catch` or is the Block-like body of a function.
//
// NOTE: ECMA262 would just call this a Statement
// Go: ast/utilities.go:687 IsStatementButNotDeclaration
pub fn is_statement_but_not_declaration(node: Node) -> bool {
    is_statement_kind_but_not_declaration_kind(node.kind())
}

// Determines whether a node is a Statement. Ideally this does not use Parent pointers, but it may use
// them to rule out a Block node that is part of `try` or `catch` or is the Block-like body of a function.
//
// NOTE: ECMA262 would call this either a StatementListItem or ModuleListItem
// Go: ast/utilities.go:695 IsStatement
pub fn is_statement(node: Node) -> bool {
    let kind = node.kind();
    is_statement_kind_but_not_declaration_kind(kind)
        || is_declaration_statement_kind(kind)
        || is_block_statement(node)
}

// Determines whether a node is a BlockStatement. If parents are available, this ensures the Block is
// not part of a `try` statement, `catch` clause, or the Block-like body of a function
// Go: ast/utilities.go:702 isBlockStatement
fn is_block_statement(node: Node) -> bool {
    if node.kind() != SyntaxKind::Block {
        return false;
    }
    if node.parent().is_some()
        && (node.parent().kind() == SyntaxKind::TryStatement
            || node.parent().kind() == SyntaxKind::CatchClause)
    {
        return false;
    }
    !is_function_block(node)
}

// Determines whether a node is the Block-like body of a function by walking the parent of the node
// Go: ast/utilities.go:713 IsFunctionBlock
pub fn is_function_block(node: Node) -> bool {
    node.is_some()
        && node.kind() == SyntaxKind::Block
        && node.parent().is_some()
        && is_function_like(node.parent())
}

// Go: ast/utilities.go:717 IsBlockOrCatchScoped
pub fn is_block_or_catch_scoped(declaration: Node) -> bool {
    get_combined_node_flags(declaration).intersects(NodeFlags::BLOCK_SCOPED)
        || is_catch_clause_variable_declaration_or_binding_element(declaration)
}

// Go: ast/utilities.go:721 IsCatchClauseVariableDeclarationOrBindingElement
pub fn is_catch_clause_variable_declaration_or_binding_element(declaration: Node) -> bool {
    let node = get_root_declaration(declaration);
    node.kind() == SyntaxKind::VariableDeclaration
        && node.parent().kind() == SyntaxKind::CatchClause
}

// Go: ast/utilities.go:726 IsTypeNodeKind
pub fn is_type_node_kind(kind: SyntaxKind) -> bool {
    match kind {
        SyntaxKind::AnyKeyword
        | SyntaxKind::UnknownKeyword
        | SyntaxKind::NumberKeyword
        | SyntaxKind::BigIntKeyword
        | SyntaxKind::ObjectKeyword
        | SyntaxKind::BooleanKeyword
        | SyntaxKind::StringKeyword
        | SyntaxKind::SymbolKeyword
        | SyntaxKind::VoidKeyword
        | SyntaxKind::UndefinedKeyword
        | SyntaxKind::NeverKeyword
        | SyntaxKind::IntrinsicKeyword
        | SyntaxKind::ExpressionWithTypeArguments
        | SyntaxKind::JsDocAllType
        | SyntaxKind::JsDocNullableType
        | SyntaxKind::JsDocNonNullableType
        | SyntaxKind::JsDocOptionalType
        | SyntaxKind::JsDocVariadicType => return true,
        _ => {}
    }
    (kind as u16) >= (SyntaxKind::FIRST_TYPE_NODE as u16)
        && (kind as u16) <= (SyntaxKind::LAST_TYPE_NODE as u16)
}

// Go: ast/utilities.go:751 IsTypeNode
pub fn is_type_node(node: Node) -> bool {
    is_type_node_kind(node.kind())
}

// Go: ast/utilities.go:755 IsJSDocKind
pub fn is_js_doc_kind(kind: SyntaxKind) -> bool {
    (SyntaxKind::FIRST_JS_DOC_NODE as u16) <= (kind as u16)
        && (kind as u16) <= (SyntaxKind::LAST_JS_DOC_NODE as u16)
}

// Go: ast/utilities.go:759 IsJSDocTypeAssertion
pub fn is_js_doc_type_assertion(node: Node) -> bool {
    if node.is_nil() || !is_parenthesized_expression(node) || !is_in_js_file(node) {
        return false;
    }
    let expr = node.expression();
    is_as_expression(expr)
        && expr.type_().is_some()
        && expr.type_().flags().intersects(NodeFlags::REPARSED)
}

// Go: ast/utilities.go:767 IsPrologueDirective
pub fn is_prologue_directive(node: Node) -> bool {
    node.kind() == SyntaxKind::ExpressionStatement
        && node.expression().kind() == SyntaxKind::StringLiteral
}

// PORT: `crate::flags` defines the single-bit `OEK*` consts. The composite
// consts from the same Go const block are defined here.
impl OuterExpressionKinds {
    pub const OEK_ASSERTIONS: Self =
        Self(Self::OEK_TYPE_ASSERTIONS.0 | Self::OEK_NON_NULL_ASSERTIONS.0 | Self::OEK_SATISFIES.0);
    pub const OEK_ALL: Self = Self(
        Self::OEK_PARENTHESES.0
            | Self::OEK_ASSERTIONS.0
            | Self::OEK_PARTIALLY_EMITTED_EXPRESSIONS.0
            | Self::OEK_EXPRESSIONS_WITH_TYPE_ARGUMENTS.0,
    );
    pub const OEK_ALL_EXCEPT_ASSERTIONS_OR_EXPRESSIONS_WITH_TYPE_ARGUMENTS: Self = Self(
        Self::OEK_ALL.0 & !Self::OEK_ASSERTIONS.0 & !Self::OEK_EXPRESSIONS_WITH_TYPE_ARGUMENTS.0,
    );
    pub const OEK_EXPRESSION_TYPE_PASSTHROUGH: Self =
        Self(Self::OEK_PARENTHESES.0 | Self::OEK_ASSIGNMENTS.0 | Self::OEK_COMMA.0);
}

// Determines whether node is an "outer expression" of the provided kinds
// Go: ast/utilities.go:791 IsOuterExpression
pub fn is_outer_expression(node: Node, kinds: OuterExpressionKinds) -> bool {
    match node.kind() {
        SyntaxKind::ParenthesizedExpression => {
            return kinds.intersects(OuterExpressionKinds::OEK_PARENTHESES)
                && !(kinds.intersects(OuterExpressionKinds::OEK_EXCLUDE_JS_DOC_TYPE_ASSERTION)
                    && is_js_doc_type_assertion(node));
        }
        SyntaxKind::TypeAssertionExpression | SyntaxKind::AsExpression => {
            return kinds.intersects(OuterExpressionKinds::OEK_TYPE_ASSERTIONS);
        }
        SyntaxKind::SatisfiesExpression => {
            return kinds.intersects(
                OuterExpressionKinds::OEK_EXPRESSIONS_WITH_TYPE_ARGUMENTS
                    | OuterExpressionKinds::OEK_SATISFIES,
            );
        }
        SyntaxKind::ExpressionWithTypeArguments => {
            return kinds.intersects(OuterExpressionKinds::OEK_EXPRESSIONS_WITH_TYPE_ARGUMENTS);
        }
        SyntaxKind::NonNullExpression => {
            return kinds.intersects(OuterExpressionKinds::OEK_NON_NULL_ASSERTIONS);
        }
        SyntaxKind::PartiallyEmittedExpression => {
            return kinds.intersects(OuterExpressionKinds::OEK_PARTIALLY_EMITTED_EXPRESSIONS);
        }
        SyntaxKind::BinaryExpression => match node.operator_token().kind() {
            SyntaxKind::EqualsToken => {
                return kinds.intersects(OuterExpressionKinds::OEK_ASSIGNMENTS);
            }
            SyntaxKind::CommaToken => {
                return kinds.intersects(OuterExpressionKinds::OEK_COMMA);
            }
            _ => {}
        },
        _ => {}
    }
    false
}

// Descends into an expression, skipping past "outer expressions" of the provided kinds
// Go: ast/utilities.go:817 SkipOuterExpressions
pub fn skip_outer_expressions(node: Node, kinds: OuterExpressionKinds) -> Node {
    let mut node = node;
    while is_outer_expression(node, kinds) {
        if is_binary_expression(node) {
            node = node.right();
        } else {
            node = node.expression();
        }
    }
    node
}

// Skips past the parentheses of an expression
// Go: ast/utilities.go:829 SkipParentheses
pub fn skip_parentheses(node: Node) -> Node {
    skip_outer_expressions(node, OuterExpressionKinds::OEK_PARENTHESES)
}

// Go: ast/utilities.go:833 SkipTypeParentheses
pub fn skip_type_parentheses(node: Node) -> Node {
    let mut node = node;
    while is_parenthesized_type_node(node) {
        node = node.type_();
    }
    node
}

// Go: ast/utilities.go:840 SkipPartiallyEmittedExpressions
pub fn skip_partially_emitted_expressions(node: Node) -> Node {
    skip_outer_expressions(
        node,
        OuterExpressionKinds::OEK_PARTIALLY_EMITTED_EXPRESSIONS,
    )
}

// Walks up the parents of a parenthesized expression to find the containing node
// Go: ast/utilities.go:845 WalkUpParenthesizedExpressions
pub fn walk_up_parenthesized_expressions(node: Node) -> Node {
    let mut node = node;
    while node.is_some() && node.kind() == SyntaxKind::ParenthesizedExpression {
        node = node.parent();
    }
    node
}

// Walks up the parents of a parenthesized type to find the containing node
// Go: ast/utilities.go:853 WalkUpParenthesizedTypes
pub fn walk_up_parenthesized_types(node: Node) -> Node {
    let mut node = node;
    while node.is_some() && node.kind() == SyntaxKind::ParenthesizedType {
        node = node.parent();
    }
    node
}

// Walks up the parents of a node to find the containing SourceFile
// Go: ast/utilities.go:861 GetSourceFileOfNode
// PORT: a frozen store node whose parent walk ends at its store root gets
// that root in O(1) (`ast::store::frozen_source_file_of_node`). Other nodes
// (synthetic nodes, nodes before the freeze) walk the parents like Go.
pub fn get_source_file_of_node(node: Node) -> Node {
    if let Some(root) = frozen_source_file_of_node(node) {
        debug_assert_eq!(root, walk_to_source_file(node));
        return root;
    }
    walk_to_source_file(node)
}

/// The Go `GetSourceFileOfNode` parent walk.
fn walk_to_source_file(node: Node) -> Node {
    let mut node = node;
    while node.is_some() {
        if node.kind() == SyntaxKind::SourceFile {
            return node;
        }
        node = node.parent();
    }
    Node::NIL
}

// Go: ast/utilities.go:877 newParentInChildrenSetter
// PORT: Go keeps `parent` in a closure state and recurses through
// `node.ForEachChild(state.visit)`. Rust carries the same state in a
// struct. Go pools the closure with `sync.Pool`; that is only an
// allocation cache, so it is not ported.
struct ParentInChildrenSetter {
    parent: Node,
}

impl ParentInChildrenSetter {
    fn visit(&mut self, node: Node) -> bool {
        if self.parent.is_some() {
            crate::ast::synthetic::set_node_parent(node, self.parent);
        }
        let save_parent = self.parent;
        self.parent = node;
        node.for_each_child(|child| self.visit(child));
        self.parent = save_parent;
        false
    }
}

fn new_parent_in_children_setter() -> ParentInChildrenSetter {
    ParentInChildrenSetter { parent: Node::NIL }
}

// Go: ast/utilities.go:899 SetParentInChildren
pub fn set_parent_in_children(node: Node) {
    let mut f = new_parent_in_children_setter();
    f.visit(node);
}
