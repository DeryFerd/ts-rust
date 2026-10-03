use crate::ls::prelude::*;

// Port of Go `ls/completions.go` lines 3499-4878: commit characters,
// scopes, object, class and JSX completion containers, member filters,
// completion item defaults, label and JSX closing tag completions,
// `createLSPCompletionItem`, completion list blockers, client capability
// checks, argument info for completions and the `Source*` constants.

use crate::frontend::scanner::scanner_p1::utf8_decode_last_rune_in_string;

// Go: completions.go:4094 computeCommitCharactersAndIsNewIdentifier
// PORT: Go returns one of the shared package slices (`allCommitCharacters`,
// `noCommaCommitCharacters`, `emptyCommitCharacters`); Rust returns an owned
// copy. None of them is nil in Go, so the result is a plain `Vec`.
pub fn compute_commit_characters_and_is_new_identifier(
    context_token: Node,
    file: Node,
    position: i32,
) -> (bool, Vec<String>) {
    let all_commit_characters = || -> Vec<String> {
        ALL_COMMIT_CHARACTERS
            .iter()
            .map(|s| s.to_string())
            .collect()
    };
    let no_comma_commit_characters = || -> Vec<String> {
        NO_COMMA_COMMIT_CHARACTERS
            .iter()
            .map(|s| s.to_string())
            .collect()
    };
    let empty_commit_characters = || -> Vec<String> {
        EMPTY_COMMIT_CHARACTERS
            .iter()
            .map(|s| s.to_string())
            .collect()
    };

    if context_token.is_nil() {
        return (false, all_commit_characters());
    }
    let containing_node_kind = context_token.parent().kind();
    let token_kind = keyword_for_node(context_token);
    // Previous token may have been a keyword that was converted to an identifier.
    match token_kind {
        SyntaxKind::CommaToken => match containing_node_kind {
            // func( a, |
            // new C(a, |
            SyntaxKind::CallExpression | SyntaxKind::NewExpression => {
                let expression = context_token.parent().expression();
                // func\n(a, |
                if get_line_of_position(file, expression.end())
                    != get_line_of_position(file, position)
                {
                    return (true, no_comma_commit_characters());
                }
                return (true, all_commit_characters());
            }
            // const x = (a, |
            SyntaxKind::BinaryExpression => {
                return (true, no_comma_commit_characters());
            }
            // constructor( a, | /* public, protected, private keywords are allowed here, so show completion */
            // var x: (s: string, list|
            // const obj = { x, |
            SyntaxKind::Constructor
            | SyntaxKind::FunctionType
            | SyntaxKind::ObjectLiteralExpression => {
                return (true, empty_commit_characters());
            }
            // [a, |
            SyntaxKind::ArrayLiteralExpression => {
                return (true, all_commit_characters());
            }
            _ => {
                return (false, all_commit_characters());
            }
        },
        SyntaxKind::OpenParenToken => match containing_node_kind {
            // func( |
            // new C(a|
            SyntaxKind::CallExpression | SyntaxKind::NewExpression => {
                let expression = context_token.parent().expression();
                // func\n( |
                if get_line_of_position(file, expression.end())
                    != get_line_of_position(file, position)
                {
                    return (true, no_comma_commit_characters());
                }
                return (true, all_commit_characters());
            }
            // const x = (a|
            SyntaxKind::ParenthesizedExpression => {
                return (true, no_comma_commit_characters());
            }
            // constructor( |
            // function F(pred: (a| /* this can become an arrow function, where 'a' is the argument */
            SyntaxKind::Constructor | SyntaxKind::ParenthesizedType => {
                return (true, empty_commit_characters());
            }
            _ => {
                return (false, all_commit_characters());
            }
        },
        SyntaxKind::OpenBracketToken => match containing_node_kind {
            // [ |
            // [ | : string ]
            // [ | : string ]
            // [ |    /* this can become an index signature */
            SyntaxKind::ArrayLiteralExpression
            | SyntaxKind::IndexSignature
            | SyntaxKind::TupleType
            | SyntaxKind::ComputedPropertyName => {
                return (true, all_commit_characters());
            }
            _ => {
                return (false, all_commit_characters());
            }
        },
        // module |
        // namespace |
        // import |
        SyntaxKind::ModuleKeyword | SyntaxKind::NamespaceKeyword | SyntaxKind::ImportKeyword => {
            return (true, empty_commit_characters());
        }
        SyntaxKind::DotToken => match containing_node_kind {
            // module A.|
            SyntaxKind::ModuleDeclaration => {
                return (true, empty_commit_characters());
            }
            _ => {
                return (false, all_commit_characters());
            }
        },
        SyntaxKind::OpenBraceToken => match containing_node_kind {
            // class A { |
            // const obj = { |
            SyntaxKind::ClassDeclaration | SyntaxKind::ObjectLiteralExpression => {
                return (true, empty_commit_characters());
            }
            _ => {
                return (false, all_commit_characters());
            }
        },
        SyntaxKind::EqualsToken => match containing_node_kind {
            // const x = a|
            // x = a|
            SyntaxKind::VariableDeclaration | SyntaxKind::BinaryExpression => {
                return (true, all_commit_characters());
            }
            _ => {
                return (false, all_commit_characters());
            }
        },
        SyntaxKind::TemplateHead => {
            // `aa ${|
            return (
                containing_node_kind == SyntaxKind::TemplateExpression,
                all_commit_characters(),
            );
        }
        SyntaxKind::TemplateMiddle => {
            // `aa ${10} dd ${|
            return (
                containing_node_kind == SyntaxKind::TemplateSpan,
                all_commit_characters(),
            );
        }
        SyntaxKind::AsyncKeyword => {
            // const obj = { async c|()
            // const obj = { async c|
            if containing_node_kind == SyntaxKind::MethodDeclaration
                || containing_node_kind == SyntaxKind::ShorthandPropertyAssignment
            {
                return (true, empty_commit_characters());
            }
            return (false, all_commit_characters());
        }
        SyntaxKind::AsteriskToken => {
            // const obj = { * c|
            if containing_node_kind == SyntaxKind::MethodDeclaration {
                return (true, empty_commit_characters());
            }
            return (false, all_commit_characters());
        }
        _ => {}
    }

    if is_class_member_completion_keyword(token_kind) {
        return (true, empty_commit_characters());
    }

    (false, all_commit_characters())
}

// Go: completions.go:4222 keywordForNode
pub fn keyword_for_node(node: Node) -> SyntaxKind {
    if is_identifier(node) {
        return identifier_to_keyword_kind(node);
    }
    node.kind()
}

// Go: completions.go:4231 getScopeNode
// Finds the first node that "embraces" the position, so that one may
// accurately aggregate locals from the closest containing scope.
pub fn get_scope_node(initial_token: Node, position: i32, file: Node) -> Node {
    let mut scope = initial_token;
    while scope.is_some() && !position_belongs_to_node(scope, position, file) {
        scope = scope.parent();
    }
    scope
}

// Go: completions.go:4239 isSnippetScope
pub fn is_snippet_scope(scope_node: Node) -> bool {
    match scope_node.kind() {
        SyntaxKind::SourceFile
        | SyntaxKind::TemplateExpression
        | SyntaxKind::JsxExpression
        | SyntaxKind::Block => true,
        _ => is_statement(scope_node),
    }
}

// Go: completions.go:4252 isProbablyGlobalType
// Determines if a type is exactly the same type resolved by the global 'self', 'global', or 'globalThis'.
pub fn is_probably_global_type(t: TypeId, file: Node, type_checker: &mut Checker) -> bool {
    // The type of `self` and `window` is the same in lib.dom.d.ts, but `window` does not exist in
    // lib.webworker.d.ts, so checking against `self` is also a check against `window` when it exists.
    let self_symbol = type_checker.get_global_symbol_exported(
        "self",
        SymbolFlags::VALUE,
        None, /*diagnostic*/
    );
    if self_symbol.is_some() && type_checker.get_type_of_symbol_at_location(self_symbol, file) == t
    {
        return true;
    }
    let global_symbol = type_checker.get_global_symbol_exported(
        "global",
        SymbolFlags::VALUE,
        None, /*diagnostic*/
    );
    if global_symbol.is_some()
        && type_checker.get_type_of_symbol_at_location(global_symbol, file) == t
    {
        return true;
    }
    let global_this_symbol = type_checker.get_global_symbol_exported(
        "globalThis",
        SymbolFlags::VALUE,
        None, /*diagnostic*/
    );
    if global_this_symbol.is_some()
        && type_checker.get_type_of_symbol_at_location(global_this_symbol, file) == t
    {
        return true;
    }
    false
}

// Go: completions.go:4270 tryGetTypeLiteralNode
pub fn try_get_type_literal_node(node: Node) -> Node {
    if node.is_nil() {
        return Node::NIL;
    }

    let parent = node.parent();
    match node.kind() {
        SyntaxKind::OpenBraceToken => {
            if is_type_literal_node(parent) {
                return parent;
            }
        }
        SyntaxKind::SemicolonToken | SyntaxKind::CommaToken | SyntaxKind::Identifier => {
            if parent.kind() == SyntaxKind::PropertySignature
                && is_type_literal_node(parent.parent())
            {
                return parent.parent();
            }
        }
        _ => {}
    }

    Node::NIL
}

// Go: completions.go:4290 getConstraintOfTypeArgumentProperty
pub fn get_constraint_of_type_argument_property(node: Node, type_checker: &mut Checker) -> TypeId {
    if node.is_nil() {
        return TypeId::NIL;
    }

    if is_type_node(node) {
        let constraint = type_checker.get_type_argument_constraint_exported(node);
        if constraint.is_some() {
            return constraint;
        }
    }

    let t = get_constraint_of_type_argument_property(node.parent(), type_checker);
    if t.is_nil() {
        return TypeId::NIL;
    }

    match node.kind() {
        SyntaxKind::PropertySignature => {
            // Try to get the reparsed node first - we may be in JSDoc.
            let reparsed = get_reparsed_node_for_node(node);
            let symbol = reparsed.symbol();
            if symbol.is_some() {
                let name = type_checker.sym(symbol).name.as_str();
                return type_checker.get_type_of_property_of_contextual_type_exported(t, name);
            }

            // In some cases, we won't have a corresponding symbol
            // (e.g. JSDoc types that never get re-attached) so we'll use
            // the name as declared by the property as a best-effort.
            let (name, ok) = try_get_text_of_property_name(reparsed.name());
            if ok {
                return type_checker.get_type_of_property_of_contextual_type_exported(t, &name);
            }

            return TypeId::NIL;
        }
        SyntaxKind::ColonToken => {
            if node.parent().kind() == SyntaxKind::PropertySignature {
                // The cursor is at a property value location like `Foo<{ x: | }`.
                // `t` already refers to the appropriate property type.
                return t;
            }
        }
        SyntaxKind::IntersectionType | SyntaxKind::TypeLiteral | SyntaxKind::UnionType => {
            return t;
        }
        SyntaxKind::OpenBracketToken => {
            return type_checker.get_element_type_of_array_type_exported(t);
        }
        _ => {}
    }

    TypeId::NIL
}

// Go: completions.go:4338 tryGetObjectLikeCompletionContainer
pub fn try_get_object_like_completion_container(
    context_token: Node,
    position: i32,
    file: Node,
) -> Node {
    if context_token.is_nil() {
        return Node::NIL;
    }

    let parent = context_token.parent();
    match context_token.kind() {
        // const x = { |
        // const x = { a: 0, |
        SyntaxKind::OpenBraceToken | SyntaxKind::CommaToken => {
            if is_object_literal_expression(parent) || is_object_binding_pattern(parent) {
                return parent;
            }
        }
        SyntaxKind::AsteriskToken => {
            if is_method_declaration(parent) && is_object_literal_expression(parent.parent()) {
                return parent.parent();
            }
        }
        SyntaxKind::AsyncKeyword => {
            if is_object_literal_expression(parent.parent()) {
                return parent.parent();
            }
        }
        SyntaxKind::Identifier => {
            if context_token.text() == "async" && is_shorthand_property_assignment(parent) {
                return parent.parent();
            } else {
                if is_object_literal_expression(parent.parent())
                    && (is_spread_assignment(parent)
                        || is_shorthand_property_assignment(parent)
                            && get_line_of_position(file, context_token.end())
                                != get_line_of_position(file, position))
                {
                    return parent.parent();
                }
                let ancestor_node = find_ancestor(parent, is_property_assignment);
                if ancestor_node.is_some()
                    && lsutil::get_last_token(ancestor_node, file) == context_token
                    && is_object_literal_expression(ancestor_node.parent())
                {
                    return ancestor_node.parent();
                }
            }
        }
        _ => {
            if parent.parent().is_some()
                && parent.parent().parent().is_some()
                && (is_method_declaration(parent.parent())
                    || is_get_accessor_declaration(parent.parent())
                    || is_set_accessor_declaration(parent.parent()))
                && is_object_literal_expression(parent.parent().parent())
            {
                return parent.parent().parent();
            }
            if is_spread_assignment(parent) && is_object_literal_expression(parent.parent()) {
                return parent.parent();
            }
            let ancestor_node = find_ancestor(parent, is_property_assignment);
            if context_token.kind() != SyntaxKind::ColonToken
                && ancestor_node.is_some()
                && lsutil::get_last_token(ancestor_node, file) == context_token
                && is_object_literal_expression(ancestor_node.parent())
            {
                return ancestor_node.parent();
            }
        }
    }

    Node::NIL
}

// Go: completions.go:4396 tryGetObjectLiteralContextualType
pub fn try_get_object_literal_contextual_type(node: Node, type_checker: &mut Checker) -> TypeId {
    let t = type_checker.get_contextual_type_exported(node, ContextFlags::NONE);
    if t.is_some() {
        return t;
    }

    let parent = walk_up_parenthesized_expressions(node.parent());
    if is_binary_expression(parent)
        && parent.operator_token().kind() == SyntaxKind::EqualsToken
        && node == parent.left()
    {
        // Object literal is assignment pattern: ({ | } = x)
        return type_checker.get_type_at_location(parent);
    }
    if is_expression(parent) {
        // f(() => (({ | })));
        return type_checker.get_contextual_type_exported(parent, ContextFlags::NONE);
    }

    TypeId::NIL
}

// Go: completions.go:4417 getPropertiesForObjectExpression
pub fn get_properties_for_object_expression(
    contextual_type: TypeId,
    completions_type: TypeId,
    obj: Node,
    type_checker: &mut Checker,
) -> Vec<SymbolId> {
    let has_completions_type = completions_type.is_some() && completions_type != contextual_type;
    let types: Vec<TypeId> = if type_checker.ty(contextual_type).is_union() {
        type_checker.ty(contextual_type).types().to_vec()
    } else {
        vec![contextual_type]
    };
    let mut filtered_types: Vec<TypeId> = Vec::new();
    for t in types {
        if type_checker.get_promised_type_of_promise(t).is_nil() {
            filtered_types.push(t);
        }
    }
    let promise_filtered_contextual_type = type_checker.get_union_type_exported(&filtered_types);

    let t = if has_completions_type
        && !type_checker
            .ty(completions_type)
            .flags
            .intersects(TypeFlags::ANY_OR_UNKNOWN)
    {
        type_checker.get_union_type_exported(&[promise_filtered_contextual_type, completions_type])
    } else {
        promise_filtered_contextual_type
    };

    // Filter out members whose only declaration is the object literal itself to avoid
    // self-fulfilling completions like:
    //
    // function f<T>(x: T) {}
    // f({ abc/**/: "" }) // `abc` is a member of `T` but only because it declares itself
    let has_declaration_other_than_self = |type_checker: &Checker, member: SymbolId| -> bool {
        let declarations = &type_checker.sym(member).declarations;
        if declarations.is_empty() {
            return true;
        }
        declarations.iter().any(|decl| decl.parent() != obj)
    };

    let properties = get_apparent_properties(t, obj, type_checker);
    if type_checker.ty(t).is_class() && contains_non_public_properties(type_checker, &properties) {
        Vec::new()
    } else if has_completions_type {
        properties
            .into_iter()
            .filter(|&member| has_declaration_other_than_self(&*type_checker, member))
            .collect()
    } else {
        properties
    }
}

// Go: completions.go:4463 getApparentProperties
// PORT: the ls package function, not the checker method of the same name.
pub fn get_apparent_properties(t: TypeId, node: Node, type_checker: &mut Checker) -> Vec<SymbolId> {
    if !type_checker.ty(t).is_union() {
        return type_checker.get_apparent_properties(t);
    }
    let member_types = type_checker.ty(t).types().to_vec();
    let mut filtered: Vec<TypeId> = Vec::new();
    for member_type in member_types {
        let excluded = type_checker
            .ty(member_type)
            .flags
            .intersects(TypeFlags::PRIMITIVE)
            || type_checker.is_array_like_type_exported(member_type)
            || type_checker.is_type_invalid_due_to_union_discriminant(member_type, node)
            || type_checker.type_has_call_or_construct_signatures_exported(member_type)
            || type_checker.ty(member_type).is_class() && {
                let apparent_properties = type_checker.get_apparent_properties(member_type);
                contains_non_public_properties(type_checker, &apparent_properties)
            };
        if !excluded {
            filtered.push(member_type);
        }
    }
    type_checker.get_all_possible_properties_of_types(&filtered)
}

// Go: completions.go:4476 containsNonPublicProperties
// PORT: Go calls the package function `checker.GetDeclarationModifierFlagsFromSymbol`;
// in Rust it is a `Checker` method (symbols live in the checker arena), so
// the checker is an extra first parameter.
pub fn contains_non_public_properties(type_checker: &mut Checker, props: &[SymbolId]) -> bool {
    props.iter().any(|&p| {
        type_checker
            .get_declaration_modifier_flags_from_symbol_exported(p)
            .intersects(ModifierFlags::NON_PUBLIC_ACCESSIBILITY_MODIFIER)
    })
}

// Go: completions.go:4484 filterObjectMembersList
// Filters out members that are already declared in the object literal or binding pattern.
// Also computes the set of existing members declared by spread assignment.
pub fn filter_object_members_list(
    contextual_member_symbols: &[SymbolId],
    existing_members: &[Node],
    file: Node,
    position: i32,
    type_checker: &mut Checker,
) -> (Vec<SymbolId>, FxHashSet<String>) {
    if existing_members.is_empty() {
        return (contextual_member_symbols.to_vec(), FxHashSet::default());
    }

    let mut members_declared_by_spread_assignment: FxHashSet<String> = FxHashSet::default();
    let mut existing_member_names: FxHashSet<String> = FxHashSet::default();
    for &member in existing_members {
        // Ignore omitted expressions for missing members.
        if member.kind() != SyntaxKind::PropertyAssignment
            && member.kind() != SyntaxKind::ShorthandPropertyAssignment
            && member.kind() != SyntaxKind::BindingElement
            && member.kind() != SyntaxKind::MethodDeclaration
            && member.kind() != SyntaxKind::GetAccessor
            && member.kind() != SyntaxKind::SetAccessor
            && member.kind() != SyntaxKind::SpreadAssignment
        {
            continue;
        }

        // If this is the current item we are editing right now, do not filter it out.
        if is_currently_editing_node(member, file, position) {
            continue;
        }

        let mut existing_name = String::new();

        if is_spread_assignment(member) {
            set_member_declared_by_spread_assignment(
                member,
                &mut members_declared_by_spread_assignment,
                type_checker,
            );
        } else if is_binding_element(member) && member.property_name().is_some() {
            // include only identifiers in completion list
            if member.property_name().kind() == SyntaxKind::Identifier {
                existing_name = member.property_name().text().to_string();
            }
        } else {
            // TODO: Account for computed property name
            // NOTE: if one only performs this step when m.name is an identifier,
            // things like '__proto__' are not filtered out.
            let name = get_name_of_declaration(member);
            if name.is_some() && is_property_name_literal(name) {
                existing_name = name.text().to_string();
            }
        }

        if !existing_name.is_empty() {
            existing_member_names.insert(existing_name);
        }
    }

    let filtered_symbols: Vec<SymbolId> = contextual_member_symbols
        .iter()
        .copied()
        .filter(|&m| !existing_member_names.contains(type_checker.sym(m).name.as_str()))
        .collect();

    (filtered_symbols, members_declared_by_spread_assignment)
}

// Go: completions.go:4545 isCurrentlyEditingNode
pub fn is_currently_editing_node(node: Node, file: Node, position: i32) -> bool {
    let start = astnav::get_start_of_node(node, file, false /*includeJSDoc*/);
    start <= position && position <= node.end()
}

// Go: completions.go:4550 setMemberDeclaredBySpreadAssignment
pub fn set_member_declared_by_spread_assignment(
    declaration: Node,
    members: &mut FxHashSet<String>,
    type_checker: &mut Checker,
) {
    let expression = declaration.expression();
    let symbol = type_checker.get_symbol_at_location_exported(expression);
    let mut t = TypeId::NIL;
    if symbol.is_some() {
        t = type_checker.get_type_of_symbol_at_location(symbol, expression);
    }
    let mut properties: Vec<SymbolId> = Vec::new();
    if t.is_some()
        && type_checker
            .ty(t)
            .flags
            .intersects(TypeFlags::STRUCTURED_TYPE)
    {
        properties = type_checker
            .ty(t)
            .as_structured_type()
            .properties()
            .to_vec();
    }
    for property in properties {
        members.insert(type_checker.sym(property).name.as_str().to_string());
    }
}

// Go: completions.go:4568 tryGetConstructorLikeCompletionContainer
// Returns the immediate owning class declaration of a context token,
// on the condition that one exists and that the context implies completion should be given.
pub fn try_get_constructor_like_completion_container(context_token: Node) -> Node {
    if context_token.is_nil() {
        return Node::NIL;
    }

    let parent = context_token.parent();
    match context_token.kind() {
        SyntaxKind::OpenParenToken | SyntaxKind::CommaToken => {
            if is_constructor_declaration(parent) {
                return parent;
            }
            return Node::NIL;
        }
        _ => {
            if is_constructor_parameter_completion(context_token) {
                return parent.parent();
            }
        }
    }
    Node::NIL
}

// Go: completions.go:4588 isConstructorParameterCompletion
pub fn is_constructor_parameter_completion(node: Node) -> bool {
    node.parent().is_some()
        && is_parameter_declaration(node.parent())
        && is_constructor_declaration(node.parent().parent())
        && (is_parameter_property_modifier(node.kind()) || is_declaration_name(node))
}

// Go: completions.go:4595 tryGetObjectTypeDeclarationCompletionContainer
// Returns the immediate owning class declaration of a context token,
// on the condition that one exists and that the context implies completion should be given.
pub fn try_get_object_type_declaration_completion_container(
    file: Node,
    context_token: Node,
    location: Node,
    position: i32,
) -> Node {
    // class c { method() { } | method2() { } }
    match location.kind() {
        SyntaxKind::SyntaxList => {
            if is_object_type_declaration(location.parent()) {
                return location.parent();
            }
            return Node::NIL;
        }
        SyntaxKind::EndOfFile => {
            let stmt_list = location.parent().statement_list();
            if !stmt_list.is_nil()
                && !stmt_list.nodes().is_empty()
                && is_object_type_declaration(stmt_list.nodes().get(stmt_list.nodes().len() - 1))
            {
                let cls = stmt_list.nodes().get(stmt_list.nodes().len() - 1);
                if astnav::find_child_of_kind(cls, SyntaxKind::CloseBraceToken, file).is_nil() {
                    return cls;
                }
            }
        }
        SyntaxKind::PrivateIdentifier => {
            if is_property_declaration(location.parent()) {
                return find_ancestor(location, is_class_like);
            }
        }
        SyntaxKind::Identifier => {
            let original_keyword_kind = identifier_to_keyword_kind(location);
            if original_keyword_kind != SyntaxKind::Unknown {
                return Node::NIL;
            }
            // class c { public prop = c| }
            if is_property_declaration(location.parent())
                && location.parent().initializer() == location
            {
                return Node::NIL;
            }
            // class c extends React.Component { a: () => 1\n compon| }
            if is_from_object_type_declaration(location) {
                return find_ancestor(location, is_object_type_declaration);
            }
        }
        _ => {}
    }

    if context_token.is_nil() {
        return Node::NIL;
    }

    // class C { blah; constructor/**/ }
    // or
    // class C { blah \n constructor/**/ }
    if location.kind() == SyntaxKind::ConstructorKeyword
        || (is_identifier(context_token)
            && is_property_declaration(context_token.parent())
            && is_class_like(location))
    {
        return find_ancestor(context_token, is_class_like);
    }

    match context_token.kind() {
        // class c { public prop = | /* global completions */ }
        SyntaxKind::EqualsToken => Node::NIL,
        // class c {getValue(): number; | }
        // class c { method() { } | }
        SyntaxKind::SemicolonToken | SyntaxKind::CloseBraceToken => {
            // class c { method() { } b| }
            if is_from_object_type_declaration(location) && location.parent().name() == location {
                return location.parent().parent();
            }
            if is_object_type_declaration(location) {
                return location;
            }
            Node::NIL
        }
        // class c { |
        // class c {getValue(): number, | }
        SyntaxKind::OpenBraceToken | SyntaxKind::CommaToken => {
            if is_object_type_declaration(context_token.parent()) {
                return context_token.parent();
            }
            Node::NIL
        }
        _ => {
            if is_object_type_declaration(location) {
                // class C extends React.Component { a: () => 1\n| }
                // class C { prop = ""\n | }
                if get_line_of_position(file, context_token.end())
                    != get_line_of_position(file, position)
                {
                    return location;
                }
                let is_valid_keyword: fn(SyntaxKind) -> bool =
                    if is_class_like(context_token.parent().parent()) {
                        is_class_member_completion_keyword
                    } else {
                        is_interface_or_type_literal_completion_keyword
                    };

                if is_valid_keyword(context_token.kind())
                    || context_token.kind() == SyntaxKind::AsteriskToken
                    || is_identifier(context_token)
                        && is_valid_keyword(identifier_to_keyword_kind(context_token))
                {
                    return context_token.parent().parent();
                }
            }

            Node::NIL
        }
    }
}

// Go: completions.go:4692 isFromObjectTypeDeclaration
pub fn is_from_object_type_declaration(node: Node) -> bool {
    node.parent().is_some()
        && is_class_or_type_element(node.parent())
        && is_object_type_declaration(node.parent().parent())
}

// Go: completions.go:4697 filterClassMembersList
// Filters out completion suggestions for class elements.
// PORT: Go reads the symbols through pointers and calls the package function
// `checker.GetDeclarationModifierFlagsFromSymbol`. In Rust both need the
// checker (symbol arena), so it is an extra first parameter.
pub fn filter_class_members_list(
    type_checker: &mut Checker,
    base_symbols: &[SymbolId],
    existing_members: &[Node],
    class_element_modifier_flags: ModifierFlags,
    file: Node,
    position: i32,
) -> Vec<SymbolId> {
    let mut existing_member_names: FxHashSet<String> = FxHashSet::default();
    for &member in existing_members {
        // Ignore omitted expressions for missing members.
        if member.kind() != SyntaxKind::PropertyDeclaration
            && member.kind() != SyntaxKind::MethodDeclaration
            && member.kind() != SyntaxKind::GetAccessor
            && member.kind() != SyntaxKind::SetAccessor
        {
            continue;
        }

        // If this is the current item we are editing right now, do not filter it out
        if is_currently_editing_node(member, file, position) {
            continue;
        }

        // Don't filter member even if the name matches if it is declared private in the list.
        if member.modifier_flags().intersects(ModifierFlags::PRIVATE) {
            continue;
        }

        // Do not filter it out if the static presence doesn't match.
        if is_static(member) != class_element_modifier_flags.intersects(ModifierFlags::STATIC) {
            continue;
        }

        let existing_name = get_property_name_for_property_name_node(member.name());
        if !existing_name.is_empty() {
            existing_member_names.insert(existing_name);
        }
    }

    base_symbols
        .iter()
        .copied()
        .filter(|&property_symbol| {
            !existing_member_names.contains(&symbol_name(&type_checker.symbols, property_symbol))
                && !type_checker.sym(property_symbol).declarations.is_empty()
                && !type_checker
                    .get_declaration_modifier_flags_from_symbol_exported(property_symbol)
                    .intersects(ModifierFlags::PRIVATE)
                && !(type_checker
                    .sym(property_symbol)
                    .value_declaration
                    .is_some()
                    && is_private_identifier_class_element_declaration(
                        type_checker.sym(property_symbol).value_declaration,
                    ))
        })
        .collect()
}

// Go: completions.go:4743 tryGetContainingJsxElement
pub fn try_get_containing_jsx_element(context_token: Node, file: Node) -> Node {
    if context_token.is_nil() {
        return Node::NIL;
    }

    let parent = context_token.parent();
    match context_token.kind() {
        SyntaxKind::GreaterThanToken
        | SyntaxKind::LessThanSlashToken
        | SyntaxKind::SlashToken
        | SyntaxKind::Identifier
        | SyntaxKind::PropertyAccessExpression
        | SyntaxKind::JsxNamespacedName
        | SyntaxKind::JsxAttributes
        | SyntaxKind::JsxAttribute
        | SyntaxKind::JsxSpreadAttribute => {
            if parent.is_some()
                && (parent.kind() == SyntaxKind::JsxSelfClosingElement
                    || parent.kind() == SyntaxKind::JsxOpeningElement)
            {
                if context_token.kind() == SyntaxKind::GreaterThanToken {
                    let preceding_token = astnav::find_preceding_token(file, context_token.pos());
                    if parent.type_arguments().is_empty()
                        || preceding_token.is_some()
                            && preceding_token.kind() == SyntaxKind::SlashToken
                    {
                        return Node::NIL;
                    }
                }
                return parent;
            } else if parent.is_some()
                && is_jsx_namespaced_name(parent)
                && parent.parent().is_some()
                && (parent.parent().kind() == SyntaxKind::JsxSelfClosingElement
                    || parent.parent().kind() == SyntaxKind::JsxOpeningElement)
            {
                return parent.parent();
            } else if parent.is_some() && parent.kind() == SyntaxKind::JsxAttribute {
                // Currently we parse JsxOpeningLikeElement as:
                //      JsxOpeningLikeElement
                //          attributes: JsxAttributes
                //             properties: NodeArray<JsxAttributeLike>
                return parent.parent().parent();
            }
        }
        // The context token is the closing } or " of an attribute, which means
        // its parent is a JsxExpression, whose parent is a JsxAttribute,
        // whose parent is a JsxOpeningLikeElement
        SyntaxKind::StringLiteral => {
            if parent.is_some()
                && (parent.kind() == SyntaxKind::JsxAttribute
                    || parent.kind() == SyntaxKind::JsxSpreadAttribute)
            {
                // Currently we parse JsxOpeningLikeElement as:
                //      JsxOpeningLikeElement
                //          attributes: JsxAttributes
                //             properties: NodeArray<JsxAttributeLike>
                return parent.parent().parent();
            }
        }
        SyntaxKind::CloseBraceToken => {
            if parent.is_some()
                && parent.kind() == SyntaxKind::JsxExpression
                && parent.parent().is_some()
                && parent.parent().kind() == SyntaxKind::JsxAttribute
            {
                // Currently we parse JsxOpeningLikeElement as:
                //      JsxOpeningLikeElement
                //          attributes: JsxAttributes
                //             properties: NodeArray<JsxAttributeLike>
                //                  each JsxAttribute can have initializer as JsxExpression
                return parent.parent().parent().parent();
            }
            if parent.is_some() && parent.kind() == SyntaxKind::JsxSpreadAttribute {
                // Currently we parse JsxOpeningLikeElement as:
                //      JsxOpeningLikeElement
                //          attributes: JsxAttributes
                //             properties: NodeArray<JsxAttributeLike>
                return parent.parent().parent();
            }
        }
        _ => {}
    }

    Node::NIL
}

// Go: completions.go:4807 filterJsxAttributes
// Filters out completion suggestions from 'symbols' according to existing JSX attributes.
// @returns Symbols to be suggested in a JSX element, barring those whose attributes
// do not occur at the current position and have not otherwise been typed.
// PORT: Go returns a pointer to the spread member set; it is never nil, so
// Rust returns the set by value.
pub fn filter_jsx_attributes(
    symbols: &[SymbolId],
    attributes: &[Node],
    file: Node,
    position: i32,
    type_checker: &mut Checker,
) -> (Vec<SymbolId>, FxHashSet<String>) {
    let mut existing_names: FxHashSet<String> = FxHashSet::default();
    let mut members_declared_by_spread_assignment: FxHashSet<String> = FxHashSet::default();
    for &attr in attributes {
        // If this is the item we are editing right now, do not filter it out.
        if is_currently_editing_node(attr, file, position) {
            continue;
        }

        if attr.kind() == SyntaxKind::JsxAttribute {
            existing_names.insert(attr.name().text().to_string());
        } else if is_jsx_spread_attribute(attr) {
            set_member_declared_by_spread_assignment(
                attr,
                &mut members_declared_by_spread_assignment,
                type_checker,
            );
        }
    }

    (
        symbols
            .iter()
            .copied()
            .filter(|&a| !existing_names.contains(type_checker.sym(a).name.as_str()))
            .collect(),
        members_declared_by_spread_assignment,
    )
}

// Go: completions.go:4833 isTypeKeywordTokenOrIdentifier
pub fn is_type_keyword_token_or_identifier(node: Node) -> bool {
    is_type_keyword_token(node)
        || is_identifier(node) && identifier_to_keyword_kind(node) == SyntaxKind::TypeKeyword
}

impl LanguageService {
    // Go: completions.go:4840 setItemDefaults
    // Returns the item defaults for completion items, if that capability is supported.
    // Otherwise, if some item default is not supported by client, sets that property on each item.
    // PORT: Go shares one `*[]string` between the defaults and every item;
    // Rust clones the list into each place.
    pub fn set_item_defaults(
        &self,
        ctx: &Context,
        position: i32,
        file: Node,
        items: &mut [CompletionItem],
        default_commit_characters: Option<&Vec<String>>,
        optional_replacement_span: Option<lsproto::Range>,
    ) -> Option<lsproto::CompletionItemDefaults> {
        let mut item_defaults: Option<lsproto::CompletionItemDefaults> = None;
        if let Some(default_commit_characters) = default_commit_characters {
            let supports_item_commit_characters = client_supports_item_commit_characters(ctx);
            if client_supports_default_commit_characters(ctx) && supports_item_commit_characters {
                item_defaults = Some(lsproto::CompletionItemDefaults {
                    commit_characters: Some(default_commit_characters.clone()),
                    ..Default::default()
                });
            } else if supports_item_commit_characters {
                for item in items.iter_mut() {
                    if item.completion_item.commit_characters.is_none() {
                        item.completion_item.commit_characters =
                            Some(default_commit_characters.clone());
                    }
                }
            }
        }
        if let Some(optional_replacement_span) = optional_replacement_span {
            // Ported from vscode ts extension.
            let (end, fidelity) = self.create_lsp_position(position, file);
            if !fidelity.is_exact() {
                return item_defaults;
            }
            let insert_range = lsproto::Range {
                start: optional_replacement_span.start,
                end,
            };
            if client_supports_default_edit_range(ctx) {
                // Go: core.OrElse(itemDefaults, &lsproto.CompletionItemDefaults{})
                let defaults = item_defaults.get_or_insert_with(Default::default);
                defaults.edit_range = Some(lsproto::RangeOrEditRangeWithInsertReplace {
                    range: None,
                    edit_range_with_insert_replace: Some(lsproto::EditRangeWithInsertReplace {
                        insert: insert_range,
                        replace: optional_replacement_span,
                    }),
                });
                for item in items.iter_mut() {
                    // If `editRange` is set, `insertText` is ignored by the client, so we need to
                    // provide `textEdit` instead.
                    if item.completion_item.insert_text.is_some()
                        && item.completion_item.text_edit.is_none()
                    {
                        let new_text = item.completion_item.insert_text.clone().unwrap_or_default();
                        item.completion_item.text_edit =
                            Some(lsproto::TextEditOrInsertReplaceEdit {
                                text_edit: None,
                                insert_replace_edit: Some(lsproto::InsertReplaceEdit {
                                    new_text,
                                    insert: insert_range,
                                    replace: optional_replacement_span,
                                }),
                            });
                        item.completion_item.insert_text = None;
                    }
                }
            } else if client_supports_item_insert_replace(ctx) {
                for item in items.iter_mut() {
                    if item.completion_item.text_edit.is_none() {
                        // Go: *core.OrElse(item.InsertText, &item.Label)
                        let new_text = match &item.completion_item.insert_text {
                            Some(insert_text) => insert_text.clone(),
                            None => item.completion_item.label.clone(),
                        };
                        item.completion_item.text_edit =
                            Some(lsproto::TextEditOrInsertReplaceEdit {
                                text_edit: None,
                                insert_replace_edit: Some(lsproto::InsertReplaceEdit {
                                    new_text,
                                    insert: insert_range,
                                    replace: optional_replacement_span,
                                }),
                            });
                    }
                }
            }
        }

        item_defaults
    }

    // Go: completions.go:4913 specificKeywordCompletionInfo
    pub fn specific_keyword_completion_info(
        &self,
        ctx: &Context,
        position: i32,
        file: Node,
        items: Vec<CompletionItem>,
        is_new_identifier_location: bool,
        optional_replacement_span: Option<lsproto::Range>,
    ) -> Option<CompletionList> {
        let mut items = items;
        let default_commit_characters = get_default_commit_characters(is_new_identifier_location);
        let item_defaults = self.set_item_defaults(
            ctx,
            position,
            file,
            &mut items,
            Some(&default_commit_characters),
            optional_replacement_span,
        );
        Some(CompletionList {
            is_incomplete: false,
            item_defaults,
            items,
            ..Default::default()
        })
    }

    // Go: completions.go:4937 getJsxClosingTagCompletion
    pub fn get_jsx_closing_tag_completion(
        &self,
        ctx: &Context,
        location: Node,
        file: Node,
        position: i32,
    ) -> Option<CompletionList> {
        // We wanna walk up the tree till we find a JSX closing element.
        let jsx_closing_element = find_ancestor_or_quit(location, |node| match node.kind() {
            SyntaxKind::JsxClosingElement => FindAncestorResult::FIND_ANCESTOR_TRUE,
            SyntaxKind::LessThanSlashToken
            | SyntaxKind::GreaterThanToken
            | SyntaxKind::Identifier
            | SyntaxKind::PropertyAccessExpression => FindAncestorResult::FIND_ANCESTOR_FALSE,
            _ => FindAncestorResult::FIND_ANCESTOR_QUIT,
        });

        if jsx_closing_element.is_nil() {
            return None;
        }

        // In the TypeScript JSX element, if such element is not defined. When users query for completion at closing tag,
        // instead of simply giving unknown value, the completion will return the tag-name of an associated opening-element.
        // For example:
        //     var x = <div> </ /*1*/
        // The completion list at "1" will contain "div>" with type any
        // And at `<div> </ /*1*/ >` (with a closing `>`), the completion list will contain "div".
        // And at property access expressions `<MainComponent.Child> </MainComponent. /*1*/ >` the completion will
        // return full closing tag with an optional replacement span
        // For example:
        //     var x = <MainComponent.Child> </     MainComponent /*1*/  >
        //     var y = <MainComponent.Child> </   /*2*/   MainComponent >
        // the completion list at "1" and "2" will contain "MainComponent.Child" with a replacement span of closing tag name
        let has_closing_angle_bracket =
            astnav::find_child_of_kind(jsx_closing_element, SyntaxKind::GreaterThanToken, file)
                .is_some();
        let tag_name = jsx_closing_element.parent().opening_element().tag_name();
        let closing_tag = get_text_of_node(tag_name);
        let full_closing_tag = closing_tag + if has_closing_angle_bracket { "" } else { ">" };
        let (optional_replacement_span, fidelity) =
            self.create_lsp_range_from_node(jsx_closing_element.tag_name(), file);
        if !fidelity.is_exact() {
            return None;
        }
        let default_commit_characters =
            get_default_commit_characters(false /*isNewIdentifierLocation*/);

        let lsp_item = self.create_lsp_completion_item(
            ctx,
            &full_closing_tag, /*name*/
            "",                /*insertText*/
            "",                /*filterText*/
            SORT_TEXT_LOCATION_PRIORITY,
            lsutil::ScriptElementKind::CLASS_ELEMENT,
            lsutil::ScriptElementKindModifier::NONE, /*kindModifiers*/
            None,                                    /*replacementSpan*/
            None,                                    /*commitCharacters*/
            None,                                    /*labelDetails*/
            file,
            position,
            true,  /*isMemberCompletion*/
            false, /*isSnippet*/
            false, /*hasAction*/
            false, /*preselect*/
            "",    /*source*/
            None,  /*autoImportEntryData*/
            // !!! jsx autoimports
            None, /*additionalTextEdits*/
            None, /*detail*/
        );
        let item = CompletionItem {
            completion_item: lsp_item,
            ..Default::default()
        };
        let mut items = vec![item];
        let item_defaults = self.set_item_defaults(
            ctx,
            position,
            file,
            &mut items,
            Some(&default_commit_characters),
            Some(optional_replacement_span),
        );

        Some(CompletionList {
            is_incomplete: false,
            item_defaults,
            items,
            ..Default::default()
        })
    }

    // Go: completions.go:5023 createLSPCompletionItem
    pub fn create_lsp_completion_item(
        &self,
        _ctx: &Context,
        name: &str,
        insert_text: &str,
        filter_text: &str,
        sort_text: &str,
        element_kind: lsutil::ScriptElementKind,
        kind_modifiers: lsutil::ScriptElementKindModifier,
        replacement_span: Option<lsproto::Range>,
        commit_characters: Option<Vec<String>>,
        label_details: Option<lsproto::CompletionItemLabelDetails>,
        file: Node,
        position: i32,
        is_member_completion: bool,
        is_snippet: bool,
        has_action: bool,
        preselect: bool,
        source: &str,
        auto_import_fix: Option<lsproto::AutoImportFix>,
        additional_text_edits: Option<Vec<lsproto::TextEdit>>,
        detail: Option<String>,
    ) -> lsproto::CompletionItem {
        let mut name = name.to_string();
        let mut insert_text = insert_text.to_string();
        let mut filter_text = filter_text.to_string();

        let kind = get_completions_symbol_kind(element_kind);
        let data = lsproto::CompletionItemData {
            file_name: source_file_original_file_name(file).to_string(),
            position,
            supplemental_file_index: supplemental_file_index(file),
            source: source.to_string(),
            name: name.clone(),
            auto_import: auto_import_fix,
            ..Default::default()
        };

        // Text edit
        let mut text_edit: Option<lsproto::TextEditOrInsertReplaceEdit> = None;
        if let Some(replacement_span) = replacement_span {
            text_edit = Some(lsproto::TextEditOrInsertReplaceEdit {
                text_edit: Some(lsproto::TextEdit {
                    new_text: if insert_text.is_empty() {
                        name.clone()
                    } else {
                        insert_text.clone()
                    },
                    range: replacement_span,
                }),
                insert_replace_edit: None,
            });
        }

        // Filter text

        // Ported from vscode ts extension.
        let (word_size, word_start) = get_word_length_and_start(file, position);
        let dot_accessor = get_dot_accessor(file, position - word_size);
        if filter_text.is_empty() {
            filter_text = get_filter_text(
                file,
                position,
                &insert_text,
                &name,
                word_start,
                &dot_accessor,
            );
        }

        // Adjustements based on kind modifiers.
        let mut tags: Option<Vec<lsproto::CompletionItemTag>> = None;
        // Copied from vscode ts extension: `MyCompletionItem.constructor`.
        if is_member_completion
            && kind_modifiers.intersects(lsutil::ScriptElementKindModifier::OPTIONAL)
        {
            if insert_text.is_empty() {
                insert_text = name.clone();
            }
            if filter_text.is_empty() || is_snippet {
                filter_text = name.clone();
            }
            name = name + "?";
        }
        if kind_modifiers.intersects(lsutil::ScriptElementKindModifier::DEPRECATED) {
            tags = Some(vec![lsproto::CompletionItemTag::DEPRECATED]);
        }

        if has_action && !source.is_empty() {
            // !!! adjust label like vscode does
        }

        // Client assumes plain text by default.
        let mut insert_text_format: Option<lsproto::InsertTextFormat> = None;
        if is_snippet {
            insert_text_format = Some(lsproto::InsertTextFormat::SNIPPET);
        }

        lsproto::CompletionItem {
            label: name,
            label_details,
            kind: Some(kind),
            tags,
            detail,
            preselect: bool_to_ptr(preselect),
            sort_text: Some(sort_text.to_string()),
            filter_text: str_ptr_to(&filter_text),
            insert_text: str_ptr_to(&insert_text),
            insert_text_format,
            text_edit,
            commit_characters,
            // Go `[]*lsproto.TextEdit`: the port's edits are never nil.
            additional_text_edits: additional_text_edits
                .map(|edits| edits.into_iter().map(Some).collect()),
            data: Some(data),
            ..Default::default()
        }
    }

    // Go: completions.go:5119 getLabelCompletionsAtPosition
    pub fn get_label_completions_at_position(
        &self,
        ctx: &Context,
        node: Node,
        file: Node,
        position: i32,
        optional_replacement_span: Option<lsproto::Range>,
    ) -> Option<CompletionList> {
        let mut items = self.get_label_statement_completions(ctx, node, file, position);
        if items.is_empty() {
            return None;
        }
        let default_commit_characters =
            get_default_commit_characters(false /*isNewIdentifierLocation*/);
        let item_defaults = self.set_item_defaults(
            ctx,
            position,
            file,
            &mut items,
            Some(&default_commit_characters),
            optional_replacement_span,
        );
        Some(CompletionList {
            is_incomplete: false,
            item_defaults,
            items,
            ..Default::default()
        })
    }

    // Go: completions.go:5146 getLabelStatementCompletions
    pub fn get_label_statement_completions(
        &self,
        ctx: &Context,
        node: Node,
        file: Node,
        position: i32,
    ) -> Vec<CompletionItem> {
        let mut uniques: FxHashSet<String> = FxHashSet::default();
        let mut items: Vec<CompletionItem> = Vec::new();
        let mut current = node;
        while current.is_some() {
            if is_function_like(current) {
                break;
            }
            if is_labeled_statement(current) {
                let name = current.label().text();
                if !uniques.contains(name) {
                    uniques.insert(name.to_string());
                    let lsp_item = self.create_lsp_completion_item(
                        ctx,
                        name,
                        "", /*insertText*/
                        "", /*filterText*/
                        SORT_TEXT_LOCATION_PRIORITY,
                        lsutil::ScriptElementKind::LABEL,
                        lsutil::ScriptElementKindModifier::NONE, /*kindModifiers*/
                        None,                                    /*replacementSpan*/
                        None,                                    /*commitCharacters*/
                        None,                                    /*labelDetails*/
                        file,
                        position,
                        false, /*isMemberCompletion*/
                        false, /*isSnippet*/
                        false, /*hasAction*/
                        false, /*preselect*/
                        "",    /*source*/
                        None,  /*autoImportEntryData*/
                        None,  /*additionalTextEdits*/
                        None,  /*detail*/
                    );
                    items.push(CompletionItem {
                        completion_item: lsp_item,
                        ..Default::default()
                    });
                }
            }
            current = current.parent();
        }
        items
    }
}

// Go: completions.go:5195 isCompletionListBlocker
pub fn is_completion_list_blocker(
    context_token: Node,
    previous_token: Node,
    location: Node,
    file: Node,
    position: i32,
    type_checker: &mut Checker,
) -> bool {
    is_in_string_or_regular_expression_or_template_literal(context_token, position)
        || is_solely_identifier_definition_location(
            context_token,
            previous_token,
            file,
            position,
            type_checker,
        )
        || is_dot_of_numeric_literal(context_token, file)
        || is_in_jsx_text(context_token, location)
        || is_big_int_literal(context_token)
}

// Go: completions.go:5210 isInStringOrRegularExpressionOrTemplateLiteral
pub fn is_in_string_or_regular_expression_or_template_literal(
    context_token: Node,
    position: i32,
) -> bool {
    // To be "in" one of these literals, the position has to be:
    //   1. entirely within the token text.
    //   2. at the end position of an unterminated token.
    //   3. at the end of a regular expression (due to trailing flags like '/foo/g').
    (is_regular_expression_literal(context_token) || is_string_text_containing_node(context_token))
        && context_token.loc().contains_exclusive(position)
        || position == context_token.end()
            && (is_unterminated_literal(context_token)
                || is_regular_expression_literal(context_token))
}

// Go: completions.go:5222 isSolelyIdentifierDefinitionLocation
// true if we are certain that the currently edited location must define a new location; false otherwise.
pub fn is_solely_identifier_definition_location(
    context_token: Node,
    previous_token: Node,
    file: Node,
    position: i32,
    type_checker: &mut Checker,
) -> bool {
    let parent = context_token.parent();
    let containing_node_kind = parent.kind();
    match context_token.kind() {
        SyntaxKind::CommaToken => {
            return containing_node_kind == SyntaxKind::VariableDeclaration
                || is_variable_declaration_list_but_not_type_argument(
                    context_token,
                    file,
                    type_checker,
                )
                || containing_node_kind == SyntaxKind::VariableStatement
                || containing_node_kind == SyntaxKind::EnumDeclaration // enum a { foo, |
                || is_function_like_but_not_constructor(containing_node_kind)
                || containing_node_kind == SyntaxKind::InterfaceDeclaration // interface A<T, |
                || containing_node_kind == SyntaxKind::ArrayBindingPattern // var [x, y|
                || containing_node_kind == SyntaxKind::TypeAliasDeclaration // type Map, K, |
                // class A<T, |
                // var C = class D<T, |
                || (is_class_like(parent)
                    && !parent.type_parameter_list().is_nil()
                    && parent.type_parameter_list().end() >= context_token.pos());
        }
        SyntaxKind::DotToken => {
            return containing_node_kind == SyntaxKind::ArrayBindingPattern; // var [.|
        }
        SyntaxKind::ColonToken => {
            return containing_node_kind == SyntaxKind::BindingElement; // var {x :html|
        }
        SyntaxKind::OpenBracketToken => {
            return containing_node_kind == SyntaxKind::ArrayBindingPattern; // var [x|
        }
        SyntaxKind::OpenParenToken => {
            return containing_node_kind == SyntaxKind::CatchClause
                || is_function_like_but_not_constructor(containing_node_kind);
        }
        SyntaxKind::OpenBraceToken => {
            return containing_node_kind == SyntaxKind::EnumDeclaration; // enum a { |
        }
        SyntaxKind::LessThanToken => {
            return containing_node_kind == SyntaxKind::ClassDeclaration // class A< |
                || containing_node_kind == SyntaxKind::ClassExpression // var C = class D< |
                || containing_node_kind == SyntaxKind::InterfaceDeclaration // interface A< |
                || containing_node_kind == SyntaxKind::TypeAliasDeclaration // type List< |
                || is_function_like_kind(containing_node_kind);
        }
        SyntaxKind::StaticKeyword => {
            return containing_node_kind == SyntaxKind::PropertyDeclaration
                && !is_class_like(parent.parent());
        }
        SyntaxKind::DotDotDotToken => {
            return containing_node_kind == SyntaxKind::Parameter
                || (parent.parent().is_some()
                    && parent.parent().kind() == SyntaxKind::ArrayBindingPattern); // var [...z|
        }
        SyntaxKind::PublicKeyword | SyntaxKind::PrivateKeyword | SyntaxKind::ProtectedKeyword => {
            return containing_node_kind == SyntaxKind::Parameter
                && !is_constructor_declaration(parent.parent());
        }
        SyntaxKind::AsKeyword => {
            return containing_node_kind == SyntaxKind::ImportSpecifier
                || containing_node_kind == SyntaxKind::ExportSpecifier
                || containing_node_kind == SyntaxKind::NamespaceImport;
        }
        SyntaxKind::GetKeyword | SyntaxKind::SetKeyword => {
            return !is_from_object_type_declaration(context_token);
        }
        SyntaxKind::Identifier => {
            if (containing_node_kind == SyntaxKind::ImportSpecifier
                || containing_node_kind == SyntaxKind::ExportSpecifier)
                && context_token == parent.name()
                && context_token.text() == "type"
            {
                // import { type | }
                return false;
            }
            let ancestor_variable_declaration = find_ancestor(parent, is_variable_declaration);
            if ancestor_variable_declaration.is_some()
                && get_line_end_of_position(file, context_token.end()) < position
            {
                // let a
                // |
                return false;
            }
        }
        SyntaxKind::ClassKeyword
        | SyntaxKind::EnumKeyword
        | SyntaxKind::InterfaceKeyword
        | SyntaxKind::FunctionKeyword
        | SyntaxKind::VarKeyword
        | SyntaxKind::ImportKeyword
        | SyntaxKind::LetKeyword
        | SyntaxKind::ConstKeyword
        | SyntaxKind::InferKeyword => {
            return true;
        }
        SyntaxKind::TypeKeyword => {
            // import { type foo| }
            return containing_node_kind != SyntaxKind::ImportSpecifier;
        }
        SyntaxKind::AsteriskToken => {
            return is_function_like(parent) && !is_method_declaration(parent);
        }
        _ => {}
    }

    let token_kind = keyword_for_node(context_token);
    // If the previous token is keyword corresponding to class member completion keyword
    // there will be completion available here
    if is_class_member_completion_keyword(token_kind)
        && is_from_object_type_declaration(context_token)
    {
        return false;
    }

    if is_constructor_parameter_completion(context_token) {
        // constructor parameter completion is available only if
        // - its modifier of the constructor parameter or
        // - its name of the parameter and not being edited
        // eg. constructor(a |<- this shouldnt show completion
        if !is_identifier(context_token)
            || is_parameter_property_modifier(token_kind)
            || is_currently_editing_node(context_token, file, position)
        {
            return false;
        }
    }

    // Previous token may have been a keyword that was converted to an identifier.
    match keyword_for_node(context_token) {
        SyntaxKind::AbstractKeyword
        | SyntaxKind::ClassKeyword
        | SyntaxKind::DeclareKeyword
        | SyntaxKind::EnumKeyword
        | SyntaxKind::FunctionKeyword
        | SyntaxKind::InterfaceKeyword
        | SyntaxKind::LetKeyword
        | SyntaxKind::PrivateKeyword
        | SyntaxKind::ProtectedKeyword
        | SyntaxKind::PublicKeyword
        | SyntaxKind::StaticKeyword
        | SyntaxKind::VarKeyword => {
            return true;
        }
        SyntaxKind::AsyncKeyword => {
            return is_property_declaration(context_token.parent());
        }
        _ => {}
    }

    // If we are inside a class declaration, and `constructor` is totally not present,
    // but we request a completion manually at a whitespace...
    let ancestor_class_like = find_ancestor(parent, is_class_like);
    if ancestor_class_like.is_some()
        && context_token == previous_token
        && is_previous_property_declaration_terminated(context_token, file, position)
    {
        // Don't block completions.
        return false;
    }

    let ancestor_property_declaration = find_ancestor(parent, is_property_declaration);
    // If we are inside a class declaration and typing `constructor` after property declaration...
    if ancestor_property_declaration.is_some()
        && context_token != previous_token
        && is_class_like(previous_token.parent().parent())
        // And the cursor is at the token...
        && position <= previous_token.end()
    {
        // If we are sure that the previous property declaration is terminated according to newline or semicolon...
        if is_previous_property_declaration_terminated(context_token, file, previous_token.end()) {
            // Don't block completions.
            return false;
        } else if context_token.kind() != SyntaxKind::EqualsToken
            // Should not block: `class C { blah = c/**/ }`
            // But should block: `class C { blah = somewhat c/**/ }` and `class C { blah: SomeType c/**/ }`
            && (is_initialized_property(ancestor_property_declaration)
                || ancestor_property_declaration.type_().is_some())
        {
            return true;
        }
    }
    if token_kind == SyntaxKind::ConstKeyword {
        return true;
    }
    is_declaration_name(context_token)
        && !is_shorthand_property_assignment(parent)
        && !is_jsx_attribute(parent)
        // Don't block completions if we're in `class C /**/`, `interface I /**/` or `<T /**/>` ,
        // because we're *past* the end of the identifier and might want to complete `extends`.
        // If `contextToken !== previousToken`, this is `class C ex/**/`, `interface I ex/**/` or `<T ex/**/>`.
        && !((is_class_like(parent)
            || is_interface_declaration(parent)
            || is_type_parameter_declaration(parent))
            && (context_token != previous_token || position > previous_token.end()))
}

// Go: completions.go:5366 isVariableDeclarationListButNotTypeArgument
pub fn is_variable_declaration_list_but_not_type_argument(
    node: Node,
    file: Node,
    type_checker: &mut Checker,
) -> bool {
    node.parent().kind() == SyntaxKind::VariableDeclarationList
        && !is_possibly_type_argument_position(node, file, type_checker)
}

// Go: completions.go:5371 isFunctionLikeButNotConstructor
pub fn is_function_like_but_not_constructor(kind: SyntaxKind) -> bool {
    is_function_like_kind(kind) && kind != SyntaxKind::Constructor
}

// Go: completions.go:5375 isPreviousPropertyDeclarationTerminated
pub fn is_previous_property_declaration_terminated(
    context_token: Node,
    file: Node,
    position: i32,
) -> bool {
    context_token.kind() != SyntaxKind::EqualsToken
        && (context_token.kind() == SyntaxKind::SemicolonToken
            || get_line_of_position(file, context_token.end())
                != get_line_of_position(file, position))
}

// Go: completions.go:5381 isDotOfNumericLiteral
pub fn is_dot_of_numeric_literal(context_token: Node, file: Node) -> bool {
    if context_token.kind() == SyntaxKind::NumericLiteral {
        let text =
            &source_file_text(file)[context_token.pos() as usize..context_token.end() as usize];
        let (r, _) = utf8_decode_last_rune_in_string(text, text.len());
        return r == '.' as i32;
    }

    false
}

// Go: completions.go:5391 isInJsxText
pub fn is_in_jsx_text(context_token: Node, location: Node) -> bool {
    if context_token.kind() == SyntaxKind::JsxText {
        return true;
    }

    if context_token.kind() == SyntaxKind::GreaterThanToken && context_token.parent().is_some() {
        // <Component<string> /**/ />
        // <Component<string> /**/ ><Component>
        // - contextToken: GreaterThanToken (before cursor)
        // - location: JsxSelfClosingElement or JsxOpeningElement
        // - contextToken.parent === location
        if location == context_token.parent() && is_jsx_opening_like_element(location) {
            return false;
        }

        if context_token.parent().kind() == SyntaxKind::JsxOpeningElement {
            // <div>/**/
            // - contextToken: GreaterThanToken (before cursor)
            // - location: JSXElement
            // - different parents (JSXOpeningElement, JSXElement)
            return location.parent().kind() != SyntaxKind::JsxOpeningElement;
        }

        if context_token.parent().kind() == SyntaxKind::JsxClosingElement
            || context_token.parent().kind() == SyntaxKind::JsxSelfClosingElement
        {
            return context_token.parent().parent().is_some()
                && context_token.parent().parent().kind() == SyntaxKind::JsxElement;
        }
    }

    false
}

// Go: completions.go:5423 clientSupportsItemLabelDetails
pub fn client_supports_item_label_details(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .completion
        .completion_item
        .label_details_support
}

// Go: completions.go:5427 clientSupportsItemSnippet
pub fn client_supports_item_snippet(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .completion
        .completion_item
        .snippet_support
}

// Go: completions.go:5431 clientSupportsItemCommitCharacters
pub fn client_supports_item_commit_characters(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .completion
        .completion_item
        .commit_characters_support
}

// Go: completions.go:5435 clientSupportsItemInsertReplace
pub fn client_supports_item_insert_replace(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .completion
        .completion_item
        .insert_replace_support
}

// Go: completions.go:5439 clientSupportsDefaultCommitCharacters
pub fn client_supports_default_commit_characters(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .completion
        .completion_list
        .item_defaults
        .iter()
        .any(|s| s == "commitCharacters")
}

// Go: completions.go:5443 clientSupportsDefaultEditRange
pub fn client_supports_default_edit_range(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .completion
        .completion_list
        .item_defaults
        .iter()
        .any(|s| s == "editRange")
}

// Go: completions.go:5447 argumentInfoForCompletions
#[derive(Clone, Copy, Debug, Default)]
pub struct ArgumentInfoForCompletions {
    pub invocation: Node,
    pub argument_index: i32,
    pub argument_count: i32,
}

// Go: completions.go:5453 getArgumentInfoForCompletions
pub fn get_argument_info_for_completions(
    node: Node,
    position: i32,
    file: Node,
    type_checker: &mut Checker,
) -> Option<ArgumentInfoForCompletions> {
    let info = get_immediately_containing_argument_info(node, position, file, type_checker)?;
    if info.is_type_parameter_list || info.invocation.call_invocation.is_none() {
        return None;
    }
    let call_invocation = info.invocation.call_invocation.as_ref()?;
    Some(ArgumentInfoForCompletions {
        invocation: call_invocation.node,
        argument_index: info.argument_index,
        argument_count: info.argument_count,
    })
}

// Go: completions.go:4864 Source* consts
// Special values for `CompletionInfo['source']` used to disambiguate
// completion items with the same `name`. (Each completion item must
// have a unique name/source combination, because those two fields
// comprise `CompletionEntryIdentifier` in `getCompletionEntryDetails`.
//
// When the completion item is an auto-import suggestion, the source
// is the module specifier of the suggestion. To avoid collisions,
// the values here should not be a module specifier we would ever
// generate for an auto-import.

// Completions that require `this.` insertion text
pub const SOURCE_THIS_PROPERTY: &str = "ThisProperty/";
// Auto-import that comes attached to a class member snippet
pub const SOURCE_CLASS_MEMBER_SNIPPET: &str = "ClassMemberSnippet/";
// A type-only import that needs to be promoted in order to be used at the completion location
pub const SOURCE_TYPE_ONLY_ALIAS: &str = "TypeOnlyAlias/";
// Auto-import that comes attached to an object literal method snippet
pub const SOURCE_OBJECT_LITERAL_METHOD_SNIPPET: &str = "ObjectLiteralMethodSnippet/";
// Case completions for switch statements
pub const SOURCE_SWITCH_CASES: &str = "SwitchCases/";
// Completions for an object literal expression
pub const SOURCE_OBJECT_LITERAL_MEMBER_WITH_COMMA: &str = "ObjectLiteralMemberWithComma/";
