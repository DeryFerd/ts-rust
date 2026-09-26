//! One-member leading unions and intersections have a separate AST-shape gap.
//! These branch controls use multiple members and do not set that expectation.

use std::{collections::HashSet, ops::Range};

use ts_ast::SyntaxKind::{
    AnyKeyword, AsExpression, BooleanKeyword, ColonToken, ConditionalType, FunctionType,
    Identifier, InferType, IntersectionType, JsDocNullableType, NeverKeyword, NumberKeyword,
    NumericLiteral, OptionalType, Parameter, QuestionToken, StringKeyword, TypeParameter,
    TypeReference, UnionType, VoidKeyword,
};
use ts_ast::{ConditionalTypeNodeData, NodeData, NodeId, SyntaxKind, TypeAliasDeclarationData};
use ts_core::DiagnosticCategory;
use ts_parser::{ParseResult, parse_source_file};

fn span(parsed: &ParseResult, id: NodeId) -> Range<usize> {
    let range = parsed.arena.get(id).expect("allocated node").range;
    usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()
}

fn assert_owned_tree(parsed: &ParseResult, source: &str) {
    assert_eq!(span(parsed, parsed.source_file), 0..source.len());
    assert_eq!(parsed.arena.get(parsed.source_file).unwrap().parent, None);
    let mut pending = vec![parsed.source_file];
    let mut visited = HashSet::new();
    while let Some(id) = pending.pop() {
        assert!(visited.insert(id), "repeated child {id:?}");
        let node = parsed.arena.get(id).expect("allocated parent");
        assert!(source.get(span(parsed, id)).is_some(), "{:?}", node.range);
        node.for_each_child(|child_id| {
            let child = parsed.arena.get(child_id).expect("allocated child");
            assert_eq!(child.parent, Some(id), "{:?}", child.kind);
            assert!(node.range.start <= child.range.start);
            assert!(child.range.end <= node.range.end);
            pending.push(child_id);
        });
    }
}

fn statements(parsed: &ParseResult) -> &[NodeId] {
    let NodeData::SourceFile(file) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected source file");
    };
    &file.statements.nodes
}

fn alias<'a>(
    parsed: &'a ParseResult,
    index: usize,
    expected_name: &str,
) -> (NodeId, &'a TypeAliasDeclarationData) {
    let id = statements(parsed)[index];
    let NodeData::TypeAliasDeclaration(alias) = &parsed.arena.get(id).unwrap().data else {
        panic!("expected type alias");
    };
    let NodeData::Identifier(name) = &parsed.arena.get(alias.name).unwrap().data else {
        panic!("expected alias name");
    };
    assert_eq!(name.text, expected_name);
    assert_eq!(
        parsed.arena.get(id).unwrap().parent,
        Some(parsed.source_file)
    );
    assert_eq!(parsed.arena.get(alias.name).unwrap().parent, Some(id));
    assert_eq!(parsed.arena.get(alias.type_).unwrap().parent, Some(id));
    (id, alias)
}

fn conditional(parsed: &ParseResult, id: NodeId) -> &ConditionalTypeNodeData {
    let NodeData::ConditionalTypeNode(conditional) = &parsed.arena.get(id).unwrap().data else {
        panic!("expected conditional type");
    };
    conditional
}

fn children(
    parsed: &ParseResult,
    source: &str,
    parent: NodeId,
    expected: &[(NodeId, SyntaxKind, &str)],
) {
    for &(id, kind, text) in expected {
        let node = parsed.arena.get(id).unwrap();
        assert_eq!(node.parent, Some(parent));
        assert_eq!(node.kind, kind);
        assert_eq!(&source[span(parsed, id)], text);
    }
}

fn members(parsed: &ParseResult, id: NodeId, kind: SyntaxKind) -> &[NodeId] {
    assert_eq!(parsed.arena.get(id).unwrap().kind, kind);
    match &parsed.arena.get(id).unwrap().data {
        NodeData::UnionTypeNode(union) => &union.types.nodes,
        NodeData::IntersectionTypeNode(intersection) => &intersection.types.nodes,
        _ => panic!("expected union or intersection"),
    }
}

fn assert_after(parsed: &ParseResult, source: &str, index: usize) {
    let (id, after) = alias(parsed, index, "After");
    let start = source.find("type After = number;").unwrap();
    assert_eq!(
        span(parsed, id),
        start..start + "type After = number;".len()
    );
    children(
        parsed,
        source,
        id,
        &[(after.type_, NumberKeyword, "number")],
    );
}

fn assert_infer(parsed: &ParseResult, source: &str, parent: NodeId, id: NodeId, name: &str) {
    children(
        parsed,
        source,
        parent,
        &[(id, InferType, &format!("infer {name}"))],
    );
    let NodeData::InferTypeNode(infer) = &parsed.arena.get(id).unwrap().data else {
        panic!("expected infer type");
    };
    let parameter_id = infer.type_parameter;
    children(parsed, source, id, &[(parameter_id, TypeParameter, name)]);
    let NodeData::TypeParameterDeclaration(parameter) =
        &parsed.arena.get(parameter_id).unwrap().data
    else {
        panic!("expected inferred parameter");
    };
    assert!(parameter.constraint.is_none());
    assert!(parameter.default_type.is_none());
    children(
        parsed,
        source,
        parameter_id,
        &[(parameter.name, Identifier, name)],
    );
}

fn assert_callback(
    parsed: &ParseResult,
    source: &str,
    parent: NodeId,
    id: NodeId,
    text: &str,
    parameters: &[&str],
) {
    children(parsed, source, parent, &[(id, FunctionType, text)]);
    let NodeData::FunctionTypeNode(function) = &parsed.arena.get(id).unwrap().data else {
        panic!("expected function type");
    };
    assert!(function.type_parameters.is_none());
    assert_eq!(function.parameters.nodes.len(), parameters.len());
    for (&parameter_id, &text) in function.parameters.nodes.iter().zip(parameters) {
        children(parsed, source, id, &[(parameter_id, Parameter, text)]);
        let NodeData::ParameterDeclaration(parameter) =
            &parsed.arena.get(parameter_id).unwrap().data
        else {
            panic!("expected callback parameter");
        };
        let (name, annotation) = text.split_once(": ").unwrap();
        children(
            parsed,
            source,
            parameter_id,
            &[(parameter.name, Identifier, name)],
        );
        let type_id = parameter.type_.expect("callback annotation");
        assert_eq!(&source[span(parsed, type_id)], annotation);
        assert_eq!(
            parsed.arena.get(type_id).unwrap().parent,
            Some(parameter_id)
        );
    }
    children(
        parsed,
        source,
        id,
        &[(
            function.type_.expect("callback return"),
            VoidKeyword,
            "void",
        )],
    );
}

fn assert_missing_type(parsed: &ParseResult, source: &str, parent: NodeId, id: NodeId, at: usize) {
    children(parsed, source, parent, &[(id, TypeReference, "")]);
    assert_eq!(span(parsed, id), at..at);
    let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(id).unwrap().data else {
        panic!("expected missing type reference");
    };
    assert!(reference.type_arguments.is_none());
    children(parsed, source, id, &[(reference.type_name, Identifier, "")]);
    assert_eq!(span(parsed, reference.type_name), at..at);
}

fn assert_diagnostic(parsed: &ParseResult, source: &str, code: u32, message: &str) {
    let start = source.find(": never").unwrap();
    assert_eq!(parsed.diagnostics.len(), 1, "{:?}", parsed.diagnostics);
    let diagnostic = &parsed.diagnostics[0];
    assert_eq!(diagnostic.code, Some(code));
    assert_eq!(diagnostic.category, DiagnosticCategory::Error);
    assert_eq!(diagnostic.message, message);
    assert_eq!(
        usize::try_from(diagnostic.range.start.get()).unwrap(),
        start
    );
    assert_eq!(
        usize::try_from(diagnostic.range.end.get()).unwrap(),
        start + 1
    );
}

#[test]
fn leading_type_operators_keep_the_true_branch_out_of_extends() {
    for (operator, kind) in [("|", UnionType), ("&", IntersectionType)] {
        for separator in [" ", "\n    "] {
            let branch = format!("{operator} Left {operator} Right");
            let body = format!("T extends string ?{separator}{branch} : never");
            let source = format!("/* é🙂 */\ntype Result<T> = {body};\ntype After = number;\n");
            let parsed = parse_source_file(&source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            assert_eq!(statements(&parsed).len(), 2);
            let (alias_id, alias) = alias(&parsed, 0, "Result");
            children(
                &parsed,
                &source,
                alias_id,
                &[(alias.type_, ConditionalType, &body)],
            );
            let start = source.find(&body).unwrap();
            assert_eq!(span(&parsed, alias.type_), start..start + body.len());
            let condition = conditional(&parsed, alias.type_);
            children(
                &parsed,
                &source,
                alias.type_,
                &[
                    (condition.check_type, TypeReference, "T"),
                    (condition.extends_type, StringKeyword, "string"),
                    (condition.true_type, kind, &branch),
                    (condition.false_type, NeverKeyword, "never"),
                ],
            );
            let parts = members(&parsed, condition.true_type, kind);
            assert_eq!(parts.len(), 2);
            for (&part, name) in parts.iter().zip(["Left", "Right"]) {
                children(
                    &parsed,
                    &source,
                    condition.true_type,
                    &[(part, TypeReference, name)],
                );
            }
            assert_after(&parsed, &source, 1);
            assert_owned_tree(&parsed, &source);
        }
    }
}

fn assert_pipeline_destination(parsed: &ParseResult, source: &str) {
    let (_, destination) = alias(parsed, 0, "PipelineDestination");
    assert_eq!(destination.type_parameters.as_ref().unwrap().nodes.len(), 2);
    let condition = conditional(parsed, destination.type_);
    children(
        parsed,
        source,
        destination.type_,
        &[
            (condition.check_type, TypeReference, "S"),
            (
                condition.extends_type,
                TypeReference,
                "PipelineTransformSource<infer ST>",
            ),
        ],
    );
    let NodeData::TypeReferenceNode(reference) =
        &parsed.arena.get(condition.extends_type).unwrap().data
    else {
        panic!("expected generic extends reference");
    };
    let arguments = &reference.type_arguments.as_ref().unwrap().nodes;
    assert_eq!(arguments.len(), 1);
    assert_infer(parsed, source, condition.extends_type, arguments[0], "ST");
    let parts = members(parsed, condition.true_type, UnionType);
    assert_eq!(parts.len(), 3);
    for (&part, text) in parts.iter().zip([
        "NodeJS.WritableStream",
        "PipelineDestinationIterableFunction<ST>",
        "PipelineDestinationPromiseFunction<ST, P>",
    ]) {
        children(
            parsed,
            source,
            condition.true_type,
            &[(part, TypeReference, text)],
        );
    }
    children(
        parsed,
        source,
        destination.type_,
        &[(condition.false_type, NeverKeyword, "never")],
    );
}

fn assert_pipeline_results(parsed: &ParseResult, source: &str) {
    for (index, name) in [(1, "PipelineCallback"), (2, "PipelinePromise")] {
        let (_, alias) = alias(parsed, index, name);
        let condition = conditional(parsed, alias.type_);
        let NodeData::TypeReferenceNode(reference) =
            &parsed.arena.get(condition.extends_type).unwrap().data
        else {
            panic!("expected destination reference");
        };
        let arguments = &reference.type_arguments.as_ref().unwrap().nodes;
        assert_eq!(arguments.len(), 2);
        children(
            parsed,
            source,
            condition.extends_type,
            &[(arguments[0], AnyKeyword, "any")],
        );
        assert_infer(parsed, source, condition.extends_type, arguments[1], "P");
        if index == 1 {
            assert_callback(
                parsed,
                source,
                alias.type_,
                condition.true_type,
                "(err: NodeJS.ErrnoException | null, value: P) => void",
                &["err: NodeJS.ErrnoException | null", "value: P"],
            );
            assert_callback(
                parsed,
                source,
                alias.type_,
                condition.false_type,
                "(err: NodeJS.ErrnoException | null) => void",
                &["err: NodeJS.ErrnoException | null"],
            );
        } else {
            children(
                parsed,
                source,
                alias.type_,
                &[
                    (condition.true_type, TypeReference, "Promise<P>"),
                    (condition.false_type, TypeReference, "Promise<void>"),
                ],
            );
        }
    }
}

#[test]
fn original_pipeline_declarations_keep_infer_and_callback_ownership() {
    let source = concat!(
        "        type PipelineDestination<S extends PipelineTransformSource<any>, P> = S extends\n",
        "            PipelineTransformSource<infer ST> ?\n",
        "                | NodeJS.WritableStream\n",
        "                | PipelineDestinationIterableFunction<ST>\n",
        "                | PipelineDestinationPromiseFunction<ST, P>\n",
        "            : never;\n",
        "        type PipelineCallback<S extends PipelineDestination<any, any>> = S extends\n",
        "            PipelineDestinationPromiseFunction<any, infer P> ? (err: NodeJS.ErrnoException | null, value: P) => void\n",
        "            : (err: NodeJS.ErrnoException | null) => void;\n",
        "        type PipelinePromise<S extends PipelineDestination<any, any>> = S extends\n",
        "            PipelineDestinationPromiseFunction<any, infer P> ? Promise<P> : Promise<void>;\n",
        "type After = number;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(statements(&parsed).len(), 4);
    assert_pipeline_destination(&parsed, source);
    assert_pipeline_results(&parsed, source);
    assert!(
        parsed
            .arena
            .iter()
            .all(|(_, node)| node.kind != JsDocNullableType)
    );
    assert_after(&parsed, source, 3);
    assert_owned_tree(&parsed, source);
}

#[test]
fn nested_false_conditionals_and_following_aliases_keep_their_ranges() {
    let inner = "T extends number ? & Third & Fourth : never";
    for before_question in [" ", "\n    "] {
        let outer = format!("T extends string{before_question}? | Left | Right : {inner}");
        let source = format!("type Nested<T> = {outer};\ntype After = number;\n");
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        assert_eq!(statements(&parsed).len(), 2);
        let (alias_id, alias) = alias(&parsed, 0, "Nested");
        children(
            &parsed,
            &source,
            alias_id,
            &[(alias.type_, ConditionalType, &outer)],
        );
        let condition = conditional(&parsed, alias.type_);
        children(
            &parsed,
            &source,
            alias.type_,
            &[
                (condition.extends_type, StringKeyword, "string"),
                (condition.true_type, UnionType, "| Left | Right"),
                (condition.false_type, ConditionalType, inner),
            ],
        );
        let nested = conditional(&parsed, condition.false_type);
        children(
            &parsed,
            &source,
            condition.false_type,
            &[
                (nested.check_type, TypeReference, "T"),
                (nested.extends_type, NumberKeyword, "number"),
                (nested.true_type, IntersectionType, "& Third & Fourth"),
                (nested.false_type, NeverKeyword, "never"),
            ],
        );
        let parts = members(&parsed, nested.true_type, IntersectionType);
        assert_eq!(parts.len(), 2);
        for (&member, text) in parts.iter().zip(["Third", "Fourth"]) {
            children(
                &parsed,
                &source,
                nested.true_type,
                &[(member, TypeReference, text)],
            );
        }
        assert_after(&parsed, &source, 1);
        assert_owned_tree(&parsed, &source);
    }
}

fn assert_cast_conditional(parsed: &ParseResult, source: &str) {
    let NodeData::VariableStatement(statement) =
        &parsed.arena.get(statements(parsed)[2]).unwrap().data
    else {
        panic!("expected cast statement");
    };
    let NodeData::VariableDeclarationList(declarations) =
        &parsed.arena.get(statement.declaration_list).unwrap().data
    else {
        panic!("expected declarations");
    };
    let NodeData::VariableDeclaration(declaration) = &parsed
        .arena
        .get(declarations.declarations.nodes[0])
        .unwrap()
        .data
    else {
        panic!("expected result variable");
    };
    let initializer = declaration.initializer.unwrap();
    let NodeData::ConditionalExpression(expression) = &parsed.arena.get(initializer).unwrap().data
    else {
        panic!("expected expression conditional");
    };
    children(
        parsed,
        source,
        initializer,
        &[
            (expression.condition, AsExpression, "value as T"),
            (expression.question_token, QuestionToken, "?"),
            (expression.colon_token, ColonToken, ":"),
            (expression.when_true, NumericLiteral, "1"),
            (expression.when_false, NumericLiteral, "0"),
        ],
    );
    let NodeData::AsExpression(cast) = &parsed.arena.get(expression.condition).unwrap().data else {
        panic!("expected cast condition");
    };
    children(
        parsed,
        source,
        expression.condition,
        &[
            (cast.expression, Identifier, "value"),
            (cast.type_, TypeReference, "T"),
        ],
    );
}

#[test]
fn postfix_nullable_tuple_optionals_and_cast_conditionals_stay_separate() {
    let source = concat!(
        "type Nullable = string?;\n",
        "type Optional = [number?, boolean?];\n",
        "const result = value as T ? 1 : 0;\n",
        "type After = number;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(statements(&parsed).len(), 4);
    let (nullable_id, nullable) = alias(&parsed, 0, "Nullable");
    children(
        &parsed,
        source,
        nullable_id,
        &[(nullable.type_, JsDocNullableType, "string?")],
    );
    let NodeData::JsDocNullableType(nullable_type) =
        &parsed.arena.get(nullable.type_).unwrap().data
    else {
        panic!("expected retained nullable syntax");
    };
    children(
        &parsed,
        source,
        nullable.type_,
        &[(nullable_type.type_, StringKeyword, "string")],
    );
    let (_, optional) = alias(&parsed, 1, "Optional");
    let NodeData::TupleTypeNode(tuple) = &parsed.arena.get(optional.type_).unwrap().data else {
        panic!("expected optional tuple");
    };
    assert_eq!(tuple.elements.nodes.len(), 2);
    for (&element, (text, kind)) in tuple
        .elements
        .nodes
        .iter()
        .zip([("number", NumberKeyword), ("boolean", BooleanKeyword)])
    {
        children(
            &parsed,
            source,
            optional.type_,
            &[(element, OptionalType, &format!("{text}?"))],
        );
        let NodeData::OptionalTypeNode(optional_type) = &parsed.arena.get(element).unwrap().data
        else {
            panic!("expected optional element");
        };
        children(
            &parsed,
            source,
            element,
            &[(optional_type.type_, kind, text)],
        );
    }
    assert_cast_conditional(&parsed, source);
    assert_after(&parsed, source, 3);
    assert_owned_tree(&parsed, source);
}

#[test]
fn missing_members_keep_type_diagnostics_and_the_following_alias() {
    for (operator, kind) in [("|", UnionType), ("&", IntersectionType)] {
        let branch = format!("{operator} Left {operator} ");
        let source = format!(
            "/* é🙂 */\ntype Broken<T> = T extends string ? {branch}: never;\ntype After = number;\n"
        );
        let parsed = parse_source_file(&source);
        assert_diagnostic(&parsed, &source, 1110, "Type expected.");
        assert_eq!(statements(&parsed).len(), 2);
        let (_, alias) = alias(&parsed, 0, "Broken");
        let condition = conditional(&parsed, alias.type_);
        children(
            &parsed,
            &source,
            alias.type_,
            &[
                (condition.extends_type, StringKeyword, "string"),
                (condition.true_type, kind, &branch),
            ],
        );
        let parts = members(&parsed, condition.true_type, kind);
        assert_eq!(parts.len(), 2);
        children(
            &parsed,
            &source,
            condition.true_type,
            &[(parts[0], TypeReference, "Left")],
        );
        assert_missing_type(
            &parsed,
            &source,
            condition.true_type,
            parts[1],
            source.find(": never").unwrap(),
        );
        children(
            &parsed,
            &source,
            alias.type_,
            &[(condition.false_type, NeverKeyword, "never")],
        );
        assert_after(&parsed, &source, 1);
        assert_owned_tree(&parsed, &source);
    }
}

#[test]
fn a_union_extends_operand_does_not_replace_a_missing_question_mark() {
    let source = "type Broken<T> = T extends string | number : never;\ntype After = number;\n";
    let parsed = parse_source_file(source);
    assert_diagnostic(&parsed, source, 1005, "'?' expected.");
    assert_eq!(statements(&parsed).len(), 2);
    let (_, alias) = alias(&parsed, 0, "Broken");
    let condition = conditional(&parsed, alias.type_);
    children(
        &parsed,
        source,
        alias.type_,
        &[(condition.extends_type, UnionType, "string | number")],
    );
    let parts = members(&parsed, condition.extends_type, UnionType);
    assert_eq!(parts.len(), 2);
    children(
        &parsed,
        source,
        condition.extends_type,
        &[
            (parts[0], StringKeyword, "string"),
            (parts[1], NumberKeyword, "number"),
        ],
    );
    assert_missing_type(
        &parsed,
        source,
        alias.type_,
        condition.true_type,
        source.find(": never").unwrap(),
    );
    children(
        &parsed,
        source,
        alias.type_,
        &[(condition.false_type, NeverKeyword, "never")],
    );
    assert_after(&parsed, source, 1);
    assert_owned_tree(&parsed, source);
}
