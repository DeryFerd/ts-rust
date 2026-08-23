use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeId};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: &str = "interface Array<T> {} interface ReadonlyArray<T> {}";

const SOURCE: &str = concat!(
    "interface KnownObject { known: number; }\n",
    "const object = { known: 1 };\n",
    "const values: number[] = [1, 2];\n",
    "const text = \"abc\";\n",
    "function take(value: number): number { return value; }\n",
    "function increment(items: number[]): number { return items[0] + 1; }\n",
    "function readonlyFirst(readonlyItems: ReadonlyArray<number>): number { return readonlyItems[0]; }\n",
    "function missingKey(input: KnownObject): unknown { return input[\"missing\"]; }\n",
    "const known = object[\"known\"];\n",
    "const first = values[0];\n",
    "const character = text[\"0\"];\n",
    "const plus = increment(values);\n",
    "const called = take(values[0]);\n",
    "const namedArray = values[\"name\"];\n",
    "const invalid = object[true];\n",
);

fn context<'a>(
    library: &'a ParseResult,
    library_file: FileId,
    source: &'a ParseResult,
    source_file: FileId,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (parsed, file, name, module_state) in [
        (
            library,
            library_file,
            "\"/project/lib.d.ts\"",
            CanonicalModuleState::Script,
        ),
        (
            source,
            source_file,
            "\"/project/element-access.ts\"",
            CanonicalModuleState::External,
        ),
    ] {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(name),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        [(library_file, &library.arena), (source_file, &source.arena)]
            .into_iter()
            .collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let initializer = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected)
                .then_some(variable.initializer)
                .flatten()
        })
        .unwrap_or_else(|| panic!("missing initializer for {expected}"));
    NodeRef::new(parsed.arena.id(), file, initializer)
}

fn node_text<'source>(source: &'source str, parsed: &ParseResult, node: NodeRef) -> &'source str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
}

fn element_expression(source: &str, parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let node = NodeRef::new(parsed.arena.id(), file, node);
            (matches!(&record.data, NodeData::ElementAccessExpression(_))
                && node_text(source, parsed, node) == expected)
                .then_some(node)
        })
        .unwrap_or_else(|| panic!("missing element expression {expected:?}"))
}

#[test]
fn source_element_access_checks_properties_arrays_strings_compositions_and_diagnostics() {
    let library = parse_source_file(LIBRARY);
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let library_file = FileId::new(0);
    let file = FileId::new(1);
    let mut context = context(&library, library_file, &parsed, file);

    context.check_source_file(file).unwrap();

    for (name, expected) in [
        ("known", "number"),
        ("first", "number"),
        ("character", "string"),
        ("plus", "number"),
        ("called", "number"),
    ] {
        let initializer = variable_initializer(&parsed, file, name);
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, initializer))
                .unwrap(),
            expected,
            "initializer for {name}",
        );
    }

    for expression in ["items[0]", "readonlyItems[0]"] {
        let element = element_expression(SOURCE, &parsed, file, expression);
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, element))
                .unwrap(),
            "number",
            "element {expression}",
        );
    }

    let known = variable_initializer(&parsed, file, "known");
    assert!(
        context
            .store()
            .symbol_node_links(known)
            .is_some_and(|links| links.resolved_symbol.is_some())
    );

    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.diagnostic.code(),
                node_text(SOURCE, &parsed, diagnostic.node.unwrap()),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [
            (7053, "input[\"missing\"]"),
            (7015, "\"name\""),
            (2538, "true"),
        ],
    );

    let type_count = context.store().type_len();
    let diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(context.store().type_len(), type_count);
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn indexed_access_accepts_nested_receivers_parenthesized_keys_and_literal_key_unions() {
    let source = concat!(
        "type Pair = { first: number; second: string };\n",
        "type Numbers = { first: number; second: number };\n",
        "type Left = { value: number; left: string };\n",
        "type Right = { value: string; right: number };\n",
        "function select(pair: Pair, key: \"first\" | \"second\"): string | number {\n",
        "  return pair[key];\n",
        "}\n",
        "function selectNumber(pair: Numbers, key: \"first\" | \"second\"): number {\n",
        "  return pair[key];\n",
        "}\n",
        "function shared(pair: Left | Right): string | number {\n",
        "  return pair[\"value\"];\n",
        "}\n",
        "function arrayAt(values: number[], key: 0 | 1): number {\n",
        "  return values[key];\n",
        "}\n",
        "const container = { text: \"ab\" };\n",
        "const matrix: number[][] = [[1, 2]];\n",
        "const fromProperty = container.text[0];\n",
        "const fromElement = matrix[0][0];\n",
        "const wrappedReceiver = (matrix)[0];\n",
        "const wrappedIndex = matrix[(0)];\n",
    );
    let library = parse_source_file(LIBRARY);
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let library_file = FileId::new(20);
    let file = FileId::new(21);
    let mut context = context(&library, library_file, &parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    for (name, expected) in [
        ("fromProperty", "string"),
        ("fromElement", "number"),
        ("wrappedReceiver", "number[]"),
        ("wrappedIndex", "number[]"),
    ] {
        assert_eq!(
            context
                .type_to_string(resolved_type(
                    &context,
                    variable_initializer(&parsed, file, name),
                ))
                .unwrap(),
            expected,
            "initializer for {name}",
        );
    }

    for (expression, expected) in [
        ("pair[key]", "string | number"),
        ("pair[\"value\"]", "string | number"),
        ("values[key]", "number"),
    ] {
        let element = element_expression(source, &parsed, file, expression);
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, element))
                .unwrap(),
            expected,
            "element {expression}",
        );
    }

    let union_key = element_expression(source, &parsed, file, "pair[key]");
    assert!(
        context
            .store()
            .symbol_node_links(union_key)
            .is_none_or(|links| links.resolved_symbol.is_none()),
    );
    let union_property = element_expression(source, &parsed, file, "pair[\"value\"]");
    assert!(
        context
            .store()
            .symbol_node_links(union_property)
            .is_some_and(|links| links.resolved_symbol.is_some()),
    );

    let counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        counts,
    );
}

#[test]
fn boolean_index_reports_the_complete_boolean_type() {
    let source = concat!(
        "type Pair = { first: number };\n",
        "function invalid(pair: Pair, key: boolean): unknown {\n",
        "  return pair[key];\n",
        "}\n",
    );
    let library = parse_source_file(LIBRARY);
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let library_file = FileId::new(22);
    let file = FileId::new(23);
    let mut context = context(&library, library_file, &parsed, file);

    context.check_source_file(file).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one invalid-index diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2538);
    assert_eq!(node_text(source, &parsed, diagnostic.node.unwrap()), "key");
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'boolean' cannot be used as an index type.",
    );
}

#[test]
fn const_enum_element_access_preserves_member_identity_and_missing_diagnostics() {
    let source = concat!(
        "const enum Status { Ready = 1 }\n",
        "const value = Status[\"Ready\"];\n",
        "const missing = Status[\"Missing\"];\n",
    );
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(source);
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(25);
    let mut context = context(&library, FileId::new(24), &parsed, file);

    context.check_source_file(file).unwrap();

    let value = variable_initializer(&parsed, file, "value");
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, value))
            .unwrap(),
        "Status.Ready",
    );
    assert!(
        context
            .store()
            .symbol_node_links(value)
            .and_then(|links| links.resolved_symbol)
            .is_some()
    );
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one missing enum-member diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2339);
    assert_eq!(
        diagnostic.diagnostic.arguments,
        ["Missing", "typeof Status"]
    );
    assert_eq!(
        node_text(source, &parsed, diagnostic.node.unwrap()),
        "\"Missing\""
    );

    let warm = (context.store().type_len(), context.diagnostics().clone());
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (context.store().type_len(), context.diagnostics().clone()),
        warm
    );
}

#[test]
fn numeric_enum_reverse_lookup_preserves_const_enum_dynamic_index_errors() {
    let source = concat!(
        "enum Size { Small, Large }\n",
        "const selected = Size.Large;\n",
        "const label = Size[selected];\n",
        "const enum Fixed { Ready }\n",
        "const rejected = Fixed[1];\n",
        "label + '';\n",
    );
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(source);
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(27);
    let mut context = context(&library, FileId::new(26), &parsed, file);

    context.check_source_file(file).unwrap();

    let label = variable_initializer(&parsed, file, "label");
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, label))
            .unwrap(),
        "string",
    );
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one dynamic const-enum access diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2476);
    assert_eq!(node_text(source, &parsed, diagnostic.node.unwrap()), "1");

    let concatenation = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::BinaryExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap();
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, concatenation))
            .unwrap(),
        "string",
    );

    let warm = (context.store().type_len(), context.diagnostics().clone());
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (context.store().type_len(), context.diagnostics().clone()),
        warm,
    );
}

#[test]
fn enum_indices_distinguish_numeric_strings_any_and_const_enum_access() {
    let source = concat!(
        "enum Numeric { Ready = 1 }\n",
        "const reverse = Numeric[\"1\"];\n",
        "const invalid = Numeric[\"01\"];\n",
        "enum Text { Ready = 'ready' }\n",
        "let key: any;\n",
        "const missing = Text[key];\n",
        "const enum Fixed { Ready = 1 }\n",
        "const rejected = Fixed[key];\n",
    );
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(source);
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(29);
    let mut context = context(&library, FileId::new(28), &parsed, file);

    context.check_source_file(file).unwrap();

    assert_eq!(
        context
            .type_to_string(resolved_type(
                &context,
                variable_initializer(&parsed, file, "reverse"),
            ))
            .unwrap(),
        "string",
    );
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| (
                diagnostic.diagnostic.code(),
                node_text(source, &parsed, diagnostic.node.unwrap()),
            ))
            .collect::<Vec<_>>(),
        [(7015, "\"01\""), (7053, "Text[key]"), (2476, "key")],
    );

    let warm = (context.store().type_len(), context.diagnostics().clone());
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (context.store().type_len(), context.diagnostics().clone()),
        warm,
    );
}

#[test]
fn ambient_type_queries_preserve_union_identity_for_index_diagnostics() {
    let source = concat!(
        "declare let key: string;\n",
        "declare let first: { id: 'a' } | { id: 'b' };\n",
        "declare let second: typeof first | { id: 'c' };\n",
        "first[key];\n",
        "second[key];\n",
    );
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(source);
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(31);
    let mut context = context(&library, FileId::new(30), &parsed, file);

    context.check_source_file(file).unwrap();

    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.diagnostic.code(),
                node_text(source, &parsed, diagnostic.node.unwrap()),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(diagnostics, [(7053, "first[key]"), (7053, "second[key]")]);

    let query = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::TypeQueryNode(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .expect("the second declaration queries the first ambient union");
    let NodeData::TypeQueryNode(query_data) = &parsed.arena.get(query.node).unwrap().data else {
        unreachable!("the selected node is a type query")
    };
    let name = NodeRef::new(parsed.arena.id(), file, query_data.expr_name);
    assert!(
        context
            .store()
            .symbol_node_links(name)
            .and_then(|links| links.resolved_symbol)
            .is_some()
    );
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, query))
            .unwrap(),
        "{ id: \"a\"; } | { id: \"b\"; }",
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}
