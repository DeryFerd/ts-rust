use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeId};
use ts_parser::{parse_source_file, ParseResult};

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
    assert!(context
        .store()
        .symbol_node_links(known)
        .is_some_and(|links| links.resolved_symbol.is_some()));

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
