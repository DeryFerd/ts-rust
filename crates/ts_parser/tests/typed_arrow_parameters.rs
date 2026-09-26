use std::collections::HashSet;

use ts_ast::{NodeData, NodeId, ParameterDeclarationData, SyntaxKind, TypeReferenceNodeData};
use ts_core::TextRange;
use ts_parser::{ParseResult, parse_source_file};

const MIME_ARROW: &str = concat!(
    "(\n",
    "  filename: string,\n",
    "  mimes: Record<string, string> = baseMimes\n",
    "): string | undefined => {\n",
    "  const regexp = /\\.([a-zA-Z0-9]+?)$/\n",
    "  const match = filename.match(regexp)\n",
    "  if (!match) {\n",
    "    return\n",
    "  }\n",
    "  return mimes[match[1].toLowerCase()]\n",
    "}",
);

fn text(parsed: &ParseResult, range: TextRange) -> &str {
    &parsed.arena.source_text().unwrap()[range.start.get() as usize..range.end.get() as usize]
}

fn node_text(parsed: &ParseResult, id: NodeId) -> &str {
    text(parsed, parsed.arena.get(id).unwrap().range)
}

fn statements(parsed: &ParseResult) -> &[NodeId] {
    let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected a source file");
    };
    &source.statements.nodes
}

fn initializer(parsed: &ParseResult, statement: NodeId, name: &str) -> NodeId {
    let NodeData::VariableStatement(statement) = &parsed.arena.get(statement).unwrap().data else {
        panic!("expected a variable statement");
    };
    let NodeData::VariableDeclarationList(list) =
        &parsed.arena.get(statement.declaration_list).unwrap().data
    else {
        panic!("expected a declaration list");
    };
    assert_eq!(list.declarations.nodes.len(), 1);
    let NodeData::VariableDeclaration(declaration) =
        &parsed.arena.get(list.declarations.nodes[0]).unwrap().data
    else {
        panic!("expected a variable declaration");
    };
    assert_eq!(node_text(parsed, declaration.name), name);
    declaration.initializer.unwrap()
}

fn parameter(parsed: &ParseResult, id: NodeId) -> &ParameterDeclarationData {
    let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(id).unwrap().data else {
        panic!("expected a parameter");
    };
    assert_eq!(parsed.arena.get(id).unwrap().kind, SyntaxKind::Parameter);
    assert!(parameter.dot_dot_dot_token.is_none());
    assert!(parameter.question_token.is_none());
    parameter
}

fn reference(parsed: &ParseResult, id: NodeId) -> &TypeReferenceNodeData {
    let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(id).unwrap().data else {
        panic!("expected a type reference");
    };
    reference
}

fn assert_complete_tree(parsed: &ParseResult, source: &str) {
    assert_eq!(parsed.arena.source_text(), Some(source));
    let root = parsed.arena.get(parsed.source_file).unwrap();
    assert_eq!(root.range.start.get(), 0);
    assert_eq!(root.range.end.get() as usize, source.len());
    let NodeData::SourceFile(file) = &root.data else {
        panic!("expected a source file");
    };
    let eof = parsed.arena.get(file.end_of_file_token).unwrap();
    assert_eq!(eof.kind, SyntaxKind::EndOfFile);
    assert_eq!(eof.range.start.get() as usize, source.len());
    assert_eq!(eof.range.end.get() as usize, source.len());
    let mut pending = vec![parsed.source_file];
    let mut visited = HashSet::new();
    while let Some(id) = pending.pop() {
        assert!(visited.insert(id), "repeated child {id:?}");
        let node = parsed.arena.get(id).unwrap();
        assert!(node.range.start <= node.range.end);
        assert!(source.is_char_boundary(node.range.start.get() as usize));
        assert!(source.is_char_boundary(node.range.end.get() as usize));
        node.for_each_child(|child| {
            let record = parsed.arena.get(child).unwrap();
            assert_eq!(record.parent, Some(id));
            assert!(node.range.start <= record.range.start);
            assert!(record.range.end <= node.range.end);
            pending.push(child);
        });
    }
}

#[test]
fn mime_typed_default_keeps_the_two_parameters_and_return_type() {
    let source = format!("export const getMimeType = {MIME_ARROW}\nconst after = 1;\n");
    let parsed = parse_source_file(&source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_complete_tree(&parsed, &source);
    let statements = statements(&parsed);
    assert_eq!(statements.len(), 2);
    let arrow_id = initializer(&parsed, statements[0], "getMimeType");
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(arrow_id).unwrap().data else {
        panic!("expected the MIME arrow function");
    };
    assert_eq!(node_text(&parsed, arrow_id), MIME_ARROW);
    assert_eq!(
        parsed.arena.get(arrow_id).unwrap().range.start.get() as usize,
        source.find('(').unwrap()
    );
    assert_eq!(arrow.parameters.nodes.len(), 2);
    assert!(!arrow.parameters.has_trailing_comma);
    assert!(arrow.type_parameters.is_none());
    let filename_id = arrow.parameters.nodes[0];
    assert_eq!(node_text(&parsed, filename_id), "filename: string");
    let filename = parameter(&parsed, filename_id);
    assert_eq!(node_text(&parsed, filename.name), "filename");
    assert_eq!(
        parsed.arena.get(filename.type_.unwrap()).unwrap().kind,
        SyntaxKind::StringKeyword
    );
    assert!(filename.initializer.is_none());
    let mimes_id = arrow.parameters.nodes[1];
    assert_eq!(
        node_text(&parsed, mimes_id),
        "mimes: Record<string, string> = baseMimes"
    );
    let mimes = parameter(&parsed, mimes_id);
    assert_eq!(node_text(&parsed, mimes.name), "mimes");
    assert_eq!(node_text(&parsed, mimes.initializer.unwrap()), "baseMimes");
    let type_id = mimes.type_.unwrap();
    assert_eq!(node_text(&parsed, type_id), "Record<string, string>");
    let record = reference(&parsed, type_id);
    assert_eq!(node_text(&parsed, record.type_name), "Record");
    let arguments = record.type_arguments.as_ref().unwrap();
    assert_eq!(text(&parsed, arguments.range), "<string, string>");
    assert_eq!(arguments.nodes.len(), 2);
    for argument in &arguments.nodes {
        assert_eq!(
            parsed.arena.get(*argument).unwrap().kind,
            SyntaxKind::StringKeyword
        );
    }
    let return_id = arrow.type_.unwrap();
    assert_eq!(node_text(&parsed, return_id), "string | undefined");
    let NodeData::UnionTypeNode(return_type) = &parsed.arena.get(return_id).unwrap().data else {
        panic!("expected the written return union");
    };
    assert_eq!(
        return_type
            .types
            .nodes
            .iter()
            .map(|id| parsed.arena.get(*id).unwrap().kind)
            .collect::<Vec<_>>(),
        [SyntaxKind::StringKeyword, SyntaxKind::UndefinedKeyword]
    );
    assert_eq!(node_text(&parsed, arrow.equals_greater_than_token), "=>");
    assert_eq!(
        parsed
            .arena
            .get(arrow.equals_greater_than_token)
            .unwrap()
            .range
            .start
            .get() as usize,
        source.find("=>").unwrap()
    );
    let NodeData::Block(body) = &parsed.arena.get(arrow.body).unwrap().data else {
        panic!("expected the original MIME body");
    };
    assert_eq!(body.statements.nodes.len(), 4);
    assert_eq!(
        node_text(&parsed, initializer(&parsed, statements[1], "after")),
        "1"
    );
    assert_eq!(
        parsed
            .arena
            .iter()
            .filter(|(_, node)| matches!(node.data, NodeData::ArrowFunction(_)))
            .count(),
        1
    );
}

fn assert_nested_default_type(parsed: &ParseResult, id: NodeId) {
    assert_eq!(
        node_text(parsed, id),
        "Wrapper<Record<string, Array<number>>>"
    );
    let wrapper = reference(parsed, id);
    assert_eq!(node_text(parsed, wrapper.type_name), "Wrapper");
    let arguments = wrapper.type_arguments.as_ref().unwrap();
    assert_eq!(arguments.nodes.len(), 1);
    let record = reference(parsed, arguments.nodes[0]);
    assert_eq!(node_text(parsed, record.type_name), "Record");
    let arguments = record.type_arguments.as_ref().unwrap();
    assert_eq!(arguments.nodes.len(), 2);
    assert_eq!(
        parsed.arena.get(arguments.nodes[0]).unwrap().kind,
        SyntaxKind::StringKeyword
    );
    let array = reference(parsed, arguments.nodes[1]);
    assert_eq!(node_text(parsed, array.type_name), "Array");
    let arguments = array.type_arguments.as_ref().unwrap();
    assert_eq!(arguments.nodes.len(), 1);
    assert_eq!(
        parsed.arena.get(arguments.nodes[0]).unwrap().kind,
        SyntaxKind::NumberKeyword
    );
}

#[test]
fn nested_generic_closers_before_a_default_remain_parameter_type_tokens() {
    let source = concat!(
        "const select = (entry: Wrapper<Record<string, Array<number>>> = fallback): ",
        "Wrapper<Record<string, Array<number>>> => entry;\n",
        "const after = 1;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_complete_tree(&parsed, source);
    let statements = statements(&parsed);
    assert_eq!(statements.len(), 2);
    let arrow_id = initializer(&parsed, statements[0], "select");
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(arrow_id).unwrap().data else {
        panic!("expected the typed arrow");
    };
    assert_eq!(arrow.parameters.nodes.len(), 1);
    let parameter_id = arrow.parameters.nodes[0];
    assert_eq!(
        node_text(&parsed, parameter_id),
        "entry: Wrapper<Record<string, Array<number>>> = fallback"
    );
    let parameter = parameter(&parsed, parameter_id);
    assert_eq!(node_text(&parsed, parameter.name), "entry");
    assert_nested_default_type(&parsed, parameter.type_.unwrap());
    assert_nested_default_type(&parsed, arrow.type_.unwrap());
    assert_ne!(parameter.type_.unwrap(), arrow.type_.unwrap());
    assert_eq!(
        node_text(&parsed, parameter.initializer.unwrap()),
        "fallback"
    );
    assert_eq!(
        parsed
            .arena
            .get(parameter.initializer.unwrap())
            .unwrap()
            .kind,
        SyntaxKind::Identifier
    );
    assert_eq!(node_text(&parsed, arrow.body), "entry");
    assert_eq!(
        parsed.arena.get(arrow.body).unwrap().kind,
        SyntaxKind::Identifier
    );
    assert_eq!(
        parsed.arena.get(arrow_id).unwrap().range.end.get() as usize,
        source.find(";\n").unwrap()
    );
    assert_eq!(
        node_text(&parsed, initializer(&parsed, statements[1], "after")),
        "1"
    );
}
