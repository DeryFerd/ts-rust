use ts_ast::{NodeData, SyntaxKind};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

fn assert_nested_function_type(source: &str, parameter_name: &str) {
    for parse in [parse_source_file, parse_jsx_source_file] {
        let parsed = parse(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
            panic!("expected source file");
        };
        assert_eq!(root.statements.nodes.len(), 2);
        let NodeData::FunctionDeclaration(outer) =
            &parsed.arena.get(root.statements.nodes[0]).unwrap().data
        else {
            panic!("expected outer function");
        };
        let NodeData::Block(body) = &parsed.arena.get(outer.body.unwrap()).unwrap().data else {
            panic!("expected function body");
        };
        assert_eq!(body.statements.nodes.len(), 2);
        let NodeData::TypeAliasDeclaration(alias) =
            &parsed.arena.get(body.statements.nodes[0]).unwrap().data
        else {
            panic!("expected type alias");
        };
        let NodeData::FunctionTypeNode(function) = &parsed.arena.get(alias.type_).unwrap().data
        else {
            panic!("expected function type");
        };
        let parameters = function.type_parameters.as_ref().unwrap();
        assert_eq!(parameters.nodes.len(), 1);
        let NodeData::TypeParameterDeclaration(parameter) =
            &parsed.arena.get(parameters.nodes[0]).unwrap().data
        else {
            panic!("expected type parameter");
        };
        assert_eq!(identifier_text(&parsed, parameter.name), parameter_name);
        assert_eq!(
            parsed.arena.get(root.statements.nodes[1]).unwrap().kind,
            SyntaxKind::VariableStatement
        );
    }
}

fn identifier_text(parsed: &ParseResult, name: ts_ast::NodeId) -> &str {
    let NodeData::Identifier(identifier) = &parsed.arena.get(name).unwrap().data else {
        panic!("expected identifier");
    };
    &identifier.text
}

#[test]
fn nested_function_type_clears_outer_await_context() {
    assert_nested_function_type(
        concat!(
            "async function outer() { type Fn = <await>() => void; const innerAfter = 1; }\n",
            "const after = 2;\n",
        ),
        "await",
    );
}

#[test]
fn nested_function_type_clears_outer_yield_context() {
    assert_nested_function_type(
        concat!(
            "function* outer() { type Fn = <yield>() => void; const innerAfter = 1; }\n",
            "const after = 2;\n",
        ),
        "yield",
    );
}
