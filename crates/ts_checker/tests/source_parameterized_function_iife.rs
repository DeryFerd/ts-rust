use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_420);
const LIBRARY: FileId = FileId::new(203_421);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (FILE, parsed, "\"/project/parameterized-function-iife.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file == LIBRARY,
                    file == LIBRARY,
                    if file == LIBRARY {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            strict_function_types: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

#[derive(Clone, Copy)]
struct Iife {
    result_name: NodeRef,
    call: NodeRef,
    callee: NodeRef,
    function: NodeRef,
    parameter: NodeRef,
    parameter_name: NodeRef,
    parameter_annotation: NodeRef,
    return_annotation: NodeRef,
    return_statement: NodeRef,
    returned_parameter: NodeRef,
    argument: NodeRef,
}

fn iife(parsed: &ParseResult) -> Iife {
    let declarations = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| match &record.data {
            NodeData::VariableDeclaration(variable) => Some(variable),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [variable] = declarations.as_slice() else {
        panic!("expected the one result declaration");
    };
    let call_node = variable.initializer.unwrap();
    let NodeData::CallExpression(call) = &parsed.arena.get(call_node).unwrap().data else {
        panic!("expected the result initializer call");
    };
    let callee_record = parsed.arena.get(call.expression).unwrap();
    assert_eq!(callee_record.parent, Some(call_node));
    let NodeData::ParenthesizedExpression(parenthesized) = &callee_record.data else {
        panic!("expected a parenthesized function callee");
    };
    let function_record = parsed.arena.get(parenthesized.expression).unwrap();
    assert_eq!(function_record.parent, Some(call.expression));
    let NodeData::FunctionExpression(function) = &function_record.data else {
        panic!("expected the actual function expression");
    };
    assert!(function.name.is_none());
    assert!(function.modifiers.is_none());
    assert!(function.asterisk_token.is_none());
    assert!(function.type_parameters.is_none());
    let [parameter_node] = function.parameters.nodes.as_slice() else {
        panic!("expected the one typed parameter");
    };
    let parameter_record = parsed.arena.get(*parameter_node).unwrap();
    assert_eq!(parameter_record.parent, Some(parenthesized.expression));
    let NodeData::ParameterDeclaration(parameter) = &parameter_record.data else {
        unreachable!();
    };
    let block_record = parsed.arena.get(function.body).unwrap();
    assert_eq!(block_record.parent, Some(parenthesized.expression));
    let NodeData::Block(block) = &block_record.data else {
        unreachable!();
    };
    let [return_node] = block.statements.nodes.as_slice() else {
        panic!("expected the parameter return");
    };
    let return_record = parsed.arena.get(*return_node).unwrap();
    assert_eq!(return_record.parent, Some(function.body));
    let NodeData::ReturnStatement(statement) = &return_record.data else {
        unreachable!();
    };
    let returned_parameter = statement.expression.unwrap();
    assert_eq!(
        parsed.arena.get(returned_parameter).unwrap().parent,
        Some(*return_node)
    );
    let [argument] = call.arguments.nodes.as_slice() else {
        panic!("expected the one actual argument");
    };
    assert_eq!(parsed.arena.get(*argument).unwrap().parent, Some(call_node));
    Iife {
        result_name: node(parsed, variable.name),
        call: node(parsed, call_node),
        callee: node(parsed, call.expression),
        function: node(parsed, parenthesized.expression),
        parameter: node(parsed, *parameter_node),
        parameter_name: node(parsed, parameter.name),
        parameter_annotation: node(parsed, parameter.type_.unwrap()),
        return_annotation: node(parsed, function.type_.unwrap()),
        return_statement: node(parsed, *return_node),
        returned_parameter: node(parsed, returned_parameter),
        argument: node(parsed, *argument),
    }
}

fn assert_types(
    checker: &mut CanonicalCheckerContext<'_>,
    nodes: Iife,
    return_type: TypeId,
) -> (TypeId, SignatureId) {
    let string_type = checker.store().intrinsic_bootstrap().unwrap().string_type;
    let raw_parameter = checker
        .file(FILE)
        .unwrap()
        .1
        .symbol(nodes.parameter)
        .unwrap();
    let parameter = checker.store().get_merged_symbol(raw_parameter).unwrap();
    for location in [nodes.parameter_name, nodes.returned_parameter] {
        assert_eq!(
            checker.get_symbol_at_location(location),
            Ok(Some(parameter))
        );
        assert_eq!(checker.get_type_at_location(location), Ok(string_type));
    }
    assert_eq!(
        checker.get_type_from_type_node(nodes.parameter_annotation),
        Ok(string_type)
    );
    assert_eq!(
        checker.get_type_from_type_node(nodes.return_annotation),
        Ok(return_type)
    );
    for location in [nodes.call, nodes.result_name] {
        assert_eq!(checker.get_type_at_location(location), Ok(return_type));
    }
    let function_type = checker.get_type_at_location(nodes.function).unwrap();
    assert_eq!(
        checker.get_type_at_location(nodes.callee),
        Ok(function_type)
    );
    let TypeData::Object(object) = checker.store().type_payload(function_type).unwrap().data()
    else {
        panic!("expected the canonical callable type");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected the one canonical call signature");
    };
    let signature = *signature;
    assert_eq!(
        checker.get_return_type_of_signature(signature),
        Ok(return_type)
    );
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(nodes.function));
    assert_eq!(record.parameters(), &[parameter]);
    assert_eq!(record.min_argument_count(), 1);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.this_parameter(), None);
    assert!(!record.has_rest_parameter());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.resolved_return_type(), Some(return_type));
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(FILE).unwrap())
            .unwrap()
            .type_checked
    );
    (function_type, signature)
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.type_resolution_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let location = node(parsed, id);
                (
                    location,
                    store.node_links(location).cloned(),
                    store.type_node_links(location).cloned(),
                    store.symbol_node_links(location).cloned(),
                    store.signature_links(location).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(owner, _)| (owner, store.value_symbol_links(owner).cloned()))
            .collect::<Vec<_>>(),
        store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        store.relation_state_snapshot(),
        checker.file(FILE).unwrap().1.flow_graph().clone(),
        checker.diagnostics().clone(),
    )
}

fn assert_diagnostics(checker: &CanonicalCheckerContext<'_>, nodes: Iife, invalid: bool) {
    let diagnostics = checker.diagnostics().as_slice();
    if !invalid {
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        return;
    }
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    for (location, code, arguments, message) in [
        (
            nodes.return_statement,
            2322,
            ["string", "number"],
            "Type 'string' is not assignable to type 'number'.",
        ),
        (
            nodes.argument,
            2345,
            ["number", "string"],
            "Argument of type 'number' is not assignable to parameter of type 'string'.",
        ),
    ] {
        let diagnostic = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.node == Some(location))
            .unwrap_or_else(|| panic!("missing diagnostic at {location:?}: {diagnostics:?}"));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
        assert!(diagnostic.diagnostic.details.is_empty());
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.related_information.is_empty());
    }
}

fn check_iife(source: &str, invalid: bool) {
    let parsed = parse_source_file(source);
    let library = parse_source_file(ES5);
    let nodes = iife(&parsed);
    for source_first in [false, true] {
        let mut checker = context(&parsed, &library);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let string_type = bootstrap.string_type;
        let number_type = bootstrap.number_type;
        let return_type = if invalid { number_type } else { string_type };
        if source_first {
            checker.check_source_file(FILE).unwrap();
        }
        assert_eq!(checker.get_type_at_location(nodes.call), Ok(return_type));
        checker.check_source_file(FILE).unwrap();
        let identity = assert_types(&mut checker, nodes, return_type);
        assert_diagnostics(&checker, nodes, invalid);
        let before = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(assert_types(&mut checker, nodes, return_type), identity);
            assert_diagnostics(&checker, nodes, invalid);
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

#[test]
fn parameterized_function_iife_checks_argument_parameter_and_return() {
    check_iife(
        "export const result: string = (function(value: string): string {
            return value;
        })(\"input\");",
        false,
    );
}

#[test]
fn parameterized_function_iife_reports_wrong_argument_and_return() {
    check_iife(
        "export const result: number = (function(value: string): number {
            return value;
        })(1);",
        true,
    );
}
