use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(53_350);
const FILE: FileId = FileId::new(53_351);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'arena>(
    library: &'arena ParseResult,
    source: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (LIBRARY, library, "\"/lib.es5.d.ts\"", true),
        (FILE, source, "\"/callable-integration.ts\"", false),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, name, library) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(name),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn only_node(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
    });
    let node = nodes.next().expect("the source must contain this node");
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    node
}

fn variable(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 4] {
    let store = checker.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
    ]
}

fn assert_capture_assignment_error(checker: &CanonicalCheckerContext<'_>, node: NodeRef) {
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected one assignment error from the captured union")
    };
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string | number' is not assignable to type 'number'.",
    );
    assert!(diagnostic.related_information.is_empty());
}

#[test]
fn object_method_capture_keeps_the_declared_type_before_a_later_write() {
    let library = parse_source_file(ES5);
    let parsed = parse_source_file(concat!(
        "let value: string | number = 1;\n",
        "const object = { read() { return value; } };\n",
        "value = 'later';\n",
        "const result: number = object.read();\n",
    ));
    let method = only_node(&parsed, SyntaxKind::MethodDeclaration);
    let returned = only_node(&parsed, SyntaxKind::ReturnStatement);
    let NodeData::ReturnStatement(returned) = &parsed.arena.get(returned.node).unwrap().data else {
        unreachable!()
    };
    let read = NodeRef::new(parsed.arena.id(), FILE, returned.expression.unwrap());
    let value = variable(&parsed, "value");
    let NodeData::VariableDeclaration(value_data) = &parsed.arena.get(value.node).unwrap().data
    else {
        unreachable!()
    };
    let annotation = NodeRef::new(parsed.arena.id(), FILE, value_data.type_.unwrap());
    let result = variable(&parsed, "result");
    let NodeData::VariableDeclaration(result_data) = &parsed.arena.get(result.node).unwrap().data
    else {
        unreachable!()
    };
    let result_name = NodeRef::new(parsed.arena.id(), FILE, result_data.name);
    let call = NodeRef::new(parsed.arena.id(), FILE, result_data.initializer.unwrap());
    for query_first in [false, true] {
        let mut checker = context(&library, &parsed);
        if query_first {
            checker.get_type_at_location(method).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        assert_capture_assignment_error(&checker, result_name);
        let union = checker.get_type_at_location(annotation).unwrap();
        assert_eq!(checker.type_to_string(union).unwrap(), "string | number");
        let owner = symbol(&checker, method);
        assert_eq!(
            checker.store().symbol(owner).unwrap().flags(),
            SymbolFlags::METHOD
        );
        let callable = checker.get_type_at_location(method).unwrap();
        assert_eq!(
            checker.store().type_payload(callable).unwrap().symbol(),
            Some(owner)
        );
        let method_signature = signature(&checker, method);
        assert_eq!(
            checker
                .store()
                .signature(method_signature)
                .unwrap()
                .declaration(),
            Some(method)
        );
        assert_eq!(
            checker.get_return_type_of_signature(method_signature),
            Ok(union)
        );
        assert_eq!(checker.get_type_at_location(read), Ok(union));
        assert_eq!(
            checker.get_symbol_at_location(read),
            Ok(Some(symbol(&checker, value)))
        );
        assert_eq!(checker.get_type_at_location(call), Ok(union));
        assert_eq!(signature(&checker, call), method_signature);

        let warm = counts(&checker);
        let diagnostics = checker.diagnostics().clone();
        checker.recheck_source_file(FILE).unwrap();
        assert_eq!(checker.get_type_at_location(method), Ok(callable));
        assert_eq!(signature(&checker, method), method_signature);
        assert_eq!(
            checker.get_return_type_of_signature(method_signature),
            Ok(union)
        );
        assert_eq!(checker.get_type_at_location(read), Ok(union));
        assert_eq!(checker.get_type_at_location(call), Ok(union));
        assert_eq!(signature(&checker, call), method_signature);
        assert_eq!(counts(&checker), warm);
        assert_eq!(checker.diagnostics(), &diagnostics);
    }
}

#[test]
fn nested_arrow_keeps_the_method_parameter_type_before_a_later_write() {
    let library = parse_source_file(ES5);
    let parsed = parse_source_file(concat!(
        "const object = { run(value: string | number): number {\n",
        "  value = 1;\n",
        "  const read = () => value;\n",
        "  value = 'later';\n",
        "  return read();\n",
        "} };\n",
        "const result = object.run(0);\n",
    ));
    let method = only_node(&parsed, SyntaxKind::MethodDeclaration);
    let arrow = only_node(&parsed, SyntaxKind::ArrowFunction);
    let returned = only_node(&parsed, SyntaxKind::ReturnStatement);
    let NodeData::MethodDeclaration(method_data) = &parsed.arena.get(method.node).unwrap().data
    else {
        unreachable!()
    };
    let parameter = NodeRef::new(parsed.arena.id(), FILE, method_data.parameters.nodes[0]);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    let annotation = NodeRef::new(parsed.arena.id(), FILE, parameter_data.type_.unwrap());
    let NodeData::ArrowFunction(arrow_data) = &parsed.arena.get(arrow.node).unwrap().data else {
        unreachable!()
    };
    let read = NodeRef::new(parsed.arena.id(), FILE, arrow_data.body);
    for query_first in [false, true] {
        let mut checker = context(&library, &parsed);
        if query_first {
            checker.get_type_at_location(arrow).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        assert_capture_assignment_error(&checker, returned);
        let union = checker.get_type_at_location(annotation).unwrap();
        assert_eq!(checker.type_to_string(union).unwrap(), "string | number");
        let parameter_owner = symbol(&checker, parameter);
        assert_eq!(
            checker.get_symbol_at_location(read),
            Ok(Some(parameter_owner))
        );
        assert_eq!(checker.get_type_at_location(read), Ok(union));
        let method_signature = signature(&checker, method);
        let arrow_signature = signature(&checker, arrow);
        assert_eq!(
            checker
                .store()
                .signature(method_signature)
                .unwrap()
                .parameters(),
            &[parameter_owner]
        );
        assert_eq!(
            checker
                .store()
                .signature(arrow_signature)
                .unwrap()
                .declaration(),
            Some(arrow)
        );
        assert_eq!(
            checker.get_return_type_of_signature(arrow_signature),
            Ok(union)
        );
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            checker.get_return_type_of_signature(method_signature),
            Ok(number)
        );

        let warm = counts(&checker);
        let diagnostics = checker.diagnostics().clone();
        checker.recheck_source_file(FILE).unwrap();
        assert_eq!(signature(&checker, method), method_signature);
        assert_eq!(signature(&checker, arrow), arrow_signature);
        assert_eq!(
            checker.get_symbol_at_location(read),
            Ok(Some(parameter_owner))
        );
        assert_eq!(checker.get_type_at_location(read), Ok(union));
        assert_eq!(
            checker.get_return_type_of_signature(method_signature),
            Ok(number)
        );
        assert_eq!(
            checker.get_return_type_of_signature(arrow_signature),
            Ok(union)
        );
        assert_eq!(counts(&checker), warm);
        assert_eq!(checker.diagnostics(), &diagnostics);
    }
}
