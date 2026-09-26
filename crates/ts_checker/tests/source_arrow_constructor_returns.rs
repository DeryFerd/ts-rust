use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    signatures::SignatureFlags,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_110);
const LIBRARY: FileId = FileId::new(203_111);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (FILE, parsed, "\"/project/arrow-constructor-returns.ts\""),
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
            no_unchecked_indexed_access: true,
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

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)))
        .collect::<Vec<_>>();
    let [found] = nodes.as_slice() else {
        panic!("expected one {kind:?}")
    };
    *found
}

fn assertion(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::AsExpression(assertion) = &record.data else {
                return None;
            };
            (parsed.arena.get(assertion.type_)?.kind == kind).then_some(node(parsed, id))
        })
        .unwrap()
}

fn interface(parsed: &ParseResult, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), LIBRARY, id))
        })
        .unwrap()
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(location)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
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

#[allow(clippy::too_many_lines)] // Keep constructor, wrapper, callable, and replay identities together.
fn check(argument: &str, invalid: bool) {
    let source = format!(
        "export {{}};\nconst make = () => {{\n  return ((((new Error({argument}))) as unknown) as number);\n}};\nconst result = make();\n"
    );
    let parsed = parse_source_file(&source);
    let library = parse_source_file(ES5);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    let construction = only(&parsed, SyntaxKind::NewExpression);
    let arrow = only(&parsed, SyntaxKind::ArrowFunction);
    let call = only(&parsed, SyntaxKind::CallExpression);
    let returned = only(&parsed, SyntaxKind::ReturnStatement);
    let unknown_cast = assertion(&parsed, SyntaxKind::UnknownKeyword);
    let number_cast = assertion(&parsed, SyntaxKind::NumberKeyword);
    let NodeData::NewExpression(new) = &parsed.arena.get(construction.node).unwrap().data else {
        unreachable!()
    };
    assert!(new.type_arguments.is_none());
    let callee = node(&parsed, new.expression);
    let [argument] = new.arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("the constructor must keep its supplied argument")
    };
    let argument = node(&parsed, *argument);
    let error_declaration = interface(&library, "Error");
    let constructor_declaration = interface(&library, "ErrorConstructor");
    let NodeData::ArrowFunction(function) = &parsed.arena.get(arrow.node).unwrap().data else {
        unreachable!()
    };
    let NodeData::Block(block) = &parsed.arena.get(function.body).unwrap().data else {
        unreachable!()
    };
    assert_eq!(block.statements.nodes, [returned.node]);
    let NodeData::ReturnStatement(statement) = &parsed.arena.get(returned.node).unwrap().data
    else {
        unreachable!()
    };
    let return_expression = node(&parsed, statement.expression.unwrap());
    let wrappers = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::ParenthesizedExpression(parenthesized) = &record.data else {
                return None;
            };
            Some((node(&parsed, id), node(&parsed, parenthesized.expression)))
        })
        .collect::<Vec<_>>();
    assert!(wrappers.len() >= 2);

    for query_first in [false, true] {
        let mut checker = context(&parsed, &library);
        assert!(checker.global_types().diagnostics().is_empty());
        assert!(
            !checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .is_some_and(|links| links.type_checked)
        );
        let cold = query_first.then(|| checker.get_type_at_location(construction).unwrap());
        checker.check_source_file(FILE).unwrap();
        let error_owner = symbol(&checker, error_declaration);
        let constructor_owner = symbol(&checker, constructor_declaration);
        let error_type = checker.get_declared_type_of_symbol(error_owner).unwrap();
        let constructor_type = checker
            .get_declared_type_of_symbol(constructor_owner)
            .unwrap();
        assert_eq!(checker.get_type_at_location(construction), Ok(error_type));
        if let Some(cold) = cold {
            assert_eq!(cold, error_type);
        }
        assert_eq!(checker.get_type_at_location(callee), Ok(constructor_type));
        assert_eq!(
            checker.get_symbol_at_location(callee),
            Ok(Some(error_owner))
        );
        assert_eq!(
            checker.store().type_payload(error_type).unwrap().symbol(),
            Some(error_owner)
        );
        assert_eq!(
            checker
                .store()
                .type_payload(constructor_type)
                .unwrap()
                .symbol(),
            Some(constructor_owner)
        );
        assert_ne!(error_type, constructor_type);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let (unknown, number) = (bootstrap.unknown_type, bootstrap.number_type);
        assert_ne!(error_type, unknown);
        assert_ne!(error_type, number);
        assert_eq!(checker.get_type_at_location(unknown_cast), Ok(unknown));
        assert_eq!(checker.get_type_at_location(number_cast), Ok(number));
        assert_eq!(checker.get_type_at_location(return_expression), Ok(number));
        for &(wrapper, child) in &wrappers {
            let expected = checker.get_type_at_location(child).unwrap();
            assert_eq!(checker.get_type_at_location(wrapper), Ok(expected));
        }
        let construct_signature = signature(&checker, construction);
        assert_eq!(
            checker.get_return_type_of_signature(construct_signature),
            Ok(error_type)
        );
        let construct = checker.store().signature(construct_signature).unwrap();
        assert!(construct.flags().contains(SignatureFlags::CONSTRUCT));
        assert!(construct.type_parameters().is_empty());
        assert_eq!(construct.min_argument_count(), 0);
        assert_eq!(construct.parameters().len(), 1);
        assert_eq!(construct.target(), None);
        assert_eq!(construct.mapper(), None);
        let declaration = construct.declaration().unwrap();
        assert_eq!(declaration.file, LIBRARY);
        assert_eq!(
            library.arena.get(declaration.node).unwrap().kind,
            SyntaxKind::ConstructSignature
        );
        assert_eq!(
            library.arena.get(declaration.node).unwrap().parent,
            Some(constructor_declaration.node)
        );
        let arrow_signature = signature(&checker, arrow);
        assert_ne!(arrow_signature, construct_signature);
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
            Ok(number)
        );
        assert_eq!(checker.get_type_at_location(call), Ok(number));
        assert_eq!(signature(&checker, call), arrow_signature);
        if invalid {
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!("the constructor argument must still be checked")
            };
            assert_eq!(diagnostic.diagnostic.code(), 2345);
            assert_eq!(diagnostic.diagnostic.category(), Category::Error);
            assert_eq!(diagnostic.node, Some(argument));
            assert!(diagnostic.range_override.is_none());
            assert!(diagnostic.related_information.is_empty());
            assert!(diagnostic.diagnostic.details.is_empty());
            assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Argument of type 'number' is not assignable to parameter of type 'string'."
            );
        } else {
            assert!(checker.diagnostics().is_empty());
        }
        let queries = [
            construction,
            callee,
            argument,
            unknown_cast,
            number_cast,
            return_expression,
            call,
            arrow,
        ];
        let types =
            queries.map(|location| (location, checker.get_type_at_location(location).unwrap()));
        let before = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            for (location, type_) in types {
                assert_eq!(checker.get_type_at_location(location), Ok(type_));
            }
            assert_eq!(signature(&checker, construction), construct_signature);
            assert_eq!(signature(&checker, arrow), arrow_signature);
            assert_eq!(signature(&checker, call), arrow_signature);
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

#[test]
fn stored_arrow_constructor_returns_keep_real_error_and_cast_types() {
    check("\"x\"", false);
}

#[test]
fn stored_arrow_constructor_returns_report_invalid_error_arguments() {
    check("1", true);
}
