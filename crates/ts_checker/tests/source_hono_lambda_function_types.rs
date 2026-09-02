use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeError,
    IntrinsicBootstrapOptions, SignatureId, TypeData, TypeId, TypeNodeUnavailable,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(299_412);
const LIBRARY: FileId = FileId::new(299_413);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

// Keep the original declaration from Hono's src/adapter/aws-lambda/types.ts.
const CALLBACK: &str =
    "type Callback<TResult = any> = (error?: Error | string | null, result?: TResult) => void\n";

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (FILE, parsed, "\"/project/lambda-function-types.ts\""),
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

struct Alias {
    declaration: NodeRef,
    body: NodeRef,
    formals: Vec<NodeRef>,
    parameters: Vec<NodeRef>,
    returned: NodeRef,
}

fn alias(parsed: &ParseResult, expected: &str) -> Alias {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            if name.text != expected {
                return None;
            }
            let function_record = parsed.arena.get(alias.type_).unwrap();
            assert_eq!(function_record.parent, Some(id));
            let NodeData::FunctionTypeNode(function) = &function_record.data else {
                panic!("expected the alias's written function type");
            };
            Some(Alias {
                declaration: node(parsed, id),
                body: node(parsed, alias.type_),
                formals: alias
                    .type_parameters
                    .iter()
                    .flat_map(|parameters| &parameters.nodes)
                    .map(|&id| node(parsed, id))
                    .collect(),
                parameters: function
                    .parameters
                    .nodes
                    .iter()
                    .map(|&id| node(parsed, id))
                    .collect(),
                returned: node(parsed, function.type_.unwrap()),
            })
        })
        .unwrap_or_else(|| panic!("missing alias {expected}"))
}

fn variable(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(node(parsed, variable.name))
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn calls(parsed: &ParseResult) -> Vec<NodeRef> {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some(node(parsed, id))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
    calls
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, callable: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(callable).unwrap().data() else {
        panic!("expected an actual callable object");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one call signature");
    };
    *signature
}

fn parameter_types(checker: &CanonicalCheckerContext<'_>, signature: SignatureId) -> Vec<TypeId> {
    checker
        .store()
        .signature(signature)
        .unwrap()
        .parameters()
        .iter()
        .map(|&parameter| {
            checker
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type
                .unwrap()
        })
        .collect()
}

fn assert_union(checker: &CanonicalCheckerContext<'_>, actual: TypeId, expected: &[TypeId]) {
    let TypeData::Union(union) = checker.store().type_payload(actual).unwrap().data() else {
        panic!("expected the actual optional parameter union");
    };
    assert_eq!(union.union.types.len(), expected.len());
    assert!(expected.iter().all(|type_| union.union.types.contains(type_)));
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
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = node(parsed, id);
                (
                    store.type_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.value_symbol_links(symbol).cloned(),
                    store.type_alias_links(symbol).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        checker.diagnostics().clone(),
    )
}

#[test]
fn lambda_callback_captures_its_alias_parameter_without_a_generic_call_signature() {
    let parsed = parse_source_file(CALLBACK);
    let library = parse_source_file(ES5);
    let callback = alias(&parsed, "Callback");
    assert_eq!(callback.formals.len(), 1);
    assert_eq!(callback.parameters.len(), 2);

    for type_first in [false, true] {
        let mut checker = context(&parsed, &library);
        let cold = type_first.then(|| checker.get_type_from_type_node(callback.body).unwrap());
        checker.check_source_file(FILE).unwrap();
        let owner = symbol(&checker, callback.declaration);
        let callable = checker.get_declared_type_of_symbol(owner).unwrap();
        assert_eq!(checker.get_type_from_type_node(callback.body), Ok(callable));
        if let Some(cold) = cold {
            assert_eq!(callable, cold);
        }
        let formal_owner = symbol(&checker, callback.formals[0]);
        let formal = checker.get_declared_type_of_symbol(formal_owner).unwrap();
        let formal_record = checker.store().type_payload(formal).unwrap();
        assert_eq!(formal_record.symbol(), Some(formal_owner));
        assert!(matches!(formal_record.data(), TypeData::TypeParameter(_)));
        let alias_links = checker.store().type_alias_links(owner).unwrap();
        assert_eq!(alias_links.declared_type, Some(callable));
        assert_eq!(alias_links.type_parameters.as_deref(), Some(&[formal][..]));
        let record = checker.store().type_payload(callable).unwrap();
        assert_eq!(record.symbol(), Some(symbol(&checker, callback.body)));
        let metadata = checker.store().type_alias(record.alias().unwrap()).unwrap();
        assert_eq!(metadata.symbol(), Some(owner));
        assert_eq!(metadata.type_arguments(), Some(&[formal][..]));

        let selected = signature(&checker, callable);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let (string, null, undefined, void) = (
            bootstrap.string_type,
            bootstrap.null_type,
            bootstrap.undefined_type,
            bootstrap.void_type,
        );
        let expected_parameters = callback
            .parameters
            .iter()
            .map(|&parameter| symbol(&checker, parameter))
            .collect::<Vec<_>>();
        let actual = parameter_types(&checker, selected);
        let TypeData::Union(error) = checker.store().type_payload(actual[0]).unwrap().data()
        else {
            panic!("the error parameter must retain its union");
        };
        let error = *error
            .union
            .types
            .iter()
            .find(|&&type_| ![string, null, undefined].contains(&type_))
            .unwrap();
        let error_owner = checker
            .store()
            .type_payload(error)
            .unwrap()
            .symbol()
            .unwrap();
        let error_symbol = checker.store().symbol(error_owner).unwrap();
        assert_eq!(error_symbol.name().as_utf8(), Some("Error"));
        assert!(
            error_symbol
                .declarations()
                .unwrap()
                .iter()
                .all(|node| node.file == LIBRARY)
        );
        assert_union(&checker, actual[0], &[error, string, null, undefined]);
        assert_union(&checker, actual[1], &[formal, undefined]);
        for (index, &parameter) in callback.parameters.iter().enumerate() {
            let record = parsed.arena.get(parameter.node).unwrap();
            assert_eq!(record.parent, Some(callback.body.node));
            let NodeData::ParameterDeclaration(parameter) = &record.data else {
                unreachable!();
            };
            assert!(parameter.question_token.is_some());
            assert_eq!(
                checker.get_type_at_location(node(&parsed, parameter.name)),
                Ok(actual[index])
            );
            if index == 1 {
                assert_eq!(
                    checker.get_type_from_type_node(node(&parsed, parameter.type_.unwrap())),
                    Ok(formal)
                );
            }
        }
        assert_eq!(checker.get_type_from_type_node(callback.returned), Ok(void));
        assert_eq!(checker.get_return_type_of_signature(selected), Ok(void));
        let record = checker.store().signature(selected).unwrap();
        assert_eq!(record.declaration(), Some(callback.body));
        assert_eq!(record.parameters(), expected_parameters);
        assert!(record.type_parameters().is_empty());
        assert_eq!(record.min_argument_count(), 0);
        assert_eq!(record.this_parameter(), None);
        assert!(!record.has_rest_parameter());
        assert_eq!(record.target(), None);
        assert_eq!(record.mapper(), None);
        assert!(checker.diagnostics().is_empty());

        let before = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(checker.get_declared_type_of_symbol(owner), Ok(callable));
            assert_eq!(checker.get_type_from_type_node(callback.body), Ok(callable));
            assert_eq!(signature(&checker, callable), selected);
            assert_eq!(parameter_types(&checker, selected), actual);
            assert_eq!(checker.get_return_type_of_signature(selected), Ok(void));
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

#[test]
fn lambda_callback_instances_keep_concrete_and_default_results_and_native_errors() {
    let parsed = parse_source_file(&format!(
        "{CALLBACK}\
         declare const numeric: Callback<number>;\n\
         declare const defaulted: Callback;\n\
         numeric();\n\
         numeric(null, 1);\n\
         defaulted(null, 'allowed by the written default');\n\
         numeric(null, 'wrong');\n"
    ));
    let library = parse_source_file(ES5);
    let callback = alias(&parsed, "Callback");
    let mut checker = context(&parsed, &library);
    checker.check_source_file(FILE).unwrap();
    let numeric_name = variable(&parsed, "numeric");
    let defaulted_name = variable(&parsed, "defaulted");
    let numeric = checker.get_type_at_location(numeric_name).unwrap();
    let defaulted = checker.get_type_at_location(defaulted_name).unwrap();
    assert_ne!(numeric, defaulted);
    let numeric_signature = signature(&checker, numeric);
    let defaulted_signature = signature(&checker, defaulted);
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let (number, undefined, any, void) = (
        bootstrap.number_type,
        bootstrap.undefined_type,
        bootstrap.any_type,
        bootstrap.void_type,
    );
    let numeric_parameters = parameter_types(&checker, numeric_signature);
    let defaulted_parameters = parameter_types(&checker, defaulted_signature);
    assert_eq!(numeric_parameters[0], defaulted_parameters[0]);
    assert_union(&checker, numeric_parameters[1], &[number, undefined]);
    assert_eq!(defaulted_parameters[1], any);
    for selected in [numeric_signature, defaulted_signature] {
        assert_eq!(checker.get_return_type_of_signature(selected), Ok(void));
        let record = checker.store().signature(selected).unwrap();
        assert_eq!(record.declaration(), Some(callback.body));
        assert!(record.type_parameters().is_empty());
        assert_eq!(record.min_argument_count(), 0);
    }
    let calls = calls(&parsed);
    assert_eq!(calls.len(), 4);
    for &call in &calls {
        assert_eq!(checker.get_type_at_location(call), Ok(void));
    }
    let NodeData::CallExpression(bad_call) = &parsed.arena.get(calls[3].node).unwrap().data else {
        unreachable!();
    };
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected only the wrong numeric result diagnostic");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(
        diagnostic.node,
        Some(node(&parsed, bad_call.arguments.nodes[1]))
    );
    assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'string' is not assignable to parameter of type 'number'."
    );
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
    let before = snapshot(&checker, &parsed);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        assert_eq!(checker.get_type_at_location(numeric_name), Ok(numeric));
        assert_eq!(checker.get_type_at_location(defaulted_name), Ok(defaulted));
        assert_eq!(
            parameter_types(&checker, numeric_signature),
            numeric_parameters
        );
        assert_eq!(
            parameter_types(&checker, defaulted_signature),
            defaulted_parameters
        );
        assert_eq!(snapshot(&checker, &parsed), before);
    }
}

#[test]
fn captured_alias_defaults_preserve_required_parameters_and_non_generic_controls() {
    let parsed = parse_source_file(concat!(
        "type Transform<Input, Output = Input> = (value: Input, fallback?: Output) => Output;\n",
        "type Plain = (value?: string) => number;\n",
        "declare const convert: Transform<number, string>;\n",
        "declare const identity: Transform<number>;\n",
        "declare const plain: Plain;\n",
        "const text = convert(1);\n",
        "const count = identity(1);\n",
        "const plainCount = plain();\n",
        "convert();\n",
    ));
    let library = parse_source_file(ES5);
    let transform = alias(&parsed, "Transform");
    let mut checker = context(&parsed, &library);
    checker.check_source_file(FILE).unwrap();
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let (number, string, undefined) = (
        bootstrap.number_type,
        bootstrap.string_type,
        bootstrap.undefined_type,
    );
    for (name, first, second, returned, minimum) in [
        ("convert", Some(number), string, string, 1),
        ("identity", Some(number), number, number, 1),
        ("plain", None, string, number, 0),
    ] {
        let callable = checker
            .get_type_at_location(variable(&parsed, name))
            .unwrap();
        let selected = signature(&checker, callable);
        let parameters = parameter_types(&checker, selected);
        if let Some(first) = first {
            assert_eq!(parameters.len(), 2);
            assert_eq!(parameters[0], first);
        } else {
            assert_eq!(parameters.len(), 1);
        }
        assert_union(&checker, *parameters.last().unwrap(), &[second, undefined]);
        assert_eq!(checker.get_return_type_of_signature(selected), Ok(returned));
        let record = checker.store().signature(selected).unwrap();
        assert!(record.type_parameters().is_empty());
        assert_eq!(record.min_argument_count(), minimum);
    }
    for (name, expected) in [("text", string), ("count", number), ("plainCount", number)] {
        assert_eq!(
            checker.get_type_at_location(variable(&parsed, name)),
            Ok(expected)
        );
    }
    let calls = calls(&parsed);
    assert_eq!(calls.len(), 4);
    let NodeData::CallExpression(missing) = &parsed.arena.get(calls[3].node).unwrap().data else {
        unreachable!();
    };
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected only the missing required argument diagnostic");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2554);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.node, Some(node(&parsed, missing.expression)));
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Expected 1-2 arguments, but got 0."
    );
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("expected the original required parameter location");
    };
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(related.node, Some(transform.parameters[0]));
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument for 'value' was not provided."
    );
    let before = snapshot(&checker, &parsed);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        assert_eq!(snapshot(&checker, &parsed), before);
    }
}

#[test]
fn captured_function_alias_keeps_this_parameter_unsupported_without_publication() {
    let parsed = parse_source_file("type Receiver<T> = (this: T, value: T) => T;");
    let library = parse_source_file(ES5);
    let receiver = alias(&parsed, "Receiver");
    let mut checker = context(&parsed, &library);
    let before = snapshot(&checker, &parsed);
    for _ in 0..2 {
        assert_eq!(
            checker.get_type_from_type_node(receiver.body),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedSyntax {
                    node: receiver.parameters[0],
                    kind: SyntaxKind::FunctionType,
                }
            ))
        );
        assert!(checker.store().type_node_links(receiver.body).is_none());
        assert!(checker.store().signature_links(receiver.body).is_none());
        assert_eq!(snapshot(&checker, &parsed), before);
        assert!(checker.diagnostics().is_empty());
    }
}

#[test]
fn captured_function_alias_preserves_concrete_array_parameters() {
    let parsed = parse_source_file(concat!(
        "type Select<T> = (rows: string[], value: T) => T;\n",
        "declare const select: Select<number>;\n",
        "declare const rows: string[];\n",
        "const result = select(rows, 1);\n",
    ));
    let library = parse_source_file(ES5);
    let select = alias(&parsed, "Select");
    let mut checker = context(&parsed, &library);
    checker.check_source_file(FILE).unwrap();
    let rows_name = variable(&parsed, "rows");
    let rows = checker.get_type_at_location(rows_name).unwrap();
    let select_name = variable(&parsed, "select");
    let callable = checker.get_type_at_location(select_name).unwrap();
    let selected = signature(&checker, callable);
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    let TypeData::TypeReference(array) = checker.store().type_payload(rows).unwrap().data()
    else {
        panic!("the rows parameter must retain its actual array type");
    };
    assert_eq!(array.resolved_type_arguments.as_deref(), Some(&[string][..]));
    assert_eq!(parameter_types(&checker, selected), [rows, number]);
    assert_eq!(checker.get_return_type_of_signature(selected), Ok(number));
    let declared = checker.get_type_from_type_node(select.body).unwrap();
    let original = signature(&checker, declared);
    assert_eq!(parameter_types(&checker, original)[0], rows);
    let calls = calls(&parsed);
    let [call] = calls.as_slice() else {
        panic!("expected one selected call");
    };
    assert_eq!(checker.get_type_at_location(*call), Ok(number));
    assert_eq!(
        checker.get_type_at_location(variable(&parsed, "result")),
        Ok(number)
    );
    assert!(checker.diagnostics().is_empty());
    let before = snapshot(&checker, &parsed);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        assert_eq!(checker.get_type_at_location(select_name), Ok(callable));
        assert_eq!(checker.get_type_at_location(rows_name), Ok(rows));
        assert_eq!(parameter_types(&checker, selected), [rows, number]);
        assert_eq!(checker.get_return_type_of_signature(selected), Ok(number));
        assert_eq!(snapshot(&checker, &parsed), before);
    }
}
