use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    SourceCheckError, TypeData, TypeId, UnsupportedSourceSyntax, VariableUnsupported,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(204_620);
const LIBRARY: FileId = FileId::new(204_621);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

const STRING_SOURCE: &str = r#"
export function create(): (value: number) => string {
    const earlier = (value: number): string => { return later(value); };
    const later = (value: number): string => { return "done"; };
    return earlier;
}
const callback = create();
const result: string = callback(1);
"#;

const VOID_SOURCE: &str = r#"
export function create(): () => void {
    const earlier = (): void => { later(1); };
    const later = (value: number) => { const checked: number = value; };
    return earlier;
}
const callback = create();
const result: void = callback();
"#;

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (FILE, parsed, "\"/project/forward-closure-references.ts\""),
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
struct Variable {
    declaration: NodeRef,
    name: NodeRef,
    initializer: NodeRef,
}

fn variable(parsed: &ParseResult, expected: &str) -> Variable {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::VariableDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(data.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| Variable {
                declaration: node(parsed, id),
                name: node(parsed, data.name),
                initializer: node(parsed, data.initializer.unwrap()),
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn factory(parsed: &ParseResult) -> (NodeRef, NodeRef, NodeRef) {
    let functions = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::FunctionDeclaration(data) = &record.data else {
                return None;
            };
            Some((
                node(parsed, id),
                node(parsed, data.name.unwrap()),
                node(parsed, data.type_.unwrap()),
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(functions.len(), 1);
    functions[0]
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let bound = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(bound).unwrap()
}

fn calls_to(parsed: &ParseResult, expected: &str) -> Vec<(NodeRef, NodeRef, Vec<NodeRef>)> {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(call.expression)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    node(parsed, id),
                    node(parsed, call.expression),
                    call.arguments
                        .nodes
                        .iter()
                        .map(|&id| node(parsed, id))
                        .collect(),
                )
            })
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|(call, _, _)| parsed.arena.get(call.node).unwrap().range.start);
    calls
}

fn signature(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    type_: TypeId,
    declaration: NodeRef,
    expected_parameters: &[TypeId],
    returned: TypeId,
) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the real callable object");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let signatures = object.structured.signatures.as_deref().unwrap();
    assert_eq!(signatures.len(), 1);
    let selected = signatures[0];
    let parameters = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::FunctionDeclaration(data) => &data.parameters,
        NodeData::FunctionTypeNode(data) => &data.parameters,
        NodeData::ArrowFunction(data) => &data.parameters,
        _ => panic!("expected the source callable declaration"),
    };
    assert_eq!(parameters.nodes.len(), expected_parameters.len());
    let mut owners = Vec::new();
    for (&parameter, &expected) in parameters.nodes.iter().zip(expected_parameters) {
        let owner = symbol(checker, node(parsed, parameter));
        let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter).unwrap().data
        else {
            unreachable!();
        };
        assert_eq!(
            checker.get_type_at_location(node(parsed, data.name)),
            Ok(expected)
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type,
            Some(expected)
        );
        owners.push(owner);
    }
    assert_eq!(checker.get_return_type_of_signature(selected), Ok(returned));
    let record = checker.store().signature(selected).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.parameters(), owners);
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(expected_parameters.len()).unwrap()
    );
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.this_parameter(), None);
    assert!(!record.has_rest_parameter());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.resolved_return_type(), Some(returned));
    selected
}

fn assert_types(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult, is_void: bool) {
    let intrinsics = checker.store().intrinsic_bootstrap().unwrap();
    let number = intrinsics.number_type;
    let returned = if is_void {
        intrinsics.void_type
    } else {
        intrinsics.string_type
    };
    let earlier_parameters = if is_void { Vec::new() } else { vec![number] };
    let (factory_node, factory_name, annotation) = factory(parsed);
    let declared = checker.get_type_from_type_node(annotation).unwrap();
    let declared_signature = signature(
        checker,
        parsed,
        declared,
        annotation,
        &earlier_parameters,
        returned,
    );
    let factory_type = checker.get_type_at_location(factory_name).unwrap();
    let factory_signature = signature(checker, parsed, factory_type, factory_node, &[], declared);
    let mut local_signatures = Vec::new();
    for (name, parameters) in [
        ("earlier", earlier_parameters.as_slice()),
        ("later", &[number][..]),
    ] {
        let local = variable(parsed, name);
        let NodeData::VariableDeclaration(data) =
            &parsed.arena.get(local.declaration.node).unwrap().data
        else {
            unreachable!();
        };
        assert!(
            data.type_.is_none(),
            "the local callable must have no variable annotation"
        );
        let binding = symbol(checker, local.declaration);
        let owner = symbol(checker, local.initializer);
        assert_ne!(binding, owner);
        assert_eq!(
            checker.store().symbol(binding).unwrap().flags(),
            SymbolFlags::BLOCK_SCOPED_VARIABLE
        );
        assert_eq!(
            checker.store().symbol(binding).unwrap().declarations(),
            Some(&[local.declaration][..])
        );
        assert_eq!(
            checker.store().symbol(owner).unwrap().declarations(),
            Some(&[local.initializer][..])
        );
        assert_eq!(
            checker
                .file(FILE)
                .unwrap()
                .1
                .block_scope_container(local.declaration),
            Some(factory_node)
        );
        let type_ = checker.get_type_at_location(local.initializer).unwrap();
        assert_eq!(
            checker.store().type_payload(type_).unwrap().symbol(),
            Some(owner)
        );
        assert_eq!(checker.get_type_at_location(local.name), Ok(type_));
        assert_eq!(
            checker
                .store()
                .value_symbol_links(binding)
                .unwrap()
                .resolved_type,
            Some(type_)
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type,
            Some(type_)
        );
        let selected = signature(
            checker,
            parsed,
            type_,
            local.initializer,
            parameters,
            returned,
        );
        assert_ne!(selected, declared_signature);
        local_signatures.push(selected);
        if name == "later" {
            let calls = calls_to(parsed, "later");
            let [(call, callee, arguments)] = calls.as_slice() else {
                panic!("expected one deferred call");
            };
            assert_eq!(arguments.len(), 1);
            assert_eq!(checker.get_symbol_at_location(*callee), Ok(Some(binding)));
            assert_eq!(checker.get_type_at_location(*callee), Ok(type_));
            assert_eq!(checker.get_type_at_location(*call), Ok(returned));
            if matches!(
                &parsed.arena.get(arguments[0].node).unwrap().data,
                NodeData::Identifier(_)
            ) {
                let parameter = checker
                    .store()
                    .signature(local_signatures[0])
                    .unwrap()
                    .parameters()[0];
                assert_eq!(
                    checker.get_symbol_at_location(arguments[0]),
                    Ok(Some(parameter))
                );
                assert_eq!(checker.get_type_at_location(arguments[0]), Ok(number));
            }
            assert_eq!(
                checker
                    .store()
                    .signature_links(*call)
                    .unwrap()
                    .resolved_signature
                    .signature(),
                Some(selected)
            );
        }
    }
    assert_ne!(local_signatures[0], local_signatures[1]);
    if !is_void {
        assert_ne!(
            checker
                .store()
                .signature(local_signatures[0])
                .unwrap()
                .parameters(),
            checker
                .store()
                .signature(local_signatures[1])
                .unwrap()
                .parameters()
        );
    }
    let callback = variable(parsed, "callback");
    assert_eq!(checker.get_type_at_location(callback.name), Ok(declared));
    assert_eq!(
        checker.get_type_at_location(callback.initializer),
        Ok(declared)
    );
    assert_eq!(
        checker
            .store()
            .signature_links(callback.initializer)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(factory_signature)
    );
    let result = variable(parsed, "result");
    assert_eq!(checker.get_type_at_location(result.name), Ok(returned));
    assert_eq!(
        checker.get_type_at_location(result.initializer),
        Ok(returned)
    );
    assert_eq!(
        checker
            .store()
            .signature_links(result.initializer)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(declared_signature)
    );
    assert!(checker.store().type_resolution_is_empty());
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(FILE).unwrap())
            .unwrap()
            .type_checked
    );
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
            store.type_resolution_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let location = node(parsed, id);
                (
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

#[test]
fn local_closure_reads_later_callable_with_real_types_and_replay() {
    for (source, is_void) in [(STRING_SOURCE, false), (VOID_SOURCE, true)] {
        let parsed = parse_source_file(source);
        let library = parse_source_file(ES5);
        let callee = calls_to(&parsed, "later")[0].1;
        for query_first in [false, true] {
            let mut checker = context(&parsed, &library);
            let first = query_first.then(|| checker.get_type_at_location(callee).unwrap());
            checker.check_source_file(FILE).unwrap();
            assert_types(&mut checker, &parsed, is_void);
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            if let Some(first) = first {
                assert_eq!(checker.get_type_at_location(callee), Ok(first));
            }
            let before = snapshot(&checker, &parsed);
            for _ in 0..2 {
                checker.check_source_file(FILE).unwrap();
                checker.recheck_source_file(FILE).unwrap();
                assert_types(&mut checker, &parsed, is_void);
                assert_eq!(snapshot(&checker, &parsed), before);
            }
        }
    }
}

#[test]
fn deferred_local_calls_keep_native_argument_and_return_errors() {
    for wrong_argument in [true, false] {
        let source = if wrong_argument {
            STRING_SOURCE.replace("later(value)", "later(\"bad\")")
        } else {
            STRING_SOURCE.replace("return \"done\";", "return value;")
        };
        let parsed = parse_source_file(&source);
        let library = parse_source_file(ES5);
        let (location, code, arguments, message) = if wrong_argument {
            (
                calls_to(&parsed, "later")[0].2[0],
                2345,
                ["string", "number"],
                "Argument of type 'string' is not assignable to parameter of type 'number'.",
            )
        } else {
            let later = variable(&parsed, "later");
            let NodeData::ArrowFunction(arrow) =
                &parsed.arena.get(later.initializer.node).unwrap().data
            else {
                unreachable!();
            };
            let returns = parsed
                .arena
                .iter()
                .filter_map(|(id, record)| {
                    (matches!(&record.data, NodeData::ReturnStatement(_))
                        && record.parent == Some(arrow.body))
                    .then_some(node(&parsed, id))
                })
                .collect::<Vec<_>>();
            assert_eq!(returns.len(), 1);
            (
                returns[0],
                2322,
                ["number", "string"],
                "Type 'number' is not assignable to type 'string'.",
            )
        };
        for query_first in [false, true] {
            let mut checker = context(&parsed, &library);
            if query_first {
                checker
                    .get_type_at_location(calls_to(&parsed, "later")[0].1)
                    .unwrap();
            }
            checker.check_source_file(FILE).unwrap();
            assert_types(&mut checker, &parsed, false);
            let diagnostics = checker.diagnostics().as_slice();
            assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
            let diagnostic = &diagnostics[0];
            assert_eq!(diagnostic.node, Some(location));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.diagnostic.category(), Category::Error);
            assert_eq!(diagnostic.diagnostic.arguments, arguments);
            assert!(diagnostic.diagnostic.details.is_empty());
            assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
            assert!(diagnostic.related_information.is_empty());
            let before = snapshot(&checker, &parsed);
            for _ in 0..2 {
                checker.check_source_file(FILE).unwrap();
                checker.recheck_source_file(FILE).unwrap();
                assert_types(&mut checker, &parsed, false);
                assert_eq!(snapshot(&checker, &parsed), before);
            }
        }
    }
}

#[test]
fn deferred_closure_does_not_make_an_eager_later_read_prior() {
    let source = STRING_SOURCE.replace(
        "    const later =",
        "    const eager = later(1);\n    const later =",
    );
    let parsed = parse_source_file(&source);
    let library = parse_source_file(ES5);
    let calls = calls_to(&parsed, "later");
    assert_eq!(calls.len(), 2);
    let later = variable(&parsed, "later");
    let eager = variable(&parsed, "eager");
    assert_eq!(calls[1].0, eager.initializer);
    let mut checker = context(&parsed, &library);
    let expected = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Variable(
        VariableUnsupported::IdentifierNotPrior {
            node: calls[1].1,
            symbol: symbol(&checker, later.declaration),
            declaration: later.declaration,
        },
    ));
    for _ in 0..2 {
        assert_eq!(checker.check_source_file(FILE), Err(expected));
        assert!(checker.diagnostics().is_empty());
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
        assert!(checker.store().type_resolution_is_empty());
    }
}
