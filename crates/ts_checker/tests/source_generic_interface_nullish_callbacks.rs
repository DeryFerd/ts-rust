use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(206_940);
const SOURCE: FileId = FileId::new(206_941);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(source: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (SOURCE, source, "\"/project/nullish-callbacks.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let default_library = file == LIBRARY;
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    default_library,
                    default_library,
                    CanonicalModuleState::Script,
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
            no_implicit_this: true,
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
    NodeRef::new(parsed.arena.id(), SOURCE, id)
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)))
        .collect::<Vec<_>>();
    result.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    result
}

fn variable(parsed: &ParseResult, name: &str) -> NodeRef {
    nodes(parsed, SyntaxKind::VariableDeclaration)
        .into_iter()
        .find(|declaration| {
            let NodeData::VariableDeclaration(data) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!()
            };
            matches!(&parsed.arena.get(data.name).unwrap().data,
                NodeData::Identifier(identifier) if identifier.text == name)
        })
        .expect("the variable must have a real source declaration")
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(SOURCE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn value_type(checker: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .expect("the checked value must retain its type")
}

fn signature(checker: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(location)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the declaration or call must retain its signature")
}

fn callable_signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("the callback or method must retain a callable object")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("the callable must have exactly one signature")
    };
    *signature
}

fn parameter_type(checker: &CanonicalCheckerContext<'_>, signature: SignatureId) -> TypeId {
    let [parameter] = checker.store().signature(signature).unwrap().parameters() else {
        panic!("the signature must have exactly one parameter")
    };
    value_type(checker, *parameter)
}

fn nullish_callback(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> TypeId {
    let store = checker.store();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    let record = store.type_payload(type_).unwrap();
    let TypeData::Union(union) = record.data() else {
        panic!("the callback must retain its written null and undefined members")
    };
    assert_eq!(union.union.types.len(), 3);
    assert!(union.union.types.contains(&bootstrap.null_type));
    assert!(union.union.types.contains(&bootstrap.undefined_type));
    assert!(record.alias().is_none());
    assert!(union.origin.is_none());
    *union
        .union
        .types
        .iter()
        .find(|&&member| member != bootstrap.null_type && member != bootstrap.undefined_type)
        .unwrap()
}

fn assert_callback(
    checker: &mut CanonicalCheckerContext<'_>,
    callback: TypeId,
    argument: TypeId,
    result: TypeId,
) -> SignatureId {
    let signature = callable_signature(checker, callback);
    assert_eq!(parameter_type(checker, signature), argument);
    assert_eq!(checker.get_return_type_of_signature(signature), Ok(result));
    let record = checker.store().signature(signature).unwrap();
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.min_argument_count(), 1);
    signature
}

#[derive(Debug, Eq, PartialEq)]
struct Checked {
    types: Vec<TypeId>,
    signatures: Vec<SignatureId>,
    argument_target: TypeId,
}

#[allow(clippy::too_many_lines)] // Follow the original callback through receiver and call mapping.
fn checked_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    invalid: bool,
) -> Checked {
    let interface = nodes(parsed, SyntaxKind::InterfaceDeclaration)[0];
    let method = nodes(parsed, SyntaxKind::MethodSignature)[0];
    let formals = nodes(parsed, SyntaxKind::TypeParameter);
    let [outer_node, inner_node] = formals.as_slice() else {
        panic!("the receiver and method must keep their separate formals")
    };
    assert_eq!(
        parsed.arena.get(outer_node.node).unwrap().parent,
        Some(interface.node)
    );
    assert_eq!(
        parsed.arena.get(inner_node.node).unwrap().parent,
        Some(method.node)
    );
    let owner = symbol(checker, interface);
    let method_owner = symbol(checker, method);
    let outer_owner = symbol(checker, *outer_node);
    let inner_owner = symbol(checker, *inner_node);
    assert_ne!(outer_owner, inner_owner);
    let target = checker.get_declared_type_of_symbol(owner).unwrap();
    let outer = checker.get_declared_type_of_symbol(outer_owner).unwrap();
    let inner = checker.get_declared_type_of_symbol(inner_owner).unwrap();
    assert_ne!(outer, inner);
    for (type_, owner) in [(outer, outer_owner), (inner, inner_owner)] {
        let record = checker.store().type_payload(type_).unwrap();
        assert_eq!(record.symbol(), Some(owner));
        let TypeData::TypeParameter(parameter) = record.data() else {
            panic!("the formal must retain its binder-owned type")
        };
        assert!(parameter.target.is_none());
        assert!(parameter.mapper.is_none());
    }
    let original_method = value_type(checker, method_owner);
    let original_signature = signature(checker, method);
    assert_eq!(
        callable_signature(checker, original_method),
        original_signature
    );
    let original_union = parameter_type(checker, original_signature);
    let original_callback = nullish_callback(checker, original_union);
    let original_callback_signature = assert_callback(checker, original_callback, outer, inner);
    let original_record = checker.store().signature(original_signature).unwrap();
    assert_eq!(original_record.declaration(), Some(method));
    assert_eq!(original_record.type_parameters(), [inner]);
    assert_eq!(original_record.min_argument_count(), 0);
    assert!(original_record.target().is_none());
    assert!(original_record.mapper().is_none());
    let callback_declaration = checker
        .store()
        .signature(original_callback_signature)
        .unwrap()
        .declaration()
        .unwrap();
    assert_eq!(
        parsed.arena.get(callback_declaration.node).unwrap().kind,
        SyntaxKind::FunctionType
    );
    let callback_owner = symbol(checker, callback_declaration);
    assert_eq!(
        checker
            .store()
            .type_payload(original_callback)
            .unwrap()
            .symbol(),
        Some(callback_owner)
    );

    let calls = nodes(parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), if invalid { 2 } else { 4 });
    let NodeData::CallExpression(first) = &parsed.arena.get(calls[0].node).unwrap().data else {
        unreachable!()
    };
    let access = node(parsed, first.expression);
    let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(access.node).unwrap().data
    else {
        panic!("the callback must belong to the real generic interface receiver")
    };
    let receiver = checker
        .get_type_at_location(node(parsed, property.expression))
        .unwrap();
    let copied_method = checker.get_type_at_location(access).unwrap();
    let copied_signature = callable_signature(checker, copied_method);
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let number = bootstrap.number_type;
    let TypeData::TypeReference(reference) = checker.store().type_payload(receiver).unwrap().data()
    else {
        panic!("the receiver must be Channel<string>")
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[string][..])
    );
    let TypeData::Object(object) = checker.store().type_payload(copied_method).unwrap().data()
    else {
        unreachable!()
    };
    assert_eq!(object.target, Some(original_method));
    assert_eq!(
        checker.store().map_type(object.mapper.unwrap(), outer),
        Some(string)
    );
    let copied = checker.store().signature(copied_signature).unwrap();
    assert_eq!(copied.target(), Some(original_signature));
    assert_eq!(copied.declaration(), Some(method));
    let [copied_inner] = copied.type_parameters() else {
        panic!("the copied generic method must keep its own fresh formal")
    };
    let copied_inner = *copied_inner;
    let method_mapper = copied.mapper().unwrap();
    assert_ne!(copied_inner, inner);
    assert_ne!(copied_inner, outer);
    let TypeData::TypeParameter(parameter) =
        checker.store().type_payload(copied_inner).unwrap().data()
    else {
        unreachable!()
    };
    assert_eq!(parameter.target, Some(inner));
    assert_eq!(parameter.mapper, Some(method_mapper));
    let copied_union = parameter_type(checker, copied_signature);
    let copied_callback = nullish_callback(checker, copied_union);
    let copied_callback_signature = assert_callback(checker, copied_callback, string, copied_inner);
    let TypeData::Object(object) = checker
        .store()
        .type_payload(copied_callback)
        .unwrap()
        .data()
    else {
        unreachable!()
    };
    assert_eq!(object.target, Some(original_callback));
    assert_eq!(object.mapper, Some(method_mapper));
    assert_eq!(
        checker
            .store()
            .type_payload(copied_callback)
            .unwrap()
            .symbol(),
        Some(callback_owner)
    );

    let selected = signature(checker, calls[0]);
    let selected_record = checker.store().signature(selected).unwrap();
    assert_eq!(selected_record.target(), Some(copied_signature));
    assert_eq!(selected_record.declaration(), Some(method));
    assert!(selected_record.type_parameters().is_empty());
    assert_eq!(
        checker
            .store()
            .map_type(selected_record.mapper().unwrap(), copied_inner),
        Some(number)
    );
    let argument_target = parameter_type(checker, selected);
    let selected_callback = nullish_callback(checker, argument_target);
    let selected_callback_signature = assert_callback(checker, selected_callback, string, number);
    for callback in [copied_callback_signature, selected_callback_signature] {
        let record = checker.store().signature(callback).unwrap();
        assert_eq!(record.declaration(), Some(callback_declaration));
        assert!(record.target().is_some());
        assert!(record.mapper().is_some());
    }
    let mut types = vec![
        target,
        outer,
        inner,
        receiver,
        original_union,
        copied_inner,
        copied_union,
        original_callback,
        copied_callback,
        selected_callback,
    ];
    let mut signatures = vec![
        original_signature,
        original_callback_signature,
        copied_signature,
        copied_callback_signature,
        selected,
        selected_callback_signature,
    ];
    for (index, call) in calls.into_iter().enumerate() {
        let expected = if index == 0 || invalid {
            number
        } else {
            string
        };
        assert_eq!(checker.get_type_at_location(call), Ok(expected));
        let selected = signature(checker, call);
        assert_eq!(checker.get_return_type_of_signature(selected), Ok(expected));
        types.push(expected);
        signatures.push(selected);
    }
    Checked {
        types,
        signatures,
        argument_target,
    }
}

fn check_case(invalid: bool) {
    let mut text = concat!(
        "interface Channel<T> { map<R = T>(callback?: (((value: T) => R)) | undefined | null): R; }\n",
        "declare const channel: Channel<string>;\n",
        "declare const good: (value: string) => number;\n",
        "const result = channel.map<number>(good);\n",
    ).to_owned();
    text.push_str(if invalid {
        "declare const bad: (value: number) => number;\nchannel.map<number>(bad);\n"
    } else {
        "const fromNull = channel.map(null);\nconst fromUndefined = channel.map(undefined);\nconst fromDefault = channel.map();\n"
    });
    let source = parse_source_file(&text);
    let library = parse_source_file(ES5);
    let mut checker = context(&source, &library);
    checker.check_source_file(SOURCE).unwrap();
    let checked = checked_state(&mut checker, &source, invalid);
    if invalid {
        let calls = nodes(&source, SyntaxKind::CallExpression);
        let NodeData::CallExpression(call) = &source.arena.get(calls[1].node).unwrap().data else {
            unreachable!()
        };
        let [argument] = call.arguments.nodes.as_slice() else {
            panic!("the wrong callback must remain the real call argument")
        };
        let source_type = value_type(&checker, symbol(&checker, variable(&source, "bad")));
        let arguments = [
            checker.type_to_string(source_type).unwrap(),
            checker.type_to_string(checked.argument_target).unwrap(),
        ];
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("the wrong callback must produce one native argument error")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.node, Some(node(&source, *argument)));
        assert!(diagnostic.range_override.is_none());
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
    } else {
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
    }
    let root = checker.source_file(SOURCE).unwrap();
    assert!(
        checker
            .store()
            .source_file_links(root)
            .unwrap()
            .type_checked
    );
    let snapshot = |checker: &CanonicalCheckerContext<'_>| {
        let store = checker.store();
        (
            [
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.type_alias_len(),
            ],
            source
                .arena
                .iter()
                .map(|(id, _)| {
                    let node = node(&source, id);
                    (
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                        checker
                            .file(SOURCE)
                            .unwrap()
                            .1
                            .symbol(node)
                            .and_then(|symbol| store.get_merged_symbol(symbol))
                            .and_then(|symbol| store.value_symbol_links(symbol))
                            .cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            store.source_file_links(root).cloned(),
            checker.diagnostics().clone(),
        )
    };
    let warm = snapshot(&checker);
    for _ in 0..2 {
        checker.check_source_file(SOURCE).unwrap();
        assert_eq!(checked_state(&mut checker, &source, invalid), checked);
        checker.recheck_source_file(SOURCE).unwrap();
        assert_eq!(checked_state(&mut checker, &source, invalid), checked);
        assert_eq!(snapshot(&checker), warm);
    }
}

#[test]
fn generic_interface_nullish_callbacks_keep_receiver_and_method_mapping() {
    check_case(false);
}

#[test]
fn generic_interface_nullish_callbacks_report_the_wrong_callback_argument() {
    check_case(true);
}
