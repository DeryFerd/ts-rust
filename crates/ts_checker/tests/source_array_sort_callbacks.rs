use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(497_800);
const SOURCE_FILE: FileId = FileId::new(497_801);
const LIBRARY: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'arena>(
    library: &'arena ParseResult,
    parsed: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (LIBRARY_FILE, library, "\"/lib/lib.es5.d.ts\"", true),
        (SOURCE_FILE, parsed, "\"/project/sort.ts\"", false),
    ];
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, library) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    if library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _, _) in &files {
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
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), SOURCE_FILE, id)
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    assert_eq!(parsed.arena.get(id).unwrap().parent, Some(parent.node));
    node(parsed, id)
}

fn variable(parsed: &ParseResult, expected: &str) -> NodeRef {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::VariableDeclaration(data) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(data.name)?.data else {
            return None;
        };
        (name.text == expected).then_some(node(parsed, id))
    });
    let result = matches.next().expect("the local declaration must exist");
    assert!(matches.next().is_none());
    result
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(location)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

#[derive(Clone, Copy)]
struct SortCall {
    local: NodeRef,
    call: NodeRef,
    callee: NodeRef,
    receiver: NodeRef,
    arrow: NodeRef,
    parameters: [NodeRef; 2],
    names: [NodeRef; 2],
    body: NodeRef,
}

fn sort_call(parsed: &ParseResult, local_name: &str) -> SortCall {
    let local = variable(parsed, local_name);
    let NodeData::VariableDeclaration(local_data) = &parsed.arena.get(local.node).unwrap().data
    else {
        unreachable!()
    };
    let call = child(parsed, local, local_data.initializer.unwrap());
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("the local initializer must be the original call")
    };
    let callee = child(parsed, call, call_data.expression);
    let NodeData::PropertyAccessExpression(access) = &parsed.arena.get(callee.node).unwrap().data
    else {
        unreachable!()
    };
    let name = child(parsed, callee, access.name);
    assert!(matches!(&parsed.arena.get(name.node).unwrap().data,
        NodeData::Identifier(name) if name.text == "sort"));
    let receiver = child(parsed, callee, access.expression);
    let [arrow] = call_data.arguments.nodes.as_slice() else {
        unreachable!()
    };
    let arrow = child(parsed, call, *arrow);
    let NodeData::ArrowFunction(data) = &parsed.arena.get(arrow.node).unwrap().data else {
        unreachable!()
    };
    assert!(data.type_parameters.is_none());
    assert!(data.type_.is_none());
    let [left, right] = data.parameters.nodes.as_slice() else {
        unreachable!()
    };
    let parameters = [child(parsed, arrow, *left), child(parsed, arrow, *right)];
    let names = parameters.map(|parameter| {
        let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
        else {
            unreachable!()
        };
        assert!(data.type_.is_none());
        assert!(data.initializer.is_none());
        assert!(data.question_token.is_none());
        assert!(data.dot_dot_dot_token.is_none());
        child(parsed, parameter, data.name)
    });
    SortCall {
        local,
        call,
        callee,
        receiver,
        arrow,
        parameters,
        names,
        body: child(parsed, arrow, data.body),
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Observation {
    receiver: TypeId,
    result: TypeId,
    callback: TypeId,
    callback_signature: SignatureId,
    selected: SignatureId,
    method: SemanticSymbolId,
}

fn observe(context: &mut CanonicalCheckerContext<'_>, call: SortCall, array: bool) -> Observation {
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let parameter_type = if array { number } else { string };
    let parameters = call.parameters.map(|parameter| symbol(context, parameter));
    for ((parameter, name), owner) in call.parameters.into_iter().zip(call.names).zip(parameters) {
        assert_eq!(value_type(context, owner), parameter_type);
        assert_eq!(context.get_type_at_location(name), Ok(parameter_type));
        assert_eq!(context.get_symbol_at_location(name), Ok(Some(owner)));
        assert_eq!(
            context.store().symbol(owner).unwrap().declarations(),
            Some(&[parameter][..])
        );
        assert_eq!(
            context.file(SOURCE_FILE).unwrap().1.container(parameter),
            Some(call.arrow)
        );
    }
    let callback = context.get_type_at_location(call.arrow).unwrap();
    let callback_owner = symbol(context, call.arrow);
    assert_eq!(value_type(context, callback_owner), callback);
    assert_eq!(
        context.store().type_payload(callback).unwrap().symbol(),
        Some(callback_owner)
    );
    let callback_signature = signature(context, call.arrow);
    let record = context.store().signature(callback_signature).unwrap();
    assert_eq!(record.declaration(), Some(call.arrow));
    assert_eq!(record.parameters(), parameters);
    assert_eq!(record.min_argument_count(), 2);
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(
        context.get_return_type_of_signature(callback_signature),
        Ok(number)
    );
    assert_eq!(context.get_type_at_location(call.body), Ok(number));
    let receiver = context.get_type_at_location(call.receiver).unwrap();
    let result = if array {
        let TypeData::TypeReference(reference) =
            context.store().type_payload(receiver).unwrap().data()
        else {
            panic!("the receiver must remain the real Array reference")
        };
        assert_eq!(
            reference.object.target,
            Some(context.global_types().array_type)
        );
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[number][..])
        );
        receiver
    } else {
        assert!(
            !matches!(context.store().type_payload(receiver).unwrap().data(), TypeData::TypeReference(reference)
            if reference.object.target == Some(context.global_types().array_type))
        );
        string
    };
    assert_eq!(context.get_type_at_location(call.call), Ok(result));
    assert_eq!(value_type(context, symbol(context, call.local)), result);
    let method = context
        .get_symbol_at_location(call.callee)
        .unwrap()
        .unwrap();
    let method_record = context.store().symbol(method).unwrap();
    assert_eq!(method_record.flags(), SymbolFlags::METHOD);
    assert_eq!(method_record.name().as_utf8(), Some("sort"));
    if array {
        let owner = context
            .store()
            .type_payload(context.global_types().array_type)
            .unwrap()
            .symbol()
            .unwrap();
        let members = context.store().symbol(owner).unwrap().members().unwrap();
        assert_eq!(
            context
                .store()
                .symbol_table(members)
                .unwrap()
                .get_source("sort"),
            Some(method)
        );
    }
    let selected = signature(context, call.call);
    let selected_record = context.store().signature(selected).unwrap();
    let declaration = selected_record.declaration().unwrap();
    assert_eq!(
        declaration.file,
        if array { LIBRARY_FILE } else { SOURCE_FILE }
    );
    assert!(method_record.declarations().unwrap().contains(&declaration));
    assert_eq!(selected_record.parameters().len(), 1);
    assert_eq!(
        selected_record.min_argument_count(),
        if array { 0 } else { 1 }
    );
    assert_eq!(context.get_return_type_of_signature(selected), Ok(result));
    Observation {
        receiver,
        result,
        callback,
        callback_signature,
        selected,
        method,
    }
}

fn state(context: &CanonicalCheckerContext<'_>) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    let arena = context.file(SOURCE_FILE).unwrap().0;
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        context.diagnostics().clone(),
        store
            .source_file_links(context.source_file(SOURCE_FILE).unwrap())
            .cloned(),
        arena
            .iter()
            .map(|(id, _)| {
                let node = NodeRef::new(arena.id(), SOURCE_FILE, id);
                (
                    node,
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
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
                    store.declared_type_links(symbol).cloned(),
                    store.mapped_symbol_links(symbol).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store.relation_state_snapshot(),
    )
}

#[test]
fn local_array_sort_keeps_context_and_custom_sort_keeps_its_own_signature() {
    let source = r#"
interface CustomSort { sort(compare: (left: string, right: string) => number): string; }
export function numeric(values: number[], offset: number): number[] {
    const sorted = values.sort((left, right) => left - right + offset);
    return sorted;
}
export function custom(sorter: CustomSort): string {
    const text = sorter.sort((left, right) => left.length - right.length);
    return text;
}
"#;
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(source);
    let array = sort_call(&parsed, "sorted");
    let custom = sort_call(&parsed, "text");
    for query_first in [false, true] {
        let mut context = context(&library, &parsed);
        assert!(context.global_type_diagnostics().next().is_none());
        if query_first {
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            assert_eq!(context.get_type_at_location(array.names[0]), Ok(number));
        }
        context.check_source_file(SOURCE_FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let expected = (
            observe(&mut context, array, true),
            observe(&mut context, custom, false),
        );
        assert_ne!(expected.0.method, expected.1.method);
        assert_ne!(expected.0.callback_signature, expected.1.callback_signature);
        let NodeData::BinaryExpression(body) = &parsed.arena.get(array.body.node).unwrap().data
        else {
            unreachable!()
        };
        let captured = child(&parsed, array.body, body.right);
        assert!(matches!(&parsed.arena.get(captured.node).unwrap().data,
            NodeData::Identifier(name) if name.text == "offset"));
        let offset = context.get_symbol_at_location(captured).unwrap().unwrap();
        let function = context
            .file(SOURCE_FILE)
            .unwrap()
            .1
            .container(array.call)
            .unwrap();
        let NodeData::FunctionDeclaration(declaration) =
            &parsed.arena.get(function.node).unwrap().data
        else {
            unreachable!()
        };
        let [_, offset_parameter] = declaration.parameters.nodes.as_slice() else {
            unreachable!()
        };
        assert_eq!(
            offset,
            symbol(&context, child(&parsed, function, *offset_parameter))
        );
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(context.get_type_at_location(captured), Ok(number));
        assert_eq!(value_type(&context, offset), number);
        let warm = state(&context);
        for _ in 0..2 {
            context.check_source_file(SOURCE_FILE).unwrap();
            context.recheck_source_file(SOURCE_FILE).unwrap();
            assert_eq!(
                (
                    observe(&mut context, array, true),
                    observe(&mut context, custom, false)
                ),
                expected
            );
            assert_eq!(state(&context), warm);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn local_array_sort_reports_the_native_error_inside_its_callback() {
    let source = r#"
declare function acceptText(value: string): number;
export function invalid(values: number[]): number[] {
    const sorted = values.sort((left, right) => acceptText(left));
    return sorted;
}
"#;
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(source);
    let call = sort_call(&parsed, "sorted");
    let NodeData::CallExpression(body) = &parsed.arena.get(call.body.node).unwrap().data else {
        unreachable!()
    };
    let [argument] = body.arguments.nodes.as_slice() else {
        unreachable!()
    };
    let argument = child(&parsed, call.body, *argument);
    assert_eq!(
        parsed.arena.get(argument.node).unwrap().kind,
        SyntaxKind::Identifier
    );
    for query_first in [false, true] {
        let mut context = context(&library, &parsed);
        assert!(context.global_type_diagnostics().next().is_none());
        if query_first {
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            assert_eq!(context.get_type_at_location(call.names[0]), Ok(number));
        }
        context.check_source_file(SOURCE_FILE).unwrap();
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("only the original callback body argument must fail")
        };
        assert_eq!(diagnostic.node, Some(argument));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Argument of type 'number' is not assignable to parameter of type 'string'."
        );
        assert!(diagnostic.related_information.is_empty());
        let expected = observe(&mut context, call, true);
        let parameter = symbol(&context, call.parameters[0]);
        assert_eq!(
            context.get_symbol_at_location(argument),
            Ok(Some(parameter))
        );
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(context.get_type_at_location(argument), Ok(number));
        let warm = state(&context);
        for _ in 0..2 {
            context.check_source_file(SOURCE_FILE).unwrap();
            context.recheck_source_file(SOURCE_FILE).unwrap();
            assert_eq!(observe(&mut context, call, true), expected);
            assert_eq!(state(&context), warm);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}
