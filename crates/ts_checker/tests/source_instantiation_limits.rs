use std::collections::HashSet;

use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnosticRange, CanonicalCheckerOptions,
    CanonicalTypeMapperStore, TypeData, TypeId,
};
use ts_core::{TextPos, TextRange};
use ts_parser::{ParseResult, parse_source_file};

fn call_nodes(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|(start, _)| *start);
    calls.into_iter().map(|(_, call)| call).collect()
}

fn call_callee(parsed: &ParseResult, file: FileId, call: NodeRef) -> NodeRef {
    let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected a call expression")
    };
    NodeRef::new(parsed.arena.id(), file, call.expression)
}

fn call_argument(parsed: &ParseResult, file: FileId, call: NodeRef, index: usize) -> NodeRef {
    let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected a call expression")
    };
    NodeRef::new(parsed.arena.id(), file, call.arguments.nodes[index])
}

fn call_type_argument(parsed: &ParseResult, file: FileId, call: NodeRef, index: usize) -> NodeRef {
    let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected a call expression")
    };
    NodeRef::new(
        parsed.arena.id(),
        file,
        call.type_arguments.as_ref().unwrap().nodes[index],
    )
}

fn function_parameter(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ParameterDeclaration(parameter) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(parameter.name)?.data else {
                return None;
            };
            let parent = parsed.arena.get(record.parent?)?;
            (name.text == expected && parent.kind == SyntaxKind::FunctionDeclaration)
                .then(|| NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing function parameter {expected:?}"))
}

fn recovered_array_leaf(store: &CanonicalTypeMapperStore, mut type_: TypeId) -> (usize, TypeId) {
    let mut depth = 0;
    loop {
        let Some(record) = store.type_payload(type_) else {
            panic!("missing recovered type {type_:?}")
        };
        let TypeData::TypeReference(reference) = record.data() else {
            return (depth, type_);
        };
        let [element] = reference
            .resolved_type_arguments
            .as_deref()
            .unwrap_or_default()
        else {
            return (depth, type_);
        };
        depth += 1;
        type_ = *element;
    }
}

#[test]
#[allow(clippy::too_many_lines)] // One production vertical pins ordering, graph shape, recovery, and replay.
fn generic_call_instantiation_limits_are_lazy_recovering_and_query_scoped() {
    let deep_tail = format!("T{}", "[]".repeat(101));
    let source = format!(
        concat!(
            "function deep<T extends string>(head: T, tail: {deep_tail}): number ",
            "{{ return 1; }}\n",
            "const tail: any = 0;\n",
            "const tooFew = deep<string>('ok');\n",
            "const tooManyTypes = deep<string, number>('ok', tail);\n",
            "const badConstraint = deep<number>('ok', tail);\n",
            "const firstMismatch = deep<string>(1, tail);\n",
            "const reachesDeep = deep<string>('ok', tail);\n",
        ),
        deep_tail = deep_tail,
    );
    let parsed = parse_source_file(&source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    let library_file = FileId::new(0);
    let file = FileId::new(1);
    let mut binder = CanonicalBinder::new();
    for (parsed, file, name) in [
        (&library, library_file, "\"/project/lib.d.ts\""),
        (&parsed, file, "\"/project/source-instantiation-limits.ts\""),
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
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(library_file, &library.arena), (file, &parsed.arena)]
            .into_iter()
            .collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();
    let calls = call_nodes(&parsed, file);
    let [
        too_few,
        too_many_types,
        bad_constraint,
        first_mismatch,
        reaches_deep,
    ] = calls.as_slice()
    else {
        panic!("expected five generic calls")
    };

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2554, 2558, 2344, 2345, 2589]
    );
    assert_eq!(
        diagnostics[0].node,
        Some(call_callee(&parsed, file, *too_few))
    );
    assert_eq!(diagnostics[0].range_override, None);
    let [missing_tail] = diagnostics[0].related_information.as_slice() else {
        panic!("TS2554 must retain one missing-argument diagnostic")
    };
    assert_eq!(missing_tail.diagnostic.code(), 6210);
    assert_eq!(
        missing_tail.node,
        Some(function_parameter(&parsed, file, "tail"))
    );

    let type_argument_start = source.find("string, number").unwrap();
    assert_eq!(diagnostics[1].node, Some(*too_many_types));
    assert_eq!(
        diagnostics[1].range_override,
        Some(CanonicalCheckerDiagnosticRange::new(
            *too_many_types,
            TextRange::new(
                TextPos::new(u32::try_from(type_argument_start).unwrap()),
                TextPos::new(u32::try_from(type_argument_start + "string, number".len()).unwrap()),
            ),
        ))
    );
    assert!(diagnostics[1].related_information.is_empty());
    assert_eq!(
        diagnostics[2].node,
        Some(call_type_argument(&parsed, file, *bad_constraint, 0))
    );
    assert_eq!(diagnostics[2].range_override, None);
    assert!(diagnostics[2].related_information.is_empty());
    assert_eq!(
        diagnostics[3].node,
        Some(call_argument(&parsed, file, *first_mismatch, 0))
    );
    assert_eq!(diagnostics[3].range_override, None);
    assert!(diagnostics[3].related_information.is_empty());
    assert_eq!(diagnostics[4].node, Some(*reaches_deep));
    assert_eq!(diagnostics[4].range_override, None);
    assert!(diagnostics[4].related_information.is_empty());

    let store = context.store();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    let error = bootstrap.error_type;
    let call_links = calls
        .iter()
        .map(|call| {
            let type_ = store
                .type_node_links(*call)
                .and_then(|links| links.resolved_type)
                .expect("every call publishes its recovery result");
            let signature = store
                .signature_links(*call)
                .and_then(|links| links.resolved_signature.signature())
                .expect("every call publishes its selected signature");
            assert_eq!(type_, number);
            (type_, signature)
        })
        .collect::<Vec<_>>();
    let selected_signatures = call_links
        .iter()
        .map(|(_, signature)| *signature)
        .collect::<Vec<_>>();
    assert_eq!(
        selected_signatures
            .iter()
            .copied()
            .collect::<HashSet<_>>()
            .len(),
        5,
        "four call-local recoveries and one checked signature are distinct"
    );
    let checked_signature = *selected_signatures.last().unwrap();
    let original_signature = store
        .signature(checked_signature)
        .and_then(|signature| signature.target())
        .expect("the successful call selects an instantiated signature");
    let instantiated = store
        .signatures()
        .filter(|(_, signature)| signature.target() == Some(original_signature))
        .map(|(signature, _)| signature)
        .collect::<Vec<_>>();
    assert_eq!(
        instantiated.len(),
        5,
        "TS2345's hidden checked shell must be reused by the later successful call"
    );

    for recovery in &selected_signatures[..4] {
        let signature = store.signature(*recovery).unwrap();
        assert_eq!(signature.target(), Some(original_signature));
        assert!(signature.mapper().is_some());
        assert_eq!(signature.resolved_return_type(), Some(number));
        assert!(signature.parameters().iter().all(|parameter| {
            store
                .value_symbol_links(*parameter)
                .is_some_and(|links| links.resolved_type.is_none())
        }));
    }

    let checked = store.signature(checked_signature).unwrap();
    assert_eq!(checked.target(), Some(original_signature));
    assert!(checked.mapper().is_some());
    assert_eq!(checked.resolved_return_type(), Some(number));
    let [head, tail] = checked.parameters() else {
        panic!("deep has two instantiated parameters")
    };
    assert_eq!(
        store
            .value_symbol_links(*head)
            .and_then(|links| links.resolved_type),
        Some(string)
    );
    let recovered_tail = store
        .value_symbol_links(*tail)
        .and_then(|links| links.resolved_type)
        .expect("the successful call demands the deep suffix");
    let (wrapper_depth, leaf) = recovered_array_leaf(store, recovered_tail);
    assert_eq!(wrapper_depth, 100);
    assert_eq!(leaf, error);

    let warm_state = (
        store.type_len(),
        store.mapper_len(),
        store.symbol_len(),
        store.signature_len(),
        context.diagnostics().clone(),
        call_links,
    );
    context.check_source_file(file).unwrap();
    let warm_call_links = calls
        .iter()
        .map(|call| {
            (
                context
                    .store()
                    .type_node_links(*call)
                    .and_then(|links| links.resolved_type)
                    .unwrap(),
                context
                    .store()
                    .signature_links(*call)
                    .and_then(|links| links.resolved_signature.signature())
                    .unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
            warm_call_links,
        ),
        warm_state
    );
}
