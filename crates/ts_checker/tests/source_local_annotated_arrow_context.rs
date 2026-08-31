use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnosticRange, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId, SignatureLinks,
    SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_841);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/local-annotated-arrow.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
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

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
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

fn callable_signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("the checked callback must retain its callable object");
    };
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("each callback has one call signature");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    *signature
}

#[derive(Debug, Eq, PartialEq)]
struct ArrowState {
    declaration: NodeRef,
    callable: TypeId,
    target: TypeId,
    signature: SignatureId,
    target_signature: SignatureId,
    parameter: TypeId,
    returned: TypeId,
    target_return: TypeId,
}

#[allow(clippy::too_many_lines)] // Check the real local binding and the separate source signature together.
fn arrow_state(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) -> ArrowState {
    let (id, variable) = parsed
        .arena
        .iter()
        .find_map(|(id, record)| match &record.data {
            NodeData::VariableDeclaration(variable) => Some((id, variable)),
            _ => None,
        })
        .unwrap();
    let binding_node = node(parsed, id);
    let declaration = node(parsed, variable.initializer.unwrap());
    let annotation = node(parsed, variable.type_.unwrap());
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(declaration.node).unwrap().data else {
        panic!("the source initializer must remain an arrow");
    };
    assert_eq!(parsed.arena.get(declaration.node).unwrap().parent, Some(id));
    let list = parsed.arena.get(id).unwrap().parent.unwrap();
    let statement = parsed.arena.get(list).unwrap().parent.unwrap();
    let block = parsed.arena.get(statement).unwrap().parent.unwrap();
    assert!(matches!(
        parsed.arena.get(block).unwrap().data,
        NodeData::Block(_)
    ));
    assert_ne!(block, parsed.source_file);
    let function = parsed.arena.get(block).unwrap().parent.unwrap();
    assert!(matches!(
        parsed.arena.get(function).unwrap().data,
        NodeData::FunctionDeclaration(_)
    ));
    let owner = symbol(checker, declaration);
    let binding = symbol(checker, binding_node);
    assert_ne!(owner, binding);
    assert_eq!(
        checker.store().symbol(owner).unwrap().flags(),
        SymbolFlags::FUNCTION
    );
    assert_eq!(
        checker.store().symbol(owner).unwrap().declarations(),
        Some(&[declaration][..])
    );
    assert_eq!(
        checker.store().symbol(owner).unwrap().value_declaration(),
        Some(declaration)
    );
    assert_eq!(
        checker.store().symbol(binding).unwrap().flags(),
        SymbolFlags::BLOCK_SCOPED_VARIABLE
    );
    assert_eq!(
        checker
            .file(FILE)
            .unwrap()
            .1
            .block_scope_container(binding_node),
        Some(node(parsed, function))
    );
    let callable = checker.get_type_at_location(declaration).unwrap();
    let target = checker.get_type_at_location(annotation).unwrap();
    assert_ne!(callable, target);
    assert_eq!(
        checker.get_type_at_location(node(parsed, variable.name)),
        Ok(target)
    );
    assert_eq!(
        checker.get_symbol_at_location(node(parsed, variable.name)),
        Ok(Some(binding))
    );
    for (symbol, type_) in [(owner, callable), (binding, target)] {
        assert_eq!(
            checker
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            Some(type_)
        );
    }
    assert_eq!(
        checker.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    let source_signature = signature(checker, declaration);
    let target_signature = callable_signature(checker, target);
    assert_eq!(callable_signature(checker, callable), source_signature);
    assert_ne!(source_signature, target_signature);
    let [parameter_node] = arrow.parameters.nodes.as_slice() else {
        panic!("each local arrow has one real parameter");
    };
    let NodeData::ParameterDeclaration(parameter) =
        &parsed.arena.get(*parameter_node).unwrap().data
    else {
        unreachable!();
    };
    assert!(parameter.type_.is_none());
    let parameter_owner = symbol(checker, node(parsed, *parameter_node));
    let parameter_type = checker
        .get_type_at_location(node(parsed, parameter.name))
        .unwrap();
    assert_eq!(
        checker.get_symbol_at_location(node(parsed, parameter.name)),
        Ok(Some(parameter_owner))
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(parameter_owner)
            .unwrap()
            .resolved_type,
        Some(parameter_type)
    );
    let target_parameter = checker
        .store()
        .signature(target_signature)
        .unwrap()
        .parameters()[0];
    assert_ne!(parameter_owner, target_parameter);
    assert_eq!(
        checker
            .store()
            .value_symbol_links(target_parameter)
            .unwrap()
            .resolved_type,
        Some(parameter_type)
    );
    let returned = checker
        .get_return_type_of_signature(source_signature)
        .unwrap();
    let target_return = checker
        .get_return_type_of_signature(target_signature)
        .unwrap();
    let source = checker.store().signature(source_signature).unwrap();
    assert_eq!(source.declaration(), Some(declaration));
    assert_eq!(source.parameters(), &[parameter_owner]);
    assert_eq!(source.resolved_return_type(), Some(returned));
    assert!(source.type_parameters().is_empty());
    assert_eq!(source.target(), None);
    assert_eq!(source.mapper(), None);
    ArrowState {
        declaration,
        callable,
        target,
        signature: source_signature,
        target_signature,
        parameter: parameter_type,
        returned,
        target_return,
    }
}

fn calls(parsed: &ParseResult) -> Vec<NodeRef> {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            matches!(record.data, NodeData::CallExpression(_)).then_some(node(parsed, id))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
    calls
}

fn argument(parsed: &ParseResult, call: NodeRef) -> NodeRef {
    let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    node(parsed, call.arguments.nodes[0])
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 6],
    types: Vec<Option<TypeNodeLinks>>,
    symbols: Vec<Option<SymbolNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Snapshot {
    let store = checker.store();
    let nodes = parsed
        .arena
        .iter()
        .map(|(id, _)| node(parsed, id))
        .collect::<Vec<_>>();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        types: nodes
            .iter()
            .map(|node| store.type_node_links(*node).cloned())
            .collect(),
        symbols: nodes
            .iter()
            .map(|node| store.symbol_node_links(*node).cloned())
            .collect(),
        signatures: nodes
            .iter()
            .map(|node| store.signature_links(*node).cloned())
            .collect(),
        values: nodes
            .iter()
            .filter_map(|node| checker.file(FILE).unwrap().1.symbol(*node))
            .map(|symbol| {
                store
                    .value_symbol_links(store.get_merged_symbol(symbol).unwrap())
                    .cloned()
            })
            .collect(),
        source: store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: checker.diagnostics().clone(),
    }
}

fn replay(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult, state: &ArrowState) {
    let warm = snapshot(checker, parsed);
    for recheck in [false, true] {
        if recheck {
            checker.recheck_source_file(FILE).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        assert_eq!(&arrow_state(checker, parsed), state);
        assert_eq!(snapshot(checker, parsed), warm);
        assert!(checker.store().type_resolution_is_empty());
    }
}

#[test]
fn typed_local_let_and_const_arrows_check_callback_statements_and_keep_source_signatures() {
    for kind in ["let", "const"] {
        let parsed = parse_source_file(&format!(
            "type NotifyFunction = (callback: () => void) => void;\n\
             function run(callback: () => void): void {{\n\
               {kind} notifyFn: NotifyFunction = (callback) => {{ callback(); }};\n\
               notifyFn(callback);\n\
             }}"
        ));
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        assert!(checker.diagnostics().as_slice().is_empty());
        let state = arrow_state(&mut checker, &parsed);
        let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(state.returned, void);
        assert_eq!(state.target_return, void);
        let callback_signature = callable_signature(&checker, state.parameter);
        let calls = calls(&parsed);
        assert_eq!(calls.len(), 2);
        for (call, expected_signature) in calls
            .iter()
            .zip([callback_signature, state.target_signature])
        {
            let parent = parsed.arena.get(call.node).unwrap().parent.unwrap();
            assert!(matches!(
                parsed.arena.get(parent).unwrap().data,
                NodeData::ExpressionStatement(_)
            ));
            assert_eq!(checker.get_type_at_location(*call), Ok(void));
            assert_eq!(signature(&checker, *call), expected_signature);
        }
        replay(&mut checker, &parsed, &state);
    }
}

#[test]
fn typed_local_arrow_body_and_outer_calls_report_exact_errors() {
    for (callback, body, outer, failed_call, code, message) in [
        (
            "() => void",
            "callback(1)",
            "notifyFn(callback)",
            0,
            2554,
            "Expected 0 arguments, but got 1.",
        ),
        (
            "(value: string) => void",
            "callback(1)",
            "notifyFn(callback)",
            0,
            2345,
            "Argument of type 'number' is not assignable to parameter of type 'string'.",
        ),
        (
            "() => void",
            "callback()",
            "notifyFn(1)",
            1,
            2345,
            "Argument of type 'number' is not assignable to parameter of type '() => void'.",
        ),
    ] {
        let parsed = parse_source_file(&format!(
            "type NotifyFunction = (callback: {callback}) => void;\n\
             function run(callback: {callback}): void {{\n\
               let notifyFn: NotifyFunction = (callback) => {{ {body}; }};\n\
               {outer};\n\
             }}"
        ));
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        let state = arrow_state(&mut checker, &parsed);
        let calls = calls(&parsed);
        assert_eq!(calls.len(), 2);
        let call = calls[failed_call];
        let argument = argument(&parsed, call);
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!(
                "only the wrong call must report an error: {:?}",
                checker.diagnostics()
            );
        };
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.related_information.is_empty());
        if code == 2554 {
            assert_eq!(diagnostic.node, Some(call));
            assert_eq!(
                diagnostic.range_override,
                Some(CanonicalCheckerDiagnosticRange::new(
                    call,
                    parsed.arena.get(argument.node).unwrap().range
                ))
            );
        } else {
            assert_eq!(diagnostic.node, Some(argument));
            assert_eq!(diagnostic.range_override, None);
        }
        let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(state.returned, void);
        assert_eq!(state.target_return, void);
        replay(&mut checker, &parsed, &state);
    }
}

#[test]
fn typed_local_arrow_inferred_return_keeps_the_actual_type_and_target() {
    for target_return in ["string", "number"] {
        let parsed = parse_source_file(&format!(
            "function run(): void {{\n\
               const read: (value: string) => {target_return} = (value) => {{ return value; }};\n\
               read(\"hello\");\n\
             }}"
        ));
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        let state = arrow_state(&mut checker, &parsed);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let expected = if target_return == "string" {
            string
        } else {
            bootstrap.number_type
        };
        assert_eq!(state.parameter, string);
        assert_eq!(state.returned, string);
        assert_eq!(state.target_return, expected);
        let calls = calls(&parsed);
        assert_eq!(calls.len(), 1);
        assert_eq!(checker.get_type_at_location(calls[0]), Ok(expected));
        assert_eq!(signature(&checker, calls[0]), state.target_signature);
        if target_return == "string" {
            assert!(checker.diagnostics().as_slice().is_empty());
        } else {
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!("the inferred string return must fail its number target");
            };
            assert_eq!(diagnostic.node, Some(state.declaration));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type '(value: string) => string' is not assignable to type '(value: string) => number'."
            );
            assert!(diagnostic.related_information.is_empty());
        }
        replay(&mut checker, &parsed, &state);
    }
}
