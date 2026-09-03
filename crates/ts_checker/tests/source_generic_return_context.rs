use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, type_records::LiteralValue, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(495_631);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-return-context.ts\""),
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

fn named(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let name = match &record.data {
                NodeData::FunctionDeclaration(data) => data.name?,
                NodeData::VariableDeclaration(data) => data.name,
                _ => return None,
            };
            matches!(&parsed.arena.get(name)?.data,
                NodeData::Identifier(name) if name.text == expected)
            .then_some(node(parsed, id))
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

struct Call {
    name: NodeRef,
    annotation: NodeRef,
    expression: NodeRef,
    argument: NodeRef,
}

fn call(parsed: &ParseResult, name: &str) -> Call {
    let declaration = named(parsed, name);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let expression = node(parsed, variable.initializer.unwrap());
    let record = parsed.arena.get(expression.node).unwrap();
    assert_eq!(record.parent, Some(declaration.node));
    let NodeData::CallExpression(data) = &record.data else {
        panic!("expected the actual initializer call")
    };
    let [argument] = data.arguments.nodes.as_slice() else {
        panic!("expected one actual argument")
    };
    assert_eq!(
        parsed.arena.get(*argument).unwrap().parent,
        Some(expression.node)
    );
    assert_eq!(
        parsed.arena.get(*argument).unwrap().kind,
        SyntaxKind::StringLiteral
    );
    Call {
        name: node(parsed, variable.name),
        annotation: node(parsed, variable.type_.unwrap()),
        expression,
        argument: node(parsed, *argument),
    }
}

fn assert_union(context: &CanonicalCheckerContext<'_>, type_: TypeId, member: TypeId) {
    let store = context.store();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    let mut expected = vec![member, bootstrap.undefined_type];
    expected.sort_unstable();
    let record = store.type_payload(type_).unwrap();
    assert_eq!(record.flags(), TypeFlags::UNION);
    assert!(record.alias().is_none());
    let TypeData::Union(union) = record.data() else {
        panic!("expected the canonical union with undefined")
    };
    assert_eq!(union.union.types, expected);
    assert_eq!(union.origin, None);
    assert_eq!(bootstrap.cached_union_type(&expected), Some(type_));
}

struct Function {
    declaration: NodeRef,
    signature: SignatureId,
    formal: TypeId,
    parameter: NodeRef,
    parameter_symbol: SemanticSymbolId,
}

fn assert_function(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Function {
    let declaration = named(parsed, "maybe");
    let NodeData::FunctionDeclaration(function) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(function.body.is_some());
    let owner = symbol(context, declaration);
    assert_eq!(
        context.store().symbol(owner).unwrap().declarations(),
        Some([declaration].as_slice())
    );
    let [formal_node] = function.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one real generic formal")
    };
    let formal_node = node(parsed, *formal_node);
    assert_eq!(
        parsed.arena.get(formal_node.node).unwrap().parent,
        Some(declaration.node)
    );
    let formal_owner = symbol(context, formal_node);
    let formal_symbol = context.store().symbol(formal_owner).unwrap();
    assert_eq!(formal_symbol.parent(), None);
    assert_eq!(formal_symbol.declarations(), Some([formal_node].as_slice()));
    assert_eq!(formal_symbol.value_declaration(), None);
    let formal = context.get_declared_type_of_symbol(formal_owner).unwrap();
    let formal_record = context.store().type_payload(formal).unwrap();
    assert_eq!(formal_record.flags(), TypeFlags::TYPE_PARAMETER);
    assert_eq!(formal_record.symbol(), Some(formal_owner));
    let TypeData::TypeParameter(data) = formal_record.data() else {
        unreachable!()
    };
    assert_eq!(data.target, None);
    assert_eq!(data.mapper, None);
    assert!(!data.is_this_type);
    let [parameter] = function.parameters.nodes.as_slice() else {
        panic!("expected one required value parameter")
    };
    let parameter = node(parsed, *parameter);
    assert_eq!(
        parsed.arena.get(parameter.node).unwrap().parent,
        Some(declaration.node)
    );
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(data.initializer.is_none());
    assert!(data.question_token.is_none());
    assert_eq!(
        context.get_type_from_type_node(node(parsed, data.type_.unwrap())),
        Ok(formal)
    );
    let parameter_symbol = symbol(context, parameter);
    let parameter_record = context.store().symbol(parameter_symbol).unwrap();
    assert_eq!(
        parameter_record.declarations(),
        Some([parameter].as_slice())
    );
    assert_eq!(parameter_record.value_declaration(), Some(parameter));
    let links = context
        .store()
        .value_symbol_links(parameter_symbol)
        .unwrap();
    assert_eq!(links.resolved_type, Some(formal));
    assert_eq!(links.target, None);
    assert_eq!(links.mapper, None);
    let returned = context
        .get_type_from_type_node(node(parsed, function.type_.unwrap()))
        .unwrap();
    assert_union(context, returned, formal);
    let signature = signature(context, declaration);
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.type_parameters(), [formal]);
    assert_eq!(record.parameters(), [parameter_symbol]);
    assert_eq!(record.min_argument_count(), 1);
    assert!(!record.has_rest_parameter());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(
        context.get_return_type_of_signature(signature),
        Ok(returned)
    );
    Function {
        declaration,
        signature,
        formal,
        parameter,
        parameter_symbol,
    }
}

fn assert_call(
    context: &mut CanonicalCheckerContext<'_>,
    call: &Call,
    function: &Function,
    literal: &str,
) -> TypeId {
    let returned = context.get_type_at_location(call.expression).unwrap();
    let store = context.store();
    let fresh = store
        .type_node_links(call.argument)
        .unwrap()
        .resolved_type
        .unwrap();
    let record = store.type_payload(fresh).unwrap();
    assert_eq!(record.flags(), TypeFlags::STRING_LITERAL);
    let TypeData::Literal(data) = record.data() else {
        panic!("the raw argument cache must retain its literal")
    };
    assert_eq!(data.value, LiteralValue::String(literal.to_owned()));
    assert_eq!(data.fresh_type, Some(fresh));
    let regular = data.regular_type;
    assert_ne!(fresh, regular);
    let record = store.type_payload(regular).unwrap();
    assert_eq!(record.flags(), TypeFlags::STRING_LITERAL);
    let TypeData::Literal(data) = record.data() else {
        unreachable!()
    };
    assert_eq!(data.value, LiteralValue::String(literal.to_owned()));
    assert_eq!(data.regular_type, regular);
    assert_eq!(data.fresh_type, Some(fresh));
    let selected = signature(context, call.expression);
    assert_ne!(selected, function.signature);
    let record = store.signature(selected).unwrap();
    assert_eq!(record.target(), Some(function.signature));
    assert_eq!(record.declaration(), Some(function.declaration));
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.min_argument_count(), 1);
    assert!(!record.has_rest_parameter());
    let mapper = record.mapper().unwrap();
    assert_eq!(store.map_type(mapper, function.formal), Some(regular));
    let [parameter] = record.parameters() else {
        panic!("the selected signature must retain one parameter")
    };
    assert_ne!(*parameter, function.parameter_symbol);
    let parameter_record = store.symbol(*parameter).unwrap();
    assert_eq!(
        parameter_record.declarations(),
        Some([function.parameter].as_slice())
    );
    assert_eq!(
        parameter_record.value_declaration(),
        Some(function.parameter)
    );
    let links = store.value_symbol_links(*parameter).unwrap();
    assert_eq!(links.target, Some(function.parameter_symbol));
    assert_eq!(links.mapper, Some(mapper));
    assert_eq!(links.resolved_type, Some(regular));
    assert_eq!(context.get_return_type_of_signature(selected), Ok(returned));
    assert_union(context, returned, regular);
    assert_eq!(
        context.type_to_string(returned).unwrap(),
        format!("\"{literal}\" | undefined")
    );
    returned
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    let nodes = parsed
        .arena
        .iter()
        .map(|(id, _)| node(parsed, id))
        .collect::<Vec<_>>();
    let signatures = nodes
        .iter()
        .filter_map(|&node| {
            store
                .signature_links(node)
                .and_then(|links| links.resolved_signature.signature())
        })
        .collect::<Vec<_>>();
    let symbols = nodes
        .iter()
        .filter_map(|&node| context.file(FILE).unwrap().1.symbol(node))
        .chain(
            signatures
                .iter()
                .flat_map(|&id| store.signature(id).unwrap().parameters().iter().copied()),
        )
        .collect::<Vec<_>>();
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
        nodes
            .iter()
            .map(|&node| {
                (
                    node,
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        signatures
            .iter()
            .map(|&id| {
                let signature = store.signature(id).unwrap();
                (
                    id,
                    signature.declaration(),
                    signature.type_parameters().to_vec(),
                    signature.parameters().to_vec(),
                    signature.min_argument_count(),
                    signature.resolved_min_argument_count(),
                    signature.resolved_return_type(),
                    signature.target(),
                    signature.mapper(),
                )
            })
            .collect::<Vec<_>>(),
        symbols
            .iter()
            .map(|&symbol| {
                (
                    symbol,
                    store.declared_type_links(symbol).cloned(),
                    store.value_symbol_links(symbol).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        store.relation_state_snapshot(),
        context.diagnostics().clone(),
    )
}

#[test]
fn generic_union_return_context_keeps_argument_literal_identity_and_replays() {
    let parsed = parse_source_file(concat!(
        "function maybe<T>(value: T): T | undefined { return value; }\n",
        "const good: \"a\" | undefined = maybe(\"a\");\n",
        "const wrong: \"a\" | undefined = maybe(\"b\");\n",
    ));
    let good = call(&parsed, "good");
    let wrong = call(&parsed, "wrong");
    for call_first in [false, true] {
        let mut context = context(&parsed);
        if call_first {
            context.get_type_at_location(wrong.expression).unwrap();
        }
        context.check_source_file(FILE).unwrap();
        let function = assert_function(&mut context, &parsed);
        let good_return = assert_call(&mut context, &good, &function, "a");
        let wrong_return = assert_call(&mut context, &wrong, &function, "b");
        let expected = context.get_type_from_type_node(good.annotation).unwrap();
        assert_eq!(
            context.get_type_from_type_node(wrong.annotation),
            Ok(expected)
        );
        assert_eq!(good_return, expected);
        assert_ne!(wrong_return, expected);
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!(
                "expected only the assignment error, not a call error: {:?}",
                context.diagnostics()
            )
        };
        assert_eq!(diagnostic.node, Some(wrong.name));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.arguments,
            ["\"b\" | undefined", "\"a\" | undefined"]
        );
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type '\"b\" | undefined' is not assignable to type '\"a\" | undefined'."
        );
        let cold = snapshot(&context, &parsed);
        context.check_source_file(FILE).unwrap();
        assert_eq!(snapshot(&context, &parsed), cold);
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(
                assert_call(&mut context, &good, &function, "a"),
                good_return
            );
            assert_eq!(
                assert_call(&mut context, &wrong, &function, "b"),
                wrong_return
            );
            assert_eq!(snapshot(&context, &parsed), cold);
        }
    }
}
