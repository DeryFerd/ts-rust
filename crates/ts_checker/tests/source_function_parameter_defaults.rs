use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostic, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, TypeData, TypeId, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(495_630);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/function-parameter-defaults.ts\""),
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

fn variable_initializer(parsed: &ParseResult, name: &str) -> NodeRef {
    let declaration = named(parsed, name);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a variable")
    };
    node(parsed, data.initializer.unwrap())
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

struct FunctionState {
    declaration: NodeRef,
    signature: SignatureId,
    formal: TypeId,
    default_parameter: NodeRef,
    value_parameter: NodeRef,
    minimum: i32,
}

#[allow(clippy::too_many_arguments)] // Each expected value describes one real source parameter.
#[allow(clippy::too_many_lines)] // Keep source, symbol, signature, and body identity checks together.
fn assert_function(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
    default_index: usize,
    primitive: TypeId,
    initializer_text: &str,
    minimum: i32,
    display: &str,
) -> FunctionState {
    let declaration = named(parsed, name);
    let record = parsed.arena.get(declaration.node).unwrap();
    let NodeData::FunctionDeclaration(function) = &record.data else {
        panic!("expected the generic function")
    };
    assert!(function.body.is_some());
    let [formal_node] = function.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one real generic formal")
    };
    let formal_node = node(parsed, *formal_node);
    let formal_owner = symbol(context, formal_node);
    let owner = symbol(context, declaration);
    assert_eq!(
        parsed.arena.get(formal_node.node).unwrap().parent,
        Some(declaration.node)
    );
    assert_eq!(
        context.store().symbol(owner).unwrap().declarations(),
        Some([declaration].as_slice())
    );
    let formal_symbol = context.store().symbol(formal_owner).unwrap();
    assert_eq!(formal_symbol.parent(), None);
    assert_eq!(formal_symbol.declarations(), Some([formal_node].as_slice()));
    assert_eq!(formal_symbol.value_declaration(), None);
    let formal = context.get_declared_type_of_symbol(formal_owner).unwrap();
    let formal_record = context.store().type_payload(formal).unwrap();
    assert_eq!(formal_record.flags(), TypeFlags::TYPE_PARAMETER);
    assert_eq!(formal_record.symbol(), Some(formal_owner));
    let TypeData::TypeParameter(formal_data) = formal_record.data() else {
        unreachable!()
    };
    assert_eq!(formal_data.target, None);
    assert_eq!(formal_data.mapper, None);
    assert!(!formal_data.is_this_type);
    assert_eq!(function.parameters.nodes.len(), 2);
    let parameters = function
        .parameters
        .nodes
        .iter()
        .map(|&id| node(parsed, id))
        .collect::<Vec<_>>();
    let default_parameter = parameters[default_index];
    let value_parameter = parameters[1 - default_index];
    let mut owners = Vec::new();
    for &parameter in &parameters {
        assert_eq!(
            parsed.arena.get(parameter.node).unwrap().parent,
            Some(declaration.node)
        );
        let parameter_owner = symbol(context, parameter);
        let parameter_record = context.store().symbol(parameter_owner).unwrap();
        assert_eq!(
            parameter_record.declarations(),
            Some([parameter].as_slice())
        );
        assert_eq!(parameter_record.value_declaration(), Some(parameter));
        owners.push(parameter_owner);
    }
    let NodeData::ParameterDeclaration(default) =
        &parsed.arena.get(default_parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(default.type_.is_none());
    assert!(default.question_token.is_none());
    assert!(default.dot_dot_dot_token.is_none());
    let default_name = node(parsed, default.name);
    let initializer = node(parsed, default.initializer.unwrap());
    assert_eq!(
        parsed.arena.get(initializer.node).unwrap().parent,
        Some(default_parameter.node)
    );
    assert!(matches!(
        parsed.arena.get(initializer.node).unwrap().kind,
        SyntaxKind::NumericLiteral | SyntaxKind::StringLiteral
    ));
    let NodeData::Identifier(default_name_data) =
        &parsed.arena.get(default_name.node).unwrap().data
    else {
        unreachable!()
    };
    let mut reads = parsed.arena.iter().filter_map(|(id, child)| {
        (child.range.start >= record.range.start && child.range.end <= record.range.end
            && id != default.name
            && matches!(&child.data, NodeData::Identifier(name) if name.text == default_name_data.text))
            .then_some(node(parsed, id))
    }).collect::<Vec<_>>();
    assert_eq!(reads.len(), 1);
    reads.extend([default_parameter, default_name]);
    for read in reads {
        assert_eq!(context.get_type_at_location(read), Ok(primitive));
        assert_eq!(
            context.get_symbol_at_location(read),
            Ok(Some(owners[default_index]))
        );
    }
    assert_eq!(
        context
            .store()
            .value_symbol_links(owners[default_index])
            .unwrap()
            .resolved_type,
        Some(primitive)
    );
    let literal = context.get_type_at_location(initializer).unwrap();
    assert_ne!(literal, primitive);
    assert_eq!(context.type_to_string(literal).unwrap(), initializer_text);
    assert_eq!(
        context
            .store()
            .value_symbol_links(owners[1 - default_index])
            .unwrap()
            .resolved_type,
        Some(formal)
    );
    let NodeData::ParameterDeclaration(value) =
        &parsed.arena.get(value_parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(value.initializer.is_none());
    assert_eq!(
        context.get_type_from_type_node(node(parsed, value.type_.unwrap())),
        Ok(formal)
    );
    assert_eq!(
        context.get_type_from_type_node(node(parsed, function.type_.unwrap())),
        Ok(formal)
    );
    let signature = signature(context, declaration);
    let signature_record = context.store().signature(signature).unwrap();
    assert_eq!(signature_record.declaration(), Some(declaration));
    assert_eq!(signature_record.type_parameters(), [formal]);
    assert_eq!(signature_record.parameters(), owners);
    assert_eq!(signature_record.min_argument_count(), minimum);
    assert!(!signature_record.has_rest_parameter());
    assert_eq!(signature_record.target(), None);
    assert_eq!(signature_record.mapper(), None);
    assert_eq!(context.get_return_type_of_signature(signature), Ok(formal));
    let callable = context.get_type_at_location(declaration).unwrap();
    assert_eq!(context.type_to_string(callable).unwrap(), display);
    FunctionState {
        declaration,
        signature,
        formal,
        default_parameter,
        value_parameter,
        minimum,
    }
}

fn assert_call(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    variable: &str,
    function: &FunctionState,
) -> (NodeRef, TypeId) {
    let declaration = named(parsed, variable);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let call = node(parsed, data.initializer.unwrap());
    assert_eq!(
        parsed.arena.get(call.node).unwrap().kind,
        SyntaxKind::CallExpression
    );
    let expected = context
        .get_type_from_type_node(node(parsed, data.type_.unwrap()))
        .unwrap();
    assert_eq!(context.get_type_at_location(call), Ok(expected));
    let selected = signature(context, call);
    assert_ne!(selected, function.signature);
    let record = context.store().signature(selected).unwrap();
    assert_eq!(record.target(), Some(function.signature));
    assert_eq!(record.declaration(), Some(function.declaration));
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.min_argument_count(), function.minimum);
    assert_eq!(record.parameters().len(), 2);
    assert_eq!(
        context
            .store()
            .map_type(record.mapper().unwrap(), function.formal),
        Some(expected)
    );
    assert_eq!(context.get_return_type_of_signature(selected), Ok(expected));
    (call, expected)
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

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    queries: &[(NodeRef, TypeId)],
) {
    let cold = snapshot(context, parsed);
    context.check_source_file(FILE).unwrap();
    assert_eq!(snapshot(context, parsed), cold);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        for &(node, expected) in queries {
            assert_eq!(context.get_type_at_location(node), Ok(expected));
        }
        assert_eq!(snapshot(context, parsed), cold);
    }
}

fn assert_diagnostic(
    diagnostic: &CanonicalCheckerDiagnostic,
    node: NodeRef,
    code: u32,
    arguments: &[&str],
    message: &str,
) {
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.diagnostic.arguments, arguments);
    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
}

#[test]
fn generic_literal_defaults_keep_widened_body_types_optional_calls_and_replay() {
    let parsed = parse_source_file(concat!(
        "function keep<T>(value: T, max = 0): T { const limit: number = max; return value; }\n",
        "function label<T>(value: T, prefix = \"x\"): T { const text: string = prefix; return value; }\n",
        "const omitted: \"a\" = keep(\"a\");\n",
        "const explicitUndefined: string = keep<string>(\"a\", undefined);\n",
        "const supplied: number = keep<number>(1, 2);\n",
        "const omittedLabel: \"b\" = label(\"b\");\n",
        "const undefinedLabel: string = label<string>(\"b\", undefined);\n",
        "const suppliedLabel: number = label<number>(2, \"ok\");\n",
    ));
    for call_first in [false, true] {
        let mut context = context(&parsed);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        if call_first {
            let call = variable_initializer(&parsed, "supplied");
            assert_eq!(context.get_type_at_location(call), Ok(number));
        }
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let keep = assert_function(
            &mut context,
            &parsed,
            "keep",
            1,
            number,
            "0",
            1,
            "<T>(value: T, max?: number) => T",
        );
        let label = assert_function(
            &mut context,
            &parsed,
            "label",
            1,
            string,
            "\"x\"",
            1,
            "<T>(value: T, prefix?: string) => T",
        );
        assert_ne!(keep.formal, label.formal);
        assert_ne!(keep.signature, label.signature);
        let mut queries = vec![
            (keep.default_parameter, number),
            (label.default_parameter, string),
        ];
        for name in ["omitted", "explicitUndefined", "supplied"] {
            queries.push(assert_call(&mut context, &parsed, name, &keep));
        }
        for name in ["omittedLabel", "undefinedLabel", "suppliedLabel"] {
            queries.push(assert_call(&mut context, &parsed, name, &label));
        }
        assert_replay(&mut context, &parsed, &queries);
    }
}

#[test]
fn generic_numeric_defaults_keep_body_and_argument_errors_and_replay() {
    let parsed = parse_source_file(concat!(
        "function keep<T>(value: T, max = 0): T { const wrong: string = max; return value; }\n",
        "const bad: string = keep<string>(\"a\", \"bad\");\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let keep = assert_function(
        &mut context,
        &parsed,
        "keep",
        1,
        number,
        "0",
        1,
        "<T>(value: T, max?: number) => T",
    );
    let NodeData::VariableDeclaration(wrong) =
        &parsed.arena.get(named(&parsed, "wrong").node).unwrap().data
    else {
        unreachable!()
    };
    let call = variable_initializer(&parsed, "bad");
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    let [body_error, argument_error] = context.diagnostics().as_slice() else {
        panic!(
            "expected only the body and default-argument errors: {:?}",
            context.diagnostics()
        )
    };
    assert_diagnostic(
        body_error,
        node(&parsed, wrong.name),
        2322,
        &["number", "string"],
        "Type 'number' is not assignable to type 'string'.",
    );
    assert_diagnostic(
        argument_error,
        node(&parsed, data.arguments.nodes[1]),
        2345,
        &["string", "number"],
        "Argument of type 'string' is not assignable to parameter of type 'number'.",
    );
    assert!(body_error.related_information.is_empty());
    assert!(argument_error.related_information.is_empty());
    let result = context.get_type_at_location(call).unwrap();
    assert_eq!(
        result,
        context.store().intrinsic_bootstrap().unwrap().string_type
    );
    assert_replay(
        &mut context,
        &parsed,
        &[(keep.default_parameter, number), (call, result)],
    );
}

#[test]
fn generic_default_before_required_parameter_keeps_minimum_arity_and_replay() {
    let parsed = parse_source_file(concat!(
        "function before<T>(max = 0, value: T): T { const limit: number = max; return value; }\n",
        "const supplied: string = before<string>(2, \"a\");\n",
        "const placeholder: string = before<string>(undefined, \"a\");\n",
        "const tooShort = before<string>(2);\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let before = assert_function(
        &mut context,
        &parsed,
        "before",
        0,
        number,
        "0",
        2,
        "<T>(max: number | undefined, value: T) => T",
    );
    let supplied = assert_call(&mut context, &parsed, "supplied", &before);
    let placeholder = assert_call(&mut context, &parsed, "placeholder", &before);
    let call = variable_initializer(&parsed, "tooShort");
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "expected only the missing-argument error: {:?}",
            context.diagnostics()
        )
    };
    assert_eq!(diagnostic.diagnostic.code(), 2554);
    assert_eq!(diagnostic.diagnostic.arguments, ["2", "1"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Expected 2 arguments, but got 1."
    );
    let range = diagnostic.range_override.map_or_else(
        || {
            parsed
                .arena
                .get(diagnostic.node.unwrap().node)
                .unwrap()
                .range
        },
        |range| range.range(),
    );
    assert_eq!(range, parsed.arena.get(data.expression).unwrap().range);
    let [note] = diagnostic.related_information.as_slice() else {
        panic!("expected the real missing parameter note")
    };
    assert_eq!(note.node, Some(before.value_parameter));
    assert_eq!(note.diagnostic.code(), 6210);
    assert_eq!(note.diagnostic.arguments, ["value"]);
    assert_eq!(
        note.diagnostic.render().unwrap(),
        "An argument for 'value' was not provided."
    );
    assert_replay(
        &mut context,
        &parsed,
        &[(before.default_parameter, number), supplied, placeholder],
    );
}
