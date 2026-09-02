use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_119);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-method-assignments.ts\""),
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
        [(FILE, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn reference(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, node)
}

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| (record.kind == kind).then_some(reference(parsed, node)));
    let node = nodes.next().unwrap_or_else(|| panic!("missing {kind:?}"));
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    node
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let bound = context.file(FILE).unwrap().1;
    context
        .store()
        .get_merged_symbol(bound.symbol(declaration).unwrap())
        .unwrap()
}

struct Assignment {
    class: NodeRef,
    formal: NodeRef,
    method: NodeRef,
    parameter: NodeRef,
    parameter_type: NodeRef,
    return_type: NodeRef,
    expression: NodeRef,
    left: NodeRef,
    name: NodeRef,
    right: NodeRef,
}

fn assignment(parsed: &ParseResult) -> Assignment {
    let class = only(parsed, SyntaxKind::ClassDeclaration);
    let formal = only(parsed, SyntaxKind::TypeParameter);
    let constructor = only(parsed, SyntaxKind::Constructor);
    let method = only(parsed, SyntaxKind::MethodDeclaration);
    let parameter = only(parsed, SyntaxKind::Parameter);
    let expression = only(parsed, SyntaxKind::BinaryExpression);
    let NodeData::ClassDeclaration(class_data) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(
        class_data.type_parameters.as_ref().unwrap().nodes,
        [formal.node]
    );
    assert_eq!(class_data.members.nodes, [constructor.node, method.node]);
    for node in [formal, constructor, method] {
        assert_eq!(
            parsed.arena.get(node.node).unwrap().parent,
            Some(class.node)
        );
    }
    let NodeData::MethodDeclaration(method_data) = &parsed.arena.get(method.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(method_data.parameters.nodes, [parameter.node]);
    assert!(method_data.type_parameters.is_none());
    assert!(method_data.postfix_token.is_none());
    let NodeData::Identifier(method_name) = &parsed.arena.get(method_data.name).unwrap().data
    else {
        panic!("expected the actual method name")
    };
    assert_eq!(method_name.text, "subscribe");
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(
        parsed.arena.get(parameter.node).unwrap().parent,
        Some(method.node)
    );
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(
        parsed.arena.get(binary.operator_token).unwrap().kind,
        SyntaxKind::EqualsToken
    );
    let statement = parsed.arena.get(expression.node).unwrap().parent.unwrap();
    let NodeData::ExpressionStatement(statement_data) = &parsed.arena.get(statement).unwrap().data
    else {
        panic!("expected a constructor assignment statement")
    };
    assert_eq!(statement_data.expression, expression.node);
    let NodeData::ConstructorDeclaration(constructor_data) =
        &parsed.arena.get(constructor.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(
        parsed.arena.get(statement).unwrap().parent,
        constructor_data.body
    );
    let NodeData::PropertyAccessExpression(left) = &parsed.arena.get(binary.left).unwrap().data
    else {
        panic!("expected the actual method write target")
    };
    assert_eq!(
        parsed.arena.get(left.expression).unwrap().kind,
        SyntaxKind::ThisKeyword
    );
    assert_eq!(
        parsed.arena.get(binary.left).unwrap().parent,
        Some(expression.node)
    );
    let NodeData::Identifier(name) = &parsed.arena.get(left.name).unwrap().data else {
        panic!("expected a public method name")
    };
    assert_eq!(name.text, method_name.text);
    Assignment {
        class,
        formal,
        method,
        parameter,
        parameter_type: reference(parsed, parameter_data.type_.unwrap()),
        return_type: reference(parsed, method_data.type_.unwrap()),
        expression,
        left: reference(parsed, binary.left),
        name: reference(parsed, left.name),
        right: reference(parsed, binary.right),
    }
}

fn assert_method(
    context: &mut CanonicalCheckerContext<'_>,
    nodes: &Assignment,
) -> (SemanticSymbolId, TypeId, TypeId, SignatureId) {
    let class = symbol(context, nodes.class);
    let formal = symbol(context, nodes.formal);
    let method = symbol(context, nodes.method);
    let parameter = symbol(context, nodes.parameter);
    let store = context.store();
    let formal_type = store
        .declared_type_links(formal)
        .unwrap()
        .declared_type
        .unwrap();
    assert_eq!(store.symbol(formal).unwrap().parent(), Some(class));
    let formal_record = store.type_payload(formal_type).unwrap();
    assert_eq!(formal_record.flags(), TypeFlags::TYPE_PARAMETER);
    assert_eq!(formal_record.symbol(), Some(formal));
    let TypeData::TypeParameter(formal_data) = formal_record.data() else {
        panic!("expected the class's canonical T")
    };
    assert!(!formal_data.is_this_type);
    assert_eq!(formal_data.target, None);
    assert_eq!(formal_data.mapper, None);
    let member = store.symbol(method).unwrap();
    assert_eq!(member.flags(), SymbolFlags::METHOD);
    assert_eq!(member.parent(), Some(class));
    assert_eq!(member.declarations(), Some(&[nodes.method][..]));
    assert_eq!(member.value_declaration(), Some(nodes.method));
    let members = store.symbol(class).unwrap().members().unwrap();
    assert_eq!(
        store.symbol_table(members).unwrap().get_source("subscribe"),
        Some(method)
    );
    let callable = store
        .value_symbol_links(method)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(
        store.value_symbol_links(parameter).unwrap().resolved_type,
        Some(formal_type)
    );
    let signature = store
        .signature_links(nodes.method)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let signature_record = store.signature(signature).unwrap();
    assert_eq!(signature_record.declaration(), Some(nodes.method));
    assert_eq!(signature_record.flags(), SignatureFlags::NONE);
    assert!(signature_record.type_parameters().is_empty());
    assert_eq!(signature_record.parameters(), &[parameter]);
    assert_eq!(signature_record.min_argument_count(), 1);
    assert_eq!(signature_record.resolved_return_type(), Some(formal_type));
    assert_eq!(signature_record.target(), None);
    assert_eq!(signature_record.mapper(), None);
    let TypeData::Object(callable_data) = store.type_payload(callable).unwrap().data() else {
        panic!("expected the method's declared callable object")
    };
    assert_eq!(callable_data.target, None);
    assert_eq!(callable_data.mapper, None);
    assert_eq!(callable_data.structured.call_signature_count, 1);
    assert_eq!(
        callable_data.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(context.get_type_at_location(nodes.method), Ok(callable));
    assert_eq!(
        context.get_type_from_type_node(nodes.parameter_type),
        Ok(formal_type)
    );
    assert_eq!(
        context.get_type_from_type_node(nodes.return_type),
        Ok(formal_type)
    );
    assert_eq!(
        context.get_return_type_of_signature(signature),
        Ok(formal_type)
    );
    (method, formal_type, callable, signature)
}

fn assert_assignment(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    nodes: &Assignment,
    invalid: bool,
) -> (SemanticSymbolId, TypeId, TypeId, SignatureId) {
    let identity = assert_method(context, nodes);
    let (method, _, callable, _) = identity;
    assert_eq!(
        context.get_symbol_at_location(nodes.name).unwrap(),
        Some(method)
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(nodes.left)
            .unwrap()
            .resolved_symbol,
        Some(method)
    );
    assert_eq!(context.get_type_at_location(nodes.left), Ok(callable));
    let right_type = if invalid {
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let count = symbol(context, only(parsed, SyntaxKind::VariableDeclaration));
        assert_eq!(
            context.get_symbol_at_location(nodes.right).unwrap(),
            Some(count)
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(count)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        number
    } else {
        let NodeData::PropertyAccessExpression(right) =
            &parsed.arena.get(nodes.right.node).unwrap().data
        else {
            panic!("expected a read of the same method, not a bind call")
        };
        assert_eq!(
            parsed.arena.get(right.expression).unwrap().kind,
            SyntaxKind::ThisKeyword
        );
        assert_eq!(
            context
                .get_symbol_at_location(reference(parsed, right.name))
                .unwrap(),
            Some(method)
        );
        callable
    };
    assert_eq!(context.get_type_at_location(nodes.right), Ok(right_type));
    assert_eq!(
        context.get_type_at_location(nodes.expression),
        Ok(right_type)
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(method)
            .unwrap()
            .resolved_type,
        Some(callable)
    );
    let callable_text = context.type_to_string(callable).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    if invalid {
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        let diagnostic = &diagnostics[0];
        assert_eq!(diagnostic.node, Some(nodes.left));
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.arguments,
            ["number", callable_text.as_str()]
        );
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            format!("Type 'number' is not assignable to type '{callable_text}'.")
        );
    } else {
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }
    identity
}

fn check_assignment(source: &str, invalid: bool) {
    let parsed = parse_source_file(source);
    let nodes = assignment(&parsed);
    for query_first in [false, true] {
        let mut context = context(&parsed);
        let early = query_first.then(|| context.get_type_at_location(nodes.expression).unwrap());
        context.check_source_file(FILE).unwrap();
        let identity = assert_assignment(&mut context, &parsed, &nodes, invalid);
        if let Some(early) = early {
            assert_eq!(context.get_type_at_location(nodes.expression), Ok(early));
        }
        let diagnostics = context.diagnostics().clone();
        for _ in 0..2 {
            context.check_source_file(FILE).unwrap();
            assert_eq!(
                assert_assignment(&mut context, &parsed, &nodes, invalid),
                identity
            );
            assert_eq!(context.diagnostics(), &diagnostics);
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(
                assert_assignment(&mut context, &parsed, &nodes, invalid),
                identity
            );
            assert_eq!(context.diagnostics(), &diagnostics);
        }
    }
}

#[test]
fn generic_class_constructor_method_self_assignment_keeps_the_declared_signature() {
    check_assignment(
        concat!(
            "class Listener<T> {\n",
            "  constructor() { this.subscribe = this.subscribe; }\n",
            "  subscribe(value: T): T { return value; }\n",
            "}\n",
        ),
        false,
    );
}

#[test]
fn generic_class_constructor_number_to_method_assignment_reports_ts2322() {
    check_assignment(
        concat!(
            "declare const count: number;\n",
            "class Listener<T> {\n",
            "  constructor() { this.subscribe = count; }\n",
            "  subscribe(value: T): T { return value; }\n",
            "}\n",
        ),
        true,
    );
}
