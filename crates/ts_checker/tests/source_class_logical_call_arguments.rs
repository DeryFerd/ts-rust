use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, type_records::LiteralValue,
};
use ts_diagnostics::Category;
use ts_jsnum::Number;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_230);
const SOURCE: &str = concat!(
    "declare function takeNumber(value: number): number;\n",
    "declare const fallback: number;\n",
    "class Cache {\n",
    "  gcTime!: number;\n",
    "  label?: string;\n",
    "  isServer(): boolean { return false; }\n",
    "  update(value: number | undefined, flag: boolean): void {\n",
    "    takeNumber(this.gcTime || 0);\n",
    "    takeNumber(this.label || 0);\n",
    "    takeNumber(value ?? (flag ? 1 : 2));\n",
    "    takeNumber(value ?? (this.isServer() ? fallback : 3));\n",
    "  }\n",
    "}\n",
);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-logical-call-arguments.ts\""),
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

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn named(parsed: &ParseResult, kind: SyntaxKind, expected: &str) -> (NodeRef, NodeRef) {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        if record.kind != kind {
            return None;
        }
        let name = match &record.data {
            NodeData::ClassDeclaration(data) => data.name?,
            NodeData::FunctionDeclaration(data) => data.name?,
            NodeData::MethodDeclaration(data) => data.name,
            NodeData::PropertyDeclaration(data) => data.name,
            NodeData::VariableDeclaration(data) => data.name,
            _ => return None,
        };
        let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
            return None;
        };
        (identifier.text == expected).then(|| (node(parsed, id), node(parsed, name)))
    });
    let found = matches.next().unwrap();
    assert!(matches.next().is_none(), "duplicate {expected} declaration");
    found
}

fn expression(parsed: &ParseResult, kind: SyntaxKind, text: &str) -> NodeRef {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        let start = usize::try_from(record.range.start.get()).unwrap();
        let end = usize::try_from(record.range.end.get()).unwrap();
        (record.kind == kind && &SOURCE[start..end] == text).then(|| node(parsed, id))
    });
    let found = matches.next().unwrap_or_else(|| panic!("missing {text}"));
    assert!(matches.next().is_none(), "duplicate {text}");
    found
}

fn owner(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn cached_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn union_members(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> Vec<TypeId> {
    let TypeData::Union(union) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the argument must retain its different branch types");
    };
    union.union.types.clone()
}

fn assert_number_literal(context: &CanonicalCheckerContext<'_>, type_: TypeId, value: i32) {
    let number = Number::new(f64::from(value));
    let TypeData::Literal(literal) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the fallback must retain its number literal");
    };
    assert_eq!(literal.value, LiteralValue::Number(number));
    assert_eq!(
        Some(literal.regular_type),
        context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .cached_number_literal_type(number)
    );
}

fn check_method_parameters(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    class: NodeRef,
    reads: [NodeRef; 2],
    boolean: TypeId,
    number: TypeId,
    undefined: TypeId,
) -> [TypeId; 2] {
    let (method, _) = named(parsed, SyntaxKind::MethodDeclaration, "update");
    let NodeData::ClassDeclaration(class_data) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    assert!(class_data.members.nodes.contains(&method.node));
    let method_record = parsed.arena.get(method.node).unwrap();
    assert_eq!(method_record.parent, Some(class.node));
    let NodeData::MethodDeclaration(method_data) = &method_record.data else {
        unreachable!()
    };
    let body = parsed.arena.get(method_data.body.unwrap()).unwrap();
    assert_eq!(body.kind, SyntaxKind::Block);
    assert_eq!(body.parent, Some(method.node));
    let [value, flag] = method_data.parameters.nodes.as_slice() else {
        panic!("the method keeps both declared parameters");
    };
    let parameters = [*value, *flag];
    let mut types = Vec::new();
    for ((parameter, read), expected_name) in
        parameters.into_iter().zip(reads).zip(["value", "flag"])
    {
        let record = parsed.arena.get(parameter).unwrap();
        assert_eq!(record.kind, SyntaxKind::Parameter);
        assert_eq!(record.parent, Some(method.node));
        let NodeData::ParameterDeclaration(data) = &record.data else {
            panic!("the method owns a real parameter declaration");
        };
        assert!(data.initializer.is_none());
        for id in [data.name, read.node] {
            let record = parsed.arena.get(id).unwrap();
            assert_eq!(record.kind, SyntaxKind::Identifier);
            let NodeData::Identifier(identifier) = &record.data else {
                unreachable!()
            };
            assert_eq!(identifier.text, expected_name);
        }
        let annotation = node(parsed, data.type_.unwrap());
        assert_eq!(
            parsed.arena.get(annotation.node).unwrap().parent,
            Some(parameter)
        );
        let symbol = owner(context, node(parsed, parameter));
        assert_eq!(
            context.store().symbol(symbol).unwrap().value_declaration(),
            Some(node(parsed, parameter))
        );
        assert_eq!(
            context.file(FILE).unwrap().1.flow_container(read),
            Some(method)
        );
        assert_eq!(context.get_symbol_at_location(read), Ok(Some(symbol)));
        let type_ = context.get_type_from_type_node(annotation).unwrap();
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            Some(type_)
        );
        assert_eq!(cached_type(context, read), type_);
        types.push(type_);
    }
    let mut members = vec![number, undefined];
    members.sort_unstable();
    assert_eq!(union_members(context, types[0]), members);
    assert_eq!(types[1], boolean);
    types.try_into().unwrap()
}

fn check_method_condition(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    class: NodeRef,
    boolean: TypeId,
    number: TypeId,
) -> SignatureId {
    let conditional = expression(
        parsed,
        SyntaxKind::ConditionalExpression,
        "this.isServer() ? fallback : 3",
    );
    let NodeData::ConditionalExpression(branches) =
        &parsed.arena.get(conditional.node).unwrap().data
    else {
        unreachable!()
    };
    let call = node(parsed, branches.condition);
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("the conditional tests the actual method call");
    };
    assert!(call_data.arguments.nodes.is_empty());
    assert!(call_data.type_arguments.is_none());
    let access = node(parsed, call_data.expression);
    let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(access.node).unwrap().data
    else {
        panic!("the condition keeps its method receiver")
    };
    assert_eq!(
        parsed.arena.get(property.expression).unwrap().kind,
        SyntaxKind::ThisKeyword
    );
    let (method, _) = named(parsed, SyntaxKind::MethodDeclaration, "isServer");
    let method_symbol = owner(context, method);
    assert_eq!(
        context.store().symbol(method_symbol).unwrap().parent(),
        Some(owner(context, class))
    );
    assert_eq!(
        context.get_symbol_at_location(access),
        Ok(Some(method_symbol))
    );
    let selected = signature(context, call);
    let record = context.store().signature(selected).unwrap();
    assert_eq!(record.declaration(), Some(method));
    assert!(record.parameters().is_empty());
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.min_argument_count(), 0);
    assert_eq!(record.resolved_return_type(), Some(boolean));
    assert_eq!(cached_type(context, call), boolean);
    assert_eq!(context.get_return_type_of_signature(selected), Ok(boolean));
    let fallback = node(parsed, branches.when_true);
    let (declaration, _) = named(parsed, SyntaxKind::VariableDeclaration, "fallback");
    assert_eq!(
        context.get_symbol_at_location(fallback),
        Ok(Some(owner(context, declaration)))
    );
    assert_eq!(cached_type(context, fallback), number);
    assert_number_literal(
        context,
        cached_type(context, node(parsed, branches.when_false)),
        3,
    );
    assert_eq!(cached_type(context, conditional), number);
    selected
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.type_predicate_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
            store.type_resolution_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = node(parsed, id);
                (
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
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect::<Vec<_>>(),
        store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        context.diagnostics().clone(),
    )
}

#[test]
#[allow(clippy::too_many_lines)]
fn class_logical_call_arguments_keep_branches_errors_and_replay() {
    let parsed = parse_source_file(SOURCE);
    let arguments = [
        "this.gcTime || 0",
        "this.label || 0",
        "value ?? (flag ? 1 : 2)",
        "value ?? (this.isServer() ? fallback : 3)",
    ]
    .map(|text| expression(&parsed, SyntaxKind::BinaryExpression, text));
    let calls = arguments.map(|argument| {
        let parent = parsed.arena.get(argument.node).unwrap().parent.unwrap();
        let NodeData::CallExpression(call) = &parsed.arena.get(parent).unwrap().data else {
            panic!("the logical expression is the actual call argument");
        };
        assert_eq!(call.arguments.nodes, [argument.node]);
        assert!(call.type_arguments.is_none());
        let NodeData::Identifier(callee) = &parsed.arena.get(call.expression).unwrap().data else {
            panic!("the call uses the declared function");
        };
        assert_eq!(callee.text, "takeNumber");
        node(&parsed, parent)
    });
    let conditional = expression(&parsed, SyntaxKind::ConditionalExpression, "flag ? 1 : 2");
    let NodeData::ConditionalExpression(branches) =
        &parsed.arena.get(conditional.node).unwrap().data
    else {
        unreachable!()
    };
    let branch_nodes = [branches.when_true, branches.when_false].map(|id| node(&parsed, id));
    let flag = node(&parsed, branches.condition);
    let NodeData::BinaryExpression(nullish) = &parsed.arena.get(arguments[2].node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(
        parsed.arena.get(nullish.operator_token).unwrap().kind,
        SyntaxKind::QuestionQuestionToken
    );
    let value = node(&parsed, nullish.left);

    for query_first in [false, true] {
        let mut context = context(&parsed);
        let (class, class_name) = named(&parsed, SyntaxKind::ClassDeclaration, "Cache");
        if query_first {
            context.get_type_at_location(class_name).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, string, undefined, boolean) = (
            bootstrap.number_type,
            bootstrap.string_type,
            bootstrap.undefined_type,
            bootstrap.boolean_type,
        );
        let fields = ["gcTime", "label"].map(|name| {
            owner(
                &context,
                named(&parsed, SyntaxKind::PropertyDeclaration, name).0,
            )
        });
        for field in fields {
            assert_eq!(
                context.store().symbol(field).unwrap().parent(),
                Some(owner(&context, class))
            );
        }
        let field_types = fields.map(|field| context.get_class_query_member_type(field).unwrap());
        assert_eq!(field_types[0], number);
        let mut label_members = vec![string, undefined];
        label_members.sort_unstable();
        assert_eq!(union_members(&context, field_types[1]), label_members);
        let results = arguments.map(|argument| cached_type(&context, argument));
        assert_eq!(results[0], number);
        assert_eq!(results[2], number);
        assert_eq!(results[3], number);
        let bad_members = union_members(&context, results[1]);
        assert_eq!(bad_members.len(), 2);
        assert!(bad_members.contains(&string));
        let zero = *bad_members.iter().find(|type_| **type_ != string).unwrap();
        assert_number_literal(&context, zero, 0);
        assert_eq!(context.type_to_string(results[1]).unwrap(), "string | 0");
        let branch_types = branch_nodes.map(|branch| cached_type(&context, branch));
        for (type_, value) in branch_types.into_iter().zip([1, 2]) {
            assert_number_literal(&context, type_, value);
        }
        let conditional_type = cached_type(&context, conditional);
        let mut expected_branches = branch_types.to_vec();
        expected_branches.sort_unstable();
        assert_eq!(union_members(&context, conditional_type), expected_branches);
        assert_eq!(cached_type(&context, flag), boolean);
        let parameter_types = check_method_parameters(
            &mut context,
            &parsed,
            class,
            [value, flag],
            boolean,
            number,
            undefined,
        );
        let method_condition =
            check_method_condition(&mut context, &parsed, class, boolean, number);

        let (declaration, name) = named(&parsed, SyntaxKind::FunctionDeclaration, "takeNumber");
        let callable_type = context.get_type_at_location(name).unwrap();
        let selected = signature(&context, declaration);
        let NodeData::FunctionDeclaration(function) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let [parameter] = function.parameters.nodes.as_slice() else {
            panic!("one parameter")
        };
        let parameter = owner(&context, node(&parsed, *parameter));
        let record = context.store().signature(selected).unwrap();
        assert_eq!(record.declaration(), Some(declaration));
        assert_eq!(record.parameters(), &[parameter]);
        assert_eq!(record.min_argument_count(), 1);
        assert_eq!(record.resolved_return_type(), Some(number));
        assert!(record.type_parameters().is_empty());
        assert!(!record.has_rest_parameter());
        assert!(record.target().is_none());
        assert!(record.mapper().is_none());
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        let TypeData::Object(callable) =
            context.store().type_payload(callable_type).unwrap().data()
        else {
            panic!("the function keeps its canonical callable object")
        };
        assert_eq!(
            callable.structured.signatures.as_deref(),
            Some(&[selected][..])
        );
        assert_eq!(callable.structured.call_signature_count, 1);
        for call in calls {
            assert_eq!(signature(&context, call), selected);
            assert_eq!(cached_type(&context, call), number);
        }
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!(
                "expected one incompatible argument error: {:?}",
                context.diagnostics()
            );
        };
        assert_eq!(diagnostic.node, Some(arguments[1]));
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.diagnostic.arguments, ["string | 0", "number"]);
        assert_eq!(
            diagnostic.diagnostic.details,
            ["  Type 'string' is not assignable to type 'number'."]
        );
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            concat!(
                "Argument of type 'string | 0' is not assignable to parameter of type 'number'.\n",
                "  Type 'string' is not assignable to type 'number'.",
            )
        );
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        assert!(
            context
                .store()
                .source_file_links(context.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );
        let warm = snapshot(&context, &parsed);
        for _ in 0..2 {
            assert_eq!(context.get_type_at_location(name), Ok(callable_type));
            assert_eq!(context.get_return_type_of_signature(selected), Ok(number));
            assert_eq!(
                check_method_condition(&mut context, &parsed, class, boolean, number),
                method_condition
            );
            assert_eq!(
                check_method_parameters(
                    &mut context,
                    &parsed,
                    class,
                    [value, flag],
                    boolean,
                    number,
                    undefined,
                ),
                parameter_types
            );
            for (field, type_) in fields.into_iter().zip(field_types) {
                assert_eq!(context.get_class_query_member_type(field), Ok(type_));
            }
            context.check_source_file(FILE).unwrap();
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(
                arguments.map(|argument| cached_type(&context, argument)),
                results
            );
            assert_eq!(cached_type(&context, conditional), conditional_type);
            assert_eq!(calls.map(|call| signature(&context, call)), [selected; 4]);
            assert_eq!(snapshot(&context, &parsed), warm);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}
