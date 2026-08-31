use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    type_records::StructuredTypeData,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(9_240);

const fn structured_data(data: &TypeData) -> Option<&StructuredTypeData> {
    match data {
        TypeData::Object(data) => Some(&data.structured),
        TypeData::TypeReference(data) => Some(&data.object.structured),
        TypeData::Interface(data) => Some(&data.reference.object.structured),
        TypeData::Tuple(data) => Some(&data.interface.reference.object.structured),
        TypeData::InstantiationExpression(data) => Some(&data.object.structured),
        TypeData::Mapped(data) => Some(&data.object.structured),
        TypeData::ReverseMapped(data) => Some(&data.object.structured),
        TypeData::EvolvingArray(data) => Some(&data.object.structured),
        TypeData::Union(data) => Some(&data.union.structured),
        TypeData::Intersection(data) => Some(&data.intersection.structured),
        _ => None,
    }
}

fn node_ref(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, node)
}

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/private-destructuring-writes.ts\""),
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
            strict_property_initialization: true,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

struct WriteNodes {
    class: NodeRef,
    field: NodeRef,
    callable: NodeRef,
    parameter: NodeRef,
    source: NodeRef,
    parentheses: NodeRef,
    assignment: NodeRef,
    target: NodeRef,
    rhs: NodeRef,
    after: NodeRef,
}

fn variable_statement(parsed: &ParseResult, statement: NodeId) -> NodeRef {
    let NodeData::VariableStatement(statement) = &parsed.arena.get(statement).unwrap().data else {
        panic!("expected a local variable statement")
    };
    let NodeData::VariableDeclarationList(list) =
        &parsed.arena.get(statement.declaration_list).unwrap().data
    else {
        panic!("expected a variable declaration list")
    };
    let [declaration] = list.declarations.nodes.as_slice() else {
        panic!("expected one local declaration")
    };
    node_ref(parsed, *declaration)
}

fn write_nodes(parsed: &ParseResult, expected: &str) -> WriteNodes {
    let (class_node, class) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(class.name?)?.data else {
                return None;
            };
            (name.text == expected).then_some((node_ref(parsed, node), class))
        })
        .unwrap();
    let [field, callable] = class.members.nodes.as_slice() else {
        panic!("expected one private field and one callable")
    };
    let (parameters, body) = match &parsed.arena.get(*callable).unwrap().data {
        NodeData::MethodDeclaration(method) => (&method.parameters, method.body.unwrap()),
        NodeData::ConstructorDeclaration(constructor) => {
            (&constructor.parameters, constructor.body.unwrap())
        }
        _ => panic!("expected a method or constructor"),
    };
    let [parameter] = parameters.nodes.as_slice() else {
        panic!("expected one scalar parameter")
    };
    let NodeData::Block(block) = &parsed.arena.get(body).unwrap().data else {
        panic!("expected the callable body")
    };
    let [source, statement, after] = block.statements.nodes.as_slice() else {
        panic!("expected a source declaration, write, and read")
    };
    let NodeData::ExpressionStatement(statement) = &parsed.arena.get(*statement).unwrap().data
    else {
        panic!("expected the assignment statement")
    };
    let parentheses = node_ref(parsed, statement.expression);
    let NodeData::ParenthesizedExpression(inner) =
        &parsed.arena.get(parentheses.node).unwrap().data
    else {
        panic!("expected the original assignment parentheses")
    };
    let assignment = node_ref(parsed, inner.expression);
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        panic!("expected the destructuring assignment")
    };
    assert_eq!(
        parsed.arena.get(binary.operator_token).unwrap().kind,
        SyntaxKind::EqualsToken
    );
    let NodeData::ObjectLiteralExpression(pattern) = &parsed.arena.get(binary.left).unwrap().data
    else {
        panic!("expected an object assignment pattern")
    };
    let [property] = pattern.properties.nodes.as_slice() else {
        panic!("expected one assignment leaf")
    };
    let NodeData::PropertyAssignment(property) = &parsed.arena.get(*property).unwrap().data else {
        panic!("expected the selected source property")
    };
    WriteNodes {
        class: class_node,
        field: node_ref(parsed, *field),
        callable: node_ref(parsed, *callable),
        parameter: node_ref(parsed, *parameter),
        source: variable_statement(parsed, *source),
        parentheses,
        assignment,
        target: node_ref(parsed, property.initializer),
        rhs: node_ref(parsed, binary.right),
        after: variable_statement(parsed, *after),
    }
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn variable_parts(parsed: &ParseResult, declaration: NodeRef) -> (NodeRef, NodeRef) {
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a local declaration")
    };
    (
        node_ref(parsed, variable.name),
        node_ref(parsed, variable.initializer.unwrap()),
    )
}

fn checked_type(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    checker
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type at {node:?}"))
}

fn assert_private_target(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    nodes: &WriteNodes,
    expected: TypeId,
) -> SemanticSymbolId {
    let owner = symbol(checker, nodes.class);
    let field = symbol(checker, nodes.field);
    let record = checker.store().symbol(field).unwrap();
    assert_eq!(record.parent(), Some(owner));
    assert_eq!(record.declarations(), Some([nodes.field].as_slice()));
    assert_eq!(record.value_declaration(), Some(nodes.field));
    assert_eq!(record.flags(), SymbolFlags::PROPERTY);
    assert!(record.name().is_private_identifier());
    let members = checker
        .store()
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|table| checker.store().symbol_table(table))
        .unwrap();
    assert_eq!(members.get(record.name()), Some(field));
    assert_eq!(members.get_source("#state"), None);
    assert_eq!(
        checker
            .store()
            .value_symbol_links(field)
            .unwrap()
            .resolved_type,
        Some(expected)
    );
    let NodeData::PropertyDeclaration(declaration) =
        &parsed.arena.get(nodes.field.node).unwrap().data
    else {
        panic!("expected the private field declaration")
    };
    assert_eq!(
        checker.get_type_from_type_node(node_ref(parsed, declaration.type_.unwrap())),
        Ok(expected)
    );
    let field_name = node_ref(parsed, declaration.name);
    assert_eq!(checker.get_symbol_at_location(field_name), Ok(Some(field)));
    let instance = checker.get_declared_type_of_symbol(owner).unwrap();
    assert_eq!(
        checker.store().type_payload(instance).unwrap().symbol(),
        Some(owner)
    );
    let TypeData::Interface(class) = checker.store().type_payload(instance).unwrap().data() else {
        panic!("expected the declared class instance")
    };
    let this_type = class.this_type.unwrap();
    let (after_name, after_read) = variable_parts(parsed, nodes.after);
    for access in [nodes.target, after_read] {
        let NodeData::PropertyAccessExpression(property) =
            &parsed.arena.get(access.node).unwrap().data
        else {
            panic!("expected a private property access")
        };
        let receiver = node_ref(parsed, property.expression);
        let name = node_ref(parsed, property.name);
        assert_eq!(
            parsed.arena.get(receiver.node).unwrap().kind,
            SyntaxKind::ThisKeyword
        );
        assert!(matches!(&parsed.arena.get(name.node).unwrap().data,
            NodeData::PrivateIdentifier(identifier) if identifier.text == "#state"));
        assert_eq!(
            checker.file(FILE).unwrap().1.flow_container(access),
            Some(nodes.callable)
        );
        assert_eq!(checked_type(checker, access), expected);
        assert_eq!(checker.get_type_at_location(access), Ok(expected));
        assert_eq!(checker.get_type_at_location(name), Ok(expected));
        assert_eq!(checker.get_type_at_location(receiver), Ok(this_type));
        assert_eq!(checker.get_symbol_at_location(access), Ok(Some(field)));
        assert_eq!(checker.get_symbol_at_location(name), Ok(Some(field)));
        assert_eq!(
            checker
                .store()
                .symbol_node_links(access)
                .unwrap()
                .resolved_symbol,
            Some(field)
        );
    }
    assert_eq!(checker.get_type_at_location(after_name), Ok(expected));
    let graph = checker.file(FILE).unwrap().1.flow_graph();
    let writes = graph.nodes().iter().filter(|flow| {
        flow.flags.contains(FlowFlags::ASSIGNMENT)
            && flow.payload == Some(FlowNodePayload::Ast(nodes.target))
    });
    assert_eq!(writes.count(), 1);
    field
}

fn assert_source_result(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    nodes: &WriteNodes,
    source_value: TypeId,
    target_value: TypeId,
) {
    let parameter = symbol(checker, nodes.parameter);
    let NodeData::ParameterDeclaration(declaration) =
        &parsed.arena.get(nodes.parameter.node).unwrap().data
    else {
        panic!("expected the scalar parameter declaration")
    };
    assert_eq!(
        checker
            .store()
            .symbol(parameter)
            .unwrap()
            .value_declaration(),
        Some(nodes.parameter)
    );
    assert_eq!(
        checker.file(FILE).unwrap().1.container(nodes.parameter),
        Some(nodes.callable)
    );
    assert_eq!(
        checker.get_type_at_location(node_ref(parsed, declaration.name)),
        Ok(source_value)
    );
    let source = symbol(checker, nodes.source);
    let (source_name, _) = variable_parts(parsed, nodes.source);
    let object = checked_type(checker, nodes.rhs);
    assert_ne!(object, source_value);
    assert_ne!(object, target_value);
    assert_eq!(
        checker
            .store()
            .value_symbol_links(source)
            .unwrap()
            .resolved_type,
        Some(object)
    );
    assert_eq!(checker.get_symbol_at_location(nodes.rhs), Ok(Some(source)));
    for expression in [source_name, nodes.rhs, nodes.assignment, nodes.parentheses] {
        assert_eq!(checked_type(checker, expression), object);
        assert_eq!(checker.get_type_at_location(expression), Ok(object));
    }
    let property = checker
        .store()
        .type_payload(object)
        .and_then(|record| structured_data(record.data()))
        .and_then(|data| data.members)
        .and_then(|members| checker.store().symbol_table(members))
        .and_then(|members| members.get_source("value"))
        .unwrap();
    assert_ne!(property, symbol(checker, nodes.field));
    assert_eq!(
        checker
            .store()
            .value_symbol_links(property)
            .unwrap()
            .resolved_type,
        Some(source_value)
    );
}

fn assert_stable_replay(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    writes: &[(&WriteNodes, TypeId, TypeId)],
) {
    let snapshot = |checker: &CanonicalCheckerContext<'_>| {
        let store = checker.store();
        (
            [
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.index_info_len(),
                store.type_alias_len(),
                store.symbol_store().symbol_table_len(),
            ],
            store.relation_state_snapshot(),
            parsed
                .arena
                .iter()
                .map(|(node, _)| {
                    let node = node_ref(parsed, node);
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
                    )
                })
                .collect::<Vec<_>>(),
            store
                .source_file_links(checker.source_file(FILE).unwrap())
                .cloned(),
            checker.diagnostics().clone(),
        )
    };
    let file = checker.source_file(FILE).unwrap();
    assert!(
        checker
            .store()
            .source_file_links(file)
            .unwrap()
            .type_checked
    );
    let before = snapshot(checker);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        assert_eq!(snapshot(checker), before);
        checker.recheck_source_file(FILE).unwrap();
        for &(nodes, target, source) in writes {
            assert_private_target(checker, parsed, nodes, target);
            assert_source_result(checker, parsed, nodes, source, target);
        }
        assert_eq!(snapshot(checker), before);
    }
}

#[test]
fn private_destructuring_writes_keep_distinct_owners_in_both_query_orders() {
    let parsed = parse_source_file(concat!(
        "class Numbers {\n",
        "  #state: number = 0;\n",
        "  update(value: number): void {\n",
        "    const source = { value };\n",
        "    ({ value: this.#state } = source);\n",
        "    const after: number = this.#state;\n",
        "  }\n",
        "}\n",
        "class Text {\n",
        "  #state: string = '';\n",
        "  update(value: string): void {\n",
        "    const source = { value };\n",
        "    ({ value: this.#state } = source);\n",
        "    const after: string = this.#state;\n",
        "  }\n",
        "}\n",
    ));
    let numeric_case = write_nodes(&parsed, "Numbers");
    let text_case = write_nodes(&parsed, "Text");
    for query_first in [false, true] {
        let mut checker = context(&parsed);
        if query_first {
            checker.get_type_at_location(text_case.target).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let first = assert_private_target(&mut checker, &parsed, &numeric_case, number);
        let second = assert_private_target(&mut checker, &parsed, &text_case, string);
        assert_ne!(first, second);
        assert_ne!(
            checker.store().symbol(first).unwrap().name(),
            checker.store().symbol(second).unwrap().name()
        );
        assert_ne!(
            symbol(&checker, numeric_case.parameter),
            symbol(&checker, text_case.parameter)
        );
        assert_ne!(
            symbol(&checker, numeric_case.source),
            symbol(&checker, text_case.source)
        );
        assert_source_result(&mut checker, &parsed, &numeric_case, number, number);
        assert_source_result(&mut checker, &parsed, &text_case, string, string);
        assert_stable_replay(
            &mut checker,
            &parsed,
            &[
                (&numeric_case, number, number),
                (&text_case, string, string),
            ],
        );
    }
}

#[test]
fn private_destructuring_writes_report_the_exact_target_error() {
    let source = concat!(
        "class Numbers {\n",
        "  #state: number = 0;\n",
        "  update(value: string): void {\n",
        "    const source = { value };\n",
        "    ({ value: this.#state } = source);\n",
        "    const after: number = this.#state;\n",
        "  }\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    let nodes = write_nodes(&parsed, "Numbers");
    for query_first in [false, true] {
        let mut checker = context(&parsed);
        if query_first {
            checker.get_type_at_location(nodes.assignment).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!(
                "expected one private-field assignment error: {:?}",
                checker.diagnostics()
            )
        };
        assert_eq!(diagnostic.node, Some(nodes.target));
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'."
        );
        let range = parsed.arena.get(nodes.target.node).unwrap().range;
        assert_eq!(
            &source[range.start.get() as usize..range.end.get() as usize],
            "this.#state"
        );
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        assert_private_target(&mut checker, &parsed, &nodes, number);
        assert_source_result(&mut checker, &parsed, &nodes, string, number);
        assert_stable_replay(&mut checker, &parsed, &[(&nodes, number, string)]);
    }
}

#[test]
fn private_destructuring_writes_complete_constructor_initialization() {
    let parsed = parse_source_file(concat!(
        "class Numbers {\n",
        "  #state: number;\n",
        "  constructor(value: number) {\n",
        "    const source = { value };\n",
        "    ({ value: this.#state } = source);\n",
        "    const after: number = this.#state;\n",
        "  }\n",
        "}\n",
    ));
    let nodes = write_nodes(&parsed, "Numbers");
    let NodeData::PropertyDeclaration(field) = &parsed.arena.get(nodes.field.node).unwrap().data
    else {
        panic!("expected the private field")
    };
    assert_eq!(field.initializer, None);
    assert_eq!(field.postfix_token, None);
    for query_first in [false, true] {
        let mut checker = context(&parsed);
        if query_first {
            checker.get_type_at_location(nodes.target).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        assert_private_target(&mut checker, &parsed, &nodes, number);
        assert_source_result(&mut checker, &parsed, &nodes, number, number);
        assert_stable_replay(&mut checker, &parsed, &[(&nodes, number, number)]);
    }
}
