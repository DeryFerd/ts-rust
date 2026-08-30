use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(19_860);

// The final two classes from the pinned abstractPropertyInConstructor.ts, including CRLF.
const ORIGINAL_TAIL: &str = concat!(
    "abstract class C1 {\r\n",
    "    abstract x: string;\r\n",
    "    abstract y: string;\r\n",
    "\r\n",
    "    constructor() {\r\n",
    "        let self = this;                // ok\r\n",
    "        let { x, y: y1 } = this;        // error\r\n",
    "        ({ x, y: y1, \"y\": y1 } = this); // error\r\n",
    "    }\r\n",
    "}\r\n",
    "\r\n",
    "class C2 {\r\n",
    "    x: string;\r\n",
    "    y: string;\r\n",
    "\r\n",
    "    constructor() {\r\n",
    "        let self = this;                // ok\r\n",
    "        let { x, y: y1 } = this;        // ok\r\n",
    "        ({ x, y: y1, \"y\": y1 } = this); // ok\r\n",
    "    }\r\n",
    "}\r\n",
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
                EscapedName::source("\"/project/abstractPropertyInConstructor.ts\""),
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
                ..IntrinsicBootstrapOptions::default()
            },
            strict_bind_call_apply: true,
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            strict_property_initialization: true,
            use_unknown_in_catch_variables: true,
            no_implicit_any: true,
            no_implicit_this: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

struct BindingNodes {
    class: NodeRef,
    fields: [NodeRef; 2],
    field_names: [NodeRef; 2],
    elements: [NodeRef; 2],
    locals: [NodeRef; 2],
    key: NodeRef,
    binding_receiver: NodeRef,
    parentheses: NodeRef,
    assignment: NodeRef,
    object: NodeRef,
    properties: [NodeRef; 3],
    keys: [NodeRef; 3],
    values: [NodeRef; 2],
    assignment_receiver: NodeRef,
}

#[allow(clippy::too_many_lines)] // Follow the actual declaration and assignment AST once.
fn binding_nodes(parsed: &ParseResult, expected: &str) -> BindingNodes {
    let (class_id, class) = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(class.name?)?.data else {
                return None;
            };
            (name.text == expected).then_some((id, class))
        })
        .unwrap();
    let [first, second, constructor] = class.members.nodes.as_slice() else {
        panic!("each control class must keep two fields and one constructor")
    };
    let fields = [node(parsed, *first), node(parsed, *second)];
    let field_names = fields.map(|field| {
        let NodeData::PropertyDeclaration(property) = &parsed.arena.get(field.node).unwrap().data
        else {
            panic!("the member must be the real field declaration")
        };
        node(parsed, property.name)
    });
    let NodeData::ConstructorDeclaration(constructor) =
        &parsed.arena.get(*constructor).unwrap().data
    else {
        panic!("the final member must be the actual constructor")
    };
    let NodeData::Block(body) = &parsed.arena.get(constructor.body.unwrap()).unwrap().data else {
        panic!("the constructor must retain its body")
    };
    let [_, binding, assignment_statement] = body.statements.nodes.as_slice() else {
        panic!("the original constructor must retain all three statements")
    };
    let NodeData::VariableStatement(statement) = &parsed.arena.get(*binding).unwrap().data else {
        panic!("the second statement must declare the bindings")
    };
    let NodeData::VariableDeclarationList(list) =
        &parsed.arena.get(statement.declaration_list).unwrap().data
    else {
        panic!("the binding must retain its declaration list")
    };
    let [declaration] = list.declarations.nodes.as_slice() else {
        panic!("the binding statement must have one declaration")
    };
    let NodeData::VariableDeclaration(declaration) = &parsed.arena.get(*declaration).unwrap().data
    else {
        unreachable!()
    };
    let pattern_record = parsed.arena.get(declaration.name).unwrap();
    assert_eq!(pattern_record.kind, SyntaxKind::ObjectBindingPattern);
    let NodeData::BindingPattern(pattern) = &pattern_record.data else {
        panic!("the declaration must retain its object binding pattern")
    };
    let [first, second] = pattern.elements.nodes.as_slice() else {
        panic!("the pattern must retain the shorthand and renamed bindings")
    };
    let elements = [node(parsed, *first), node(parsed, *second)];
    let locals = elements.map(|element| {
        let NodeData::BindingElement(binding) = &parsed.arena.get(element.node).unwrap().data
        else {
            unreachable!()
        };
        node(parsed, binding.name.unwrap())
    });
    let NodeData::BindingElement(renamed) = &parsed.arena.get(*second).unwrap().data else {
        unreachable!()
    };
    let key = node(parsed, renamed.property_name.unwrap());
    let binding_receiver = node(parsed, declaration.initializer.unwrap());
    let NodeData::ExpressionStatement(statement) =
        &parsed.arena.get(*assignment_statement).unwrap().data
    else {
        panic!("the last statement must remain an assignment expression")
    };
    let parentheses = node(parsed, statement.expression);
    let NodeData::ParenthesizedExpression(parenthesized) =
        &parsed.arena.get(parentheses.node).unwrap().data
    else {
        panic!("the original parentheses must remain present")
    };
    let assignment = node(parsed, parenthesized.expression);
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        panic!("the parenthesized expression must contain the assignment")
    };
    let object = node(parsed, binary.left);
    let NodeData::ObjectLiteralExpression(literal) = &parsed.arena.get(object.node).unwrap().data
    else {
        panic!("the assignment must keep its real object literal pattern")
    };
    let [first, second, third] = literal.properties.nodes.as_slice() else {
        panic!("the pattern must retain both spellings of the duplicate property")
    };
    let properties = [
        node(parsed, *first),
        node(parsed, *second),
        node(parsed, *third),
    ];
    let keys = properties.map(
        |property| match &parsed.arena.get(property.node).unwrap().data {
            NodeData::ShorthandPropertyAssignment(property) => node(parsed, property.name),
            NodeData::PropertyAssignment(property) => node(parsed, property.name),
            _ => panic!("the original pattern must keep its actual property declarations"),
        },
    );
    let values = [properties[1], properties[2]].map(|property| {
        let NodeData::PropertyAssignment(property) = &parsed.arena.get(property.node).unwrap().data
        else {
            unreachable!()
        };
        node(parsed, property.initializer)
    });
    BindingNodes {
        class: node(parsed, class_id),
        fields,
        field_names,
        elements,
        locals,
        key,
        binding_receiver,
        parentheses,
        assignment,
        object,
        properties,
        keys,
        values,
        assignment_receiver: node(parsed, binary.right),
    }
}

fn read_row(
    context: &mut CanonicalCheckerContext<'_>,
    location: NodeRef,
    symbol_first: bool,
) -> (TypeId, Option<SemanticSymbolId>) {
    if symbol_first {
        let symbol = context.get_symbol_at_location(location).unwrap();
        (context.get_type_at_location(location).unwrap(), symbol)
    } else {
        let type_ = context.get_type_at_location(location).unwrap();
        (type_, context.get_symbol_at_location(location).unwrap())
    }
}

#[allow(clippy::too_many_lines)] // Compare every artifact row with the same source and binder graph.
fn assert_binding_rows(
    context: &mut CanonicalCheckerContext<'_>,
    nodes: &BindingNodes,
    types: [TypeId; 2],
    object_display: &str,
    symbol_first: bool,
) {
    let fields = nodes.fields.map(|field| symbol(context, field));
    let locals = nodes.elements.map(|element| symbol(context, element));
    let properties = nodes.properties.map(|property| symbol(context, property));
    assert_ne!(fields[0], locals[0]);
    assert_ne!(fields[1], locals[1]);
    assert_ne!(properties[0], locals[0]);
    assert_ne!(properties[0], fields[0]);
    assert_ne!(properties[1], fields[1]);
    assert_eq!(properties[1], properties[2]);
    assert_eq!(
        context.get_symbol_declarations(properties[1]).unwrap(),
        &nodes.properties[1..]
    );
    for (local, element) in locals.into_iter().zip(nodes.elements) {
        assert_eq!(context.get_symbol_declarations(local).unwrap(), &[element]);
    }

    let this_type = context
        .get_type_at_location(nodes.binding_receiver)
        .unwrap();
    assert_eq!(context.type_to_string(this_type).unwrap(), "this");
    let object_type = context.get_type_at_location(nodes.object).unwrap();
    assert_ne!(object_type, this_type);
    assert_eq!(context.type_to_string(object_type).unwrap(), object_display);
    let record = context.store().type_payload(object_type).unwrap();
    assert_eq!(record.symbol(), Some(symbol(context, nodes.object)));
    let TypeData::Object(object) = record.data() else {
        panic!("the assignment pattern must retain its canonical object type")
    };
    let published = object.structured.properties.as_deref().unwrap();
    assert_eq!(published.len(), 2);
    for ((&property, raw), type_) in published.iter().zip(properties).zip(types) {
        let links = context.store().value_symbol_links(property).unwrap();
        assert_eq!(links.target, Some(raw));
        assert_eq!(links.resolved_type, Some(type_));
    }

    // Go getTypeOfNode returns errorType for an explicit binding propertyName.
    // Its independent symbol query still returns the actual source property.
    let error_type = context.store().intrinsic_bootstrap().unwrap().error_type;
    let expected = [
        (nodes.field_names[0], types[0], Some(fields[0])),
        (nodes.field_names[1], types[1], Some(fields[1])),
        (nodes.locals[0], types[0], Some(locals[0])),
        (nodes.key, error_type, Some(fields[1])),
        (nodes.locals[1], types[1], Some(locals[1])),
        (nodes.parentheses, this_type, None),
        (nodes.assignment, this_type, None),
        (nodes.object, object_type, None),
        (nodes.keys[0], types[0], Some(properties[0])),
        (nodes.keys[1], types[1], Some(properties[1])),
        (nodes.values[0], types[1], Some(locals[1])),
        (nodes.keys[2], types[1], Some(properties[1])),
        (nodes.values[1], types[1], Some(locals[1])),
        (
            nodes.assignment_receiver,
            this_type,
            Some(symbol(context, nodes.class)),
        ),
    ];
    for (location, type_, symbol) in expected {
        assert_eq!(read_row(context, location, symbol_first), (type_, symbol));
    }
    assert_eq!(context.type_to_string(error_type).unwrap(), "any");
    for (field, type_) in fields.into_iter().zip(types) {
        assert_eq!(
            context
                .store()
                .value_symbol_links(field)
                .unwrap()
                .resolved_type,
            Some(type_)
        );
    }
}

fn assert_diagnostics(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    cases: &[(&str, bool, BindingNodes)],
) {
    let mut expected = Vec::new();
    for (class, abstract_, nodes) in cases {
        let names = nodes.field_names.map(|name| {
            let NodeData::Identifier(name) = &parsed.arena.get(name.node).unwrap().data else {
                unreachable!()
            };
            name.text.as_str()
        });
        if *abstract_ {
            for (location, name) in [
                (nodes.locals[0], names[0]),
                (nodes.key, names[1]),
                (nodes.keys[0], names[0]),
                (nodes.keys[1], names[1]),
                (nodes.keys[2], names[1]),
            ] {
                expected.push((
                    2715,
                    parsed.arena.get(location.node).unwrap().range,
                    format!("Abstract property '{name}' in class '{class}' cannot be accessed in the constructor."),
                ));
            }
        } else {
            for (location, name) in nodes.field_names.into_iter().zip(names) {
                expected.push((
                    2564,
                    parsed.arena.get(location.node).unwrap().range,
                    format!("Property '{name}' has no initializer and is not definitely assigned in the constructor."),
                ));
            }
        }
    }
    let actual = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            assert!(diagnostic.related_information.is_empty());
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
            (
                diagnostic.diagnostic.code(),
                range,
                diagnostic.diagnostic.render().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(actual, expected);
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 8] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.merged_symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
        store.properties_type_cache_len(),
    ]
}

fn check_queries_and_replay(
    parsed: &ParseResult,
    cases: &[(&str, bool, BindingNodes)],
    different_types: bool,
    object_display: &str,
) {
    for symbol_first in [true, false] {
        let mut context = context(parsed);
        let first = &cases[0].2;
        let expected_key = symbol(&context, first.fields[1]);
        let error_type = context.store().intrinsic_bootstrap().unwrap().error_type;
        assert_eq!(
            read_row(&mut context, first.key, symbol_first),
            (error_type, Some(expected_key))
        );
        context.check_source_file(FILE).unwrap();
        assert_diagnostics(&context, parsed, cases);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let types = if different_types {
            [bootstrap.number_type, bootstrap.boolean_type]
        } else {
            [bootstrap.string_type; 2]
        };
        for (_, _, nodes) in cases {
            assert_binding_rows(&mut context, nodes, types, object_display, symbol_first);
        }
        let links = |context: &CanonicalCheckerContext<'_>| {
            parsed
                .arena
                .iter()
                .map(|(id, _)| {
                    let location = node(parsed, id);
                    (
                        context.store().type_node_links(location).cloned(),
                        context.store().symbol_node_links(location).cloned(),
                        context.store().signature_links(location).cloned(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let before = (
            counts(&context),
            links(&context),
            context.diagnostics().clone(),
        );
        context.recheck_source_file(FILE).unwrap();
        for (_, _, nodes) in cases.iter().rev() {
            assert_binding_rows(&mut context, nodes, types, object_display, !symbol_first);
        }
        assert_diagnostics(&context, parsed, cases);
        assert_eq!(
            (
                counts(&context),
                links(&context),
                context.diagnostics().clone()
            ),
            before
        );
    }
}

#[test]
fn original_class_binding_rows_keep_property_and_local_identities_in_both_query_orders() {
    let parsed = parse_source_file(ORIGINAL_TAIL);
    let cases = [
        ("C1", true, binding_nodes(&parsed, "C1")),
        ("C2", false, binding_nodes(&parsed, "C2")),
    ];
    check_queries_and_replay(&parsed, &cases, false, "{ x: string; y: string; }");
}

#[test]
fn renamed_binding_rows_use_actual_property_types_and_duplicate_declarations() {
    let parsed = parse_source_file(concat!(
        "class Holder {\n",
        "  left: number;\n",
        "  right: boolean;\n",
        "  constructor() {\n",
        "    let self = this;\n",
        "    let { left, right: copy } = this;\n",
        "    ({ left, right: copy, \"right\": copy } = this);\n",
        "  }\n",
        "}\n",
    ));
    let cases = [("Holder", false, binding_nodes(&parsed, "Holder"))];
    check_queries_and_replay(&parsed, &cases, true, "{ left: number; right: boolean; }");
}
