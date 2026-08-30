use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    ArrayLiteralLinks, CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    NodeLinks, SignatureId, SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId,
    TypeNodeLinks, signatures::TypePredicateKind, types::TypeFlags,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(8_300);
const SOURCE_FILE: FileId = FileId::new(8_301);
const LIBRARY: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'arena>(
    library: &'arena ParseResult,
    parsed: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (LIBRARY_FILE, library, "\"/lib/lib.es5.d.ts\"", true),
        (
            SOURCE_FILE,
            parsed,
            "\"/project/filter-controls.ts\"",
            false,
        ),
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
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
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

fn reference(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), SOURCE_FILE, node)
}

fn variable(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(reference(parsed, node))
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn initializer(parsed: &ParseResult, expected: &str) -> NodeRef {
    let node = variable(parsed, expected);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(node.node).unwrap().data else {
        unreachable!()
    };
    reference(parsed, variable.initializer.unwrap())
}

fn nodes_of_kind(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some((record.range.start, reference(parsed, node)))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|(start, _)| *start);
    nodes.into_iter().map(|(_, node)| node).collect()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn checked_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type at {node:?}"))
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap_or_else(|| panic!("missing signature at {node:?}"))
}

fn array_element(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> TypeId {
    let TypeData::TypeReference(array) = context.store().type_payload(type_).unwrap().data() else {
        panic!("filter must retain a real Array reference")
    };
    assert_eq!(array.object.target, Some(context.global_types().array_type));
    let [element] = array.resolved_type_arguments.as_deref().unwrap() else {
        panic!("Array must retain its one element type")
    };
    *element
}

fn assert_boolean_constructor(context: &CanonicalCheckerContext<'_>, callback: NodeRef) {
    let type_ = checked_type(context, callback);
    let TypeData::Interface(interface) = context.store().type_payload(type_).unwrap().data() else {
        panic!("Boolean must retain its declared constructor interface")
    };
    let structured = &interface.reference.object.structured;
    let [call, construct] = structured.signatures.as_deref().unwrap() else {
        panic!("Boolean must retain the bundled call and construct signatures")
    };
    assert_eq!(structured.call_signature_count, 1);
    let call = context.store().signature(*call).unwrap();
    assert_eq!(call.declaration().unwrap().file, LIBRARY_FILE);
    assert_eq!(call.type_parameters().len(), 1);
    assert_eq!(call.parameters().len(), 1);
    assert_eq!(call.min_argument_count(), 0);
    assert_eq!(call.resolved_type_predicate(), None);
    assert_eq!(
        call.resolved_return_type(),
        Some(context.store().intrinsic_bootstrap().unwrap().boolean_type)
    );
    let construct = context.store().signature(*construct).unwrap();
    assert_eq!(construct.declaration().unwrap().file, LIBRARY_FILE);
    assert_eq!(construct.parameters().len(), 1);
    assert_eq!(construct.min_argument_count(), 0);
    let returned = context
        .store()
        .type_payload(construct.resolved_return_type().unwrap())
        .unwrap();
    assert_eq!(returned.flags(), TypeFlags::OBJECT);
    let owner = context.store().symbol(returned.symbol().unwrap()).unwrap();
    assert_eq!(owner.name().as_utf8(), Some("Boolean"));
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    common: Option<NodeLinks>,
    type_: Option<TypeNodeLinks>,
    signature: Option<SignatureLinks>,
    symbol: Option<SymbolNodeLinks>,
    array: Option<ArrayLiteralLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 8],
    nodes: Vec<NodeState>,
    source: Option<SourceFileLinks>,
}

fn publication(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Publication {
    let store = context.store();
    Publication {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_predicate_len(),
            store.conditional_root_len(),
            store.type_alias_len(),
            store.index_info_len(),
        ],
        nodes: parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = reference(parsed, node);
                NodeState {
                    node,
                    common: store.node_links(node).cloned(),
                    type_: store.type_node_links(node).cloned(),
                    signature: store.signature_links(node).cloned(),
                    symbol: store.symbol_node_links(node).cloned(),
                    array: store.array_literal_links(node).cloned(),
                }
            })
            .collect(),
        source: store
            .source_file_links(context.source_file(SOURCE_FILE).unwrap())
            .cloned(),
    }
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    locations: &[(NodeRef, TypeId)],
) {
    for &(node, type_) in locations {
        assert_eq!(context.get_type_at_location(node), Ok(type_));
    }
    let warm = publication(context, parsed);
    let diagnostics = context.diagnostics().clone();
    for _ in 0..2 {
        for &(node, type_) in locations.iter().rev() {
            assert_eq!(context.get_type_at_location(node), Ok(type_));
        }
        context.recheck_source_file(SOURCE_FILE).unwrap();
        assert_eq!(publication(context, parsed), warm);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
fn interface_method_conditionals_capture_interface_and_method_parameters() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(concat!(
        "interface Select<T> {\n",
        "  pick<S>(value: S): T extends string ? S : number;\n",
        "}\n",
    ));
    let [conditional] = nodes_of_kind(&parsed, SyntaxKind::ConditionalType)[..] else {
        panic!("the method must retain its conditional return")
    };
    let [method] = nodes_of_kind(&parsed, SyntaxKind::MethodSignature)[..] else {
        panic!("the interface must retain its generic method")
    };
    let [interface_parameter, method_parameter] =
        nodes_of_kind(&parsed, SyntaxKind::TypeParameter)[..]
    else {
        panic!("the interface and method must each retain a type parameter")
    };
    for source_first in [false, true] {
        let mut context = context(&library, &parsed);
        if source_first {
            context.check_source_file(SOURCE_FILE).unwrap();
        }
        let conditional_type = context.get_type_from_type_node(conditional).unwrap();
        let parameter_types = [interface_parameter, method_parameter].map(|parameter| {
            let owner = symbol(&context, parameter);
            let type_ = context
                .store()
                .declared_type_links(owner)
                .and_then(|links| links.declared_type)
                .unwrap();
            let record = context.store().type_payload(type_).unwrap();
            assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
            assert_eq!(record.symbol(), Some(owner));
            assert_eq!(context.get_symbol_declarations(owner).unwrap(), [parameter]);
            type_
        });
        assert_ne!(parameter_types[0], parameter_types[1]);
        let TypeData::Conditional(conditional_data) = context
            .store()
            .type_payload(conditional_type)
            .unwrap()
            .data()
        else {
            panic!("the generic return must retain its deferred conditional")
        };
        let root_id = conditional_data.root;
        let root = context.store().conditional_root(root_id).unwrap();
        assert_eq!(root.node(), conditional);
        assert_eq!(root.check_type(), parameter_types[0]);
        assert_eq!(
            root.extends_type(),
            context.store().intrinsic_bootstrap().unwrap().string_type
        );
        assert_eq!(
            root.outer_type_parameters(),
            Some(parameter_types.as_slice())
        );
        assert!(root.is_distributive());
        assert!(root.infer_type_parameters().is_none_or(<[_]>::is_empty));

        context.check_source_file(SOURCE_FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let method_signature = signature(&context, method);
        let method_record = context.store().signature(method_signature).unwrap();
        assert_eq!(method_record.declaration(), Some(method));
        assert_eq!(method_record.type_parameters(), [parameter_types[1]]);
        assert_eq!(method_record.resolved_return_type(), Some(conditional_type));
        assert_eq!(
            context.get_return_type_of_signature(method_signature),
            Ok(conditional_type)
        );
        let root_cache = context
            .store()
            .conditional_root(root_id)
            .unwrap()
            .instantiations()
            .clone();
        assert_replay(&mut context, &parsed, &[(conditional, conditional_type)]);
        assert_eq!(
            context.get_type_from_type_node(conditional),
            Ok(conditional_type)
        );
        let root = context.store().conditional_root(root_id).unwrap();
        assert_eq!(
            root.outer_type_parameters(),
            Some(parameter_types.as_slice())
        );
        assert_eq!(root.instantiations(), &root_cache);
    }
}

#[test]
fn concrete_interface_conditionals_keep_property_types_and_assignment_diagnostics() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(concat!(
        "interface Ready { result: string extends string ? number : boolean; }\n",
        "declare const ready: Ready;\n",
        "const correct: number = ready.result;\n",
        "const wrong: string = ready.result;\n",
    ));
    let [conditional] = nodes_of_kind(&parsed, SyntaxKind::ConditionalType)[..] else {
        panic!("the property must retain its conditional annotation")
    };
    for source_first in [false, true] {
        let mut context = context(&library, &parsed);
        if source_first {
            context.check_source_file(SOURCE_FILE).unwrap();
        }
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(context.get_type_from_type_node(conditional), Ok(number));
        context.check_source_file(SOURCE_FILE).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the wrong assignment must retain exactly one diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        let wrong = variable(&parsed, "wrong");
        let NodeData::VariableDeclaration(wrong_data) = &parsed.arena.get(wrong.node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(diagnostic.node, Some(reference(&parsed, wrong_data.name)));
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        assert_replay(
            &mut context,
            &parsed,
            &[
                (conditional, number),
                (initializer(&parsed, "correct"), number),
                (initializer(&parsed, "wrong"), number),
            ],
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Compare the real overload, callback, and array types together.
fn bundled_array_filters_keep_boolean_truthiness_and_predicate_types() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(concat!(
        "declare const anys: any[];\n",
        "const anyFiltered = anys.filter(Boolean);\n",
        "declare const nullable: (string | null)[];\n",
        "const truthyFiltered = nullable.filter(Boolean);\n",
        "const objectFiltered = [{ name: 'x' }].filter(value => value.name);\n",
        "const booleanFiltered = [true, true, false, null].filter(\n",
        "  (thing): thing is boolean => thing !== null\n",
        ");\n",
    ));
    let calls = [
        "anyFiltered",
        "truthyFiltered",
        "objectFiltered",
        "booleanFiltered",
    ]
    .map(|name| initializer(&parsed, name));
    for source_first in [false, true] {
        let mut context = context(&library, &parsed);
        assert!(context.global_type_diagnostics().next().is_none());
        if source_first {
            context.check_source_file(SOURCE_FILE).unwrap();
        } else {
            context.get_type_at_location(calls[3]).unwrap();
        }
        context.check_source_file(SOURCE_FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );

        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (any, string, boolean, null) = (
            bootstrap.any_type,
            bootstrap.string_type,
            bootstrap.boolean_type,
            bootstrap.null_type,
        );
        let results = calls.map(|call| checked_type(&context, call));
        let elements = results.map(|type_| array_element(&context, type_));
        assert_eq!(elements[0], any);
        let TypeData::Union(nullable) = context.store().type_payload(elements[1]).unwrap().data()
        else {
            panic!("Boolean must not remove null from the static element type")
        };
        assert_eq!(nullable.union.types.len(), 2);
        assert!(nullable.union.types.contains(&string));
        assert!(nullable.union.types.contains(&null));
        assert_eq!(elements[3], boolean);
        assert!(
            !context
                .store()
                .type_payload(elements[2])
                .unwrap()
                .flags()
                .intersects(TypeFlags::ANY | TypeFlags::UNKNOWN | TypeFlags::NEVER)
        );
        let TypeData::Object(object) = context.store().type_payload(elements[2]).unwrap().data()
        else {
            panic!("the object filter must retain its element properties")
        };
        let [property] = object.structured.properties.as_deref().unwrap() else {
            panic!("the object element must retain its one name property")
        };
        assert_eq!(
            context.store().symbol(*property).unwrap().name().as_utf8(),
            Some("name")
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(*property)
                .unwrap()
                .resolved_type,
            Some(string)
        );

        let array_owner = context
            .store()
            .type_payload(context.global_types().array_type)
            .unwrap()
            .symbol()
            .unwrap();
        let methods = context
            .store()
            .symbol(array_owner)
            .unwrap()
            .members()
            .unwrap();
        let filter = context
            .store()
            .symbol_table(methods)
            .unwrap()
            .get_source("filter")
            .unwrap();
        let declarations = context
            .store()
            .symbol(filter)
            .unwrap()
            .declarations()
            .unwrap();
        let [predicate, ordinary] = declarations else {
            panic!("the bundled Array.filter must retain its two overloads")
        };
        let (predicate, ordinary) = (*predicate, *ordinary);
        assert_eq!(predicate.file, LIBRARY_FILE);
        assert_eq!(ordinary.file, LIBRARY_FILE);
        let mut locations = Vec::new();
        for (index, call) in calls.into_iter().enumerate() {
            let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data
            else {
                unreachable!()
            };
            let callee = reference(&parsed, call_data.expression);
            let NodeData::PropertyAccessExpression(access) =
                &parsed.arena.get(callee.node).unwrap().data
            else {
                unreachable!()
            };
            let receiver = reference(&parsed, access.expression);
            let callback = reference(&parsed, call_data.arguments.nodes[0]);
            let selected = signature(&context, call);
            let selected_record = context.store().signature(selected).unwrap();
            assert_eq!(
                selected_record.declaration(),
                Some(if index == 3 { predicate } else { ordinary })
            );
            assert_eq!(selected_record.resolved_return_type(), Some(results[index]));
            assert_eq!(selected_record.min_argument_count(), 1);
            assert_eq!(selected_record.parameters().len(), 2);
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(callee)
                    .unwrap()
                    .resolved_symbol,
                Some(filter)
            );
            if index < 3 {
                assert_eq!(
                    array_element(&context, checked_type(&context, receiver)),
                    elements[index]
                );
            }
            locations.extend([
                (call, results[index]),
                (receiver, checked_type(&context, receiver)),
                (callee, checked_type(&context, callee)),
                (callback, checked_type(&context, callback)),
            ]);
            if index < 2 {
                assert_boolean_constructor(&context, callback);
                continue;
            }
            let NodeData::ArrowFunction(arrow) = &parsed.arena.get(callback.node).unwrap().data
            else {
                panic!("the source must keep its original arrow callback")
            };
            let parameter = reference(&parsed, arrow.parameters.nodes[0]);
            let parameter_owner = symbol(&context, parameter);
            let callback_signature = signature(&context, callback);
            let callback_record = context.store().signature(callback_signature).unwrap();
            let return_type = if index == 2 { string } else { boolean };
            assert_eq!(callback_record.parameters(), [parameter_owner]);
            assert_eq!(callback_record.resolved_return_type(), Some(return_type));
            let parameter_type = context
                .store()
                .value_symbol_links(parameter_owner)
                .and_then(|links| links.resolved_type)
                .unwrap();
            assert_eq!(
                parameter_type,
                array_element(&context, checked_type(&context, receiver))
            );
            if index == 2 {
                assert_eq!(callback_record.resolved_type_predicate(), None);
            } else {
                let predicate = callback_record
                    .resolved_type_predicate()
                    .and_then(|predicate| context.store().type_predicate(predicate))
                    .unwrap();
                assert_eq!(predicate.kind(), TypePredicateKind::Identifier);
                assert_eq!(predicate.parameter_name(), "thing");
                assert_eq!(predicate.parameter_index(), 0);
                assert_eq!(predicate.type_id(), Some(boolean));
                assert_eq!(
                    context.type_to_string(parameter_type).unwrap(),
                    "boolean | null"
                );
            }
            locations.push((reference(&parsed, arrow.body), return_type));
        }
        assert_replay(&mut context, &parsed, &locations);
    }
}
