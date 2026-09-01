use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData,
};
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_880);
const LIBRARIES: [(&str, &str); 2] = [
    (
        "lib.es5.d.ts",
        include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
    ),
    (
        "lib.es2015.collection.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.collection.d.ts"),
    ),
];
const PREFIX: &str = concat!(
    "export {};\n",
    "type Node = { regex?: RegExp; children: Node[]; };\n",
    "declare const parentNode: Node;\n",
    "declare const childNode: Node;\n",
    "declare const handledNodes: Set<Node>;\n",
    "const _pushToLeaves = (parent: Node, child: Node, handled: Set<Node>): void => {\n",
    "  if (handled.has(parent)) {\n",
    "    return;\n",
    "  }\n",
    "  handled.add(parent);\n",
    "  const { children } = parent;\n",
);

fn context<'a>(
    parsed: &'a ParseResult,
    libraries: &'a [ParseResult; 2],
) -> CanonicalCheckerContext<'a> {
    let files = libraries
        .iter()
        .enumerate()
        .map(|(index, parsed)| {
            (
                FileId::new(u32::try_from(index).unwrap()),
                parsed,
                format!("\"/__typescript/lib/{}\"", LIBRARIES[index].0),
                true,
            )
        })
        .chain(std::iter::once((
            FILE,
            parsed,
            "\"/project/callable-object-bindings.ts\"".to_owned(),
            false,
        )))
        .collect::<Vec<_>>();
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, library) in &files {
        assert!(
            parsed.diagnostics.is_empty(),
            "{path}: {:?}",
            parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                *file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    *library,
                    *library,
                    if *library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_implied_node_format(ModuleKind::EsNext),
            )
            .unwrap();
    }
    for (file, parsed, _, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, *file)
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
            no_implicit_any: true,
            no_unchecked_indexed_access: true,
            strict_function_types: true,
            module_kind: ModuleKind::EsNext,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::EsNext,
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

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)))
        .collect::<Vec<_>>();
    let [found] = matches.as_slice() else {
        panic!("expected one {kind:?}")
    };
    *found
}

fn named(parsed: &ParseResult, id: NodeId, expected: &str) -> bool {
    matches!(&parsed.arena.get(id).unwrap().data, NodeData::Identifier(name) if name.text == expected)
}

fn call(parsed: &ParseResult, expected: &str) -> NodeRef {
    let calls = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            let callee = match &parsed.arena.get(call.expression).unwrap().data {
                NodeData::PropertyAccessExpression(property) => property.name,
                _ => call.expression,
            };
            named(parsed, callee, expected).then_some(node(parsed, id))
        })
        .collect::<Vec<_>>();
    let [found] = calls.as_slice() else {
        panic!("expected one call to {expected}")
    };
    *found
}

fn library_method(parsed: &ParseResult, file: FileId, owner: &str, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            if !named(parsed, interface.name, owner) {
                return None;
            }
            interface.members.nodes.iter().find_map(|&id| {
                let NodeData::MethodSignatureDeclaration(method) = &parsed.arena.get(id)?.data
                else {
                    return None;
                };
                named(parsed, method.name, name).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    id,
                ))
            })
        })
        .unwrap_or_else(|| panic!("missing actual {owner}.{name} declaration"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
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

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.type_alias_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

#[allow(clippy::too_many_lines)] // Keep source, library, diagnostic, and replay checks on the same context.
fn check(argument: &str, error: Option<&str>) {
    let source = format!(
        "{PREFIX}  children.push({argument});\n}};\n_pushToLeaves(parentNode, childNode, handledNodes);\n"
    );
    let parsed = parse_source_file(&source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let libraries = LIBRARIES.map(|(_, source)| parse_source_file(source));
    let arrow = only(&parsed, SyntaxKind::ArrowFunction);
    let NodeData::ArrowFunction(function) = &parsed.arena.get(arrow.node).unwrap().data else {
        unreachable!()
    };
    let binding = only(&parsed, SyntaxKind::BindingElement);
    let NodeData::BindingElement(element) = &parsed.arena.get(binding.node).unwrap().data else {
        unreachable!()
    };
    assert!(element.property_name.is_none());
    assert!(element.initializer.is_none());
    let local = node(&parsed, element.name.unwrap());
    let initializer = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            (parsed.arena.get(variable.name)?.kind == SyntaxKind::ObjectBindingPattern)
                .then(|| node(&parsed, variable.initializer.unwrap()))
        })
        .unwrap();
    let alias = only(&parsed, SyntaxKind::TypeAliasDeclaration);
    let NodeData::TypeAliasDeclaration(alias) = &parsed.arena.get(alias.node).unwrap().data else {
        unreachable!()
    };
    let NodeData::TypeLiteralNode(shape) = &parsed.arena.get(alias.type_).unwrap().data else {
        unreachable!()
    };
    let (property, array_annotation) = shape
        .members
        .nodes
        .iter()
        .find_map(|&id| {
            let NodeData::PropertySignatureDeclaration(property) = &parsed.arena.get(id)?.data
            else {
                return None;
            };
            named(&parsed, property.name, "children")
                .then_some((node(&parsed, id), node(&parsed, property.type_)))
        })
        .unwrap();
    let [has, add, push, invoke] =
        ["has", "add", "push", "_pushToLeaves"].map(|name| call(&parsed, name));
    let NodeData::CallExpression(push_call) = &parsed.arena.get(push.node).unwrap().data else {
        unreachable!()
    };
    let [push_argument] = push_call.arguments.nodes.as_slice() else {
        panic!("push must have one argument")
    };
    let push_argument = node(&parsed, *push_argument);
    let NodeData::PropertyAccessExpression(push_property) =
        &parsed.arena.get(push_call.expression).unwrap().data
    else {
        unreachable!()
    };
    let receiver = node(&parsed, push_property.expression);
    let methods = [
        library_method(&libraries[1], FileId::new(1), "Set", "has"),
        library_method(&libraries[1], FileId::new(1), "Set", "add"),
        library_method(&libraries[0], FileId::new(0), "Array", "push"),
    ];

    for query_first in [false, true] {
        let mut context = context(&parsed, &libraries);
        assert!(context.global_types().diagnostics().is_empty());
        if query_first {
            context.get_type_at_location(local).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let local_symbol = symbol(&context, binding);
        let property_symbol = symbol(&context, property);
        let parameters = function
            .parameters
            .nodes
            .iter()
            .map(|&id| node(&parsed, id))
            .collect::<Vec<_>>();
        let parameter_symbols = parameters
            .iter()
            .map(|&parameter| symbol(&context, parameter))
            .collect::<Vec<_>>();
        let parameter_types = parameters
            .iter()
            .zip(&parameter_symbols)
            .map(|(parameter, &parameter_symbol)| {
                let NodeData::ParameterDeclaration(parameter) =
                    &parsed.arena.get(parameter.node).unwrap().data
                else {
                    unreachable!()
                };
                let name = node(&parsed, parameter.name);
                assert_eq!(
                    context.get_symbol_at_location(name).unwrap(),
                    Some(parameter_symbol)
                );
                let type_ = context.get_type_at_location(name).unwrap();
                assert_eq!(
                    context
                        .get_type_at_location(node(&parsed, parameter.type_.unwrap()))
                        .unwrap(),
                    type_
                );
                type_
            })
            .collect::<Vec<_>>();
        let [node_type, child_type, set_type] = parameter_types.as_slice() else {
            panic!("the original arrow has three parameters")
        };
        assert_eq!(node_type, child_type);
        assert_eq!(
            context.get_type_at_location(initializer).unwrap(),
            *node_type
        );
        assert_eq!(
            context.get_symbol_at_location(initializer).unwrap(),
            Some(parameter_symbols[0])
        );
        let children_type = context.get_type_at_location(local).unwrap();
        assert_eq!(
            context.get_type_at_location(receiver).unwrap(),
            children_type
        );
        assert_eq!(
            context.get_symbol_at_location(receiver).unwrap(),
            Some(local_symbol)
        );
        assert_eq!(
            context.get_type_at_location(array_annotation).unwrap(),
            children_type
        );
        assert_eq!(
            context.get_symbol_at_location(local).unwrap(),
            Some(local_symbol)
        );
        assert_ne!(local_symbol, property_symbol);
        assert!(!parameter_symbols.contains(&local_symbol));
        let local_record = context.store().symbol(local_symbol).unwrap();
        assert_eq!(local_record.declarations(), Some(&[binding][..]));
        assert_eq!(local_record.value_declaration(), Some(binding));
        assert_eq!(
            local_record.parent(),
            context
                .store()
                .symbol(parameter_symbols[0])
                .unwrap()
                .parent()
        );
        assert_eq!(
            context
                .store()
                .symbol(property_symbol)
                .unwrap()
                .declarations(),
            Some(&[property][..])
        );
        assert_eq!(
            context.store().symbol(property_symbol).unwrap().parent(),
            Some(symbol(&context, node(&parsed, alias.type_)))
        );
        for owner in [local_symbol, property_symbol] {
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(owner)
                    .unwrap()
                    .resolved_type,
                Some(children_type)
            );
        }
        let TypeData::TypeReference(array) =
            context.store().type_payload(children_type).unwrap().data()
        else {
            panic!("children must keep the real Node[] reference")
        };
        assert_eq!(array.object.target, Some(context.global_types().array_type));
        assert_eq!(
            array.resolved_type_arguments.as_deref(),
            Some(&[*node_type][..])
        );
        let TypeData::TypeReference(set) = context.store().type_payload(*set_type).unwrap().data()
        else {
            panic!("handled must keep the real Set<Node> reference")
        };
        assert_eq!(
            set.resolved_type_arguments.as_deref(),
            Some(&[*node_type][..])
        );
        let set_owner = context
            .store()
            .symbol(symbol(&context, methods[0]))
            .unwrap()
            .parent();
        assert_eq!(
            context
                .store()
                .type_payload(set.object.target.unwrap())
                .unwrap()
                .symbol(),
            set_owner
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (boolean, number, void) = (
            bootstrap.boolean_type,
            bootstrap.number_type,
            bootstrap.void_type,
        );
        for ((call, declaration), expected) in [has, add, push]
            .into_iter()
            .zip(methods)
            .zip([boolean, *set_type, number])
        {
            assert_eq!(context.get_type_at_location(call).unwrap(), expected);
            assert_eq!(
                context
                    .store()
                    .signature(signature(&context, call))
                    .unwrap()
                    .declaration(),
                Some(declaration)
            );
        }
        assert_eq!(context.get_type_at_location(invoke).unwrap(), void);
        let arrow_signature = signature(&context, arrow);
        assert_eq!(signature(&context, invoke), arrow_signature);
        let callable = context.store().signature(arrow_signature).unwrap();
        assert_eq!(callable.declaration(), Some(arrow));
        assert_eq!(callable.parameters(), parameter_symbols);
        assert_eq!(callable.min_argument_count(), 3);
        assert!(callable.type_parameters().is_empty());
        assert_eq!(callable.resolved_return_type(), Some(void));
        match error {
            None => assert!(context.diagnostics().is_empty()),
            Some(message) => {
                let [diagnostic] = context.diagnostics().as_slice() else {
                    panic!("only the changed push argument must fail")
                };
                assert_eq!(diagnostic.diagnostic.code(), 2345);
                assert_eq!(diagnostic.node, Some(push_argument));
                assert_eq!(diagnostic.range_override, None);
                assert!(diagnostic.related_information.is_empty());
                assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
            }
        }
        let before = counts(&context);
        let diagnostics = context.diagnostics().clone();
        let nodes = parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let location = node(&parsed, id);
                (
                    location,
                    context.store().type_node_links(location).cloned(),
                    context.store().symbol_node_links(location).cloned(),
                    context.store().signature_links(location).cloned(),
                )
            })
            .collect::<Vec<_>>();
        let owners = parameter_symbols
            .iter()
            .copied()
            .chain([local_symbol, property_symbol])
            .map(|owner| (owner, context.store().value_symbol_links(owner).cloned()))
            .collect::<Vec<_>>();
        for _ in 0..2 {
            context.check_source_file(FILE).unwrap();
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(context.get_type_at_location(local).unwrap(), children_type);
            assert_eq!(
                context.get_symbol_at_location(local).unwrap(),
                Some(local_symbol)
            );
            assert_eq!(signature(&context, arrow), arrow_signature);
            assert_eq!(signature(&context, invoke), arrow_signature);
            for (location, types, symbols, signatures) in &nodes {
                assert_eq!(context.store().type_node_links(*location), types.as_ref());
                assert_eq!(
                    context.store().symbol_node_links(*location),
                    symbols.as_ref()
                );
                assert_eq!(
                    context.store().signature_links(*location),
                    signatures.as_ref()
                );
            }
            for (owner, links) in &owners {
                assert_eq!(context.store().value_symbol_links(*owner), links.as_ref());
            }
            assert_eq!(context.diagnostics(), &diagnostics);
            assert_eq!(counts(&context), before);
        }
    }
}

#[test]
fn callable_object_binding_keeps_the_real_node_array_and_replay() {
    check("child", None);
}

#[test]
fn callable_object_binding_reports_the_original_push_argument_error() {
    check(
        "1",
        Some("Argument of type 'number' is not assignable to parameter of type 'Node'."),
    );
}
