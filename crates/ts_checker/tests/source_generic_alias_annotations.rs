use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(4_520);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    context_with_options(parsed, CanonicalCheckerOptions::default())
}

fn context_with_options(
    parsed: &ParseResult,
    options: CanonicalCheckerOptions,
) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-alias-annotations.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(binder.finish(), vec![(FILE, &parsed.arena)], options).unwrap()
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    let store = context.store();
    (
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
    )
}

#[test]
fn generic_alias_declarations_keep_parameter_and_return_query_identities() {
    let mut failures = Vec::new();
    for body in [
        "Value",
        "Scalar",
        "Box<Value>",
        "Boxed<Value>",
        "Value | undefined",
        "Box<Value> | ReadonlyBox<Value>",
    ] {
        let parsed = parse_source_file(&format!(
            "interface Array<T> {{}} interface ReadonlyArray<T> {{}} interface Box<T> {{ value: T }} \
             interface ReadonlyBox<T> {{ readonly value: T }} type Scalar = string; \
             type Boxed<T> = Box<T>; type Alias<Value> = {body}; \
             declare function pass<T>(value: Alias<T>): Alias<T>;"
        ));
        let mut context = context(&parsed);
        if let Err(error) = context.check_source_file(FILE) {
            failures.push(format!("{body}: {error:?}"));
            continue;
        }
        assert!(
            context.diagnostics().is_empty(),
            "{body}: {:?}",
            context.diagnostics()
        );
        let function = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    FILE,
                    node,
                ))
            })
            .unwrap();
        let symbol = context.file(FILE).unwrap().1.symbol(function).unwrap();
        let callable = context
            .store()
            .value_symbol_links(symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data()
        else {
            panic!("the declaration must retain a callable object")
        };
        let signature = object.structured.signatures.as_ref().unwrap()[0];
        let result = context.get_return_type_of_signature(signature).unwrap();
        let parameter = context.store().signature(signature).unwrap().parameters()[0];
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type,
            Some(result)
        );
        let before = counts(&context);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(
            context.get_return_type_of_signature(signature).unwrap(),
            result
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            Some(callable)
        );
        assert_eq!(counts(&context), before, "{body}");
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn generic_identity_alias_calls_reuse_existing_explicit_argument_inference() {
    let parsed = parse_source_file(concat!(
        "type Identity<Value> = Value; ",
        "declare function echo<T>(value: Identity<T>): Identity<T>; ",
        "const result: number = echo<number>(1);",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let call = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::CallExpression(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                FILE,
                node,
            ))
        })
        .unwrap();
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(
        context.store().type_node_links(call).unwrap().resolved_type,
        Some(number)
    );
    let before = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(&context), before);
}

#[test]
fn generic_alias_interface_calls_reuse_existing_reference_arguments() {
    let parsed = parse_source_file(concat!(
        "interface Box<T> { value: T } type Wrapped<Value> = Box<Value>; ",
        "declare function copy<T>(value: Wrapped<T>): Wrapped<T>; ",
        "declare const input: Box<number>; ",
        "const result: Box<number> = copy<number>(input);",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let before = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(&context), before);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn generic_alias_optional_parameters_keep_base_and_resolved_types_distinct() {
    for strict_null_checks in [false, true] {
        for (annotation, optional) in [
            ("T", true),
            ("Identity<T>", false),
            ("Identity<T>", true),
            ("(Identity<T>)", true),
        ] {
            let question = if optional { "?" } else { "" };
            let parsed = parse_source_file(&format!(
                "type Identity<Value> = Value; \
                 declare function f<T>(value{question}: {annotation}): Identity<T>;"
            ));
            let mut context = context_with_options(
                &parsed,
                CanonicalCheckerOptions {
                    intrinsic: IntrinsicBootstrapOptions {
                        strict_null_checks,
                        exact_optional_property_types: false,
                    },
                    ..CanonicalCheckerOptions::default()
                },
            );
            context.check_source_file(FILE).unwrap();
            assert!(context.diagnostics().is_empty());
            let declaration = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        parsed.arena.id(),
                        FILE,
                        node,
                    ))
                })
                .unwrap();
            let owner = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
            let callable = context
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type
                .unwrap();
            let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data()
            else {
                panic!("the declaration must retain a callable object")
            };
            let signature = object.structured.signatures.as_ref().unwrap()[0];
            let record = context.store().signature(signature).unwrap();
            assert_eq!(record.min_argument_count(), i32::from(!optional));
            let base = record.type_parameters()[0];
            let parameter = record.parameters()[0];
            let resolved = context
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type
                .unwrap();
            if strict_null_checks && optional {
                let TypeData::Union(union) = context.store().type_payload(resolved).unwrap().data()
                else {
                    panic!("the optional parameter must include undefined")
                };
                let undefined = context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .undefined_type;
                assert_eq!(union.union.types.len(), 2);
                assert!(union.union.types.contains(&base));
                assert!(union.union.types.contains(&undefined));
            } else {
                assert_eq!(resolved, base);
            }
            assert_eq!(
                context.get_return_type_of_signature(signature).unwrap(),
                base
            );
            let before = counts(&context);
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(counts(&context), before);
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(parameter)
                    .unwrap()
                    .resolved_type,
                Some(resolved)
            );
            assert_eq!(
                context.get_return_type_of_signature(signature).unwrap(),
                base
            );
            assert!(context.diagnostics().is_empty());
        }
    }
}

#[test]
fn generic_alias_return_queries_keep_the_same_identity_in_either_query_order() {
    for before in [false, true] {
        for annotation in ["Identity<T>", "(Identity<T>)"] {
            let parsed = parse_source_file(&format!(
                "type Identity<Value> = Value; declare function make<T>(): {annotation};"
            ));
            let mut context = context(&parsed);
            let (function, annotation) = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::FunctionDeclaration(function) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), FILE, node),
                        NodeRef::new(parsed.arena.id(), FILE, function.type_?),
                    ))
                })
                .unwrap();
            let early = before.then(|| context.get_type_from_type_node(annotation).unwrap());
            context.check_source_file(FILE).unwrap();
            let resolved = context.get_type_from_type_node(annotation).unwrap();
            if let Some(early) = early {
                assert_eq!(early, resolved);
            }
            let owner = context.file(FILE).unwrap().1.symbol(function).unwrap();
            let callable = context
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type
                .unwrap();
            let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data()
            else {
                panic!("the function must have its source callable type")
            };
            let signature = object.structured.signatures.as_ref().unwrap()[0];
            let before = counts(&context);
            assert_eq!(
                context.get_return_type_of_signature(signature).unwrap(),
                resolved
            );
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(counts(&context), before);
            assert!(context.diagnostics().is_empty());
        }
    }
}

#[test]
fn unsupported_alias_dependencies_do_not_publish_an_earlier_callable() {
    let parsed = parse_source_file(concat!(
        "type Identity<T> = T; type Broken<T> = Missing<T>; ",
        "declare function first<T>(value: Identity<T>): Identity<T>; ",
        "declare function later<T>(value: Broken<T>): Broken<T>;",
    ));
    let mut context = context(&parsed);
    assert!(context.check_source_file(FILE).is_err());
    for (node, record) in parsed.arena.iter() {
        if record.kind != SyntaxKind::FunctionDeclaration {
            continue;
        }
        let owner = context
            .file(FILE)
            .unwrap()
            .1
            .symbol(NodeRef::new(parsed.arena.id(), FILE, node))
            .unwrap();
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(
            context
                .store()
                .signature_links(NodeRef::new(parsed.arena.id(), FILE, node))
                .is_none()
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // One source check proves the full published alias and callable.
fn property_object_alias_parameter_publishes_exact_callable_and_replays() {
    let parsed = parse_source_file(concat!(
        "type Alias<T> = { value: T }; ",
        "declare function make<T>(value: Alias<T>): T;",
    ));
    let mut context = context(&parsed);
    let result = context.check_source_file(FILE);
    assert_eq!(result, Ok(()));
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let (alias_declaration, alias_parameter_node, literal) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            Some((
                node_ref(node),
                node_ref(alias.type_parameters.as_ref()?.nodes[0]),
                node_ref(alias.type_),
            ))
        })
        .unwrap();
    let (declaration, type_parameter_node, parameter_node, return_annotation) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            Some((
                node_ref(node),
                node_ref(function.type_parameters.as_ref()?.nodes[0]),
                node_ref(function.parameters.nodes[0]),
                node_ref(function.type_?),
            ))
        })
        .unwrap();
    let NodeData::ParameterDeclaration(parameter) =
        &parsed.arena.get(parameter_node.node).unwrap().data
    else {
        unreachable!()
    };
    let parameter_annotation = node_ref(parameter.type_.unwrap());
    let [
        alias_owner,
        alias_parameter_owner,
        source_symbol,
        owner,
        type_parameter_owner,
        parameter,
    ] = [
        alias_declaration,
        alias_parameter_node,
        literal,
        declaration,
        type_parameter_node,
        parameter_node,
    ]
    .map(|node| context.file(FILE).unwrap().1.symbol(node).unwrap());
    let signature = context
        .store()
        .signature_links(declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let callable = context
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    let TypeData::Object(callable_data) = context.store().type_payload(callable).unwrap().data()
    else {
        panic!("make must publish its callable object")
    };
    assert_eq!(callable_data.structured.call_signature_count, 1);
    assert_eq!(
        callable_data.structured.signatures.as_deref(),
        Some([signature].as_slice())
    );
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.parameters(), &[parameter]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.type_parameters().len(), 1);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    let function_parameter = record.type_parameters()[0];
    assert_eq!(record.resolved_return_type(), Some(function_parameter));
    assert_eq!(
        context
            .store()
            .type_payload(function_parameter)
            .unwrap()
            .symbol(),
        Some(type_parameter_owner)
    );
    assert_eq!(
        context
            .store()
            .declared_type_links(type_parameter_owner)
            .unwrap()
            .declared_type,
        Some(function_parameter)
    );
    let instance = context
        .store()
        .value_symbol_links(parameter)
        .unwrap()
        .resolved_type
        .unwrap();
    let links = context.store().type_alias_links(alias_owner).unwrap();
    let target = links.declared_type.unwrap();
    let alias_parameters = links.type_parameters.as_deref().unwrap();
    assert_eq!(alias_parameters.len(), 1);
    let alias_parameter = alias_parameters[0];
    assert_ne!(alias_parameter, function_parameter);
    assert_ne!(target, instance);
    assert_ne!(source_symbol, alias_owner);
    assert_eq!(
        context
            .store()
            .type_payload(alias_parameter)
            .unwrap()
            .symbol(),
        Some(alias_parameter_owner)
    );
    assert_eq!(
        context
            .store()
            .declared_type_links(alias_parameter_owner)
            .unwrap()
            .declared_type,
        Some(alias_parameter)
    );
    let instance_record = context.store().type_payload(instance).unwrap();
    assert_eq!(instance_record.symbol(), Some(source_symbol));
    let TypeData::Object(instance_data) = instance_record.data() else {
        panic!("Alias<make.T> must be an instantiated object")
    };
    assert_eq!(instance_data.target, Some(target));
    let mapper = instance_data.mapper.unwrap();
    assert_eq!(
        context.store().mapper_kind(mapper),
        Some(ts_checker::semantic::TypeMapperKind::Simple)
    );
    assert_eq!(
        context.store().map_type(mapper, alias_parameter),
        Some(function_parameter)
    );
    let metadata = context
        .store()
        .type_alias(instance_record.alias().unwrap())
        .unwrap();
    assert_eq!(metadata.symbol(), Some(alias_owner));
    assert_eq!(
        metadata.type_arguments(),
        Some([function_parameter].as_slice())
    );
    let target_record = context.store().type_payload(target).unwrap();
    assert_eq!(target_record.symbol(), Some(source_symbol));
    let target_alias = context
        .store()
        .type_alias(target_record.alias().unwrap())
        .unwrap();
    assert_eq!(target_alias.symbol(), Some(alias_owner));
    assert_eq!(
        target_alias.type_arguments(),
        Some([alias_parameter].as_slice())
    );
    let TypeData::Object(target_data) = target_record.data() else {
        panic!("the original alias must retain its type-literal object")
    };
    assert_eq!(target_data.target, None);
    assert_eq!(target_data.mapper, None);
    assert_eq!(
        context
            .store()
            .type_node_links(literal)
            .unwrap()
            .resolved_type,
        Some(target)
    );
    let requests = links.instantiations.as_ref().unwrap();
    assert!(requests.values().any(|type_| *type_ == target));
    assert!(requests.values().any(|type_| *type_ == instance));
    let ts_checker::semantic::type_records::TypeCacheState::Allocated(instantiations) =
        &target_data.instantiations
    else {
        panic!("the original object must own its canonical instantiation cache")
    };
    assert!(instantiations.values().any(|type_| *type_ == instance));

    let query_nodes = [parameter_annotation, return_annotation];
    let query_links = query_nodes.map(|node| context.store().type_node_links(node).cloned());
    for (links, expected) in query_links.iter().zip([instance, function_parameter]) {
        assert_eq!(
            links.as_ref().and_then(|links| links.resolved_type),
            Some(expected)
        );
    }
    let query_counts = (
        counts(&context),
        context.store().type_alias_len(),
        context.store().symbol_store().symbol_table_len(),
    );
    assert_eq!(
        context.get_type_from_type_node(parameter_annotation),
        Ok(instance)
    );
    assert_eq!(
        context.get_type_from_type_node(return_annotation),
        Ok(function_parameter)
    );
    assert_eq!(
        context.get_return_type_of_signature(signature),
        Ok(function_parameter)
    );
    assert_eq!(
        (
            counts(&context),
            context.store().type_alias_len(),
            context.store().symbol_store().symbol_table_len()
        ),
        query_counts
    );
    assert_eq!(
        query_nodes.map(|node| context.store().type_node_links(node).cloned()),
        query_links
    );
    let state = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        let signature = store.signature(signature).unwrap();
        (
            (
                counts(context),
                store.type_alias_len(),
                store.symbol_store().symbol_table_len(),
            ),
            store.type_alias_links(alias_owner).cloned(),
            [target, instance, callable].map(|type_| {
                let record = store.type_payload(type_).unwrap();
                let TypeData::Object(object) = record.data() else {
                    panic!("published object identities must remain objects")
                };
                (
                    record.flags(),
                    record.object_flags(),
                    record.symbol(),
                    record.alias(),
                    object.clone(),
                )
            }),
            [owner, parameter].map(|symbol| store.value_symbol_links(symbol).cloned()),
            [alias_parameter_owner, type_parameter_owner]
                .map(|symbol| store.declared_type_links(symbol).cloned()),
            [
                literal,
                alias_parameter_node,
                type_parameter_node,
                parameter_annotation,
                return_annotation,
            ]
            .map(|node| store.type_node_links(node).cloned()),
            store.signature_links(declaration).cloned(),
            (
                signature.declaration(),
                signature.parameters().to_vec(),
                signature.type_parameters().to_vec(),
                signature.min_argument_count(),
                signature.target(),
                signature.mapper(),
                signature.resolved_return_type(),
            ),
            context.diagnostics().clone(),
        )
    };
    let before = state(&context);
    for forced in [false, true] {
        if forced {
            context.recheck_source_file(FILE).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        assert_eq!(
            context.get_type_from_type_node(parameter_annotation),
            Ok(instance)
        );
        assert_eq!(
            context.get_type_from_type_node(return_annotation),
            Ok(function_parameter)
        );
        assert_eq!(
            context.get_return_type_of_signature(signature),
            Ok(function_parameter)
        );
        assert_eq!(state(&context), before);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn nested_generic_alias_parameters_keep_canonical_identities_in_either_query_order() {
    let source = "type Alias<T> = T; interface Box<T> { value: T } declare function f<T>(value: Box<Alias<T>>): T;";
    for annotation_first in [false, true] {
        let parsed = parse_source_file(source);
        let nodes = NestedAliasNodes::new(&parsed);
        let mut context = context(&parsed);
        let early = annotation_first.then(|| {
            context
                .get_type_from_type_node(nodes.outer_annotation)
                .unwrap()
        });
        context.check_source_file(FILE).unwrap();
        let identities = nested_alias_identities(&mut context, &nodes);
        if let Some(early) = early {
            assert_eq!(early, identities.parameter_type);
        }
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );

        let before = counts(&context);
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(nested_alias_identities(&mut context, &nodes), identities);
            assert_eq!(counts(&context), before);
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
        }
    }
}

struct NestedAliasNodes {
    declarations: [NodeRef; 3],
    type_parameters: [NodeRef; 3],
    parameter: NodeRef,
    outer_annotation: NodeRef,
    inner_annotation: NodeRef,
    return_annotation: NodeRef,
    alias_body: NodeRef,
}

impl NestedAliasNodes {
    fn new(parsed: &ParseResult) -> Self {
        let node = |id| NodeRef::new(parsed.arena.id(), FILE, id);
        let declarations = [
            SyntaxKind::FunctionDeclaration,
            SyntaxKind::TypeAliasDeclaration,
            SyntaxKind::InterfaceDeclaration,
        ]
        .map(|kind| {
            parsed
                .arena
                .iter()
                .find_map(|(id, record)| (record.kind == kind).then_some(node(id)))
                .unwrap()
        });
        let [function, alias, interface] = declarations;
        let NodeData::FunctionDeclaration(function) =
            &parsed.arena.get(function.node).unwrap().data
        else {
            panic!("expected the function declaration")
        };
        let NodeData::TypeAliasDeclaration(alias) = &parsed.arena.get(alias.node).unwrap().data
        else {
            panic!("expected the alias declaration")
        };
        let NodeData::InterfaceDeclaration(interface) =
            &parsed.arena.get(interface.node).unwrap().data
        else {
            panic!("expected the interface declaration")
        };
        let type_parameters = [
            function.type_parameters.as_ref().unwrap(),
            alias.type_parameters.as_ref().unwrap(),
            interface.type_parameters.as_ref().unwrap(),
        ]
        .map(|parameters| {
            assert_eq!(parameters.nodes.len(), 1);
            node(parameters.nodes[0])
        });
        assert_eq!(function.parameters.nodes.len(), 1);
        let parameter = node(function.parameters.nodes[0]);
        let NodeData::ParameterDeclaration(parameter_data) =
            &parsed.arena.get(parameter.node).unwrap().data
        else {
            panic!("expected the function parameter")
        };
        let outer_annotation = node(parameter_data.type_.unwrap());
        let NodeData::TypeReferenceNode(reference) =
            &parsed.arena.get(outer_annotation.node).unwrap().data
        else {
            panic!("expected the Box type reference")
        };
        let arguments = reference.type_arguments.as_ref().unwrap();
        assert_eq!(arguments.nodes.len(), 1);
        Self {
            declarations,
            type_parameters,
            parameter,
            outer_annotation,
            inner_annotation: node(arguments.nodes[0]),
            return_annotation: node(function.type_.unwrap()),
            alias_body: node(alias.type_),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
struct NestedAliasIdentities {
    callable: TypeId,
    signature: SignatureId,
    parameter: SemanticSymbolId,
    parameter_type: TypeId,
    type_parameters: [TypeId; 3],
    box_target: TypeId,
    box_this: TypeId,
}

fn nested_alias_type_parameters(
    context: &CanonicalCheckerContext<'_>,
    nodes: &NestedAliasNodes,
) -> [TypeId; 3] {
    let bound = context.file(FILE).unwrap().1;
    let symbols = nodes
        .type_parameters
        .map(|node| bound.symbol(node).unwrap());
    assert_ne!(symbols[0], symbols[1]);
    assert_ne!(symbols[0], symbols[2]);
    assert_ne!(symbols[1], symbols[2]);
    let types = symbols.map(|symbol| {
        let type_ = context
            .store()
            .declared_type_links(symbol)
            .unwrap()
            .declared_type
            .unwrap();
        let record = context.store().type_payload(type_).unwrap();
        assert!(matches!(record.data(), TypeData::TypeParameter(_)));
        assert_eq!(record.symbol(), Some(symbol));
        type_
    });
    assert_ne!(types[0], types[1]);
    assert_ne!(types[0], types[2]);
    assert_ne!(types[1], types[2]);
    for (symbol, node) in symbols.into_iter().zip(nodes.type_parameters) {
        assert_eq!(
            context.store().symbol(symbol).unwrap().declarations(),
            Some(&[node][..])
        );
    }
    let alias_symbol = bound.symbol(nodes.declarations[1]).unwrap();
    let alias = context.store().type_alias_links(alias_symbol).unwrap();
    assert_eq!(alias.type_parameters.as_deref(), Some(&[types[1]][..]));
    assert_eq!(alias.declared_type, Some(types[1]));
    types
}

#[allow(clippy::too_many_lines)] // One snapshot checks each owner and its parameter identities.
fn nested_alias_identities(
    context: &mut CanonicalCheckerContext<'_>,
    nodes: &NestedAliasNodes,
) -> NestedAliasIdentities {
    let [function_symbol, _, box_symbol] = nodes
        .declarations
        .map(|node| context.file(FILE).unwrap().1.symbol(node).unwrap());
    let parameter = context
        .file(FILE)
        .unwrap()
        .1
        .symbol(nodes.parameter)
        .unwrap();
    let parameter_type = context
        .get_type_from_type_node(nodes.outer_annotation)
        .unwrap();
    let type_parameters = nested_alias_type_parameters(context, nodes);
    let [function_parameter, alias_parameter, box_parameter] = type_parameters;
    assert_eq!(
        context
            .get_type_from_type_node(nodes.inner_annotation)
            .unwrap(),
        function_parameter
    );
    assert_eq!(
        context
            .get_type_from_type_node(nodes.return_annotation)
            .unwrap(),
        function_parameter
    );
    assert_eq!(
        context.get_type_from_type_node(nodes.alias_body).unwrap(),
        alias_parameter
    );
    let callable = context
        .store()
        .value_symbol_links(function_symbol)
        .unwrap()
        .resolved_type
        .unwrap();
    let callable_record = context.store().type_payload(callable).unwrap();
    assert_eq!(callable_record.symbol(), Some(function_symbol));
    let TypeData::Object(object) = callable_record.data() else {
        panic!("the function must retain a callable object")
    };
    let signatures = object.structured.signatures.as_ref().unwrap();
    assert_eq!(signatures.len(), 1);
    let signature = signatures[0];
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(nodes.declarations[0]));
    assert_eq!(record.type_parameters(), &[function_parameter]);
    assert_eq!(record.parameters(), &[parameter]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(
        context.get_return_type_of_signature(signature).unwrap(),
        function_parameter
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(parameter)
            .unwrap()
            .resolved_type,
        Some(parameter_type)
    );
    let box_target = context
        .store()
        .declared_type_links(box_symbol)
        .unwrap()
        .declared_type
        .unwrap();
    let target = context.store().type_payload(box_target).unwrap();
    assert_eq!(target.symbol(), Some(box_symbol));
    let TypeData::Interface(interface) = target.data() else {
        panic!("Box must retain its declared interface target")
    };
    let box_this = interface.this_type.expect("Box must retain its this type");
    assert_eq!(interface.outer_type_parameter_count, 0);
    assert_eq!(
        interface.all_type_parameters.as_deref(),
        Some(&[box_parameter, box_this][..])
    );
    assert_eq!(
        interface.reference.resolved_type_arguments.as_deref(),
        Some(&[box_parameter][..])
    );
    assert_eq!(interface.reference.object.target, Some(box_target));
    let this_record = context.store().type_payload(box_this).unwrap();
    assert_eq!(this_record.symbol(), Some(box_symbol));
    let TypeData::TypeParameter(this_data) = this_record.data() else {
        panic!("Box's this type must be a type parameter")
    };
    assert!(this_data.is_this_type);
    assert_eq!(this_data.constraint, Some(box_target));
    assert!(this_data.target.is_none());
    assert!(this_data.mapper.is_none());
    assert!(!type_parameters.contains(&box_this));
    let TypeData::TypeReference(reference) =
        context.store().type_payload(parameter_type).unwrap().data()
    else {
        panic!("the parameter must be a reference to Box")
    };
    assert_eq!(reference.object.target, Some(box_target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[function_parameter][..])
    );
    NestedAliasIdentities {
        callable,
        signature,
        parameter,
        parameter_type,
        type_parameters,
        box_target,
        box_this,
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the two parameter owners, complete signature graph, and replay together.
fn generic_identity_alias_arrow_keeps_distinct_parameters_and_replays() {
    let parsed =
        parse_source_file("type Alias<T> = T; const f = <T>(value: Alias<T>): Alias<T> => value;");
    let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let (alias_declaration, alias) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            Some((node_ref(node), alias))
        })
        .unwrap();
    let [alias_parameter] = alias.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected the alias's one type parameter")
    };
    let alias_parameter = node_ref(*alias_parameter);
    let alias_name = node_ref(alias.name);
    let alias_rhs = node_ref(alias.type_);
    let (arrow_declaration, arrow) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ArrowFunction(arrow) = &record.data else {
                return None;
            };
            Some((node_ref(node), arrow))
        })
        .unwrap();
    let [arrow_parameter] = arrow.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected the arrow's one type parameter")
    };
    let arrow_parameter = node_ref(*arrow_parameter);
    let [parameter] = arrow.parameters.nodes.as_slice() else {
        panic!("expected one value parameter")
    };
    let parameter = node_ref(*parameter);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("expected the typed value parameter")
    };
    let parameter_name = node_ref(parameter_data.name);
    let parameter_annotation = node_ref(parameter_data.type_.unwrap());
    let return_annotation = node_ref(arrow.type_.unwrap());
    let body = node_ref(arrow.body);
    let variable = node_ref(
        parsed
            .arena
            .get(arrow_declaration.node)
            .unwrap()
            .parent
            .unwrap(),
    );
    let NodeData::VariableDeclaration(variable_data) =
        &parsed.arena.get(variable.node).unwrap().data
    else {
        panic!("the arrow must remain the variable initializer")
    };
    assert_eq!(variable_data.initializer, Some(arrow_declaration.node));
    let variable_name = node_ref(variable_data.name);
    let parameter_names = [alias_parameter, arrow_parameter].map(|node| {
        let NodeData::TypeParameterDeclaration(parameter) =
            &parsed.arena.get(node.node).unwrap().data
        else {
            panic!("expected a type parameter declaration")
        };
        node_ref(parameter.name)
    });
    let arguments = [parameter_annotation, return_annotation].map(|node| {
        let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(node.node).unwrap().data
        else {
            panic!("expected the Alias<T> annotation")
        };
        let [argument] = reference.type_arguments.as_ref().unwrap().nodes.as_slice() else {
            panic!("expected the arrow's one type argument")
        };
        node_ref(*argument)
    });
    let binding = |context: &CanonicalCheckerContext<'_>, node| {
        let symbol = context.file(FILE).unwrap().1.symbol(node).unwrap();
        context.store().get_merged_symbol(symbol).unwrap()
    };
    let checked = |context: &CanonicalCheckerContext<'_>| {
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .is_some_and(|links| links.type_checked)
    };
    let nodes = parsed
        .arena
        .iter()
        .map(|(node, _)| node_ref(node))
        .collect::<Vec<_>>();
    let assert_state = |context: &mut CanonicalCheckerContext<'_>| {
        assert!(checked(context));
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let alias_symbol = binding(context, alias_declaration);
        let alias_parameter_symbol = binding(context, alias_parameter);
        let arrow_parameter_symbol = binding(context, arrow_parameter);
        let owner = binding(context, arrow_declaration);
        let variable_symbol = binding(context, variable);
        let value_symbol = binding(context, parameter);
        assert_ne!(alias_parameter_symbol, arrow_parameter_symbol);
        assert_ne!(owner, variable_symbol);
        assert_eq!(
            context.store().symbol(alias_symbol).unwrap().flags(),
            SymbolFlags::TYPE_ALIAS
        );
        for (symbol, declaration, flags) in [
            (owner, arrow_declaration, SymbolFlags::FUNCTION),
            (
                variable_symbol,
                variable,
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
            ),
            (
                alias_parameter_symbol,
                alias_parameter,
                SymbolFlags::TYPE_PARAMETER,
            ),
            (
                arrow_parameter_symbol,
                arrow_parameter,
                SymbolFlags::TYPE_PARAMETER,
            ),
        ] {
            let record = context.store().symbol(symbol).unwrap();
            assert_eq!(record.flags(), flags);
            assert_eq!(record.declarations(), Some(&[declaration][..]));
        }
        assert_eq!(
            context.store().symbol(owner).unwrap().value_declaration(),
            Some(arrow_declaration)
        );
        assert_eq!(
            context
                .store()
                .symbol(variable_symbol)
                .unwrap()
                .value_declaration(),
            Some(variable)
        );
        let alias_t = context
            .store()
            .declared_type_links(alias_parameter_symbol)
            .unwrap()
            .declared_type
            .unwrap();
        let arrow_t = context
            .store()
            .declared_type_links(arrow_parameter_symbol)
            .unwrap()
            .declared_type
            .unwrap();
        assert_ne!(alias_t, arrow_t);
        for (type_, symbol) in [
            (alias_t, alias_parameter_symbol),
            (arrow_t, arrow_parameter_symbol),
        ] {
            let record = context.store().type_payload(type_).unwrap();
            assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
            assert_eq!(record.symbol(), Some(symbol));
            let TypeData::TypeParameter(parameter) = record.data() else {
                panic!("expected the binder-owned parameter")
            };
            assert_eq!(parameter.target, None);
            assert_eq!(parameter.mapper, None);
        }
        let alias_links = context
            .store()
            .type_alias_links(alias_symbol)
            .cloned()
            .unwrap();
        assert_eq!(alias_links.declared_type, Some(alias_t));
        assert_eq!(alias_links.type_parameters.as_deref(), Some(&[alias_t][..]));
        // One identity seed and one shared Alias<arrow T> result. Cache keys stay opaque.
        let mut cached_alias_types = alias_links
            .instantiations
            .as_ref()
            .unwrap()
            .values()
            .copied()
            .collect::<Vec<_>>();
        cached_alias_types.sort_unstable();
        let mut expected_alias_types = [alias_t, arrow_t];
        expected_alias_types.sort_unstable();
        assert_eq!(cached_alias_types, expected_alias_types);
        let callable = context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            context
                .store()
                .value_symbol_links(variable_symbol)
                .unwrap()
                .resolved_type,
            Some(callable)
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(value_symbol)
                .unwrap()
                .resolved_type,
            Some(arrow_t)
        );
        let signature = context
            .store()
            .signature_links(arrow_declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let record = context.store().type_payload(callable).unwrap();
        assert_eq!(record.flags(), TypeFlags::OBJECT);
        assert_eq!(
            record.object_flags(),
            ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        );
        assert_eq!(record.symbol(), Some(owner));
        let TypeData::Object(object) = record.data() else {
            panic!("expected the arrow's callable object")
        };
        assert_eq!(
            object.structured.signatures.as_deref(),
            Some(&[signature][..])
        );
        assert_eq!(object.structured.call_signature_count, 1);
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.declaration(), Some(arrow_declaration));
        assert_eq!(record.type_parameters(), [arrow_t]);
        assert_eq!(record.parameters(), [value_symbol]);
        assert_eq!(record.resolved_return_type(), Some(arrow_t));
        assert_eq!(record.target(), None);
        assert_eq!(record.mapper(), None);
        let reference_results = [
            (alias_rhs, alias_t, alias_parameter_symbol),
            (parameter_annotation, arrow_t, alias_symbol),
            (return_annotation, arrow_t, alias_symbol),
            (arguments[0], arrow_t, arrow_parameter_symbol),
            (arguments[1], arrow_t, arrow_parameter_symbol),
        ];
        // Check publication before public queries can fill any missing cache.
        for (node, type_, symbol) in reference_results {
            assert_eq!(
                context.store().type_node_links(node).unwrap().resolved_type,
                Some(type_)
            );
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(node)
                    .unwrap()
                    .resolved_symbol,
                Some(symbol)
            );
        }
        assert_eq!(context.store().type_node_links(arrow_declaration), None);
        assert_eq!(
            context.store().type_node_links(body).unwrap().resolved_type,
            Some(arrow_t)
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(body)
                .unwrap()
                .resolved_symbol,
            Some(value_symbol)
        );
        let cache_state = |context: &CanonicalCheckerContext<'_>| {
            let record = context.store().signature(signature).unwrap();
            (
                context.store().type_alias_links(alias_symbol).cloned(),
                (
                    record.declaration(),
                    record.type_parameters().to_vec(),
                    record.parameters().to_vec(),
                    record.resolved_return_type(),
                    record.target(),
                    record.mapper(),
                ),
                nodes
                    .iter()
                    .map(|&node| {
                        (
                            node,
                            context.store().node_links(node).cloned(),
                            context.store().type_node_links(node).cloned(),
                            context.store().symbol_node_links(node).cloned(),
                            context.store().signature_links(node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                [
                    alias_symbol,
                    alias_parameter_symbol,
                    arrow_parameter_symbol,
                    owner,
                    variable_symbol,
                    value_symbol,
                ]
                .map(|symbol| {
                    (
                        symbol,
                        context.store().value_symbol_links(symbol).cloned(),
                        context.store().declared_type_links(symbol).cloned(),
                    )
                }),
                context
                    .store()
                    .source_file_links(context.source_file(FILE).unwrap())
                    .cloned(),
            )
        };
        let cached = cache_state(context);
        let before = counts(context);
        assert_eq!(
            context.get_declared_type_of_symbol(alias_symbol).unwrap(),
            alias_t
        );
        for (node, type_, symbol) in reference_results {
            assert_eq!(context.get_type_from_type_node(node).unwrap(), type_);
            assert_eq!(context.get_type_at_location(node).unwrap(), type_);
            let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(node.node).unwrap().data
            else {
                panic!("expected the retained reference syntax")
            };
            assert_eq!(
                context
                    .get_symbol_at_location(node_ref(reference.type_name))
                    .unwrap(),
                Some(symbol)
            );
        }
        for (node, type_, symbol) in [
            (alias_name, alias_t, alias_symbol),
            (parameter_names[0], alias_t, alias_parameter_symbol),
            (parameter_names[1], arrow_t, arrow_parameter_symbol),
            (parameter_name, arrow_t, value_symbol),
            (body, arrow_t, value_symbol),
            (variable_name, callable, variable_symbol),
        ] {
            assert_eq!(context.get_type_at_location(node).unwrap(), type_);
            assert_eq!(context.get_symbol_at_location(node).unwrap(), Some(symbol));
        }
        assert_eq!(
            context.get_type_at_location(arrow_declaration).unwrap(),
            callable
        );
        assert_eq!(
            context.get_symbol_at_location(arrow_declaration).unwrap(),
            None
        );
        assert_eq!(
            context.get_return_type_of_signature(signature).unwrap(),
            arrow_t
        );
        assert_eq!(cache_state(context), cached);
        assert_eq!(counts(context), before);
        assert!(context.diagnostics().is_empty());
        (alias_t, arrow_t, callable, signature, cached)
    };
    for first in [None, Some(parameter_annotation), Some(return_annotation)] {
        let mut context = context(&parsed);
        let owner = binding(&context, arrow_declaration);
        let variable_symbol = binding(&context, variable);
        assert!(!checked(&context));
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(
            context
                .store()
                .value_symbol_links(variable_symbol)
                .is_none()
        );
        assert!(context.store().signature_links(arrow_declaration).is_none());
        let initial_signatures = context.store().signature_len();
        let early = first.map(|node| context.get_type_from_type_node(node).unwrap());
        assert!(!checked(&context));
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(
            context
                .store()
                .value_symbol_links(variable_symbol)
                .is_none()
        );
        assert!(context.store().signature_links(arrow_declaration).is_none());
        assert_eq!(context.store().signature_len(), initial_signatures);
        assert!(context.diagnostics().is_empty());
        context.check_source_file(FILE).unwrap();
        let cold = assert_state(&mut context);
        if let Some(early) = early {
            assert_eq!(early, cold.1);
        }
        let before = counts(&context);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(assert_state(&mut context), cold);
        assert_eq!(counts(&context), before);
    }
}

#[test]
fn generic_alias_source_boundary_keeps_recursive_and_const_forms_unsupported() {
    for source in [
        "interface Array<T> {} interface ReadonlyArray<T> {} type Alias<T> = T[]; declare function f<T>(value: Alias<T>): void;",
        "type Alias<T> = Alias<T>[]; declare function f<T>(value: Alias<T>): void;",
        "type First<T> = Second<T>; type Second<T> = First<T>[]; declare function f<T>(value: First<T>): void;",
        "type Alias<T> = T; declare function f<const T>(value: Alias<T>): void;",
        "type Alias<T> = typeof f; declare function f<T>(value: Alias<T>): void;",
        "namespace N { export type Again<T> = Alias<T>; } type Alias<T> = N.Again<T>; declare function f<T>(value: Alias<T>): void;",
    ] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed);
        let before = counts(&context);
        assert!(context.check_source_file(FILE).is_err(), "{source}");
        assert_eq!(counts(&context), before, "{source}");
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Both declarations and wrapper forms must retain separate owners.
fn return_only_property_object_alias_publishes_distinct_callables_and_replays() {
    for annotation in ["Unsupported<T>", "(Unsupported<T>)"] {
        let parsed = parse_source_file(&format!(
            "type Identity<Value> = Value; type Unsupported<Value> = {{ value: Value }}; \
             declare function first<T>(value: Identity<T>): Identity<T>; \
             declare function later<T>(): {annotation};"
        ));
        let mut context = context(&parsed);
        let result = context.check_source_file(FILE);
        assert_eq!(result, Ok(()), "{annotation}");
        assert!(
            context.diagnostics().is_empty(),
            "{annotation}: {:?}",
            context.diagnostics()
        );
        let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
        let alias_parts = |expected: &str| {
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                        return None;
                    };
                    (name.text == expected).then(|| {
                        (
                            node_ref(node),
                            node_ref(alias.type_parameters.as_ref().unwrap().nodes[0]),
                            node_ref(alias.type_),
                        )
                    })
                })
                .unwrap()
        };
        let (identity_declaration, identity_parameter_node, identity_rhs) = alias_parts("Identity");
        let (alias_declaration, alias_parameter_node, literal) = alias_parts("Unsupported");
        let function_parts = |expected: &str| {
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::FunctionDeclaration(function) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(function.name?)?.data else {
                        return None;
                    };
                    (name.text == expected).then(|| {
                        (
                            node_ref(node),
                            node_ref(function.type_parameters.as_ref().unwrap().nodes[0]),
                            function
                                .parameters
                                .nodes
                                .iter()
                                .copied()
                                .map(node_ref)
                                .collect::<Vec<_>>(),
                            node_ref(function.type_.unwrap()),
                        )
                    })
                })
                .unwrap()
        };
        let (first_declaration, first_type_parameter_node, first_parameters, first_return) =
            function_parts("first");
        let (later_declaration, later_type_parameter_node, later_parameters, later_return) =
            function_parts("later");
        let [first_parameter_node] = first_parameters.as_slice() else {
            panic!("first must retain its single value parameter")
        };
        assert!(later_parameters.is_empty());
        let NodeData::ParameterDeclaration(parameter) =
            &parsed.arena.get(first_parameter_node.node).unwrap().data
        else {
            unreachable!()
        };
        let first_parameter_annotation = node_ref(parameter.type_.unwrap());
        let mut later_reference = later_return;
        while let NodeData::ParenthesizedTypeNode(wrapper) =
            &parsed.arena.get(later_reference.node).unwrap().data
        {
            later_reference = node_ref(wrapper.type_);
        }
        assert!(matches!(
            parsed.arena.get(later_reference.node).unwrap().data,
            NodeData::TypeReferenceNode(_)
        ));
        let bound_symbol = |node| context.file(FILE).unwrap().1.symbol(node).unwrap();
        let declarations = [first_declaration, later_declaration];
        let owners = declarations.map(bound_symbol);
        let parameter_owners =
            [first_type_parameter_node, later_type_parameter_node].map(bound_symbol);
        let first_parameter = bound_symbol(*first_parameter_node);
        let alias_owner = bound_symbol(alias_declaration);
        let alias_parameter_owner = bound_symbol(alias_parameter_node);
        let identity_owner = bound_symbol(identity_declaration);
        let identity_parameter_owner = bound_symbol(identity_parameter_node);
        let source_symbol = bound_symbol(literal);
        let signatures = declarations.map(|declaration| {
            context
                .store()
                .signature_links(declaration)
                .unwrap()
                .resolved_signature
                .signature()
                .unwrap()
        });
        let callables = owners.map(|owner| {
            context
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type
                .unwrap()
        });
        assert_ne!(signatures[0], signatures[1]);
        assert_ne!(callables[0], callables[1]);
        for ((declaration, signature), callable) in
            declarations.into_iter().zip(signatures).zip(callables)
        {
            let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data()
            else {
                panic!("each function must publish its own callable object")
            };
            assert_eq!(object.structured.call_signature_count, 1);
            assert_eq!(
                object.structured.signatures.as_deref(),
                Some([signature].as_slice())
            );
            let record = context.store().signature(signature).unwrap();
            assert_eq!(record.declaration(), Some(declaration));
            assert_eq!(record.type_parameters().len(), 1);
            assert_eq!(record.target(), None);
            assert_eq!(record.mapper(), None);
        }
        let first_signature = context.store().signature(signatures[0]).unwrap();
        assert_eq!(first_signature.parameters(), &[first_parameter]);
        assert_eq!(first_signature.min_argument_count(), 1);
        let later_signature = context.store().signature(signatures[1]).unwrap();
        assert!(later_signature.parameters().is_empty());
        assert_eq!(later_signature.min_argument_count(), 0);
        let parameters = signatures.map(|signature| {
            context
                .store()
                .signature(signature)
                .unwrap()
                .type_parameters()[0]
        });
        assert_ne!(parameters[0], parameters[1]);
        for (parameter, owner) in parameters.into_iter().zip(parameter_owners) {
            assert_eq!(
                context.store().type_payload(parameter).unwrap().symbol(),
                Some(owner)
            );
            assert_eq!(
                context
                    .store()
                    .declared_type_links(owner)
                    .unwrap()
                    .declared_type,
                Some(parameter)
            );
        }
        assert_eq!(
            context
                .store()
                .value_symbol_links(first_parameter)
                .unwrap()
                .resolved_type,
            Some(parameters[0])
        );
        let identity_links = context.store().type_alias_links(identity_owner).unwrap();
        let identity_parameter = identity_links.type_parameters.as_ref().unwrap()[0];
        assert_eq!(
            identity_links.type_parameters.as_deref(),
            Some([identity_parameter].as_slice())
        );
        assert_eq!(identity_links.declared_type, Some(identity_parameter));
        assert_eq!(
            context
                .store()
                .type_payload(identity_parameter)
                .unwrap()
                .symbol(),
            Some(identity_parameter_owner)
        );
        let links = context.store().type_alias_links(alias_owner).unwrap();
        let target = links.declared_type.unwrap();
        let alias_parameter = links.type_parameters.as_ref().unwrap()[0];
        assert_eq!(
            links.type_parameters.as_deref(),
            Some([alias_parameter].as_slice())
        );
        assert_eq!(
            context
                .store()
                .type_payload(alias_parameter)
                .unwrap()
                .symbol(),
            Some(alias_parameter_owner)
        );
        assert_eq!(
            context
                .store()
                .declared_type_links(alias_parameter_owner)
                .unwrap()
                .declared_type,
            Some(alias_parameter)
        );
        assert_ne!(identity_parameter, alias_parameter);
        for parameter in parameters {
            assert_ne!(parameter, identity_parameter);
            assert_ne!(parameter, alias_parameter);
        }
        let instance = context
            .store()
            .type_node_links(later_reference)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_ne!(instance, target);
        assert_ne!(instance, parameters[0]);
        assert_ne!(source_symbol, alias_owner);
        let record = context.store().type_payload(instance).unwrap();
        assert_eq!(record.symbol(), Some(source_symbol));
        let TypeData::Object(instance_data) = record.data() else {
            panic!("later must return Unsupported<later.T>, not the template")
        };
        assert_eq!(instance_data.target, Some(target));
        let mapper = instance_data.mapper.unwrap();
        assert_eq!(
            context.store().mapper_kind(mapper),
            Some(ts_checker::semantic::TypeMapperKind::Simple)
        );
        assert_eq!(
            context.store().map_type(mapper, alias_parameter),
            Some(parameters[1])
        );
        let metadata = context.store().type_alias(record.alias().unwrap()).unwrap();
        assert_eq!(metadata.symbol(), Some(alias_owner));
        assert_eq!(metadata.type_arguments(), Some([parameters[1]].as_slice()));
        let target_record = context.store().type_payload(target).unwrap();
        assert_eq!(target_record.symbol(), Some(source_symbol));
        let target_alias = context
            .store()
            .type_alias(target_record.alias().unwrap())
            .unwrap();
        assert_eq!(target_alias.symbol(), Some(alias_owner));
        assert_eq!(
            target_alias.type_arguments(),
            Some([alias_parameter].as_slice())
        );
        let TypeData::Object(target_data) = target_record.data() else {
            panic!("Unsupported must retain its original type-literal object")
        };
        assert_eq!(target_data.target, None);
        assert_eq!(target_data.mapper, None);
        assert_eq!(
            context
                .store()
                .type_node_links(literal)
                .unwrap()
                .resolved_type,
            Some(target)
        );
        let requests = links.instantiations.as_ref().unwrap();
        assert!(requests.values().any(|type_| *type_ == target));
        assert!(requests.values().any(|type_| *type_ == instance));
        let ts_checker::semantic::type_records::TypeCacheState::Allocated(instantiations) =
            &target_data.instantiations
        else {
            panic!("the original object must own its canonical instantiation cache")
        };
        assert!(instantiations.values().any(|type_| *type_ == instance));

        let query_counts = (
            counts(&context),
            context.store().type_alias_len(),
            context.store().symbol_store().symbol_table_len(),
        );
        let queries = [
            (first_parameter_annotation, parameters[0]),
            (first_return, parameters[0]),
            (later_return, instance),
            (later_reference, instance),
        ];
        for (signature, expected) in signatures.into_iter().zip([parameters[0], instance]) {
            assert_eq!(
                context
                    .store()
                    .signature(signature)
                    .unwrap()
                    .resolved_return_type(),
                Some(expected)
            );
        }
        for (node, expected) in [
            (first_parameter_annotation, parameters[0]),
            (first_return, parameters[0]),
            (later_reference, instance),
        ] {
            assert_eq!(
                context
                    .store()
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type),
                Some(expected)
            );
        }
        let query_links = queries.map(|(node, _)| context.store().type_node_links(node).cloned());
        for (node, expected) in queries {
            assert_eq!(
                context.get_type_from_type_node(node),
                Ok(expected),
                "{annotation}"
            );
        }
        assert_eq!(
            context.get_return_type_of_signature(signatures[0]),
            Ok(parameters[0])
        );
        assert_eq!(
            context.get_return_type_of_signature(signatures[1]),
            Ok(instance)
        );
        assert_eq!(
            (
                counts(&context),
                context.store().type_alias_len(),
                context.store().symbol_store().symbol_table_len()
            ),
            query_counts
        );
        assert_eq!(
            queries.map(|(node, _)| context.store().type_node_links(node).cloned()),
            query_links
        );
        let state = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            (
                (
                    counts(context),
                    store.type_alias_len(),
                    store.symbol_store().symbol_table_len(),
                ),
                [identity_owner, alias_owner].map(|owner| store.type_alias_links(owner).cloned()),
                [target, instance, callables[0], callables[1]].map(|type_| {
                    let record = store.type_payload(type_).unwrap();
                    let TypeData::Object(object) = record.data() else {
                        panic!("published object identities must remain objects")
                    };
                    (
                        record.flags(),
                        record.object_flags(),
                        record.symbol(),
                        record.alias(),
                        object.clone(),
                    )
                }),
                [owners[0], owners[1], first_parameter]
                    .map(|owner| store.value_symbol_links(owner).cloned()),
                [
                    identity_parameter_owner,
                    alias_parameter_owner,
                    parameter_owners[0],
                    parameter_owners[1],
                ]
                .map(|owner| store.declared_type_links(owner).cloned()),
                [
                    identity_rhs,
                    literal,
                    identity_parameter_node,
                    alias_parameter_node,
                    first_type_parameter_node,
                    later_type_parameter_node,
                    first_parameter_annotation,
                    first_return,
                    later_return,
                    later_reference,
                ]
                .map(|node| store.type_node_links(node).cloned()),
                declarations.map(|declaration| store.signature_links(declaration).cloned()),
                signatures.map(|signature| {
                    let signature = store.signature(signature).unwrap();
                    (
                        signature.declaration(),
                        signature.parameters().to_vec(),
                        signature.type_parameters().to_vec(),
                        signature.min_argument_count(),
                        signature.target(),
                        signature.mapper(),
                        signature.resolved_return_type(),
                    )
                }),
                context.diagnostics().clone(),
            )
        };
        let before = state(&context);
        for forced in [false, true] {
            if forced {
                context.recheck_source_file(FILE).unwrap();
            } else {
                context.check_source_file(FILE).unwrap();
            }
            for (node, expected) in queries {
                assert_eq!(
                    context.get_type_from_type_node(node),
                    Ok(expected),
                    "{annotation}"
                );
            }
            assert_eq!(
                context.get_return_type_of_signature(signatures[0]),
                Ok(parameters[0])
            );
            assert_eq!(
                context.get_return_type_of_signature(signatures[1]),
                Ok(instance)
            );
            assert_eq!(state(&context), before, "{annotation}");
            assert!(
                context.diagnostics().is_empty(),
                "{annotation}: {:?}",
                context.diagnostics()
            );
        }
    }
}
