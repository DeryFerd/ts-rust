use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    SourceCheckError, TypeData, TypeId, artifact_queries::CanonicalArtifactQueryError,
    signatures::SignatureFlags, type_records::StructuredTypeData,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(19_850);
const LIBRARY_FILE: FileId = FileId::new(19_851);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

const ABSTRACT_SOURCE: &str = concat!(
    "// @target: es2015\n",
    "abstract class AbstractClass {\n",
    "    constructor(str: string, other: AbstractClass) {\n",
    "        this.method(parseInt(str));\n",
    "    }\n",
    "    abstract method(num: number): void;\n",
    "}\n",
);

fn context<'a>(
    parsed: &'a ParseResult,
    library: Option<&'a ParseResult>,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    let mut inputs = Vec::new();
    if let Some(library) = library {
        inputs.push((library, LIBRARY_FILE, "\"/lib/lib.es5.d.ts\"", true));
    }
    inputs.push((parsed, FILE, "\"/project/class-method-display.ts\"", false));
    for (parsed, file, path, library) in &inputs {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                *file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(*path),
                    CanonicalSourceLanguage::TypeScript,
                    *library,
                    *library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, *file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        inputs
            .into_iter()
            .map(|(parsed, file, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            no_implicit_any: true,
            strict_property_initialization: true,
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
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn class_nodes(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let name = class.name?;
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some((node(parsed, id), node(parsed, name)))
        })
        .unwrap()
}

struct Method {
    declaration: NodeRef,
    name: NodeRef,
    parameters: Vec<NodeRef>,
}

fn methods(parsed: &ParseResult, expected: &str) -> Vec<Method> {
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let (name, parameters) = match &record.data {
                NodeData::MethodDeclaration(method) => (method.name, &method.parameters),
                NodeData::MethodSignatureDeclaration(method) => (method.name, &method.parameters),
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then(|| Method {
                declaration: node(parsed, id),
                name: node(parsed, name),
                parameters: parameters
                    .nodes
                    .iter()
                    .map(|&id| node(parsed, id))
                    .collect(),
            })
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|method| {
        parsed
            .arena
            .get(method.declaration.node)
            .unwrap()
            .range
            .start
    });
    assert!(!result.is_empty(), "missing method {expected}");
    result
}

fn accesses(parsed: &ParseResult, expected: &str) -> Vec<(NodeRef, NodeRef)> {
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(access.name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some((node(parsed, id), node(parsed, access.name)))
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|(access, _)| parsed.arena.get(access.node).unwrap().range.start);
    result
}

fn call_of_access(parsed: &ParseResult, access: NodeRef) -> NodeRef {
    let parent = node(
        parsed,
        parsed.arena.get(access.node).unwrap().parent.unwrap(),
    );
    let NodeData::CallExpression(call) = &parsed.arena.get(parent.node).unwrap().data else {
        panic!("the original method access must remain a call")
    };
    assert_eq!(call.expression, access.node);
    parent
}

fn node_text<'a>(source: &'a str, parsed: &ParseResult, location: NodeRef) -> &'a str {
    let range = parsed.arena.get(location.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 8] {
    let store = context.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
        store.properties_type_cache_len(),
    ]
}

fn is_checked(context: &CanonicalCheckerContext<'_>) -> bool {
    context
        .store()
        .source_file_links(context.source_file(FILE).unwrap())
        .is_some_and(|links| links.type_checked)
}

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

fn signatures(context: &CanonicalCheckerContext<'_>, method_type: TypeId) -> Vec<SignatureId> {
    let structured =
        structured_data(context.store().type_payload(method_type).unwrap().data()).unwrap();
    let signatures = structured.signatures.clone().unwrap();
    assert_eq!(structured.call_signature_count, signatures.len());
    signatures
}

fn assert_signature(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    method: &Method,
    signature: SignatureId,
    parameters: &[(&str, TypeId)],
    return_type: TypeId,
) {
    let owner = symbol(context, method.declaration);
    assert_eq!(
        context.get_symbol_at_location(method.name).unwrap(),
        Some(owner)
    );
    let record = context.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::METHOD);
    assert_eq!(method.parameters.len(), parameters.len());
    let parameter_symbols = method
        .parameters
        .iter()
        .map(|&parameter| symbol(context, parameter))
        .collect::<Vec<_>>();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(method.declaration));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert!(record.type_parameters().is_empty());
    assert!(record.this_parameter().is_none());
    assert_eq!(record.parameters(), parameter_symbols);
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(parameters.len()).unwrap()
    );
    assert_eq!(record.resolved_return_type(), Some(return_type));
    assert_eq!(
        context
            .store()
            .signature_links(method.declaration)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(signature)
    );
    for ((&declaration, &parameter), &(name, expected_type)) in method
        .parameters
        .iter()
        .zip(&parameter_symbols)
        .zip(parameters)
    {
        let record = context.store().symbol(parameter).unwrap();
        assert_eq!(record.name().as_utf8(), Some(name));
        assert_eq!(record.declarations(), Some(&[declaration][..]));
        assert_eq!(record.value_declaration(), Some(declaration));
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type,
            Some(expected_type)
        );
        let NodeData::ParameterDeclaration(parameter) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(
            context
                .get_type_at_location(node(parsed, parameter.name))
                .unwrap(),
            expected_type
        );
    }
}

#[allow(clippy::too_many_lines)] // Compare source caches around both formatter entry points.
fn assert_display_read_only(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    displays: &[(TypeId, NodeRef, &str)],
) {
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        let nodes = parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let location = node(parsed, id);
                (
                    location,
                    store.node_links(location).cloned(),
                    store.type_node_links(location).cloned(),
                    store.symbol_node_links(location).cloned(),
                    store.signature_links(location).cloned(),
                )
            })
            .collect::<Vec<_>>();
        let values = parsed
            .arena
            .iter()
            .filter_map(|(id, _)| {
                let raw = context.file(FILE)?.1.symbol(node(parsed, id))?;
                let symbol = store.get_merged_symbol(raw)?;
                Some((
                    symbol,
                    store.value_symbol_links(symbol).cloned(),
                    store.declared_type_links(symbol).cloned(),
                ))
            })
            .collect::<Vec<_>>();
        let signatures = nodes
            .iter()
            .filter_map(|(_, _, _, _, links)| {
                let id = links.as_ref()?.resolved_signature.signature()?;
                let record = store.signature(id)?;
                Some((
                    id,
                    record.declaration(),
                    record.flags(),
                    record.parameters().to_vec(),
                    record.min_argument_count(),
                    record.resolved_min_argument_count(),
                    record.resolved_return_type(),
                ))
            })
            .collect::<Vec<_>>();
        let types = values
            .iter()
            .flat_map(|(_, value, declared)| {
                value
                    .as_ref()
                    .and_then(|links| links.resolved_type)
                    .into_iter()
                    .chain(declared.as_ref().and_then(|links| links.declared_type))
            })
            .map(|type_| {
                let record = store.type_payload(type_).unwrap();
                let members = structured_data(record.data()).map(|structured| {
                    (
                        structured.members,
                        structured.properties.clone(),
                        structured.signatures.clone(),
                        structured.call_signature_count,
                        structured.index_infos.clone(),
                    )
                });
                (
                    type_,
                    record.flags(),
                    record.object_flags(),
                    record.symbol(),
                    members,
                )
            })
            .collect::<Vec<_>>();
        (
            counts(context),
            store.relation_state_snapshot(),
            context.diagnostics().clone(),
            store
                .source_file_links(context.source_file(FILE).unwrap())
                .cloned(),
            nodes,
            values,
            signatures,
            types,
        )
    };
    let before = snapshot(context);
    let raw = format!("{:?}", context.store());
    for _ in 0..2 {
        for &(type_, location, expected) in displays {
            assert_eq!(context.type_to_string(type_).unwrap(), expected);
            assert_eq!(format!("{:?}", context.store()), raw);
            assert_eq!(
                context.type_to_string_at_location(type_, location).unwrap(),
                expected
            );
            assert_eq!(format!("{:?}", context.store()), raw);
        }
    }
    assert_eq!(snapshot(context), before);
}

#[test]
#[allow(clippy::too_many_lines)] // Check the original call and signature in three query orders.
fn original_abstract_method_keeps_full_signature_in_each_query_order() {
    let library = parse_source_file(ES5);
    let parsed = parse_source_file(ABSTRACT_SOURCE);
    let (class, class_name) = class_nodes(&parsed, "AbstractClass");
    let declarations = methods(&parsed, "method");
    let [method] = declarations.as_slice() else {
        unreachable!()
    };
    let method_accesses = accesses(&parsed, "method");
    let [(access, name)] = method_accesses.as_slice() else {
        unreachable!()
    };
    let (access, name) = (*access, *name);
    let call = call_of_access(&parsed, access);
    assert_eq!(node_text(ABSTRACT_SOURCE, &parsed, access), "this.method");
    assert_eq!(
        node_text(ABSTRACT_SOURCE, &parsed, call),
        "this.method(parseInt(str))"
    );

    for first_query in [None, Some(class_name), Some(access)] {
        let mut context = context(&parsed, Some(&library));
        assert!(!is_checked(&context));
        if let Some(location) = first_query {
            context.get_type_at_location(location).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        assert!(is_checked(&context));
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let void = bootstrap.void_type;
        assert_eq!(context.get_type_at_location(call).unwrap(), void);
        let NodeData::CallExpression(outer_call) = &parsed.arena.get(call.node).unwrap().data
        else {
            unreachable!()
        };
        let [argument] = outer_call.arguments.nodes.as_slice() else {
            unreachable!()
        };
        let argument = node(&parsed, *argument);
        assert_eq!(context.get_type_at_location(argument).unwrap(), number);
        let NodeData::CallExpression(parse_int_call) =
            &parsed.arena.get(argument.node).unwrap().data
        else {
            unreachable!()
        };
        let parse_int = context
            .get_symbol_at_location(node(&parsed, parse_int_call.expression))
            .unwrap()
            .unwrap();
        let [declaration] = context.get_symbol_declarations(parse_int).unwrap() else {
            unreachable!()
        };
        assert_eq!(declaration.file, LIBRARY_FILE);
        let NodeData::FunctionDeclaration(function) =
            &library.arena.get(declaration.node).unwrap().data
        else {
            panic!("parseInt must come from its real library declaration")
        };
        let NodeData::Identifier(identifier) =
            &library.arena.get(function.name.unwrap()).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(identifier.text, "parseInt");
        let method_type = context.get_type_at_location(access).unwrap();
        assert_eq!(context.get_type_at_location(name).unwrap(), method_type);
        let method_symbol = symbol(&context, method.declaration);
        let class_symbol = symbol(&context, class);
        assert_eq!(
            context.store().symbol(method_symbol).unwrap().parent(),
            Some(class_symbol)
        );
        assert_eq!(
            context.store().type_payload(method_type).unwrap().symbol(),
            Some(method_symbol)
        );
        assert_eq!(
            context.get_symbol_at_location(access).unwrap(),
            Some(method_symbol)
        );
        assert_eq!(
            context.get_symbol_at_location(name).unwrap(),
            Some(method_symbol)
        );
        assert_eq!(
            context.get_symbol_declarations(method_symbol).unwrap(),
            &[method.declaration]
        );
        let class_type = context.get_type_at_location(class_name).unwrap();
        let members = structured_data(context.store().type_payload(class_type).unwrap().data())
            .unwrap()
            .members
            .unwrap();
        assert_eq!(
            context
                .store()
                .symbol_table(members)
                .unwrap()
                .get_source("method"),
            Some(method_symbol)
        );
        let method_signatures = signatures(&context, method_type);
        let [signature] = method_signatures.as_slice() else {
            unreachable!()
        };
        assert_signature(
            &mut context,
            &parsed,
            method,
            *signature,
            &[("num", number)],
            void,
        );
        let displays = [(method_type, call, "(num: number) => void")];
        assert_display_read_only(&mut context, &parsed, &displays);
        let before = counts(&context);
        let diagnostics = context.diagnostics().clone();
        context.recheck_source_file(FILE).unwrap();
        for location in [access, name] {
            assert_eq!(context.get_type_at_location(location).unwrap(), method_type);
            assert_eq!(
                context.get_symbol_at_location(location).unwrap(),
                Some(method_symbol)
            );
        }
        assert_eq!(signatures(&context, method_type), method_signatures);
        assert_display_read_only(&mut context, &parsed, &displays);
        assert_eq!(counts(&context), before);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
fn concrete_method_display_keeps_inferred_returns_and_zero_argument_methods() {
    let parsed = parse_source_file(concat!(
        "class Counter {\n",
        "  constructor() { this.echo(1); this.ready(); }\n",
        "  echo(value: number) { return value; }\n",
        "  ready() { return true; }\n",
        "}",
    ));
    let mut context = context(&parsed, None);
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let boolean = bootstrap.boolean_type;
    let mut displays = Vec::new();
    let mut observed = Vec::new();
    for (name, parameters, result, display) in [
        (
            "echo",
            vec![("value", number)],
            number,
            "(value: number) => number",
        ),
        ("ready", Vec::new(), boolean, "() => boolean"),
    ] {
        let declarations = methods(&parsed, name);
        let [method] = declarations.as_slice() else {
            unreachable!()
        };
        let accesses = accesses(&parsed, name);
        let [(access, property_name)] = accesses.as_slice() else {
            unreachable!()
        };
        let call = call_of_access(&parsed, *access);
        let method_type = context.get_type_at_location(*access).unwrap();
        assert_eq!(
            context.get_type_at_location(*property_name).unwrap(),
            method_type
        );
        assert_eq!(context.get_type_at_location(call).unwrap(), result);
        let method_symbol = symbol(&context, method.declaration);
        assert_eq!(
            context.store().type_payload(method_type).unwrap().symbol(),
            Some(method_symbol)
        );
        assert_eq!(
            context.get_symbol_at_location(*access).unwrap(),
            Some(method_symbol)
        );
        let signatures = signatures(&context, method_type);
        let [signature] = signatures.as_slice() else {
            unreachable!()
        };
        assert_signature(
            &mut context,
            &parsed,
            method,
            *signature,
            &parameters,
            result,
        );
        displays.push((method_type, call, display));
        observed.push((*access, method_type, method_symbol, *signature));
    }
    assert_display_read_only(&mut context, &parsed, &displays);
    let before = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    for (access, expected, method, signature) in observed {
        assert_eq!(context.get_type_at_location(access).unwrap(), expected);
        assert_eq!(
            context.get_symbol_at_location(access).unwrap(),
            Some(method)
        );
        assert_eq!(signatures(&context, expected), [signature]);
    }
    assert_display_read_only(&mut context, &parsed, &displays);
    assert_eq!(counts(&context), before);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn interface_overload_display_keeps_declaration_order_and_required_parameters() {
    let parsed = parse_source_file(concat!(
        "interface Service {\n",
        "  read(value: string, radix: number): number;\n",
        "  read(value: number): string;\n",
        "}\n",
        "declare const service: Service;\n",
        "const numeric = service.read('10', 10);\n",
        "const textual = service.read(1);\n",
        "const read = service.read;",
    ));
    let mut context = context(&parsed, None);
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    let methods = methods(&parsed, "read");
    assert_eq!(methods.len(), 2);
    let accesses = accesses(&parsed, "read");
    let [(first, _), (second, _), (detached, _)] = accesses.as_slice() else {
        unreachable!()
    };
    let method_type = context.get_type_at_location(*first).unwrap();
    let method_symbol = symbol(&context, methods[0].declaration);
    assert_eq!(symbol(&context, methods[1].declaration), method_symbol);
    assert_eq!(
        context.store().type_payload(method_type).unwrap().symbol(),
        Some(method_symbol)
    );
    assert_eq!(
        context.get_symbol_declarations(method_symbol).unwrap(),
        &[methods[0].declaration, methods[1].declaration]
    );
    let method_signatures = signatures(&context, method_type);
    let [first_signature, second_signature] = method_signatures.as_slice() else {
        unreachable!()
    };
    assert_ne!(first_signature, second_signature);
    assert_signature(
        &mut context,
        &parsed,
        &methods[0],
        *first_signature,
        &[("value", string), ("radix", number)],
        number,
    );
    assert_signature(
        &mut context,
        &parsed,
        &methods[1],
        *second_signature,
        &[("value", number)],
        string,
    );
    assert_eq!(
        context
            .get_type_at_location(call_of_access(&parsed, *first))
            .unwrap(),
        number
    );
    assert_eq!(
        context
            .get_type_at_location(call_of_access(&parsed, *second))
            .unwrap(),
        string
    );
    let display = "{ (value: string, radix: number): number; (value: number): string; }";
    let displays = [(method_type, *detached, display)];
    for (access, name) in &accesses {
        for location in [*access, *name] {
            assert_eq!(context.get_type_at_location(location).unwrap(), method_type);
            assert_eq!(
                context.get_symbol_at_location(location).unwrap(),
                Some(method_symbol)
            );
        }
    }
    assert_display_read_only(&mut context, &parsed, &displays);
    let before = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(
        context.get_type_at_location(*detached).unwrap(),
        method_type
    );
    assert_eq!(signatures(&context, method_type), method_signatures);
    assert_display_read_only(&mut context, &parsed, &displays);
    assert_eq!(counts(&context), before);
    assert!(context.diagnostics().is_empty());
}

#[allow(clippy::too_many_lines)] // Keep the original overload row's public and hidden identities together.
fn assert_supported_method_overload_row(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    methods: &[Method],
) {
    context.check_source_file(FILE).unwrap();
    assert!(is_checked(context));
    assert!(context.diagnostics().is_empty());
    let [first, second, implementation] = methods else {
        panic!("the original source has two overloads and one implementation");
    };
    let (class, _) = class_nodes(parsed, "Service");
    let class_owner = symbol(context, class);
    let method_owner = symbol(context, first.declaration);
    let declarations = methods
        .iter()
        .map(|method| method.declaration)
        .collect::<Vec<_>>();
    let record = context.store().symbol(method_owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::METHOD);
    assert_eq!(record.parent(), Some(class_owner));
    assert_eq!(record.declarations(), Some(declarations.as_slice()));
    assert_eq!(record.value_declaration(), Some(first.declaration));
    assert_eq!(
        context
            .store()
            .symbol(class_owner)
            .unwrap()
            .members()
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("read")),
        Some(method_owner)
    );
    let callable = context.get_type_at_location(first.name).unwrap();
    assert_eq!(
        context.store().type_payload(callable).unwrap().symbol(),
        Some(method_owner)
    );
    let signature_ids = methods
        .iter()
        .enumerate()
        .map(|(index, method)| {
            assert_eq!(symbol(context, method.declaration), method_owner);
            assert_eq!(context.get_type_at_location(method.name).unwrap(), callable);
            let NodeData::MethodDeclaration(data) =
                &parsed.arena.get(method.declaration.node).unwrap().data
            else {
                panic!("the original class member must remain a method");
            };
            assert_eq!(data.body.is_some(), index == 2);
            context
                .store()
                .signature_links(method.declaration)
                .unwrap()
                .resolved_signature
                .signature()
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert_ne!(signature_ids[0], signature_ids[1]);
    assert_ne!(signature_ids[0], signature_ids[2]);
    assert_ne!(signature_ids[1], signature_ids[2]);
    assert_eq!(signatures(context, callable), signature_ids[..2]);
    assert!(!signatures(context, callable).contains(&signature_ids[2]));
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (number, string) = (bootstrap.number_type, bootstrap.string_type);
    let NodeData::ParameterDeclaration(parameter) = &parsed
        .arena
        .get(implementation.parameters[0].node)
        .unwrap()
        .data
    else {
        panic!("the implementation must retain its parameter");
    };
    let annotation = node(parsed, parameter.type_.unwrap());
    let union = context.get_type_from_type_node(annotation).unwrap();
    let TypeData::Union(data) = context.store().type_payload(union).unwrap().data() else {
        panic!("the implementation annotation must retain number and string");
    };
    assert_eq!(data.union.types.len(), 2);
    assert!(data.union.types.contains(&number));
    assert!(data.union.types.contains(&string));
    for (method, signature, expected) in [
        (first, signature_ids[0], number),
        (second, signature_ids[1], string),
        (implementation, signature_ids[2], union),
    ] {
        assert_signature(
            context,
            parsed,
            method,
            signature,
            &[("value", expected)],
            expected,
        );
    }
    let parameter_symbols = methods
        .iter()
        .map(|method| symbol(context, method.parameters[0]))
        .collect::<Vec<_>>();
    assert_ne!(parameter_symbols[0], parameter_symbols[1]);
    assert_ne!(parameter_symbols[0], parameter_symbols[2]);
    assert_ne!(parameter_symbols[1], parameter_symbols[2]);
    let NodeData::MethodDeclaration(data) = &parsed
        .arena
        .get(implementation.declaration.node)
        .unwrap()
        .data
    else {
        unreachable!()
    };
    let NodeData::Block(body) = &parsed.arena.get(data.body.unwrap()).unwrap().data else {
        panic!("the implementation must retain its real block");
    };
    let [return_statement] = body.statements.nodes.as_slice() else {
        panic!("the original block has one return");
    };
    let NodeData::ReturnStatement(returned) = &parsed.arena.get(*return_statement).unwrap().data
    else {
        panic!("the original body must return its parameter");
    };
    let returned = node(parsed, returned.expression.unwrap());
    assert_eq!(context.get_type_at_location(returned).unwrap(), union);
    assert_eq!(
        context.get_symbol_at_location(returned).unwrap(),
        Some(parameter_symbols[2])
    );
    let displays = [(
        callable,
        first.name,
        "{ (value: number): number; (value: string): string; }",
    )];
    assert_display_read_only(context, parsed, &displays);
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        const TOKEN: &str = ", next_relation_observation_token: ";
        const DERIVED: &str = ", derived_types: ";
        const VALIDATION: &str = ", union_cache_needs_validation: ";

        let complete = format!("{:?}", context.store());
        assert!(complete.starts_with("SemanticStore { "));
        for field in [TOKEN, DERIVED, VALIDATION] {
            assert_eq!(complete.matches(field).count(), 1, "{field}");
        }
        let (state, dirty) = complete
            .rsplit_once(VALIDATION)
            .expect("the final union validation field is present");
        let dirty = match dirty {
            "true }" => true,
            "false }" => false,
            _ => panic!("the final union validation field must be a bool"),
        };
        let (prefix, token_and_suffix) = state
            .split_once(TOKEN)
            .expect("the observation counter is present");
        let (token_text, suffix) = token_and_suffix
            .split_once(DERIVED)
            .expect("the counter is followed by the derived type caches");
        let token = token_text
            .parse::<u64>()
            .expect("the observation counter is a u64");
        assert_eq!(token.to_string(), token_text);
        let state =
            format!("{prefix}{TOKEN}<counter>{DERIVED}{suffix}{VALIDATION}<validation-state> }}");
        ((state, context.diagnostics().clone()), token, dirty)
    };
    let (warm, mut token, dirty) = snapshot(context);
    assert!(dirty);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert!(is_checked(context));
        assert!(context.diagnostics().is_empty());
        assert_eq!(context.get_type_at_location(returned).unwrap(), union);
        assert_eq!(context.get_type_from_type_node(annotation).unwrap(), union);
        assert_eq!(signatures(context, callable), signature_ids[..2]);
        for (method, signature, expected) in [
            (first, signature_ids[0], number),
            (second, signature_ids[1], string),
            (implementation, signature_ids[2], union),
        ] {
            assert_eq!(context.get_type_at_location(method.name).unwrap(), callable);
            assert_signature(
                context,
                parsed,
                method,
                signature,
                &[("value", expected)],
                expected,
            );
        }
        assert_display_read_only(context, parsed, &displays);
        let (replayed, replay_token, replay_dirty) = snapshot(context);
        assert_eq!(replayed, warm);
        assert_eq!(replay_token, token.checked_add(4).unwrap());
        assert!(!replay_dirty);
        token = replay_token;
    }
}

#[test]
fn class_method_overloads_preserve_signatures_and_generic_methods_remain_unsupported() {
    for (index, source) in [
        "class Service { read(value: number): number; read(value: string): string; read(value: number | string) { return value; } }",
        "class Service { read<T>(value: T): T { return value; } }",
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed, None);
        let methods = methods(&parsed, "read");
        if index == 0 {
            assert_supported_method_overload_row(&mut context, &parsed, &methods);
            continue;
        }
        let before = counts(&context);
        let error = context.check_source_file(FILE).unwrap_err();
        assert!(
            matches!(error, SourceCheckError::Unsupported(_)),
            "{source}: {error:?}"
        );
        assert_eq!(context.check_source_file(FILE).unwrap_err(), error);
        assert_eq!(
            context.get_type_at_location(methods[0].name).unwrap_err(),
            CanonicalArtifactQueryError::SourceCheck(error)
        );
        for method in methods {
            assert!(
                context
                    .store()
                    .signature_links(method.declaration)
                    .is_none()
            );
            assert!(
                context
                    .store()
                    .value_symbol_links(symbol(&context, method.declaration))
                    .is_none()
            );
        }
        assert_eq!(counts(&context), before);
        assert!(context.diagnostics().is_empty());
        assert!(!is_checked(&context));
    }
}
