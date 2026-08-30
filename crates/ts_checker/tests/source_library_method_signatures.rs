use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, SignatureLinks, SourceFileLinks, TypeData, TypeId,
    TypeNodeLinks, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const FIRST: FileId = FileId::new(202_600);
const SECOND: FileId = FileId::new(202_601);
const SOURCE: FileId = FileId::new(202_602);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const ES2015_CORE: &str = include_str!("../../ts_bundled/libs/lib.es2015.core.d.ts");

fn context<'a>(
    first: &'a ParseResult,
    second: &'a ParseResult,
    source: &'a ParseResult,
    default_libraries: bool,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    let files = [(FIRST, first), (SECOND, second), (SOURCE, source)];
    for (file, parsed) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let path = match file {
            FIRST if default_libraries => "\"/lib/lib.es5.d.ts\"",
            SECOND if default_libraries => "\"/lib/lib.es2015.core.d.ts\"",
            FIRST => "\"/project/first.d.ts\"",
            SECOND => "\"/project/second.d.ts\"",
            SOURCE => "\"/project/main.ts\"",
            _ => unreachable!(),
        };
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file != SOURCE,
                    default_libraries && file != SOURCE,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for (file, parsed) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed)| (file, &parsed.arena))
            .collect(),
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

struct Method {
    declaration: NodeRef,
    name: NodeRef,
    parameters: Vec<NodeRef>,
    return_type: NodeRef,
}

fn method(parsed: &ParseResult, file: FileId, owner: &str, name: &str) -> Method {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                return None;
            };
            let NodeData::Identifier(method_name) = &parsed.arena.get(method.name)?.data else {
                return None;
            };
            let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(record.parent?)?.data
            else {
                return None;
            };
            let NodeData::Identifier(owner_name) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (owner_name.text == owner && method_name.text == name).then(|| Method {
                declaration: NodeRef::new(parsed.arena.id(), file, node),
                name: NodeRef::new(parsed.arena.id(), file, method.name),
                parameters: method
                    .parameters
                    .nodes
                    .iter()
                    .map(|node| NodeRef::new(parsed.arena.id(), file, *node))
                    .collect(),
                return_type: NodeRef::new(parsed.arena.id(), file, method.type_.unwrap()),
            })
        })
        .unwrap_or_else(|| panic!("missing {owner}.{name}"))
}

fn raw_symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    context.file(node.file).unwrap().1.symbol(node).unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    context
        .store()
        .get_merged_symbol(raw_symbol(context, node))
        .unwrap()
}

fn assert_merged_method(
    context: &CanonicalCheckerContext<'_>,
    first: &Method,
    second: &Method,
) -> SemanticSymbolId {
    assert_ne!(
        raw_symbol(context, first.declaration),
        raw_symbol(context, second.declaration),
    );
    let merged = symbol(context, first.declaration);
    assert_eq!(symbol(context, second.declaration), merged);
    let record = context.store().symbol(merged).unwrap();
    assert_eq!(record.flags(), SymbolFlags::METHOD | SymbolFlags::TRANSIENT);
    assert_eq!(
        record.declarations(),
        Some(&[first.declaration, second.declaration][..]),
    );
    merged
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn parameter_types(context: &CanonicalCheckerContext<'_>, signature: SignatureId) -> Vec<TypeId> {
    context
        .store()
        .signature(signature)
        .unwrap()
        .parameters()
        .iter()
        .map(|symbol| {
            context
                .store()
                .value_symbol_links(*symbol)
                .and_then(|links| links.resolved_type)
                .unwrap()
        })
        .collect()
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), SOURCE, node),
            ))
        })
        .collect::<Vec<_>>();
    found.sort_by_key(|(start, _)| *start);
    found.into_iter().map(|(_, node)| node).collect()
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 6],
    types: Vec<Option<TypeNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    sources: Vec<Option<SourceFileLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    first: &ParseResult,
    second: &ParseResult,
    source: &ParseResult,
) -> Snapshot {
    let store = context.store();
    let nodes = [(FIRST, first), (SECOND, second), (SOURCE, source)]
        .into_iter()
        .flat_map(|(file, parsed)| {
            parsed
                .arena
                .iter()
                .map(move |(node, _)| NodeRef::new(parsed.arena.id(), file, node))
        })
        .collect::<Vec<_>>();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        types: nodes
            .iter()
            .map(|node| store.type_node_links(*node).cloned())
            .collect(),
        signatures: nodes
            .iter()
            .map(|node| store.signature_links(*node).cloned())
            .collect(),
        values: nodes
            .iter()
            .filter_map(|node| context.file(node.file).unwrap().1.symbol(*node))
            .map(|symbol| {
                store
                    .value_symbol_links(store.get_merged_symbol(symbol).unwrap())
                    .cloned()
            })
            .collect(),
        sources: [FIRST, SECOND, SOURCE]
            .map(|file| {
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            })
            .to_vec(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    first: &ParseResult,
    second: &ParseResult,
    source: &ParseResult,
    queries: &[(NodeRef, TypeId)],
) {
    let warm = snapshot(context, first, second, source);
    for recheck in [false, true] {
        if recheck {
            context.recheck_source_file(SOURCE).unwrap();
        } else {
            context.check_source_file(SOURCE).unwrap();
        }
        for &(node, expected) in queries {
            assert_eq!(context.get_type_at_location(node), Ok(expected), "{node:?}");
        }
        assert_eq!(snapshot(context, first, second, source), warm);
        assert!(context.store().type_resolution_is_empty());
    }
}

#[test]
fn real_library_keys_overloads_share_one_canonical_method_and_replay() {
    let first = parse_source_file(ES5);
    let second = parse_source_file(ES2015_CORE);
    let source = parse_source_file("");
    let methods = [
        method(&first, FIRST, "ObjectConstructor", "keys"),
        method(&second, SECOND, "ObjectConstructor", "keys"),
    ];
    let mut context = context(&first, &second, &source, true);
    let merged = assert_merged_method(&context, &methods[0], &methods[1]);
    assert!(context.store().value_symbol_links(merged).is_none());

    // This isolates the retained MethodSignature stop. It does not run Object.freeze.
    let callable = context.get_type_at_location(methods[0].name).unwrap();
    for method in &methods {
        assert_eq!(context.get_type_at_location(method.name), Ok(callable));
        assert_eq!(
            context.get_type_at_location(method.declaration),
            Ok(callable),
        );
        assert_eq!(
            context.get_symbol_at_location(method.name),
            Ok(Some(merged))
        );
    }
    let record = context.store().type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(merged));
    let TypeData::Object(object) = record.data() else {
        panic!("the merged library method must retain its callable object");
    };
    let signatures = object.structured.signatures.as_ref().unwrap().clone();
    assert_eq!(signatures.len(), 2);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let mut returns = Vec::new();
    for (method, signature) in methods.iter().zip(signatures) {
        assert_eq!(
            context.store().signature(signature).unwrap().declaration(),
            Some(method.declaration),
        );
        assert_eq!(
            context.store().signature(signature).unwrap().parameters(),
            &[symbol(&context, method.parameters[0])],
        );
        assert_eq!(
            context
                .store()
                .signature(signature)
                .unwrap()
                .min_argument_count(),
            1,
        );
        let result = context.get_return_type_of_signature(signature).unwrap();
        assert_eq!(
            context.get_type_from_type_node(method.return_type),
            Ok(result)
        );
        let TypeData::TypeReference(array) = context.store().type_payload(result).unwrap().data()
        else {
            panic!("keys must return the declared string array");
        };
        assert_eq!(array.object.target, Some(context.global_types().array_type));
        assert_eq!(
            array.resolved_type_arguments.as_deref(),
            Some(&[string][..])
        );
        returns.push(result);
    }
    assert_eq!(returns[0], returns[1]);
    assert_eq!(
        parameter_types(&context, signature(&context, methods[0].declaration)),
        [context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .non_primitive_type],
    );
    let second_parameter =
        parameter_types(&context, signature(&context, methods[1].declaration))[0];
    assert_eq!(context.type_to_string(second_parameter).unwrap(), "{}");
    assert_ne!(
        second_parameter,
        context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .non_primitive_type,
    );
    context.check_source_file(SOURCE).unwrap();
    assert!(context.diagnostics().is_empty());
    for file in [FIRST, SECOND] {
        assert!(
            !context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .is_some_and(|links| links.type_checked),
        );
    }
    let queries = methods
        .iter()
        .flat_map(|method| [(method.name, callable), (method.declaration, callable)])
        .collect::<Vec<_>>();
    assert_replay(&mut context, &first, &second, &source, &queries);
}

#[test]
fn real_library_keys_calls_preserve_overload_selection_arrays_and_arity_errors() {
    let first = parse_source_file(ES5);
    let second = parse_source_file(ES2015_CORE);
    let source_text = concat!(
        "const names = Object.keys({ id: 1 });\n",
        "const scalarNames = Object.keys(1);\n",
        "const bad = Object.keys({}, true);\n",
    );
    let source = parse_source_file(source_text);
    let methods = [
        method(&first, FIRST, "ObjectConstructor", "keys"),
        method(&second, SECOND, "ObjectConstructor", "keys"),
    ];
    let mut context = context(&first, &second, &source, true);
    let merged = assert_merged_method(&context, &methods[0], &methods[1]);
    context.check_source_file(SOURCE).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("only the extra Object.keys argument must produce a diagnostic");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2554);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 2.",
    );
    assert_eq!(diagnostic.node.unwrap().file, SOURCE);
    let range = diagnostic.range_override.unwrap().range();
    assert_eq!(
        &source_text[usize::try_from(range.start.get()).unwrap()
            ..usize::try_from(range.end.get()).unwrap()],
        "true",
    );
    assert!(diagnostic.related_information.is_empty());

    let selected = signature(&context, methods[1].declaration);
    let result = context.get_return_type_of_signature(selected).unwrap();
    let TypeData::TypeReference(array) = context.store().type_payload(result).unwrap().data()
    else {
        panic!("Object.keys must keep the canonical string array result");
    };
    assert_eq!(array.object.target, Some(context.global_types().array_type));
    assert_eq!(
        array.resolved_type_arguments.as_deref(),
        Some(&[context.store().intrinsic_bootstrap().unwrap().string_type][..]),
    );
    let calls = nodes(&source, SyntaxKind::CallExpression);
    let accesses = nodes(&source, SyntaxKind::PropertyAccessExpression);
    assert_eq!(calls.len(), 3);
    assert_eq!(accesses.len(), 3);
    let callable = context.get_type_at_location(methods[0].name).unwrap();
    let mut queries = Vec::new();
    for (call, access) in calls.into_iter().zip(accesses) {
        assert_eq!(signature(&context, call), selected);
        assert_eq!(context.get_type_at_location(call), Ok(result));
        assert_eq!(context.get_type_at_location(access), Ok(callable));
        assert_eq!(context.get_symbol_at_location(access), Ok(Some(merged)));
        queries.extend([(call, result), (access, callable)]);
    }
    for method in &methods {
        assert_eq!(context.get_type_at_location(method.name), Ok(callable));
        queries.push((method.name, callable));
    }
    assert_replay(&mut context, &first, &second, &source, &queries);
}

#[test]
fn split_method_overloads_select_real_signatures_and_preserve_bad_calls() {
    let first = parse_source_file("interface Reader { read(value: string): number; }");
    let second =
        parse_source_file("interface Reader { read(value: number, extra: number): number; }");
    let source_text = concat!(
        "declare const reader: Reader;\n",
        "const text = reader.read('text');\n",
        "const pair = reader.read(1, 2);\n",
        "const bad = reader.read(true);\n",
    );
    let source = parse_source_file(source_text);
    let methods = [
        method(&first, FIRST, "Reader", "read"),
        method(&second, SECOND, "Reader", "read"),
    ];
    for query_first in [false, true] {
        let mut context = context(&first, &second, &source, false);
        let merged = assert_merged_method(&context, &methods[0], &methods[1]);
        let early = query_first.then(|| context.get_type_at_location(methods[0].name).unwrap());
        context.check_source_file(SOURCE).unwrap();
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("only the bad read argument must produce a diagnostic");
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Argument of type 'boolean' is not assignable to parameter of type 'string'.",
        );
        let node = diagnostic.node.unwrap();
        assert_eq!(node.file, SOURCE);
        let range = source.arena.get(node.node).unwrap().range;
        assert_eq!(
            &source_text[usize::try_from(range.start.get()).unwrap()
                ..usize::try_from(range.end.get()).unwrap()],
            "true",
        );
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());

        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let callable = context.get_type_at_location(methods[0].name).unwrap();
        assert!(early.is_none_or(|early| early == callable));
        assert_eq!(
            context.store().type_payload(callable).unwrap().symbol(),
            Some(merged)
        );
        let signatures = methods
            .iter()
            .map(|method| signature(&context, method.declaration))
            .collect::<Vec<_>>();
        assert_ne!(signatures[0], signatures[1]);
        assert_eq!(parameter_types(&context, signatures[0]), [string]);
        assert_eq!(parameter_types(&context, signatures[1]), [number, number]);
        for signature in &signatures {
            assert_eq!(context.get_return_type_of_signature(*signature), Ok(number));
        }
        let calls = nodes(&source, SyntaxKind::CallExpression);
        assert_eq!(calls.len(), 3);
        let mut queries = Vec::new();
        for (&call, expected) in calls
            .iter()
            .zip([signatures[0], signatures[1], signatures[0]])
        {
            assert_eq!(signature(&context, call), expected);
            assert_eq!(context.get_type_at_location(call), Ok(number));
            queries.push((call, number));
        }
        for method in &methods {
            assert_eq!(context.get_type_at_location(method.name), Ok(callable));
            queries.push((method.name, callable));
        }
        assert_replay(&mut context, &first, &second, &source, &queries);
    }
}

#[test]
fn split_method_overloads_contextualize_each_callback() {
    let first = parse_source_file(concat!(
        "interface Visitor { ",
        "visit(kind: 'text', callback: (value: string) => string): string; }",
    ));
    let second = parse_source_file(concat!(
        "interface Visitor { ",
        "visit(kind: 'count', callback: (value: number) => number): number; }",
    ));
    let source = parse_source_file(concat!(
        "declare const visitor: Visitor;\n",
        "const text = visitor.visit('text', value => value);\n",
        "const count = visitor.visit('count', value => value + 1);\n",
    ));
    let methods = [
        method(&first, FIRST, "Visitor", "visit"),
        method(&second, SECOND, "Visitor", "visit"),
    ];
    let mut context = context(&first, &second, &source, false);
    assert_merged_method(&context, &methods[0], &methods[1]);
    context.check_source_file(SOURCE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let calls = nodes(&source, SyntaxKind::CallExpression);
    let arrows = nodes(&source, SyntaxKind::ArrowFunction);
    assert_eq!(calls.len(), 2);
    assert_eq!(arrows.len(), 2);
    let mut queries = Vec::new();
    for (index, (input, output)) in [(string, string), (number, number)].into_iter().enumerate() {
        let call = calls[index];
        let arrow = arrows[index];
        assert_eq!(
            signature(&context, call),
            signature(&context, methods[index].declaration),
        );
        assert_eq!(context.get_type_at_location(call), Ok(output));
        let NodeData::ArrowFunction(arrow_data) = &source.arena.get(arrow.node).unwrap().data
        else {
            unreachable!();
        };
        let parameter = NodeRef::new(arrow.arena, SOURCE, arrow_data.parameters.nodes[0]);
        let NodeData::ParameterDeclaration(parameter_data) =
            &source.arena.get(parameter.node).unwrap().data
        else {
            unreachable!();
        };
        assert!(parameter_data.type_.is_none());
        let parameter_name = NodeRef::new(arrow.arena, SOURCE, parameter_data.name);
        let arrow_signature = signature(&context, arrow);
        assert_eq!(parameter_types(&context, arrow_signature), [input]);
        assert_eq!(
            context
                .store()
                .signature(arrow_signature)
                .unwrap()
                .parameters(),
            &[symbol(&context, parameter)],
        );
        assert_eq!(context.get_type_at_location(parameter_name), Ok(input));
        assert_eq!(
            context.get_return_type_of_signature(arrow_signature),
            Ok(output)
        );
        let body = NodeRef::new(arrow.arena, SOURCE, arrow_data.body);
        assert_eq!(context.get_type_at_location(body), Ok(output));
        let callable = context.get_type_at_location(arrow).unwrap();
        queries.extend([
            (call, output),
            (arrow, callable),
            (parameter_name, input),
            (body, output),
        ]);
    }
    assert_replay(&mut context, &first, &second, &source, &queries);
}

#[test]
#[allow(clippy::too_many_lines)] // Keep generic source identity, specialization, and replay together.
fn split_generic_method_overloads_preserve_inferred_and_explicit_types() {
    let first = parse_source_file("interface Adapter { map<T>(value: T): T; }");
    let second =
        parse_source_file("interface Adapter { map(value: number, scale: number): number; }");
    let source_text = concat!(
        "declare const adapter: Adapter;\n",
        "declare const original: { id: number };\n",
        "const inferred = adapter.map(original);\n",
        "const explicit = adapter.map<string>('text');\n",
        "const scaled = adapter.map(2, 3);\n",
        "const bad = adapter.map<string>(1);\n",
    );
    let source = parse_source_file(source_text);
    let methods = [
        method(&first, FIRST, "Adapter", "map"),
        method(&second, SECOND, "Adapter", "map"),
    ];
    let mut context = context(&first, &second, &source, false);
    let merged = assert_merged_method(&context, &methods[0], &methods[1]);
    context.check_source_file(SOURCE).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("only the explicit string call with a number must fail");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'number' is not assignable to parameter of type 'string'.",
    );
    let node = diagnostic.node.unwrap();
    assert_eq!(node.file, SOURCE);
    let range = source.arena.get(node.node).unwrap().range;
    assert_eq!(
        &source_text[usize::try_from(range.start.get()).unwrap()
            ..usize::try_from(range.end.get()).unwrap()],
        "1",
    );
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());

    let generic = signature(&context, methods[0].declaration);
    let concrete = signature(&context, methods[1].declaration);
    let type_parameter = context
        .store()
        .signature(generic)
        .unwrap()
        .type_parameters()[0];
    assert!(matches!(
        context.store().type_payload(type_parameter).unwrap().data(),
        TypeData::TypeParameter(_),
    ));
    assert_eq!(parameter_types(&context, generic), [type_parameter]);
    assert_eq!(
        context.get_return_type_of_signature(generic),
        Ok(type_parameter)
    );
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(parameter_types(&context, concrete), [number, number]);
    assert_eq!(context.get_return_type_of_signature(concrete), Ok(number));

    let calls = nodes(&source, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 4);
    let NodeData::CallExpression(call) = &source.arena.get(calls[0].node).unwrap().data else {
        unreachable!();
    };
    let original = NodeRef::new(source.arena.id(), SOURCE, call.arguments.nodes[0]);
    let original_type = context.get_type_at_location(original).unwrap();
    assert_eq!(
        context.type_to_string(original_type).unwrap(),
        "{ id: number; }"
    );
    let mut queries = vec![(original, original_type)];
    for (&call, result) in calls.iter().zip([original_type, string, number, string]) {
        let selected = signature(&context, call);
        assert_eq!(context.get_type_at_location(call), Ok(result));
        assert_eq!(context.get_return_type_of_signature(selected), Ok(result));
        if call == calls[2] {
            assert_eq!(selected, concrete);
        } else {
            let record = context.store().signature(selected).unwrap();
            assert_eq!(record.target(), Some(generic));
            assert!(record.mapper().is_some());
            assert!(record.type_parameters().is_empty());
            assert_eq!(parameter_types(&context, selected), [result]);
        }
        queries.push((call, result));
    }
    let callable = context.get_type_at_location(methods[0].name).unwrap();
    assert_eq!(
        context.store().type_payload(callable).unwrap().symbol(),
        Some(merged)
    );
    for method in &methods {
        assert_eq!(context.get_type_at_location(method.name), Ok(callable));
        queries.push((method.name, callable));
    }
    assert_replay(&mut context, &first, &second, &source, &queries);
}
