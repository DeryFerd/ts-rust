use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(205_720);
const STRING_LIBRARY: FileId = FileId::new(205_721);
const NUMBER_LIBRARY: FileId = FileId::new(205_722);

struct Source<'arena> {
    file: FileId,
    parsed: &'arena ParseResult,
    path: &'static str,
    declaration: bool,
    library: bool,
}

fn context<'arena>(sources: &[Source<'arena>]) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for source in sources {
        assert!(
            source.parsed.diagnostics.is_empty(),
            "{:?}",
            source.parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &source.parsed.arena,
                source.parsed.source_file,
                source.file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(source.path),
                    CanonicalSourceLanguage::TypeScript,
                    source.declaration,
                    source.library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for source in sources {
        binder
            .bind_typescript_declaration_slice(&source.parsed.arena, source.file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        sources
            .iter()
            .map(|source| (source.file, &source.parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let record = parsed.arena.get(id).unwrap();
    let owner = parsed.arena.get(parent.node).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(owner.range.start <= record.range.start);
    assert!(record.range.end <= owner.range.end);
    node(parsed, parent.file, id)
}

fn one_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, file, id)));
    let result = matches.next().unwrap_or_else(|| panic!("missing {kind:?}"));
    assert!(matches.next().is_none(), "expected one {kind:?}");
    result
}

fn declaration_name(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let name = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::FunctionDeclaration(data) => data.name.unwrap(),
        NodeData::ModuleDeclaration(data) => data.name,
        NodeData::VariableDeclaration(data) => data.name,
        _ => panic!("the selected declaration has an identifier name"),
    };
    child(parsed, declaration, name)
}

fn initializer(parsed: &ParseResult, name: &str) -> NodeRef {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::VariableDeclaration(data) = &record.data else {
            return None;
        };
        let initializer = data.initializer?;
        let NodeData::Identifier(identifier) = &parsed.arena.get(data.name).unwrap().data else {
            return None;
        };
        (identifier.text == name).then(|| child(parsed, node(parsed, SOURCE, id), initializer))
    });
    let result = matches
        .next()
        .unwrap_or_else(|| panic!("missing initializer {name}"));
    assert!(matches.next().is_none());
    result
}

fn call_parts(parsed: &ParseResult, call: NodeRef) -> (NodeRef, Vec<NodeRef>) {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("the initializer must retain its actual call")
    };
    (
        child(parsed, call, data.expression),
        data.arguments
            .nodes
            .iter()
            .map(|&argument| child(parsed, call, argument))
            .collect(),
    )
}

fn raw_symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    context
        .store()
        .get_merged_symbol(raw_symbol(context, declaration))
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(location)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the real declaration or call must retain its signature")
}

fn value_type(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .expect("the source symbol must retain its value type")
}

fn assert_callable(
    context: &CanonicalCheckerContext<'_>,
    owner: SemanticSymbolId,
    functions: &[NodeRef],
    namespace: NodeRef,
    flags: SymbolFlags,
) -> (TypeId, Vec<SignatureId>, SemanticSymbolId) {
    let store = context.store();
    let record = store.symbol(owner).unwrap();
    assert_eq!(record.flags(), flags);
    let declarations = record.declarations().unwrap();
    assert_eq!(declarations.len(), functions.len() + 1);
    assert_eq!(
        declarations
            .iter()
            .filter(|&&node| node == namespace)
            .count(),
        1
    );
    assert!(functions.contains(&record.value_declaration().unwrap()));
    for &declaration in functions {
        assert_eq!(
            declarations
                .iter()
                .filter(|&&node| node == declaration)
                .count(),
            1
        );
        assert_eq!(symbol(context, declaration), owner);
    }
    assert_eq!(symbol(context, namespace), owner);
    let table = store.symbol_table(record.exports().unwrap()).unwrap();
    assert_eq!(table.len(), 1);
    let member = table.get_source("label").unwrap();
    let member_record = store.symbol(member).unwrap();
    assert_eq!(
        store.get_merged_symbol(member_record.parent().unwrap()),
        Some(owner)
    );
    let signatures = functions
        .iter()
        .map(|&declaration| {
            let signature = signature(context, declaration);
            let record = store.signature(signature).unwrap();
            assert_eq!(record.declaration(), Some(declaration));
            assert_eq!(record.flags(), SignatureFlags::NONE);
            assert_eq!(record.min_argument_count(), 1);
            assert_eq!(record.parameters().len(), 1);
            assert!(record.type_parameters().is_empty());
            assert_eq!(record.target(), None);
            assert_eq!(record.mapper(), None);
            let (arena, bound) = context.file(declaration.file).unwrap();
            let function_node = arena.get(declaration.node).unwrap();
            let NodeData::FunctionDeclaration(function) = &function_node.data else {
                panic!("the signature must keep its actual function declaration")
            };
            assert_eq!(function_node.kind, SyntaxKind::FunctionDeclaration);
            assert_eq!(function.parameters.nodes.len(), record.parameters().len());
            for (&parameter, &parameter_symbol) in
                function.parameters.nodes.iter().zip(record.parameters())
            {
                let parameter_ref = NodeRef::new(arena.id(), declaration.file, parameter);
                let parameter_node = arena.get(parameter).unwrap();
                let NodeData::ParameterDeclaration(parameter_data) = &parameter_node.data else {
                    panic!("the signature must keep its actual parameter declaration")
                };
                assert_eq!(parameter_node.kind, SyntaxKind::Parameter);
                assert_eq!(parameter_node.parent, Some(declaration.node));
                assert_eq!(bound.symbol(parameter_ref), Some(parameter_symbol));
                assert_eq!(symbol(context, parameter_ref), parameter_symbol);
                let annotation = arena.get(parameter_data.type_.unwrap()).unwrap();
                assert_eq!(annotation.parent, Some(parameter));
                assert!(parameter_node.range.start <= annotation.range.start);
                assert!(annotation.range.end <= parameter_node.range.end);
            }
            signature
        })
        .collect::<Vec<_>>();
    let callable = value_type(context, owner);
    let record = store.type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(data) = record.data() else {
        panic!("the merged function must retain its ordinary callable object")
    };
    assert_eq!(data.structured.call_signature_count, signatures.len());
    assert_eq!(
        data.structured.signatures.as_deref(),
        Some(signatures.as_slice())
    );
    (callable, signatures, member)
}

fn assert_call(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    call: NodeRef,
    owner: SemanticSymbolId,
    callable: TypeId,
    selected: SignatureId,
    result: TypeId,
) {
    let (callee, arguments) = call_parts(parsed, call);
    assert_eq!(arguments.len(), 1);
    assert_eq!(context.get_symbol_at_location(callee), Ok(Some(owner)));
    assert_eq!(context.get_type_at_location(callee), Ok(callable));
    assert_eq!(context.get_type_at_location(call), Ok(result));
    assert_eq!(signature(context, call), selected);
    assert_eq!(
        context
            .store()
            .symbol_node_links(callee)
            .unwrap()
            .resolved_symbol,
        Some(owner)
    );
    assert_eq!(
        context.store().type_node_links(call).unwrap().resolved_type,
        Some(result)
    );
}

fn assert_namespace_member(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    access: NodeRef,
    member: SemanticSymbolId,
) -> TypeId {
    let NodeData::PropertyAccessExpression(data) = &source.arena.get(access.node).unwrap().data
    else {
        panic!("the source must read the merged namespace property")
    };
    let name = child(source, access, data.name);
    let expected = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(context.get_type_at_location(access), Ok(expected));
    assert_eq!(context.get_symbol_at_location(name), Ok(Some(member)));
    assert_eq!(value_type(context, member), expected);
    expected
}

fn state(context: &CanonicalCheckerContext<'_>) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        context.diagnostics().clone(),
        context
            .file_order()
            .iter()
            .map(|&file| {
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            })
            .collect::<Vec<_>>(),
        context
            .file_order()
            .iter()
            .flat_map(|&file| {
                let arena = context.file(file).unwrap().0;
                arena.iter().map(move |(id, _)| {
                    let node = NodeRef::new(arena.id(), file, id);
                    (
                        node,
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, record)| {
                (
                    symbol,
                    record.flags(),
                    record.check_flags(),
                    record.parent(),
                    record.declarations().map(<[_]>::to_vec),
                    record.value_declaration(),
                    record.exports().map(|table| {
                        (
                            table,
                            store
                                .symbol_table(table)
                                .unwrap()
                                .iter()
                                .map(|(name, member)| (name.to_owned(), member))
                                .collect::<Vec<_>>(),
                        )
                    }),
                    store.value_symbol_links(symbol).cloned(),
                )
            })
            .collect::<Vec<_>>(),
    )
}

#[test]
fn source_function_value_namespace_keeps_calls_members_and_argument_errors() {
    let source = parse_source_file(concat!(
        "declare function convert(value: number): number;\n",
        "declare namespace convert { export const label: string; }\n",
        "declare const wrong: string;\n",
        "const result = convert(1);\n",
        "const label = convert.label;\n",
        "const rejected = convert(wrong);\n",
    ));
    let function = one_node(&source, SOURCE, SyntaxKind::FunctionDeclaration);
    let namespace = one_node(&source, SOURCE, SyntaxKind::ModuleDeclaration);
    let result = initializer(&source, "result");
    let rejected = initializer(&source, "rejected");
    let access = initializer(&source, "label");
    let (_, bad_arguments) = call_parts(&source, rejected);
    for query_first in [false, true] {
        let mut context = context(&[Source {
            file: SOURCE,
            parsed: &source,
            path: "\"/project/merged-callable.ts\"",
            declaration: false,
            library: false,
        }]);
        let owner = symbol(&context, function);
        let early = query_first.then(|| {
            context
                .get_type_at_location(declaration_name(&source, function))
                .unwrap()
        });
        context.check_source_file(SOURCE).unwrap();
        let flags = SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE;
        let (callable, signatures, member) =
            assert_callable(&context, owner, &[function], namespace, flags);
        if let Some(early) = early {
            assert_eq!(early, callable);
        }
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            context
                .store()
                .signature(signatures[0])
                .unwrap()
                .resolved_return_type(),
            Some(number)
        );
        assert_call(
            &mut context,
            &source,
            result,
            owner,
            callable,
            signatures[0],
            number,
        );
        let property_type = assert_namespace_member(&mut context, &source, access, member);
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("only the string argument must fail")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.node, Some(bad_arguments[0]));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
        assert!(diagnostic.diagnostic.details.is_empty());
        assert!(diagnostic.related_information.is_empty());
        let before = state(&context);
        for _ in 0..2 {
            context.check_source_file(SOURCE).unwrap();
            context.recheck_source_file(SOURCE).unwrap();
            assert_eq!(
                assert_callable(&context, owner, &[function], namespace, flags),
                (callable, signatures.clone(), member)
            );
            assert_call(
                &mut context,
                &source,
                result,
                owner,
                callable,
                signatures[0],
                number,
            );
            assert_eq!(
                assert_namespace_member(&mut context, &source, access, member),
                property_type
            );
            assert_eq!(state(&context), before);
        }
    }
}

#[test]
fn native_merged_function_namespace_keeps_real_overloads_and_source_owners() {
    let string_library = parse_source_file("declare function select(value: string): string;\n");
    let number_library = parse_source_file(concat!(
        "declare function select(value: number): number;\n",
        "declare namespace select { const label: string; }\n",
    ));
    let source = parse_source_file(concat!(
        "declare const wrong: boolean;\n",
        "const text = select('ok');\n",
        "const number = select(1);\n",
        "const label = select.label;\n",
        "const rejected = select(wrong);\n",
    ));
    let functions = [
        one_node(
            &string_library,
            STRING_LIBRARY,
            SyntaxKind::FunctionDeclaration,
        ),
        one_node(
            &number_library,
            NUMBER_LIBRARY,
            SyntaxKind::FunctionDeclaration,
        ),
    ];
    let namespace = one_node(
        &number_library,
        NUMBER_LIBRARY,
        SyntaxKind::ModuleDeclaration,
    );
    let text = initializer(&source, "text");
    let number = initializer(&source, "number");
    let rejected = initializer(&source, "rejected");
    let access = initializer(&source, "label");
    let (_, bad_arguments) = call_parts(&source, rejected);
    for query_first in [false, true] {
        let mut context = context(&[
            Source {
                file: STRING_LIBRARY,
                parsed: &string_library,
                path: "\"/lib/lib.select-string.d.ts\"",
                declaration: true,
                library: true,
            },
            Source {
                file: NUMBER_LIBRARY,
                parsed: &number_library,
                path: "\"/lib/lib.select-number.d.ts\"",
                declaration: true,
                library: true,
            },
            Source {
                file: SOURCE,
                parsed: &source,
                path: "\"/project/use-merged-library.ts\"",
                declaration: false,
                library: false,
            },
        ]);
        let first = raw_symbol(&context, functions[0]);
        let second = raw_symbol(&context, functions[1]);
        let owner = symbol(&context, functions[0]);
        assert_ne!(first, second);
        assert_ne!(owner, first);
        assert_ne!(owner, second);
        assert_eq!(symbol(&context, functions[1]), owner);
        assert_eq!(symbol(&context, namespace), owner);
        let flags = SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE | SymbolFlags::TRANSIENT;
        assert_eq!(context.store().symbol(owner).unwrap().flags(), flags);
        let early = query_first.then(|| {
            let (callee, _) = call_parts(&source, text);
            context.get_type_at_location(callee).unwrap()
        });
        context.check_source_file(SOURCE).unwrap();
        let (callable, signatures, member) =
            assert_callable(&context, owner, &functions, namespace, flags);
        if let Some(early) = early {
            assert_eq!(early, callable);
        }
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string_type, number_type) = (bootstrap.string_type, bootstrap.number_type);
        for (&signature, expected) in signatures.iter().zip([string_type, number_type]) {
            let record = context.store().signature(signature).unwrap();
            assert_eq!(record.resolved_return_type(), Some(expected));
            assert_eq!(value_type(&context, record.parameters()[0]), expected);
        }
        assert_call(
            &mut context,
            &source,
            text,
            owner,
            callable,
            signatures[0],
            string_type,
        );
        assert_call(
            &mut context,
            &source,
            number,
            owner,
            callable,
            signatures[1],
            number_type,
        );
        let property_type = assert_namespace_member(&mut context, &source, access, member);
        let recovered = signature(&context, rejected);
        assert!(!signatures.contains(&recovered));
        assert_eq!(
            context.store().signature(recovered).unwrap().flags(),
            SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE
        );
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("only the boolean argument must fail both overloads")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2769);
        assert_eq!(diagnostic.node, Some(bad_arguments[0]));
        assert_eq!(diagnostic.range_override, None);
        // Later declaration files are tried first, so the string overload fails last.
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            concat!(
                "No overload matches this call.\n",
                "  The last overload gave the following error.\n",
                "    Argument of type 'boolean' is not assignable to parameter of type 'string'.",
            )
        );
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("the failure must point to the real last overload")
        };
        assert_eq!(related.diagnostic.code(), 2771);
        assert_eq!(related.node, Some(functions[0]));
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "The last overload is declared here."
        );
        let before = state(&context);
        for _ in 0..2 {
            context.check_source_file(SOURCE).unwrap();
            context.recheck_source_file(SOURCE).unwrap();
            assert_eq!(
                assert_callable(&context, owner, &functions, namespace, flags),
                (callable, signatures.clone(), member)
            );
            assert_call(
                &mut context,
                &source,
                text,
                owner,
                callable,
                signatures[0],
                string_type,
            );
            assert_call(
                &mut context,
                &source,
                number,
                owner,
                callable,
                signatures[1],
                number_type,
            );
            assert_eq!(
                assert_namespace_member(&mut context, &source, access, member),
                property_type
            );
            assert_eq!(signature(&context, rejected), recovered);
            assert_eq!(state(&context), before);
        }
    }
}
