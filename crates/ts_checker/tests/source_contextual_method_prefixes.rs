use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_140);
const LIBRARY: FileId = FileId::new(203_141);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (FILE, parsed, "\"/project/contextual-method-prefixes.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file == LIBRARY,
                    file == LIBRARY,
                    if file == LIBRARY {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
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

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)))
        .collect::<Vec<_>>();
    assert_eq!(nodes.len(), 1, "expected one {kind:?}");
    nodes[0]
}

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::VariableDeclaration(declaration) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(declaration.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    node(parsed, id),
                    node(parsed, declaration.name),
                    node(parsed, declaration.initializer.unwrap()),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let bound = checker.file(FILE).unwrap().1;
    let raw = bound.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn callable_signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the actual callable object");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let signatures = object.structured.signatures.as_deref().unwrap();
    assert_eq!(signatures.len(), 1);
    signatures[0]
}

fn assert_union(checker: &CanonicalCheckerContext<'_>, type_: TypeId, expected: &[TypeId]) {
    let TypeData::Union(union) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected a canonical union");
    };
    assert_eq!(union.union.types.len(), expected.len());
    for member in expected {
        assert!(union.union.types.contains(member));
    }
}

#[derive(Clone, Copy)]
enum Case {
    Number,
    InvalidLocal,
    Literal,
}

#[derive(Debug, Eq, PartialEq)]
struct MethodState {
    method_type: TypeId,
    method_signature: SignatureId,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    return_type: TypeId,
    generic_context: TypeId,
    raw_context: TypeId,
    context_callable: TypeId,
    context_signature: SignatureId,
    context_member: SemanticSymbolId,
}

fn method_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    case: Case,
) -> MethodState {
    let method = only(parsed, SyntaxKind::MethodDeclaration);
    let NodeData::MethodDeclaration(declaration) = &parsed.arena.get(method.node).unwrap().data
    else {
        unreachable!();
    };
    assert_eq!(declaration.parameters.nodes.len(), 2);
    let method_owner = symbol(checker, method);
    let method_type = checker.get_type_at_location(method).unwrap();
    assert_eq!(
        checker.get_type_at_location(node(parsed, declaration.name)),
        Ok(method_type)
    );
    assert_eq!(
        checker.get_symbol_at_location(node(parsed, declaration.name)),
        Ok(Some(method_owner))
    );
    let object = node(
        parsed,
        parsed.arena.get(method.node).unwrap().parent.unwrap(),
    );
    assert_eq!(
        parsed.arena.get(object.node).unwrap().kind,
        SyntaxKind::ObjectLiteralExpression
    );
    let owner = checker.store().symbol(method_owner).unwrap();
    assert_eq!(owner.flags(), SymbolFlags::METHOD);
    assert_eq!(owner.parent(), Some(symbol(checker, object)));
    assert_eq!(owner.declarations(), Some(&[method][..]));
    assert_eq!(owner.value_declaration(), Some(method));
    assert_eq!(
        checker.store().type_payload(method_type).unwrap().symbol(),
        Some(method_owner)
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(method_owner)
            .unwrap()
            .resolved_type,
        Some(method_type)
    );

    let payload = only(parsed, SyntaxKind::TypeAliasDeclaration);
    let payload_type = checker
        .get_declared_type_of_symbol(symbol(checker, payload))
        .unwrap();
    let (string_type, symbol_type, undefined_type, any_type, number_type) = {
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        (
            bootstrap.string_type,
            bootstrap.es_symbol_type,
            bootstrap.undefined_type,
            bootstrap.any_type,
            bootstrap.number_type,
        )
    };
    let mut parameters = Vec::new();
    for &id in &declaration.parameters.nodes {
        let parameter = node(parsed, id);
        let NodeData::ParameterDeclaration(data) = &parsed.arena.get(id).unwrap().data else {
            panic!("expected an actual method parameter");
        };
        assert_eq!(parsed.arena.get(id).unwrap().parent, Some(method.node));
        let owner = symbol(checker, parameter);
        let type_ = checker
            .get_type_at_location(node(parsed, data.name))
            .unwrap();
        assert_eq!(checker.get_type_at_location(parameter), Ok(type_));
        assert_eq!(
            checker.get_symbol_at_location(node(parsed, data.name)),
            Ok(Some(owner))
        );
        let record = checker.store().symbol(owner).unwrap();
        assert_eq!(record.declarations(), Some(&[parameter][..]));
        assert_eq!(record.value_declaration(), Some(parameter));
        assert_eq!(
            checker
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type,
            Some(type_)
        );
        parameters.push((owner, type_));
    }
    assert_ne!(parameters[0].0, parameters[1].0);
    assert_eq!(parameters[0].1, payload_type);
    assert_union(checker, parameters[1].1, &[string_type, symbol_type]);

    let method_signature = callable_signature(checker, method_type);
    assert_eq!(
        checker
            .store()
            .signature_links(method)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(method_signature)
    );
    let return_type = checker
        .get_return_type_of_signature(method_signature)
        .unwrap();
    let signature = checker.store().signature(method_signature).unwrap();
    assert_eq!(signature.declaration(), Some(method));
    assert_eq!(signature.flags(), SignatureFlags::NONE);
    assert_eq!(signature.min_argument_count(), 2);
    assert_eq!(signature.parameters(), &[parameters[0].0, parameters[1].0]);
    assert!(signature.type_parameters().is_empty());
    assert_eq!(signature.this_parameter(), None);
    assert_eq!(signature.target(), None);
    assert_eq!(signature.mapper(), None);
    assert_eq!(signature.resolved_return_type(), Some(return_type));

    let (_, reader_name, initializer) = variable(parsed, "reader");
    assert_eq!(initializer, object);
    let reader = only(parsed, SyntaxKind::InterfaceDeclaration);
    let reader_owner = symbol(checker, reader);
    let reader_target = checker.get_declared_type_of_symbol(reader_owner).unwrap();
    let generic_context = checker.get_type_at_location(reader_name).unwrap();
    let TypeData::Reference(reference) = checker
        .store()
        .type_payload(generic_context)
        .unwrap()
        .data()
    else {
        panic!("expected the actual Reader<Payload> context");
    };
    assert_eq!(reference.object.target, Some(reader_target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[payload_type][..])
    );

    let (_, _, contextual_read) = variable(parsed, "contextualRead");
    let NodeData::PropertyAccessExpression(access) =
        &parsed.arena.get(contextual_read.node).unwrap().data
    else {
        panic!("expected the real contextual property read");
    };
    let context_member = checker
        .get_symbol_at_location(node(parsed, access.name))
        .unwrap()
        .unwrap();
    let raw_context = checker.get_type_at_location(contextual_read).unwrap();
    let TypeData::Union(optional) = checker.store().type_payload(raw_context).unwrap().data()
    else {
        panic!("the optional method must keep its raw union type");
    };
    assert_eq!(optional.union.types.len(), 2);
    assert!(optional.union.types.contains(&undefined_type));
    let context_callable = *optional
        .union
        .types
        .iter()
        .find(|&&type_| type_ != undefined_type)
        .unwrap();
    assert_ne!(context_callable, method_type);
    let context_signature = callable_signature(checker, context_callable);
    let context_return = checker
        .get_return_type_of_signature(context_signature)
        .unwrap();
    let context_declaration = only(parsed, SyntaxKind::MethodSignature);
    let context_owner = symbol(checker, context_declaration);
    let owner = checker.store().symbol(context_owner).unwrap();
    assert!(
        owner
            .flags()
            .contains(SymbolFlags::METHOD | SymbolFlags::OPTIONAL)
    );
    assert_eq!(owner.parent(), Some(reader_owner));
    assert_eq!(owner.declarations(), Some(&[context_declaration][..]));
    let mut declared_parameters = parsed
        .arena
        .iter()
        .filter(|(_, record)| {
            record.kind == SyntaxKind::Parameter && record.parent == Some(context_declaration.node)
        })
        .map(|(id, record)| (record.range.start, node(parsed, id)))
        .collect::<Vec<_>>();
    declared_parameters.sort_by_key(|&(start, _)| start);
    assert_eq!(declared_parameters.len(), 3);
    let declared_symbols = declared_parameters
        .iter()
        .map(|&(_, parameter)| symbol(checker, parameter))
        .collect::<Vec<_>>();
    let signature = checker.store().signature(context_signature).unwrap();
    assert_eq!(signature.declaration(), Some(context_declaration));
    assert_eq!(signature.parameters().len(), 3);
    assert_eq!(signature.min_argument_count(), 3);
    assert!(signature.type_parameters().is_empty());
    assert_eq!(signature.this_parameter(), None);
    assert!(!signature.has_rest_parameter());
    assert!(signature.target().is_some());
    assert!(signature.mapper().is_some());
    assert_ne!(context_signature, method_signature);
    let target = checker
        .store()
        .signature(signature.target().unwrap())
        .unwrap();
    assert_eq!(target.declaration(), Some(context_declaration));
    assert_eq!(target.parameters(), declared_symbols);

    let (local, local_name, local_initializer) = variable(parsed, "result");
    let local_owner = symbol(checker, local);
    let local_type = if matches!(case, Case::InvalidLocal) {
        string_type
    } else {
        number_type
    };
    assert_eq!(checker.get_type_at_location(local_name), Ok(local_type));
    assert_eq!(
        checker.get_type_at_location(local_initializer),
        Ok(number_type)
    );
    assert_eq!(
        checker.get_symbol_at_location(local_name),
        Ok(Some(local_owner))
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(local_owner)
            .unwrap()
            .resolved_type,
        Some(local_type)
    );
    let method_range = parsed.arena.get(method.node).unwrap().range;
    for (id, record) in parsed.arena.iter() {
        if record.range.start < method_range.start || record.range.end > method_range.end {
            continue;
        }
        let NodeData::Identifier(name) = &record.data else {
            continue;
        };
        let expected = match name.text.as_str() {
            "value" => parameters[0].0,
            "key" => parameters[1].0,
            "result" => local_owner,
            _ => continue,
        };
        assert_eq!(
            checker.get_symbol_at_location(node(parsed, id)),
            Ok(Some(expected))
        );
    }
    match case {
        Case::Number => {
            assert_eq!(context_return, any_type);
            assert_eq!(return_type, number_type);
        }
        Case::InvalidLocal => {
            assert_eq!(context_return, any_type);
            assert_union(checker, return_type, &[number_type, string_type]);
        }
        Case::Literal => {
            assert_eq!(checker.type_to_string(return_type).unwrap(), "\"ok\"");
            assert_eq!(return_type, context_return);
            let TypeData::Literal(literal) =
                checker.store().type_payload(return_type).unwrap().data()
            else {
                panic!("expected the inferred literal return");
            };
            assert_eq!(literal.regular_type, return_type);
            let returned = parsed
                .arena
                .iter()
                .filter_map(|(_, record)| match &record.data {
                    NodeData::ReturnStatement(statement) => statement.expression,
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(returned.len(), 2);
            for expression in returned {
                let expression_type = checker
                    .get_type_at_location(node(parsed, expression))
                    .unwrap();
                let TypeData::Literal(literal) = checker
                    .store()
                    .type_payload(expression_type)
                    .unwrap()
                    .data()
                else {
                    panic!("expected the real literal expression");
                };
                assert_eq!(literal.regular_type, return_type);
            }
        }
    }
    MethodState {
        method_type,
        method_signature,
        parameters,
        return_type,
        generic_context,
        raw_context,
        context_callable,
        context_signature,
        context_member,
    }
}

fn assert_diagnostics(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult, case: Case) {
    let actual = checker.diagnostics().as_slice();
    if !matches!(case, Case::InvalidLocal) {
        assert!(actual.is_empty(), "{actual:?}");
        return;
    }
    assert_eq!(actual.len(), 1, "{actual:?}");
    let (_, name, _) = variable(parsed, "result");
    let diagnostic = &actual[0];
    assert_eq!(diagnostic.node, Some(name));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
    assert!(diagnostic.diagnostic.details.is_empty());
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'number' is not assignable to type 'string'."
    );
    assert!(diagnostic.related_information.is_empty());
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.type_resolution_len(),
        ],
        parsed
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
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(owner, _)| (owner, store.value_symbol_links(owner).cloned()))
            .collect::<Vec<_>>(),
        store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        store.relation_state_snapshot(),
        checker.file(FILE).unwrap().1.flow_graph().clone(),
        checker.diagnostics().clone(),
    )
}

fn check(case: Case) {
    let local_type = if matches!(case, Case::InvalidLocal) {
        "string"
    } else {
        "number"
    };
    let (context_return, returns) = if matches!(case, Case::Literal) {
        (
            "\"ok\"",
            "if (key === \"count\") return \"ok\";\n    return \"ok\";",
        )
    } else {
        (
            "any",
            "if (key === \"count\") return result;\n    return value.count;",
        )
    };
    let source = format!(
        "export {{}};\n\
         type Payload = {{ count: number; }};\n\
         interface Reader<T> {{ read?(value: T, key: string | symbol, receiver: unknown): {context_return}; }}\n\
         const reader: Reader<Payload> = {{\n\
           read(value, key) {{\n\
             const result: {local_type} = value.count;\n\
             {returns}\n\
           }}\n\
         }};\n\
         const contextualRead = reader.read;\n"
    );
    let parsed = parse_source_file(&source);
    let library = parse_source_file(ES5);
    let method = only(&parsed, SyntaxKind::MethodDeclaration);
    let NodeData::MethodDeclaration(data) = &parsed.arena.get(method.node).unwrap().data else {
        unreachable!();
    };
    let NodeData::ParameterDeclaration(value) =
        &parsed.arena.get(data.parameters.nodes[0]).unwrap().data
    else {
        unreachable!();
    };
    let first_query = node(&parsed, value.name);
    for source_first in [false, true] {
        let mut checker = context(&parsed, &library);
        if source_first {
            checker.check_source_file(FILE).unwrap();
        }
        let first_type = checker.get_type_at_location(first_query).unwrap();
        checker.check_source_file(FILE).unwrap();
        let state = method_state(&mut checker, &parsed, case);
        assert_eq!(first_type, state.parameters[0].1);
        assert_diagnostics(&checker, &parsed, case);
        let before = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(method_state(&mut checker, &parsed, case), state);
            assert_diagnostics(&checker, &parsed, case);
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

#[test]
fn optional_generic_method_context_keeps_two_real_parameters_and_branch_returns() {
    check(Case::Number);
}

#[test]
fn contextual_method_prefix_keeps_the_local_assignment_error_under_any_return() {
    check(Case::InvalidLocal);
}

#[test]
fn contextual_method_statement_return_keeps_the_literal_context() {
    check(Case::Literal);
}
