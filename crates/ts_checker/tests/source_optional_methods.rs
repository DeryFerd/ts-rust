use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

fn context(
    parsed: &ParseResult,
    file: FileId,
    intrinsic: IntrinsicBootstrapOptions,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/optional-methods.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn method(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    name: &str,
) -> SemanticSymbolId {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(method.name)?.data else {
                return None;
            };
            (identifier.text == name).then(|| {
                context
                    .file(file)
                    .unwrap()
                    .1
                    .symbol(NodeRef::new(parsed.arena.id(), file, node))
                    .unwrap()
            })
        })
        .unwrap()
}

fn callable(
    context: &CanonicalCheckerContext<'_>,
    method: SemanticSymbolId,
    strict: bool,
    exact: bool,
) -> TypeId {
    let store = context.store();
    let value = store
        .value_symbol_links(method)
        .unwrap()
        .resolved_type
        .unwrap();
    if !strict {
        return value;
    }
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    let sentinel = if exact {
        bootstrap.missing_type
    } else {
        bootstrap.undefined_type
    };
    let TypeData::Union(union) = store.type_payload(value).unwrap().data() else {
        panic!("a strict optional method has a union value")
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&sentinel));
    *union
        .union
        .types
        .iter()
        .find(|type_| **type_ != sentinel)
        .unwrap()
}

fn call_signature(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
        panic!("a method callable is an object")
    };
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("the method has one signature")
    };
    *signature
}

#[test]
fn optional_methods_preserve_callable_values_and_expanded_parameter_unions() {
    for (strict, exact) in [(false, false), (true, false), (true, true)] {
        let parsed =
            parse_source_file("interface Shape { read?(value?: string | number): number; }");
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(4_220);
        let mut context = context(
            &parsed,
            file,
            IntrinsicBootstrapOptions {
                strict_null_checks: strict,
                exact_optional_property_types: exact,
            },
        );
        let method = method(&parsed, file, &context, "read");
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        assert_eq!(
            context.store().symbol(method).unwrap().flags(),
            SymbolFlags::METHOD | SymbolFlags::OPTIONAL
        );
        let callable = callable(&context, method, strict, exact);
        let record = context.store().type_payload(callable).unwrap();
        assert_eq!(record.symbol(), Some(method));
        let signature = call_signature(&context, callable);
        let parameters = context.store().signature(signature).unwrap();
        assert_eq!(parameters.min_argument_count(), 0);
        let parameter = parameters.parameters()[0];
        let parameter_type = context
            .store()
            .value_symbol_links(parameter)
            .unwrap()
            .resolved_type
            .unwrap();
        let TypeData::Union(union) = context.store().type_payload(parameter_type).unwrap().data()
        else {
            panic!("the parameter retains its annotation union")
        };
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let mut expected = vec![bootstrap.string_type, bootstrap.number_type];
        if strict {
            expected.push(bootstrap.undefined_type);
        }
        expected.sort_unstable();
        assert_eq!(union.union.types, expected);
        let number = bootstrap.number_type;
        assert_eq!(
            context.get_return_type_of_signature(signature).unwrap(),
            number
        );
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len()
            ),
            warm
        );
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn generic_optional_methods_compose_with_rest_binding_signatures() {
    let parsed = parse_source_file(concat!(
        "interface I<T> { ",
        "next(...[value]: [] | [T]): { value: T }; ",
        "return?(value?: T): { value: T }; ",
        "throw?(reason?: any): { value: T }; }",
    ));
    assert!(parsed.diagnostics.is_empty());
    let file = FileId::new(4_221);
    let mut context = context(
        &parsed,
        file,
        IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: true,
        },
    );
    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    for name in ["return", "throw"] {
        let symbol = method(&parsed, file, &context, name);
        let callable = callable(&context, symbol, true, true);
        let signature = call_signature(&context, callable);
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.min_argument_count(), 0);
        let expected_return = record.resolved_return_type().unwrap();
        assert_eq!(
            context.get_return_type_of_signature(signature).unwrap(),
            expected_return
        );
    }
    let next = method(&parsed, file, &context, "next");
    let value = context
        .store()
        .value_symbol_links(next)
        .unwrap()
        .resolved_type
        .unwrap();
    let signature = context
        .store()
        .signature(call_signature(&context, value))
        .unwrap();
    assert_eq!(signature.min_argument_count(), 0);
    assert_eq!(
        context
            .store()
            .symbol(signature.parameters()[0])
            .unwrap()
            .name(),
        EscapedName::source("__0").as_ref()
    );
    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len()
        ),
        warm
    );
    assert!(context.diagnostics().is_empty());
}

#[test]
fn optional_method_overloads_in_type_literals_retain_signatures_and_return_types() {
    let parsed = parse_source_file(concat!(
        "type Shape = { ",
        "read?(value: string): number; ",
        "read?(value?: number): string; };",
    ));
    assert!(parsed.diagnostics.is_empty());
    let file = FileId::new(4_222);
    let mut context = context(
        &parsed,
        file,
        IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        },
    );
    let node = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::TypeLiteralNode(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap();
    let owner = context.get_type_from_type_node(node).unwrap();
    let symbol = method(&parsed, file, &context, "read");
    let callable = callable(&context, symbol, true, false);
    let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
        panic!("the optional overload set has a callable object")
    };
    let signatures = object.structured.signatures.clone().unwrap();
    assert_eq!(signatures.len(), 2);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let returns = [bootstrap.number_type, bootstrap.string_type];
    for ((signature, expected_return), minimum) in signatures.iter().zip(returns).zip([1, 0]) {
        assert_eq!(
            context
                .store()
                .signature(*signature)
                .unwrap()
                .min_argument_count(),
            minimum
        );
        assert_eq!(
            context.get_return_type_of_signature(*signature).unwrap(),
            expected_return
        );
    }
    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
    );
    assert_eq!(context.get_type_from_type_node(node).unwrap(), owner);
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len()
        ),
        warm
    );
    assert!(context.diagnostics().is_empty());
}
