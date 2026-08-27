use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, TypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(4_520);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
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
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
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
fn unsupported_alias_instantiation_does_not_publish_a_callable_or_grow_on_retry() {
    let parsed = parse_source_file(concat!(
        "type Alias<T> = { value: T }; ",
        "declare function make<T>(value: Alias<T>): T;",
    ));
    let mut context = context(&parsed);
    assert!(matches!(
        context.check_source_file(FILE),
        Err(SourceCheckError::DeclaredType(_))
    ));
    let before = counts(&context);
    assert!(matches!(
        context.check_source_file(FILE),
        Err(SourceCheckError::DeclaredType(_))
    ));
    assert_eq!(counts(&context), before);
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
    assert!(context.store().value_symbol_links(owner).is_none());
    assert!(context.store().signature_links(declaration).is_none());
}

#[test]
fn generic_alias_source_boundary_keeps_recursive_and_const_forms_unsupported() {
    for source in [
        "interface Array<T> {} interface ReadonlyArray<T> {} type Alias<T> = T[]; declare function f<T>(value: Alias<T>): void;",
        "type Alias<T> = Alias<T>[]; declare function f<T>(value: Alias<T>): void;",
        "type First<T> = Second<T>; type Second<T> = First<T>[]; declare function f<T>(value: First<T>): void;",
        "type Alias<T> = T; declare function f<const T>(value: Alias<T>): void;",
        "type Alias<T> = T; const f = <T>(value: Alias<T>): Alias<T> => value;",
        "type Alias<T> = T; interface Box<T> { value: T } declare function f<T>(value: Box<Alias<T>>): T;",
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
