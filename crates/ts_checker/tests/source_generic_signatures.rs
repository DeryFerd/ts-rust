use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, SourceFunctionUnsupported,
    UnsupportedSourceSyntax,
};
use ts_parser::parse_source_file;

#[test]
fn generic_identity_body_parameter_read_checks_cold_and_warm() {
    let parsed = parse_source_file("function identity<T>(value: T): T { return value; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();

    context.check_source_file(file).unwrap();
    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
}

#[test]
fn ordered_generic_parameters_constraints_and_defaults_check_cold_and_warm() {
    let parsed = parse_source_file(
        "function first<T, U>(left: T, right: U): T { return left; }\n\
         function dependent<T extends string, U extends T = T>(value: U): U { return value; }\n\
         function make<T = string>(): string { return ''; }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/ordered-generics.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();

    context.check_source_file(file).unwrap();
    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
}

#[test]
fn duplicate_type_parameter_names_fall_back_without_publication() {
    let parsed = parse_source_file("function duplicate<T, T>(value: T): T { return value; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let source = parsed.arena.get(parsed.source_file).unwrap();
    let NodeData::SourceFile(source) = &source.data else {
        panic!("expected source file")
    };
    let declaration_id = source.statements.nodes[0];
    let declaration_record = parsed.arena.get(declaration_id).unwrap();
    let NodeData::FunctionDeclaration(function) = &declaration_record.data else {
        panic!("expected function declaration")
    };
    let type_parameter_ids = function
        .type_parameters
        .as_ref()
        .expect("expected type parameters")
        .nodes
        .clone();
    let declaration = NodeRef::new(parsed.arena.id(), file, declaration_id);

    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/duplicate-generics.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();
    let (owner, type_parameter_symbols) = {
        let (_, bound) = context.file(file).unwrap();
        (
            bound.symbol(declaration).unwrap(),
            type_parameter_ids
                .iter()
                .map(|node| {
                    bound
                        .symbol(NodeRef::new(parsed.arena.id(), file, *node))
                        .unwrap()
                })
                .collect::<Vec<_>>(),
        )
    };
    let before = (context.store().type_len(), context.store().signature_len());

    for _ in 0..2 {
        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::Callable(_))
            ))
        ));
        assert_eq!(
            (context.store().type_len(), context.store().signature_len()),
            before
        );
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(context.store().signature_links(declaration).is_none());
        assert!(
            type_parameter_symbols
                .iter()
                .all(|symbol| context.store().declared_type_links(*symbol).is_none())
        );
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn empty_generic_functions_infer_void_and_validate_explicit_type_argument_counts() {
    let parsed = parse_source_file(concat!(
        "function callback<First, Second>() {}\n",
        "callback<number>();\n",
        "callback<number, string>();\n",
        "callback<number, string, boolean>();\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/empty-generic.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();

    context.check_source_file(file).unwrap();

    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2558, 2558],
    );
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(&record.data, NodeData::FunctionDeclaration(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap();
    let signature = context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    assert_eq!(
        context
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type(),
        Some(context.store().intrinsic_bootstrap().unwrap().void_type),
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}
