use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    SymbolNodeLinks, TypeData, UnsupportedSourceSyntax,
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

fn checker_options() -> CanonicalCheckerOptions {
    CanonicalCheckerOptions {
        intrinsic: IntrinsicBootstrapOptions {
            strict_null_checks: true,
            ..IntrinsicBootstrapOptions::default()
        },
        strict_function_types: true,
        ..CanonicalCheckerOptions::default()
    }
}

fn checker_context(
    parsed: &ParseResult,
    file: FileId,
    declaration_file: bool,
    module_state: CanonicalModuleState,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/ambient-overloads.ts\""),
                CanonicalSourceLanguage::TypeScript,
                declaration_file,
                module_state,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        checker_options(),
    )
    .unwrap()
}

fn function_declarations(parsed: &ParseResult, file: FileId, expected: &str) -> Vec<NodeRef> {
    let mut declarations = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let name = function.name.and_then(|name| parsed.arena.get(name))?;
            let NodeData::Identifier(name) = &name.data else {
                return None;
            };
            (name.text == expected).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    declarations.sort_by_key(|(start, _)| *start);
    declarations
        .into_iter()
        .map(|(_, declaration)| declaration)
        .collect()
}

fn calls(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|(start, _)| *start);
    calls.into_iter().map(|(_, call)| call).collect()
}

fn call_callee(parsed: &ParseResult, file: FileId, call: NodeRef) -> NodeRef {
    let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!("the helper selected a call expression")
    };
    NodeRef::new(parsed.arena.id(), file, call.expression)
}

fn merged_symbol(
    context: &CanonicalCheckerContext<'_>,
    file: FileId,
    declaration: NodeRef,
) -> SemanticSymbolId {
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signature_for_declaration(
    context: &CanonicalCheckerContext<'_>,
    declaration: NodeRef,
) -> ts_checker::semantic::SignatureId {
    context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .expect("ambient overload declaration must own its signature")
}

fn is_type_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

#[test]
#[allow(clippy::too_many_lines)]
fn ambient_overload_groups_preserve_provenance_order_and_select_hoisted_calls_cold_and_warm() {
    for (index, (prefix, module_state)) in [
        ("", CanonicalModuleState::Script),
        ("export {};\n", CanonicalModuleState::External),
    ]
    .into_iter()
    .enumerate()
    {
        let source = format!(
            "{prefix}{}",
            concat!(
                "const before: 'literal' = pick(1);\n",
                "declare function pick(value: number): 'broad';\n",
                "declare function pick(value: 1): 'literal';\n",
                "declare function pick(value: string, suffix?: string): 'text';\n",
                "const literal: 'literal' = pick(1);\n",
                "const text: 'text' = pick('x');\n",
                "const optional: 'text' = pick('x', '!');\n",
            ),
        );
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_400 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, false, module_state);
        let declarations = function_declarations(&parsed, file, "pick");
        let [broad, _literal, _text] = declarations.as_slice() else {
            panic!("fixture must retain three ordered overload declarations")
        };
        let owner = merged_symbol(&context, file, *broad);
        assert!(
            declarations
                .iter()
                .all(|declaration| merged_symbol(&context, file, *declaration) == owner)
        );
        let calls = calls(&parsed, file);
        let [before, literal_call, text_call, optional_call] = calls.as_slice() else {
            panic!("fixture must retain four calls")
        };

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
        let callable = context
            .store()
            .value_symbol_links(owner)
            .and_then(|links| links.resolved_type)
            .expect("overload owner must retain one callable type");
        let record = context.store().type_payload(callable).unwrap();
        let TypeData::Object(object) = record.data() else {
            panic!("source overload owner must retain an anonymous object")
        };
        let signatures = declarations
            .iter()
            .map(|declaration| signature_for_declaration(&context, *declaration))
            .collect::<Vec<_>>();
        assert_eq!(record.flags(), TypeFlags::OBJECT);
        assert_eq!(
            record.object_flags(),
            ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        );
        assert_eq!(record.symbol(), Some(owner));
        assert_eq!(
            object.structured.signatures.as_deref(),
            Some(signatures.as_slice())
        );
        assert_eq!(object.structured.call_signature_count, signatures.len());
        for (declaration, signature) in declarations.iter().zip(&signatures) {
            let signature_record = context.store().signature(*signature).unwrap();
            assert_eq!(signature_record.declaration(), Some(*declaration));
            assert_eq!(signature_record.type_parameters(), &[]);
            assert_eq!(signature_record.target(), None);
            assert_eq!(signature_record.mapper(), None);
        }
        let selected = |call| {
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
        };
        assert_eq!(selected(*before), Some(signatures[1]));
        assert_eq!(selected(*literal_call), Some(signatures[1]));
        assert_eq!(selected(*text_call), Some(signatures[2]));
        assert_eq!(selected(*optional_call), Some(signatures[2]));
        for call in &calls {
            let callee = call_callee(&parsed, file, *call);
            assert_eq!(
                context.store().symbol_node_links(callee),
                Some(&SymbolNodeLinks {
                    resolved_symbol: Some(owner),
                })
            );
            assert!(
                context
                    .store()
                    .type_node_links(*call)
                    .and_then(|links| links.resolved_type)
                    .is_some()
            );
        }
        let text_parameters = context
            .store()
            .signature(signatures[2])
            .unwrap()
            .parameters()
            .to_vec();
        let [required, optional] = text_parameters.as_slice() else {
            panic!("third overload must retain its required and optional parameters")
        };
        assert_eq!(
            context
                .store()
                .signature(signatures[2])
                .unwrap()
                .min_argument_count(),
            1
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(*required)
                .and_then(|links| links.resolved_type)
                .map(|type_| context.type_to_string(type_).unwrap()),
            Some("string".to_owned())
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(*optional)
                .and_then(|links| links.resolved_type)
                .map(|type_| context.type_to_string(type_).unwrap()),
            Some("string | undefined".to_owned())
        );

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().relation_state_snapshot(),
            context.store().value_symbol_links(owner).cloned(),
            declarations
                .iter()
                .map(|declaration| context.store().signature_links(*declaration).cloned())
                .collect::<Vec<_>>(),
            [*before, *literal_call, *text_call, *optional_call].map(|call| {
                (
                    context.store().type_node_links(call).cloned(),
                    context.store().signature_links(call).cloned(),
                )
            }),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().relation_state_snapshot(),
                context.store().value_symbol_links(owner).cloned(),
                declarations
                    .iter()
                    .map(|declaration| context.store().signature_links(*declaration).cloned())
                    .collect::<Vec<_>>(),
                [*before, *literal_call, *text_call, *optional_call].map(|call| {
                    (
                        context.store().type_node_links(call).cloned(),
                        context.store().signature_links(call).cloned(),
                    )
                }),
            ),
            warm
        );
    }
}

#[test]
fn later_bad_overload_group_rejects_all_overload_publication() {
    for (index, source) in [
        concat!(
            "declare function ready(value: number): number;\n",
            "declare function ready(value: string): string;\n",
            "declare function bad<T>(value: T): T;\n",
            "declare function bad<T>(value: T, other: T): T;\n",
        ),
        concat!(
            "declare function ready(value: number): number;\n",
            "declare function ready(value: string): string;\n",
            "declare function bad(...values: number[]): number;\n",
            "declare function bad(value: string): string;\n",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_410 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, false, CanonicalModuleState::Script);
        let ready = function_declarations(&parsed, file, "ready");
        let ready_owner = merged_symbol(&context, file, ready[0]);

        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(_) | SourceCheckError::DeclaredType(_))
        ));

        assert!(context.store().value_symbol_links(ready_owner).is_none());
        assert!(
            ready
                .iter()
                .all(|declaration| { context.store().signature_links(*declaration).is_none() })
        );
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }
}

#[test]
fn later_bad_callable_provider_keeps_the_ready_overload_cold_across_retries() {
    let ready = concat!(
        "declare function ready(value: number): number;\n",
        "declare function ready(value: string): string;\n",
    );
    for (index, source) in [
        format!(
            "{ready}{}",
            concat!(
                "declare function bad(",
                "this: object, value: number",
                "): number;\n",
            )
        ),
        format!(
            "{ready}{}",
            concat!(
                "const bad = (",
                "{ value }: { value: number }",
                "): number => 1;\n",
            )
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_413 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, false, CanonicalModuleState::Script);
        let declarations = function_declarations(&parsed, file, "ready");
        let [first, second] = declarations.as_slice() else {
            panic!("fixture must retain the ready overload group")
        };
        let ready_owner = merged_symbol(&context, file, *first);
        assert_eq!(ready_owner, merged_symbol(&context, file, *second));
        let cold = (context.store().type_len(), context.store().signature_len());

        for _ in 0..2 {
            assert!(
                matches!(
                    context.check_source_file(file),
                    Err(SourceCheckError::DeclaredType(_)
                        | SourceCheckError::Unsupported(_)
                        | SourceCheckError::Arrow(_))
                ),
                "later provider escaped its typed boundary: {source}",
            );
            assert_eq!(
                (context.store().type_len(), context.store().signature_len(),),
                cold,
            );
            assert!(context.store().value_symbol_links(ready_owner).is_none());
            assert!(
                declarations
                    .iter()
                    .all(|declaration| { context.store().signature_links(*declaration).is_none() })
            );
            assert!(context.diagnostics().is_empty());
            assert!(!is_type_checked(&context, file));
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn failed_multi_overloads_keep_marked_recovery_out_of_public_candidates() {
    use ts_checker::semantic::signatures::SignatureFlags;
    let parsed = parse_source_file(concat!(
        "declare function parse(value: number, radix: number): string;\n",
        "declare function parse(value: string): number;\n",
        "const good = parse('1');\n",
        "const bad = parse(true);\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_412);
    let mut context = checker_context(&parsed, file, false, CanonicalModuleState::Script);
    let declarations = function_declarations(&parsed, file, "parse");
    let calls = calls(&parsed, file);
    let [good, bad] = calls.as_slice() else {
        panic!("fixture must retain one successful and one failed call")
    };

    context.check_source_file(file).unwrap();

    assert!(declarations.iter().all(|declaration| {
        context
            .store()
            .signature_links(*declaration)
            .is_some_and(|links| links.resolved_signature.signature().is_some())
    }));
    assert!(context.store().signature_links(*good).is_some());
    assert!(context.store().type_node_links(*good).is_some());
    let visible = declarations
        .iter()
        .map(|declaration| signature_for_declaration(&context, *declaration))
        .collect::<Vec<_>>();
    let recovered = signature_for_declaration(&context, *bad);
    assert!(!visible.contains(&recovered));
    let record = context.store().signature(recovered).unwrap();
    assert_eq!(
        record.flags(),
        SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE
    );
    assert_eq!(record.declaration(), Some(declarations[0]));
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.parameters().len(), 2);
    let source_parameters = context.store().signature(visible[0]).unwrap().parameters();
    for (parameter, source) in record.parameters().iter().zip(source_parameters) {
        assert_ne!(parameter, source);
        let links = context.store().value_symbol_links(*parameter).unwrap();
        assert_eq!(links.target, Some(*source));
        assert_eq!(
            context.store().symbol(*parameter).unwrap().declarations(),
            context.store().symbol(*source).unwrap().declarations()
        );
    }
    let parameter_types = record
        .parameters()
        .iter()
        .map(|parameter| {
            let type_ = context
                .store()
                .value_symbol_links(*parameter)
                .unwrap()
                .resolved_type
                .unwrap();
            context.type_to_string(type_).unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(parameter_types, ["string | number", "number"]);
    let never = context.store().intrinsic_bootstrap().unwrap().never_type;
    assert_eq!(record.resolved_return_type(), Some(never));
    assert_eq!(
        context.store().type_node_links(*bad).unwrap().resolved_type,
        Some(never)
    );
    let callable = context
        .get_type_at_location(call_callee(&parsed, file, *bad))
        .unwrap();
    let members = match context.store().type_payload(callable).unwrap().data() {
        TypeData::Object(data) => &data.structured,
        _ => panic!("expected the source callable's structured type"),
    };
    assert_eq!(members.signatures.as_deref(), Some(visible.as_slice()));
    assert_eq!(members.call_signature_count, visible.len());
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("only the one matching arity reports an argument error")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'boolean' is not assignable to parameter of type 'string'."
    );
    let argument = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::TrueKeyword).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap();
    assert_eq!(diagnostic.node, Some(argument));
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
    assert!(is_type_checked(&context, file));
    let cold = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().mapper_len(),
        context.store().symbol_len(),
        context.store().signature_links(*good).cloned(),
        context.store().type_node_links(*good).cloned(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().signature_links(*good).cloned(),
            context.store().type_node_links(*good).cloned(),
            context.diagnostics().clone()
        ),
        cold
    );
    assert_eq!(signature_for_declaration(&context, *bad), recovered);
    assert_eq!(
        declarations
            .iter()
            .map(|declaration| signature_for_declaration(&context, *declaration))
            .collect::<Vec<_>>(),
        visible
    );
}

#[test]
fn declaration_file_ambient_overloads_publish_signatures_in_source_order() {
    let parsed = parse_source_file(concat!(
        "declare function choose(value: number): number;",
        "declare function choose(value: string): string;",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_419);
    let mut context = checker_context(&parsed, file, true, CanonicalModuleState::Script);
    let declarations = function_declarations(&parsed, file, "choose");
    let owner = merged_symbol(&context, file, declarations[0]);

    context.check_source_file(file).unwrap();

    let signatures = declarations
        .iter()
        .map(|declaration| signature_for_declaration(&context, *declaration))
        .collect::<Vec<_>>();
    assert_eq!(signatures.len(), 2);
    assert_ne!(signatures[0], signatures[1]);
    assert!(context.store().value_symbol_links(owner).is_some());
    assert!(context.diagnostics().is_empty());
    assert!(is_type_checked(&context, file));

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        signatures,
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            declarations
                .iter()
                .map(|declaration| signature_for_declaration(&context, *declaration))
                .collect::<Vec<_>>(),
        ),
        warm,
    );
}

#[test]
fn overload_forms_outside_the_exact_leaf_remain_typed_boundaries() {
    for (index, (source, declaration_file, module_state)) in [
        (
            "export declare function f(value: number): number;\
             export declare function f(value: string): string;",
            false,
            CanonicalModuleState::External,
        ),
        (
            "declare function f<T>(value: T): T;\
             declare function f<T>(value: T, other: T): T;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "function f(value: number): number;\
             function f(value: number): number { return value; }",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function f(value: number): number;\
             function f(value: string): string { return value; }",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function f(...value: number[]): number;\
             declare function f(value: string): string;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function f(value = 1): number;\
             declare function f(value: string): string;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function f(this: object, value: number): number;\
             declare function f(value: string): string;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function f({ value }: { value: number }): number;\
             declare function f(value: string): string;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function f(value?: number, required: string): number;\
             declare function f(value: string): string;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function f(value: number): number;\
             declare function f(value: string): string;\
             var f: unknown;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare namespace N {\
                 function f(value: number): number;\
                 function f(value: string): string;\
             }",
            false,
            CanonicalModuleState::Script,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_420 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, declaration_file, module_state);
        assert!(
            matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(_))
            ),
            "fixture escaped its typed boundary: {source}",
        );
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }
}

#[test]
fn global_script_overloads_spanning_files_are_a_typed_boundary() {
    let first = parse_source_file("declare function shared(value: number): number;");
    let second = parse_source_file("declare function shared(value: string): string;");
    assert!(first.diagnostics.is_empty());
    assert!(second.diagnostics.is_empty());
    let first_file = FileId::new(2_440);
    let second_file = FileId::new(2_441);
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path) in [
        (&first, first_file, "\"/project/first.ts\""),
        (&second, second_file, "\"/project/second.ts\""),
    ] {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(first_file, &first.arena), (second_file, &second.arena)]
            .into_iter()
            .collect(),
        checker_options(),
    )
    .unwrap();

    assert!(matches!(
        context.check_source_file(first_file),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Function(_)
        ))
    ));
    assert!(context.diagnostics().is_empty());
    assert!(!is_type_checked(&context, first_file));
}
