use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    SymbolNodeLinks, TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

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
                EscapedName::source("\"/project/ambient-functions.ts\""),
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
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn function_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let name = function.name.and_then(|name| parsed.arena.get(name))?;
            let NodeData::Identifier(name) = &name.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing function {expected}"))
}

fn first_function_parameter(parsed: &ParseResult, file: FileId, declaration: NodeRef) -> NodeRef {
    let NodeData::FunctionDeclaration(function) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!("the helper selected a function declaration")
    };
    let parameter = function
        .parameters
        .nodes
        .first()
        .expect("fixture function must have a parameter");
    NodeRef::new(parsed.arena.id(), file, *parameter)
}

fn merged_symbol(
    context: &CanonicalCheckerContext<'_>,
    file: FileId,
    declaration: NodeRef,
) -> SemanticSymbolId {
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
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

fn is_type_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

#[test]
fn ambient_object_arguments_report_exact_optional_property_mismatches() {
    let parsed = parse_source_file(concat!(
        "declare function accept(value: { y?: string }): void; ",
        "declare function generic<T>(value: T): T; ",
        "accept({ y: undefined });",
        "generic<{ y?: string }>({ y: undefined });",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

    for (index, exact_optional_property_types) in [false, true].into_iter().enumerate() {
        let file = FileId::new(2_390 + u32::try_from(index).unwrap());
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/exact-optional-argument.ts\""),
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
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types,
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();

        context.check_source_file(file).unwrap();

        let expected = if exact_optional_property_types {
            vec![2379, 2379]
        } else {
            Vec::new()
        };
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            expected
        );
        if exact_optional_property_types {
            for diagnostic in context.diagnostics().as_slice() {
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    concat!(
                        "Argument of type '{ y: undefined; }' is not assignable to ",
                        "parameter of type '{ y?: string; }' with ",
                        "'exactOptionalPropertyTypes: true'. Consider adding ",
                        "'undefined' to the types of the target's properties.\n",
                        "  Types of property 'y' are incompatible.\n",
                        "    Type 'undefined' is not assignable to type 'string'.",
                    )
                );
                assert_eq!(
                    diagnostic.diagnostic.details,
                    [
                        "  Types of property 'y' are incompatible.",
                        "    Type 'undefined' is not assignable to type 'string'.",
                    ]
                );
            }
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn ambient_function_is_one_hoisted_callable_in_scripts_and_external_modules() {
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
                "const before = formatNumber(1);\n",
                "declare function formatNumber(value: LaterNumber, suffix?: string): string;\n",
                "type LaterNumber = number;\n",
                "const after = formatNumber(2, \"!\");\n",
            ),
        );
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_200 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, false, module_state);
        let declaration = function_declaration(&parsed, file, "formatNumber");
        let parameter = first_function_parameter(&parsed, file, declaration);
        let owner = merged_symbol(&context, file, declaration);
        let parameter_symbol = merged_symbol(&context, file, parameter);
        let calls = calls(&parsed, file);
        let [before, after] = calls.as_slice() else {
            panic!("fixture must contain calls before and after the declaration")
        };

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = context
            .store()
            .value_symbol_links(owner)
            .and_then(|links| links.resolved_type)
            .expect("ambient owner must retain its callable type");
        assert_ne!(callable, string);
        assert_eq!(
            context.store().value_symbol_links(parameter_symbol),
            Some(&ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            })
        );
        let declaration_signature = context
            .store()
            .signature_links(declaration)
            .and_then(|links| links.resolved_signature.signature())
            .expect("ambient declaration must own one canonical signature");
        assert_eq!(
            context
                .store()
                .signature(declaration_signature)
                .and_then(ts_checker::semantic::signatures::Signature::resolved_return_type),
            Some(string)
        );
        for call in [*before, *after] {
            let callee = call_callee(&parsed, file, call);
            assert_eq!(
                context.store().type_node_links(call),
                Some(&TypeNodeLinks {
                    resolved_type: Some(string),
                    ..TypeNodeLinks::default()
                })
            );
            assert_eq!(
                context
                    .store()
                    .signature_links(call)
                    .and_then(|links| links.resolved_signature.signature()),
                Some(declaration_signature)
            );
            assert_eq!(
                context.store().symbol_node_links(callee),
                Some(&SymbolNodeLinks {
                    resolved_symbol: Some(owner),
                })
            );
        }

        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            context.store().value_symbol_links(owner).cloned(),
            context
                .store()
                .value_symbol_links(parameter_symbol)
                .cloned(),
            context.store().signature_links(declaration).cloned(),
            context
                .store()
                .signature(declaration_signature)
                .and_then(ts_checker::semantic::signatures::Signature::resolved_return_type),
            [*before, *after].map(|call| {
                let callee = call_callee(&parsed, file, call);
                (
                    context.store().type_node_links(call).cloned(),
                    context.store().signature_links(call).cloned(),
                    context.store().symbol_node_links(callee).cloned(),
                )
            }),
            context.diagnostics().len(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
                context.store().value_symbol_links(owner).cloned(),
                context
                    .store()
                    .value_symbol_links(parameter_symbol)
                    .cloned(),
                context.store().signature_links(declaration).cloned(),
                context
                    .store()
                    .signature(declaration_signature)
                    .and_then(ts_checker::semantic::signatures::Signature::resolved_return_type),
                [*before, *after].map(|call| {
                    let callee = call_callee(&parsed, file, call);
                    (
                        context.store().type_node_links(call).cloned(),
                        context.store().signature_links(call).cloned(),
                        context.store().symbol_node_links(callee).cloned(),
                    )
                }),
                context.diagnostics().len(),
            ),
            warm
        );
    }
}

#[test]
fn later_invalid_ambient_signature_rejects_the_whole_source_before_publication() {
    let parsed = parse_source_file(concat!(
        "const early = ready(1);\n",
        "declare function ready(value: number): number;\n",
        "declare function missing(value: number);\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_202);
    let mut context = checker_context(&parsed, file, false, CanonicalModuleState::Script);
    let ready = function_declaration(&parsed, file, "ready");
    let missing = function_declaration(&parsed, file, "missing");
    let ready_owner = merged_symbol(&context, file, ready);
    let early_call = calls(&parsed, file)[0];
    let early_callee = call_callee(&parsed, file, early_call);
    let before = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        context.store().relation_state_snapshot(),
    );

    for _ in 0..2 {
        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Function(_)
            ))
        ));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().relation_state_snapshot(),
            ),
            before
        );
        assert!(context.store().value_symbol_links(ready_owner).is_none());
        assert!(context.store().signature_links(ready).is_none());
        assert!(context.store().signature_links(missing).is_none());
        assert!(context.store().type_node_links(early_call).is_none());
        assert!(context.store().signature_links(early_call).is_none());
        assert!(context.store().symbol_node_links(early_callee).is_none());
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }
}

#[test]
fn declaration_file_and_exported_ambient_functions_publish_canonical_signatures() {
    for (index, (source, name, declaration_file, module_state)) in [
        (
            "export declare function exported(value: number): number;",
            "exported",
            false,
            CanonicalModuleState::External,
        ),
        (
            "declare function explicit(value: number): number;",
            "explicit",
            true,
            CanonicalModuleState::Script,
        ),
        (
            "export declare function declaration(value: number): number;",
            "declaration",
            true,
            CanonicalModuleState::External,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_240 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, declaration_file, module_state);
        let declaration = function_declaration(&parsed, file, name);
        let owner = merged_symbol(&context, file, declaration);

        context.check_source_file(file).unwrap();

        assert!(context.store().value_symbol_links(owner).is_some());
        assert!(context.store().signature_links(declaration).is_some());
        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        );
        context.check_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.diagnostics().clone(),
            ),
            warm,
        );
    }
}

#[test]
fn ambient_function_forms_outside_the_exact_leaf_remain_typed_boundaries() {
    for (index, (source, declaration_file, module_state)) in [
        (
            "declare function genericMerged<T>(value: T): T;\
             declare function genericMerged<T>(value: T, other: T): T;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function missing(value: number);",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function optionalGeneric<T>(value?: T): T;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function rest(...values: number[]): void;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function destructured({ value }: { value: number }): void;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare namespace Nested { function member(value: number): number; }",
            false,
            CanonicalModuleState::Script,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_210 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, declaration_file, module_state);
        assert!(
            matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(_))
            ),
            "fixture unexpectedly escaped its typed boundary: {source}",
        );
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }
}
