use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(18_202);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/exported-overloads.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::External,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), FILE, node),
            ))
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|(start, _)| *start);
    result.into_iter().map(|(_, node)| node).collect()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the checked declaration or call must retain its signature")
}

fn assert_exported_group(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    declarations: &[NodeRef],
) -> Vec<SignatureId> {
    let bound = context.file(FILE).unwrap().1;
    let owner = bound.symbol(declarations[0]).unwrap();
    let local = bound.local_symbol(declarations[0]).unwrap();
    let module = bound.symbol(bound.source_file()).unwrap();
    assert_ne!(owner, local);
    for (index, declaration) in declarations.iter().copied().enumerate() {
        assert_eq!(bound.symbol(declaration), Some(owner));
        assert_eq!(bound.local_symbol(declaration), Some(local));
        let NodeData::FunctionDeclaration(function) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("the group must retain function declarations")
        };
        assert_eq!(function.body.is_some(), index + 1 == declarations.len());
    }
    let owner_record = context.store().symbol(owner).unwrap();
    let local_record = context.store().symbol(local).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(owner_record.declarations(), Some(declarations));
    assert_eq!(owner_record.value_declaration(), Some(declarations[0]));
    assert_eq!(owner_record.parent(), Some(module));
    assert_eq!(local_record.flags(), SymbolFlags::EXPORT_VALUE);
    assert_eq!(local_record.declarations(), Some(declarations));
    assert_eq!(local_record.export_symbol(), Some(owner));
    assert_eq!(local_record.parent(), None);
    let exports = context.store().symbol(module).unwrap().exports().unwrap();
    assert_eq!(
        context
            .store()
            .symbol_table(exports)
            .unwrap()
            .get(owner_record.name()),
        Some(owner)
    );
    let locals = bound.locals(bound.source_file()).unwrap();
    assert_eq!(
        context
            .store()
            .symbol_table(locals)
            .unwrap()
            .get(owner_record.name()),
        Some(local)
    );

    let signatures = declarations
        .iter()
        .map(|declaration| signature(context, *declaration))
        .collect::<Vec<_>>();
    let callable = context
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .unwrap();
    let record = context.store().type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("the exported overload group must retain its callable object")
    };
    let public = &signatures[..signatures.len() - 1];
    assert_eq!(object.structured.signatures.as_deref(), Some(public));
    assert_eq!(object.structured.call_signature_count, public.len());
    assert!(!public.contains(signatures.last().unwrap()));
    for (declaration, signature) in declarations.iter().zip(&signatures) {
        assert_eq!(
            context.store().signature(*signature).unwrap().declaration(),
            Some(*declaration)
        );
    }
    signatures
}

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, queries: &[NodeRef]) {
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().relation_state_snapshot(),
            context.diagnostics().clone(),
            queries
                .iter()
                .map(|node| {
                    (
                        context.store().signature_links(*node).cloned(),
                        context.store().type_node_links(*node).cloned(),
                        context.store().symbol_node_links(*node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
        )
    };
    let before = snapshot(context);
    context.check_source_file(FILE).unwrap();
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(snapshot(context), before);
    assert!(
        context
            .source_file(FILE)
            .and_then(|source| context.store().source_file_links(source))
            .is_some_and(|links| links.type_checked)
    );
}

#[test]
fn exported_noop_keeps_void_before_undefined_and_its_real_implementation() {
    let parsed = parse_source_file(concat!(
        "const before = noop();\n",
        "export function noop(): void\n",
        "export function noop(): undefined\n",
        "export function noop() {}\n",
        "const after = noop();\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    let declarations = nodes(&parsed, SyntaxKind::FunctionDeclaration);
    assert_eq!(declarations.len(), 3);
    let signatures = assert_exported_group(&context, &parsed, &declarations);
    let intrinsic = context.store().intrinsic_bootstrap().unwrap();
    let expected = [
        intrinsic.void_type,
        intrinsic.undefined_type,
        intrinsic.void_type,
    ];
    for (signature, return_type) in signatures.iter().zip(expected) {
        assert_eq!(
            context
                .store()
                .signature(*signature)
                .unwrap()
                .resolved_return_type(),
            Some(return_type)
        );
    }
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    let void_type = expected[0];
    for call in &calls {
        assert_eq!(signature(&context, *call), signatures[0]);
        assert_eq!(context.get_type_at_location(*call), Ok(void_type));
        let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
            panic!("expected a source call")
        };
        let callee = NodeRef::new(call.arena, call.file, data.expression);
        assert_eq!(
            context
                .store()
                .symbol_node_links(callee)
                .unwrap()
                .resolved_symbol,
            context.file(FILE).unwrap().1.local_symbol(declarations[0])
        );
    }
    let queries = declarations.into_iter().chain(calls).collect::<Vec<_>>();
    assert_replay(&mut context, &queries);
}

#[test]
fn exported_generic_overloads_keep_required_public_parameters() {
    let parsed = parse_source_file(concat!(
        "export type RefObject<T> = { current: T };\n",
        "export function useRef<T>(initialValue: T): RefObject<T>\n",
        "export function useRef<T>(initialValue: T | null): RefObject<T | null>\n",
        "export function useRef<T>(initialValue: T | undefined): RefObject<T | undefined>\n",
        "export function useRef<T>(initialValue?: T | null): RefObject<T | null | undefined> {\n",
        "  return { current: initialValue };\n",
        "}\n",
        "const value: RefObject<number> = useRef<number>(1);\n",
        "const nullable: RefObject<number | null> = useRef<number>(null);\n",
        "const optional: RefObject<number | undefined> = useRef<number>(undefined);\n",
        "const missing = useRef<number>();\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declarations = nodes(&parsed, SyntaxKind::FunctionDeclaration);
    assert_eq!(declarations.len(), 4);
    let signatures = assert_exported_group(&context, &parsed, &declarations);
    let mut type_parameters = Vec::new();
    for (signature, minimum) in signatures.iter().zip([1, 1, 1, 0]) {
        let record = context.store().signature(*signature).unwrap();
        assert_eq!(record.min_argument_count(), minimum);
        let [parameter] = record.type_parameters() else {
            panic!("each declaration must own its generic parameter")
        };
        assert!(!type_parameters.contains(parameter));
        type_parameters.push(*parameter);
    }
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 4);
    let annotations = nodes(&parsed, SyntaxKind::VariableDeclaration)
        .into_iter()
        .filter_map(|node| {
            let NodeData::VariableDeclaration(variable) = &parsed.arena.get(node.node)?.data else {
                return None;
            };
            variable
                .type_
                .map(|type_| NodeRef::new(node.arena, node.file, type_))
        })
        .collect::<Vec<_>>();
    assert_eq!(annotations.len(), 3);
    for (index, (call, annotation)) in calls.iter().zip(&annotations).enumerate() {
        let selected = signature(&context, *call);
        assert_eq!(
            context.store().signature(selected).unwrap().target(),
            Some(signatures[index])
        );
        let expected = context.get_type_from_type_node(*annotation).unwrap();
        assert_eq!(context.get_type_at_location(*call), Ok(expected));
    }
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "only the missing public argument must fail: {:?}",
            context.diagnostics()
        )
    };
    assert_eq!(diagnostic.diagnostic.code(), 2554);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0."
    );
    assert_eq!(diagnostic.node, Some(calls[3]));
    assert!(diagnostic.range_override.is_none());
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("the missing public parameter must retain its note")
    };
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument for 'initialValue' was not provided."
    );
    let parameter = context
        .store()
        .signature(signatures[0])
        .unwrap()
        .parameters()[0];
    assert_eq!(
        related.node,
        context
            .store()
            .symbol(parameter)
            .unwrap()
            .value_declaration()
    );
    let queries = declarations.into_iter().chain(calls).collect::<Vec<_>>();
    assert_replay(&mut context, &queries);
}

#[test]
fn a_broad_exported_implementation_cannot_accept_a_wrong_public_call() {
    let parsed = parse_source_file(concat!(
        "export function read(value: string): number;\n",
        "export function read(value: number, other: number): number;\n",
        "export function read(value: unknown, other?: number): number { return 0; }\n",
        "const result = read(true);\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declarations = nodes(&parsed, SyntaxKind::FunctionDeclaration);
    let signatures = assert_exported_group(&context, &parsed, &declarations);
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "the wrong public argument must produce one diagnostic: {:?}",
            context.diagnostics()
        )
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'boolean' is not assignable to parameter of type 'string'."
    );
    assert_eq!(
        diagnostic.node,
        Some(nodes(&parsed, SyntaxKind::TrueKeyword)[0])
    );
    assert!(diagnostic.range_override.is_none());
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("the broad implementation must remain hidden and explain the failed call")
    };
    assert_eq!(related.node, Some(declarations[2]));
    assert_eq!(related.diagnostic.code(), 2793);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "The call would have succeeded against this implementation, but implementation signatures of overloads are not externally visible."
    );
    let call = nodes(&parsed, SyntaxKind::CallExpression)[0];
    let recovered = signature(&context, call);
    assert!(!signatures.contains(&recovered));
    assert_eq!(
        context.store().signature(recovered).unwrap().flags(),
        SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE
    );
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(context.get_type_at_location(call), Ok(number));
    let queries = declarations.into_iter().chain([call]).collect::<Vec<_>>();
    assert_replay(&mut context, &queries);
}

#[test]
fn exported_implementation_compatibility_checks_parameters_and_returns_in_order() {
    for (implementation, incompatible) in [
        (
            "export function read(value: string): number { return 0; }\n",
            1,
        ),
        (
            "export function read(value: unknown): string { return 'wrong'; }\n",
            0,
        ),
    ] {
        let source = format!(
            "export function read(value: string): number;\nexport function read(value: number): number;\n{implementation}"
        );
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        context.check_source_file(FILE).unwrap();
        let declarations = nodes(&parsed, SyntaxKind::FunctionDeclaration);
        assert_eq!(
            assert_exported_group(&context, &parsed, &declarations).len(),
            3
        );
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!(
                "the first incompatible overload must produce one diagnostic: {:?}",
                context.diagnostics()
            )
        };
        assert_eq!(diagnostic.diagnostic.code(), 2394);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "This overload signature is not compatible with its implementation signature."
        );
        assert_eq!(diagnostic.node, Some(declarations[incompatible]));
        assert!(diagnostic.range_override.is_none());
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("the incompatible overload must identify its implementation")
        };
        assert_eq!(related.node, Some(declarations[2]));
        assert_eq!(related.diagnostic.code(), 2750);
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "The implementation signature is declared here."
        );
        assert_replay(&mut context, &declarations);
    }
}

#[test]
fn compatible_exported_overloads_still_check_the_implementation_body() {
    let parsed = parse_source_file(concat!(
        "export function read(value: string): number;\n",
        "export function read(value: number): number;\n",
        "export function read(value: unknown): number { return 'wrong'; }\n",
        "const result: number = read('text');\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declarations = nodes(&parsed, SyntaxKind::FunctionDeclaration);
    let signatures = assert_exported_group(&context, &parsed, &declarations);
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "the implementation body must still produce its return error: {:?}",
            context.diagnostics()
        )
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
    assert_eq!(
        diagnostic.node,
        Some(nodes(&parsed, SyntaxKind::ReturnStatement)[0])
    );
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
    let call = nodes(&parsed, SyntaxKind::CallExpression)[0];
    assert_eq!(signature(&context, call), signatures[0]);
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(context.get_type_at_location(call), Ok(number));
    let queries = declarations.into_iter().chain([call]).collect::<Vec<_>>();
    assert_replay(&mut context, &queries);
}
