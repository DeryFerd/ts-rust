use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostic, CanonicalCheckerOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(62_270);
const LAST_OVERLOAD_NOTE: &str = "The last overload is declared here.";
const IMPLEMENTATION_NOTE: &str = "The call would have succeeded against this implementation, but implementation signatures of overloads are not externally visible.";
const NUMBER_ARGUMENT_ERROR: &str =
    "Argument of type 'boolean' is not assignable to parameter of type 'number'.";
const NUMBER_OVERLOAD_ERROR: &str = concat!(
    "No overload matches this call.\n",
    "  The last overload gave the following error.\n",
    "    Argument of type 'boolean' is not assignable to parameter of type 'number'.",
);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/overload-error-recovery.ts\""),
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
        CanonicalCheckerOptions {
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    nodes
}

fn callee(parsed: &ParseResult, call: NodeRef) -> NodeRef {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected a real source call")
    };
    NodeRef::new(call.arena, call.file, data.expression)
}

fn argument(parsed: &ParseResult, call: NodeRef, index: usize) -> NodeRef {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected a real source call")
    };
    NodeRef::new(call.arena, call.file, data.arguments.nodes[index])
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the declaration or recovered call must retain its exact signature")
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .expect("the checked call must retain its recovery return")
}

fn assert_primary(
    diagnostic: &CanonicalCheckerDiagnostic,
    code: u32,
    node: NodeRef,
    message: &str,
) {
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
}

fn assert_related(diagnostic: &CanonicalCheckerDiagnostic, expected: &[(u32, NodeRef, &str)]) {
    assert_eq!(diagnostic.related_information.len(), expected.len());
    for (related, (code, node, message)) in diagnostic.related_information.iter().zip(expected) {
        assert_eq!(related.diagnostic.code(), *code);
        assert_eq!(related.node, Some(*node));
        assert_eq!(related.diagnostic.render().unwrap(), *message);
    }
}

fn source_parameter_types(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source_parameters: &[Vec<SemanticSymbolId>],
) -> Vec<Vec<TypeId>> {
    let mut source_types = Vec::with_capacity(source_parameters.len());
    for parameters in source_parameters {
        let mut types = Vec::with_capacity(parameters.len());
        for parameter in parameters {
            let declaration = context
                .store()
                .symbol(*parameter)
                .unwrap()
                .value_declaration()
                .unwrap();
            let NodeData::ParameterDeclaration(parameter) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("each overload parameter retains its written annotation")
            };
            types.push(
                context
                    .get_type_from_type_node(NodeRef::new(
                        declaration.arena,
                        declaration.file,
                        parameter.type_.unwrap(),
                    ))
                    .unwrap(),
            );
        }
        source_types.push(types);
    }
    source_types
}

fn assert_recovery_signature(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    call: NodeRef,
    declarations: &[NodeRef],
    expected_return: &str,
) -> SignatureId {
    let candidates = declarations
        .iter()
        .map(|node| signature(context, *node))
        .collect::<Vec<_>>();
    let source_parameters = candidates
        .iter()
        .map(|candidate| {
            context
                .store()
                .signature(*candidate)
                .unwrap()
                .parameters()
                .to_vec()
        })
        .collect::<Vec<_>>();
    let source_types = source_parameter_types(context, parsed, &source_parameters);
    let recovered = signature(context, call);
    assert!(!candidates.contains(&recovered));
    let record = context.store().signature(recovered).unwrap();
    let literal = candidates.iter().any(|candidate| {
        context
            .store()
            .signature(*candidate)
            .unwrap()
            .flags()
            .contains(SignatureFlags::HAS_LITERAL_TYPES)
    });
    let flags = SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE
        | if literal {
            SignatureFlags::HAS_LITERAL_TYPES
        } else {
            SignatureFlags::NONE
        };
    assert_eq!(record.flags(), flags);
    assert_eq!(record.declaration(), Some(declarations[0]));
    assert!(record.type_parameters().is_empty());
    assert!(record.this_parameter().is_none());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    assert!(record.composite().is_none());
    assert!(record.isolated_signature_type().is_none());
    assert!(record.resolved_type_predicate().is_none());
    assert_eq!(
        record.parameters().len(),
        source_parameters.iter().map(Vec::len).max().unwrap()
    );
    assert_eq!(
        usize::try_from(record.min_argument_count()).unwrap(),
        source_parameters.iter().map(Vec::len).min().unwrap()
    );
    for (index, parameter) in record.parameters().iter().enumerate() {
        let sources = source_parameters
            .iter()
            .filter_map(|parameters| parameters.get(index).copied())
            .collect::<Vec<_>>();
        let types = source_types
            .iter()
            .filter_map(|types| types.get(index).copied())
            .collect::<Vec<_>>();
        assert_recovery_parameter(context, *parameter, &sources, &types);
    }
    assert_eq!(
        record.resolved_return_type(),
        Some(resolved_type(context, call))
    );
    assert_eq!(
        context.get_return_type_of_signature(recovered).unwrap(),
        resolved_type(context, call),
    );
    assert_eq!(
        context
            .type_to_string(resolved_type(context, call))
            .unwrap(),
        expected_return,
    );
    recovered
}

fn assert_recovery_parameter(
    context: &CanonicalCheckerContext<'_>,
    parameter: SemanticSymbolId,
    sources: &[SemanticSymbolId],
    types: &[TypeId],
) {
    assert!(!sources.contains(&parameter));
    let source = context.store().symbol(sources[0]).unwrap();
    let record = context.store().symbol(parameter).unwrap();
    assert_eq!(record.flags(), source.flags() | SymbolFlags::TRANSIENT);
    assert_eq!(record.name(), source.name());
    assert_eq!(record.declarations(), source.declarations());
    assert_eq!(record.value_declaration(), source.value_declaration());
    assert_eq!(record.parent(), source.parent());
    let links = context.store().value_symbol_links(parameter).unwrap();
    assert_eq!(links.target, Some(sources[0]));
    assert!(links.mapper.is_none());
    assert!(links.write_type.is_none());
    let combined = links.resolved_type.unwrap();
    let mut expected = types.to_vec();
    expected.sort_unstable();
    expected.dedup();
    if let [only] = expected.as_slice() {
        assert_eq!(combined, *only);
    } else {
        let TypeData::Union(union) = context.store().type_payload(combined).unwrap().data() else {
            panic!("a recovery parameter must keep the actual candidate type union")
        };
        assert_eq!(union.union.types, expected);
    }
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    [
        context.store().type_len(),
        context.store().signature_len(),
        context.store().mapper_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().index_info_len(),
        context.store().type_predicate_len(),
    ]
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    calls: &[NodeRef],
    declarations: &[NodeRef],
) {
    let visible = declarations
        .iter()
        .filter(|declaration| {
            !matches!(
                &parsed.arena.get(declaration.node).unwrap().data,
                NodeData::MethodDeclaration(method) if method.body.is_some()
            )
        })
        .map(|declaration| signature(context, *declaration))
        .collect::<Vec<_>>();
    for call in calls {
        let callable = context.get_type_at_location(callee(parsed, *call)).unwrap();
        let structured = context
            .store()
            .type_payload(callable)
            .unwrap()
            .data()
            .structured()
            .unwrap();
        assert_eq!(structured.signatures.as_deref(), Some(visible.as_slice()));
        assert_eq!(structured.call_signature_count, visible.len());
    }
    let queries = calls
        .iter()
        .copied()
        .chain(calls.iter().map(|call| callee(parsed, *call)))
        .collect::<Vec<_>>();
    let expected_types = queries
        .iter()
        .map(|node| context.get_type_at_location(*node).unwrap())
        .collect::<Vec<_>>();
    let signatures = calls
        .iter()
        .chain(declarations)
        .map(|node| signature(context, *node))
        .collect::<Vec<_>>();
    let expected_returns = calls
        .iter()
        .map(|call| resolved_type(context, *call))
        .collect::<Vec<_>>();
    for (call, expected) in calls.iter().zip(&expected_returns) {
        let signature = signature(context, *call);
        assert_eq!(
            context.get_return_type_of_signature(signature).unwrap(),
            *expected,
        );
    }
    let publications = queries
        .iter()
        .map(|node| {
            (
                context.store().type_node_links(*node).cloned(),
                context.store().signature_links(*node).cloned(),
                context.store().symbol_node_links(*node).cloned(),
            )
        })
        .collect::<Vec<_>>();
    let before = counts(context);
    let relations = context.store().relation_state_snapshot();
    let diagnostics = context.diagnostics().clone();
    for _ in 0..2 {
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        for (node, expected) in queries.iter().zip(&expected_types) {
            assert_eq!(context.get_type_at_location(*node).unwrap(), *expected);
        }
        for (call, expected) in calls.iter().zip(&expected_returns) {
            let signature = signature(context, *call);
            assert_eq!(
                context.get_return_type_of_signature(signature).unwrap(),
                *expected,
            );
        }
        assert_eq!(
            calls
                .iter()
                .chain(declarations)
                .map(|node| signature(context, *node))
                .collect::<Vec<_>>(),
            signatures,
        );
        assert_eq!(
            queries
                .iter()
                .map(|node| {
                    (
                        context.store().type_node_links(*node).cloned(),
                        context.store().signature_links(*node).cloned(),
                        context.store().symbol_node_links(*node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            publications,
        );
        assert_eq!(context.diagnostics(), &diagnostics);
        assert_eq!(counts(context), before);
        assert_eq!(context.store().relation_state_snapshot(), relations);
    }
}

#[test]
fn fixed_overload_failures_report_the_last_argument_error_and_keep_successes() {
    let parsed = parse_source_file(concat!(
        "interface Choice {\n",
        "  (value: string): number;\n",
        "  (value: number): number;\n",
        "}\n",
        "declare const choose: Choice;\n",
        "const good = choose('ready');\n",
        "const bad = choose(true);\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declarations = nodes(&parsed, SyntaxKind::CallSignature);
    assert_eq!(declarations.len(), 2);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let [good, bad] = calls.as_slice() else {
        panic!("the fixture keeps one successful call and one failed call")
    };
    assert_eq!(
        signature(&context, *good),
        signature(&context, declarations[0])
    );
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("only the failed call must produce a diagnostic")
    };
    assert_primary(
        diagnostic,
        2769,
        argument(&parsed, *bad, 0),
        NUMBER_OVERLOAD_ERROR,
    );
    assert!(diagnostic.range_override.is_none());
    assert_related(diagnostic, &[(2771, declarations[1], LAST_OVERLOAD_NOTE)]);
    assert_recovery_signature(&mut context, &parsed, *bad, &declarations, "number");
    assert_replay(&mut context, &parsed, &calls, &declarations);
}

#[test]
fn literal_overload_order_controls_the_last_failure_and_related_declaration() {
    let parsed = parse_source_file(concat!(
        "interface Choice {\n",
        "  (value: number): number;\n",
        "  (value: 'named'): number;\n",
        "}\n",
        "declare const choose: Choice;\n",
        "const bad = choose(true);\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declarations = nodes(&parsed, SyntaxKind::CallSignature);
    assert_eq!(declarations.len(), 2);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("the fixture keeps one failed call")
    };
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the reordered overload set must report one argument error")
    };
    assert_primary(
        diagnostic,
        2769,
        argument(&parsed, *call, 0),
        NUMBER_OVERLOAD_ERROR,
    );
    assert!(diagnostic.range_override.is_none());
    assert_related(diagnostic, &[(2771, declarations[0], LAST_OVERLOAD_NOTE)]);
    assert_recovery_signature(
        &mut context,
        &parsed,
        *call,
        &[declarations[1], declarations[0]],
        "number",
    );
    assert_replay(&mut context, &parsed, &calls, &declarations);
}

#[test]
fn one_arity_match_keeps_its_argument_error_separate_from_the_recovery_return() {
    let parsed = parse_source_file(concat!(
        "interface Choice {\n",
        "  (left: string, right: string): string;\n",
        "  (value: number): number;\n",
        "}\n",
        "declare const choose: Choice;\n",
        "const bad = choose(true);\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declarations = nodes(&parsed, SyntaxKind::CallSignature);
    assert_eq!(declarations.len(), 2);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("the fixture keeps one failed call")
    };
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the single arity match must keep its ordinary argument error")
    };
    assert_primary(
        diagnostic,
        2345,
        argument(&parsed, *call, 0),
        NUMBER_ARGUMENT_ERROR,
    );
    assert!(diagnostic.range_override.is_none());
    assert_related(diagnostic, &[]);
    assert_recovery_signature(&mut context, &parsed, *call, &declarations, "never");
    assert_eq!(
        resolved_type(&context, *call),
        context.store().intrinsic_bootstrap().unwrap().never_type,
    );
    assert_replay(&mut context, &parsed, &calls, &declarations);
}

#[test]
fn class_overload_failure_notes_keep_the_implementation_out_of_the_candidates() {
    let parsed = parse_source_file(concat!(
        "class Reader {\n",
        "  read(value: string): number;\n",
        "  read(value: number): number;\n",
        "  read(value: any): any { return value; }\n",
        "}\n",
        "function bad(reader: Reader): number { return reader.read(true); }\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declarations = nodes(&parsed, SyntaxKind::MethodDeclaration);
    let [first, last, implementation] = declarations.as_slice() else {
        panic!("the class keeps two overloads and their real implementation")
    };
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("the fixture keeps one failed method call")
    };
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the broad implementation must not make the call valid")
    };
    assert_primary(
        diagnostic,
        2769,
        argument(&parsed, *call, 0),
        NUMBER_OVERLOAD_ERROR,
    );
    assert!(diagnostic.range_override.is_none());
    assert_related(
        diagnostic,
        &[
            (2771, *last, LAST_OVERLOAD_NOTE),
            (2793, *implementation, IMPLEMENTATION_NOTE),
        ],
    );
    let recovered =
        assert_recovery_signature(&mut context, &parsed, *call, &declarations[..2], "number");
    assert_ne!(recovered, signature(&context, *implementation));
    let callable = context
        .get_type_at_location(callee(&parsed, *call))
        .unwrap();
    let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
        panic!("the real class method must retain its overload set")
    };
    let candidates = [signature(&context, *first), signature(&context, *last)];
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(candidates.as_slice())
    );
    assert_eq!(object.structured.call_signature_count, 2);
    assert_eq!(
        context
            .store()
            .signature(signature(&context, *implementation))
            .unwrap()
            .resolved_return_type(),
        Some(context.store().intrinsic_bootstrap().unwrap().any_type),
    );
    assert_replay(&mut context, &parsed, &calls, &declarations);
}

#[test]
fn mixed_overload_arity_errors_keep_original_bounds_ranges_and_parameter_notes() {
    let source = concat!(
        "interface Choice {\n",
        "  (text: string): string;\n",
        "  (left: number, right: number): string;\n",
        "}\n",
        "declare const choose: Choice;\n",
        "const missing = choose();\n",
        "const extra = choose(1, 2, 3);\n",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declarations = nodes(&parsed, SyntaxKind::CallSignature);
    assert_eq!(declarations.len(), 2);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let [missing_call, extra_call] = calls.as_slice() else {
        panic!("the fixture keeps one missing-argument call and one extra-argument call")
    };
    let [missing, extra] = context.diagnostics().as_slice() else {
        panic!("both bad arities must keep their source diagnostic order")
    };
    assert_primary(
        missing,
        2554,
        callee(&parsed, *missing_call),
        "Expected 1-2 arguments, but got 0.",
    );
    assert!(missing.range_override.is_none());
    let NodeData::CallSignatureDeclaration(first) =
        &parsed.arena.get(declarations[0].node).unwrap().data
    else {
        panic!("the shortest overload keeps its source parameter")
    };
    let parameter = NodeRef::new(parsed.arena.id(), FILE, first.parameters.nodes[0]);
    assert_related(
        missing,
        &[(6210, parameter, "An argument for 'text' was not provided.")],
    );
    assert_primary(
        extra,
        2554,
        *extra_call,
        "Expected 1-2 arguments, but got 3.",
    );
    assert_related(extra, &[]);
    let range = extra.range_override.unwrap();
    assert_eq!(range.anchor(), *extra_call);
    let range = range.range();
    assert_eq!(
        &source[usize::try_from(range.start.get()).unwrap()
            ..usize::try_from(range.end.get()).unwrap()],
        "3",
    );
    assert_eq!(
        range,
        parsed
            .arena
            .get(argument(&parsed, *extra_call, 2).node)
            .unwrap()
            .range
    );
    for call in &calls {
        assert_recovery_signature(&mut context, &parsed, *call, &declarations, "string");
    }
    assert_replay(&mut context, &parsed, &calls, &declarations);
}

#[test]
fn an_overload_arity_gap_reports_the_two_real_neighbor_counts() {
    let parsed = parse_source_file(concat!(
        "interface Choice {\n",
        "  (text: string): string;\n",
        "  (first: number, second: number, third: number): string;\n",
        "}\n",
        "declare const choose: Choice;\n",
        "const bad = choose('ready', 2);\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declarations = nodes(&parsed, SyntaxKind::CallSignature);
    assert_eq!(declarations.len(), 2);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("the fixture keeps one call between the two real arities")
    };
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("an arity gap must produce one exact overload-count diagnostic")
    };
    assert_primary(
        diagnostic,
        2575,
        callee(&parsed, *call),
        "No overload expects 2 arguments, but overloads do exist that expect either 1 or 3 arguments.",
    );
    assert!(diagnostic.range_override.is_none());
    assert_related(diagnostic, &[]);
    assert_recovery_signature(&mut context, &parsed, *call, &declarations, "string");
    assert_replay(&mut context, &parsed, &calls, &declarations);
}

#[test]
fn missing_argument_notes_keep_source_order_after_literal_overload_reordering() {
    let parsed = parse_source_file(concat!(
        "interface Choice {\n",
        "  (broad: string): number;\n",
        "  (specialized: 'x'): number;\n",
        "}\n",
        "declare const choose: Choice;\n",
        "const bad = choose();\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declarations = nodes(&parsed, SyntaxKind::CallSignature);
    let [broad, specialized] = declarations.as_slice() else {
        panic!("the broad overload precedes the literal overload in the source")
    };
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("the fixture keeps one call with a missing argument")
    };
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the failed call must keep one arity error")
    };
    assert_primary(
        diagnostic,
        2554,
        callee(&parsed, *call),
        "Expected 1 arguments, but got 0.",
    );
    assert!(diagnostic.range_override.is_none());
    let NodeData::CallSignatureDeclaration(first) = &parsed.arena.get(broad.node).unwrap().data
    else {
        panic!("the first source overload keeps its broad parameter")
    };
    assert_related(
        diagnostic,
        &[(
            6210,
            NodeRef::new(parsed.arena.id(), FILE, first.parameters.nodes[0]),
            "An argument for 'broad' was not provided.",
        )],
    );
    let originals = [
        signature(&context, *broad),
        signature(&context, *specialized),
    ];
    let recovered = signature(&context, *call);
    assert!(!originals.contains(&recovered));
    let record = context.store().signature(recovered).unwrap();
    assert_eq!(record.declaration(), Some(*specialized));
    assert_eq!(
        record.flags(),
        SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE
            | SignatureFlags::HAS_LITERAL_TYPES,
    );
    assert_eq!(record.min_argument_count(), 1);
    let [parameter] = record.parameters() else {
        panic!("the combined failure signature keeps one parameter")
    };
    let sources = [originals[1], originals[0]]
        .map(|signature| context.store().signature(signature).unwrap().parameters()[0]);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_recovery_parameter(&context, *parameter, &sources, &[bootstrap.string_type]);
    assert_eq!(record.resolved_return_type(), Some(bootstrap.number_type));
    assert_eq!(resolved_type(&context, *call), bootstrap.number_type);
    let number = bootstrap.number_type;
    assert_eq!(
        context.get_return_type_of_signature(recovered).unwrap(),
        number,
    );
    assert_replay(&mut context, &parsed, &calls, &declarations);
}
