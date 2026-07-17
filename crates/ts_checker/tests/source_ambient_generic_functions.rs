use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnosticRange, CanonicalCheckerOptions,
    SourceCheckError, TypeData, TypeId, UnsupportedSourceSyntax, ValueSymbolLinks,
    types::{ObjectFlags, TypeFlags},
};
use ts_core::{TextPos, TextRange};
use ts_parser::{ParseResult, parse_source_file};

#[derive(Clone, Debug)]
struct FunctionParts {
    declaration: NodeRef,
    type_parameters: Vec<NodeRef>,
    parameters: Vec<NodeRef>,
    return_type: NodeRef,
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
                EscapedName::source("\"/project/ambient-generic-functions.ts\""),
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

fn function_parts(parsed: &ParseResult, file: FileId, expected: &str) -> FunctionParts {
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
            if name.text != expected {
                return None;
            }
            Some(FunctionParts {
                declaration: NodeRef::new(parsed.arena.id(), file, node),
                type_parameters: function
                    .type_parameters
                    .as_ref()?
                    .nodes
                    .iter()
                    .map(|node| NodeRef::new(parsed.arena.id(), file, *node))
                    .collect(),
                parameters: function
                    .parameters
                    .nodes
                    .iter()
                    .map(|node| NodeRef::new(parsed.arena.id(), file, *node))
                    .collect(),
                return_type: NodeRef::new(parsed.arena.id(), file, function.type_?),
            })
        })
        .unwrap_or_else(|| panic!("missing generic function {expected}"))
}

fn parameter_type(parsed: &ParseResult, file: FileId, parameter: NodeRef) -> NodeRef {
    let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!("the helper selected a parameter declaration")
    };
    NodeRef::new(
        parsed.arena.id(),
        file,
        parameter
            .type_
            .expect("fixture parameter must be annotated"),
    )
}

fn type_parameter_bounds(
    parsed: &ParseResult,
    file: FileId,
    type_parameter: NodeRef,
) -> (Option<NodeRef>, Option<NodeRef>) {
    let NodeData::TypeParameterDeclaration(type_parameter) =
        &parsed.arena.get(type_parameter.node).unwrap().data
    else {
        unreachable!("the helper selected a type-parameter declaration")
    };
    (
        type_parameter
            .constraint
            .map(|node| NodeRef::new(parsed.arena.id(), file, node)),
        type_parameter
            .default_type
            .map(|node| NodeRef::new(parsed.arena.id(), file, node)),
    )
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

fn call_type_arguments(parsed: &ParseResult, file: FileId, call: NodeRef) -> Vec<NodeRef> {
    let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!("the helper selected a call expression")
    };
    call.type_arguments
        .as_ref()
        .expect("fixture call must have explicit type arguments")
        .nodes
        .iter()
        .map(|node| NodeRef::new(parsed.arena.id(), file, *node))
        .collect()
}

fn is_type_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

fn signature_for_declaration(
    context: &CanonicalCheckerContext<'_>,
    declaration: NodeRef,
) -> ts_checker::semantic::SignatureId {
    context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .expect("generic ambient declaration must own a signature")
}

fn type_parameters_for_function(
    context: &CanonicalCheckerContext<'_>,
    file: FileId,
    function: &FunctionParts,
) -> Vec<TypeId> {
    function
        .type_parameters
        .iter()
        .map(|declaration| {
            let symbol = merged_symbol(context, file, *declaration);
            context
                .store()
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .expect("generic ambient type parameter must own its declared type")
        })
        .collect()
}

#[test]
#[allow(clippy::too_many_lines)]
fn generic_ambient_functions_are_hoisted_with_exact_signature_provenance_cold_and_warm() {
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
                "const before = dependent<string>(\"left\", \"right\");\n",
                "declare function identity<T>(value: T): T;\n",
                "const inferredIdentity = identity(\"inferred\");\n",
                "const explicitIdentity = identity<string>(\"explicit\");\n",
                "declare function dependent<T extends string, U extends T = T>(left: T, right: U): U;\n",
                "const inferredDependent = dependent(\"same\", \"same\");\n",
                "const after = identity(1);\n",
            ),
        );
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_300 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, false, module_state);
        let identity = function_parts(&parsed, file, "identity");
        let dependent = function_parts(&parsed, file, "dependent");
        let identity_owner = merged_symbol(&context, file, identity.declaration);
        let dependent_owner = merged_symbol(&context, file, dependent.declaration);
        let identity_parameter = merged_symbol(&context, file, identity.parameters[0]);
        let dependent_parameters = dependent
            .parameters
            .iter()
            .map(|parameter| merged_symbol(&context, file, *parameter))
            .collect::<Vec<_>>();
        let identity_type_parameter = merged_symbol(&context, file, identity.type_parameters[0]);
        let dependent_type_parameters = dependent
            .type_parameters
            .iter()
            .map(|parameter| merged_symbol(&context, file, *parameter))
            .collect::<Vec<_>>();
        let calls = calls(&parsed, file);
        let [
            before,
            inferred_identity,
            explicit_identity,
            inferred_dependent,
            after,
        ] = calls.as_slice()
        else {
            panic!("fixture must retain five ordered generic calls")
        };

        for owner in [identity_owner, dependent_owner] {
            assert!(context.store().value_symbol_links(owner).is_none());
        }
        for declaration in [identity.declaration, dependent.declaration] {
            assert!(context.store().signature_links(declaration).is_none());
        }
        for symbol in std::iter::once(identity_type_parameter)
            .chain(dependent_type_parameters.iter().copied())
        {
            assert!(context.store().declared_type_links(symbol).is_none());
        }
        for call in &calls {
            assert!(context.store().type_node_links(*call).is_none());
            assert!(context.store().signature_links(*call).is_none());
        }

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let identity_type_parameters = type_parameters_for_function(&context, file, &identity);
        let dependent_type_parameter_types =
            type_parameters_for_function(&context, file, &dependent);
        let [identity_t] = identity_type_parameters.as_slice() else {
            unreachable!("identity has one type parameter")
        };
        let [dependent_t, dependent_u] = dependent_type_parameter_types.as_slice() else {
            unreachable!("dependent has two type parameters")
        };
        let identity_signature = signature_for_declaration(&context, identity.declaration);
        let dependent_signature = signature_for_declaration(&context, dependent.declaration);

        for (function, owner, signature, type_parameters, parameters, return_type) in [
            (
                &identity,
                identity_owner,
                identity_signature,
                identity_type_parameters.as_slice(),
                std::slice::from_ref(&identity_parameter),
                *identity_t,
            ),
            (
                &dependent,
                dependent_owner,
                dependent_signature,
                dependent_type_parameter_types.as_slice(),
                dependent_parameters.as_slice(),
                *dependent_u,
            ),
        ] {
            let callable = context
                .store()
                .value_symbol_links(owner)
                .and_then(|links| links.resolved_type)
                .expect("generic ambient owner must retain its callable identity");
            let record = context.store().type_payload(callable).unwrap();
            let TypeData::Object(object) = record.data() else {
                panic!("generic ambient owner must retain an anonymous object")
            };
            assert_eq!(record.flags(), TypeFlags::OBJECT);
            assert_eq!(
                record.object_flags(),
                ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
            );
            assert_eq!(record.symbol(), Some(owner));
            assert_eq!(record.alias(), None);
            assert_eq!(
                object.structured.signatures.as_deref(),
                Some(&[signature][..])
            );
            assert_eq!(object.structured.call_signature_count, 1);
            let signature_record = context.store().signature(signature).unwrap();
            assert_eq!(signature_record.declaration(), Some(function.declaration));
            assert_eq!(signature_record.type_parameters(), type_parameters);
            assert_eq!(signature_record.parameters(), parameters);
            assert_eq!(signature_record.resolved_return_type(), Some(return_type));
            assert_eq!(signature_record.target(), None);
            assert_eq!(signature_record.mapper(), None);
        }

        assert_eq!(
            context.store().value_symbol_links(identity_parameter),
            Some(&ValueSymbolLinks {
                resolved_type: Some(*identity_t),
                ..ValueSymbolLinks::default()
            })
        );
        assert_eq!(
            context.store().value_symbol_links(dependent_parameters[0]),
            Some(&ValueSymbolLinks {
                resolved_type: Some(*dependent_t),
                ..ValueSymbolLinks::default()
            })
        );
        assert_eq!(
            context.store().value_symbol_links(dependent_parameters[1]),
            Some(&ValueSymbolLinks {
                resolved_type: Some(*dependent_u),
                ..ValueSymbolLinks::default()
            })
        );
        for (annotation, expected, symbol) in [
            (
                parameter_type(&parsed, file, identity.parameters[0]),
                *identity_t,
                identity_type_parameter,
            ),
            (identity.return_type, *identity_t, identity_type_parameter),
            (
                parameter_type(&parsed, file, dependent.parameters[0]),
                *dependent_t,
                dependent_type_parameters[0],
            ),
            (
                parameter_type(&parsed, file, dependent.parameters[1]),
                *dependent_u,
                dependent_type_parameters[1],
            ),
            (
                dependent.return_type,
                *dependent_u,
                dependent_type_parameters[1],
            ),
        ] {
            assert_eq!(
                context
                    .store()
                    .type_node_links(annotation)
                    .and_then(|links| links.resolved_type),
                Some(expected)
            );
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(annotation)
                    .and_then(|links| links.resolved_symbol),
                Some(symbol)
            );
        }

        let (t_constraint_node, t_default_node) =
            type_parameter_bounds(&parsed, file, dependent.type_parameters[0]);
        let (u_constraint_node, u_default_node) =
            type_parameter_bounds(&parsed, file, dependent.type_parameters[1]);
        assert!(t_constraint_node.is_some());
        assert!(t_default_node.is_none());
        for node in [u_constraint_node.unwrap(), u_default_node.unwrap()] {
            assert_eq!(
                context
                    .store()
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type),
                Some(*dependent_t)
            );
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(node)
                    .and_then(|links| links.resolved_symbol),
                Some(dependent_type_parameters[0])
            );
        }
        let TypeData::TypeParameter(t_data) =
            context.store().type_payload(*dependent_t).unwrap().data()
        else {
            panic!("T must retain its canonical type-parameter record")
        };
        let TypeData::TypeParameter(u_data) =
            context.store().type_payload(*dependent_u).unwrap().data()
        else {
            panic!("U must retain its canonical type-parameter record")
        };
        assert_eq!(t_data.constraint, Some(bootstrap.string_type));
        assert_eq!(
            t_data.resolved_default_type,
            Some(bootstrap.no_constraint_type)
        );
        assert!(
            t_data
                .constrained
                .resolved_base_constraint
                .is_none_or(|base| base == bootstrap.string_type)
        );
        assert_eq!(u_data.constraint, Some(*dependent_t));
        assert_eq!(u_data.resolved_default_type, Some(*dependent_t));
        assert!(
            u_data
                .constrained
                .resolved_base_constraint
                .is_none_or(|base| base == bootstrap.string_type)
        );

        let call_types = calls
            .iter()
            .map(|call| {
                context
                    .store()
                    .type_node_links(*call)
                    .and_then(|links| links.resolved_type)
                    .expect("generic call must retain its selected return")
            })
            .collect::<Vec<_>>();
        assert_eq!(call_types[0], bootstrap.string_type);
        assert_eq!(call_types[2], bootstrap.string_type);
        assert_eq!(
            context.store().type_payload(call_types[1]).unwrap().flags(),
            TypeFlags::STRING_LITERAL
        );
        assert_eq!(
            context.store().type_payload(call_types[3]).unwrap().flags(),
            TypeFlags::STRING_LITERAL
        );
        assert_eq!(
            context.store().type_payload(call_types[4]).unwrap().flags(),
            TypeFlags::NUMBER_LITERAL
        );
        for (call, generic_signature, owner) in [
            (*before, dependent_signature, dependent_owner),
            (*inferred_identity, identity_signature, identity_owner),
            (*explicit_identity, identity_signature, identity_owner),
            (*inferred_dependent, dependent_signature, dependent_owner),
            (*after, identity_signature, identity_owner),
        ] {
            let selected = context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
                .expect("generic call must retain an instantiated signature");
            let selected = context.store().signature(selected).unwrap();
            assert!(selected.type_parameters().is_empty());
            assert_eq!(selected.target(), Some(generic_signature));
            assert!(selected.mapper().is_some());
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(call_callee(&parsed, file, call))
                    .and_then(|links| links.resolved_symbol),
                Some(owner)
            );
        }

        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().relation_state_snapshot(),
            [identity_owner, dependent_owner]
                .map(|owner| context.store().value_symbol_links(owner).cloned()),
            [
                identity_type_parameter,
                dependent_type_parameters[0],
                dependent_type_parameters[1],
            ]
            .map(|symbol| context.store().declared_type_links(symbol).cloned()),
            [identity.declaration, dependent.declaration]
                .map(|declaration| context.store().signature_links(declaration).cloned()),
            calls
                .iter()
                .map(|call| {
                    (
                        context.store().type_node_links(*call).cloned(),
                        context.store().signature_links(*call).cloned(),
                        context
                            .store()
                            .symbol_node_links(call_callee(&parsed, file, *call))
                            .cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            context.diagnostics().clone(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().relation_state_snapshot(),
                [identity_owner, dependent_owner]
                    .map(|owner| context.store().value_symbol_links(owner).cloned()),
                [
                    identity_type_parameter,
                    dependent_type_parameters[0],
                    dependent_type_parameters[1],
                ]
                .map(|symbol| context.store().declared_type_links(symbol).cloned()),
                [identity.declaration, dependent.declaration]
                    .map(|declaration| context.store().signature_links(declaration).cloned()),
                calls
                    .iter()
                    .map(|call| {
                        (
                            context.store().type_node_links(*call).cloned(),
                            context.store().signature_links(*call).cloned(),
                            context
                                .store()
                                .symbol_node_links(call_callee(&parsed, file, *call))
                                .cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                context.diagnostics().clone(),
            ),
            warm
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn ambient_generic_calls_match_pinned_type_argument_diagnostics_and_ranges() {
    const SOURCE: &str = concat!(
        "declare function f<T>(a: T): T;\n",
        "declare function constrained<T extends string>(value: T): T;\n",
        "f<   string, number>(\"a\");\n",
        "f<\n",
        "    string, number>(\"a\");\n",
        "constrained<number>(1);\n",
        "f<string>(1);\n",
    );
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_302);
    let mut context = checker_context(&parsed, file, false, CanonicalModuleState::Script);
    let f = function_parts(&parsed, file, "f");
    let f_owner = merged_symbol(&context, file, f.declaration);
    let f_signature_declaration = f.declaration;
    let calls = calls(&parsed, file);
    let [inline, multiline, constraint, argument] = calls.as_slice() else {
        panic!("fixture must retain four generic calls")
    };

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2558, 2558, 2344, 2345]
    );
    let inline_start = SOURCE.find("string, number").unwrap();
    let multiline_start = SOURCE[inline_start + 1..]
        .find("string, number")
        .map(|start| start + inline_start + 1)
        .unwrap();
    for (diagnostic, call, start) in [
        (&diagnostics[0], *inline, inline_start),
        (&diagnostics[1], *multiline, multiline_start),
    ] {
        let start = u32::try_from(start).unwrap();
        assert_eq!(diagnostic.node, Some(call));
        assert_eq!(
            diagnostic.range_override,
            Some(CanonicalCheckerDiagnosticRange::new(
                call,
                TextRange::new(TextPos::new(start), TextPos::new(start + 14)),
            ))
        );
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Expected 1 type arguments, but got 2."
        );
        let type_arguments = call_type_arguments(&parsed, file, call);
        let [string_argument, number_argument] = type_arguments.as_slice() else {
            panic!("TS2558 fixture must retain both explicit type arguments")
        };
        assert_eq!(
            parsed.arena.get(string_argument.node).unwrap().kind,
            SyntaxKind::StringKeyword
        );
        assert_eq!(
            parsed.arena.get(number_argument.node).unwrap().kind,
            SyntaxKind::NumberKeyword
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(call_callee(&parsed, file, call))
                .and_then(|links| links.resolved_symbol),
            Some(f_owner)
        );
    }

    let f_signature = signature_for_declaration(&context, f_signature_declaration);
    let recovery_signatures = [*inline, *multiline].map(|call| {
        let signature = context
            .store()
            .signature_links(call)
            .and_then(|links| links.resolved_signature.signature())
            .expect("TS2558 call must retain a recovery signature");
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.target(), Some(f_signature));
        assert!(record.mapper().is_some());
        assert!(record.type_parameters().is_empty());
        assert_eq!(
            context
                .store()
                .type_node_links(call)
                .and_then(|links| links.resolved_type),
            Some(context.store().intrinsic_bootstrap().unwrap().string_type)
        );
        signature
    });
    assert_ne!(recovery_signatures[0], recovery_signatures[1]);

    let constraint_type_argument = call_type_arguments(&parsed, file, *constraint)[0];
    assert_eq!(diagnostics[2].node, Some(constraint_type_argument));
    assert_eq!(diagnostics[2].range_override, None);
    assert_eq!(
        diagnostics[2].diagnostic.render().unwrap(),
        "Type 'number' does not satisfy the constraint 'string'."
    );
    let NodeData::CallExpression(argument_call) = &parsed.arena.get(argument.node).unwrap().data
    else {
        unreachable!("the helper selected a call")
    };
    let argument_node = NodeRef::new(parsed.arena.id(), file, argument_call.arguments.nodes[0]);
    assert_eq!(diagnostics[3].node, Some(argument_node));
    assert_eq!(diagnostics[3].range_override, None);
    assert_eq!(
        diagnostics[3].diagnostic.render().unwrap(),
        "Argument of type 'number' is not assignable to parameter of type 'string'."
    );
    assert!(is_type_checked(&context, file));

    let warm = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        context.store().relation_state_snapshot(),
        calls
            .iter()
            .map(|call| {
                (
                    context.store().type_node_links(*call).cloned(),
                    context.store().signature_links(*call).cloned(),
                    context
                        .store()
                        .symbol_node_links(call_callee(&parsed, file, *call))
                        .cloned(),
                )
            })
            .collect::<Vec<_>>(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().relation_state_snapshot(),
            calls
                .iter()
                .map(|call| {
                    (
                        context.store().type_node_links(*call).cloned(),
                        context.store().signature_links(*call).cloned(),
                        context
                            .store()
                            .symbol_node_links(call_callee(&parsed, file, *call))
                            .cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            context.diagnostics().clone(),
        ),
        warm
    );
}

#[test]
fn unsupported_later_direct_call_statement_keeps_earlier_call_unpublished() {
    let parsed = parse_source_file(concat!(
        "declare function f<T>(value: T): T;\n",
        "f<string>(\"ready\");\n",
        "f<string>({ value: 1 });\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_303);
    let mut context = checker_context(&parsed, file, false, CanonicalModuleState::Script);
    let f = function_parts(&parsed, file, "f");
    let owner = merged_symbol(&context, file, f.declaration);
    let type_parameter = merged_symbol(&context, file, f.type_parameters[0]);
    let calls = calls(&parsed, file);
    let [earlier, later] = calls.as_slice() else {
        panic!("fixture must retain two direct call statements")
    };
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
                UnsupportedSourceSyntax::Call(node)
            )) if node == *later
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
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(
            context
                .store()
                .declared_type_links(type_parameter)
                .is_none()
        );
        assert!(context.store().signature_links(f.declaration).is_none());
        assert!(context.store().type_node_links(*earlier).is_none());
        assert!(context.store().signature_links(*earlier).is_none());
        assert!(
            context
                .store()
                .symbol_node_links(call_callee(&parsed, file, *earlier))
                .is_none()
        );
        assert!(context.store().type_node_links(*later).is_none());
        assert!(context.store().signature_links(*later).is_none());
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }
}

#[test]
fn invalid_later_generic_ambient_function_rejects_the_whole_source_atomically() {
    let parsed = parse_source_file(concat!(
        "const early = ready(1);\n",
        "declare function ready<T>(value: T): T;\n",
        "declare function invalid<T>(value?: T): T;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_304);
    let mut context = checker_context(&parsed, file, false, CanonicalModuleState::Script);
    let ready = function_parts(&parsed, file, "ready");
    let invalid = function_parts(&parsed, file, "invalid");
    let ready_owner = merged_symbol(&context, file, ready.declaration);
    let ready_type_parameter = merged_symbol(&context, file, ready.type_parameters[0]);
    let early_call = calls(&parsed, file)[0];
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
        assert!(
            context
                .store()
                .declared_type_links(ready_type_parameter)
                .is_none()
        );
        assert!(context.store().signature_links(ready.declaration).is_none());
        assert!(
            context
                .store()
                .signature_links(invalid.declaration)
                .is_none()
        );
        assert!(context.store().type_node_links(early_call).is_none());
        assert!(context.store().signature_links(early_call).is_none());
        assert!(
            context
                .store()
                .symbol_node_links(call_callee(&parsed, file, early_call))
                .is_none()
        );
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }
}

#[test]
fn ambient_generic_forms_outside_the_existing_exact_closure_remain_typed_boundaries() {
    for (index, (source, declaration_file, module_state)) in [
        (
            "declare function optional<T>(value?: T): T;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function constant<const T>(value: T): T;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function shaped<T extends { id: number }>(value: T): T;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function rest<T>(...values: T[]): T;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function initialized<T>(value: T = undefined): T;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function withThis<T>(this: T, value: T): T;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function destructured<T>([value]: T[]): T;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "export declare function exported<T>(value: T): T;",
            false,
            CanonicalModuleState::External,
        ),
        (
            "declare function merged<T>(value: T): T;\
             declare function merged<T>(value: T): T;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare namespace Nested { function member<T>(value: T): T; }",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare function explicit<T>(value: T): T;",
            true,
            CanonicalModuleState::Script,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_310 + u32::try_from(index).unwrap());
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
