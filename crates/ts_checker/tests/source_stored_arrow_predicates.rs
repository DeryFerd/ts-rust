use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, NodeLinks, SignatureId, SignatureLinks, SourceFileLinks,
    SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks, TypePredicateId, ValueSymbolLinks,
    signatures::TypePredicateKind, type_records::LiteralValue, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(207_112);
const FILE: FileId = FileId::new(207_113);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'arena>(
    library: &'arena ParseResult,
    parsed: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (LIBRARY, library, "\"/lib.es5.d.ts\"", true),
        (FILE, parsed, "\"/project/stored-predicates.ts\"", false),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, library) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    CanonicalModuleState::Script,
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for (file, parsed, _, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let owner = parsed.arena.get(parent.node).unwrap();
    let record = parsed.arena.get(id).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(owner.range.start <= record.range.start);
    assert!(record.range.end <= owner.range.end);
    node(parsed, id)
}

fn text(parsed: &ParseResult, location: NodeRef) -> &str {
    let range = parsed.arena.get(location.node).unwrap().range;
    &parsed.arena.source_text().unwrap()
        [usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

struct Binding {
    declaration: NodeRef,
    name: NodeRef,
    initializer: NodeRef,
}

fn binding(parsed: &ParseResult, expected: &str) -> Binding {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::VariableDeclaration(variable) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
            return None;
        };
        if name.text != expected {
            return None;
        }
        assert!(variable.type_.is_none());
        let declaration = node(parsed, id);
        Some(Binding {
            declaration,
            name: child(parsed, declaration, variable.name),
            initializer: child(parsed, declaration, variable.initializer.unwrap()),
        })
    });
    let binding = matches.next().expect("the source has this variable");
    assert!(matches.next().is_none(), "expected one variable {expected}");
    binding
}

struct Parameter {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
}

struct Arrow {
    binding: Binding,
    declaration: NodeRef,
    parameters: Vec<Parameter>,
    predicate: NodeRef,
    predicate_name: NodeRef,
    narrowed: NodeRef,
    body: NodeRef,
}

fn stored_arrow(parsed: &ParseResult, expected: &str) -> Arrow {
    let binding = binding(parsed, expected);
    let declaration = binding.initializer;
    let record = parsed.arena.get(declaration.node).unwrap();
    assert_eq!(record.kind, SyntaxKind::ArrowFunction);
    assert_eq!(record.parent, Some(binding.declaration.node));
    let NodeData::ArrowFunction(arrow) = &record.data else {
        panic!("the variable initializer is the actual arrow");
    };
    assert!(arrow.type_parameters.is_none());
    assert!(arrow.modifiers.is_none());
    let predicate = child(parsed, declaration, arrow.type_.unwrap());
    let predicate_record = parsed.arena.get(predicate.node).unwrap();
    assert_eq!(predicate_record.kind, SyntaxKind::TypePredicate);
    let NodeData::TypePredicateNode(data) = &predicate_record.data else {
        panic!("the written return is the actual type predicate");
    };
    assert!(data.asserts_modifier.is_none());
    Arrow {
        binding,
        declaration,
        parameters: arrow
            .parameters
            .nodes
            .iter()
            .map(|&id| {
                let declaration = child(parsed, declaration, id);
                let NodeData::ParameterDeclaration(parameter) =
                    &parsed.arena.get(id).unwrap().data
                else {
                    panic!("the arrow retains its actual parameter");
                };
                assert!(parameter.initializer.is_none());
                assert!(parameter.dot_dot_dot_token.is_none());
                Parameter {
                    declaration,
                    name: child(parsed, declaration, parameter.name),
                    annotation: child(parsed, declaration, parameter.type_.unwrap()),
                }
            })
            .collect(),
        predicate,
        predicate_name: child(parsed, predicate, data.parameter_name),
        narrowed: child(parsed, predicate, data.type_.unwrap()),
        body: child(parsed, declaration, arrow.body),
    }
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    let merged = checker.store().get_merged_symbol(raw).unwrap();
    assert_eq!(raw, merged);
    merged
}

fn checked(checker: &CanonicalCheckerContext<'_>) -> bool {
    checker
        .store()
        .source_file_links(checker.source_file(FILE).unwrap())
        .is_some_and(|links| links.type_checked)
}

fn start(checker: &mut CanonicalCheckerContext<'_>, arrow: &Arrow, query_first: bool) {
    assert!(!checked(checker));
    assert!(checker.store().signature_links(arrow.declaration).is_none());
    if query_first {
        checker.get_type_at_location(arrow.declaration).unwrap();
    }
    checker.check_source_file(FILE).unwrap();
    assert!(checked(checker));
    assert_eq!(checker.store().type_resolution_len(), 0);
}

#[derive(Debug, Eq, PartialEq)]
struct PredicateState {
    owner: SemanticSymbolId,
    binding: SemanticSymbolId,
    type_: TypeId,
    signature: SignatureId,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    predicate: TypePredicateId,
    narrowed: TypeId,
    returned: TypeId,
}

#[allow(clippy::too_many_lines)] // Keep the written predicate and its actual owners in one check.
fn predicate_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    arrow: &Arrow,
    parameter_index: usize,
) -> PredicateState {
    let owner = symbol(checker, arrow.declaration);
    let binding = symbol(checker, arrow.binding.declaration);
    assert_ne!(owner, binding);
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(record.declarations(), Some(&[arrow.declaration][..]));
    assert_eq!(record.value_declaration(), Some(arrow.declaration));
    let record = checker.store().symbol(binding).unwrap();
    assert_eq!(record.flags(), SymbolFlags::BLOCK_SCOPED_VARIABLE);
    assert_eq!(
        record.declarations(),
        Some(&[arrow.binding.declaration][..])
    );
    let type_ = checker.get_type_at_location(arrow.declaration).unwrap();
    assert_eq!(checker.get_type_at_location(arrow.binding.name), Ok(type_));
    assert_eq!(
        checker.get_symbol_at_location(arrow.binding.name),
        Ok(Some(binding))
    );
    for symbol in [owner, binding] {
        assert_eq!(
            checker
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            Some(type_)
        );
    }
    let signature = checker
        .store()
        .signature_links(arrow.declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let record = checker.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("the arrow has its source callable object");
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    let parameters = arrow
        .parameters
        .iter()
        .map(|parameter| {
            let owner = symbol(checker, parameter.declaration);
            let record = checker.store().symbol(owner).unwrap();
            assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
            assert_eq!(record.declarations(), Some(&[parameter.declaration][..]));
            assert_eq!(record.value_declaration(), Some(parameter.declaration));
            let type_ = checker.get_type_at_location(parameter.name).unwrap();
            assert_eq!(
                checker.get_symbol_at_location(parameter.name),
                Ok(Some(owner))
            );
            assert_eq!(
                checker.get_type_from_type_node(parameter.annotation),
                Ok(type_)
            );
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(owner)
                    .unwrap()
                    .resolved_type,
                Some(type_)
            );
            (owner, type_)
        })
        .collect::<Vec<_>>();
    let returned = checker.get_return_type_of_signature(signature).unwrap();
    let boolean = checker.store().intrinsic_bootstrap().unwrap().boolean_type;
    assert_eq!(returned, boolean);
    assert_eq!(checker.get_type_from_type_node(arrow.predicate), Ok(boolean));
    let narrowed = checker.get_type_from_type_node(arrow.narrowed).unwrap();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(arrow.declaration));
    assert_eq!(
        record.parameters(),
        parameters.iter().map(|&(owner, _)| owner).collect::<Vec<_>>()
    );
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(parameters.len()).unwrap()
    );
    assert_eq!(record.resolved_return_type(), Some(boolean));
    assert!(record.type_parameters().is_empty());
    assert!(record.this_parameter().is_none());
    assert!(!record.has_rest_parameter());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    let predicate = record.resolved_type_predicate().unwrap();
    let record = checker.store().type_predicate(predicate).unwrap();
    assert_eq!(record.kind(), TypePredicateKind::Identifier);
    assert_eq!(
        record.parameter_index(),
        i32::try_from(parameter_index).unwrap()
    );
    assert_eq!(record.parameter_name(), text(parsed, arrow.predicate_name));
    assert_eq!(
        record.parameter_name(),
        text(parsed, arrow.parameters[parameter_index].name)
    );
    assert_eq!(record.type_id(), Some(narrowed));
    assert_eq!(
        checker.store().symbol_node_links(arrow.predicate_name),
        Some(&SymbolNodeLinks {
            resolved_symbol: Some(parameters[parameter_index].0),
        })
    );
    assert_eq!(
        checker.store().type_node_links(arrow.predicate),
        Some(&TypeNodeLinks {
            resolved_type: Some(boolean),
            outer_type_parameters: None,
        })
    );
    PredicateState {
        owner,
        binding,
        type_,
        signature,
        parameters,
        predicate,
        narrowed,
        returned,
    }
}

fn assert_call(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    expected: &str,
    state: &PredicateState,
) -> NodeRef {
    let binding = binding(parsed, expected);
    let call = binding.initializer;
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("the source contains the actual predicate call");
    };
    let callee = child(parsed, call, data.expression);
    assert_eq!(checker.get_type_at_location(callee), Ok(state.type_));
    assert_eq!(
        checker.get_symbol_at_location(callee),
        Ok(Some(state.binding))
    );
    assert_eq!(checker.get_type_at_location(call), Ok(state.returned));
    assert_eq!(checker.get_type_at_location(binding.name), Ok(state.returned));
    assert_eq!(
        checker
            .store()
            .signature_links(call)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(state.signature)
    );
    call
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    common: Option<NodeLinks>,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 9],
    nodes: Vec<NodeState>,
    values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn publication(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Publication {
    let store = checker.store();
    Publication {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.type_predicate_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
            store.type_resolution_len(),
        ],
        nodes: parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = node(parsed, id);
                NodeState {
                    node,
                    common: store.node_links(node).cloned(),
                    type_: store.type_node_links(node).cloned(),
                    symbol: store.symbol_node_links(node).cloned(),
                    signature: store.signature_links(node).cloned(),
                }
            })
            .collect(),
        values: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect(),
        source: store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: checker.diagnostics().clone(),
    }
}

fn assert_replay(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    arrow: &Arrow,
    parameter_index: usize,
    state: &PredicateState,
    call: NodeRef,
) {
    let before = publication(checker, parsed);
    checker.check_source_file(FILE).unwrap();
    assert_eq!(publication(checker, parsed), before);
    for _ in 0..2 {
        checker.recheck_source_file(FILE).unwrap();
        assert_eq!(
            &predicate_state(checker, parsed, arrow, parameter_index),
            state
        );
        assert_eq!(checker.get_type_at_location(call), Ok(state.returned));
        assert!(checked(checker));
        assert_eq!(publication(checker, parsed), before);
    }
}

#[test]
fn stored_arrow_predicates_keep_local_alias_and_parameter_identity() {
    let library = parse_source_file(ES5);
    let parsed = parse_source_file(concat!(
        "type SecFetchSite = 'same-origin' | 'same-site' | 'none' | 'cross-site';\n",
        "const isSecFetchSite = (value: string): value is SecFetchSite => value === 'same-origin';\n",
        "const accepted = isSecFetchSite('same-origin');\n",
    ));
    let arrow = stored_arrow(&parsed, "isSecFetchSite");
    assert_eq!(text(&parsed, arrow.predicate), "value is SecFetchSite");
    for query_first in [false, true] {
        let mut checker = context(&library, &parsed);
        start(&mut checker, &arrow, query_first);
        let state = predicate_state(&mut checker, &parsed, &arrow, 0);
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(state.parameters[0].1, string);
        assert_eq!(
            checker.is_type_assignable_to(state.narrowed, string),
            Ok(true)
        );
        assert_eq!(checker.get_type_at_location(arrow.body), Ok(state.returned));
        let TypeData::Union(union) = checker.store().type_payload(state.narrowed).unwrap().data()
        else {
            panic!("the local alias keeps its four string literals");
        };
        let mut values = union
            .union
            .types
            .iter()
            .map(|&type_| {
                let record = checker.store().type_payload(type_).unwrap();
                assert!(record.flags().contains(TypeFlags::STRING_LITERAL));
                let TypeData::Literal(literal) = record.data() else {
                    panic!("the alias constituent is a real literal");
                };
                let LiteralValue::String(value) = &literal.value else {
                    panic!("the predicate narrows to string literals");
                };
                value.as_str()
            })
            .collect::<Vec<_>>();
        values.sort_unstable();
        assert_eq!(values, ["cross-site", "none", "same-origin", "same-site"]);
        let call = assert_call(&mut checker, &parsed, "accepted", &state);
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        assert_replay(&mut checker, &parsed, &arrow, 0, &state, call);
    }
}

#[test]
fn stored_arrow_predicates_use_the_named_second_parameter() {
    let library = parse_source_file(ES5);
    let parsed = parse_source_file(concat!(
        "const hasToken = (other: number, value: string): value is 'ok' => value === 'ok';\n",
        "const accepted = hasToken(1, 'ok');\n",
    ));
    let arrow = stored_arrow(&parsed, "hasToken");
    assert_eq!(text(&parsed, arrow.predicate), "value is 'ok'");
    for query_first in [false, true] {
        let mut checker = context(&library, &parsed);
        start(&mut checker, &arrow, query_first);
        let state = predicate_state(&mut checker, &parsed, &arrow, 1);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        assert_eq!(state.parameters.len(), 2);
        assert_ne!(state.parameters[0].0, state.parameters[1].0);
        assert_eq!(state.parameters[0].1, number);
        assert_eq!(state.parameters[1].1, string);
        assert_eq!(
            checker.is_type_assignable_to(state.narrowed, string),
            Ok(true)
        );
        assert_eq!(
            checker.is_type_assignable_to(state.narrowed, number),
            Ok(false)
        );
        let TypeData::Literal(literal) =
            checker.store().type_payload(state.narrowed).unwrap().data()
        else {
            panic!("the written narrowed type is the actual string literal");
        };
        assert_eq!(literal.value, LiteralValue::String("ok".into()));
        assert_eq!(checker.get_type_at_location(arrow.body), Ok(state.returned));
        let call = assert_call(&mut checker, &parsed, "accepted", &state);
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        assert_replay(&mut checker, &parsed, &arrow, 1, &state, call);
    }
}

#[test]
fn stored_arrow_predicate_diagnostics_keep_real_types_and_replay() {
    let library = parse_source_file(ES5);
    for invalid_narrowing in [true, false] {
        let source = if invalid_narrowing {
            "const bad = (value: string): value is number => true; const result = bad('text');"
        } else {
            "const bad = (value: string): value is string => 1; const result = bad('text');"
        };
        let parsed = parse_source_file(source);
        let arrow = stored_arrow(&parsed, "bad");
        for query_first in [false, true] {
            let mut checker = context(&library, &parsed);
            start(&mut checker, &arrow, query_first);
            let state = predicate_state(&mut checker, &parsed, &arrow, 0);
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let string = bootstrap.string_type;
            let number = bootstrap.number_type;
            assert_eq!(state.parameters[0].1, string);
            assert_eq!(
                state.narrowed,
                if invalid_narrowing { number } else { string }
            );
            assert_eq!(
                checker.is_type_assignable_to(state.narrowed, string),
                Ok(!invalid_narrowing)
            );
            let body_type = checker.get_type_at_location(arrow.body).unwrap();
            let body = checker.store().type_payload(body_type).unwrap();
            assert!(body.flags().contains(if invalid_narrowing {
                TypeFlags::BOOLEAN_LITERAL
            } else {
                TypeFlags::NUMBER_LITERAL
            }));
            let call = assert_call(&mut checker, &parsed, "result", &state);
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!("expected one native diagnostic: {:?}", checker.diagnostics());
            };
            let (site, expected_text, code, message) = if invalid_narrowing {
                (
                    arrow.narrowed,
                    "number",
                    2677,
                    concat!(
                        "A type predicate's type must be assignable to its parameter's type.\n",
                        "  Type 'number' is not assignable to type 'string'.",
                    ),
                )
            } else {
                (
                    arrow.body,
                    "1",
                    2322,
                    "Type 'number' is not assignable to type 'boolean'.",
                )
            };
            assert_eq!(diagnostic.node, Some(site));
            assert_eq!(text(&parsed, site), expected_text);
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
            assert!(diagnostic.related_information.is_empty());
            assert_replay(&mut checker, &parsed, &arrow, 0, &state, call);
        }
    }
}

#[test]
fn stored_arrow_predicate_errors_keep_the_missing_property_note() {
    let library = parse_source_file(ES5);
    let parsed = parse_source_file(concat!(
        "interface PredicateInput { required: string; }\n",
        "interface PredicateNarrowed {}\n",
        "declare const input: PredicateInput;\n",
        "const bad = (value: PredicateInput): value is PredicateNarrowed => true;\n",
        "const result = bad(input);\n",
    ));
    let arrow = stored_arrow(&parsed, "bad");
    let mut properties = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::PropertySignatureDeclaration(property) = &record.data else {
            return None;
        };
        assert_eq!(record.kind, SyntaxKind::PropertySignature);
        let declaration = node(&parsed, id);
        Some(child(&parsed, declaration, property.name))
    });
    let property_name = properties.next().unwrap();
    assert!(properties.next().is_none());
    assert_eq!(text(&parsed, property_name), "required");
    for query_first in [false, true] {
        let mut checker = context(&library, &parsed);
        start(&mut checker, &arrow, query_first);
        let state = predicate_state(&mut checker, &parsed, &arrow, 0);
        assert_ne!(state.narrowed, state.parameters[0].1);
        assert_eq!(
            checker.is_type_assignable_to(state.narrowed, state.parameters[0].1),
            Ok(false)
        );
        for type_ in [state.narrowed, state.parameters[0].1] {
            assert!(matches!(
                checker.store().type_payload(type_).unwrap().data(),
                TypeData::Interface(_)
            ));
        }
        let call = assert_call(&mut checker, &parsed, "result", &state);
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("expected one predicate error: {:?}", checker.diagnostics());
        };
        assert_eq!(diagnostic.node, Some(arrow.narrowed));
        assert_eq!(text(&parsed, arrow.narrowed), "PredicateNarrowed");
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), 2677);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            concat!(
                "A type predicate's type must be assignable to its parameter's type.\n",
                "  Property 'required' is missing in type 'PredicateNarrowed' ",
                "but required in type 'PredicateInput'.",
            )
        );
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("the predicate error retains the real required-property declaration");
        };
        assert_eq!(related.node, Some(property_name));
        assert_eq!(related.diagnostic.code(), 2728);
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "'required' is declared here."
        );
        assert_replay(&mut checker, &parsed, &arrow, 0, &state, call);
    }
}
