use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, SignatureLinks, SourceFileLinks, SymbolNodeLinks,
    TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_924);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/returned-compose-arrow.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            )
            .with_always_strict(true),
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

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn value_type(checker: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected a real callable object");
    };
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one call signature");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    *signature
}

fn variable_name(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(node(parsed, variable.name))
        })
        .unwrap()
}

struct ReturnedArrow {
    declaration: NodeRef,
    owner: NodeRef,
    annotation: NodeRef,
}

fn returned_arrow(parsed: &ParseResult) -> ReturnedArrow {
    let mut arrows = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::ReturnStatement(returned) = &record.data else {
            return None;
        };
        let expression = returned.expression?;
        matches!(
            parsed.arena.get(expression)?.data,
            NodeData::ArrowFunction(_)
        )
        .then_some((id, expression))
    });
    let (returned, declaration) = arrows.next().unwrap();
    assert!(arrows.next().is_none());
    assert_eq!(parsed.arena.get(declaration).unwrap().parent, Some(returned));
    let block = parsed.arena.get(returned).unwrap().parent.unwrap();
    assert!(matches!(
        parsed.arena.get(block).unwrap().data,
        NodeData::Block(_)
    ));
    let owner = parsed.arena.get(block).unwrap().parent.unwrap();
    let annotation = match &parsed.arena.get(owner).unwrap().data {
        NodeData::FunctionDeclaration(function) => function.type_.unwrap(),
        NodeData::ArrowFunction(arrow) => arrow.type_.unwrap(),
        _ => panic!("the return must belong to its annotated source callable"),
    };
    ReturnedArrow {
        declaration: node(parsed, declaration),
        owner: node(parsed, owner),
        annotation: node(parsed, annotation),
    }
}

#[derive(Debug, Eq, PartialEq)]
struct ArrowState {
    callable: TypeId,
    target: TypeId,
    owner_signature: SignatureId,
    signature: SignatureId,
    target_signature: SignatureId,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    returned: TypeId,
    target_return: TypeId,
}

#[allow(clippy::too_many_lines)] // Check the returned arrow and its contextual signature together.
fn arrow_state(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) -> ArrowState {
    let arrow = returned_arrow(parsed);
    let owner = symbol(checker, arrow.declaration);
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(record.declarations(), Some(&[arrow.declaration][..]));
    assert_eq!(record.value_declaration(), Some(arrow.declaration));
    assert_ne!(owner, symbol(checker, arrow.owner));
    let callable = checker.get_type_at_location(arrow.declaration).unwrap();
    assert_eq!(value_type(checker, owner), callable);
    assert_eq!(
        checker.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    let target = checker.get_type_at_location(arrow.annotation).unwrap();
    let source_signature = signature(checker, callable);
    let target_signature = signature(checker, target);
    assert_ne!(callable, target);
    assert_ne!(source_signature, target_signature);
    let owner_type = checker.get_type_at_location(arrow.owner).unwrap();
    let owner_signature = signature(checker, owner_type);
    assert_eq!(
        checker.get_return_type_of_signature(owner_signature),
        Ok(target)
    );
    assert_eq!(
        checker
            .store()
            .signature_links(arrow.declaration)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(source_signature)
    );
    let NodeData::ArrowFunction(syntax) = &parsed.arena.get(arrow.declaration.node).unwrap().data
    else {
        unreachable!();
    };
    assert!(syntax.type_.is_none());
    let source_parameters = checker
        .store()
        .signature(source_signature)
        .unwrap()
        .parameters()
        .to_vec();
    let target_parameters = checker
        .store()
        .signature(target_signature)
        .unwrap()
        .parameters()
        .to_vec();
    assert_eq!(syntax.parameters.nodes.len(), 2);
    assert_eq!(source_parameters.len(), 2);
    assert_eq!(target_parameters.len(), 2);
    let mut parameters = Vec::new();
    for (index, &declaration) in syntax.parameters.nodes.iter().enumerate() {
        let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(declaration).unwrap().data
        else {
            unreachable!();
        };
        assert!(parameter.type_.is_none());
        let owner = symbol(checker, node(parsed, declaration));
        let name = node(parsed, parameter.name);
        let type_ = checker.get_type_at_location(name).unwrap();
        assert_eq!(source_parameters[index], owner);
        assert_ne!(target_parameters[index], owner);
        assert_eq!(checker.get_symbol_at_location(name), Ok(Some(owner)));
        assert_eq!(value_type(checker, owner), type_);
        assert_eq!(value_type(checker, target_parameters[index]), type_);
        parameters.push((owner, type_));
    }
    let returned = checker
        .get_return_type_of_signature(source_signature)
        .unwrap();
    let target_return = checker
        .get_return_type_of_signature(target_signature)
        .unwrap();
    let source = checker.store().signature(source_signature).unwrap();
    assert_eq!(source.declaration(), Some(arrow.declaration));
    assert_eq!(source.resolved_return_type(), Some(returned));
    assert!(source.type_parameters().is_empty());
    assert_eq!(source.target(), None);
    assert_eq!(source.mapper(), None);
    ArrowState {
        callable,
        target,
        owner_signature,
        signature: source_signature,
        target_signature,
        parameters,
        returned,
        target_return,
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 6],
    types: Vec<Option<TypeNodeLinks>>,
    symbols: Vec<Option<SymbolNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Snapshot {
    let store = checker.store();
    let nodes = parsed
        .arena
        .iter()
        .map(|(id, _)| node(parsed, id))
        .collect::<Vec<_>>();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        types: nodes
            .iter()
            .map(|&node| store.type_node_links(node).cloned())
            .collect(),
        symbols: nodes
            .iter()
            .map(|&node| store.symbol_node_links(node).cloned())
            .collect(),
        signatures: nodes
            .iter()
            .map(|&node| store.signature_links(node).cloned())
            .collect(),
        values: nodes
            .iter()
            .filter_map(|&node| checker.file(FILE).unwrap().1.symbol(node))
            .map(|owner| {
                store
                    .value_symbol_links(store.get_merged_symbol(owner).unwrap())
                    .cloned()
            })
            .collect(),
        source: store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: checker.diagnostics().clone(),
    }
}

fn replay(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult, state: &ArrowState) {
    let warm = snapshot(checker, parsed);
    assert!(warm.source.as_ref().unwrap().type_checked);
    for recheck in [false, true] {
        if recheck {
            checker.recheck_source_file(FILE).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        assert_eq!(&arrow_state(checker, parsed), state);
        assert_eq!(snapshot(checker, parsed), warm);
        assert!(checker.store().type_resolution_is_empty());
    }
}

#[test]
fn returned_block_arrows_keep_generic_context_and_distinct_parameter_owners() {
    for declaration in [
        "function compose<T>(seed: T): (context: T, next: (entry: T) => T) => T { return (context, next) => { const current: T = context; return next(current); }; }",
        "const compose = <T>(seed: T): ((context: T, next: (entry: T) => T) => T) => { return (context, next) => { const current: T = context; return next(current); }; };",
    ] {
        let parsed = parse_source_file(&format!(
            "{declaration}\n\
             declare const step: (entry: number) => number;\n\
             const run = compose<number>(1);\n\
             const result: number = run(2, step);"
        ));
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        assert!(checker.diagnostics().is_empty(), "{:?}", checker.diagnostics());
        let state = arrow_state(&mut checker, &parsed);
        let parameters = checker
            .store()
            .signature(state.owner_signature)
            .unwrap()
            .type_parameters();
        let [parameter] = parameters else {
            panic!("the returned arrow must use its owner's type parameter");
        };
        let parameter = *parameter;
        assert!(matches!(
            checker.store().type_payload(parameter).unwrap().data(),
            TypeData::TypeParameter(_)
        ));
        assert_eq!(state.parameters[0].1, parameter);
        assert_eq!(state.returned, parameter);
        assert_eq!(state.target_return, parameter);
        let next = signature(&checker, state.parameters[1].1);
        let next_parameter = checker.store().signature(next).unwrap().parameters()[0];
        assert_eq!(value_type(&checker, next_parameter), parameter);
        assert_eq!(checker.get_return_type_of_signature(next), Ok(parameter));
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            checker.get_type_at_location(variable_name(&parsed, "result")),
            Ok(number)
        );
        replay(&mut checker, &parsed, &state);
    }
}

#[test]
fn returned_arrows_keep_optional_context_in_the_parameter_and_local() {
    let parsed = parse_source_file(
        "function compose(): (context: number, next?: string) => number {\n\
           return (context, next) => {\n\
             const saved: string | undefined = next;\n\
             return context;\n\
           };\n\
         }\n\
         const run = compose();\n\
         const result: number = run(1);",
    );
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    assert!(checker.diagnostics().is_empty(), "{:?}", checker.diagnostics());
    let state = arrow_state(&mut checker, &parsed);
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let TypeData::Union(union) = checker
        .store()
        .type_payload(state.parameters[1].1)
        .unwrap()
        .data()
    else {
        panic!("the optional contextual parameter must include undefined");
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&bootstrap.string_type));
    assert!(union.union.types.contains(&bootstrap.undefined_type));
    assert_eq!(state.parameters[0].1, number);
    assert_eq!(state.returned, number);
    assert_eq!(state.target_return, number);
    assert_eq!(
        checker.get_type_at_location(variable_name(&parsed, "saved")),
        Ok(state.parameters[1].1)
    );
    assert_eq!(
        checker.get_type_at_location(variable_name(&parsed, "result")),
        Ok(number)
    );
    replay(&mut checker, &parsed, &state);
}

#[test]
fn returned_arrow_body_reports_the_native_argument_error_and_replays_it() {
    let parsed = parse_source_file(
        "function compose(): (context: number, next: (entry: number) => number) => number {\n\
           return (context, next) => { return next('bad'); };\n\
         }",
    );
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    let state = arrow_state(&mut checker, &parsed);
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(state.parameters[0].1, number);
    assert_eq!(state.returned, number);
    assert_eq!(state.target_return, number);
    let (call, argument) = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            Some((node(&parsed, id), node(&parsed, call.arguments.nodes[0])))
        })
        .unwrap();
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!(
            "expected only the wrong argument error: {:?}",
            checker.diagnostics()
        );
    };
    assert_eq!(diagnostic.node, Some(argument));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'string' is not assignable to parameter of type 'number'."
    );
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(checker.get_type_at_location(call), Ok(number));
    let next_signature = signature(&checker, state.parameters[1].1);
    assert_eq!(
        checker
            .store()
            .signature_links(call)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(next_signature)
    );
    replay(&mut checker, &parsed, &state);
}
