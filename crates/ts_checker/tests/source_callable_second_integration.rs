use ts_ast::{FileId, NodeData, NodeFlags, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    DeclaredTypeLinks, IntrinsicBootstrapOptions, SignatureId, SignatureLinks, SourceFileLinks,
    SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
    type_records::StructuredTypeData,
};
use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

const FILE: FileId = FileId::new(202_750);

fn context(parsed: &ParseResult, language: CanonicalSourceLanguage) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    let path = match language {
        CanonicalSourceLanguage::TypeScript => "\"/project/second-callable-integration.ts\"",
        CanonicalSourceLanguage::JavaScript => "\"/project/second-callable-integration.js\"",
    };
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source(path),
                language,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    match language {
        CanonicalSourceLanguage::TypeScript => binder
            .bind_typescript_declaration_slice(&parsed.arena, FILE)
            .unwrap(),
        CanonicalSourceLanguage::JavaScript => binder
            .bind_javascript_declaration_slice(&parsed.arena, FILE)
            .unwrap(),
    };
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
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn only_node(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)))
        .collect::<Vec<_>>();
    let [node] = nodes.as_slice() else {
        panic!("expected one {kind:?}, got {nodes:?}")
    };
    *node
}

fn node_text(parsed: &ParseResult, location: NodeRef) -> &str {
    let range = parsed.arena.get(location.node).unwrap().range;
    &parsed.arena.source_text().unwrap()[range.start.get() as usize..range.end.get() as usize]
}

#[derive(Clone, Copy)]
struct NamedDeclaration {
    declaration: NodeRef,
    name: NodeRef,
}

fn named_declaration(parsed: &ParseResult, declaration: NodeRef) -> NamedDeclaration {
    let record = parsed.arena.get(declaration.node).unwrap();
    let name = match (&record.data, record.kind) {
        (NodeData::VariableDeclaration(data), SyntaxKind::VariableDeclaration) => data.name,
        (NodeData::ParameterDeclaration(data), SyntaxKind::Parameter) => data.name,
        (NodeData::BindingElement(data), SyntaxKind::BindingElement) => data.name.unwrap(),
        _ => panic!("expected a variable, parameter, or binding element"),
    };
    assert_eq!(parsed.arena.get(name).unwrap().kind, SyntaxKind::Identifier);
    NamedDeclaration {
        declaration,
        name: node(parsed, name),
    }
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn callable_signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected a callable object")
    };
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected exactly one public call signature")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    *signature
}

fn assert_signature(
    checker: &CanonicalCheckerContext<'_>,
    signature: SignatureId,
    declaration: NodeRef,
    parameters: &[SemanticSymbolId],
    type_parameters: &[TypeId],
) {
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.parameters(), parameters);
    assert_eq!(record.type_parameters(), type_parameters);
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(parameters.len()).unwrap()
    );
    assert!(record.this_parameter().is_none());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
}

fn assert_value(
    checker: &mut CanonicalCheckerContext<'_>,
    named: NamedDeclaration,
    type_: TypeId,
    flags: SymbolFlags,
) -> SemanticSymbolId {
    let owner = symbol(checker, named.declaration);
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), flags);
    assert_eq!(record.declarations(), Some(&[named.declaration][..]));
    assert_eq!(record.value_declaration(), Some(named.declaration));
    let links = checker.store().value_symbol_links(owner).unwrap();
    assert_eq!(links.resolved_type, Some(type_));
    assert!(links.target.is_none());
    assert!(links.mapper.is_none());
    assert_eq!(checker.get_symbol_at_location(named.name), Ok(Some(owner)));
    assert_eq!(checker.get_type_at_location(named.name), Ok(type_));
    owner
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 8],
    types: Vec<Option<TypeNodeLinks>>,
    symbols: Vec<Option<SymbolNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    declared: Vec<Option<DeclaredTypeLinks>>,
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
    let owners = nodes
        .iter()
        .filter_map(|node| checker.file(FILE).unwrap().1.symbol(*node))
        .map(|symbol| store.get_merged_symbol(symbol).unwrap())
        .collect::<Vec<_>>();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.conditional_root_len(),
            store.symbol_store().symbol_table_len(),
        ],
        types: nodes
            .iter()
            .map(|node| store.type_node_links(*node).cloned())
            .collect(),
        symbols: nodes
            .iter()
            .map(|node| store.symbol_node_links(*node).cloned())
            .collect(),
        signatures: nodes
            .iter()
            .map(|node| store.signature_links(*node).cloned())
            .collect(),
        values: owners
            .iter()
            .map(|owner| store.value_symbol_links(*owner).cloned())
            .collect(),
        declared: owners
            .iter()
            .map(|owner| store.declared_type_links(*owner).cloned())
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
    types: &[(NodeRef, TypeId)],
    returns: &[(SignatureId, TypeId)],
) {
    for &(location, expected) in types {
        assert_eq!(checker.get_type_at_location(location), Ok(expected));
    }
    for &(signature, expected) in returns {
        assert_eq!(
            checker.get_return_type_of_signature(signature),
            Ok(expected)
        );
    }
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    let warm = snapshot(checker, parsed);
    for recheck in [false, true] {
        if recheck {
            checker.recheck_source_file(FILE).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        for &(location, expected) in types {
            assert_eq!(checker.get_type_at_location(location), Ok(expected));
        }
        for &(signature, expected) in returns {
            assert_eq!(
                checker.get_return_type_of_signature(signature),
                Ok(expected)
            );
        }
        assert_eq!(snapshot(checker, parsed), warm);
        assert!(checker.store().type_resolution_is_empty());
    }
}

struct GenericFunctionParts {
    function: NodeRef,
    parameter: NodeRef,
    constraint: NodeRef,
    returned: NodeRef,
    selected: NodeRef,
    unselected: NodeRef,
}

fn generic_function_parts(parsed: &ParseResult, function: NodeRef) -> GenericFunctionParts {
    let NodeData::FunctionTypeNode(data) = &parsed.arena.get(function.node).unwrap().data else {
        panic!("the callback annotation must remain a real FunctionType")
    };
    assert!(data.parameters.nodes.is_empty());
    let [parameter] = data.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("the callback must retain exactly one type parameter")
    };
    let NodeData::TypeParameterDeclaration(parameter_data) =
        &parsed.arena.get(*parameter).unwrap().data
    else {
        unreachable!()
    };
    let returned = data.type_.unwrap();
    let NodeData::ConditionalTypeNode(conditional) = &parsed.arena.get(returned).unwrap().data
    else {
        panic!("the written callback return must remain a conditional type")
    };
    GenericFunctionParts {
        function,
        parameter: node(parsed, *parameter),
        constraint: node(parsed, parameter_data.constraint.unwrap()),
        returned: node(parsed, returned),
        selected: node(parsed, conditional.true_type),
        unselected: node(parsed, conditional.false_type),
    }
}

struct ContextualFunctionParts {
    binding: NamedDeclaration,
    annotation: NodeRef,
    expression: NodeRef,
    parameter: NamedDeclaration,
    target_parameter: NamedDeclaration,
    generic: GenericFunctionParts,
    literal: NodeRef,
}

fn contextual_function_parts(parsed: &ParseResult) -> ContextualFunctionParts {
    let binding = named_declaration(parsed, only_node(parsed, SyntaxKind::VariableDeclaration));
    let NodeData::VariableDeclaration(variable) =
        &parsed.arena.get(binding.declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let annotation = node(parsed, variable.type_.unwrap());
    let NodeData::FunctionTypeNode(target) = &parsed.arena.get(annotation.node).unwrap().data
    else {
        panic!("adapt must retain its nongeneric function type annotation")
    };
    assert!(target.type_parameters.is_none());
    let [target_parameter] = target.parameters.nodes.as_slice() else {
        panic!("adapt must have one contextual parameter")
    };
    let NodeData::ParameterDeclaration(target_data) =
        &parsed.arena.get(*target_parameter).unwrap().data
    else {
        unreachable!()
    };
    let expression = node(parsed, variable.initializer.unwrap());
    let NodeData::FunctionExpression(function) = &parsed.arena.get(expression.node).unwrap().data
    else {
        panic!("adapt must use an actual FunctionExpression")
    };
    assert!(function.type_parameters.is_none());
    assert!(function.type_.is_none());
    let [parameter] = function.parameters.nodes.as_slice() else {
        panic!("the function expression must retain its one source parameter")
    };
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(*parameter).unwrap().data
    else {
        unreachable!()
    };
    assert!(parameter_data.type_.is_none());
    let NodeData::Block(body) = &parsed.arena.get(function.body).unwrap().data else {
        panic!("the function must keep its block body")
    };
    let [returned] = body.statements.nodes.as_slice() else {
        panic!("the body must contain only its written return")
    };
    let NodeData::ReturnStatement(returned) = &parsed.arena.get(*returned).unwrap().data else {
        unreachable!()
    };
    ContextualFunctionParts {
        binding,
        annotation,
        expression,
        parameter: named_declaration(parsed, node(parsed, *parameter)),
        target_parameter: named_declaration(parsed, node(parsed, *target_parameter)),
        generic: generic_function_parts(parsed, node(parsed, target_data.type_.unwrap())),
        literal: node(parsed, returned.expression.unwrap()),
    }
}

struct ContextualCallables {
    source: TypeId,
    target: TypeId,
    nested: TypeId,
    source_signature: SignatureId,
    target_signature: SignatureId,
    nested_signature: SignatureId,
}

fn contextual_callables(
    checker: &mut CanonicalCheckerContext<'_>,
    parts: &ContextualFunctionParts,
) -> ContextualCallables {
    let source = checker.get_type_at_location(parts.expression).unwrap();
    let target = checker.get_type_at_location(parts.annotation).unwrap();
    let nested = checker
        .get_type_from_type_node(parts.generic.function)
        .unwrap();
    assert_ne!(source, target);
    assert_ne!(nested, source);
    assert_ne!(nested, target);
    for (type_, declaration) in [
        (source, parts.expression),
        (target, parts.annotation),
        (nested, parts.generic.function),
    ] {
        assert_eq!(
            checker.store().type_payload(type_).unwrap().symbol(),
            Some(symbol(checker, declaration))
        );
    }
    let parameter = assert_value(
        checker,
        parts.parameter,
        nested,
        SymbolFlags::FUNCTION_SCOPED_VARIABLE,
    );
    let target_parameter = assert_value(
        checker,
        parts.target_parameter,
        nested,
        SymbolFlags::FUNCTION_SCOPED_VARIABLE,
    );
    assert_ne!(parameter, target_parameter);
    let binding = assert_value(
        checker,
        parts.binding,
        target,
        SymbolFlags::BLOCK_SCOPED_VARIABLE,
    );
    assert_ne!(binding, symbol(checker, parts.expression));
    let source_signature = callable_signature(checker, source);
    let target_signature = callable_signature(checker, target);
    let nested_signature = callable_signature(checker, nested);
    assert_ne!(source_signature, target_signature);
    assert_ne!(source_signature, nested_signature);
    assert_ne!(target_signature, nested_signature);
    assert_signature(
        checker,
        source_signature,
        parts.expression,
        &[parameter],
        &[],
    );
    assert_signature(
        checker,
        target_signature,
        parts.annotation,
        &[target_parameter],
        &[],
    );
    ContextualCallables {
        source,
        target,
        nested,
        source_signature,
        target_signature,
        nested_signature,
    }
}

fn demand_generic_return(
    checker: &mut CanonicalCheckerContext<'_>,
    parts: &GenericFunctionParts,
    signature: SignatureId,
) -> TypeId {
    let type_parameter = symbol(checker, parts.parameter);
    let inner = checker
        .store()
        .declared_type_links(type_parameter)
        .unwrap()
        .declared_type
        .unwrap();
    assert_signature(checker, signature, parts.function, &[], &[inner]);
    assert_eq!(
        checker
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type(),
        None
    );
    for node in [parts.returned, parts.selected, parts.unselected] {
        assert!(checker.store().type_node_links(node).is_none());
    }
    let record = checker.store().type_payload(inner).unwrap();
    assert_eq!(record.symbol(), Some(type_parameter));
    let TypeData::TypeParameter(generic) = record.data() else {
        panic!("the reduced return must use the original K type")
    };
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(generic.constraint, Some(number));
    assert!(generic.target.is_none());
    assert!(generic.mapper.is_none());
    let owner = checker.store().symbol(type_parameter).unwrap();
    assert_eq!(owner.flags(), SymbolFlags::TYPE_PARAMETER);
    assert_eq!(owner.declarations(), Some(&[parts.parameter][..]));
    assert!(owner.value_declaration().is_none());
    assert_eq!(checker.get_return_type_of_signature(signature), Ok(inner));
    assert_eq!(checker.get_type_from_type_node(parts.returned), Ok(inner));
    assert_eq!(checker.get_type_from_type_node(parts.selected), Ok(inner));
    assert!(checker.store().type_node_links(parts.unselected).is_none());
    inner
}

#[test]
fn contextual_function_parameter_keeps_its_generic_function_type_and_lazy_return() {
    let parsed = parse_source_file(
        "const adapt: (callback: <K extends number>() => number extends number ? K : string) => 1 = function(callback) { return 1; };",
    );
    let parts = contextual_function_parts(&parsed);
    for first in [None, Some(parts.generic.function), Some(parts.expression)] {
        let mut checker = context(&parsed, CanonicalSourceLanguage::TypeScript);
        let early = first.map(|node| checker.get_type_at_location(node).unwrap());
        checker.check_source_file(FILE).unwrap();
        let ContextualCallables {
            source,
            target,
            nested,
            source_signature,
            target_signature,
            nested_signature,
        } = contextual_callables(&mut checker, &parts);
        let inner = demand_generic_return(&mut checker, &parts.generic, nested_signature);
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let returned = checker
            .get_return_type_of_signature(source_signature)
            .unwrap();
        assert_eq!(
            checker.get_return_type_of_signature(target_signature),
            Ok(returned)
        );
        assert_eq!(checker.type_to_string(returned).unwrap(), "1");
        let literal = checker.get_type_at_location(parts.literal).unwrap();
        let TypeData::Literal(literal_data) = checker.store().type_payload(literal).unwrap().data()
        else {
            panic!("the body must keep its actual numeric literal")
        };
        assert_eq!(literal_data.regular_type, returned);
        if let Some(early) = early {
            assert_eq!(
                early,
                if first == Some(parts.generic.function) {
                    nested
                } else {
                    source
                }
            );
        }
        assert_replay(
            &mut checker,
            &parsed,
            &[
                (parts.expression, source),
                (parts.annotation, target),
                (parts.binding.name, target),
                (parts.parameter.name, nested),
                (parts.target_parameter.name, nested),
                (parts.generic.function, nested),
                (parts.generic.constraint, number),
                (parts.generic.returned, inner),
                (parts.generic.selected, inner),
                (parts.literal, literal),
            ],
            &[
                (source_signature, returned),
                (target_signature, returned),
                (nested_signature, inner),
            ],
        );
    }
}

fn binding(parsed: &ParseResult, expected: &str) -> NamedDeclaration {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            (record.kind == SyntaxKind::BindingElement)
                .then(|| named_declaration(parsed, node(parsed, id)))
                .filter(|binding| node_text(parsed, binding.name) == expected)
        })
        .unwrap_or_else(|| panic!("missing binding {expected}"))
}

fn assert_jsdoc_overload_key(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    call: NodeRef,
) -> (TypeId, SignatureId, SignatureId) {
    let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        unreachable!()
    };
    let declarations = source
        .statements
        .nodes
        .iter()
        .filter_map(|id| {
            (parsed.arena.get(*id).unwrap().kind == SyntaxKind::FunctionDeclaration)
                .then_some(node(parsed, *id))
        })
        .collect::<Vec<_>>();
    let [overload, implementation] = declarations.as_slice() else {
        panic!("one real overload declaration must precede its implementation")
    };
    let owner = symbol(checker, *overload);
    assert_eq!(symbol(checker, *implementation), owner);
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(record.declarations(), Some(declarations.as_slice()));
    assert_eq!(record.value_declaration(), Some(*overload));
    let public = signature(checker, *overload);
    let body = signature(checker, *implementation);
    assert_ne!(public, body);
    let callable = checker.get_type_at_location(*overload).unwrap();
    assert_eq!(callable_signature(checker, callable), public);
    assert_eq!(
        checker.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    let mut names = Vec::new();
    for (declaration, expected_signature, has_body) in
        [(*overload, public, false), (*implementation, body, true)]
    {
        let record = parsed.arena.get(declaration.node).unwrap();
        let NodeData::FunctionDeclaration(function) = &record.data else {
            unreachable!()
        };
        assert_eq!(record.parent, Some(parsed.source_file));
        assert_eq!(
            record.flags,
            if has_body {
                NodeFlags::default()
            } else {
                NodeFlags::REPARSED
            }
        );
        assert_eq!(function.body.is_some(), has_body);
        assert!(function.type_parameters.is_none());
        assert!(function.parameters.nodes.is_empty());
        assert_signature(checker, expected_signature, declaration, &[], &[]);
        let name = node(parsed, function.name.unwrap());
        names.push(name);
        assert_eq!(checker.get_symbol_at_location(name), Ok(Some(owner)));
        assert_eq!(checker.get_type_at_location(name), Ok(callable));
        assert_eq!(checker.get_type_at_location(declaration), Ok(callable));
    }
    assert_ne!(names[0], names[1]);
    assert_eq!(
        parsed.arena.get(names[0].node).unwrap().range,
        parsed.arena.get(names[1].node).unwrap().range
    );
    assert_eq!(node_text(parsed, *overload), "overload");
    let key = checker.get_type_at_location(call).unwrap();
    assert_eq!(checker.type_to_string(key).unwrap(), "\"value\"");
    assert_eq!(signature(checker, call), public);
    assert_ne!(signature(checker, call), body);
    assert_eq!(checker.get_return_type_of_signature(public), Ok(key));
    assert_eq!(checker.get_return_type_of_signature(body), Ok(key));
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    assert!(call_data.arguments.nodes.is_empty());
    assert!(call_data.type_arguments.is_none());
    let callee = node(parsed, call_data.expression);
    assert_eq!(checker.get_symbol_at_location(callee), Ok(Some(owner)));
    assert_eq!(checker.get_type_at_location(callee), Ok(callable));
    (key, public, body)
}

fn structured_fields(data: &TypeData) -> Option<&StructuredTypeData> {
    match data {
        TypeData::Object(data) => Some(&data.structured),
        TypeData::TypeReference(data) => Some(&data.object.structured),
        TypeData::Interface(data) => Some(&data.reference.object.structured),
        TypeData::Tuple(data) => Some(&data.interface.reference.object.structured),
        TypeData::InstantiationExpression(data) => Some(&data.object.structured),
        TypeData::Mapped(data) => Some(&data.object.structured),
        TypeData::ReverseMapped(data) => Some(&data.object.structured),
        TypeData::EvolvingArray(data) => Some(&data.object.structured),
        TypeData::Union(data) => Some(&data.union.structured),
        TypeData::Intersection(data) => Some(&data.intersection.structured),
        _ => None,
    }
}

fn assert_rest_property(checker: &mut CanonicalCheckerContext<'_>, rest: TypeId) {
    assert_eq!(checker.type_to_string(rest).unwrap(), "{ keep: boolean; }");
    let structured = structured_fields(checker.store().type_payload(rest).unwrap().data()).unwrap();
    let [property] = structured.properties.as_deref().unwrap() else {
        panic!("rest must exclude only the value property")
    };
    assert_eq!(
        checker.store().symbol(*property).unwrap().name().as_utf8(),
        Some("keep")
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(*property)
            .unwrap()
            .resolved_type,
        Some(checker.store().intrinsic_bootstrap().unwrap().boolean_type)
    );
}

#[test]
fn named_jsdoc_overload_call_keeps_its_literal_computed_binding_and_rest_key() {
    let parsed = parse_javascript_source_file(concat!(
        "/** @overload @returns {'value'} */\n",
        "/** @returns {'value'} */\n",
        "function key() { return 'value'; }\n",
        "const { [key()]: selected, ...rest } = { value: 1, keep: true };\n",
        "const observed = selected;\n",
    ));
    let selected = binding(&parsed, "selected");
    let rest = binding(&parsed, "rest");
    let call = only_node(&parsed, SyntaxKind::CallExpression);
    let computed = only_node(&parsed, SyntaxKind::ComputedPropertyName);
    assert_eq!(
        parsed.arena.get(call.node).unwrap().parent,
        Some(computed.node)
    );
    assert_eq!(
        parsed.arena.get(computed.node).unwrap().parent,
        Some(selected.declaration.node)
    );
    let observed = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            (node_text(&parsed, node(&parsed, variable.name)) == "observed")
                .then(|| node(&parsed, variable.initializer.unwrap()))
        })
        .unwrap();
    for query_first in [false, true] {
        let mut checker = context(&parsed, CanonicalSourceLanguage::JavaScript);
        let early = query_first.then(|| checker.get_type_at_location(selected.name).unwrap());
        checker.check_source_file(FILE).unwrap();
        let (key, public, implementation) = assert_jsdoc_overload_key(&mut checker, &parsed, call);
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let selected_symbol = assert_value(
            &mut checker,
            selected,
            number,
            SymbolFlags::BLOCK_SCOPED_VARIABLE,
        );
        let rest_type = checker.get_type_at_location(rest.name).unwrap();
        let rest_symbol = assert_value(
            &mut checker,
            rest,
            rest_type,
            SymbolFlags::BLOCK_SCOPED_VARIABLE,
        );
        assert_ne!(selected_symbol, rest_symbol);
        assert_eq!(
            checker.get_type_at_location(selected.declaration),
            Ok(number)
        );
        assert_eq!(
            checker.get_type_at_location(rest.declaration),
            Ok(rest_type)
        );
        assert_eq!(
            checker.get_symbol_at_location(observed),
            Ok(Some(selected_symbol))
        );
        assert_eq!(checker.get_type_at_location(observed), Ok(number));
        assert_rest_property(&mut checker, rest_type);
        if let Some(early) = early {
            assert_eq!(early, number);
        }
        assert_replay(
            &mut checker,
            &parsed,
            &[
                (call, key),
                (selected.declaration, number),
                (selected.name, number),
                (rest.declaration, rest_type),
                (rest.name, rest_type),
                (observed, number),
            ],
            &[(public, key), (implementation, key)],
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Check one receiver and contextual signature through each query order.
fn contextual_function_this_keeps_receiver_and_value_parameter_identities() {
    let parsed = parse_source_file(
        "const read: (input: string) => number = function(this: { value: number }, input) { return this.value; };",
    );
    let binding = named_declaration(&parsed, only_node(&parsed, SyntaxKind::VariableDeclaration));
    let NodeData::VariableDeclaration(variable) =
        &parsed.arena.get(binding.declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let expression = node(&parsed, variable.initializer.unwrap());
    let annotation = node(&parsed, variable.type_.unwrap());
    let NodeData::FunctionExpression(function) = &parsed.arena.get(expression.node).unwrap().data
    else {
        panic!("the source must retain its ordinary function expression")
    };
    assert!(function.type_.is_none());
    let [receiver, input] = function.parameters.nodes.as_slice() else {
        panic!("the source must retain its receiver and one value parameter")
    };
    let receiver = named_declaration(&parsed, node(&parsed, *receiver));
    let input = named_declaration(&parsed, node(&parsed, *input));
    let NodeData::ParameterDeclaration(receiver_data) =
        &parsed.arena.get(receiver.declaration.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(node_text(&parsed, receiver.name), "this");
    let receiver_annotation = node(&parsed, receiver_data.type_.unwrap());
    let NodeData::ParameterDeclaration(input_data) =
        &parsed.arena.get(input.declaration.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(input_data.type_.is_none());
    let NodeData::FunctionTypeNode(contextual) = &parsed.arena.get(annotation.node).unwrap().data
    else {
        panic!("the variable must retain its written function type")
    };
    let [target_input] = contextual.parameters.nodes.as_slice() else {
        panic!("the target must have one value parameter and no receiver")
    };
    let target_input = named_declaration(&parsed, node(&parsed, *target_input));
    let body = only_node(&parsed, SyntaxKind::PropertyAccessExpression);
    let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(body.node).unwrap().data
    else {
        unreachable!()
    };
    let this_read = node(&parsed, property.expression);
    let property_name = node(&parsed, property.name);
    let property_declaration = only_node(&parsed, SyntaxKind::PropertyDeclaration);
    assert_eq!(
        parsed.arena.get(this_read.node).unwrap().kind,
        SyntaxKind::ThisKeyword
    );

    for first in [None, Some(expression), Some(body)] {
        let mut checker = context(&parsed, CanonicalSourceLanguage::TypeScript);
        let early = first.map(|node| checker.get_type_at_location(node).unwrap());
        checker.check_source_file(FILE).unwrap();
        let source = checker.get_type_at_location(expression).unwrap();
        let target = checker.get_type_at_location(annotation).unwrap();
        let receiver_type = checker
            .get_type_from_type_node(receiver_annotation)
            .unwrap();
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        assert_ne!(source, target);
        for (type_, declaration) in [
            (source, expression),
            (target, annotation),
            (receiver_type, receiver_annotation),
        ] {
            assert_eq!(
                checker.store().type_payload(type_).unwrap().symbol(),
                Some(symbol(&checker, declaration))
            );
        }
        let owner = symbol(&checker, expression);
        let owner_record = checker.store().symbol(owner).unwrap();
        assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
        assert_eq!(owner_record.declarations(), Some(&[expression][..]));
        assert_eq!(owner_record.value_declaration(), Some(expression));
        let receiver_symbol = assert_value(
            &mut checker,
            receiver,
            receiver_type,
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
        );
        let input_symbol = assert_value(
            &mut checker,
            input,
            string,
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
        );
        let target_input_symbol = assert_value(
            &mut checker,
            target_input,
            string,
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
        );
        assert_ne!(receiver_symbol, input_symbol);
        assert_ne!(receiver_symbol, target_input_symbol);
        assert_ne!(input_symbol, target_input_symbol);
        assert_ne!(
            assert_value(
                &mut checker,
                binding,
                target,
                SymbolFlags::BLOCK_SCOPED_VARIABLE
            ),
            owner
        );

        let source_signature = callable_signature(&checker, source);
        let target_signature = callable_signature(&checker, target);
        assert_ne!(source_signature, target_signature);
        let signature = checker.store().signature(source_signature).unwrap();
        assert_eq!(signature.declaration(), Some(expression));
        assert_eq!(signature.this_parameter(), Some(receiver_symbol));
        assert_eq!(signature.parameters(), &[input_symbol]);
        assert_eq!(signature.min_argument_count(), 1);
        assert!(signature.type_parameters().is_empty());
        assert!(signature.target().is_none());
        assert!(signature.mapper().is_none());
        assert_signature(
            &checker,
            target_signature,
            annotation,
            &[target_input_symbol],
            &[],
        );
        assert_eq!(
            checker.file(FILE).unwrap().1.this_container(this_read),
            Some(expression)
        );
        assert_eq!(
            checker.file(FILE).unwrap().1.container(this_read),
            Some(expression)
        );
        assert_eq!(
            checker.get_symbol_at_location(this_read),
            Ok(Some(receiver_symbol))
        );
        assert_eq!(checker.get_type_at_location(this_read), Ok(receiver_type));
        let property_symbol = symbol(&checker, property_declaration);
        assert_eq!(
            checker.get_symbol_at_location(property_name),
            Ok(Some(property_symbol))
        );
        assert_eq!(checker.get_type_at_location(body), Ok(number));
        if let Some(early) = early {
            assert_eq!(
                early,
                if first == Some(expression) {
                    source
                } else {
                    number
                }
            );
        }
        assert_replay(
            &mut checker,
            &parsed,
            &[
                (expression, source),
                (annotation, target),
                (binding.name, target),
                (receiver.declaration, receiver_type),
                (receiver.name, receiver_type),
                (receiver_annotation, receiver_type),
                (input.declaration, string),
                (input.name, string),
                (target_input.declaration, string),
                (target_input.name, string),
                (this_read, receiver_type),
                (body, number),
            ],
            &[(source_signature, number), (target_signature, number)],
        );
    }
}
