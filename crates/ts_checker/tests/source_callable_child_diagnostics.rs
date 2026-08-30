use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostic, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId, SignatureLinks,
    SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(202_910);
const FILE: FileId = FileId::new(202_911);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const BOXES: &str = concat!(
    "interface TextBox { value: string }\n",
    "interface NumberBox { value: number }\n",
    "declare const numberBox: NumberBox;\n",
);

fn context<'arena>(
    library: &'arena ParseResult,
    parsed: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (LIBRARY, library, "\"/lib.es5.d.ts\"", true),
        (FILE, parsed, "\"/project/callable-children.ts\"", false),
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
                ),
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

fn text(parsed: &ParseResult, location: NodeRef) -> &str {
    let range = parsed.arena.get(location.node).unwrap().range;
    &parsed.arena.source_text().unwrap()[range.start.get() as usize..range.end.get() as usize]
}

struct Variable {
    declaration: NodeRef,
    name: NodeRef,
    annotation: Option<NodeRef>,
    initializer: NodeRef,
}

fn variable(parsed: &ParseResult, expected: &str) -> Variable {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| Variable {
                declaration: node(parsed, id),
                name: node(parsed, variable.name),
                annotation: variable.type_.map(|id| node(parsed, id)),
                initializer: node(parsed, variable.initializer.unwrap()),
            })
        })
        .unwrap_or_else(|| panic!("missing initialized variable {expected}"))
}

fn method(parsed: &ParseResult, object: NodeRef) -> NodeRef {
    let NodeData::ObjectLiteralExpression(object) = &parsed.arena.get(object.node).unwrap().data
    else {
        panic!("expected the source object literal")
    };
    let methods = object
        .properties
        .nodes
        .iter()
        .copied()
        .filter(|id| parsed.arena.get(*id).unwrap().kind == SyntaxKind::MethodDeclaration)
        .collect::<Vec<_>>();
    let [method] = methods.as_slice() else {
        panic!("expected one actual object method")
    };
    node(parsed, *method)
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn interface_type(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    expected: &str,
) -> TypeId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(node(parsed, id))
        })
        .unwrap();
    let owner = symbol(checker, declaration);
    let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
    assert_eq!(
        checker.store().type_payload(type_).unwrap().symbol(),
        Some(owner)
    );
    type_
}

fn callable_signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the real callable object")
    };
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one call signature")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    *signature
}

fn resolved_signature(checker: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(location)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

#[derive(Debug, Eq, PartialEq)]
struct CallableState {
    owner: SemanticSymbolId,
    type_: TypeId,
    signature: SignatureId,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    returned: TypeId,
}

fn callable_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    declaration: NodeRef,
) -> CallableState {
    let record = parsed.arena.get(declaration.node).unwrap();
    let (parameters, annotation, flags) = match &record.data {
        NodeData::FunctionExpression(function) => {
            (&function.parameters, function.type_, SymbolFlags::FUNCTION)
        }
        NodeData::MethodDeclaration(method) => {
            (&method.parameters, method.type_, SymbolFlags::METHOD)
        }
        _ => panic!("expected a source function expression or object method"),
    };
    let type_ = checker.get_type_at_location(declaration).unwrap();
    let owner = symbol(checker, declaration);
    let stored = checker.store().symbol(owner).unwrap();
    assert_eq!(stored.flags(), flags);
    assert_eq!(stored.declarations(), Some(&[declaration][..]));
    assert_eq!(stored.value_declaration(), Some(declaration));
    assert_eq!(
        checker.store().type_payload(type_).unwrap().symbol(),
        Some(owner)
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type,
        Some(type_)
    );
    let signature = callable_signature(checker, type_);
    assert_eq!(resolved_signature(checker, declaration), signature);
    let parameters = parameters
        .nodes
        .iter()
        .map(|&id| {
            let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(id).unwrap().data
            else {
                panic!("expected a source parameter")
            };
            let owner = symbol(checker, node(parsed, id));
            let name = node(parsed, parameter.name);
            let type_ = checker.get_type_at_location(name).unwrap();
            assert_eq!(checker.get_symbol_at_location(name), Ok(Some(owner)));
            assert_eq!(
                checker.get_type_at_location(node(parsed, parameter.type_.unwrap())),
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
    assert_eq!(
        checker.get_type_at_location(node(parsed, annotation.unwrap())),
        Ok(returned)
    );
    let stored = checker.store().signature(signature).unwrap();
    assert_eq!(stored.declaration(), Some(declaration));
    assert_eq!(
        stored.parameters(),
        parameters
            .iter()
            .map(|&(owner, _)| owner)
            .collect::<Vec<_>>()
    );
    assert_eq!(
        stored.min_argument_count(),
        i32::try_from(parameters.len()).unwrap()
    );
    assert_eq!(stored.resolved_return_type(), Some(returned));
    assert!(stored.type_parameters().is_empty());
    assert!(stored.this_parameter().is_none());
    assert!(stored.target().is_none());
    assert!(stored.mapper().is_none());
    CallableState {
        owner,
        type_,
        signature,
        parameters,
        returned,
    }
}

fn assert_primary(
    diagnostic: &CanonicalCheckerDiagnostic,
    parsed: &ParseResult,
    expected_node: NodeRef,
    expected_text: &str,
    code: u32,
    message: &str,
) {
    assert_eq!(diagnostic.node, Some(expected_node));
    assert_eq!(text(parsed, expected_node), expected_text);
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    types: Vec<Option<TypeNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    symbols: Vec<Option<SymbolNodeLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
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
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        types: nodes
            .iter()
            .map(|&node| store.type_node_links(node).cloned())
            .collect(),
        signatures: nodes
            .iter()
            .map(|&node| store.signature_links(node).cloned())
            .collect(),
        symbols: nodes
            .iter()
            .map(|&node| store.symbol_node_links(node).cloned())
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
        diagnostics: checker.diagnostics().clone(),
    }
}

fn assert_replay(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    locations: &[NodeRef],
) {
    let types = locations
        .iter()
        .map(|&node| checker.get_type_at_location(node).unwrap())
        .collect::<Vec<_>>();
    let before = snapshot(checker, parsed);
    checker.check_source_file(FILE).unwrap();
    assert_eq!(snapshot(checker, parsed), before);
    for _ in 0..2 {
        checker.recheck_source_file(FILE).unwrap();
        for (&node, &type_) in locations.iter().zip(&types) {
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
        }
        assert_eq!(snapshot(checker, parsed), before);
    }
}

#[test]
fn function_parameter_children_take_priority_over_an_incompatible_return() {
    let library = parse_source_file(ES5);
    let source = format!(
        "{BOXES}const assigned: (value: NumberBox) => NumberBox = function(value: TextBox): TextBox {{ return value; }};\n\
         const called = assigned(numberBox);\n"
    );
    let parsed = parse_source_file(&source);
    let assigned = variable(&parsed, "assigned");
    let called = variable(&parsed, "called").initializer;
    for query_first in [false, true] {
        let mut checker = context(&library, &parsed);
        if query_first {
            checker.get_type_at_location(assigned.initializer).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        let state = callable_state(&mut checker, &parsed, assigned.initializer);
        let number_box = interface_type(&mut checker, &parsed, "NumberBox");
        let text_box = interface_type(&mut checker, &parsed, "TextBox");
        assert_eq!(state.parameters[0].1, text_box);
        assert_eq!(state.returned, text_box);
        let target = checker
            .get_type_at_location(assigned.annotation.unwrap())
            .unwrap();
        let target_signature = callable_signature(&checker, target);
        let target_parameter = checker
            .store()
            .signature(target_signature)
            .unwrap()
            .parameters()[0];
        assert_eq!(
            checker
                .store()
                .value_symbol_links(target_parameter)
                .unwrap()
                .resolved_type,
            Some(number_box)
        );
        assert_eq!(
            checker.get_return_type_of_signature(target_signature),
            Ok(number_box)
        );
        assert_ne!(target_signature, state.signature);
        assert_eq!(checker.get_type_at_location(assigned.name), Ok(target));
        assert_eq!(checker.get_type_at_location(called), Ok(number_box));
        assert_eq!(resolved_signature(&checker, called), target_signature);
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("expected one parameter mismatch")
        };
        assert_primary(
            diagnostic,
            &parsed,
            assigned.name,
            "assigned",
            2322,
            concat!(
                "Type '(value: TextBox) => TextBox' is not assignable to type '(value: NumberBox) => NumberBox'.\n",
                "  Types of parameters 'value' and 'value' are incompatible.\n",
                "    Type 'NumberBox' is not assignable to type 'TextBox'.\n",
                "      Types of property 'value' are incompatible.\n",
                "        Type 'number' is not assignable to type 'string'.",
            ),
        );
        assert!(diagnostic.related_information.is_empty());
        assert_replay(
            &mut checker,
            &parsed,
            &[assigned.initializer, assigned.name, called],
        );
        assert_eq!(
            callable_state(&mut checker, &parsed, assigned.initializer),
            state
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Check both diagnostic chains and each real call signature together.
fn returned_callable_children_survive_assignment_and_call_diagnostics() {
    let library = parse_source_file(ES5);
    let parsed = parse_source_file(concat!(
        "declare function numberCallback(): number;\n",
        "declare function accepts(callback: () => () => string): void;\n",
        "const source = function(): () => number { return numberCallback; };\n",
        "const assigned: () => () => string = source;\n",
        "const rejected = accepts(source);\n",
        "const actual = source();\n",
        "const actualValue = actual();\n",
        "const expected = assigned();\n",
        "const expectedValue = expected();\n",
    ));
    let source = variable(&parsed, "source");
    let assigned = variable(&parsed, "assigned");
    let rejected = variable(&parsed, "rejected").initializer;
    let NodeData::CallExpression(call) = &parsed.arena.get(rejected.node).unwrap().data else {
        unreachable!()
    };
    let argument = node(&parsed, call.arguments.nodes[0]);
    let mut checker = context(&library, &parsed);
    checker.get_type_at_location(source.initializer).unwrap();
    checker.check_source_file(FILE).unwrap();
    let state = callable_state(&mut checker, &parsed, source.initializer);
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
    let inner_signature = callable_signature(&checker, state.returned);
    assert_eq!(
        checker.get_return_type_of_signature(inner_signature),
        Ok(number)
    );
    let target = checker
        .get_type_at_location(assigned.annotation.unwrap())
        .unwrap();
    let target_signature = callable_signature(&checker, target);
    let target_return = checker
        .get_return_type_of_signature(target_signature)
        .unwrap();
    let target_inner = callable_signature(&checker, target_return);
    assert_eq!(
        checker.get_return_type_of_signature(target_inner),
        Ok(string)
    );
    assert_ne!(state.returned, target_return);
    assert_eq!(checker.get_type_at_location(argument), Ok(state.type_));
    assert_eq!(
        checker.get_symbol_at_location(argument),
        Ok(Some(symbol(&checker, source.declaration)))
    );
    assert_eq!(checker.get_type_at_location(rejected), Ok(void));
    let calls = ["actual", "actualValue", "expected", "expectedValue"]
        .map(|name| variable(&parsed, name).initializer);
    for ((call, returned), signature) in calls
        .into_iter()
        .zip([state.returned, number, target_return, string])
        .zip([
            state.signature,
            inner_signature,
            target_signature,
            target_inner,
        ])
    {
        assert_eq!(checker.get_type_at_location(call), Ok(returned));
        assert_eq!(resolved_signature(&checker, call), signature);
    }
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    assert_primary(
        &diagnostics[0],
        &parsed,
        assigned.name,
        "assigned",
        2322,
        concat!(
            "Type '() => () => number' is not assignable to type '() => () => string'.\n",
            "  Type '() => number' is not assignable to type '() => string'.\n",
            "    Type 'number' is not assignable to type 'string'.",
        ),
    );
    assert_primary(
        &diagnostics[1],
        &parsed,
        argument,
        "source",
        2345,
        concat!(
            "Argument of type '() => () => number' is not assignable to parameter of type '() => () => string'.\n",
            "  Type '() => number' is not assignable to type '() => string'.\n",
            "    Type 'number' is not assignable to type 'string'.",
        ),
    );
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.related_information.is_empty())
    );
    assert_replay(
        &mut checker,
        &parsed,
        &[
            source.initializer,
            assigned.name,
            argument,
            rejected,
            calls[0],
            calls[1],
            calls[2],
            calls[3],
        ],
    );
    assert_eq!(
        callable_state(&mut checker, &parsed, source.initializer),
        state
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the method, receiver, target note, and argument site in one control.
fn object_method_children_keep_assignment_notes_and_callable_argument_sites() {
    let library = parse_source_file(ES5);
    let source = format!(
        "{BOXES}\
         interface NarrowBox {{ value: number; extra: string; }}\n\
         interface Expected {{ run(value: NumberBox): TextBox; }}\n\
         declare function accepts(callback: (value: NumberBox) => TextBox): void;\n\
         const object = {{ run(value: NumberBox): NumberBox {{ return value; }} }};\n\
         const assigned: Expected = {{ run(value: NarrowBox): NumberBox {{ return value; }} }};\n\
         const rejected = accepts(object.run);\n\
         const result = object.run(numberBox);\n"
    );
    let parsed = parse_source_file(&source);
    let object = variable(&parsed, "object");
    let assigned = variable(&parsed, "assigned");
    let object_method = method(&parsed, object.initializer);
    let assigned_method = method(&parsed, assigned.initializer);
    let NodeData::MethodDeclaration(method) = &parsed.arena.get(assigned_method.node).unwrap().data
    else {
        unreachable!()
    };
    let method_name = node(&parsed, method.name);
    let target_method = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            (record.kind == SyntaxKind::MethodSignature).then_some(node(&parsed, id))
        })
        .unwrap();
    let rejected = variable(&parsed, "rejected").initializer;
    let NodeData::CallExpression(call) = &parsed.arena.get(rejected.node).unwrap().data else {
        unreachable!()
    };
    let argument = node(&parsed, call.arguments.nodes[0]);
    let NodeData::PropertyAccessExpression(access) = &parsed.arena.get(argument.node).unwrap().data
    else {
        unreachable!()
    };
    let receiver_node = node(&parsed, access.expression);
    let result = variable(&parsed, "result").initializer;
    let mut checker = context(&library, &parsed);
    checker.check_source_file(FILE).unwrap();
    let actual = callable_state(&mut checker, &parsed, object_method);
    let assigned_state = callable_state(&mut checker, &parsed, assigned_method);
    let number_box = interface_type(&mut checker, &parsed, "NumberBox");
    let narrow_box = interface_type(&mut checker, &parsed, "NarrowBox");
    let text_box = interface_type(&mut checker, &parsed, "TextBox");
    let expected = interface_type(&mut checker, &parsed, "Expected");
    assert_ne!(actual.owner, assigned_state.owner);
    assert_eq!(actual.parameters[0].1, number_box);
    assert_eq!(assigned_state.parameters[0].1, narrow_box);
    assert_eq!(
        checker.is_type_assignable_to(narrow_box, number_box),
        Ok(true)
    );
    assert_eq!(
        checker.is_type_assignable_to(number_box, narrow_box),
        Ok(false)
    );
    for state in [&actual, &assigned_state] {
        assert_eq!(state.returned, number_box);
    }
    let receiver = checker.get_type_at_location(receiver_node).unwrap();
    assert_eq!(checker.get_type_at_location(object.name), Ok(receiver));
    assert_eq!(
        checker.get_symbol_at_location(receiver_node),
        Ok(Some(symbol(&checker, object.declaration)))
    );
    let proxy = checker.get_symbol_at_location(argument).unwrap().unwrap();
    let TypeData::Object(receiver_object) = checker.store().type_payload(receiver).unwrap().data()
    else {
        panic!("expected the source object's receiver type")
    };
    let members = receiver_object.structured.members.unwrap();
    assert_eq!(
        checker
            .store()
            .symbol_table(members)
            .unwrap()
            .get_source("run"),
        Some(proxy)
    );
    assert_eq!(
        checker.store().symbol(proxy).unwrap().flags(),
        SymbolFlags::METHOD | SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
    );
    assert_eq!(
        checker.store().value_symbol_links(proxy).unwrap().target,
        Some(actual.owner)
    );
    assert_eq!(checker.get_type_at_location(argument), Ok(actual.type_));
    assert_eq!(checker.get_type_at_location(assigned.name), Ok(expected));
    let target_type = checker.get_type_at_location(target_method).unwrap();
    let target_signature = callable_signature(&checker, target_type);
    assert_eq!(
        checker
            .store()
            .signature(target_signature)
            .unwrap()
            .declaration(),
        Some(target_method)
    );
    assert_eq!(
        checker.get_return_type_of_signature(target_signature),
        Ok(text_box)
    );
    assert_eq!(checker.get_type_at_location(result), Ok(number_box));
    assert_eq!(resolved_signature(&checker, result), actual.signature);
    let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
    assert_eq!(checker.get_type_at_location(rejected), Ok(void));
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    assert_primary(
        &diagnostics[0],
        &parsed,
        method_name,
        "run",
        2322,
        concat!(
            "Type '(value: NarrowBox) => NumberBox' is not assignable to type '(value: NumberBox) => TextBox'.\n",
            "  Type 'NumberBox' is not assignable to type 'TextBox'.\n",
            "    Types of property 'value' are incompatible.\n",
            "      Type 'number' is not assignable to type 'string'.",
        ),
    );
    let [related] = diagnostics[0].related_information.as_slice() else {
        panic!("expected the target method declaration")
    };
    assert_eq!(related.node, Some(target_method));
    assert_eq!(
        text(&parsed, target_method),
        "run(value: NumberBox): TextBox;"
    );
    assert_eq!(related.diagnostic.code(), 6500);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "The expected type comes from property 'run' which is declared here on type 'Expected'"
    );
    assert_primary(
        &diagnostics[1],
        &parsed,
        argument,
        "object.run",
        2345,
        concat!(
            "Argument of type '(value: NumberBox) => NumberBox' is not assignable to parameter of type '(value: NumberBox) => TextBox'.\n",
            "  Type 'NumberBox' is not assignable to type 'TextBox'.\n",
            "    Types of property 'value' are incompatible.\n",
            "      Type 'number' is not assignable to type 'string'.",
        ),
    );
    assert!(diagnostics[1].related_information.is_empty());
    assert_replay(
        &mut checker,
        &parsed,
        &[
            object_method,
            assigned_method,
            receiver_node,
            assigned.name,
            target_method,
            argument,
            rejected,
            result,
        ],
    );
    assert_eq!(callable_state(&mut checker, &parsed, object_method), actual);
    assert_eq!(
        callable_state(&mut checker, &parsed, assigned_method),
        assigned_state
    );
}

#[test]
fn callable_property_children_precede_a_neighboring_property_error() {
    let library = parse_source_file(ES5);
    let source = format!(
        "{BOXES}\
         interface Source {{ run(value: TextBox): number; neighbor: number; }}\n\
         interface Target {{ run(value: NumberBox): number; neighbor: string; }}\n\
         const object: Source = {{ run(value: TextBox): number {{ return 1; }}, neighbor: 1 }};\n\
         const assigned: Target = object;\n"
    );
    let parsed = parse_source_file(&source);
    let object = variable(&parsed, "object");
    let assigned = variable(&parsed, "assigned");
    let method = method(&parsed, object.initializer);
    let mut checker = context(&library, &parsed);
    checker.check_source_file(FILE).unwrap();
    let state = callable_state(&mut checker, &parsed, method);
    let source_type = interface_type(&mut checker, &parsed, "Source");
    let target_type = interface_type(&mut checker, &parsed, "Target");
    let text_box = interface_type(&mut checker, &parsed, "TextBox");
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(state.parameters[0].1, text_box);
    assert_eq!(state.returned, number);
    assert_eq!(checker.get_type_at_location(object.name), Ok(source_type));
    assert_eq!(
        checker.get_type_at_location(assigned.initializer),
        Ok(source_type)
    );
    assert_eq!(checker.get_type_at_location(assigned.name), Ok(target_type));
    for (owner, expected) in [(source_type, number), (target_type, string)] {
        let TypeData::Interface(interface) = checker.store().type_payload(owner).unwrap().data()
        else {
            panic!("expected the named source interface")
        };
        let members = interface.reference.object.structured.members.unwrap();
        let property = checker
            .store()
            .symbol_table(members)
            .unwrap()
            .get_source("neighbor")
            .unwrap();
        assert_eq!(
            checker
                .store()
                .value_symbol_links(property)
                .unwrap()
                .resolved_type,
            Some(expected)
        );
    }
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected the first incompatible property only")
    };
    assert_primary(
        diagnostic,
        &parsed,
        assigned.name,
        "assigned",
        2322,
        concat!(
            "Type 'Source' is not assignable to type 'Target'.\n",
            "  Types of property 'run' are incompatible.\n",
            "    Type '(value: TextBox) => number' is not assignable to type '(value: NumberBox) => number'.\n",
            "      Types of parameters 'value' and 'value' are incompatible.\n",
            "        Type 'NumberBox' is not assignable to type 'TextBox'.\n",
            "          Types of property 'value' are incompatible.\n",
            "            Type 'number' is not assignable to type 'string'.",
        ),
    );
    assert!(diagnostic.related_information.is_empty());
    assert_replay(
        &mut checker,
        &parsed,
        &[method, object.name, assigned.initializer, assigned.name],
    );
    assert_eq!(callable_state(&mut checker, &parsed, method), state);
}
