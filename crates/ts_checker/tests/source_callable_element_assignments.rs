use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_710);
const LIBRARIES: &[(&str, &str)] = &[
    (
        "lib.es5.d.ts",
        include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
    ),
    (
        "lib.decorators.d.ts",
        include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
    ),
    (
        "lib.decorators.legacy.d.ts",
        include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
    ),
];

const GENERIC: &str = concat!(
    "function replaceAt<T>(array: Array<T>, index: number, value: T): Array<T> {\n",
    "  const copy = array.slice(0);\n",
    "  copy[index] = value;\n",
    "  return copy;\n",
    "}\n",
    "declare const numbers: Array<number>;\n",
    "declare const strings: Array<string>;\n",
    "const numberCopy = replaceAt(numbers, 0, 1);\n",
    "const stringCopy = replaceAt(strings, 0, \"next\");\n",
);

const INVALID: &str = concat!(
    "function invalid(values: number[], fixed: readonly number[], index: number, bad: string, value: number): void {\n",
    "  values[index] = bad;\n",
    "  fixed[index] = value;\n",
    "}\n",
);

struct Fixture {
    text: &'static str,
    source: ParseResult,
    libraries: Vec<ParseResult>,
}

impl Fixture {
    fn new(text: &'static str) -> Self {
        let parse = |text| {
            let parsed = parse_source_file(text);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            parsed
        };
        Self {
            text,
            source: parse(text),
            libraries: LIBRARIES.iter().map(|(_, text)| parse(text)).collect(),
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let files = self
            .libraries
            .iter()
            .enumerate()
            .map(|(index, parsed)| {
                (
                    FileId::new(u32::try_from(index).unwrap()),
                    parsed,
                    format!("\"/lib/{}\"", LIBRARIES[index].0),
                    true,
                )
            })
            .chain([(
                FILE,
                &self.source,
                "\"/project/callable-element-assignments.ts\"".to_owned(),
                false,
            )])
            .collect::<Vec<_>>();
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, library) in &files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    *file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        *library,
                        *library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (file, parsed, _, _) in &files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, *file)
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
                strict_function_types: true,
                no_implicit_any: true,
                no_unchecked_indexed_access: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn expression(&self, kind: SyntaxKind, text: &str) -> NodeRef {
        let mut matches = self.source.arena.iter().filter_map(|(id, record)| {
            (record.kind == kind
                && &self.text[record.range.start.get() as usize..record.range.end.get() as usize]
                    == text)
                .then_some(node(&self.source, id))
        });
        let result = matches.next().unwrap_or_else(|| panic!("missing {text}"));
        assert!(matches.next().is_none(), "duplicate {text}");
        result
    }
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let owner = parsed.arena.get(parent.node).unwrap();
    let record = parsed.arena.get(id).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(owner.range.start <= record.range.start && record.range.end <= owner.range.end);
    node(parsed, id)
}

fn named(parsed: &ParseResult, name: &str) -> (NodeRef, NodeRef) {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        let name_id = match &record.data {
            NodeData::FunctionDeclaration(data) => data.name?,
            NodeData::VariableDeclaration(data) => data.name,
            _ => return None,
        };
        let NodeData::Identifier(identifier) = &parsed.arena.get(name_id)?.data else {
            return None;
        };
        (identifier.text == name).then_some((node(parsed, id), node(parsed, name_id)))
    });
    let result = matches.next().unwrap();
    assert!(matches.next().is_none(), "duplicate {name}");
    result
}

fn variable(parsed: &ParseResult, name: &str) -> (NodeRef, NodeRef, NodeRef) {
    let (declaration, name) = named(parsed, name);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a variable declaration");
    };
    (
        declaration,
        name,
        child(parsed, declaration, data.initializer.unwrap()),
    )
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn selected(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(node)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

fn callable_signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(callable) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the function's canonical callable object");
    };
    let [signature] = callable.structured.signatures.as_deref().unwrap() else {
        panic!("expected one function signature");
    };
    *signature
}

fn assert_array(
    checker: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    target: TypeId,
    element: TypeId,
) {
    let record = checker.store().type_payload(type_).unwrap();
    let TypeData::TypeReference(reference) = record.data() else {
        panic!("expected a canonical array reference: {record:?}");
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[element][..])
    );
}

fn assignment(fixture: &Fixture, text: &str) -> [NodeRef; 5] {
    let parsed = &fixture.source;
    let assignment = fixture.expression(SyntaxKind::BinaryExpression, text);
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        unreachable!()
    };
    let operator = child(parsed, assignment, binary.operator_token);
    assert_eq!(
        parsed.arena.get(operator.node).unwrap().kind,
        SyntaxKind::EqualsToken
    );
    let left = child(parsed, assignment, binary.left);
    let right = child(parsed, assignment, binary.right);
    let NodeData::ElementAccessExpression(element) = &parsed.arena.get(left.node).unwrap().data
    else {
        panic!("expected the actual element assignment target");
    };
    assert!(element.question_dot_token.is_none());
    [
        assignment,
        left,
        child(parsed, left, element.expression),
        child(parsed, left, element.argument_expression),
        right,
    ]
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = checker.store();
    (
        [
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
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = node(parsed, id);
                (
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect::<Vec<_>>(),
        store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        checker.diagnostics().clone(),
    )
}

fn replay(
    fixture: &Fixture,
    checker: &mut CanonicalCheckerContext<'_>,
    locations: &[(NodeRef, TypeId)],
    symbols: &[(NodeRef, SemanticSymbolId)],
    signatures: &[(SignatureId, TypeId)],
) {
    let observe = |checker: &mut CanonicalCheckerContext<'_>| {
        for &(node, type_) in locations {
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
        }
        for &(node, symbol) in symbols {
            assert_eq!(checker.get_symbol_at_location(node), Ok(Some(symbol)));
        }
        for &(signature, returned) in signatures {
            assert_eq!(
                checker.get_return_type_of_signature(signature),
                Ok(returned)
            );
        }
    };
    observe(checker);
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(FILE).unwrap())
            .unwrap()
            .type_checked
    );
    let before = snapshot(checker, &fixture.source);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        observe(checker);
        assert_eq!(snapshot(checker, &fixture.source), before);
        assert!(checker.store().type_resolution_is_empty());
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep source ownership, generic substitution and replay together.
fn generic_slice_copy_element_assignment_keeps_its_type_parameter_and_replay() {
    let fixture = Fixture::new(GENERIC);
    let parsed = &fixture.source;
    let (function, _) = named(parsed, "replaceAt");
    let NodeData::FunctionDeclaration(data) = &parsed.arena.get(function.node).unwrap().data else {
        unreachable!()
    };
    let formal = child(
        parsed,
        function,
        data.type_parameters.as_ref().unwrap().nodes[0],
    );
    let parameters = data
        .parameters
        .nodes
        .iter()
        .map(|&id| child(parsed, function, id))
        .collect::<Vec<_>>();
    let (copy, copy_name, slice) = variable(parsed, "copy");
    let [write, target, receiver, index, value] = assignment(&fixture, "copy[index] = value");
    let NodeData::CallExpression(call) = &parsed.arena.get(slice.node).unwrap().data else {
        panic!("the copy must use the actual slice call");
    };
    let access = child(parsed, slice, call.expression);
    let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(access.node).unwrap().data
    else {
        unreachable!()
    };
    let array_read = child(parsed, access, property.expression);
    let returned = fixture.expression(SyntaxKind::ReturnStatement, "return copy;");
    let NodeData::ReturnStatement(return_) = &parsed.arena.get(returned.node).unwrap().data else {
        unreachable!()
    };
    let returned = child(parsed, returned, return_.expression.unwrap());
    for query_first in [false, true] {
        let mut checker = fixture.context();
        if query_first {
            checker.get_type_at_location(slice).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().as_slice().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let function_type = checker.get_type_at_location(function).unwrap();
        let function_signature = callable_signature(&checker, function_type);
        let record = checker.store().signature(function_signature).unwrap();
        assert_eq!(record.declaration(), Some(function));
        let [parameter] = record.type_parameters() else {
            panic!("the function must keep its own type parameter");
        };
        let parameter = *parameter;
        let formal_record = checker.store().type_payload(parameter).unwrap();
        assert!(matches!(formal_record.data(), TypeData::TypeParameter(_)));
        assert_eq!(formal_record.symbol(), Some(symbol(&checker, formal)));
        let parameter_symbols = parameters
            .iter()
            .map(|&node| symbol(&checker, node))
            .collect::<Vec<_>>();
        assert_eq!(record.parameters(), parameter_symbols);
        let result = checker.get_type_at_location(slice).unwrap();
        assert_array(
            &checker,
            result,
            checker.global_types().array_type,
            parameter,
        );
        assert_eq!(
            checker.get_return_type_of_signature(function_signature),
            Ok(result)
        );
        let slice_signature = selected(&checker, slice);
        assert_eq!(
            checker.get_return_type_of_signature(slice_signature),
            Ok(result)
        );
        let declaration = checker
            .store()
            .signature(slice_signature)
            .unwrap()
            .declaration()
            .unwrap();
        assert_eq!(declaration.file, FileId::new(0));
        let library = &fixture.libraries[0];
        assert_eq!(declaration.arena, library.arena.id());
        let method = library.arena.get(declaration.node).unwrap();
        assert_eq!(method.kind, SyntaxKind::MethodSignature);
        let NodeData::MethodSignatureDeclaration(method_data) = &method.data else {
            panic!("slice must use the bundled method declaration");
        };
        let NodeData::Identifier(name) = &library.arena.get(method_data.name).unwrap().data else {
            unreachable!()
        };
        assert_eq!(name.text, "slice");
        let owner = NodeRef::new(library.arena.id(), FileId::new(0), method.parent.unwrap());
        let NodeData::InterfaceDeclaration(interface) =
            &library.arena.get(owner.node).unwrap().data
        else {
            panic!("slice must belong to the real Array interface");
        };
        assert!(interface.members.nodes.contains(&declaration.node));
        assert_eq!(
            checker
                .store()
                .type_payload(checker.global_types().array_type)
                .unwrap()
                .symbol(),
            Some(symbol(&checker, owner))
        );
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        let mut locations = vec![
            (function, function_type),
            (slice, result),
            (copy_name, result),
            (array_read, result),
            (receiver, result),
            (index, number),
            (target, parameter),
            (value, parameter),
            (write, parameter),
            (returned, result),
        ];
        let mut signatures = vec![(function_signature, result), (slice_signature, result)];
        for (name, element) in [("numberCopy", number), ("stringCopy", string)] {
            let (_, name, call) = variable(parsed, name);
            let actual = checker.get_type_at_location(call).unwrap();
            assert_array(&checker, actual, checker.global_types().array_type, element);
            locations.extend([(name, actual), (call, actual)]);
            signatures.push((selected(&checker, call), actual));
        }
        let copy_symbol = symbol(&checker, copy);
        let reads = [
            (array_read, parameter_symbols[0]),
            (receiver, copy_symbol),
            (index, parameter_symbols[1]),
            (value, parameter_symbols[2]),
            (returned, copy_symbol),
            (access, symbol(&checker, declaration)),
        ];
        for &(read, _) in &reads[..5] {
            assert_eq!(
                checker.file(FILE).unwrap().1.flow_container(read),
                Some(function)
            );
        }
        replay(&fixture, &mut checker, &locations, &reads, &signatures);
    }
}

#[test]
fn callable_element_assignments_keep_incompatible_and_readonly_errors() {
    let fixture = Fixture::new(INVALID);
    let mut checker = fixture.context();
    checker.check_source_file(FILE).unwrap();
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    let [bad_write, bad_target, values, bad_index, bad] =
        assignment(&fixture, "values[index] = bad");
    let [fixed_write, fixed_target, fixed, fixed_index, value] =
        assignment(&fixture, "fixed[index] = value");
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    for (diagnostic, node, code, text) in [
        (
            &diagnostics[0],
            bad_target,
            2322,
            "Type 'string' is not assignable to type 'number'.",
        ),
        (
            &diagnostics[1],
            fixed_target,
            2542,
            "Index signature in type 'readonly number[]' only permits reading.",
        ),
    ] {
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), text);
        assert!(diagnostic.diagnostic.details.is_empty());
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
    }
    let values_type = checker.get_type_at_location(values).unwrap();
    let fixed_type = checker.get_type_at_location(fixed).unwrap();
    assert_array(
        &checker,
        values_type,
        checker.global_types().array_type,
        number,
    );
    assert_array(
        &checker,
        fixed_type,
        checker.global_types().readonly_array_type,
        number,
    );
    let locations = [
        (values, values_type),
        (fixed, fixed_type),
        (bad_index, number),
        (fixed_index, number),
        (bad_target, number),
        (fixed_target, number),
        (bad, string),
        (value, number),
        (bad_write, string),
        (fixed_write, number),
    ];
    replay(&fixture, &mut checker, &locations, &[], &[]);
}
