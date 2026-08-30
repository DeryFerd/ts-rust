use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostic, CanonicalCheckerDiagnosticRange,
    CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId, TypeData, TypeId,
    signatures::{ElementFlags, SignatureFlags},
};
use ts_core::TextRange;
use ts_parser::{ParseResult, parse_source_file};

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-implements-rest-methods.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
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

fn declaration(parsed: &ParseResult, file: FileId, expected: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name = match &record.data {
                NodeData::ClassDeclaration(class) => class.name?,
                NodeData::InterfaceDeclaration(interface) => interface.name,
                NodeData::TypeAliasDeclaration(alias) => alias.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some((
                NodeRef::new(parsed.arena.id(), file, node),
                NodeRef::new(parsed.arena.id(), file, name),
            ))
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"))
}

fn methods(parsed: &ParseResult, owner: NodeRef) -> Vec<(NodeRef, NodeRef)> {
    let members = match &parsed.arena.get(owner.node).unwrap().data {
        NodeData::ClassDeclaration(class) => &class.members.nodes,
        NodeData::InterfaceDeclaration(interface) => &interface.members.nodes,
        _ => panic!("expected a class or interface"),
    };
    members
        .iter()
        .filter_map(|&member| {
            let name = match &parsed.arena.get(member)?.data {
                NodeData::MethodDeclaration(method) => method.name,
                NodeData::MethodSignatureDeclaration(method) => method.name,
                _ => return None,
            };
            Some((
                NodeRef::new(owner.arena, owner.file, member),
                NodeRef::new(owner.arena, owner.file, name),
            ))
        })
        .collect()
}

fn parameter(parsed: &ParseResult, method: NodeRef) -> (NodeRef, NodeRef) {
    let parameters = match &parsed.arena.get(method.node).unwrap().data {
        NodeData::MethodDeclaration(method) => &method.parameters.nodes,
        NodeData::MethodSignatureDeclaration(method) => &method.parameters.nodes,
        _ => panic!("expected a method"),
    };
    let [node] = parameters.as_slice() else {
        panic!("expected one source parameter")
    };
    let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(*node).unwrap().data else {
        panic!("expected a parameter declaration")
    };
    (
        NodeRef::new(method.arena, method.file, *node),
        NodeRef::new(method.arena, method.file, parameter.type_.unwrap()),
    )
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn call_signatures(
    context: &CanonicalCheckerContext<'_>,
    method: SemanticSymbolId,
) -> Vec<SignatureId> {
    let callable = value_type(context, method);
    let record = context.store().type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(method));
    let TypeData::Object(object) = record.data() else {
        panic!("a method retains its callable object")
    };
    let signatures = object.structured.signatures.as_ref().unwrap();
    assert_eq!(object.structured.call_signature_count, signatures.len());
    signatures.clone()
}

fn class_instance(
    context: &CanonicalCheckerContext<'_>,
    owner: SemanticSymbolId,
    properties: &[SemanticSymbolId],
) -> TypeId {
    let type_ = context
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap();
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Interface(class) = record.data() else {
        panic!("the class retains its instance type")
    };
    assert_eq!(
        class.declared_members,
        context.store().symbol(owner).unwrap().members()
    );
    assert_eq!(
        class.reference.object.structured.properties.as_deref(),
        (!properties.is_empty()).then_some(properties)
    );
    assert_eq!(class.resolved_base_types, None);
    assert_eq!(
        class.resolved_base_constructor_type,
        Some(
            context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .undefined_type
        )
    );
    type_
}

fn tuple_elements(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> Vec<TypeId> {
    let TypeData::TypeReference(reference) = context.store().type_payload(type_).unwrap().data()
    else {
        panic!("each nonempty tuple retains its canonical reference")
    };
    let arguments = reference.resolved_type_arguments.as_ref().unwrap();
    let target = reference.object.target.unwrap();
    let TypeData::Tuple(tuple) = context.store().type_payload(target).unwrap().data() else {
        panic!("the reference retains a tuple target")
    };
    assert_eq!(tuple.metadata.min_length(), arguments.len());
    assert_eq!(tuple.metadata.fixed_length(), arguments.len());
    assert!(!tuple.metadata.is_readonly());
    assert!(tuple.metadata.element_infos().iter().all(|element| {
        element.flags() == ElementFlags::REQUIRED && element.labeled_declaration().is_none()
    }));
    arguments.clone()
}

fn assert_rest_signature(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    method: NodeRef,
    signature: SignatureId,
) -> TypeId {
    let (parameter, annotation) = parameter(parsed, method);
    let parameter_symbol = symbol(context, parameter);
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(method));
    assert_eq!(record.flags(), SignatureFlags::HAS_REST_PARAMETER);
    assert_eq!(record.parameters(), [parameter_symbol]);
    assert_eq!(record.min_argument_count(), 0);
    assert_eq!(
        record.resolved_return_type(),
        Some(context.store().intrinsic_bootstrap().unwrap().void_type)
    );
    let rest = value_type(context, parameter_symbol);
    assert_eq!(
        context
            .store()
            .type_node_links(annotation)
            .unwrap()
            .resolved_type,
        Some(rest)
    );
    let TypeData::Union(union) = context.store().type_payload(rest).unwrap().data() else {
        panic!("the original rest parameter retains the whole tuple union")
    };
    assert_eq!(union.union.types.len(), 2);
    let mut elements = union
        .union
        .types
        .iter()
        .map(|&type_| tuple_elements(context, type_))
        .collect::<Vec<_>>();
    elements.sort_by_key(Vec::len);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        elements,
        [
            vec![bootstrap.number_type],
            vec![bootstrap.string_type, bootstrap.boolean_type]
        ]
    );
    rest
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    file: FileId,
    type_symbols: &[SemanticSymbolId],
    value_symbols: &[SemanticSymbolId],
    nodes: &[NodeRef],
) {
    let types = type_symbols
        .iter()
        .map(|&symbol| context.get_declared_type_of_symbol(symbol).unwrap())
        .collect::<Vec<_>>();
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        (
            [
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().index_info_len(),
                context.store().type_alias_len(),
                context.store().symbol_store().symbol_table_len(),
            ],
            context.store().relation_state_snapshot(),
            context.diagnostics().clone(),
            value_symbols
                .iter()
                .map(|&symbol| {
                    (
                        context.store().declared_type_links(symbol).cloned(),
                        context.store().value_symbol_links(symbol).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            nodes
                .iter()
                .map(|&node| {
                    (
                        context.store().type_node_links(node).cloned(),
                        context.store().signature_links(node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            context
                .store()
                .signatures()
                .map(|(id, signature)| {
                    (
                        id,
                        signature.flags(),
                        signature.declaration(),
                        signature.parameters().to_vec(),
                        signature.min_argument_count(),
                        signature.resolved_return_type(),
                    )
                })
                .collect::<Vec<_>>(),
        )
    };
    let warm = snapshot(context);
    context.check_source_file(file).unwrap();
    context.recheck_source_file(file).unwrap();
    for (&symbol, expected) in type_symbols.iter().zip(types) {
        assert_eq!(
            context.get_declared_type_of_symbol(symbol).unwrap(),
            expected
        );
    }
    assert_eq!(snapshot(context), warm);
    assert!(
        context
            .store()
            .source_file_links(context.source_file(file).unwrap())
            .unwrap()
            .type_checked
    );
}

fn assert_diagnostic(
    diagnostic: &CanonicalCheckerDiagnostic,
    node: NodeRef,
    code: u32,
    arguments: &[&str],
    rendered: &str,
) {
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.diagnostic.arguments, arguments);
    assert_eq!(diagnostic.diagnostic.render().unwrap(), rendered);
}

#[test]
fn tuple_rest_implementation_keeps_method_bivariance_and_source_signatures() {
    for (source, returns_number) in [
        (
            concat!(
                "interface Array<T> {} interface ReadonlyArray<T> {}\n",
                "interface Contract { run(...args: [number] | [string, boolean]): void; }\n",
                "type StrictCall = (...args: [number] | [string, boolean]) => void;\n",
                "class Model implements Contract { run(value: number): void {} }\n",
            ),
            false,
        ),
        (
            concat!(
                "interface Array<T> {} interface ReadonlyArray<T> {}\n",
                "class Model implements Contract { run(value: number): number { return value; } }\n",
                "interface Contract { run(...args: [number] | [string, boolean]): void; }\n",
                "type StrictCall = (...args: [number] | [string, boolean]) => void;\n",
            ),
            true,
        ),
    ] {
        let parsed = parse_source_file(source);
        let file = FileId::new(5_220);
        let mut context = context(&parsed, file);
        let class = declaration(&parsed, file, "Model").0;
        let contract = declaration(&parsed, file, "Contract").0;
        let strict = symbol(&context, declaration(&parsed, file, "StrictCall").0);
        let own_method = methods(&parsed, class)[0].0;
        let target_method = methods(&parsed, contract)[0].0;
        let owner = symbol(&context, class);
        let contract_symbol = symbol(&context, contract);
        let own_symbol = symbol(&context, own_method);
        let target_symbol = symbol(&context, target_method);
        let (own_parameter, _) = parameter(&parsed, own_method);
        let (target_parameter, rest_annotation) = parameter(&parsed, target_method);
        let own_parameter_symbol = symbol(&context, own_parameter);
        let target_parameter_symbol = symbol(&context, target_parameter);

        context.check_source_file(file).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        assert!(context.options().strict_function_types);
        assert_ne!(own_symbol, target_symbol);
        assert_eq!(
            context.store().symbol(own_symbol).unwrap().parent(),
            Some(owner)
        );
        assert_eq!(
            context.store().symbol(target_symbol).unwrap().parent(),
            Some(contract_symbol)
        );
        let own_signatures = call_signatures(&context, own_symbol);
        let [own_signature] = own_signatures.as_slice() else {
            panic!("the class publishes one original method signature")
        };
        let own_signature = *own_signature;
        let own_record = context.store().signature(own_signature).unwrap();
        assert_eq!(own_record.declaration(), Some(own_method));
        assert_eq!(own_record.flags(), SignatureFlags::NONE);
        assert_eq!(own_record.parameters(), [own_parameter_symbol]);
        assert_eq!(own_record.min_argument_count(), 1);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            own_record.resolved_return_type(),
            Some(if returns_number {
                bootstrap.number_type
            } else {
                bootstrap.void_type
            })
        );
        assert_eq!(
            value_type(&context, own_parameter_symbol),
            bootstrap.number_type
        );
        let mut observed_nodes = vec![own_method, target_method, rest_annotation];
        if returns_number {
            let NodeData::MethodDeclaration(method) =
                &parsed.arena.get(own_method.node).unwrap().data
            else {
                panic!("expected the source method")
            };
            let NodeData::Block(body) = &parsed.arena.get(method.body.unwrap()).unwrap().data
            else {
                panic!("the method keeps its source body")
            };
            let NodeData::ReturnStatement(statement) =
                &parsed.arena.get(body.statements.nodes[0]).unwrap().data
            else {
                panic!("the method returns its parameter")
            };
            let returned = NodeRef::new(own_method.arena, file, statement.expression.unwrap());
            assert_eq!(
                context
                    .store()
                    .type_node_links(returned)
                    .unwrap()
                    .resolved_type,
                Some(bootstrap.number_type)
            );
            observed_nodes.push(returned);
        }
        let target_signatures = call_signatures(&context, target_symbol);
        let [target_signature] = target_signatures.as_slice() else {
            panic!("the interface publishes its one rest signature")
        };
        let target_signature = *target_signature;
        assert_ne!(own_signature, target_signature);
        let rest = assert_rest_signature(&context, &parsed, target_method, target_signature);
        assert_eq!(
            context.get_type_from_type_node(rest_annotation).unwrap(),
            rest
        );
        let instance = class_instance(&context, owner, &[own_symbol]);
        let contract_type = context
            .get_declared_type_of_symbol(contract_symbol)
            .unwrap();
        assert_eq!(
            context.is_type_assignable_to(instance, contract_type),
            Ok(true)
        );
        let own_callable = value_type(&context, own_symbol);
        let target_callable = value_type(&context, target_symbol);
        assert_eq!(
            context.is_type_assignable_to(own_callable, target_callable),
            Ok(true)
        );
        let strict_callable = context.get_declared_type_of_symbol(strict).unwrap();
        assert_eq!(
            context.is_type_assignable_to(own_callable, strict_callable),
            Ok(false)
        );
        assert_replay(
            &mut context,
            file,
            &[contract_symbol, strict],
            &[
                owner,
                contract_symbol,
                own_symbol,
                target_symbol,
                own_parameter_symbol,
                target_parameter_symbol,
            ],
            &observed_nodes,
        );
    }
}

#[test]
fn missing_tuple_rest_method_reports_the_real_interface_declaration() {
    let parsed = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {}\n",
        "interface Contract { run(...args: [number] | [string, boolean]): void; }\n",
        "class Model implements Contract {}\n",
    ));
    let file = FileId::new(5_221);
    let mut context = context(&parsed, file);
    let (class, class_name) = declaration(&parsed, file, "Model");
    let contract = declaration(&parsed, file, "Contract").0;
    let (method, method_name) = methods(&parsed, contract)[0];
    let owner = symbol(&context, class);
    let contract_symbol = symbol(&context, contract);
    let method_symbol = symbol(&context, method);

    context.check_source_file(file).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "expected one missing method error: {:?}",
            context.diagnostics()
        )
    };
    assert_diagnostic(
        diagnostic,
        class_name,
        2420,
        &["Model", "Contract"],
        concat!(
            "Class 'Model' incorrectly implements interface 'Contract'.\n",
            "  Property 'run' is missing in type 'Model' but required in type 'Contract'.",
        ),
    );
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("the missing method retains its declaration note")
    };
    assert_eq!(related.node, Some(method_name));
    assert_eq!(related.diagnostic.code(), 2728);
    assert_eq!(related.diagnostic.arguments, ["run"]);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "'run' is declared here."
    );
    let target_type = context
        .get_declared_type_of_symbol(contract_symbol)
        .unwrap();
    let instance = class_instance(&context, owner, &[]);
    assert_eq!(
        context.is_type_assignable_to(instance, target_type),
        Ok(false)
    );
    let signature = call_signatures(&context, method_symbol)[0];
    assert_rest_signature(&context, &parsed, method, signature);
    assert_replay(
        &mut context,
        file,
        &[contract_symbol],
        &[owner, contract_symbol, method_symbol],
        &[class, method],
    );
}

#[test]
fn incompatible_required_method_reports_the_own_name_and_parameter_order() {
    let parsed = parse_source_file(concat!(
        "interface Contract { run(expected: string): void; }\n",
        "class Model implements Contract { run(actual: number): void {} }\n",
    ));
    let file = FileId::new(5_222);
    let mut context = context(&parsed, file);
    let class = declaration(&parsed, file, "Model").0;
    let contract = declaration(&parsed, file, "Contract").0;
    let (own_method, own_name) = methods(&parsed, class)[0];
    let target_method = methods(&parsed, contract)[0].0;
    let owner = symbol(&context, class);
    let contract_symbol = symbol(&context, contract);
    let own_symbol = symbol(&context, own_method);
    let target_symbol = symbol(&context, target_method);

    context.check_source_file(file).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one own method error: {:?}", context.diagnostics())
    };
    assert_diagnostic(
        diagnostic,
        own_name,
        2416,
        &["run", "Model", "Contract"],
        concat!(
            "Property 'run' in type 'Model' is not assignable to the same property in base type 'Contract'.\n",
            "  Type '(actual: number) => void' is not assignable to type '(expected: string) => void'.\n",
            "    Types of parameters 'actual' and 'expected' are incompatible.\n",
            "      Type 'string' is not assignable to type 'number'.",
        ),
    );
    assert!(diagnostic.related_information.is_empty());
    let target_type = context
        .get_declared_type_of_symbol(contract_symbol)
        .unwrap();
    let instance = class_instance(&context, owner, &[own_symbol]);
    assert_eq!(
        context.is_type_assignable_to(instance, target_type),
        Ok(false)
    );
    assert_replay(
        &mut context,
        file,
        &[contract_symbol],
        &[owner, own_symbol, target_symbol],
        &[own_method, target_method],
    );
}

#[test]
fn method_return_mismatch_does_not_report_bivariant_parameters() {
    let parsed = parse_source_file(concat!(
        "interface Contract { run(expected: unknown): string; }\n",
        "class Model implements Contract { run(actual: number): boolean { return false; } }\n",
    ));
    let file = FileId::new(5_225);
    let mut context = context(&parsed, file);
    let class = declaration(&parsed, file, "Model").0;
    let contract = declaration(&parsed, file, "Contract").0;
    let (own_method, own_name) = methods(&parsed, class)[0];
    let target_method = methods(&parsed, contract)[0].0;
    let owner = symbol(&context, class);
    let contract_symbol = symbol(&context, contract);
    let own_symbol = symbol(&context, own_method);
    let target_symbol = symbol(&context, target_method);

    context.check_source_file(file).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "expected one return type error: {:?}",
            context.diagnostics()
        )
    };
    assert_diagnostic(
        diagnostic,
        own_name,
        2416,
        &["run", "Model", "Contract"],
        concat!(
            "Property 'run' in type 'Model' is not assignable to the same property in base type 'Contract'.\n",
            "  Type '(actual: number) => boolean' is not assignable to type '(expected: unknown) => string'.\n",
            "    Type 'boolean' is not assignable to type 'string'.",
        ),
    );
    assert!(diagnostic.related_information.is_empty());
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (number, unknown) = (bootstrap.number_type, bootstrap.unknown_type);
    assert_eq!(context.is_type_assignable_to(number, unknown), Ok(true));
    assert_eq!(context.is_type_assignable_to(unknown, number), Ok(false));
    let source = value_type(&context, own_symbol);
    let target = value_type(&context, target_symbol);
    assert_eq!(context.is_type_assignable_to(source, target), Ok(false));
    let instance = class_instance(&context, owner, &[own_symbol]);
    let contract_type = context
        .get_declared_type_of_symbol(contract_symbol)
        .unwrap();
    assert_eq!(
        context.is_type_assignable_to(instance, contract_type),
        Ok(false)
    );
    assert_replay(
        &mut context,
        file,
        &[contract_symbol],
        &[owner, own_symbol, target_symbol],
        &[own_method, target_method],
    );
}

#[test]
fn implemented_method_keeps_every_real_target_overload() {
    let parsed = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {}\n",
        "interface Contract {\n",
        "  run(...args: [number] | [string, boolean]): void;\n",
        "  run(value: [boolean]): void;\n",
        "}\n",
        "class Model implements Contract { run(): void {} }\n",
    ));
    let file = FileId::new(5_223);
    let mut context = context(&parsed, file);
    let class = declaration(&parsed, file, "Model").0;
    let contract = declaration(&parsed, file, "Contract").0;
    let target_methods = methods(&parsed, contract);
    assert_eq!(target_methods.len(), 2);
    let own_method = methods(&parsed, class)[0].0;
    let owner = symbol(&context, class);
    let contract_symbol = symbol(&context, contract);
    let own_symbol = symbol(&context, own_method);
    let target_symbol = symbol(&context, target_methods[0].0);
    assert_eq!(symbol(&context, target_methods[1].0), target_symbol);
    assert_ne!(own_symbol, target_symbol);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let targets = call_signatures(&context, target_symbol);
    assert_eq!(targets.len(), 2);
    assert_ne!(targets[0], targets[1]);
    assert_rest_signature(&context, &parsed, target_methods[0].0, targets[0]);
    let fixed = context.store().signature(targets[1]).unwrap();
    let (fixed_parameter, fixed_annotation) = parameter(&parsed, target_methods[1].0);
    let fixed_parameter = symbol(&context, fixed_parameter);
    assert_eq!(fixed.declaration(), Some(target_methods[1].0));
    assert_eq!(fixed.flags(), SignatureFlags::NONE);
    assert_eq!(fixed.min_argument_count(), 1);
    assert_eq!(fixed.parameters(), [fixed_parameter]);
    let required_tuple = value_type(&context, fixed_parameter);
    assert_eq!(
        tuple_elements(&context, required_tuple),
        [context.store().intrinsic_bootstrap().unwrap().boolean_type]
    );
    assert_eq!(
        context
            .store()
            .type_node_links(fixed_annotation)
            .unwrap()
            .resolved_type,
        Some(required_tuple)
    );
    let source = call_signatures(&context, own_symbol);
    assert_eq!(source.len(), 1);
    let source = context.store().signature(source[0]).unwrap();
    assert_eq!(source.declaration(), Some(own_method));
    assert_eq!(source.flags(), SignatureFlags::NONE);
    assert_eq!(source.min_argument_count(), 0);
    assert!(source.parameters().is_empty());
    let target_type = context
        .get_declared_type_of_symbol(contract_symbol)
        .unwrap();
    let instance = class_instance(&context, owner, &[own_symbol]);
    assert_eq!(
        context.is_type_assignable_to(instance, target_type),
        Ok(true)
    );
    assert_replay(
        &mut context,
        file,
        &[contract_symbol],
        &[owner, own_symbol, target_symbol, fixed_parameter],
        &[
            own_method,
            target_methods[0].0,
            target_methods[1].0,
            fixed_annotation,
        ],
    );
}

#[test]
fn calls_through_the_implemented_interface_keep_whole_tuple_correlations() {
    let parsed = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {}\n",
        "interface Contract { run(...args: [number] | [string, boolean]): void; }\n",
        "class Model implements Contract { run(value: number): void {} }\n",
        "type NumberArgs = [number]; type TextArgs = [string, boolean];\n",
        "type CrossedArgs = [number, boolean]; type ShortArgs = [string];\n",
        "declare const api: Contract;\n",
        "declare const numeric: number; declare const text: string; declare const flag: boolean;\n",
        "api.run(numeric); api.run(text, flag);\n",
        "api.run(numeric, flag); api.run(text);\n",
    ));
    let file = FileId::new(5_224);
    let mut context = context(&parsed, file);
    let class = declaration(&parsed, file, "Model").0;
    let contract = declaration(&parsed, file, "Contract").0;
    let method = methods(&parsed, contract)[0].0;
    let owner = symbol(&context, class);
    let contract_symbol = symbol(&context, contract);
    let method_symbol = symbol(&context, method);
    let aliases = ["NumberArgs", "TextArgs", "CrossedArgs", "ShortArgs"]
        .map(|name| symbol(&context, declaration(&parsed, file, name).0));
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            matches!(record.data, NodeData::CallExpression(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    assert_eq!(calls.len(), 4);

    context.check_source_file(file).unwrap();
    let signature = call_signatures(&context, method_symbol)[0];
    let rest = assert_rest_signature(&context, &parsed, method, signature);
    for (alias, accepted) in aliases.into_iter().zip([true, true, false, false]) {
        let arguments = context.get_declared_type_of_symbol(alias).unwrap();
        assert_eq!(context.is_type_assignable_to(arguments, rest), Ok(accepted));
    }
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    for (diagnostic, (call, source_type)) in diagnostics
        .iter()
        .zip([(calls[2], "[number, boolean]"), (calls[3], "[string]")])
    {
        let NodeData::CallExpression(expression) = &parsed.arena.get(call.node).unwrap().data
        else {
            panic!("expected a source call")
        };
        let arguments = &expression.arguments.nodes;
        let first = NodeRef::new(call.arena, call.file, arguments[0]);
        let expected_node = if arguments.len() == 1 { first } else { call };
        assert_eq!(diagnostic.node, Some(expected_node));
        let range = (arguments.len() > 1).then(|| {
            CanonicalCheckerDiagnosticRange::new(
                call,
                TextRange::new(
                    parsed.arena.get(arguments[0]).unwrap().range.start,
                    parsed
                        .arena
                        .get(*arguments.last().unwrap())
                        .unwrap()
                        .range
                        .end,
                ),
            )
        });
        assert_eq!(diagnostic.range_override, range);
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(
            diagnostic.diagnostic.arguments,
            [source_type, "[number] | [string, boolean]"]
        );
        assert!(diagnostic.related_information.is_empty());
        // The tuple constituent detail chain is not implemented yet.
    }
    let void = context.store().intrinsic_bootstrap().unwrap().void_type;
    for call in &calls {
        assert_eq!(
            context
                .store()
                .type_node_links(*call)
                .unwrap()
                .resolved_type,
            Some(void)
        );
        assert_eq!(
            context
                .store()
                .signature_links(*call)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(signature)
        );
    }
    let mut type_symbols = vec![contract_symbol];
    type_symbols.extend(aliases);
    assert_replay(
        &mut context,
        file,
        &type_symbols,
        &[owner, contract_symbol, method_symbol],
        &calls,
    );
}
