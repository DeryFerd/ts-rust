use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, TypeId, types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_624);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/conditional-callable-interfaces.ts\""),
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
        [(FILE, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn declaration(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name = match &record.data {
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::TypeAliasDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn annotation(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a variable declaration")
    };
    NodeRef::new(parsed.arena.id(), FILE, variable.type_.unwrap())
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 6] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.conditional_root_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn assert_cold(context: &CanonicalCheckerContext<'_>, type_: TypeId) {
    let record = context.store().type_payload(type_).unwrap();
    assert!(
        !record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
    );
    let structured = record.data().structured().unwrap();
    assert!(structured.members.is_none());
    assert!(structured.properties.is_none());
    assert!(structured.signatures.is_none());
    assert_eq!(structured.call_signature_count, 0);
}

#[test]
#[allow(clippy::too_many_lines)] // Check the cold alias, copied Array call, diagnostic, and replay together.
fn conditional_validator_inference_keeps_array_calls_and_cold_and_warm_identity() {
    let parsed = parse_source_file(concat!(
        "interface Array<T> {}\n",
        "interface ReadonlyArray<T> {}\n",
        "interface Validator<T> { (value: T[]): T[]; }\n",
        "type Validated<V> = V extends Validator<infer T> ? T : never;\n",
        "declare const cold: Validator<string>;\n",
        "declare const warm: Validator<number>;\n",
        "declare const numbers: number[];\n",
        "warm(numbers);\n",
        "type Cold = Validated<Validator<string>>;\n",
        "type Warm = Validated<Validator<number>>;\n",
        "const accepted: Cold = 'text';\n",
        "const rejected: Warm = 'wrong';\n",
    ));
    let mut context = context(&parsed);
    let cold_node = annotation(&parsed, declaration(&parsed, "cold"));
    let warm_node = annotation(&parsed, declaration(&parsed, "warm"));
    let numbers_node = annotation(&parsed, declaration(&parsed, "numbers"));
    let cold_alias = symbol(&context, declaration(&parsed, "Cold"));
    let warm_alias = symbol(&context, declaration(&parsed, "Warm"));
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;

    let cold = context.get_type_from_type_node(cold_node).unwrap();
    assert_cold(&context, cold);
    assert_eq!(context.get_declared_type_of_symbol(cold_alias), Ok(string));
    assert_cold(&context, cold);

    context.check_source_file(FILE).unwrap();
    let warm = context.get_type_from_type_node(warm_node).unwrap();
    assert_ne!(warm, cold);
    assert_cold(&context, cold);
    assert_eq!(context.get_declared_type_of_symbol(warm_alias), Ok(number));
    let numbers = context.get_type_from_type_node(numbers_node).unwrap();
    let TypeData::TypeReference(array) = context.store().type_payload(numbers).unwrap().data()
    else {
        panic!("the real call parameter must retain its Array reference")
    };
    assert_eq!(array.object.target, Some(context.global_types().array_type));
    assert_eq!(
        array.resolved_type_arguments.as_deref(),
        Some(&[number][..])
    );

    let call = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                FILE,
                node,
            ))
        })
        .unwrap();
    let selected = context
        .store()
        .signature_links(call)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let signature = context.store().signature(selected).unwrap();
    assert!(signature.target().is_some());
    assert!(signature.mapper().is_some());
    assert_eq!(signature.resolved_return_type(), Some(numbers));
    let [parameter] = signature.parameters() else {
        panic!("the copied call signature must retain one parameter")
    };
    let parameter = context.store().value_symbol_links(*parameter).unwrap();
    assert_eq!(parameter.resolved_type, Some(numbers));
    assert_eq!(parameter.mapper, signature.mapper());
    assert!(parameter.target.is_some());
    assert_eq!(
        context
            .store()
            .type_payload(warm)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_deref(),
        Some(&[selected][..]),
    );

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the wrong assignment must retain one diagnostic")
    };
    let rejected = declaration(&parsed, "rejected");
    let NodeData::VariableDeclaration(rejected) = &parsed.arena.get(rejected.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.node,
        Some(NodeRef::new(parsed.arena.id(), FILE, rejected.name))
    );
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );

    let before = (counts(&context), context.diagnostics().clone());
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(context.get_declared_type_of_symbol(cold_alias), Ok(string));
        assert_eq!(context.get_declared_type_of_symbol(warm_alias), Ok(number));
        assert_eq!(context.get_type_from_type_node(cold_node), Ok(cold));
        assert_eq!(context.get_type_from_type_node(warm_node), Ok(warm));
        assert_eq!(context.get_type_at_location(call), Ok(numbers));
        assert_eq!(context.get_return_type_of_signature(selected), Ok(numbers));
        assert_cold(&context, cold);
        assert_eq!((counts(&context), context.diagnostics().clone()), before);
    }
}
