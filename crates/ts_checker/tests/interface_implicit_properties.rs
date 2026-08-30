use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, SourceSyntaxRole, TypeData,
    TypeId, UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(148_260);
const SOURCE: &str = concat!(
    "interface Loose {\n",
    "    value;\n",
    "    typed: string;\n",
    "}\n",
    "declare const loose: Loose;\n",
    "const implicit: number = loose.value;\n",
    "const explicit: string = loose.typed;\n",
);

fn context(parsed: &ParseResult, no_implicit_any: bool) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/interface-implicit-properties.ts\""),
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
            no_implicit_any,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn named_declaration(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name = match &record.data {
                NodeData::InterfaceDeclaration(interface) => interface.name,
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::PropertySignatureDeclaration(property) => property.name,
                NodeData::VariableDeclaration(variable) => variable.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some((
                NodeRef::new(parsed.arena.id(), FILE, node),
                NodeRef::new(parsed.arena.id(), FILE, name),
            ))
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"))
}

fn symbol(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> SemanticSymbolId {
    let declaration = named_declaration(parsed, name).0;
    context
        .store()
        .get_merged_symbol(context.file(FILE).unwrap().1.symbol(declaration).unwrap())
        .unwrap()
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn allocations(context: &CanonicalCheckerContext<'_>) -> ([usize; 7], Vec<usize>) {
    let store = context.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        store.checker_link_allocated_lengths().to_vec(),
    )
}

fn assert_properties(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult, type_: TypeId) {
    let owner = symbol(context, parsed, "Loose");
    let implicit = symbol(context, parsed, "value");
    let typed = symbol(context, parsed, "typed");
    let store = context.store();
    let TypeData::Interface(interface) = store.type_payload(type_).unwrap().data() else {
        panic!("Loose must retain its declared interface type");
    };
    assert_eq!(store.type_payload(type_).unwrap().symbol(), Some(owner));
    assert!(interface.declared_members_resolved);
    assert_eq!(
        interface.declared_members,
        store.symbol(owner).unwrap().members()
    );
    assert_eq!(
        interface.reference.object.structured.properties.as_deref(),
        Some([implicit, typed].as_slice()),
    );
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    assert_eq!(value_type(context, implicit), bootstrap.any_type);
    assert_eq!(value_type(context, typed), bootstrap.string_type);
    assert!(
        store
            .type_node_links(named_declaration(parsed, "value").1)
            .is_none()
    );
}

#[test]
fn ordinary_interface_implicit_properties_preserve_cold_and_warm_types() {
    let parsed = parse_source_file(SOURCE);
    let mut context = context(&parsed, false);
    let owner = symbol(&context, &parsed, "Loose");
    assert!(context.store().declared_type_links(owner).is_none());
    let type_ = context.get_declared_type_of_symbol(owner).unwrap();
    assert_properties(&context, &parsed, type_);
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        value_type(&context, symbol(&context, &parsed, "implicit")),
        bootstrap.number_type,
    );
    assert_eq!(
        value_type(&context, symbol(&context, &parsed, "explicit")),
        bootstrap.string_type,
    );

    let warm = allocations(&context);
    for _ in 0..3 {
        assert_eq!(context.get_declared_type_of_symbol(owner), Ok(type_));
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        assert_properties(&context, &parsed, type_);
        assert_eq!(allocations(&context), warm);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn ordinary_interface_implicit_properties_report_exact_ts7008_once() {
    let parsed = parse_source_file(SOURCE);
    let mut context = context(&parsed, true);
    let owner = symbol(&context, &parsed, "Loose");
    assert!(context.store().declared_type_links(owner).is_none());
    let type_ = context.get_declared_type_of_symbol(owner).unwrap();
    context.check_source_file(FILE).unwrap();
    assert_properties(&context, &parsed, type_);
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("only the unannotated property must report TS7008");
    };
    let name = named_declaration(&parsed, "value").1;
    assert_eq!(diagnostic.node, Some(name));
    let range = parsed.arena.get(name.node).unwrap().range;
    let start = u32::try_from(SOURCE.find("value;").unwrap()).unwrap();
    assert_eq!((range.start.get(), range.end.get()), (start, start + 5));
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(diagnostic.diagnostic.code(), 7008);
    assert_eq!(diagnostic.diagnostic.arguments, ["value", "any"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Member 'value' implicitly has an 'any' type.",
    );
    let expected = context.diagnostics().as_slice().to_vec();
    let warm = allocations(&context);
    for _ in 0..3 {
        assert_eq!(context.get_declared_type_of_symbol(owner), Ok(type_));
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        assert_properties(&context, &parsed, type_);
        assert_eq!(context.diagnostics().as_slice(), expected.as_slice());
        assert_eq!(allocations(&context), warm);
    }
}

#[test]
fn ordinary_interface_implicit_properties_do_not_admit_generic_owners() {
    let parsed = parse_source_file("interface Generic<T> { value; }");
    let mut context = context(&parsed, false);
    assert_eq!(
        context.check_source_file(FILE),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Syntax {
                node: named_declaration(&parsed, "Generic").0,
                kind: SyntaxKind::InterfaceDeclaration,
                role: SourceSyntaxRole::InterfaceDeclaration,
            }
        )),
    );
    assert!(context.diagnostics().is_empty());
}
