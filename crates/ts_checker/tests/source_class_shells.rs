use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, ValueSymbolLinks,
    type_records::{ObjectTypeData, TypeCacheState},
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "class Model {\n",
    "  readonly value?: string;\n",
    "  definite!: number;\n",
    "  static readonly count: number;\n",
    "}\n",
);

fn checker_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-shells.ts\""),
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
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn class_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let name = class.name.and_then(|name| parsed.arena.get(name))?;
            let NodeData::Identifier(name) = &name.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing class {expected}"))
}

fn class_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = class_declaration(parsed, file, expected);
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

#[test]
fn public_class_shell_query_installs_exact_instance_and_static_identities() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = checker_context(&parsed, file);
    let declaration = class_declaration(&parsed, file, "Model");
    let symbol = class_symbol(&parsed, file, &context, "Model");
    let type_count = context.store().type_len();

    let shells = context.get_nongeneric_class_shells(symbol).unwrap();

    assert_eq!(context.store().type_len(), type_count + 3);
    assert_eq!(shells.declaration(), declaration);
    assert_eq!(shells.symbol(), symbol);
    assert_ne!(shells.instance_type(), shells.value_type());
    assert_eq!(
        context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type),
        Some(shells.instance_type())
    );
    assert_eq!(
        context.store().value_symbol_links(symbol),
        Some(&ValueSymbolLinks {
            resolved_type: Some(shells.value_type()),
            ..ValueSymbolLinks::default()
        })
    );

    let instance_record = context
        .store()
        .type_payload(shells.instance_type())
        .unwrap();
    assert_eq!(instance_record.flags(), TypeFlags::OBJECT);
    assert_eq!(
        instance_record.object_flags(),
        ObjectFlags::CLASS | ObjectFlags::REFERENCE
    );
    assert_eq!(instance_record.symbol(), Some(symbol));
    let TypeData::Interface(instance) = instance_record.data() else {
        panic!("class instance must use interface storage")
    };
    assert_eq!(
        instance.resolved_base_constructor_type,
        Some(
            context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .undefined_type
        )
    );
    assert!(!instance.base_types_resolved);
    assert_eq!(instance.resolved_base_types, None);
    assert_eq!(
        instance.reference.object.target,
        Some(shells.instance_type())
    );
    assert_eq!(instance.reference.resolved_type_arguments, Some(Vec::new()));
    let parameters = instance
        .all_type_parameters
        .as_deref()
        .expect("the class owns its synthetic this type");
    assert_eq!(parameters.len(), 1);
    assert_eq!(instance.this_type, Some(parameters[0]));
    let TypeCacheState::Allocated(instantiations) = &instance.reference.object.instantiations
    else {
        panic!("the class origin owns its self-instantiation cache")
    };
    assert_eq!(instantiations.len(), 1);

    let value_record = context.store().type_payload(shells.value_type()).unwrap();
    assert_eq!(value_record.flags(), TypeFlags::OBJECT);
    assert_eq!(value_record.object_flags(), ObjectFlags::ANONYMOUS);
    assert_eq!(value_record.symbol(), Some(symbol));
    assert!(matches!(
        value_record.data(),
        TypeData::Object(object) if object == &ObjectTypeData::default()
    ));

    let warm_counts = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );
    assert_eq!(context.get_nongeneric_class_shells(symbol).unwrap(), shells);
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        ),
        warm_counts
    );
    assert!(context.diagnostics().is_empty());
}
