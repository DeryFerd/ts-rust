use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalUnionPropertyError,
    ResolvedUnionProperty, TypeData, TypeId, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const DECLARED_SOURCE: &str = concat!(
    "type Left = { left: bigint; both: string };\n",
    "type Right = { right: symbol; readonly both?: bigint };\n",
    "type Both = Left | Right;\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/union-members.ts\""),
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
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn declaration_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
    interface: bool,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name = match &record.data {
                NodeData::TypeAliasDeclaration(declaration) if !interface => declaration.name,
                NodeData::InterfaceDeclaration(declaration) if interface => declaration.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn property(context: &CanonicalCheckerContext<'_>, object: TypeId, name: &str) -> SemanticSymbolId {
    let TypeData::Object(object) = context.store().type_payload(object).unwrap().data() else {
        panic!("expected a declared type literal")
    };
    object
        .structured
        .members
        .and_then(|members| context.store().symbol_table(members))
        .and_then(|members| members.get_source(name))
        .unwrap_or_else(|| panic!("missing property {name}"))
}

fn cached_property(
    context: &CanonicalCheckerContext<'_>,
    union: TypeId,
    name: &str,
) -> SemanticSymbolId {
    let TypeData::Union(union) = context.store().type_payload(union).unwrap().data() else {
        panic!("expected a union")
    };
    union
        .union
        .property_cache
        .and_then(|cache| context.store().symbol_table(cache))
        .and_then(|cache| cache.get_source(name))
        .unwrap_or_else(|| panic!("missing cached union property {name}"))
}

fn property_declaration(
    context: &CanonicalCheckerContext<'_>,
    property: SemanticSymbolId,
) -> NodeRef {
    let [declaration] = context
        .store()
        .symbol(property)
        .unwrap()
        .declarations()
        .unwrap_or_default()
    else {
        panic!("expected one property declaration")
    };
    *declaration
}

fn assert_synthetic_links(
    context: &CanonicalCheckerContext<'_>,
    property: SemanticSymbolId,
    type_: TypeId,
    union: TypeId,
) {
    assert_eq!(
        context.store().value_symbol_links(property),
        Some(&ValueSymbolLinks {
            resolved_type: Some(type_),
            containing_type: Some(union),
            ..ValueSymbolLinks::default()
        })
    );
}

fn assert_result(
    result: ResolvedUnionProperty,
    symbol: SemanticSymbolId,
    type_: TypeId,
    optional: bool,
    readonly: bool,
) {
    assert_eq!(result.symbol(), symbol);
    assert_eq!(result.type_id(), type_);
    assert_eq!(result.is_optional(), optional);
    assert_eq!(result.is_readonly(), readonly);
}

#[test]
#[allow(clippy::too_many_lines)] // One vertical proves partial/full provenance and cold/warm identity.
fn declared_left_right_both_properties_preserve_identity_provenance_and_warm_cache() {
    let parsed = parse_source_file(DECLARED_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);
    let left_symbol = declaration_symbol(&parsed, file, &context, "Left", false);
    let right_symbol = declaration_symbol(&parsed, file, &context, "Right", false);
    let both_symbol = declaration_symbol(&parsed, file, &context, "Both", false);

    let left = context.get_declared_type_of_symbol(left_symbol).unwrap();
    let right = context.get_declared_type_of_symbol(right_symbol).unwrap();
    let both = context.get_declared_type_of_symbol(both_symbol).unwrap();
    let left_only = property(&context, left, "left");
    let right_only = property(&context, right, "right");
    let left_both = property(&context, left, "both");
    let right_both = property(&context, right, "both");
    let source_symbols = [left_only, right_only, left_both, right_both]
        .map(|symbol| context.store().symbol(symbol).unwrap().clone());
    let source_links = [left_only, right_only, left_both, right_both]
        .map(|symbol| context.store().value_symbol_links(symbol).unwrap().clone());

    let both_record = context.store().type_payload(both).unwrap();
    let TypeData::Union(both_data) = both_record.data() else {
        panic!("Both must resolve to a union")
    };
    assert_eq!(both_data.union.types, vec![left, right]);
    assert_eq!(
        both_record
            .alias()
            .and_then(|alias| context.store().type_alias(alias))
            .and_then(|alias| alias.symbol()),
        Some(both_symbol)
    );

    let before = (
        context.store().type_len(),
        context.store().symbol_store().checker_created_symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );
    assert_eq!(context.get_union_property(both, "left"), Ok(None));
    let cached_left = cached_property(&context, both, "left");
    assert_eq!(context.get_union_property(both, "right"), Ok(None));
    let cached_right = cached_property(&context, both, "right");
    let both_property = context
        .get_union_property(both, "both")
        .unwrap()
        .expect("both is present in both constituents");
    let cached_both = cached_property(&context, both, "both");
    assert_ne!(cached_left, left_only);
    assert_ne!(cached_right, right_only);
    assert_ne!(cached_both, left_both);
    assert_ne!(cached_both, right_both);
    assert_eq!(both_property.symbol(), cached_both);

    let left_record = context.store().symbol(cached_left).unwrap();
    assert_eq!(
        left_record.flags(),
        SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
    );
    assert_eq!(
        left_record.check_flags(),
        CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC | CheckFlags::READ_PARTIAL
    );
    let left_declaration = property_declaration(&context, left_only);
    assert_eq!(left_record.declarations(), Some(&[left_declaration][..]));
    assert_eq!(left_record.value_declaration(), Some(left_declaration));
    assert_eq!(
        left_record.parent(),
        context.store().symbol(left_only).unwrap().parent()
    );
    let left_type = context
        .store()
        .value_symbol_links(left_only)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_synthetic_links(&context, cached_left, left_type, both);

    let right_record = context.store().symbol(cached_right).unwrap();
    assert_eq!(
        right_record.flags(),
        SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
    );
    assert_eq!(
        right_record.check_flags(),
        CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC | CheckFlags::READ_PARTIAL
    );
    let right_declaration = property_declaration(&context, right_only);
    assert_eq!(right_record.declarations(), Some(&[right_declaration][..]));
    assert_eq!(right_record.value_declaration(), Some(right_declaration));
    assert_eq!(
        right_record.parent(),
        context.store().symbol(right_only).unwrap().parent()
    );
    let right_type = context
        .store()
        .value_symbol_links(right_only)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_synthetic_links(&context, cached_right, right_type, both);

    let both_synthetic = context.store().symbol(cached_both).unwrap();
    assert_eq!(
        both_synthetic.flags(),
        SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT
    );
    assert_eq!(
        both_synthetic.check_flags(),
        CheckFlags::SYNTHETIC_PROPERTY
            | CheckFlags::CONTAINS_PUBLIC
            | CheckFlags::READONLY
            | CheckFlags::HAS_NON_UNIFORM_TYPE
    );
    let both_declarations = [
        property_declaration(&context, left_both),
        property_declaration(&context, right_both),
    ];
    assert_eq!(both_synthetic.declarations(), Some(&both_declarations[..]));
    assert!(both_synthetic.value_declaration().is_none());
    assert!(both_synthetic.parent().is_none());
    let mut expected_both_types = [left_both, right_both]
        .map(|property| {
            context
                .store()
                .value_symbol_links(property)
                .unwrap()
                .resolved_type
                .unwrap()
        })
        .to_vec();
    expected_both_types.sort_by_key(|type_| {
        (
            context.store().type_payload(*type_).unwrap().flags(),
            *type_,
        )
    });
    let expected_both_type = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .cached_union_type(&expected_both_types)
        .expect("the cold property query cached string | bigint");
    assert_result(both_property, cached_both, expected_both_type, true, true);
    assert_eq!(
        context.type_to_string(both_property.type_id()).unwrap(),
        "string | bigint"
    );
    let TypeData::Union(property_type) = context
        .store()
        .type_payload(both_property.type_id())
        .unwrap()
        .data()
    else {
        panic!("the shared property type must be a canonical union")
    };
    assert_eq!(property_type.union.types, expected_both_types);
    assert_synthetic_links(&context, cached_both, both_property.type_id(), both);

    for ((symbol, expected), expected_links) in [left_only, right_only, left_both, right_both]
        .into_iter()
        .zip(source_symbols)
        .zip(source_links)
    {
        assert_eq!(context.store().symbol(symbol), Some(&expected));
        assert_eq!(
            context.store().value_symbol_links(symbol),
            Some(&expected_links)
        );
    }
    let cold = (
        context.store().type_len(),
        context.store().symbol_store().checker_created_symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );
    assert_eq!(cold.0, before.0 + 1);
    assert_eq!(cold.1, before.1 + 3);
    assert_eq!(cold.2, before.2 + 1);
    let after_record = context.store().type_payload(both).unwrap();
    let TypeData::Union(after_data) = after_record.data() else {
        panic!("Both must remain a union")
    };
    assert_eq!(
        after_record
            .alias()
            .and_then(|alias| context.store().type_alias(alias))
            .and_then(|alias| alias.symbol()),
        Some(both_symbol)
    );
    assert!(
        after_data
            .union
            .property_cache_without_function_property_augment
            .is_none()
    );
    assert!(after_data.union.resolved_properties.is_none());

    assert_eq!(context.get_union_property(both, "left"), Ok(None));
    assert_eq!(context.get_union_property(both, "right"), Ok(None));
    assert_eq!(
        context.get_union_property(both, "both"),
        Ok(Some(both_property))
    );
    assert_eq!(cached_property(&context, both, "left"), cached_left);
    assert_eq!(cached_property(&context, both, "right"), cached_right);
    assert_eq!(cached_property(&context, both, "both"), cached_both);
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_store().checker_created_symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        ),
        cold
    );
}

#[test]
fn declared_interface_and_type_literal_interface_mixes_are_rejected_without_writes() {
    let parsed = parse_source_file(concat!(
        "interface InterfaceLeft { both: string }\n",
        "interface InterfaceRight { both: number }\n",
        "type Shape = { both: string };\n",
        "type Interfaces = InterfaceLeft | InterfaceRight;\n",
        "type Mixed = Shape | InterfaceLeft;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut context = context(&parsed, file);
    let interface_left_symbol = declaration_symbol(&parsed, file, &context, "InterfaceLeft", true);
    let interface_right_symbol =
        declaration_symbol(&parsed, file, &context, "InterfaceRight", true);
    let shape_symbol = declaration_symbol(&parsed, file, &context, "Shape", false);
    let interfaces_symbol = declaration_symbol(&parsed, file, &context, "Interfaces", false);
    let mixed_symbol = declaration_symbol(&parsed, file, &context, "Mixed", false);

    let interface_left = context
        .get_declared_type_of_symbol(interface_left_symbol)
        .unwrap();
    let interface_right = context
        .get_declared_type_of_symbol(interface_right_symbol)
        .unwrap();
    let _shape = context.get_declared_type_of_symbol(shape_symbol).unwrap();
    let interfaces = context
        .get_declared_type_of_symbol(interfaces_symbol)
        .unwrap();
    let mixed = context.get_declared_type_of_symbol(mixed_symbol).unwrap();
    let before = (
        context.store().type_len(),
        context.store().symbol_store().checker_created_symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );

    assert!(matches!(
        context.get_union_property(interfaces, "both"),
        Err(CanonicalUnionPropertyError::UnsupportedConstituent(type_))
            if type_ == interface_left || type_ == interface_right
    ));
    assert_eq!(
        context.get_union_property(mixed, "both"),
        Err(CanonicalUnionPropertyError::UnsupportedConstituent(
            interface_left
        ))
    );
    for union in [interfaces, mixed] {
        let TypeData::Union(data) = context.store().type_payload(union).unwrap().data() else {
            panic!("fixture alias must remain a union")
        };
        assert!(data.union.property_cache.is_none());
    }
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_store().checker_created_symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        ),
        before
    );
}
