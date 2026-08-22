use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData,
    ValueSymbolLinks,
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
    checker_context_with_options(parsed, file, CanonicalCheckerOptions::default())
}

fn checker_context_with_options(
    parsed: &ParseResult,
    file: FileId,
    options: CanonicalCheckerOptions,
) -> CanonicalCheckerContext<'_> {
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
        options,
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

#[test]
fn explicit_public_field_modifiers_preserve_instance_static_and_readonly_state() {
    let parsed = parse_source_file(concat!(
        "class Model {\n",
        "  public value!: string;\n",
        "  public readonly label?: string;\n",
        "  public static count: number;\n",
        "  public static readonly total: number;\n",
        "}\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut context = checker_context(&parsed, file);
    let symbol = class_symbol(&parsed, file, &context, "Model");

    context.check_source_file(file).unwrap();
    let members = context.get_nongeneric_class_members(symbol).unwrap();
    let instance_names = members
        .instance_properties()
        .iter()
        .map(|property| {
            context
                .store()
                .symbol(*property)
                .unwrap()
                .name()
                .as_utf8()
                .unwrap()
        })
        .collect::<Vec<_>>();
    let static_names = members
        .static_properties()
        .iter()
        .map(|property| {
            context
                .store()
                .symbol(*property)
                .unwrap()
                .name()
                .as_utf8()
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(instance_names, ["value", "label"]);
    assert_eq!(static_names, ["count", "total"]);
    assert_eq!(
        context
            .store()
            .symbol(members.instance_properties()[0])
            .unwrap()
            .check_flags(),
        CheckFlags::NONE
    );
    assert_eq!(
        context
            .store()
            .symbol(members.instance_properties()[1])
            .unwrap()
            .check_flags(),
        CheckFlags::READONLY
    );
    assert_eq!(
        context
            .store()
            .symbol(members.static_properties()[1])
            .unwrap()
            .check_flags(),
        CheckFlags::READONLY
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        ),
        warm
    );
    assert!(context.diagnostics().is_empty());
}

#[test]
fn strict_property_initialization_exempts_any_unknown_and_undefined_fields() {
    let parsed = parse_source_file(concat!(
        "class Safe {\n",
        "  anyValue: any;\n",
        "  unknownValue: unknown;\n",
        "  undefinedValue: undefined;\n",
        "  optional?: string;\n",
        "  definite!: number;\n",
        "}\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let mut context = checker_context_with_options(
        &parsed,
        file,
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_property_initialization: true,
            ..CanonicalCheckerOptions::default()
        },
    );
    let symbol = class_symbol(&parsed, file, &context, "Safe");

    context.check_source_file(file).unwrap();

    let members = context.get_nongeneric_class_members(symbol).unwrap();
    assert_eq!(members.instance_properties().len(), 5);
    assert!(context.diagnostics().is_empty());

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        ),
        warm
    );
    assert!(context.diagnostics().is_empty());
}

#[test]
fn strict_property_initialization_reports_required_fields_in_declaration_order() {
    let parsed = parse_source_file(concat!(
        "class Mixed {\n",
        "  safeAny: any;\n",
        "  requiredString: string;\n",
        "  safeUnknown: unknown;\n",
        "  requiredVoid: void;\n",
        "  safeUndefined: undefined;\n",
        "  optional?: boolean;\n",
        "  definite!: string;\n",
        "  readonly requiredNumber: number;\n",
        "  static ignored: string;\n",
        "}\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let mut context = checker_context_with_options(
        &parsed,
        file,
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_property_initialization: true,
            ..CanonicalCheckerOptions::default()
        },
    );
    let symbol = class_symbol(&parsed, file, &context, "Mixed");

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 3);
    for (diagnostic, expected) in
        diagnostics
            .iter()
            .zip(["requiredString", "requiredVoid", "requiredNumber"])
    {
        assert_eq!(diagnostic.diagnostic.code(), 2564);
        assert_eq!(diagnostic.diagnostic.arguments, [expected]);
        let name = diagnostic.node.expect("TS2564 anchors the field name");
        let NodeData::Identifier(identifier) =
            &parsed.arena.get(name.node).expect("field name exists").data
        else {
            panic!("TS2564 must anchor an identifier")
        };
        assert_eq!(identifier.text, expected);
        assert_eq!(diagnostic.range_override, None);
    }
    let members = context.get_nongeneric_class_members(symbol).unwrap();
    assert_eq!(members.instance_properties().len(), 8);
    assert_eq!(members.static_properties().len(), 1);

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.diagnostics().as_slice().to_vec(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.diagnostics().as_slice().to_vec(),
        ),
        warm
    );
}
