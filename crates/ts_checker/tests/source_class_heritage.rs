use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, ClassError, ClassUnsupported, TypeData,
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "class Base {\n",
    "  base?: string;\n",
    "  static baseCount: number;\n",
    "}\n",
    "class Derived extends Base {\n",
    "  own!: number;\n",
    "  static derivedCount: string;\n",
    "}\n",
    "class Shape {\n",
    "  own!: number;\n",
    "  base?: string;\n",
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
                EscapedName::source("\"/project/class-heritage.ts\""),
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

fn names(context: &CanonicalCheckerContext<'_>, properties: &[SemanticSymbolId]) -> Vec<String> {
    properties
        .iter()
        .map(|property| {
            context
                .store()
                .symbol(*property)
                .unwrap()
                .name()
                .as_utf8()
                .unwrap()
                .to_owned()
        })
        .collect()
}

#[test]
fn direct_class_base_materializes_both_identities_and_own_first_surfaces() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = checker_context(&parsed, file);
    let base_symbol = class_symbol(&parsed, file, &context, "Base");
    let derived_symbol = class_symbol(&parsed, file, &context, "Derived");
    let derived_exports = context
        .store()
        .symbol(derived_symbol)
        .unwrap()
        .exports()
        .unwrap();
    let counts = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );

    let derived = context
        .get_nongeneric_class_members(derived_symbol)
        .unwrap();

    assert_eq!(context.store().type_len(), counts.0 + 6);
    assert_eq!(context.store().signature_len(), counts.1 + 2);
    assert_eq!(context.store().symbol_len(), counts.2);
    assert_eq!(
        context.store().symbol_store().symbol_table_len(),
        counts.3 + 3
    );
    let base_identities = derived.base().expect("Derived retains its direct base");
    assert_eq!(base_identities.symbol(), base_symbol);
    assert_eq!(
        names(&context, derived.declared_instance_properties()),
        ["own"]
    );
    assert_eq!(
        names(&context, derived.instance_properties()),
        ["own", "base"]
    );
    assert_eq!(
        names(&context, derived.declared_static_properties()),
        ["derivedCount"]
    );
    assert_eq!(
        names(&context, derived.static_properties()),
        ["derivedCount", "baseCount"]
    );
    assert_ne!(derived.static_members(), derived_exports);

    let instance_table = context
        .store()
        .symbol_table(derived.instance_members().unwrap())
        .unwrap();
    assert_eq!(instance_table.len(), 2);
    assert!(instance_table.get_source("own").is_some());
    assert!(instance_table.get_source("base").is_some());
    assert!(instance_table.get_source("baseCount").is_none());
    let static_table = context
        .store()
        .symbol_table(derived.static_members())
        .unwrap();
    assert_eq!(static_table.len(), 3);
    assert!(static_table.get_source("derivedCount").is_some());
    assert!(static_table.get_source("baseCount").is_some());
    assert_eq!(
        static_table.get_source("prototype"),
        Some(derived.prototype())
    );
    assert!(static_table.get_source("base").is_none());

    let TypeData::Interface(instance) = context
        .store()
        .type_payload(derived.shells().instance_type())
        .unwrap()
        .data()
    else {
        panic!("derived instance uses interface storage")
    };
    assert_eq!(
        instance.resolved_base_constructor_type,
        Some(base_identities.value_type())
    );
    assert_eq!(
        instance.resolved_base_types.as_deref(),
        Some(&[base_identities.instance_type()][..])
    );
    assert!(instance.base_types_resolved);
    assert_eq!(
        context
            .store()
            .type_payload(derived.shells().instance_type())
            .unwrap()
            .object_flags(),
        ObjectFlags::CLASS | ObjectFlags::REFERENCE | ObjectFlags::MEMBERS_RESOLVED
    );
    let value = context
        .store()
        .type_payload(derived.shells().value_type())
        .unwrap();
    assert_eq!(value.flags(), TypeFlags::OBJECT);
    assert_eq!(
        value.object_flags(),
        ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
    );

    let base = context.get_nongeneric_class_members(base_symbol).unwrap();
    assert_eq!(base.base(), None);
    assert_eq!(
        base.shells().instance_type(),
        base_identities.instance_type()
    );
    assert_eq!(base.shells().value_type(), base_identities.value_type());
    assert_ne!(
        derived.default_construct_signature(),
        base.default_construct_signature()
    );
    assert_eq!(
        context
            .store()
            .signature(derived.default_construct_signature())
            .unwrap()
            .resolved_return_type(),
        Some(derived.shells().instance_type())
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );
    assert_eq!(
        context
            .get_nongeneric_class_members(derived_symbol)
            .unwrap(),
        derived
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        ),
        warm
    );
}

#[test]
fn validated_class_graphs_participate_in_property_shape_relations() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut context = checker_context(&parsed, file);
    let base_symbol = class_symbol(&parsed, file, &context, "Base");
    let derived_symbol = class_symbol(&parsed, file, &context, "Derived");
    let shape_symbol = class_symbol(&parsed, file, &context, "Shape");
    let derived = context
        .get_nongeneric_class_members(derived_symbol)
        .unwrap();
    let base = context.get_nongeneric_class_members(base_symbol).unwrap();
    let shape = context.get_nongeneric_class_members(shape_symbol).unwrap();

    assert_eq!(
        context.is_type_assignable_to(
            derived.shells().instance_type(),
            base.shells().instance_type(),
        ),
        Ok(true)
    );
    assert_eq!(
        context.is_type_assignable_to(
            base.shells().instance_type(),
            derived.shells().instance_type(),
        ),
        Ok(false)
    );
    assert_eq!(
        context.is_type_assignable_to(
            derived.shells().instance_type(),
            shape.shells().instance_type(),
        ),
        Ok(true)
    );
    assert_eq!(
        context.is_type_assignable_to(
            shape.shells().instance_type(),
            derived.shells().instance_type(),
        ),
        Ok(true)
    );
}

#[test]
fn shadowed_base_names_still_use_distinct_resolved_tables() {
    let parsed = parse_source_file(concat!(
        "class Base { same: string; static shared: number; }\n",
        "class Derived extends Base { same: number; static shared: string; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let mut context = checker_context(&parsed, file);
    let derived_symbol = class_symbol(&parsed, file, &context, "Derived");
    let derived_record = context.store().symbol(derived_symbol).unwrap();
    let declared_instance_members = derived_record.members().unwrap();
    let declared_static_members = derived_record.exports().unwrap();

    let members = context
        .get_nongeneric_class_members(derived_symbol)
        .unwrap();

    assert_eq!(
        names(&context, members.declared_instance_properties()),
        ["same"]
    );
    assert_eq!(names(&context, members.instance_properties()), ["same"]);
    assert_eq!(
        members.instance_properties(),
        members.declared_instance_properties()
    );
    assert_ne!(
        members.instance_members(),
        Some(declared_instance_members),
        "maps.Clone must retain a distinct nonempty resolved instance table"
    );
    assert_eq!(
        names(&context, members.declared_static_properties()),
        ["shared"]
    );
    assert_eq!(names(&context, members.static_properties()), ["shared"]);
    assert_eq!(
        members.static_properties(),
        members.declared_static_properties()
    );
    assert_ne!(
        members.static_members(),
        declared_static_members,
        "the resolved static table always clones the prototype-bearing exports"
    );
}

#[test]
fn unsupported_later_derived_annotation_rejects_before_base_or_derived_publication() {
    let parsed = parse_source_file(concat!(
        "class Base { base: string; }\n",
        "class Derived extends Base { first: string; second: Missing; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let mut context = checker_context(&parsed, file);
    let base_symbol = class_symbol(&parsed, file, &context, "Base");
    let derived_symbol = class_symbol(&parsed, file, &context, "Derived");
    let base_property = context
        .store()
        .symbol(base_symbol)
        .and_then(|symbol| symbol.members())
        .and_then(|members| context.store().symbol_table(members))
        .and_then(|members| members.get_source("base"))
        .expect("Base retains its declared property");
    let derived_first = context
        .store()
        .symbol(derived_symbol)
        .and_then(|symbol| symbol.members())
        .and_then(|members| context.store().symbol_table(members))
        .and_then(|members| members.get_source("first"))
        .expect("Derived retains its first declared property");
    let before = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );

    assert!(matches!(
        context.get_nongeneric_class_members(derived_symbol),
        Err(ClassError::Unsupported(ClassUnsupported::PropertyType {
            kind: SyntaxKind::TypeReference,
            ..
        }))
    ));
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        ),
        before
    );
    for symbol in [base_symbol, derived_symbol] {
        assert!(
            context
                .store()
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .is_none()
        );
        assert!(
            context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .is_none()
        );
    }
    for property in [base_property, derived_first] {
        assert!(
            context
                .store()
                .value_symbol_links(property)
                .and_then(|links| links.resolved_type)
                .is_none()
        );
    }
}

#[test]
fn implements_only_heritage_stays_a_typed_unsupported_boundary() {
    let parsed = parse_source_file(concat!(
        "interface Shape { value: string; }\n",
        "class Model implements Shape { value: string; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4);
    let mut context = checker_context(&parsed, file);
    let model = class_symbol(&parsed, file, &context, "Model");
    let before = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );

    assert!(matches!(
        context.get_nongeneric_class_members(model),
        Err(ClassError::Unsupported(ClassUnsupported::Heritage(_)))
    ));
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        ),
        before
    );
    assert!(
        context
            .store()
            .declared_type_links(model)
            .and_then(|links| links.declared_type)
            .is_none()
    );
    assert!(
        context
            .store()
            .value_symbol_links(model)
            .and_then(|links| links.resolved_type)
            .is_none()
    );
}
