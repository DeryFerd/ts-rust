use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, TypeId};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "interface ReadonlyBase { readonly id: number }\n",
    "interface MutableBase { id: number }\n",
    "interface ReadonlyDerived extends ReadonlyBase { readonly label: string }\n",
    "interface MutableDerived extends MutableBase { label: string }\n",
    "type ReadonlyShape = { readonly value: number };\n",
    "type MutableShape = { value: number };\n",
    "const inline: { readonly frozen: number; open: string } = ",
    "{ frozen: 1, open: \"x\" };\n",
);

fn checker_context<'arena>(
    parsed: &'arena ParseResult,
    file: FileId,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/readonly-properties.ts\""),
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
                NodeData::InterfaceDeclaration(declaration) if interface => declaration.name,
                NodeData::TypeAliasDeclaration(declaration) if !interface => declaration.name,
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

fn declared_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
        .or_else(|| {
            context
                .store()
                .type_alias_links(symbol)
                .and_then(|links| links.declared_type)
        })
        .unwrap_or_else(|| panic!("missing declared type for {symbol:?}"))
}

fn interface_own_property(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    name: &str,
) -> SemanticSymbolId {
    let TypeData::Interface(interface) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected an interface type")
    };
    let members = interface
        .declared_members
        .expect("interface declared members are resolved");
    context
        .store()
        .symbol_table(members)
        .and_then(|table| table.get_source(name))
        .unwrap_or_else(|| panic!("missing own interface property {name}"))
}

fn structured_property(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    name: &str,
) -> SemanticSymbolId {
    let properties = match context.store().type_payload(type_).unwrap().data() {
        TypeData::Interface(interface) => {
            interface.reference.object.structured.properties.as_deref()
        }
        TypeData::Object(object) => object.structured.properties.as_deref(),
        data => panic!("expected a structured source type, got {data:?}"),
    }
    .expect("structured properties are resolved");
    properties
        .iter()
        .copied()
        .find(|property| {
            context
                .store()
                .symbol(*property)
                .is_some_and(|symbol| symbol.name().as_utf8() == Some(name))
        })
        .unwrap_or_else(|| panic!("missing structured property {name}"))
}

fn variable_annotation(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                NodeRef::new(
                    parsed.arena.id(),
                    file,
                    variable.type_.expect("variable has an annotation"),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn assert_readonly(
    context: &CanonicalCheckerContext<'_>,
    property: SemanticSymbolId,
    readonly: bool,
) {
    let expected = if readonly {
        CheckFlags::READONLY
    } else {
        CheckFlags::NONE
    };
    assert_eq!(
        context.store().symbol(property).unwrap().check_flags(),
        expected
    );
}

#[test]
#[allow(clippy::too_many_lines)] // One source proves retention, inheritance, display, and relations.
fn source_readonly_properties_survive_publication_inheritance_and_warm_rechecks() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = checker_context(&parsed, file);

    let readonly_base = declaration_symbol(&parsed, file, &context, "ReadonlyBase", true);
    let mutable_base = declaration_symbol(&parsed, file, &context, "MutableBase", true);
    let readonly_derived = declaration_symbol(&parsed, file, &context, "ReadonlyDerived", true);
    let mutable_derived = declaration_symbol(&parsed, file, &context, "MutableDerived", true);
    let readonly_shape = declaration_symbol(&parsed, file, &context, "ReadonlyShape", false);
    let mutable_shape = declaration_symbol(&parsed, file, &context, "MutableShape", false);
    let inline_annotation = variable_annotation(&parsed, file, "inline");

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());

    let readonly_base_type = declared_type(&context, readonly_base);
    let mutable_base_type = declared_type(&context, mutable_base);
    let readonly_derived_type = declared_type(&context, readonly_derived);
    let mutable_derived_type = declared_type(&context, mutable_derived);
    let readonly_shape_type = declared_type(&context, readonly_shape);
    let mutable_shape_type = declared_type(&context, mutable_shape);
    let inline_type = context
        .store()
        .type_node_links(inline_annotation)
        .and_then(|links| links.resolved_type)
        .expect("the variable annotation is resolved");

    let readonly_id = interface_own_property(&context, readonly_base_type, "id");
    let mutable_id = interface_own_property(&context, mutable_base_type, "id");
    let readonly_label = interface_own_property(&context, readonly_derived_type, "label");
    let mutable_label = interface_own_property(&context, mutable_derived_type, "label");
    assert_readonly(&context, readonly_id, true);
    assert_readonly(&context, mutable_id, false);
    assert_readonly(&context, readonly_label, true);
    assert_readonly(&context, mutable_label, false);

    let inherited_readonly_id = structured_property(&context, readonly_derived_type, "id");
    let inherited_mutable_id = structured_property(&context, mutable_derived_type, "id");
    assert_eq!(
        inherited_readonly_id, readonly_id,
        "direct heritage preserves the readonly base property symbol"
    );
    assert_eq!(
        inherited_mutable_id, mutable_id,
        "direct heritage preserves the mutable base property symbol"
    );
    assert_readonly(&context, inherited_readonly_id, true);
    assert_readonly(&context, inherited_mutable_id, false);
    assert_eq!(
        context.type_to_string(readonly_derived_type).unwrap(),
        "ReadonlyDerived",
        "named-interface formatting validates the inherited readonly property chain"
    );

    assert_readonly(
        &context,
        structured_property(&context, readonly_shape_type, "value"),
        true,
    );
    assert_readonly(
        &context,
        structured_property(&context, mutable_shape_type, "value"),
        false,
    );
    assert_readonly(
        &context,
        structured_property(&context, inline_type, "frozen"),
        true,
    );
    assert_readonly(
        &context,
        structured_property(&context, inline_type, "open"),
        false,
    );
    assert_eq!(
        context.type_to_string(inline_type).unwrap(),
        "{ readonly frozen: number; open: string; }"
    );

    for (source, target) in [
        (readonly_shape_type, mutable_shape_type),
        (mutable_shape_type, readonly_shape_type),
        (readonly_derived_type, mutable_derived_type),
        (mutable_derived_type, readonly_derived_type),
    ] {
        assert_eq!(context.is_type_assignable_to(source, target), Ok(true));
    }

    let warm_state = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        context.store().index_info_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
        context.diagnostics().clone(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().index_info_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            context.diagnostics().clone(),
        ),
        warm_state
    );
}
