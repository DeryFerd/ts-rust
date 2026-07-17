use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    TypeData, TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
    signatures::SignatureFlags,
    type_records::TypeCacheState,
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
    checker_context_with_module_state(parsed, file, CanonicalModuleState::Script)
}

fn checker_context_with_module_state(
    parsed: &ParseResult,
    file: FileId,
    module_state: CanonicalModuleState,
) -> CanonicalCheckerContext<'_> {
    checker_context_with_options(
        parsed,
        file,
        module_state,
        CanonicalCheckerOptions::default(),
    )
}

fn checker_context_with_options(
    parsed: &ParseResult,
    file: FileId,
    module_state: CanonicalModuleState,
    options: CanonicalCheckerOptions,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-members.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                module_state,
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

fn strict_property_options() -> CanonicalCheckerOptions {
    CanonicalCheckerOptions {
        intrinsic: IntrinsicBootstrapOptions {
            strict_null_checks: true,
            ..IntrinsicBootstrapOptions::default()
        },
        strict_property_initialization: true,
        ..CanonicalCheckerOptions::default()
    }
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

fn variable_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn type_alias_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing type alias {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn property_type_node(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_node, record)| {
            let NodeData::PropertyDeclaration(property) = &record.data else {
                return None;
            };
            let name = parsed.arena.get(property.name)?;
            let NodeData::Identifier(name) = &name.data else {
                return None;
            };
            (name.text == expected).then(|| {
                NodeRef::new(
                    parsed.arena.id(),
                    file,
                    property.type_.expect("fixture properties are annotated"),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing property {expected}"))
}

fn is_type_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

#[test]
fn source_check_materializes_class_members_and_accepts_unmarked_static_fields() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = checker_context(&parsed, file);
    let symbol = class_symbol(&parsed, file, &context, "Model");

    context.check_source_file(file).unwrap();

    let members = context.get_nongeneric_class_members(symbol).unwrap();
    assert_eq!(members.instance_properties().len(), 2);
    assert_eq!(members.static_properties().len(), 1);
    assert!(
        context
            .source_file(file)
            .and_then(|source| context.store().source_file_links(source))
            .is_some_and(|links| links.type_checked)
    );
    assert!(context.diagnostics().is_empty());

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
        context.diagnostics().len(),
        context
            .source_file(file)
            .and_then(|source| context.store().source_file_links(source))
            .is_some_and(|links| links.type_checked),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        context.get_nongeneric_class_members(symbol).unwrap(),
        members
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            context.diagnostics().len(),
            context
                .source_file(file)
                .and_then(|source| context.store().source_file_links(source))
                .is_some_and(|links| links.type_checked),
        ),
        warm
    );
}

#[test]
fn supported_classes_execute_at_their_lexical_statement_positions() {
    let parsed = parse_source_file(concat!(
        "class First { value?: string; }\n",
        "type Between = { marker: string };\n",
        "class Second { value!: number; static count: number; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = checker_context(&parsed, file);
    let first = class_symbol(&parsed, file, &context, "First");
    let between = type_alias_symbol(&parsed, file, &context, "Between");
    let second = class_symbol(&parsed, file, &context, "Second");

    context.check_source_file(file).unwrap();

    let first = context.get_nongeneric_class_members(first).unwrap();
    let between = context
        .store()
        .type_alias_links(between)
        .and_then(|links| links.declared_type)
        .expect("the intervening type alias must be materialized");
    let second = context.get_nongeneric_class_members(second).unwrap();
    assert!(first.shells().value_type().get() < between.get());
    assert!(between.get() < second.shells().instance_type().get());
    assert!(first.default_construct_signature().get() < second.default_construct_signature().get());
    assert!(context.diagnostics().is_empty());
}

#[test]
fn loose_options_admit_bare_instance_fields_and_replay_without_growth() {
    let parsed = parse_source_file(concat!(
        "class Loose {\n",
        "  bare: string;\n",
        "  optional?: number;\n",
        "  definite!: boolean;\n",
        "  static count: number;\n",
        "}\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

    for (index, options) in [
        CanonicalCheckerOptions::default(),
        CanonicalCheckerOptions {
            strict_property_initialization: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    ]
    .into_iter()
    .enumerate()
    {
        let file = FileId::new(10 + u32::try_from(index).unwrap());
        let mut context =
            checker_context_with_options(&parsed, file, CanonicalModuleState::Script, options);
        let symbol = class_symbol(&parsed, file, &context, "Loose");

        context.check_source_file(file).unwrap();

        let members = context.get_nongeneric_class_members(symbol).unwrap();
        assert_eq!(members.instance_properties().len(), 3);
        assert_eq!(members.static_properties().len(), 1);
        assert!(is_type_checked(&context, file));
        assert!(context.diagnostics().is_empty());
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            members.clone(),
        );

        context.recheck_source_file(file).unwrap();
        let replayed = context.get_nongeneric_class_members(symbol).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
                replayed,
            ),
            warm
        );
        assert!(is_type_checked(&context, file));
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn strict_property_options_reject_later_unsafe_field_before_earlier_publication() {
    let parsed = parse_source_file(concat!(
        "class Early { value?: string; }\n",
        "class Later { value: string; static count: number; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = checker_context_with_options(
        &parsed,
        file,
        CanonicalModuleState::Script,
        strict_property_options(),
    );
    let early = class_symbol(&parsed, file, &context, "Early");
    let later = class_declaration(&parsed, file, "Later");
    let later_symbol = class_symbol(&parsed, file, &context, "Later");
    let before = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );

    for _ in 0..2 {
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Class(later)
            ))
        );
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
        for symbol in [early, later_symbol] {
            assert!(context.store().declared_type_links(symbol).is_none());
            assert!(context.store().value_symbol_links(symbol).is_none());
        }
        assert!(!is_type_checked(&context, file));
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn later_uninitialized_variable_keeps_an_admitted_loose_class_cold_across_retries() {
    let parsed = parse_source_file(concat!(
        "class Loose { bare: string; optional?: number; static count: number; }\n",
        "var missing: Loose;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(13);
    let mut context = checker_context(&parsed, file);
    let class = class_symbol(&parsed, file, &context, "Loose");
    let missing = variable_declaration(&parsed, file, "missing");
    let cold = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );

    for _ in 0..2 {
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::MissingVariableInitializer(missing)
            ))
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
            ),
            cold
        );
        assert!(context.store().declared_type_links(class).is_none());
        assert!(context.store().value_symbol_links(class).is_none());
        assert!(!is_type_checked(&context, file));
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn exported_class_is_unsupported_before_export_symbol_planning() {
    let parsed = parse_source_file("export class Exported { value?: string; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context =
        checker_context_with_module_state(&parsed, file, CanonicalModuleState::External);
    let declaration = class_declaration(&parsed, file, "Exported");
    let bound = context.file(file).unwrap().1;
    let exported = context
        .store()
        .get_merged_symbol(bound.symbol(declaration).unwrap())
        .unwrap();
    let local = context
        .store()
        .get_merged_symbol(bound.local_symbol(declaration).unwrap())
        .unwrap();
    let before = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );

    assert_eq!(
        context.check_source_file(file),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Class(declaration)
        ))
    );
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
    for symbol in [exported, local] {
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
    assert!(
        context
            .source_file(file)
            .and_then(|source| context.store().source_file_links(source))
            .is_none_or(|links| !links.type_checked)
    );
    assert!(context.diagnostics().is_empty());
}

#[test]
fn anonymous_class_declaration_is_unsupported_before_class_planning() {
    // This is the pinned smoke regression. The parser currently also retains
    // TS1003, but the bound anonymous declaration still reaches source checking.
    let parsed = parse_source_file("class {\n  @x\n  m() {}\n};");
    let file = FileId::new(0);
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::ClassDeclaration(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .expect("fixture has one anonymous class declaration");
    let mut context = checker_context(&parsed, file);
    let before = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );

    assert_eq!(
        context.check_source_file(file),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Class(declaration)
        ))
    );
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
    assert!(
        context
            .source_file(file)
            .and_then(|source| context.store().source_file_links(source))
            .is_none_or(|links| !links.type_checked)
    );
    assert!(context.diagnostics().is_empty());
}

#[test]
fn public_class_member_query_materializes_both_sides_and_default_constructor() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = checker_context(&parsed, file);
    let symbol = class_symbol(&parsed, file, &context, "Model");
    let class_record = context.store().symbol(symbol).unwrap();
    let declared_members = class_record.members().unwrap();
    let static_members = class_record.exports().unwrap();
    let counts = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );

    let members = context.get_nongeneric_class_members(symbol).unwrap();

    assert_eq!(context.store().type_len(), counts.0 + 3);
    assert_eq!(context.store().signature_len(), counts.1 + 1);
    assert_eq!(context.store().symbol_len(), counts.2);
    assert_eq!(
        context.store().symbol_store().symbol_table_len(),
        counts.3 + 1
    );
    assert_ne!(members.instance_members(), Some(declared_members));
    assert_eq!(members.static_members(), static_members);
    assert_eq!(members.instance_properties().len(), 2);
    assert_eq!(members.static_properties().len(), 1);

    let instance_table = context
        .store()
        .symbol_table(members.instance_members().unwrap())
        .unwrap();
    assert_eq!(instance_table.len(), 2);
    assert_eq!(
        instance_table.get_source("value"),
        Some(members.instance_properties()[0])
    );
    assert_eq!(
        instance_table.get_source("definite"),
        Some(members.instance_properties()[1])
    );
    let static_table = context.store().symbol_table(static_members).unwrap();
    assert_eq!(
        static_table.get_source("count"),
        Some(members.static_properties()[0])
    );
    assert_eq!(
        static_table.get_source("prototype"),
        Some(members.prototype())
    );

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let string_type = bootstrap.string_type;
    let number_type = bootstrap.number_type;
    let undefined_type = bootstrap.undefined_type;
    let property_expectations = [
        (
            members.instance_properties()[0],
            "value",
            string_type,
            SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL,
            CheckFlags::READONLY,
        ),
        (
            members.instance_properties()[1],
            "definite",
            number_type,
            SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ),
        (
            members.static_properties()[0],
            "count",
            number_type,
            SymbolFlags::PROPERTY,
            CheckFlags::READONLY,
        ),
    ];
    for (property, name, type_, flags, check_flags) in property_expectations {
        let record = context.store().symbol(property).unwrap();
        assert_eq!(record.flags(), flags);
        assert_eq!(record.check_flags(), check_flags);
        assert_eq!(
            context.store().value_symbol_links(property),
            Some(&ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
        );
        assert_eq!(
            context
                .store()
                .type_node_links(property_type_node(&parsed, file, name)),
            Some(&TypeNodeLinks {
                resolved_type: Some(type_),
                ..TypeNodeLinks::default()
            })
        );
    }

    let shells = members.shells();
    let instance_record = context
        .store()
        .type_payload(shells.instance_type())
        .unwrap();
    assert_eq!(
        instance_record.object_flags(),
        ObjectFlags::CLASS | ObjectFlags::REFERENCE | ObjectFlags::MEMBERS_RESOLVED
    );
    let TypeData::Interface(instance) = instance_record.data() else {
        panic!("class instance must use interface storage")
    };
    assert!(instance.base_types_resolved);
    assert_eq!(
        instance.resolved_base_constructor_type,
        Some(undefined_type)
    );
    assert_eq!(instance.resolved_base_types, None);
    assert!(instance.declared_members_resolved);
    assert_eq!(instance.declared_members, Some(declared_members));
    assert_eq!(instance.declared_call_signatures, None);
    assert_eq!(instance.declared_construct_signatures, None);
    assert_eq!(instance.declared_index_infos, None);
    assert_eq!(
        instance.reference.object.structured.members,
        members.instance_members()
    );
    assert_eq!(
        instance.reference.object.structured.properties.as_deref(),
        Some(members.instance_properties())
    );
    assert_eq!(instance.reference.object.structured.signatures, None);
    assert_eq!(instance.reference.object.structured.call_signature_count, 0);
    assert_eq!(instance.reference.object.structured.index_infos, None);
    assert_eq!(instance.reference.resolved_type_arguments, Some(Vec::new()));
    let TypeCacheState::Allocated(instantiations) = &instance.reference.object.instantiations
    else {
        panic!("class instance owns its self-instantiation")
    };
    assert_eq!(instantiations.len(), 1);

    let value_record = context.store().type_payload(shells.value_type()).unwrap();
    assert_eq!(value_record.flags(), TypeFlags::OBJECT);
    assert_eq!(
        value_record.object_flags(),
        ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
    );
    let TypeData::Object(value) = value_record.data() else {
        panic!("class value must use object storage")
    };
    assert_eq!(value.structured.members, Some(static_members));
    assert_eq!(
        value.structured.properties.as_deref(),
        Some(&[members.static_properties()[0], members.prototype()][..])
    );
    assert_eq!(value.structured.call_signature_count, 0);
    assert_eq!(
        value.structured.signatures.as_deref(),
        Some(&[members.default_construct_signature()][..])
    );
    assert_eq!(value.structured.index_infos, None);

    let signature = context
        .store()
        .signature(members.default_construct_signature())
        .unwrap();
    assert_eq!(signature.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(signature.declaration(), None);
    assert!(signature.type_parameters().is_empty());
    assert!(signature.parameters().is_empty());
    assert_eq!(signature.this_parameter(), None);
    assert_eq!(
        signature.resolved_return_type(),
        Some(shells.instance_type())
    );
    assert_eq!(signature.resolved_type_predicate(), None);
    assert_eq!(signature.min_argument_count(), 0);
    assert_eq!(signature.resolved_min_argument_count(), -1);
    assert_eq!(signature.target(), None);
    assert_eq!(signature.mapper(), None);
    assert_eq!(signature.isolated_signature_type(), None);
    assert_eq!(signature.composite(), None);

    let warm_counts = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );
    assert_eq!(
        context.get_nongeneric_class_members(symbol).unwrap(),
        members
    );
    assert_eq!(context.get_nongeneric_class_shells(symbol).unwrap(), shells);
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        ),
        warm_counts
    );
    assert!(context.diagnostics().is_empty());
}
