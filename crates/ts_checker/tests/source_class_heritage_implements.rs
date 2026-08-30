use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostic, CanonicalCheckerOptions, ClassMembers,
    TypeData,
};
use ts_parser::{ParseResult, parse_source_file};

fn checker_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-heritage-implements.ts\""),
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

fn declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name = match &record.data {
                NodeData::ClassDeclaration(class) => class.name?,
                NodeData::InterfaceDeclaration(interface) => interface.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"))
}

fn declaration_name(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let name = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::ClassDeclaration(class) => class.name.unwrap(),
        NodeData::InterfaceDeclaration(interface) => interface.name,
        _ => panic!("expected a class or interface declaration"),
    };
    NodeRef::new(parsed.arena.id(), declaration.file, name)
}

fn property(parsed: &ParseResult, owner: NodeRef, expected: &str) -> (NodeRef, NodeRef) {
    let members = match &parsed.arena.get(owner.node).unwrap().data {
        NodeData::ClassDeclaration(class) => &class.members.nodes,
        NodeData::InterfaceDeclaration(interface) => &interface.members.nodes,
        _ => panic!("expected a class or interface declaration"),
    };
    members
        .iter()
        .find_map(|&member| {
            let name = match &parsed.arena.get(member)?.data {
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::PropertySignatureDeclaration(property) => property.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some((
                NodeRef::new(parsed.arena.id(), owner.file, member),
                NodeRef::new(parsed.arena.id(), owner.file, name),
            ))
        })
        .unwrap_or_else(|| panic!("missing property {expected}"))
}

fn bound_symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn read_access(parsed: &ParseResult, file: FileId, expected: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(access.name)?.data else {
                return None;
            };
            (name.text == expected).then_some((
                NodeRef::new(parsed.arena.id(), file, node),
                NodeRef::new(parsed.arena.id(), file, access.name),
            ))
        })
        .unwrap_or_else(|| panic!("missing property read {expected}"))
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 6] {
    [
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.store().mapper_len(),
        context.store().index_info_len(),
        context.store().symbol_store().symbol_table_len(),
    ]
}

fn assert_actual_base(
    context: &mut CanonicalCheckerContext<'_>,
    base_symbol: SemanticSymbolId,
    derived_symbol: SemanticSymbolId,
) -> ClassMembers {
    let base = context.get_nongeneric_class_members(base_symbol).unwrap();
    let derived = context
        .get_nongeneric_class_members(derived_symbol)
        .unwrap();
    let inherited = derived.base().expect("Derived must keep its actual base");
    assert_eq!(inherited.symbol(), base_symbol);
    assert_eq!(inherited.instance_type(), base.shells().instance_type());
    assert_eq!(inherited.value_type(), base.shells().value_type());
    let TypeData::Interface(instance) = context
        .store()
        .type_payload(derived.shells().instance_type())
        .unwrap()
        .data()
    else {
        panic!("class instance must retain its interface payload")
    };
    assert_eq!(
        instance.resolved_base_types.as_deref(),
        Some(&[base.shells().instance_type()][..])
    );
    assert_eq!(
        instance.resolved_base_constructor_type,
        Some(base.shells().value_type())
    );
    assert_eq!(
        context.is_type_assignable_to(
            derived.shells().instance_type(),
            base.shells().instance_type(),
        ),
        Ok(true)
    );
    derived
}

fn assert_warm_replay(
    context: &mut CanonicalCheckerContext<'_>,
    file: FileId,
    derived_symbol: SemanticSymbolId,
    symbols: &[SemanticSymbolId],
) {
    let members = context
        .get_nongeneric_class_members(derived_symbol)
        .unwrap();
    let types = symbols
        .iter()
        .map(|&symbol| context.get_declared_type_of_symbol(symbol).unwrap())
        .collect::<Vec<_>>();
    let warm = (
        counts(context),
        context.store().relation_state_snapshot(),
        context.diagnostics().clone(),
    );
    context.check_source_file(file).unwrap();
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        context
            .get_nongeneric_class_members(derived_symbol)
            .unwrap(),
        members
    );
    for (&symbol, type_) in symbols.iter().zip(types) {
        assert_eq!(context.get_declared_type_of_symbol(symbol).unwrap(), type_);
    }
    assert_eq!(
        (
            counts(context),
            context.store().relation_state_snapshot(),
            context.diagnostics().clone(),
        ),
        warm
    );
    assert!(
        context
            .source_file(file)
            .and_then(|source| context.store().source_file_links(source))
            .is_some_and(|links| links.type_checked)
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

fn assert_missing_property(
    diagnostic: &CanonicalCheckerDiagnostic,
    class_name: NodeRef,
    detail_source_name: &str,
    interface_name: &str,
    property_name: &str,
    property_node: NodeRef,
) {
    assert_diagnostic(
        diagnostic,
        class_name,
        2420,
        &["Derived", interface_name],
        &format!(
            "Class 'Derived' incorrectly implements interface '{interface_name}'.\n  Property '{property_name}' is missing in type '{detail_source_name}' but required in type '{interface_name}'."
        ),
    );
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("missing field must have one declaration note")
    };
    assert_eq!(related.node, Some(property_node));
    assert_eq!(related.diagnostic.code(), 2728);
    assert_eq!(related.diagnostic.arguments, [property_name]);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        format!("'{property_name}' is declared here.")
    );
}

#[test]
fn combined_heritage_keeps_base_members_and_replays_public_queries() {
    let parsed = parse_source_file(concat!(
        "interface Contract { inherited: string; own: number; }\n",
        "class Base { inherited: string; baseOnly: boolean; }\n",
        "class Derived extends Base implements Contract { own: number; }\n",
        "declare const child: Derived;\n",
        "const inherited = child.inherited;\n",
        "const own = child.own;\n",
        "const extra = child.baseOnly;\n",
    ));
    let file = FileId::new(0);
    let mut context = checker_context(&parsed, file);
    let base_node = declaration(&parsed, file, "Base");
    let derived_node = declaration(&parsed, file, "Derived");
    let contract_node = declaration(&parsed, file, "Contract");
    let base = bound_symbol(&context, base_node);
    let derived = bound_symbol(&context, derived_node);
    let contract = bound_symbol(&context, contract_node);
    let inherited = bound_symbol(&context, property(&parsed, base_node, "inherited").0);
    let base_only = bound_symbol(&context, property(&parsed, base_node, "baseOnly").0);
    let own = bound_symbol(&context, property(&parsed, derived_node, "own").0);
    assert_ne!(
        inherited,
        bound_symbol(&context, property(&parsed, contract_node, "inherited").0)
    );

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let members = assert_actual_base(&mut context, base, derived);
    assert_eq!(members.declared_instance_properties(), [own]);
    assert_eq!(members.instance_properties(), [own, inherited, base_only]);
    let contract_type = context.get_declared_type_of_symbol(contract).unwrap();
    assert_eq!(
        context.is_type_assignable_to(members.shells().instance_type(), contract_type),
        Ok(true)
    );
    assert_eq!(
        context.is_type_assignable_to(
            members.base().unwrap().instance_type(),
            members.shells().instance_type(),
        ),
        Ok(false)
    );
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let reads = [
        ("inherited", inherited, bootstrap.string_type),
        ("own", own, bootstrap.number_type),
        ("baseOnly", base_only, bootstrap.boolean_type),
    ];
    for (name, symbol, type_) in reads {
        let (access, name) = read_access(&parsed, file, name);
        assert_eq!(context.get_type_at_location(access).unwrap(), type_);
        assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
    }

    assert_warm_replay(&mut context, file, derived, &[base, derived, contract]);
    let warm = counts(&context);
    for (name, symbol, type_) in reads {
        let (access, name) = read_access(&parsed, file, name);
        assert_eq!(context.get_type_at_location(access).unwrap(), type_);
        assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
    }
    assert_eq!(counts(&context), warm);
}

#[test]
fn combined_heritage_reports_missing_interface_field_without_changing_base() {
    let parsed = parse_source_file(concat!(
        "interface Contract { inherited: string; missing: number; }\n",
        "class Base { inherited: string; }\n",
        "class Derived extends Base implements Contract {}\n",
    ));
    let file = FileId::new(1);
    let mut context = checker_context(&parsed, file);
    let base_node = declaration(&parsed, file, "Base");
    let derived_node = declaration(&parsed, file, "Derived");
    let contract_node = declaration(&parsed, file, "Contract");
    let base = bound_symbol(&context, base_node);
    let derived = bound_symbol(&context, derived_node);
    let contract = bound_symbol(&context, contract_node);

    context.check_source_file(file).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "expected one missing-field diagnostic: {:?}",
            context.diagnostics()
        )
    };
    assert_missing_property(
        diagnostic,
        declaration_name(&parsed, derived_node),
        "Base",
        "Contract",
        "missing",
        property(&parsed, contract_node, "missing").1,
    );
    let members = assert_actual_base(&mut context, base, derived);
    assert!(members.declared_instance_properties().is_empty());
    assert_eq!(
        members.instance_properties(),
        [bound_symbol(
            &context,
            property(&parsed, base_node, "inherited").0
        )]
    );
    let contract_type = context.get_declared_type_of_symbol(contract).unwrap();
    assert_eq!(
        context.is_type_assignable_to(members.shells().instance_type(), contract_type),
        Ok(false)
    );
    assert_warm_replay(&mut context, file, derived, &[base, derived, contract]);
}

#[test]
fn combined_heritage_distinguishes_own_and_inherited_member_errors() {
    for (source, own_member) in [
        (
            concat!(
                "interface Contract { value: string; }\n",
                "class Base { value: number; }\n",
                "class Derived extends Base implements Contract {}\n",
            ),
            false,
        ),
        (
            concat!(
                "interface Contract { value: string; }\n",
                "class Base { baseOnly: boolean; }\n",
                "class Derived extends Base implements Contract { value: number; }\n",
            ),
            true,
        ),
    ] {
        let parsed = parse_source_file(source);
        let file = FileId::new(2);
        let mut context = checker_context(&parsed, file);
        let base_node = declaration(&parsed, file, "Base");
        let derived_node = declaration(&parsed, file, "Derived");
        let contract_node = declaration(&parsed, file, "Contract");
        let base = bound_symbol(&context, base_node);
        let derived = bound_symbol(&context, derived_node);
        let contract = bound_symbol(&context, contract_node);

        context.check_source_file(file).unwrap();
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!(
                "expected one member diagnostic: {:?}",
                context.diagnostics()
            )
        };
        if own_member {
            assert_diagnostic(
                diagnostic,
                property(&parsed, derived_node, "value").1,
                2416,
                &["value", "Derived", "Contract"],
                "Property 'value' in type 'Derived' is not assignable to the same property in base type 'Contract'.\n  Type 'number' is not assignable to type 'string'.",
            );
        } else {
            assert_diagnostic(
                diagnostic,
                declaration_name(&parsed, derived_node),
                2420,
                &["Derived", "Contract"],
                "Class 'Derived' incorrectly implements interface 'Contract'.\n  Types of property 'value' are incompatible.\n    Type 'number' is not assignable to type 'string'.",
            );
        }
        assert!(diagnostic.related_information.is_empty());
        let members = assert_actual_base(&mut context, base, derived);
        let value_owner = if own_member { derived_node } else { base_node };
        let value = bound_symbol(&context, property(&parsed, value_owner, "value").0);
        assert!(members.instance_properties().contains(&value));
        assert_eq!(
            members.declared_instance_properties().contains(&value),
            own_member
        );
        let contract_type = context.get_declared_type_of_symbol(contract).unwrap();
        assert_eq!(
            context.is_type_assignable_to(members.shells().instance_type(), contract_type),
            Ok(false)
        );
        assert_warm_replay(&mut context, file, derived, &[base, derived, contract]);
    }
}

#[test]
fn combined_heritage_checks_implemented_interfaces_in_clause_order() {
    let parsed = parse_source_file(concat!(
        "interface First { first: number; }\n",
        "interface Second { second: string; }\n",
        "class Base { baseOnly: boolean; }\n",
        "class Derived extends Base implements Second, First {}\n",
    ));
    let file = FileId::new(3);
    let mut context = checker_context(&parsed, file);
    let base_node = declaration(&parsed, file, "Base");
    let derived_node = declaration(&parsed, file, "Derived");
    let first_node = declaration(&parsed, file, "First");
    let second_node = declaration(&parsed, file, "Second");
    let base = bound_symbol(&context, base_node);
    let derived = bound_symbol(&context, derived_node);
    let first = bound_symbol(&context, first_node);
    let second = bound_symbol(&context, second_node);

    context.check_source_file(file).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    for (diagnostic, target, property_name) in [
        (&diagnostics[0], second_node, "second"),
        (&diagnostics[1], first_node, "first"),
    ] {
        let interface_name = if target == second_node {
            "Second"
        } else {
            "First"
        };
        assert_missing_property(
            diagnostic,
            declaration_name(&parsed, derived_node),
            "Base",
            interface_name,
            property_name,
            property(&parsed, target, property_name).1,
        );
    }
    let members = assert_actual_base(&mut context, base, derived);
    assert!(members.declared_instance_properties().is_empty());
    assert_eq!(
        members.instance_properties(),
        [bound_symbol(
            &context,
            property(&parsed, base_node, "baseOnly").0
        )]
    );
    for target in [second, first] {
        let target_type = context.get_declared_type_of_symbol(target).unwrap();
        assert_eq!(
            context.is_type_assignable_to(members.shells().instance_type(), target_type),
            Ok(false)
        );
    }
    assert_warm_replay(&mut context, file, derived, &[base, derived, first, second]);
}

#[test]
fn implements_only_checks_the_same_interface_without_adding_a_base() {
    for (source, conforms) in [
        (
            concat!(
                "interface Contract { value: string; }\n",
                "class Derived implements Contract { value: string; }\n",
            ),
            true,
        ),
        (
            concat!(
                "interface Contract { value: string; }\n",
                "class Derived implements Contract {}\n",
            ),
            false,
        ),
    ] {
        let parsed = parse_source_file(source);
        let file = FileId::new(4);
        let mut context = checker_context(&parsed, file);
        let derived_node = declaration(&parsed, file, "Derived");
        let contract_node = declaration(&parsed, file, "Contract");
        let derived = bound_symbol(&context, derived_node);
        let contract = bound_symbol(&context, contract_node);

        context.check_source_file(file).unwrap();
        if conforms {
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
        } else {
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!(
                    "expected one missing-field diagnostic: {:?}",
                    context.diagnostics()
                )
            };
            assert_missing_property(
                diagnostic,
                declaration_name(&parsed, derived_node),
                "Derived",
                "Contract",
                "value",
                property(&parsed, contract_node, "value").1,
            );
        }
        let members = context.get_nongeneric_class_members(derived).unwrap();
        assert_eq!(members.base(), None);
        assert_eq!(
            members.instance_properties(),
            members.declared_instance_properties()
        );
        if conforms {
            assert_eq!(
                members.instance_properties(),
                [bound_symbol(
                    &context,
                    property(&parsed, derived_node, "value").0
                )]
            );
        } else {
            assert!(members.instance_properties().is_empty());
        }
        let TypeData::Interface(instance) = context
            .store()
            .type_payload(members.shells().instance_type())
            .unwrap()
            .data()
        else {
            panic!("class instance must retain its interface payload")
        };
        assert_eq!(instance.resolved_base_types, None);
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
        let contract_type = context.get_declared_type_of_symbol(contract).unwrap();
        assert_eq!(
            context.is_type_assignable_to(members.shells().instance_type(), contract_type),
            Ok(conforms)
        );
        assert_warm_replay(&mut context, file, derived, &[derived, contract]);
    }
}

#[test]
fn parameter_property_mismatch_reports_the_class_implementation_error() {
    let parsed = parse_source_file(concat!(
        "interface Contract { value: string; }\n",
        "class Derived implements Contract { constructor(public value: number) {} }\n",
    ));
    let file = FileId::new(5);
    let mut context = checker_context(&parsed, file);
    let derived_node = declaration(&parsed, file, "Derived");
    let contract_node = declaration(&parsed, file, "Contract");
    let derived = bound_symbol(&context, derived_node);
    let contract = bound_symbol(&context, contract_node);
    let parameter = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::ParameterDeclaration(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap();
    let value = bound_symbol(&context, parameter);

    context.check_source_file(file).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "expected one parameter-property diagnostic: {:?}",
            context.diagnostics()
        )
    };
    assert_diagnostic(
        diagnostic,
        declaration_name(&parsed, derived_node),
        2420,
        &["Derived", "Contract"],
        "Class 'Derived' incorrectly implements interface 'Contract'.\n  Types of property 'value' are incompatible.\n    Type 'number' is not assignable to type 'string'.",
    );
    assert!(diagnostic.related_information.is_empty());
    let members = context.get_nongeneric_class_members(derived).unwrap();
    assert_eq!(members.base(), None);
    assert_eq!(members.declared_instance_properties(), [value]);
    assert_eq!(members.instance_properties(), [value]);
    assert_eq!(
        context
            .store()
            .value_symbol_links(value)
            .unwrap()
            .resolved_type,
        Some(context.store().intrinsic_bootstrap().unwrap().number_type)
    );
    let contract_type = context.get_declared_type_of_symbol(contract).unwrap();
    assert_eq!(
        context.is_type_assignable_to(members.shells().instance_type(), contract_type),
        Ok(false)
    );
    assert_warm_replay(&mut context, file, derived, &[derived, contract]);
}
