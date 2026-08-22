use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, ResolvedSignatureState, SignatureLinks,
    SourceCheckError, SymbolNodeLinks, TypeData, TypeNodeLinks, UnsupportedSourceSyntax,
    ValueSymbolLinks,
    signatures::SignatureFlags,
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "class Model { value!: string; }\n",
    "const model = new Model();\n",
    "const value = model.value;\n",
);

fn checker_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-default-new.ts\""),
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

fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let declaration = variable_declaration(parsed, file, expected);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!("the helper selected a variable declaration")
    };
    NodeRef::new(
        parsed.arena.id(),
        file,
        variable
            .initializer
            .expect("fixture variable is initialized"),
    )
}

fn variable_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = variable_declaration(parsed, file, expected);
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn constructor(parsed: &ParseResult, new_expression: NodeRef) -> NodeRef {
    let NodeData::NewExpression(new_expression_data) =
        &parsed.arena.get(new_expression.node).unwrap().data
    else {
        panic!("expected a new expression")
    };
    NodeRef::new(
        new_expression.arena,
        new_expression.file,
        new_expression_data.expression,
    )
}

fn first_new_expression(parsed: &ParseResult, file: FileId) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(&record.data, NodeData::NewExpression(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .expect("fixture contains a new expression")
}

#[test]
#[allow(clippy::too_many_lines)] // Constructor identity and warm caches require one source graph.
fn direct_default_new_publishes_exact_instance_signature_and_warm_caches() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1_801);
    let mut context = checker_context(&parsed, file);
    let class = class_symbol(&parsed, file, &context, "Model");
    let model = variable_symbol(&parsed, file, &context, "model");
    let value = variable_symbol(&parsed, file, &context, "value");
    let construction = variable_initializer(&parsed, file, "model");
    let constructor = constructor(&parsed, construction);
    let access = variable_initializer(&parsed, file, "value");

    context.check_source_file(file).unwrap();

    let members = context.get_nongeneric_class_members(class).unwrap();
    let shells = members.shells();
    let signature = members.default_construct_signature();
    assert_eq!(
        context.store().symbol_node_links(constructor),
        Some(&SymbolNodeLinks {
            resolved_symbol: Some(class),
        })
    );
    assert_eq!(
        context.store().type_node_links(constructor),
        Some(&TypeNodeLinks {
            resolved_type: Some(shells.value_type()),
            ..TypeNodeLinks::default()
        })
    );
    assert_eq!(
        context.store().signature_links(construction),
        Some(&SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        })
    );
    assert_eq!(
        context.store().type_node_links(construction),
        Some(&TypeNodeLinks {
            resolved_type: Some(shells.instance_type()),
            ..TypeNodeLinks::default()
        })
    );
    assert_eq!(
        context.store().value_symbol_links(model),
        Some(&ValueSymbolLinks {
            resolved_type: Some(shells.instance_type()),
            ..ValueSymbolLinks::default()
        })
    );

    let signature_record = context.store().signature(signature).unwrap();
    assert_eq!(signature_record.flags(), SignatureFlags::CONSTRUCT);
    assert!(
        !signature_record
            .flags()
            .intersects(SignatureFlags::ABSTRACT)
    );
    assert!(signature_record.declaration().is_none());
    assert!(signature_record.type_parameters().is_empty());
    assert!(signature_record.parameters().is_empty());
    assert_eq!(signature_record.min_argument_count(), 0);
    assert_eq!(
        signature_record.resolved_return_type(),
        Some(shells.instance_type())
    );

    let value_record = context.store().type_payload(shells.value_type()).unwrap();
    assert_eq!(value_record.flags(), TypeFlags::OBJECT);
    assert_eq!(
        value_record.object_flags(),
        ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
    );
    let TypeData::Object(value_type) = value_record.data() else {
        panic!("class value must use object storage")
    };
    assert_eq!(value_type.structured.call_signature_count, 0);
    assert_eq!(
        value_type.structured.signatures.as_deref(),
        Some(&[signature][..])
    );

    let instance_record = context
        .store()
        .type_payload(shells.instance_type())
        .unwrap();
    let TypeData::Interface(instance) = instance_record.data() else {
        panic!("class instance must use interface storage")
    };
    assert_eq!(
        instance.reference.object.target,
        Some(shells.instance_type())
    );

    let property = members.instance_properties()[0];
    let string_type = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(
        context.store().symbol_node_links(access),
        Some(&SymbolNodeLinks {
            resolved_symbol: Some(property),
        })
    );
    assert_eq!(
        context.store().type_node_links(access),
        Some(&TypeNodeLinks {
            resolved_type: Some(string_type),
            ..TypeNodeLinks::default()
        })
    );
    assert_eq!(
        context.store().value_symbol_links(value),
        Some(&ValueSymbolLinks {
            resolved_type: Some(string_type),
            ..ValueSymbolLinks::default()
        })
    );
    assert!(context.diagnostics().is_empty());

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
        context.store().symbol_node_links(constructor).cloned(),
        context.store().type_node_links(constructor).cloned(),
        context.store().signature_links(construction).cloned(),
        context.store().type_node_links(construction).cloned(),
        context.store().type_node_links(access).cloned(),
        context.diagnostics().len(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        context.get_nongeneric_class_members(class).unwrap(),
        members
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            context.store().symbol_node_links(constructor).cloned(),
            context.store().type_node_links(constructor).cloned(),
            context.store().signature_links(construction).cloned(),
            context.store().type_node_links(construction).cloned(),
            context.store().type_node_links(access).cloned(),
            context.diagnostics().len(),
        ),
        warm
    );
}

#[test]
fn derived_default_new_accepts_optional_parentheses_and_reuses_inherited_members() {
    let parsed = parse_source_file(concat!(
        "class Base { base!: string; static count: number; }\n",
        "class Derived extends Base { own!: number; }\n",
        "const explicit = new Derived();\n",
        "const implicit = new Derived;\n",
        "const inherited = implicit.base;\n",
        "const own = explicit.own;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1_807);
    let mut context = checker_context(&parsed, file);
    let base_symbol = class_symbol(&parsed, file, &context, "Base");
    let derived_symbol = class_symbol(&parsed, file, &context, "Derived");
    let explicit = variable_initializer(&parsed, file, "explicit");
    let implicit = variable_initializer(&parsed, file, "implicit");
    let inherited = variable_symbol(&parsed, file, &context, "inherited");
    let own = variable_symbol(&parsed, file, &context, "own");

    context.check_source_file(file).unwrap();

    let base = context.get_nongeneric_class_members(base_symbol).unwrap();
    let derived = context
        .get_nongeneric_class_members(derived_symbol)
        .unwrap();
    assert_eq!(
        derived
            .base()
            .map(ts_checker::semantic::ClassBaseIdentities::instance_type),
        Some(base.shells().instance_type())
    );
    for construction in [explicit, implicit] {
        assert_eq!(
            context
                .store()
                .symbol_node_links(constructor(&parsed, construction)),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(derived_symbol),
            })
        );
        assert_eq!(
            context.store().type_node_links(construction),
            Some(&TypeNodeLinks {
                resolved_type: Some(derived.shells().instance_type()),
                ..TypeNodeLinks::default()
            })
        );
        assert_eq!(
            context.store().signature_links(construction),
            Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(
                    derived.default_construct_signature(),
                ),
                ..SignatureLinks::default()
            })
        );
    }
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(inherited)
            .and_then(|links| links.resolved_type),
        Some(bootstrap.string_type)
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(own)
            .and_then(|links| links.resolved_type),
        Some(bootstrap.number_type)
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );
    context.recheck_source_file(file).unwrap();
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
    assert!(context.diagnostics().is_empty());
}

#[test]
fn later_invalid_new_preflights_before_earlier_class_or_new_publication() {
    let parsed = parse_source_file(concat!(
        "class Early { value!: string; }\n",
        "const early = new Early();\n",
        "class Later { value!: string; }\n",
        "const bad = new Later(1);\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1_802);
    let mut context = checker_context(&parsed, file);
    let early_class = class_symbol(&parsed, file, &context, "Early");
    let early_new = variable_initializer(&parsed, file, "early");
    let early_constructor = constructor(&parsed, early_new);
    let bad_new = variable_initializer(&parsed, file, "bad");
    let before = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );

    assert_eq!(
        context.check_source_file(file),
        Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
            bad_new
        )))
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
    assert!(context.store().declared_type_links(early_class).is_none());
    assert!(context.store().value_symbol_links(early_class).is_none());
    assert!(
        context
            .store()
            .symbol_node_links(early_constructor)
            .is_none()
    );
    assert!(context.store().type_node_links(early_constructor).is_none());
    assert!(context.store().signature_links(early_new).is_none());
    assert!(context.store().type_node_links(early_new).is_none());
    assert!(context.diagnostics().is_empty());
}

#[test]
fn unsupported_new_forms_stop_at_typed_boundaries() {
    for (source, expected_node) in [
        (
            "class Model { value!: string; } const model = new Model(1);",
            "new",
        ),
        (
            "class Model { value!: string; } const model = new Model<string>();",
            "new",
        ),
        (
            "const factory = 1; const model = new factory();",
            "constructor",
        ),
        (
            "const model = new Model(); class Model { value!: string; }",
            "constructor",
        ),
    ] {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_803);
        let construction = first_new_expression(&parsed, file);
        let boundary = if expected_node == "constructor" {
            constructor(&parsed, construction)
        } else {
            construction
        };
        let mut context = checker_context(&parsed, file);
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                boundary
            ))),
            "{source}"
        );
        assert!(context.diagnostics().is_empty());
    }

    for source in [
        "abstract class Model { value!: string; } const model = new Model();",
        "class Model { constructor(value: string) {} value!: string; } const model = new Model();",
    ] {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_804);
        let mut context = checker_context(&parsed, file);
        assert!(
            matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Class(_)
                ))
            ),
            "{source}"
        );
        assert!(context.diagnostics().is_empty());
    }

    let source = "class Model { value!: string; } const model = new Model?.();";
    let parsed = parse_source_file(source);
    assert!(!parsed.diagnostics.is_empty());
    let file = FileId::new(1_805);
    let mut context = checker_context(&parsed, file);
    assert!(matches!(
        context.check_source_file(file),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(_)
        ))
    ));
    assert!(context.diagnostics().is_empty());
}
