use ts_ast::FileId;
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
};
use ts_parser::{ParseResult, parse_source_file};

use super::*;
use crate::semantic::{CanonicalCheckerContext, IntrinsicBootstrapOptions};

const FILE: FileId = FileId::new(97_101);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/private-object.ts\""),
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
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

#[derive(Clone, Copy)]
struct Field {
    owner: SemanticSymbolId,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    initializer: NodeRef,
}

fn source_field(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult, name: &str) -> Field {
    let (class_node, class) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            matches!(&parsed.arena.get(class.name?).unwrap().data,
                NodeData::Identifier(identifier) if identifier.text == name)
            .then_some((node, class))
        })
        .unwrap();
    let bound = context.file(FILE).unwrap().1;
    let owner = bound
        .symbol(NodeRef::new(parsed.arena.id(), FILE, class_node))
        .unwrap();
    let (declaration, initializer) = class
        .members
        .nodes
        .iter()
        .find_map(|node| {
            let NodeData::PropertyDeclaration(property) = &parsed.arena.get(*node)?.data else {
                return None;
            };
            Some((
                NodeRef::new(parsed.arena.id(), FILE, *node),
                NodeRef::new(parsed.arena.id(), FILE, property.initializer?),
            ))
        })
        .unwrap();
    Field {
        owner,
        symbol: bound.symbol(declaration).unwrap(),
        declaration,
        initializer,
    }
}

fn counts(context: &CanonicalCheckerContext<'_>) -> ([usize; 4], [usize; 26]) {
    (
        [
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
        ],
        context.store().checker_link_allocated_lengths(),
    )
}

fn object_member(store: &CanonicalTypeMapperStore, object: TypeId, name: &str) -> SemanticSymbolId {
    let TypeData::Object(object) = store.type_payload(object).unwrap().data() else {
        panic!("the checked initializer and field are object types")
    };
    store
        .symbol_table(object.structured.members.unwrap())
        .unwrap()
        .get_source(name)
        .unwrap()
}

#[test]
fn private_object_field_queries_require_completed_source_initializers() {
    for modifier in ["", "readonly "] {
        let source = format!(
            "class Model {{ {modifier}#state = {{ value: 0, nested: {{ enabled: true }} }}; \
             read() {{ return this.#state; }} }}"
        );
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        let field = source_field(&context, &parsed, "Model");
        let cold = counts(&context);
        for _ in 0..2 {
            assert_eq!(
                context.get_class_query_member_type(field.symbol),
                Err(ClassError::Unsupported(
                    ClassUnsupported::PropertyInitializer(field.declaration)
                )),
            );
            assert_eq!(counts(&context), cold);
            assert!(context.store().value_symbol_links(field.symbol).is_none());
            assert!(context.store().type_node_links(field.initializer).is_none());
            assert!(context.store().declared_type_links(field.owner).is_none());
            assert!(
                context
                    .store()
                    .source_class_provenance_for_symbol(field.owner)
                    .is_none()
            );
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(FILE).unwrap())
                    .is_none_or(|links| !links.type_checked)
            );
            assert!(context.diagnostics().is_empty());
        }

        context.check_source_file(FILE).unwrap();
        let raw = context
            .store()
            .type_node_links(field.initializer)
            .unwrap()
            .resolved_type
            .unwrap();
        let widened = context.get_class_query_member_type(field.symbol).unwrap();
        assert_ne!(raw, widened);
        assert!(context.store().validate_cached_widened_type(
            raw,
            widened,
            Some(context.global_types()),
        ));
        let provenance = context
            .store()
            .source_class_provenance_for_symbol(field.owner)
            .unwrap();
        let instance = provenance.instance_type();
        assert!(provenance.complete);
        assert!(provenance.completed_bodies.iter().all(|complete| *complete));
        assert_eq!(provenance.property_types, [Some(widened)]);
        assert_eq!(
            provenance.prepared.plan.initialized_properties[0].symbol,
            field.symbol
        );
        assert_eq!(
            provenance.prepared.plan.sources[0].visibility,
            ClassConstructorVisibility::Private,
        );
        assert_eq!(
            context.store().symbol(field.symbol).unwrap().parent(),
            Some(field.owner)
        );
        assert!(
            context
                .store()
                .symbol(field.symbol)
                .unwrap()
                .name()
                .is_private_identifier()
        );
        assert_eq!(
            context.store().symbol(field.symbol).unwrap().check_flags(),
            if modifier.is_empty() {
                CheckFlags::NONE
            } else {
                CheckFlags::READONLY
            },
        );
        let warm = counts(&context);
        for _ in 0..2 {
            assert_eq!(
                context.get_class_query_member_type(field.symbol),
                Ok(widened)
            );
            context.check_source_file(FILE).unwrap();
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(counts(&context), warm);
        }

        context
            .store_mut_for_test()
            .source_class_provenance_mut(instance)
            .unwrap()
            .complete = false;
        {
            let host = context.declared_type_host().unwrap();
            assert_eq!(
                completed_source_class_property_type(
                    context.store(),
                    &host,
                    field.owner,
                    field.symbol,
                    field.declaration,
                    field.initializer,
                ),
                Ok(None),
            );
        }
        assert!(matches!(
            context.get_class_query_member_type(field.symbol),
            Err(ClassError::Invariant(_)),
        ));
        assert_eq!(counts(&context), warm);
        context
            .store_mut_for_test()
            .source_class_provenance_mut(instance)
            .unwrap()
            .complete = true;
        assert_eq!(
            context.get_class_query_member_type(field.symbol),
            Ok(widened)
        );
        assert_eq!(counts(&context), warm);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn private_object_field_caches_reject_foreign_objects_and_changed_widened_properties() {
    let parsed = parse_source_file(concat!(
        "class Model { #state = { value: 0, nested: { enabled: true } }; }\n",
        "class Other { #state = { value: 1, nested: { enabled: false } }; }\n",
    ));
    for poison in [
        "initializer",
        "property",
        "paired_type",
        "paired_owner",
        "nested",
    ] {
        let mut context = context(&parsed);
        let field = source_field(&context, &parsed, "Model");
        let donor = source_field(&context, &parsed, "Other");
        context.check_source_file(FILE).unwrap();
        let raw_links = context
            .store()
            .type_node_links(field.initializer)
            .unwrap()
            .clone();
        let value_links = context
            .store()
            .value_symbol_links(field.symbol)
            .unwrap()
            .clone();
        let raw = raw_links.resolved_type.unwrap();
        let expected = value_links.resolved_type.unwrap();
        let donor_raw = context
            .store()
            .type_node_links(donor.initializer)
            .unwrap()
            .resolved_type
            .unwrap();
        let donor_type = context
            .store()
            .value_symbol_links(donor.symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        let instance = context
            .store()
            .source_class_provenance_for_symbol(field.owner)
            .unwrap()
            .instance_type();
        let nested = object_member(context.store(), expected, "nested");
        let raw_nested = object_member(context.store(), raw, "nested");
        assert_ne!(nested, raw_nested);
        let nested_links = context.store().value_symbol_links(nested).unwrap().clone();
        let donor_nested = object_member(context.store(), donor_type, "nested");
        let donor_nested_type = context
            .store()
            .value_symbol_links(donor_nested)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_ne!(raw, donor_raw);
        assert_ne!(expected, donor_type);
        match poison {
            "initializer" => assert!(context.store_mut_for_test().set_type_node_links(
                field.initializer,
                TypeNodeLinks {
                    resolved_type: Some(donor_raw),
                    ..raw_links.clone()
                },
            )),
            "property" => assert!(context.store_mut_for_test().set_value_symbol_links(
                field.symbol,
                ValueSymbolLinks {
                    resolved_type: Some(donor_type),
                    ..value_links.clone()
                },
            )),
            "paired_type" | "paired_owner" => {
                assert!(context.store_mut_for_test().set_value_symbol_links(
                    field.symbol,
                    ValueSymbolLinks {
                        resolved_type: Some(donor_type),
                        ..value_links.clone()
                    },
                ));
                context
                    .store_mut_for_test()
                    .source_class_provenance_mut(instance)
                    .unwrap()
                    .property_types[0] = Some(donor_type);
                if poison == "paired_owner" {
                    assert!(context.store_mut_for_test().set_type_node_links(
                        field.initializer,
                        TypeNodeLinks {
                            resolved_type: Some(donor_raw),
                            ..raw_links.clone()
                        },
                    ));
                }
            }
            "nested" => assert!(context.store_mut_for_test().set_value_symbol_links(
                nested,
                ValueSymbolLinks {
                    resolved_type: Some(donor_nested_type),
                    ..nested_links.clone()
                },
            )),
            _ => unreachable!(),
        }
        let changed = format!("{:?}", context.store());
        for _ in 0..2 {
            assert!(matches!(
                context.get_class_query_member_type(field.symbol),
                Err(ClassError::Invariant(_)),
            ));
            assert_eq!(format!("{:?}", context.store()), changed);
            assert!(context.diagnostics().is_empty());
        }
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(field.initializer, raw_links)
        );
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(field.symbol, value_links)
        );
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(nested, nested_links)
        );
        context
            .store_mut_for_test()
            .source_class_provenance_mut(instance)
            .unwrap()
            .property_types[0] = Some(expected);
        let restored = counts(&context);
        assert_eq!(
            context.get_class_query_member_type(field.symbol),
            Ok(expected)
        );
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(counts(&context), restored);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn private_object_initializer_admission_keeps_other_field_families_unsupported() {
    for source in [
        "class Model { state = { value: 0 }; }",
        "class Model { #state: { value: number } = { value: 0 }; }",
    ] {
        let parsed = parse_source_file(source);
        let context = context(&parsed);
        let field = source_field(&context, &parsed, "Model");
        let host = context.declared_type_host().unwrap();
        let before = format!("{:?}", context.store());
        for _ in 0..2 {
            assert_eq!(
                plan_source_class_members(context.store(), &host, field.owner),
                Err(ClassError::Unsupported(
                    ClassUnsupported::PropertyInitializer(field.declaration)
                )),
            );
            assert_eq!(format!("{:?}", context.store()), before);
        }
    }
}
