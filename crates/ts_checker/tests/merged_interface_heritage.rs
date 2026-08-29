use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, type_records::InterfaceTypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const ES5_FILE: FileId = FileId::new(99_010);
const LIBRARY_FILE: FileId = FileId::new(99_011);
const ADDED_FILE: FileId = FileId::new(99_012);
const CONSUMER_FILE: FileId = FileId::new(99_013);
const MODES: [(bool, bool); 3] = [(false, false), (true, false), (true, true)];
const SECOND_BASE_VALUE: &str =
    "declare var SecondBase: { prototype: SecondBase; new(): SecondBase; }; ";
const NEUTRAL_LIBRARY: &str = concat!(
    "interface Array<T> {} interface ReadonlyArray<T> {} ",
    "interface TargetRecord { readonly marker: number; } ",
    "declare var TargetRecord: { prototype: TargetRecord; new(): TargetRecord; }; ",
    "interface FirstBase { inherited: number; target: TargetRecord | null; ",
    "path(): TargetRecord[]; init(label: string, first?: boolean, second?: boolean): void; } ",
    "declare var FirstBase: { prototype: FirstBase; new(): FirstBase; }; ",
    "interface SecondBase { other: string; } ",
    "declare var SecondBase: { prototype: SecondBase; new(): SecondBase; }; ",
    "interface RootPacket extends FirstBase { own: string; } ",
    "declare var RootPacket: { prototype: RootPacket; new(): RootPacket; };",
);

type Input<'a> = (FileId, &'a ParseResult, &'static str, bool, bool);

fn context<'a>(
    files: &[Input<'a>],
    strict_null_checks: bool,
    exact_optional_property_types: bool,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, declaration, library) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, ..)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks,
                exact_optional_property_types,
            },
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn interface(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing interface {expected}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn member(parsed: &ParseResult, owner: NodeRef, expected: &str) -> (NodeRef, NodeRef) {
    let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(owner.node).unwrap().data
    else {
        panic!("member lookup needs its original interface declaration")
    };
    interface
        .members
        .nodes
        .iter()
        .find_map(|node| {
            let name = match &parsed.arena.get(*node)?.data {
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::PropertySignatureDeclaration(property) => property.name,
                NodeData::MethodSignatureDeclaration(method) => method.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some((
                NodeRef::new(owner.arena, owner.file, *node),
                NodeRef::new(owner.arena, owner.file, name),
            ))
        })
        .unwrap_or_else(|| panic!("missing member {expected}"))
}

fn interface_data<'a>(
    checker: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a InterfaceTypeData {
    let TypeData::Interface(data) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("the original interface identity must be retained")
    };
    data
}

fn resolved_member(
    checker: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    name: &str,
) -> SemanticSymbolId {
    let members = interface_data(checker, type_)
        .reference
        .object
        .structured
        .members
        .unwrap();
    checker
        .store()
        .symbol_table(members)
        .unwrap()
        .get_source(name)
        .unwrap()
}

fn assert_value_annotation_cold(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    expected: &str,
) {
    let (declaration, annotation) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, variable.type_.unwrap()),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing separate value declaration {expected}"));
    let owner = symbol(checker, declaration);
    assert_eq!(
        checker.store().symbol(owner).unwrap().value_declaration(),
        Some(declaration),
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(owner)
            .and_then(|links| links.resolved_type),
        None,
    );
    assert_eq!(
        checker
            .store()
            .type_node_links(annotation)
            .and_then(|links| links.resolved_type),
        None,
    );
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = checker.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn method_signature(
    checker: &mut CanonicalCheckerContext<'_>,
    name: NodeRef,
) -> (TypeId, SignatureId) {
    let callable = checker.get_type_at_location(name).unwrap();
    let TypeData::Object(object) = checker.store().type_payload(callable).unwrap().data() else {
        panic!("the selected method must retain its callable object")
    };
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("the selected method has one original signature")
    };
    (callable, *signature)
}

fn assert_nullable_target(checker: &CanonicalCheckerContext<'_>, type_: TypeId, target: TypeId) {
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    if bootstrap.options.strict_null_checks {
        let TypeData::Union(union) = checker.store().type_payload(type_).unwrap().data() else {
            panic!("the written nullable target must retain its union")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&target));
        assert!(union.union.types.contains(&bootstrap.null_type));
    } else {
        assert_eq!(type_, target);
    }
}

fn assert_array_target(checker: &CanonicalCheckerContext<'_>, array: TypeId, target: TypeId) {
    let TypeData::TypeReference(reference) = checker.store().type_payload(array).unwrap().data()
    else {
        panic!("the method return must retain its canonical Array reference")
    };
    assert_eq!(
        reference.object.target,
        Some(checker.global_types().array_type),
    );
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some([target].as_slice()),
    );
}

fn assert_optional_boolean_parameters(
    checker: &CanonicalCheckerContext<'_>,
    signature: SignatureId,
) {
    let store = checker.store();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    let record = store.signature(signature).unwrap();
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.parameters().len(), 3);
    assert!(!record.has_rest_parameter());
    assert_eq!(
        store
            .value_symbol_links(record.parameters()[0])
            .unwrap()
            .resolved_type,
        Some(bootstrap.string_type),
    );
    for parameter in &record.parameters()[1..] {
        let type_ = store
            .value_symbol_links(*parameter)
            .unwrap()
            .resolved_type
            .unwrap();
        if bootstrap.options.strict_null_checks {
            let TypeData::Union(union) = store.type_payload(type_).unwrap().data() else {
                panic!("an optional method parameter must include undefined")
            };
            let TypeData::Union(boolean) =
                store.type_payload(bootstrap.boolean_type).unwrap().data()
            else {
                panic!("the canonical boolean contains its two literal types")
            };
            assert_eq!(union.union.types.len(), boolean.union.types.len() + 1);
            assert!(
                boolean
                    .union
                    .types
                    .iter()
                    .all(|type_| union.union.types.contains(type_))
            );
            assert!(union.union.types.contains(&bootstrap.undefined_type));
            assert!(!union.union.types.contains(&bootstrap.missing_type));
        } else {
            assert_eq!(type_, bootstrap.boolean_type);
        }
    }
}

fn assert_target_members_cold(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    declaration: NodeRef,
    target: TypeId,
) {
    assert!(!interface_data(checker, target).declared_members_resolved);
    for name in ["addEventListener", "dispatchEvent", "removeEventListener"] {
        let owner = symbol(checker, member(parsed, declaration, name).0);
        assert!(checker.store().value_symbol_links(owner).is_none());
    }
}

fn heritage_identifier(parsed: &ParseResult, owner: NodeRef) -> NodeRef {
    let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(owner.node).unwrap().data
    else {
        panic!("the heritage clause must belong to its source interface")
    };
    let [clause] = interface
        .heritage_clauses
        .as_ref()
        .unwrap()
        .nodes
        .as_slice()
    else {
        panic!("each source declaration has one heritage clause")
    };
    let clause_id = *clause;
    let clause = parsed.arena.get(clause_id).unwrap();
    assert_eq!(clause.parent, Some(owner.node));
    let NodeData::HeritageClause(heritage) = &clause.data else {
        unreachable!()
    };
    let [base] = heritage.types.nodes.as_slice() else {
        panic!("each source declaration has one base entry")
    };
    let base_id = *base;
    let base = parsed.arena.get(base_id).unwrap();
    assert_eq!(base.parent, Some(clause_id));
    let NodeData::ExpressionWithTypeArguments(base) = &base.data else {
        unreachable!()
    };
    assert_eq!(
        parsed.arena.get(base.expression).unwrap().parent,
        Some(base_id),
    );
    NodeRef::new(owner.arena, owner.file, base.expression)
}

fn property_access(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
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
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing property read {expected}"))
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the original DOM declarations and both query orders together.
fn bundled_animation_event_merge_keeps_repeated_bases_and_lazy_target_identity() {
    let es5 = parse_source_file(include_str!("../../ts_bundled/libs/lib.es5.d.ts"));
    let dom = parse_source_file(include_str!("../../ts_bundled/libs/lib.dom.d.ts"));
    let added = parse_source_file(concat!(
        "interface Event {} interface AnimationEvent extends Event {} ",
        "interface EventTarget {}",
    ));
    let event_declaration = interface(&dom, LIBRARY_FILE, "Event");
    let animation_declaration = interface(&dom, LIBRARY_FILE, "AnimationEvent");
    let target_declaration = interface(&dom, LIBRARY_FILE, "EventTarget");
    for (strict, exact) in MODES {
        for query_first in [false, true] {
            let mut checker = context(
                &[
                    (ES5_FILE, &es5, "\"/lib/lib.es5.d.ts\"", true, true),
                    (LIBRARY_FILE, &dom, "\"/lib/lib.dom.d.ts\"", true, true),
                    (
                        ADDED_FILE,
                        &added,
                        "\"/project/react-global.d.ts\"",
                        true,
                        false,
                    ),
                ],
                strict,
                exact,
            );
            let event = symbol(&checker, event_declaration);
            let animation = symbol(&checker, animation_declaration);
            let target = symbol(&checker, target_declaration);
            assert_eq!(
                symbol(&checker, interface(&added, ADDED_FILE, "Event")),
                event
            );
            assert_eq!(
                symbol(&checker, interface(&added, ADDED_FILE, "AnimationEvent")),
                animation,
            );
            assert_eq!(
                symbol(&checker, interface(&added, ADDED_FILE, "EventTarget")),
                target,
            );
            let early = query_first.then(|| {
                [
                    checker.get_declared_type_of_symbol(event).unwrap(),
                    checker.get_declared_type_of_symbol(animation).unwrap(),
                ]
            });
            for name in ["Event", "AnimationEvent", "EventTarget"] {
                assert_value_annotation_cold(&checker, &dom, LIBRARY_FILE, name);
            }
            checker.check_source_file(ADDED_FILE).unwrap();
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let event_type = checker.get_declared_type_of_symbol(event).unwrap();
            let animation_type = checker.get_declared_type_of_symbol(animation).unwrap();
            if let Some(early) = early {
                assert_eq!(early, [event_type, animation_type]);
            }
            assert_eq!(
                interface_data(&checker, animation_type)
                    .resolved_base_types
                    .as_deref(),
                Some([event_type, event_type].as_slice()),
            );
            let base_nodes = [
                heritage_identifier(&dom, animation_declaration),
                heritage_identifier(&added, interface(&added, ADDED_FILE, "AnimationEvent")),
            ];
            assert_ne!(base_nodes[0], base_nodes[1]);
            for node in base_nodes {
                assert_eq!(checker.get_symbol_at_location(node).unwrap(), Some(event));
                assert_eq!(checker.get_type_at_location(node).unwrap(), event_type);
            }
            let target_type = checker
                .store()
                .declared_type_links(target)
                .unwrap()
                .declared_type
                .unwrap();
            assert_eq!(
                checker.store().type_payload(target_type).unwrap().symbol(),
                Some(target),
            );
            assert_target_members_cold(&checker, &dom, target_declaration, target_type);
            let query = |checker: &mut CanonicalCheckerContext<'_>| {
                let mut ids = Vec::new();
                for name in [
                    "type",
                    "target",
                    "currentTarget",
                    "srcElement",
                    "composedPath",
                    "initEvent",
                    "timeStamp",
                ] {
                    let (declaration, name_node) = member(&dom, event_declaration, name);
                    let owner = symbol(checker, declaration);
                    assert_eq!(resolved_member(checker, animation_type, name), owner);
                    assert_eq!(
                        checker.get_symbol_at_location(name_node).unwrap(),
                        Some(owner),
                    );
                    assert_eq!(
                        interface_data(checker, animation_type)
                            .reference
                            .object
                            .structured
                            .properties
                            .as_ref()
                            .unwrap()
                            .iter()
                            .filter(|symbol| **symbol == owner)
                            .count(),
                        1,
                    );
                    let published = checker
                        .store()
                        .value_symbol_links(owner)
                        .and_then(|links| links.resolved_type)
                        .expect("the resolved base member provider publishes its property type");
                    let queried = checker.get_type_at_location(name_node).unwrap();
                    assert_eq!(queried, published);
                    ids.push(queried);
                }
                assert_eq!(
                    ids[0],
                    checker.store().intrinsic_bootstrap().unwrap().string_type,
                );
                assert_eq!(
                    ids[6],
                    checker.store().intrinsic_bootstrap().unwrap().number_type,
                );
                for type_ in &ids[1..4] {
                    assert_nullable_target(checker, *type_, target_type);
                }
                let (_, path) =
                    method_signature(checker, member(&dom, event_declaration, "composedPath").1);
                let array = checker.get_return_type_of_signature(path).unwrap();
                assert_array_target(checker, array, target_type);
                ids.push(array);
                let (_, init) =
                    method_signature(checker, member(&dom, event_declaration, "initEvent").1);
                assert_optional_boolean_parameters(checker, init);
                assert_eq!(
                    checker.get_return_type_of_signature(init).unwrap(),
                    checker.store().intrinsic_bootstrap().unwrap().void_type,
                );
                ids
            };
            let ids = query(&mut checker);
            assert_target_members_cold(&checker, &dom, target_declaration, target_type);
            let snapshot = |checker: &CanonicalCheckerContext<'_>| {
                (
                    counts(checker),
                    [event_type, animation_type, target_type]
                        .map(|type_| interface_data(checker, type_).clone()),
                    checker.diagnostics().clone(),
                )
            };
            let warm = snapshot(&checker);
            for _ in 0..2 {
                checker.recheck_source_file(ADDED_FILE).unwrap();
                assert_eq!(
                    checker
                        .get_type_at_location(interface(&added, ADDED_FILE, "AnimationEvent"))
                        .unwrap(),
                    animation_type,
                );
                assert_eq!(query(&mut checker), ids);
                assert_target_members_cold(&checker, &dom, target_declaration, target_type);
                for name in ["Event", "AnimationEvent", "EventTarget"] {
                    assert_value_annotation_cold(&checker, &dom, LIBRARY_FILE, name);
                }
                assert_eq!(
                    snapshot(&checker),
                    warm,
                    "strict={strict}, exact={exact}, query_first={query_first}",
                );
            }
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep three real source contributions and their cold/warm identities together.
fn bundled_animation_event_three_contributions_keep_order_and_replay() {
    let es5 = parse_source_file(include_str!("../../ts_bundled/libs/lib.es5.d.ts"));
    let dom = parse_source_file(include_str!("../../ts_bundled/libs/lib.dom.d.ts"));
    let augmentation = concat!(
        "interface Event {} interface AnimationEvent extends Event {} ",
        "interface EventTarget {}",
    );
    let first = parse_source_file(augmentation);
    let second = parse_source_file(augmentation);
    let second_file = FileId::new(99_014);
    let contributions = [
        (&dom, LIBRARY_FILE),
        (&first, ADDED_FILE),
        (&second, second_file),
    ];
    let event_declaration = interface(&dom, LIBRARY_FILE, "Event");
    let animation_declaration = interface(&dom, LIBRARY_FILE, "AnimationEvent");
    let target_declaration = interface(&dom, LIBRARY_FILE, "EventTarget");
    let animation_declarations =
        contributions.map(|(parsed, file)| interface(parsed, file, "AnimationEvent"));
    let base_identifiers = contributions
        .into_iter()
        .zip(animation_declarations)
        .map(|((parsed, _), declaration)| heritage_identifier(parsed, declaration))
        .collect::<Vec<_>>();
    let base_nodes = contributions
        .into_iter()
        .zip(&base_identifiers)
        .map(|((parsed, file), identifier)| {
            NodeRef::new(
                parsed.arena.id(),
                file,
                parsed.arena.get(identifier.node).unwrap().parent.unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(base_nodes.len(), 3);
    for (index, node) in base_nodes.iter().enumerate() {
        assert_eq!(node.file, contributions[index].1);
        assert_eq!(
            contributions[index].0.arena.get(node.node).unwrap().kind,
            SyntaxKind::ExpressionWithTypeArguments,
        );
        assert!(base_nodes[..index].iter().all(|previous| previous != node));
    }

    for query_first in [false, true] {
        let mut checker = context(
            &[
                (ES5_FILE, &es5, "\"/lib/lib.es5.d.ts\"", true, true),
                (LIBRARY_FILE, &dom, "\"/lib/lib.dom.d.ts\"", true, true),
                (
                    ADDED_FILE,
                    &first,
                    "\"/project/react-first-global.d.ts\"",
                    true,
                    false,
                ),
                (
                    second_file,
                    &second,
                    "\"/project/react-second-global.d.ts\"",
                    true,
                    false,
                ),
            ],
            true,
            false,
        );
        let event = symbol(&checker, event_declaration);
        let animation = symbol(&checker, animation_declaration);
        let target = symbol(&checker, target_declaration);
        for (parsed, file) in contributions {
            assert_eq!(symbol(&checker, interface(parsed, file, "Event")), event);
            assert_eq!(
                symbol(&checker, interface(parsed, file, "AnimationEvent")),
                animation,
            );
            assert_eq!(
                symbol(&checker, interface(parsed, file, "EventTarget")),
                target
            );
        }
        let early = query_first.then(|| {
            [
                checker.get_declared_type_of_symbol(event).unwrap(),
                checker.get_declared_type_of_symbol(animation).unwrap(),
            ]
        });
        for name in ["Event", "AnimationEvent", "EventTarget"] {
            assert_value_annotation_cold(&checker, &dom, LIBRARY_FILE, name);
        }
        for file in [ADDED_FILE, second_file] {
            checker.check_source_file(file).unwrap();
        }
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let event_type = checker.get_declared_type_of_symbol(event).unwrap();
        let animation_type = checker.get_declared_type_of_symbol(animation).unwrap();
        let target_type = checker
            .store()
            .declared_type_links(target)
            .unwrap()
            .declared_type
            .unwrap();
        if let Some(early) = early {
            assert_eq!(early, [event_type, animation_type]);
        }
        for (type_, owner) in [
            (event_type, event),
            (animation_type, animation),
            (target_type, target),
        ] {
            assert_eq!(
                checker.store().type_payload(type_).unwrap().symbol(),
                Some(owner)
            );
        }
        assert_eq!(
            interface_data(&checker, animation_type)
                .resolved_base_types
                .as_deref(),
            Some([event_type, event_type, event_type].as_slice()),
        );
        assert_target_members_cold(&checker, &dom, target_declaration, target_type);

        let query = |checker: &mut CanonicalCheckerContext<'_>| {
            for node in &base_identifiers {
                assert_eq!(checker.get_symbol_at_location(*node).unwrap(), Some(event));
                assert_eq!(checker.get_type_at_location(*node).unwrap(), event_type);
            }
            let mut types = Vec::new();
            for (declaration, name) in [
                (animation_declaration, "animationName"),
                (event_declaration, "type"),
                (event_declaration, "target"),
                (event_declaration, "currentTarget"),
                (event_declaration, "srcElement"),
                (event_declaration, "composedPath"),
                (event_declaration, "initEvent"),
                (event_declaration, "timeStamp"),
            ] {
                let (member, name_node) = member(&dom, declaration, name);
                let owner = symbol(checker, member);
                assert_eq!(resolved_member(checker, animation_type, name), owner);
                assert_eq!(
                    checker.get_symbol_at_location(name_node).unwrap(),
                    Some(owner)
                );
                assert_eq!(
                    checker
                        .store()
                        .symbol(owner)
                        .unwrap()
                        .parent()
                        .and_then(|parent| checker.store().get_merged_symbol(parent)),
                    Some(if declaration == animation_declaration {
                        animation
                    } else {
                        event
                    }),
                );
                assert_eq!(
                    interface_data(checker, animation_type)
                        .reference
                        .object
                        .structured
                        .properties
                        .as_ref()
                        .unwrap()
                        .iter()
                        .filter(|property| **property == owner)
                        .count(),
                    1,
                );
                let published = checker
                    .store()
                    .value_symbol_links(owner)
                    .unwrap()
                    .resolved_type
                    .unwrap();
                assert_eq!(checker.get_type_at_location(name_node).unwrap(), published);
                types.push(published);
            }
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            assert_eq!(types[0], bootstrap.string_type);
            assert_eq!(types[1], bootstrap.string_type);
            assert_eq!(types[7], bootstrap.number_type);
            for type_ in &types[2..5] {
                assert_nullable_target(checker, *type_, target_type);
            }
            let (_, path) =
                method_signature(checker, member(&dom, event_declaration, "composedPath").1);
            let array = checker.get_return_type_of_signature(path).unwrap();
            assert_array_target(checker, array, target_type);
            types.push(array);
            let (_, init) =
                method_signature(checker, member(&dom, event_declaration, "initEvent").1);
            assert_optional_boolean_parameters(checker, init);
            assert_eq!(
                checker.get_return_type_of_signature(init).unwrap(),
                checker.store().intrinsic_bootstrap().unwrap().void_type
            );
            types
        };
        let types = query(&mut checker);
        let snapshot = |checker: &CanonicalCheckerContext<'_>| {
            (
                counts(checker),
                [event_type, animation_type, target_type]
                    .map(|type_| interface_data(checker, type_).clone()),
                base_identifiers
                    .iter()
                    .map(|node| {
                        (
                            checker.store().type_node_links(*node).cloned(),
                            checker.store().symbol_node_links(*node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                checker.diagnostics().clone(),
            )
        };
        let warm = snapshot(&checker);
        for _ in 0..2 {
            for file in [ADDED_FILE, second_file] {
                checker.recheck_source_file(file).unwrap();
            }
            for declaration in animation_declarations {
                assert_eq!(
                    checker.get_type_at_location(declaration).unwrap(),
                    animation_type
                );
            }
            assert_eq!(query(&mut checker), types);
            assert_target_members_cold(&checker, &dom, target_declaration, target_type);
            for name in ["Event", "AnimationEvent", "EventTarget"] {
                assert_value_annotation_cold(&checker, &dom, LIBRARY_FILE, name);
            }
            assert_eq!(snapshot(&checker), warm, "query_first={query_first}");
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Repeated and distinct source bases share the same member and replay checks.
fn neutral_merged_interface_heritage_preserves_base_order_and_separate_values() {
    for repeated in [false, true] {
        let library_source = if repeated {
            NEUTRAL_LIBRARY.to_owned()
        } else {
            NEUTRAL_LIBRARY.replace(SECOND_BASE_VALUE, "")
        };
        let library = parse_source_file(&library_source);
        let first_declaration = interface(&library, LIBRARY_FILE, "FirstBase");
        let second_declaration = interface(&library, LIBRARY_FILE, "SecondBase");
        let root_declaration = interface(&library, LIBRARY_FILE, "RootPacket");
        let target_declaration = interface(&library, LIBRARY_FILE, "TargetRecord");
        let value_names: &[&str] = if repeated {
            &["RootPacket", "FirstBase", "SecondBase", "TargetRecord"]
        } else {
            &["RootPacket", "FirstBase", "TargetRecord"]
        };
        let next_base = if repeated { "FirstBase" } else { "SecondBase" };
        let added = parse_source_file(&format!(
            "interface RootPacket extends {next_base} {{ added: boolean; }} interface TargetRecord {{}}"
        ));
        let consumer = parse_source_file(&format!(
            "declare const packet: RootPacket; \
             const own: string = packet.own; const added: boolean = packet.added; \
             const inherited: number = packet.inherited; const wrong: string = packet.inherited; {}",
            if repeated {
                ""
            } else {
                "const other: string = packet.other;"
            },
        ));
        for (strict, exact) in MODES {
            for query_first in [false, true] {
                let mut checker = context(
                    &[
                        (
                            LIBRARY_FILE,
                            &library,
                            "\"/lib/lib.heritage.d.ts\"",
                            true,
                            true,
                        ),
                        (ADDED_FILE, &added, "\"/project/added.d.ts\"", true, false),
                        (
                            CONSUMER_FILE,
                            &consumer,
                            "\"/project/consumer.ts\"",
                            false,
                            false,
                        ),
                    ],
                    strict,
                    exact,
                );
                let root = symbol(&checker, root_declaration);
                let first = symbol(&checker, first_declaration);
                let second = symbol(&checker, second_declaration);
                let target = symbol(&checker, target_declaration);
                let added_root = interface(&added, ADDED_FILE, "RootPacket");
                assert_eq!(symbol(&checker, added_root), root);
                let query = |checker: &mut CanonicalCheckerContext<'_>| {
                    let root_type = checker.get_declared_type_of_symbol(root).unwrap();
                    let mut values = vec![root_type];
                    for (name, declaration) in [
                        ("own", member(&library, root_declaration, "own").0),
                        ("added", member(&added, added_root, "added").0),
                        (
                            "inherited",
                            member(&library, first_declaration, "inherited").0,
                        ),
                    ] {
                        let access = property_access(&consumer, CONSUMER_FILE, name);
                        values.push(checker.get_type_at_location(access).unwrap());
                        let expected = symbol(checker, declaration);
                        assert_eq!(
                            checker.get_symbol_at_location(access).unwrap(),
                            Some(expected),
                        );
                        assert_eq!(resolved_member(checker, root_type, name), expected);
                    }
                    if !repeated {
                        let access = property_access(&consumer, CONSUMER_FILE, "other");
                        values.push(checker.get_type_at_location(access).unwrap());
                        let expected =
                            symbol(checker, member(&library, second_declaration, "other").0);
                        assert_eq!(
                            checker.get_symbol_at_location(access).unwrap(),
                            Some(expected),
                        );
                        assert_eq!(resolved_member(checker, root_type, "other"), expected);
                    }
                    values
                };
                let early = query_first.then(|| query(&mut checker));
                checker.check_source_file(ADDED_FILE).unwrap();
                let values = query(&mut checker);
                if let Some(early) = early {
                    assert_eq!(early, values);
                }
                checker.check_source_file(CONSUMER_FILE).unwrap();
                let [diagnostic] = checker.diagnostics().as_slice() else {
                    panic!("only the wrong inherited-property assignment must fail")
                };
                assert_eq!(diagnostic.diagnostic.code(), 2322);
                assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
                let root_type = values[0];
                let first_type = checker
                    .store()
                    .declared_type_links(first)
                    .unwrap()
                    .declared_type
                    .unwrap();
                let second_type = if repeated {
                    first_type
                } else {
                    checker
                        .store()
                        .declared_type_links(second)
                        .unwrap()
                        .declared_type
                        .unwrap()
                };
                assert_eq!(
                    interface_data(&checker, root_type)
                        .resolved_base_types
                        .as_deref(),
                    Some([first_type, second_type].as_slice()),
                );
                let mut expected = vec![
                    symbol(&checker, member(&library, root_declaration, "own").0),
                    symbol(&checker, member(&added, added_root, "added").0),
                ];
                for name in ["inherited", "target", "path", "init"] {
                    let member = symbol(&checker, member(&library, first_declaration, name).0);
                    assert_eq!(resolved_member(&checker, root_type, name), member);
                    expected.push(member);
                }
                if !repeated {
                    expected.push(symbol(
                        &checker,
                        member(&library, second_declaration, "other").0,
                    ));
                }
                assert_eq!(
                    interface_data(&checker, root_type)
                        .reference
                        .object
                        .structured
                        .properties
                        .as_deref(),
                    Some(expected.as_slice()),
                );
                let target_type = checker
                    .store()
                    .declared_type_links(target)
                    .unwrap()
                    .declared_type
                    .unwrap();
                let target_value = checker
                    .get_type_at_location(member(&library, first_declaration, "target").1)
                    .unwrap();
                let target_property = resolved_member(&checker, root_type, "target");
                assert_eq!(
                    checker
                        .store()
                        .value_symbol_links(target_property)
                        .and_then(|links| links.resolved_type),
                    Some(target_value),
                );
                assert_nullable_target(&checker, target_value, target_type);
                let (_, path) =
                    method_signature(&mut checker, member(&library, first_declaration, "path").1);
                let array = checker.get_return_type_of_signature(path).unwrap();
                assert_array_target(&checker, array, target_type);
                let (_, init) =
                    method_signature(&mut checker, member(&library, first_declaration, "init").1);
                assert_optional_boolean_parameters(&checker, init);
                assert_eq!(
                    checker.get_return_type_of_signature(init).unwrap(),
                    checker.store().intrinsic_bootstrap().unwrap().void_type,
                );
                for name in value_names {
                    assert_value_annotation_cold(&checker, &library, LIBRARY_FILE, name);
                }
                let snapshot = |checker: &CanonicalCheckerContext<'_>| {
                    (
                        counts(checker),
                        [root_type, first_type, second_type, target_type]
                            .map(|type_| interface_data(checker, type_).clone()),
                        checker.diagnostics().clone(),
                    )
                };
                let warm = snapshot(&checker);
                for _ in 0..2 {
                    checker.recheck_source_file(ADDED_FILE).unwrap();
                    checker.recheck_source_file(CONSUMER_FILE).unwrap();
                    assert_eq!(query(&mut checker), values);
                    assert_eq!(checker.get_return_type_of_signature(path).unwrap(), array);
                    assert_eq!(
                        checker
                            .get_type_at_location(member(&library, first_declaration, "target").1)
                            .unwrap(),
                        target_value,
                    );
                    assert_optional_boolean_parameters(&checker, init);
                    for name in value_names {
                        assert_value_annotation_cold(&checker, &library, LIBRARY_FILE, name);
                    }
                    assert_eq!(
                        snapshot(&checker),
                        warm,
                        "strict={strict}, exact={exact}, repeated={repeated}, query_first={query_first}",
                    );
                }
            }
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the original sources, intentional error, and separate value demand together.
fn distinct_secondary_global_base_keeps_value_and_instance_types_separate() {
    let library = parse_source_file(NEUTRAL_LIBRARY);
    let added = parse_source_file(
        "interface RootPacket extends SecondBase { added: boolean; } interface TargetRecord {}",
    );
    let consumer = parse_source_file(concat!(
        "declare const packet: RootPacket; ",
        "const own: string = packet.own; const added: boolean = packet.added; ",
        "const inherited: number = packet.inherited; const wrong: string = packet.inherited; ",
        "const other: string = packet.other;",
    ));
    let second_name = heritage_identifier(&added, interface(&added, ADDED_FILE, "RootPacket"));
    let second_node = NodeRef::new(
        second_name.arena,
        second_name.file,
        added.arena.get(second_name.node).unwrap().parent.unwrap(),
    );
    assert_eq!(
        added.arena.get(second_node.node).unwrap().kind,
        SyntaxKind::ExpressionWithTypeArguments,
    );
    let nodes = [
        (LIBRARY_FILE, &library),
        (ADDED_FILE, &added),
        (CONSUMER_FILE, &consumer),
    ]
    .into_iter()
    .flat_map(|(file, parsed)| {
        parsed
            .arena
            .iter()
            .map(move |(node, _)| NodeRef::new(parsed.arena.id(), file, node))
    })
    .collect::<Vec<_>>();
    let root_declaration = interface(&library, LIBRARY_FILE, "RootPacket");
    let first_declaration = interface(&library, LIBRARY_FILE, "FirstBase");
    let second_declaration = interface(&library, LIBRARY_FILE, "SecondBase");
    let target_declaration = interface(&library, LIBRARY_FILE, "TargetRecord");
    let added_root = interface(&added, ADDED_FILE, "RootPacket");
    let (value_declaration, value_name, value_annotation) = library
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &library.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == "SecondBase").then(|| {
                (
                    NodeRef::new(library.arena.id(), LIBRARY_FILE, node),
                    NodeRef::new(library.arena.id(), LIBRARY_FILE, variable.name),
                    NodeRef::new(library.arena.id(), LIBRARY_FILE, variable.type_.unwrap()),
                )
            })
        })
        .unwrap();
    let property_reads = consumer
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &consumer.arena.get(access.name)?.data else {
                return None;
            };
            Some((
                NodeRef::new(consumer.arena.id(), CONSUMER_FILE, node),
                name.text.as_str(),
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(property_reads.len(), 5);
    let wrong_range = consumer
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &consumer.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == "wrong").then_some(record.range)
        })
        .unwrap();
    for (strict, exact) in MODES {
        let mut checker = context(
            &[
                (
                    LIBRARY_FILE,
                    &library,
                    "\"/lib/lib.heritage.d.ts\"",
                    true,
                    true,
                ),
                (ADDED_FILE, &added, "\"/project/added.d.ts\"", true, false),
                (
                    CONSUMER_FILE,
                    &consumer,
                    "\"/project/consumer.ts\"",
                    false,
                    false,
                ),
            ],
            strict,
            exact,
        );
        let owners = nodes
            .iter()
            .filter_map(|node| checker.file(node.file).unwrap().1.symbol(*node))
            .map(|owner| checker.store().get_merged_symbol(owner).unwrap())
            .collect::<Vec<_>>();
        let snapshot = |checker: &CanonicalCheckerContext<'_>| {
            (
                counts(checker),
                checker.diagnostics().clone(),
                owners
                    .iter()
                    .map(|owner| {
                        (
                            checker.store().declared_type_links(*owner).cloned(),
                            checker.store().value_symbol_links(*owner).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                nodes
                    .iter()
                    .map(|node| {
                        (
                            checker.store().type_node_links(*node).cloned(),
                            checker.store().symbol_node_links(*node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
            )
        };
        let cold = snapshot(&checker);
        let source = checker.source_file(ADDED_FILE).unwrap();
        assert!(checker.store().source_file_links(source).is_none());
        for name in ["RootPacket", "FirstBase", "SecondBase", "TargetRecord"] {
            assert_value_annotation_cold(&checker, &library, LIBRARY_FILE, name);
        }
        assert_eq!(snapshot(&checker), cold);
        checker.check_source_file(ADDED_FILE).unwrap();
        checker.check_source_file(CONSUMER_FILE).unwrap();
        assert!(
            checker
                .store()
                .source_file_links(source)
                .unwrap()
                .type_checked
        );
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("only the original wrong inherited-property assignment must fail");
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        let diagnostic_node = diagnostic.node.unwrap();
        assert_eq!(diagnostic_node.file, CONSUMER_FILE);
        let diagnostic_range = consumer.arena.get(diagnostic_node.node).unwrap().range;
        assert!(diagnostic_range.start >= wrong_range.start);
        assert!(diagnostic_range.end <= wrong_range.end);
        let declarations = [
            root_declaration,
            first_declaration,
            second_declaration,
            target_declaration,
        ];
        let interface_owners = declarations.map(|declaration| symbol(&checker, declaration));
        let [root, first, second, _] = interface_owners;
        assert_eq!(symbol(&checker, added_root), root);
        assert_eq!(symbol(&checker, value_declaration), second);
        let types =
            interface_owners.map(|owner| checker.get_declared_type_of_symbol(owner).unwrap());
        let [root_type, first_type, second_type, _] = types;
        assert_eq!(
            interface_data(&checker, root_type)
                .resolved_base_types
                .as_deref(),
            Some([first_type, second_type].as_slice()),
        );
        assert_eq!(
            checker.get_symbol_at_location(second_name),
            Ok(Some(second))
        );
        assert_eq!(checker.get_type_at_location(second_name), Ok(second_type));
        let query = |checker: &mut CanonicalCheckerContext<'_>| {
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let (string, number, boolean) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            );
            let mut values = Vec::new();
            for &(access, name) in &property_reads {
                let (parsed, declaration, owner, expected_type) = match name {
                    "own" => (&library, root_declaration, root, string),
                    "added" => (&added, added_root, root, boolean),
                    "inherited" => (&library, first_declaration, first, number),
                    "other" => (&library, second_declaration, second, string),
                    _ => panic!("the unchanged consumer has only its original property reads"),
                };
                let expected = symbol(checker, member(parsed, declaration, name).0);
                assert_eq!(checker.store().get_parent_of_symbol(expected), Some(owner));
                assert_eq!(resolved_member(checker, root_type, name), expected);
                assert_eq!(checker.get_symbol_at_location(access), Ok(Some(expected)));
                assert_eq!(checker.get_type_at_location(access), Ok(expected_type));
                values.push(expected_type);
            }
            values
        };
        let values = query(&mut checker);
        let mut expected_members = vec![
            symbol(&checker, member(&library, root_declaration, "own").0),
            symbol(&checker, member(&added, added_root, "added").0),
        ];
        expected_members.extend(
            ["inherited", "target", "path", "init"]
                .map(|name| symbol(&checker, member(&library, first_declaration, name).0)),
        );
        expected_members.push(symbol(
            &checker,
            member(&library, second_declaration, "other").0,
        ));
        assert_eq!(
            interface_data(&checker, root_type)
                .reference
                .object
                .structured
                .properties
                .as_deref(),
            Some(expected_members.as_slice()),
        );
        for name in ["RootPacket", "FirstBase", "SecondBase", "TargetRecord"] {
            assert_value_annotation_cold(&checker, &library, LIBRARY_FILE, name);
        }
        let value_links = checker.store().value_symbol_links(second).cloned();
        let constructor = checker.get_type_at_location(value_name).unwrap();
        assert_ne!(constructor, second_type);
        assert!(matches!(
            checker.store().type_payload(constructor).unwrap().data(),
            TypeData::Object(_)
        ));
        assert_eq!(checker.get_symbol_at_location(value_name), Ok(Some(second)));
        // This artifact query resolves the annotation without publishing the variable's value cache.
        assert_eq!(
            checker.store().value_symbol_links(second).cloned(),
            value_links,
        );
        assert_eq!(
            checker
                .store()
                .type_node_links(value_annotation)
                .unwrap()
                .resolved_type,
            Some(constructor),
        );
        assert_eq!(
            checker.get_type_at_location(second_declaration),
            Ok(second_type)
        );
        let interface_state = types.map(|type_| interface_data(&checker, type_).clone());
        let warm = snapshot(&checker);
        for _ in 0..3 {
            checker.recheck_source_file(ADDED_FILE).unwrap();
            checker.recheck_source_file(CONSUMER_FILE).unwrap();
            assert_eq!(query(&mut checker), values);
            assert_eq!(checker.get_type_at_location(value_name), Ok(constructor));
            assert_eq!(
                checker.store().value_symbol_links(second).cloned(),
                value_links,
            );
            assert_eq!(checker.get_type_at_location(second_name), Ok(second_type));
            for ((owner, declaration), type_) in
                interface_owners.into_iter().zip(declarations).zip(types)
            {
                assert_eq!(checker.get_declared_type_of_symbol(owner), Ok(type_));
                assert_eq!(checker.get_type_at_location(declaration), Ok(type_));
            }
            assert_eq!(
                types.map(|type_| interface_data(&checker, type_).clone()),
                interface_state,
            );
            assert_eq!(snapshot(&checker), warm, "strict={strict}, exact={exact}");
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep real DOM owners, ordered bases, cold values, and both query orders together.
fn bundled_composition_event_keeps_secondary_global_bases_and_member_owners() {
    use std::collections::HashSet;

    let es5 = parse_source_file(include_str!("../../ts_bundled/libs/lib.es5.d.ts"));
    let dom = parse_source_file(include_str!("../../ts_bundled/libs/lib.dom.d.ts"));
    let augmentation = concat!(
        "interface Event {} ",
        "interface UIEvent extends Event {} ",
        "interface CompositionEvent extends Event {}",
    );
    let first = parse_source_file(augmentation);
    let second = parse_source_file(augmentation);
    let second_file = FileId::new(99_015);
    let contributions = [
        (&dom, LIBRARY_FILE),
        (&first, ADDED_FILE),
        (&second, second_file),
    ];
    let declarations = ["Event", "UIEvent", "CompositionEvent"]
        .map(|name| contributions.map(|(parsed, file)| interface(parsed, file, name)));
    let [event_declaration, ui_declaration, composition_declaration] =
        declarations.map(|declarations| declarations[0]);
    let target_declaration = interface(&dom, LIBRARY_FILE, "EventTarget");
    let ui_bases = contributions
        .into_iter()
        .zip(declarations[1])
        .map(|((parsed, _), declaration)| heritage_identifier(parsed, declaration))
        .collect::<Vec<_>>();
    let composition_bases = contributions
        .into_iter()
        .zip(declarations[2])
        .map(|((parsed, _), declaration)| heritage_identifier(parsed, declaration))
        .collect::<Vec<_>>();
    for nodes in [&ui_bases, &composition_bases] {
        assert_eq!(nodes.len(), 3);
        for (index, node) in nodes.iter().enumerate() {
            assert_eq!(node.file, contributions[index].1);
            assert!(nodes[..index].iter().all(|previous| previous != node));
        }
    }

    for query_first in [false, true] {
        let mut checker = context(
            &[
                (ES5_FILE, &es5, "\"/lib/lib.es5.d.ts\"", true, true),
                (LIBRARY_FILE, &dom, "\"/lib/lib.dom.d.ts\"", true, true),
                (
                    ADDED_FILE,
                    &first,
                    "\"/project/react-first-global.d.ts\"",
                    true,
                    false,
                ),
                (
                    second_file,
                    &second,
                    "\"/project/react-second-global.d.ts\"",
                    true,
                    false,
                ),
            ],
            true,
            false,
        );
        assert_eq!(
            checker.file_order(),
            [ES5_FILE, LIBRARY_FILE, ADDED_FILE, second_file],
        );
        let owners = declarations.map(|declarations| symbol(&checker, declarations[0]));
        let [event, ui, composition] = owners;
        assert_eq!(owners.into_iter().collect::<HashSet<_>>().len(), 3);
        for (owner, declarations) in owners.into_iter().zip(declarations) {
            let record = checker.store().symbol(owner).unwrap();
            assert!(record.flags().contains(
                ts_binder::SymbolFlags::INTERFACE
                    | ts_binder::SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    | ts_binder::SymbolFlags::TRANSIENT,
            ));
            assert_eq!(checker.store().get_merged_symbol(owner), Some(owner));
            let original_interfaces = record
                .declarations()
                .unwrap()
                .iter()
                .copied()
                .filter(|node| {
                    checker
                        .file(node.file)
                        .unwrap()
                        .0
                        .get(node.node)
                        .unwrap()
                        .kind
                        == SyntaxKind::InterfaceDeclaration
                })
                .collect::<Vec<_>>();
            assert_eq!(original_interfaces, declarations);
            for declaration in declarations {
                assert_eq!(symbol(&checker, declaration), owner);
            }
            assert!(checker.store().declared_type_links(owner).is_none());
        }
        let early = query_first.then(|| {
            owners.map(|owner| {
                let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
                let interface = interface_data(&checker, type_);
                assert!(!interface.base_types_resolved);
                assert!(!interface.declared_members_resolved);
                assert!(interface.resolved_base_types.is_none());
                assert!(interface.reference.object.structured.properties.is_none());
                type_
            })
        });
        for name in ["Event", "UIEvent", "CompositionEvent", "EventTarget"] {
            assert_value_annotation_cold(&checker, &dom, LIBRARY_FILE, name);
        }
        for file in [ADDED_FILE, second_file] {
            assert!(
                checker
                    .store()
                    .source_file_links(checker.source_file(file).unwrap())
                    .is_none_or(|links| !links.type_checked)
            );
            checker.check_source_file(file).unwrap();
            assert!(
                checker
                    .store()
                    .source_file_links(checker.source_file(file).unwrap())
                    .unwrap()
                    .type_checked
            );
        }
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let types = owners.map(|owner| checker.get_declared_type_of_symbol(owner).unwrap());
        let [event_type, ui_type, composition_type] = types;
        if let Some(early) = early {
            assert_eq!(early, types);
        }
        let target = symbol(&checker, target_declaration);
        let target_type = checker
            .store()
            .declared_type_links(target)
            .unwrap()
            .declared_type
            .unwrap();

        let query = |checker: &mut CanonicalCheckerContext<'_>| {
            for ((owner, declarations), type_) in owners.into_iter().zip(declarations).zip(types) {
                assert_eq!(
                    checker.store().type_payload(type_).unwrap().symbol(),
                    Some(owner)
                );
                for declaration in declarations {
                    assert_eq!(checker.get_type_at_location(declaration), Ok(type_));
                    assert_eq!(checker.get_symbol_at_location(declaration), Ok(Some(owner)));
                }
            }
            assert_eq!(
                interface_data(checker, composition_type)
                    .resolved_base_types
                    .as_deref(),
                Some([ui_type, event_type, event_type].as_slice()),
            );
            assert_eq!(
                interface_data(checker, ui_type)
                    .resolved_base_types
                    .as_deref(),
                Some([event_type, event_type, event_type].as_slice()),
            );
            for (nodes, expected) in [
                (&ui_bases, [(event, event_type); 3]),
                (
                    &composition_bases,
                    [(ui, ui_type), (event, event_type), (event, event_type)],
                ),
            ] {
                for (&node, (owner, type_)) in nodes.iter().zip(expected) {
                    assert_eq!(checker.get_symbol_at_location(node), Ok(Some(owner)));
                    assert_eq!(checker.get_type_at_location(node), Ok(type_));
                }
            }
            for (declaration, derived, base) in [
                (ui_declaration, ui_type, event_type),
                (composition_declaration, composition_type, ui_type),
            ] {
                let NodeData::InterfaceDeclaration(interface) =
                    &dom.arena.get(declaration.node).unwrap().data
                else {
                    unreachable!();
                };
                let mut expected = interface
                    .members
                    .nodes
                    .iter()
                    .map(|node| {
                        symbol(
                            checker,
                            NodeRef::new(declaration.arena, declaration.file, *node),
                        )
                    })
                    .collect::<Vec<_>>();
                expected.extend_from_slice(
                    interface_data(checker, base)
                        .reference
                        .object
                        .structured
                        .properties
                        .as_deref()
                        .unwrap(),
                );
                let structured = &interface_data(checker, derived).reference.object.structured;
                assert_eq!(structured.properties.as_deref(), Some(expected.as_slice()));
                assert_eq!(
                    expected.iter().copied().collect::<HashSet<_>>().len(),
                    expected.len()
                );
                let table = checker
                    .store()
                    .symbol_table(structured.members.unwrap())
                    .unwrap();
                assert_eq!(table.len(), expected.len());
                for property in expected {
                    assert_eq!(
                        table.get(checker.store().symbol(property).unwrap().name()),
                        Some(property)
                    );
                }
            }
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let (string, number) = (bootstrap.string_type, bootstrap.number_type);
            let mut member_types = Vec::new();
            for (declaration, owner, name, expected_type) in [
                (composition_declaration, composition, "data", string),
                (ui_declaration, ui, "detail", number),
                (event_declaration, event, "type", string),
            ] {
                let (member, name_node) = member(&dom, declaration, name);
                let property = symbol(checker, member);
                let original_owner = checker
                    .file(LIBRARY_FILE)
                    .unwrap()
                    .1
                    .symbol(declaration)
                    .unwrap();
                let record = checker.store().symbol(property).unwrap();
                assert_eq!(record.parent(), Some(original_owner));
                assert_eq!(record.declarations(), Some([member].as_slice()));
                assert_eq!(checker.store().get_parent_of_symbol(property), Some(owner));
                assert_eq!(resolved_member(checker, composition_type, name), property);
                assert_eq!(
                    checker.get_symbol_at_location(name_node),
                    Ok(Some(property))
                );
                assert_eq!(checker.get_type_at_location(name_node), Ok(expected_type));
                assert_eq!(
                    checker
                        .store()
                        .value_symbol_links(property)
                        .unwrap()
                        .resolved_type,
                    Some(expected_type)
                );
                member_types.push(expected_type);
            }
            assert_target_members_cold(checker, &dom, target_declaration, target_type);
            for name in ["Event", "UIEvent", "CompositionEvent", "EventTarget"] {
                assert_value_annotation_cold(checker, &dom, LIBRARY_FILE, name);
            }
            for file in [ES5_FILE, LIBRARY_FILE] {
                assert!(
                    checker
                        .store()
                        .source_file_links(checker.source_file(file).unwrap())
                        .is_none_or(|links| !links.type_checked)
                );
            }
            member_types
        };
        let member_types = query(&mut checker);
        let snapshot = |checker: &CanonicalCheckerContext<'_>| {
            (
                counts(checker),
                [event_type, ui_type, composition_type, target_type]
                    .map(|type_| interface_data(checker, type_).clone()),
                interface_data(checker, composition_type)
                    .reference
                    .object
                    .structured
                    .properties
                    .as_ref()
                    .unwrap()
                    .iter()
                    .map(|property| checker.store().value_symbol_links(*property).cloned())
                    .collect::<Vec<_>>(),
                ui_bases
                    .iter()
                    .chain(&composition_bases)
                    .map(|node| {
                        (
                            checker.store().type_node_links(*node).cloned(),
                            checker.store().symbol_node_links(*node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                checker.diagnostics().clone(),
            )
        };
        let warm = snapshot(&checker);
        for _ in 0..2 {
            for file in [ADDED_FILE, second_file] {
                checker.recheck_source_file(file).unwrap();
            }
            assert_eq!(query(&mut checker), member_types);
            assert!(checker.diagnostics().is_empty());
            assert_eq!(snapshot(&checker), warm, "query_first={query_first}");
        }
    }
}
