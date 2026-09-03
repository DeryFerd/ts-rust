use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeError, IntrinsicBootstrapOptions,
    SourceCheckError, TypeData, TypeId, TypeNodeUnavailable, types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const DECLARATIONS: &str = include_str!("fixtures/merged_class_interface_members/runtime.d.ts");
const POSITIVE: &str = include_str!("fixtures/merged_class_interface_members/positive.ts");
const NEGATIVE: &str = include_str!("fixtures/merged_class_interface_members/negative.ts");

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &[ParseResult],
    types: &[TypeId],
    members: &[SemanticSymbolId],
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        parsed
            .iter()
            .enumerate()
            .flat_map(|(file, parsed)| {
                parsed.arena.iter().map(move |(id, _)| {
                    let node = NodeRef::new(parsed.arena.id(), FileId::new(file as u32), id);
                    (
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect::<Vec<_>>(),
        store.relation_state_snapshot(),
        checker.diagnostics().clone(),
        types
            .iter()
            .map(|type_| format!("{:?}", store.type_payload(*type_)))
            .collect::<Vec<_>>(),
        members
            .iter()
            .map(|member| {
                (
                    store.symbol(*member).cloned(),
                    store.value_symbol_links(*member).cloned(),
                )
            })
            .collect::<Vec<_>>(),
    )
}

fn check(source: &str, negative: bool) {
    for query_first in [false, true] {
        check_once(source, negative, query_first);
    }
}

fn check_once(source: &str, negative: bool, query_first: bool) {
    let inputs = [
        (
            "/lib.es5.d.ts",
            include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
        ),
        (
            "/lib.decorators.d.ts",
            include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
        ),
        (
            "/lib.decorators.legacy.d.ts",
            include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
        ),
        ("/runtime.d.ts", DECLARATIONS),
        ("/consumer.ts", source),
    ];
    let parsed = inputs
        .iter()
        .map(|(_, source)| parse_source_file(source))
        .collect::<Vec<_>>();
    let mut binder = CanonicalBinder::new();
    for (file, ((path, _), parsed)) in inputs.iter().zip(&parsed).enumerate() {
        assert!(
            parsed.diagnostics.is_empty(),
            "{path}: {:?}",
            parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                FileId::new(file as u32),
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file != 4,
                    file < 3,
                    if file == 4 {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                ),
            )
            .unwrap();
    }
    for (file, parsed) in parsed.iter().enumerate() {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, FileId::new(file as u32))
            .unwrap();
    }
    let mut checker = CanonicalCheckerContext::new(
        binder.finish(),
        parsed
            .iter()
            .enumerate()
            .map(|(file, parsed)| (FileId::new(file as u32), &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();
    let consumer = FileId::new(4);
    if query_first {
        let property =
            parsed[4]
                .arena
                .iter()
                .find_map(|(id, node)| {
                    matches!(node.data, NodeData::PropertyAccessExpression(_))
                        .then_some(NodeRef::new(parsed[4].arena.id(), consumer, id))
                })
                .unwrap();
        checker.get_type_at_location(property).unwrap();
    }
    checker.check_source_file(consumer).unwrap_or_else(|error| {
        if let SourceCheckError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(
            TypeNodeUnavailable::UnsupportedSyntax { node, .. },
        )) = &error
        {
            let file = node.file.index();
            let range = parsed[file].arena.get(node.node).unwrap().range;
            panic!(
                "{error:?}, source {:?} at {:?}",
                &inputs[file].1[range.start.get() as usize..range.end.get() as usize],
                range
            );
        }
        panic!("{error:?}");
    });

    if negative {
        let [error] = checker.diagnostics().as_slice() else {
            panic!("one assignment error: {:?}", checker.diagnostics());
        };
        assert_eq!(error.diagnostic.code(), 2322);
        assert_eq!(
            error.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        let node = error.node.unwrap();
        assert_eq!(node.file, consumer);
        let range = parsed[4].arena.get(node.node).unwrap().range;
        assert_eq!(range.start.get() as usize, source.find("wrong").unwrap());
        assert_eq!(range.end.get() - range.start.get(), 5);
        assert!(error.range_override.is_none());
        assert!(error.related_information.is_empty());
    } else {
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let mut scalar_reads = Vec::new();
        let mut calls = 0;
        for (id, node) in parsed[4].arena.iter() {
            if matches!(node.data, NodeData::CallExpression(_)) {
                let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
                assert_eq!(
                    checker.get_type_at_location(NodeRef::new(parsed[4].arena.id(), consumer, id)),
                    Ok(number)
                );
                calls += 1;
            }
            let NodeData::PropertyAccessExpression(access) = &node.data else {
                continue;
            };
            let NodeData::Identifier(name) = &parsed[4].arena.get(access.name).unwrap().data else {
                continue;
            };
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let expected = match name.text.as_str() {
                "label" => bootstrap.string_type,
                "inherited" | "ownClass" => bootstrap.number_type,
                _ => continue,
            };
            scalar_reads.push(name.text.as_str());
            assert_eq!(
                checker.get_type_at_location(NodeRef::new(parsed[4].arena.id(), consumer, id)),
                Ok(expected)
            );
        }
        scalar_reads.sort();
        assert_eq!(scalar_reads, ["inherited", "label", "ownClass"]);
        assert_eq!(calls, 1);
    }

    let named_owner = |name: &str| {
        let declaration = parsed[3]
            .arena
            .iter()
            .find_map(|(id, node)| {
                let NodeData::InterfaceDeclaration(interface) = &node.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed[3].arena.get(interface.name)?.data
                else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(
                    parsed[3].arena.id(),
                    FileId::new(3),
                    id,
                ))
            })
            .unwrap();
        let raw = checker
            .file(declaration.file)
            .unwrap()
            .1
            .symbol(declaration)
            .unwrap();
        checker.store().get_merged_symbol(raw).unwrap()
    };
    let process = named_owner("Process");
    let emitter = named_owner("Emitter");
    let events = named_owner("Events");
    let declared = |owner| {
        checker
            .store()
            .declared_type_links(owner)
            .unwrap()
            .declared_type
            .unwrap()
    };
    let process_type = declared(process);
    let emitter_type = declared(emitter);
    let events_type = declared(events);
    let record = checker.store().type_payload(process_type).unwrap();
    let TypeData::Interface(process_data) = record.data() else {
        panic!("Process must retain its interface identity");
    };
    let [base] = process_data.resolved_base_types.as_deref().unwrap() else {
        panic!("Process must have its one written base");
    };
    let base = *base;
    let TypeData::TypeReference(reference) = checker.store().type_payload(base).unwrap().data()
    else {
        panic!("the omitted argument must create an Emitter<number> reference");
    };
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(reference.object.target, Some(emitter_type));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some([number].as_slice())
    );
    let emitter_record = checker.store().type_payload(emitter_type).unwrap();
    assert!(emitter_record.object_flags().contains(ObjectFlags::CLASS));
    assert_eq!(emitter_record.symbol(), Some(emitter));
    let emitter_symbol = checker.store().symbol(emitter).unwrap();
    assert!(
        emitter_symbol
            .flags()
            .contains(SymbolFlags::CLASS | SymbolFlags::INTERFACE)
    );
    assert_eq!(emitter_symbol.declarations().unwrap().len(), 2);

    let TypeData::Interface(emitter_data) = emitter_record.data() else {
        panic!("Emitter must retain its class target");
    };
    let [parameter] = emitter_data
        .reference
        .resolved_type_arguments
        .as_deref()
        .unwrap()
    else {
        panic!("the two declarations must share one canonical formal");
    };
    let TypeData::TypeParameter(parameter_data) =
        checker.store().type_payload(*parameter).unwrap().data()
    else {
        panic!("the target formal must remain a type parameter");
    };
    assert_eq!(parameter_data.resolved_default_type, Some(number));
    let [event_base] = emitter_data.resolved_base_types.as_deref().unwrap() else {
        panic!("the class identity must retain the interface's written base");
    };
    let TypeData::TypeReference(event_base) =
        checker.store().type_payload(*event_base).unwrap().data()
    else {
        panic!("Events<T> must remain a mapped base reference");
    };
    assert_eq!(event_base.object.target, Some(events_type));
    assert_eq!(
        event_base.resolved_type_arguments.as_deref(),
        Some([*parameter].as_slice())
    );

    let mut types = vec![process_type, base, emitter_type, events_type];
    for target in [emitter_type, events_type] {
        let TypeData::Interface(data) = checker.store().type_payload(target).unwrap().data() else {
            panic!("class and interface targets must keep their canonical formals");
        };
        types.extend(data.reference.resolved_type_arguments.as_deref().unwrap());
        if target == events_type {
            assert!(data.base_types_resolved);
            assert!(data.resolved_base_types.is_none());
        }
        if let Some(bases) = &data.resolved_base_types {
            types.extend(bases);
        }
        types.extend(data.this_type);
    }
    let members = process_data
        .reference
        .object
        .structured
        .properties
        .as_ref()
        .unwrap()
        .clone();
    if !negative {
        let read = parsed[4]
            .arena
            .iter()
            .find_map(|(id, node)| {
                let NodeData::PropertyAccessExpression(property) = &node.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed[4].arena.get(property.name)?.data else {
                    return None;
                };
                (name.text == "read").then_some(NodeRef::new(parsed[4].arena.id(), consumer, id))
            })
            .unwrap();
        let selected = checker.get_symbol_at_location(read).unwrap().unwrap();
        let original = checker
            .store()
            .symbol_table(checker.store().symbol(events).unwrap().members().unwrap())
            .unwrap()
            .get_source("read")
            .unwrap();
        let original = checker.store().get_merged_symbol(original).unwrap();
        let mut current = selected;
        let mut seen = Vec::new();
        while current != original {
            assert!(
                !seen.contains(&current),
                "method proxies must not form a cycle"
            );
            seen.push(current);
            let links = checker.store().value_symbol_links(current).unwrap();
            assert!(links.mapper.is_some());
            current = links
                .target
                .expect("the proxy must retain the actual source method");
        }
    }

    // Checking the consumer must not read an unused named method's signature.
    let unread = parsed[3]
        .arena
        .iter()
        .find_map(|(id, node)| {
            let NodeData::MethodSignatureDeclaration(method) = &node.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed[3].arena.get(method.name)?.data else {
                return None;
            };
            (name.text == "send").then_some(NodeRef::new(parsed[3].arena.id(), FileId::new(3), id))
        })
        .unwrap();
    assert!(checker.store().signature_links(unread).is_none());

    let warm = snapshot(&checker, &parsed, &types, &members);
    checker.recheck_source_file(consumer).unwrap();
    assert_eq!(snapshot(&checker, &parsed, &types, &members), warm);
    assert!(checker.store().type_resolution_is_empty());
}

#[test]
fn merged_class_interface_defaults_and_inherited_members_check_and_replay() {
    check(POSITIVE, false);
}

#[test]
fn merged_class_interface_inherited_member_reports_the_wrong_assignment() {
    check(NEGATIVE, true);
}
