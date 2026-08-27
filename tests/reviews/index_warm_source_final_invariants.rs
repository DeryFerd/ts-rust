#[test]
#[allow(clippy::too_many_lines)] // Keep each metadata pair, refusal, and restored source identity together.
fn review_index_warm_source_rejects_foreign_parameter_metadata() {
    use crate::semantic::links::{SymbolNodeLinks, TypeNodeLinks};

    let mut accepted = Vec::new();
    for poison in ["owner_declarations", "parameter_declarations"] {
        for warm in [false, true] {
            let mut fixture = fixture_with_source(
                "interface Base<T> { readonly [index: number]: T; } interface Other<T> {}",
                14_701,
            );
            let owner = interface_symbol(&fixture, "Base");
            let other_owner = interface_symbol(&fixture, "Other");
            let source_host = host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let mut parameters = Vec::new();
            for symbol in [owner, other_owner] {
                let flags = fixture.store.symbol(symbol).unwrap().flags();
                let target = get_declared_class_interface_or_type_parameter(
                    &mut fixture.store,
                    &source_host,
                    symbol,
                    flags,
                )
                .unwrap()
                .unwrap();
                let TypeData::Interface(interface) =
                    fixture.store.type_payload(target).unwrap().data()
                else {
                    panic!("the source retains a generic interface")
                };
                let arguments = interface
                    .reference
                    .resolved_type_arguments
                    .as_ref()
                    .unwrap();
                assert_eq!(arguments.len(), 1);
                parameters.push(arguments[0]);
            }
            let actual = parameters[0];
            let foreign = parameters[1];
            assert_ne!(actual, foreign);
            let actual_symbol =
                cached_ordinary_type_parameter_owner(&fixture.store, actual).unwrap();
            let foreign_symbol =
                cached_ordinary_type_parameter_owner(&fixture.store, foreign).unwrap();
            assert_ne!(actual_symbol, foreign_symbol);
            let owner_record = fixture.store.symbol(owner).unwrap();
            let owner_declarations = owner_record.declarations().unwrap().to_vec();
            let owner_value_declaration = owner_record.value_declaration();
            let other_declarations = fixture
                .store
                .symbol(other_owner)
                .unwrap()
                .declarations()
                .unwrap()
                .to_vec();
            let actual_declarations = fixture
                .store
                .symbol(actual_symbol)
                .unwrap()
                .declarations()
                .unwrap()
                .to_vec();
            let foreign_record = fixture.store.symbol(foreign_symbol).unwrap();
            let foreign_declarations = foreign_record.declarations().unwrap().to_vec();
            let foreign_value_declaration = foreign_record.value_declaration();
            let foreign_parent = foreign_record.parent();
            let foreign_members = foreign_record.members();
            let foreign_exports = foreign_record.exports();
            let foreign_export = foreign_record.export_symbol();
            assert_eq!(
                fixture.store.get_parent_of_symbol(foreign_symbol),
                Some(other_owner)
            );
            assert_eq!(actual_declarations.len(), 1);
            assert_eq!(foreign_declarations.len(), 1);
            let index_symbol = owner_record
                .members()
                .and_then(|members| fixture.store.symbol_table(members))
                .and_then(|members| members.get(InternalSymbolName::Index.as_ref()))
                .unwrap();
            let declaration = fixture
                .store
                .symbol(index_symbol)
                .unwrap()
                .declarations()
                .unwrap()[0];
            let NodeData::IndexSignatureDeclaration(index_source) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("the index retains its source declaration")
            };
            let annotation = NodeRef::new(declaration.arena, declaration.file, index_source.type_);
            let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
            let original = fixture
                .store
                .alloc_index_info(number, actual, true, Some(declaration), Vec::new())
                .unwrap();
            let wrong = fixture
                .store
                .alloc_index_info(number, foreign, true, Some(declaration), Vec::new())
                .unwrap();
            assert!(fixture.store.type_node_links(annotation).is_none());
            assert!(fixture.store.symbol_node_links(annotation).is_none());
            assert_eq!(
                fixture.store.source_node_parent(declaration),
                Some(SourceNodeParent::Parent(owner_declarations[0]))
            );
            assert_eq!(
                fixture
                    .files
                    .get(&fixture.file)
                    .unwrap()
                    .symbol(actual_declarations[0]),
                Some(actual_symbol)
            );

            let state = |store: &CanonicalTypeMapperStore| {
                (
                    (
                        store.type_len(),
                        store.mapper_len(),
                        store.symbol_len(),
                        store.signature_len(),
                        store.index_info_len(),
                    ),
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                    store.type_node_links(annotation).cloned(),
                    store.symbol_node_links(annotation).cloned(),
                    store
                        .symbol(owner)
                        .unwrap()
                        .declarations()
                        .unwrap()
                        .to_vec(),
                    (
                        store.symbol(foreign_symbol).unwrap().parent(),
                        store
                            .symbol(foreign_symbol)
                            .unwrap()
                            .declarations()
                            .unwrap()
                            .to_vec(),
                    ),
                    (
                        store.declared_type_links(actual_symbol).cloned(),
                        store.declared_type_links(foreign_symbol).cloned(),
                    ),
                )
            };
            let check = |store: &CanonicalTypeMapperStore, index, expected, label| {
                let before = state(store);
                for _ in 0..2 {
                    assert_eq!(
                        valid_index_symbol(
                            store,
                            owner,
                            &owner_declarations,
                            index_symbol,
                            &[index]
                        ),
                        expected,
                        "{poison}, warm={warm}, {label}"
                    );
                    assert_eq!(state(store), before);
                }
            };
            check(&fixture.store, original, true, "source value");
            if warm {
                assert!(fixture.store.set_type_node_links(
                    annotation,
                    TypeNodeLinks {
                        resolved_type: Some(actual),
                        outer_type_parameters: None,
                    }
                ));
                check(&fixture.store, original, true, "matching source cache");
                check(&fixture.store, wrong, false, "wrong value alone");
                assert!(fixture.store.set_type_node_links(
                    annotation,
                    TypeNodeLinks {
                        resolved_type: Some(foreign),
                        outer_type_parameters: None,
                    }
                ));
            }
            check(&fixture.store, wrong, false, "foreign source owner");

            assert!(fixture.store.set_symbol_relationships(
                foreign_symbol,
                foreign_members,
                foreign_exports,
                Some(owner),
                foreign_export
            ));
            check(&fixture.store, wrong, false, "parent change alone");
            assert!(fixture.store.set_symbol_relationships(
                foreign_symbol,
                foreign_members,
                foreign_exports,
                foreign_parent,
                foreign_export
            ));
            if poison == "owner_declarations" {
                let mut declared = owner_declarations.clone();
                declared.extend_from_slice(&other_declarations);
                assert!(fixture.store.set_symbol_declarations(
                    owner,
                    Some(declared),
                    owner_value_declaration
                ));
            } else {
                assert!(fixture.store.set_symbol_declarations(
                    foreign_symbol,
                    Some(actual_declarations.clone()),
                    foreign_value_declaration
                ));
            }
            check(&fixture.store, wrong, false, "declaration change alone");
            assert!(fixture.store.set_symbol_relationships(
                foreign_symbol,
                foreign_members,
                foreign_exports,
                Some(owner),
                foreign_export
            ));

            // The original binding and index source still identify Base's own T.
            assert_eq!(
                fixture
                    .files
                    .get(&fixture.file)
                    .unwrap()
                    .symbol(actual_declarations[0]),
                Some(actual_symbol)
            );
            assert_ne!(
                fixture
                    .files
                    .get(&fixture.file)
                    .unwrap()
                    .symbol(actual_declarations[0]),
                Some(foreign_symbol)
            );
            assert_eq!(
                fixture.store.source_node_parent(declaration),
                Some(SourceNodeParent::Parent(owner_declarations[0]))
            );
            for (links, symbol) in [("absent", None), ("matching_foreign", Some(foreign_symbol))] {
                if let Some(symbol) = symbol {
                    assert!(fixture.store.set_symbol_node_links(
                        annotation,
                        SymbolNodeLinks {
                            resolved_symbol: Some(symbol)
                        }
                    ));
                } else {
                    assert!(fixture.store.symbol_node_links(annotation).is_none());
                }
                let before = state(&fixture.store);
                for _ in 0..2 {
                    let valid = valid_index_symbol(
                        &fixture.store,
                        owner,
                        &owner_declarations,
                        index_symbol,
                        &[wrong],
                    );
                    accepted.push((poison, warm, links, valid));
                    assert_eq!(state(&fixture.store), before);
                }
            }
            assert!(fixture.store.set_symbol_node_links(
                annotation,
                SymbolNodeLinks {
                    resolved_symbol: Some(actual_symbol)
                }
            ));
            check(
                &fixture.store,
                wrong,
                false,
                "actual source symbol disagrees",
            );

            assert!(fixture.store.set_symbol_relationships(
                foreign_symbol,
                foreign_members,
                foreign_exports,
                foreign_parent,
                foreign_export
            ));
            assert!(fixture.store.set_symbol_declarations(
                owner,
                Some(owner_declarations.clone()),
                owner_value_declaration
            ));
            assert!(fixture.store.set_symbol_declarations(
                foreign_symbol,
                Some(foreign_declarations),
                foreign_value_declaration
            ));
            assert!(
                fixture
                    .store
                    .set_symbol_node_links(annotation, SymbolNodeLinks::default())
            );
            if warm {
                assert!(fixture.store.set_type_node_links(
                    annotation,
                    TypeNodeLinks {
                        resolved_type: Some(actual),
                        outer_type_parameters: None,
                    }
                ));
            } else {
                assert!(fixture.store.type_node_links(annotation).is_none());
            }
            check(&fixture.store, original, true, "restored source identity");
            assert_eq!(
                fixture.store.index_info(original).unwrap().value_type(),
                actual
            );
            assert_eq!(
                fixture
                    .store
                    .declared_type_links(actual_symbol)
                    .unwrap()
                    .declared_type,
                Some(actual)
            );
        }
    }
    assert!(
        accepted.iter().all(|(_, _, _, accepted)| !accepted),
        "foreign canonical parameters replaced the actual index source: {accepted:?}"
    );
}
