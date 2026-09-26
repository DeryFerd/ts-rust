mod type_only_class_imports {
    use super::*;
    use crate::semantic::SourceFileRef;

    const PROVIDER: &str = "export class Base {\n\
        value = 1;\n\
        constructor() {}\n\
        read() { return this.value; }\n\
        }";
    const CONSUMERS: [&str; 2] = [
        "import type { Base as ImportedBase } from './base'; const invalid = ImportedBase;",
        "import { type Base as ImportedBase } from './base'; const invalid = ImportedBase;",
    ];

    fn class_declaration(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(class.name?)?.data else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap()
    }

    fn class_symbols(
        store: &CanonicalTypeMapperStore,
        bound: &BoundFile,
        declaration: NodeRef,
        name: &str,
    ) -> (SemanticSymbolId, SemanticSymbolId) {
        let owner = bound.symbol(declaration).unwrap();
        let local = bound.local_symbol(declaration).unwrap();
        let module = bound.symbol(bound.source_file()).unwrap();
        let owner_record = store.symbol(owner).unwrap();
        assert_eq!(store.get_merged_symbol(owner), Some(owner));
        assert_eq!(owner_record.flags(), SymbolFlags::CLASS);
        assert_eq!(owner_record.check_flags(), CheckFlags::NONE);
        assert_eq!(owner_record.declarations(), Some(&[declaration][..]));
        assert_eq!(owner_record.value_declaration(), Some(declaration));
        assert_eq!(owner_record.parent(), Some(module));
        assert_eq!(owner_record.export_symbol(), None);
        assert_eq!(
            store
                .symbol_table(store.symbol(module).unwrap().exports().unwrap())
                .unwrap()
                .get_source(name),
            Some(owner)
        );
        let local_record = store.symbol(local).unwrap();
        assert_ne!(owner, local);
        assert_eq!(store.get_merged_symbol(local), Some(local));
        assert_eq!(local_record.flags(), SymbolFlags::EXPORT_VALUE);
        assert_eq!(local_record.check_flags(), CheckFlags::NONE);
        assert_eq!(local_record.declarations(), Some(&[declaration][..]));
        assert_eq!(local_record.value_declaration(), None);
        assert_eq!(local_record.members(), None);
        assert_eq!(local_record.exports(), None);
        assert_eq!(local_record.parent(), None);
        assert_eq!(local_record.export_symbol(), Some(owner));
        assert_eq!(
            store
                .symbol_table(bound.locals(bound.source_file()).unwrap())
                .unwrap()
                .get_source(name),
            Some(local)
        );
        (owner, local)
    }

    fn import_binding(
        context: &CanonicalCheckerContext<'_>,
        file: FileId,
        parsed: &ParseResult,
    ) -> SourceImportBindingPlan {
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ImportDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let plan = plan_top_level_named_type_import(
            &parsed.arena,
            context.file(file).unwrap().1,
            context.store(),
            declaration,
        )
        .unwrap();
        assert_eq!(plan.bindings.len(), 1);
        plan.bindings[0].clone()
    }

    fn value_read(parsed: &ParseResult, file: FileId) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::Identifier(identifier) = &record.data else {
                    return None;
                };
                let parent = parsed.arena.get(record.parent?)?;
                (identifier.text == "ImportedBase"
                    && matches!(&parent.data, NodeData::VariableDeclaration(variable)
                        if variable.initializer == Some(node)))
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap()
    }

    // Module export-resolution links can warm without checking the provider's body.
    fn source_cache_state(
        store: &CanonicalTypeMapperStore,
        file: FileId,
        parsed: &ParseResult,
    ) -> String {
        let nodes = parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = NodeRef::new(parsed.arena.id(), file, node);
                (
                    node,
                    store.node_links(node),
                    store.type_node_links(node),
                    store.symbol_node_links(node),
                    store.signature_links(node),
                )
            })
            .collect::<Vec<_>>();
        let symbols = store
            .symbol_store()
            .symbols()
            .filter_map(|(symbol, record)| {
                record
                    .declarations()
                    .is_some_and(|declarations| declarations.iter().any(|node| node.file == file))
                    .then_some(symbol)
            })
            .collect::<Vec<_>>();
        let links = symbols
            .iter()
            .map(|&symbol| {
                (
                    symbol,
                    store.declared_type_links(symbol),
                    store.value_symbol_links(symbol),
                    store.alias_symbol_links(symbol),
                    store.source_class_provenance_for_symbol(symbol),
                )
            })
            .collect::<Vec<_>>();
        let types = store
            .types()
            .filter(|(_, record)| {
                record
                    .symbol()
                    .is_some_and(|symbol| symbols.contains(&symbol))
            })
            .collect::<Vec<_>>();
        let signatures = store
            .signatures()
            .filter(|(_, signature)| {
                signature
                    .declaration()
                    .is_some_and(|node| node.file == file)
            })
            .collect::<Vec<_>>();
        let source = SourceFileRef::new(
            store.id(),
            NodeRef::new(parsed.arena.id(), file, parsed.source_file),
        );
        format!(
            "{:?}",
            (
                nodes,
                links,
                types,
                signatures,
                store.source_file_links(source)
            )
        )
    }

    // Keep canonical records and links, not internal observation sequence counters.
    fn canonical_state(
        store: &CanonicalTypeMapperStore,
        files: &[(FileId, &ParseResult)],
    ) -> String {
        let counts = [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
            store.merged_symbol_len(),
            store.type_resolution_len(),
        ];
        let links = store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.declared_type_links(symbol),
                    store.value_symbol_links(symbol),
                    store.alias_symbol_links(symbol),
                    store.module_symbol_links(symbol),
                    store.export_type_links(symbol),
                    store.type_alias_links(symbol),
                )
            })
            .collect::<Vec<_>>();
        let sources = files
            .iter()
            .map(|&(file, parsed)| source_cache_state(store, file, parsed))
            .collect::<Vec<_>>();
        format!(
            "{:?}",
            (
                counts,
                store.checker_link_allocated_lengths(),
                store.symbol_store(),
                store.types().collect::<Vec<_>>(),
                store.signatures().collect::<Vec<_>>(),
                links,
                sources,
            )
        )
    }

    fn assert_type_only_diagnostic(
        context: &CanonicalCheckerContext<'_>,
        binding: &SourceImportBindingPlan,
        owner: SemanticSymbolId,
        read: NodeRef,
    ) {
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the consumer must have only its type-only value-use diagnostic")
        };
        assert_eq!(diagnostic.node, Some(read));
        assert_eq!(diagnostic.diagnostic.code(), 1361);
        assert_eq!(diagnostic.diagnostic.arguments, ["ImportedBase"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "'ImportedBase' cannot be used as a value because it was imported using 'import type'."
        );
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        let store = context.store();
        assert_eq!(
            store.type_node_links(read).unwrap().resolved_type,
            Some(store.intrinsic_bootstrap().unwrap().error_type)
        );
        assert_eq!(
            store.symbol_node_links(read).unwrap().resolved_symbol,
            Some(binding.alias_symbol)
        );
        let links = store.alias_symbol_links(binding.alias_symbol).unwrap();
        assert_eq!(links.immediate_target, Some(owner));
        assert_eq!(links.alias_target, AliasTargetState::Resolved(owner));
        assert_eq!(links.type_only_declaration, Some(binding.declaration));
        assert!(store.value_symbol_links(binding.alias_symbol).is_none());
        assert!(
            store
                .source_file_links(context.source_file(read.file).unwrap())
                .unwrap()
                .type_checked
        );
    }

    fn assert_replay(
        context: &mut CanonicalCheckerContext<'_>,
        consumer: FileId,
        files: &[(FileId, &ParseResult)],
    ) {
        let warm = canonical_state(context.store(), files);
        let diagnostics = context.diagnostics().clone();
        for _ in 0..2 {
            context.recheck_source_file(consumer).unwrap();
            assert_eq!(canonical_state(context.store(), files), warm);
            assert_eq!(context.diagnostics(), &diagnostics);
        }
    }

    #[test]
    fn type_only_class_imports_keep_both_spellings_and_binder_orders_lazy() {
        for consumer_text in CONSUMERS {
            for reverse in [false, true] {
                let provider = parsed(PROVIDER);
                let consumer = parsed(consumer_text);
                let provider_file = FileId::new(890);
                let consumer_file = FileId::new(891);
                let mut files = [(provider_file, &provider), (consumer_file, &consumer)];
                if reverse {
                    files.reverse();
                }
                let mut context = context_with_routes(
                    &files,
                    &[Route {
                        source: usize::from(!reverse),
                        specifier: 0,
                        target: Some(usize::from(reverse)),
                    }],
                );
                let declaration = class_declaration(&provider, provider_file, "Base");
                let (owner, local) = class_symbols(
                    context.store(),
                    context.file(provider_file).unwrap().1,
                    declaration,
                    "Base",
                );
                let binding = import_binding(&context, consumer_file, &consumer);
                let read = value_read(&consumer, consumer_file);
                let cold_provider = source_cache_state(context.store(), provider_file, &provider);
                for symbol in [owner, local, binding.alias_symbol] {
                    assert!(context.store().value_symbol_links(symbol).is_none());
                }
                assert!(
                    context
                        .store()
                        .source_class_provenance_for_symbol(owner)
                        .is_none()
                );
                context.check_source_file(consumer_file).unwrap();
                assert_type_only_diagnostic(&context, &binding, owner, read);
                assert_eq!(
                    source_cache_state(context.store(), provider_file, &provider),
                    cold_provider
                );
                assert!(
                    context
                        .store()
                        .source_file_links(context.source_file(provider_file).unwrap())
                        .is_none_or(|links| !links.type_checked)
                );
                for symbol in [owner, local] {
                    assert!(context.store().value_symbol_links(symbol).is_none());
                }
                assert_replay(&mut context, consumer_file, &files);
            }
        }
    }

    fn assert_readonly_target(
        fixture: &Fixture,
        alias: SemanticSymbolId,
        owner: SemanticSymbolId,
        expected: &Result<NodeRef, SourceImportError>,
    ) {
        let host =
            property_type_import_host(&fixture.files, &fixture.bound, Some(&fixture.manifest));
        let files = fixture
            .files
            .iter()
            .map(|file| (file.file, &file.parsed))
            .collect::<Vec<_>>();
        let before = canonical_state(&fixture.store, &files);
        let allocations = store_state(&fixture.store);
        for _ in 0..2 {
            assert_eq!(
                &plan_direct_exported_type_target(&fixture.store, &host, alias, owner),
                expected
            );
            assert_eq!(canonical_state(&fixture.store, &files), before);
            assert_eq!(store_state(&fixture.store), allocations);
        }
    }

    #[derive(Clone, Copy)]
    enum ClassIdentityDamage {
        OwnerValueDeclaration,
        LocalExportOwner,
        ExportTable,
        LocalFlags,
        LocalTable,
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep each real identity mutation beside its exact restoration.
    fn type_only_class_targets_recheck_real_owner_local_and_export_identity() {
        for warm_alias in [false, true] {
            let mut fixture = fixture(
                &[
                    "export class Base { value = 1; constructor() {} } \
                     export class Other { value = 2; constructor() {} }",
                    CONSUMERS[0],
                ],
                &[Route {
                    source: 1,
                    specifier: 0,
                    target: Some(0),
                }],
            );
            let binding = fixture.plan_type_import(1, 0).bindings[0].clone();
            let declaration =
                class_declaration(&fixture.files[0].parsed, fixture.files[0].file, "Base");
            let bound = &fixture.bound[&fixture.files[0].file];
            let (owner, local) = class_symbols(&fixture.store, bound, declaration, "Base");
            assert_eq!(direct_export(&fixture, 0, "Base"), owner);
            let other = direct_export(&fixture, 0, "Other");
            let other_declaration =
                class_declaration(&fixture.files[0].parsed, fixture.files[0].file, "Other");
            let (_, other_local) = class_symbols(&fixture.store, bound, other_declaration, "Other");
            let module = bound.symbol(bound.source_file()).unwrap();
            let exports = fixture.store.symbol(module).unwrap().exports().unwrap();
            let locals = bound.locals(bound.source_file()).unwrap();
            if warm_alias {
                let resolved =
                    resolve_all_types(&mut fixture, std::slice::from_ref(&binding)).unwrap();
                assert_eq!(resolved[0].target_declaration, declaration);
                assert_eq!(resolved[0].target_symbol, owner);
            }
            assert_readonly_target(&fixture, binding.alias_symbol, owner, &Ok(declaration));
            for damage in [
                ClassIdentityDamage::OwnerValueDeclaration,
                ClassIdentityDamage::LocalExportOwner,
                ClassIdentityDamage::ExportTable,
                ClassIdentityDamage::LocalFlags,
                ClassIdentityDamage::LocalTable,
            ] {
                match damage {
                    ClassIdentityDamage::OwnerValueDeclaration => {
                        assert!(fixture.store.set_symbol_declarations(
                            owner,
                            Some(vec![declaration]),
                            None,
                        ));
                    }
                    ClassIdentityDamage::LocalExportOwner => {
                        assert!(fixture.store.set_symbol_relationships(
                            local,
                            None,
                            None,
                            None,
                            Some(other),
                        ));
                    }
                    ClassIdentityDamage::ExportTable => {
                        assert_eq!(
                            fixture.store.insert_symbol(
                                exports,
                                EscapedName::source("Base"),
                                other
                            ),
                            Some(Some(owner))
                        );
                    }
                    ClassIdentityDamage::LocalFlags => {
                        assert!(fixture.store.set_symbol_flags(
                            local,
                            SymbolFlags::NONE,
                            CheckFlags::NONE
                        ));
                    }
                    ClassIdentityDamage::LocalTable => {
                        assert_eq!(
                            fixture.store.insert_symbol(
                                locals,
                                EscapedName::source("Base"),
                                other_local
                            ),
                            Some(Some(local))
                        );
                    }
                }
                assert_readonly_target(
                    &fixture,
                    binding.alias_symbol,
                    owner,
                    &Err(invariant(SourceImportInvariant::InvalidTargetLinks(owner))),
                );
                match damage {
                    ClassIdentityDamage::OwnerValueDeclaration => {
                        assert!(fixture.store.set_symbol_declarations(
                            owner,
                            Some(vec![declaration]),
                            Some(declaration),
                        ));
                    }
                    ClassIdentityDamage::LocalExportOwner => {
                        assert!(fixture.store.set_symbol_relationships(
                            local,
                            None,
                            None,
                            None,
                            Some(owner),
                        ));
                    }
                    ClassIdentityDamage::ExportTable => {
                        assert_eq!(
                            fixture.store.insert_symbol(
                                exports,
                                EscapedName::source("Base"),
                                owner
                            ),
                            Some(Some(other))
                        );
                    }
                    ClassIdentityDamage::LocalFlags => {
                        assert!(fixture.store.set_symbol_flags(
                            local,
                            SymbolFlags::EXPORT_VALUE,
                            CheckFlags::NONE
                        ));
                    }
                    ClassIdentityDamage::LocalTable => {
                        assert_eq!(
                            fixture
                                .store
                                .insert_symbol(locals, EscapedName::source("Base"), local),
                            Some(Some(other_local))
                        );
                    }
                }
                assert_readonly_target(&fixture, binding.alias_symbol, owner, &Ok(declaration));
            }

            let resolved = resolve_all_types(&mut fixture, std::slice::from_ref(&binding))
                .unwrap()
                .remove(0);
            let read = identifier_initializer(&fixture, 1, "ImportedBase");
            let original = fixture
                .store
                .alias_symbol_links(binding.alias_symbol)
                .unwrap()
                .clone();
            for damage in 0..3 {
                let mut links = original.clone();
                match damage {
                    0 => links.immediate_target = Some(other),
                    1 => links.alias_target = AliasTargetState::Resolved(other),
                    2 => links.type_only_declaration = None,
                    _ => unreachable!(),
                }
                assert!(
                    fixture
                        .store
                        .set_alias_symbol_links(binding.alias_symbol, links)
                );
                let files = fixture
                    .files
                    .iter()
                    .map(|file| (file.file, &file.parsed))
                    .collect::<Vec<_>>();
                let before = canonical_state(&fixture.store, &files);
                for _ in 0..2 {
                    assert_eq!(
                        reject_source_type_import_value_use(
                            &fixture.files[1].parsed.arena,
                            &fixture.bound[&fixture.files[1].file],
                            &fixture.store,
                            &resolved,
                            read,
                            "ImportedBase",
                            binding.alias_symbol,
                        ),
                        Err(invariant(SourceImportInvariant::InvalidAliasLinks(
                            binding.alias_symbol
                        )))
                    );
                    assert_eq!(canonical_state(&fixture.store, &files), before);
                }
                assert!(
                    fixture
                        .store
                        .set_alias_symbol_links(binding.alias_symbol, original.clone())
                );
                assert_eq!(
                    reject_source_type_import_value_use(
                        &fixture.files[1].parsed.arena,
                        &fixture.bound[&fixture.files[1].file],
                        &fixture.store,
                        &resolved,
                        read,
                        "ImportedBase",
                        binding.alias_symbol,
                    ),
                    Err(unsupported(
                        SourceImportUnsupported::ValueUseOfTypeOnlyImport(read)
                    ))
                );
            }
            for symbol in [owner, local, other, other_local, binding.alias_symbol] {
                assert!(fixture.store.value_symbol_links(symbol).is_none());
            }
            assert!(
                fixture
                    .store
                    .source_class_provenance_for_symbol(owner)
                    .is_none()
            );
        }
    }

    #[test]
    fn type_only_class_imports_isolate_bodies_and_preserve_checked_provider_caches() {
        for checked_provider in [false, true] {
            let provider = parsed(if checked_provider {
                PROVIDER
            } else {
                "export class Base { value: number = 'bad'; constructor() {} \
                 read() { return this.value; } }"
            });
            let consumer = parsed(CONSUMERS[0]);
            let provider_file = FileId::new(892);
            let consumer_file = FileId::new(893);
            let files = [(provider_file, &provider), (consumer_file, &consumer)];
            let mut context = context_with_routes(
                &files,
                &[Route {
                    source: 1,
                    specifier: 0,
                    target: Some(0),
                }],
            );
            let declaration = class_declaration(&provider, provider_file, "Base");
            let (owner, local) = class_symbols(
                context.store(),
                context.file(provider_file).unwrap().1,
                declaration,
                "Base",
            );
            let binding = import_binding(&context, consumer_file, &consumer);
            if checked_provider {
                context.check_source_file(provider_file).unwrap();
                assert!(context.diagnostics().is_empty());
                let owner_value = context
                    .store()
                    .value_symbol_links(owner)
                    .unwrap()
                    .resolved_type
                    .unwrap();
                assert_eq!(
                    context
                        .store()
                        .value_symbol_links(local)
                        .unwrap()
                        .resolved_type,
                    Some(owner_value)
                );
                let provenance = context
                    .store()
                    .source_class_provenance_for_symbol(owner)
                    .unwrap();
                assert_eq!(provenance.symbol(), owner);
                assert_eq!(
                    context
                        .store()
                        .declared_type_links(owner)
                        .unwrap()
                        .declared_type,
                    Some(provenance.instance_type())
                );
            } else {
                assert!(
                    context
                        .store()
                        .source_class_provenance_for_symbol(owner)
                        .is_none()
                );
                for symbol in [owner, local] {
                    assert!(context.store().value_symbol_links(symbol).is_none());
                }
            }
            let before = source_cache_state(context.store(), provider_file, &provider);
            context.check_source_file(consumer_file).unwrap();
            assert_type_only_diagnostic(
                &context,
                &binding,
                owner,
                value_read(&consumer, consumer_file),
            );
            assert_eq!(
                source_cache_state(context.store(), provider_file, &provider),
                before
            );
            assert_eq!(
                context
                    .store()
                    .source_file_links(context.source_file(provider_file).unwrap())
                    .is_some_and(|links| links.type_checked),
                checked_provider
            );
            assert_replay(&mut context, consumer_file, &files);
        }
    }
}
