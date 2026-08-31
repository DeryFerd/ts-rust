// Included in source_imports::tests so the controls use the real import helpers.

type NamespaceIdentityInput = (&'static str, &'static str, bool, bool, CanonicalModuleState);

fn namespace_identity_libraries() -> [NamespaceIdentityInput; 3] {
    [
        (
            include_str!("../../../ts_bundled/libs/lib.es5.d.ts"),
            "/lib.es5.d.ts",
            true,
            true,
            CanonicalModuleState::Script,
        ),
        (
            include_str!("../../../ts_bundled/libs/lib.decorators.d.ts"),
            "/lib.decorators.d.ts",
            true,
            true,
            CanonicalModuleState::Script,
        ),
        (
            include_str!("../../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
            "/lib.decorators.legacy.d.ts",
            true,
            true,
            CanonicalModuleState::Script,
        ),
    ]
}

fn namespace_identity_context<'a>(
    inputs: &[NamespaceIdentityInput],
    parsed: &'a [ParseResult],
    files: &[FileId],
    routes: &[(usize, usize)],
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (index, (_, path, declaration, library, module)) in inputs.iter().enumerate() {
        assert!(parsed[index].diagnostics.is_empty());
        binder
            .bind_source_file_with_facts(
                &parsed[index].arena,
                parsed[index].source_file,
                files[index],
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(format!("\"{path}\"")),
                    CanonicalSourceLanguage::TypeScript,
                    *declaration,
                    *library,
                    *module,
                ),
            )
            .unwrap();
    }
    for (index, source) in parsed.iter().enumerate() {
        binder
            .bind_typescript_declaration_slice(&source.arena, files[index])
            .unwrap();
    }
    let entries = routes.iter().flat_map(|&(from, to)| {
        module_specifiers(&parsed[from])
            .into_iter()
            .map(move |specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    NodeRef::new(parsed[from].arena.id(), files[from], specifier),
                    CanonicalResolvedModuleInput::new(
                        files[to],
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                )
            })
    });
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        parsed
            .iter()
            .enumerate()
            .map(|(index, source)| (files[index], &source.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_emit: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ts_options::ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(entries),
    )
    .unwrap()
}

fn namespace_identity_node(
    parsed: &ParseResult,
    file: FileId,
    matches: impl Fn(&NodeData) -> bool,
) -> NodeRef {
    let nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, node)| {
            matches(&node.data).then_some(NodeRef::new(parsed.arena.id(), file, id))
        })
        .collect::<Vec<_>>();
    assert_eq!(nodes.len(), 1);
    nodes[0]
}

fn namespace_identity_access(parsed: &ParseResult, file: FileId) -> (NodeRef, NodeRef) {
    let access = namespace_identity_node(parsed, file, |data| {
        let NodeData::PropertyAccessExpression(access) = data else {
            return false;
        };
        matches!(&parsed.arena.get(access.name).unwrap().data,
            NodeData::Identifier(name) if name.text == "items")
    });
    let NodeData::PropertyAccessExpression(data) = &parsed.arena.get(access.node).unwrap().data
    else {
        unreachable!()
    };
    (access, NodeRef::new(access.arena, access.file, data.name))
}

fn namespace_identity_snapshot(context: &CanonicalCheckerContext<'_>) -> (String, String) {
    (
        format!("{:?}", context.store()),
        format!("{:?}", context.diagnostics()),
    )
}

fn namespace_identity_replay_state(snapshot: &str) -> (&str, u64, &str) {
    const FIELD: &str = ", next_relation_observation_token: ";
    let (before, rest) = snapshot.split_once(FIELD).unwrap();
    assert!(!rest.contains(FIELD));
    let (token, after) = rest.split_once(',').unwrap();
    assert!(!token.is_empty() && token.bytes().all(|byte| byte.is_ascii_digit()));
    (before, token.parse().unwrap(), after)
}

fn namespace_identity_assert_property(
    context: &mut CanonicalCheckerContext<'_>,
    access: NodeRef,
    name: NodeRef,
    source: SemanticSymbolId,
    declaration: NodeRef,
    property: SemanticSymbolId,
) {
    let before = namespace_identity_snapshot(context);
    assert_ne!(property, source);
    let origin = context
        .store()
        .synthetic_namespace_property_origin(property)
        .unwrap()
        .clone();
    assert_eq!(origin.property, property);
    assert_eq!(origin.source, source);
    assert_eq!(origin.declaration, declaration);
    let record = context.store().symbol(property).unwrap();
    assert_eq!(record.flags(), SymbolFlags::PROPERTY);
    assert_eq!(record.check_flags(), CheckFlags::NONE);
    assert_eq!(record.parent(), None);
    assert_eq!(record.value_declaration(), None);
    assert_eq!(context.store().get_merged_symbol(property), Some(property));
    assert_eq!(context.store().symbol(source), Some(&origin.source_record));
    assert_eq!(
        context.get_symbol_declarations(property).unwrap(),
        [declaration]
    );
    for location in [access, name] {
        assert_eq!(context.get_symbol_at_location(location), Ok(Some(property)));
        assert_eq!(context.get_type_at_location(location), Ok(origin.type_));
        assert_eq!(
            context.symbol_to_string_at_location(property, location),
            Ok("items".to_owned())
        );
    }
    assert_eq!(context.type_to_string(origin.type_).unwrap(), "string[]");
    assert_eq!(namespace_identity_snapshot(context), before);
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the complete original input and its diagnostic checks together.
fn synthetic_namespace_property_identity_keeps_the_complete_original_ambient_case() {
    let mut inputs = namespace_identity_libraries().to_vec();
    inputs.extend([
        (
            concat!(
                "declare function foo(): void;\r\n",
                "declare namespace foo { export const items: string[]; }\r\n",
                "export = foo;\r\n\r\n"
            ),
            "/node_modules/foo/index.d.ts",
            true,
            false,
            CanonicalModuleState::External,
        ),
        (
            "declare module 'mymod' { import * as foo from 'foo'; export { foo }; }\r\n\r\n",
            "/a.d.ts",
            true,
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare module 'mymod' { export const foo: number; }\r\n\r\n",
            "/b.d.ts",
            true,
            false,
            CanonicalModuleState::Script,
        ),
        (
            concat!(
                "declare global {\r\n",
                "    interface Array<T> {\r\n",
                "        customMethod(): T;\r\n",
                "    }\r\n",
                "}\r\n",
                "export {};\r\n\r\n"
            ),
            "/augment.ts",
            false,
            false,
            CanonicalModuleState::External,
        ),
        (
            concat!(
                "import * as foo from 'foo';\r\n",
                "const items = foo.items;\r\n",
                "const result: string = items.customMethod();\r\n\r\n",
                "const fresh: string[] = [];\r\n",
                "const result2: string = fresh.customMethod();\r\n"
            ),
            "/index.ts",
            false,
            false,
            CanonicalModuleState::External,
        ),
    ]);
    let parsed = inputs
        .iter()
        .map(|input| parse_source_file(input.0))
        .collect::<Vec<_>>();
    let files = (0..inputs.len())
        .map(|index| FileId::new(u32::try_from(index).unwrap() + 81_000))
        .collect::<Vec<_>>();
    let declaration = namespace_identity_node(&parsed[3], files[3], |data| {
        matches!(data, NodeData::VariableDeclaration(_))
    });
    let (access, name) = namespace_identity_access(&parsed[7], files[7]);
    let duplicate_names = [4, 5].map(|index| {
        let declaration = namespace_identity_node(&parsed[index], files[index], |data| {
            matches!(
                data,
                NodeData::ExportSpecifier(_) | NodeData::VariableDeclaration(_)
            )
        });
        let name = match &parsed[index].arena.get(declaration.node).unwrap().data {
            NodeData::ExportSpecifier(data) => data.name,
            NodeData::VariableDeclaration(data) => data.name,
            _ => unreachable!(),
        };
        NodeRef::new(declaration.arena, declaration.file, name)
    });
    let assert_diagnostics = |context: &CanonicalCheckerContext<'_>| {
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        for (diagnostic, (node, related, start)) in diagnostics.iter().zip([
            (duplicate_names[0], duplicate_names[1], 62),
            (duplicate_names[1], duplicate_names[0], 38),
        ]) {
            assert_eq!(diagnostic.node, Some(node));
            assert_eq!(
                context
                    .file(node.file)
                    .unwrap()
                    .0
                    .get(node.node)
                    .unwrap()
                    .range
                    .start
                    .get(),
                start
            );
            assert_eq!(
                context
                    .file(node.file)
                    .unwrap()
                    .0
                    .get(node.node)
                    .unwrap()
                    .range
                    .end
                    .get()
                    - start,
                3
            );
            assert!(diagnostic.range_override.is_none());
            assert_eq!(diagnostic.diagnostic.code(), 2451);
            assert_eq!(
                diagnostic.diagnostic.category(),
                ts_diagnostics::Category::Error
            );
            assert_eq!(diagnostic.diagnostic.arguments, ["foo"]);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Cannot redeclare block-scoped variable 'foo'."
            );
            let [other] = diagnostic.related_information.as_slice() else {
                panic!("one related declaration")
            };
            assert_eq!(other.node, Some(related));
            assert_eq!(other.diagnostic.code(), 6203);
            assert_eq!(
                other.diagnostic.category(),
                ts_diagnostics::Category::Message
            );
            let related_range = context
                .file(related.file)
                .unwrap()
                .0
                .get(related.node)
                .unwrap()
                .range;
            let related_start = if related == duplicate_names[0] {
                62
            } else {
                38
            };
            assert_eq!(related_range.start.get(), related_start);
            assert_eq!(related_range.end.get() - related_start, 3);
            assert_eq!(other.diagnostic.arguments, ["foo"]);
            assert_eq!(
                other.diagnostic.render().unwrap(),
                "'foo' was also declared here."
            );
        }
    };
    for name_first in [false, true] {
        let mut context = namespace_identity_context(&inputs, &parsed, &files, &[(4, 3), (7, 3)]);
        assert!(context.global_type_diagnostics().next().is_none());
        let source = context
            .file(files[3])
            .unwrap()
            .1
            .symbol(declaration)
            .unwrap();
        let globals = context.global_types().clone();
        assert_diagnostics(&context);
        let first = if name_first { name } else { access };
        let property = context.get_symbol_at_location(first).unwrap().unwrap();
        for &file in &files[3..] {
            context.check_source_file(file).unwrap();
        }
        namespace_identity_assert_property(
            &mut context,
            access,
            name,
            source,
            declaration,
            property,
        );
        let local = namespace_identity_node(&parsed[7], files[7], |data| {
            let NodeData::VariableDeclaration(variable) = data else {
                return false;
            };
            matches!(&parsed[7].arena.get(variable.name).unwrap().data, NodeData::Identifier(name) if name.text == "items")
        });
        assert_ne!(
            context.file(files[7]).unwrap().1.symbol(local).unwrap(),
            property
        );
        let NodeData::VariableDeclaration(variable) =
            &parsed[3].arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let source_name = NodeRef::new(declaration.arena, declaration.file, variable.name);
        assert_eq!(
            context.get_symbol_at_location(source_name),
            Ok(Some(source))
        );
        assert_eq!(
            context.get_symbol_declarations(source).unwrap(),
            [declaration]
        );
        for (id, node) in parsed[7].arena.iter() {
            let NodeData::PropertyAccessExpression(data) = &node.data else {
                continue;
            };
            if !matches!(&parsed[7].arena.get(data.name).unwrap().data, NodeData::Identifier(name) if name.text == "customMethod")
            {
                continue;
            }
            let location = NodeRef::new(parsed[7].arena.id(), files[7], id);
            let symbol = context.get_symbol_at_location(location).unwrap().unwrap();
            assert_eq!(
                context.symbol_to_string_at_location(symbol, location),
                Ok("Array.customMethod".to_owned())
            );
        }
        assert_diagnostics(&context);
        let warm = namespace_identity_snapshot(&context);
        for forced in [false, true] {
            for &file in files[3..].iter().rev() {
                if forced {
                    context.recheck_source_file(file).unwrap();
                } else {
                    context.check_source_file(file).unwrap();
                }
            }
            namespace_identity_assert_property(
                &mut context,
                access,
                name,
                source,
                declaration,
                property,
            );
            assert_diagnostics(&context);
            assert_eq!(context.global_types(), &globals);
            let after = namespace_identity_snapshot(&context);
            if forced {
                let (before_prefix, before_token, before_suffix) =
                    namespace_identity_replay_state(&warm.0);
                let (after_prefix, after_token, after_suffix) =
                    namespace_identity_replay_state(&after.0);
                assert_eq!((after_prefix, after_suffix), (before_prefix, before_suffix));
                assert_eq!(after_token, before_token.checked_add(1).unwrap());
                assert_eq!(after.1, warm.1);
            } else {
                assert_eq!(after, warm);
            }
        }
    }
    // Whole 28-type/31-symbol artifact comparison remains the original corpus gate.
}

#[test]
#[allow(clippy::too_many_lines)] // Keep both real import orders and their full replay checks together.
fn synthetic_namespace_property_identity_keeps_two_renamed_public_imports_distinct() {
    let mut inputs = namespace_identity_libraries().to_vec();
    inputs.extend([
        ("declare function foo(): void; declare namespace foo { export const items: string[]; } export = foo;", "/foo.d.ts", true, false, CanonicalModuleState::External),
        ("import * as first from './foo'; const left = first.items;", "/left.ts", false, false, CanonicalModuleState::External),
        ("import * as second from './foo'; const right = second.items;", "/right.ts", false, false, CanonicalModuleState::External),
    ]);
    let parsed = inputs
        .iter()
        .map(|input| parse_source_file(input.0))
        .collect::<Vec<_>>();
    let files = (0..inputs.len())
        .map(|index| FileId::new(u32::try_from(index).unwrap() + 82_000))
        .collect::<Vec<_>>();
    let declaration = namespace_identity_node(&parsed[3], files[3], |data| {
        matches!(data, NodeData::VariableDeclaration(_))
    });
    let accesses = [4, 5].map(|index| namespace_identity_access(&parsed[index], files[index]));
    for reverse in [false, true] {
        let mut context = namespace_identity_context(&inputs, &parsed, &files, &[(4, 3), (5, 3)]);
        let source = context
            .file(files[3])
            .unwrap()
            .1
            .symbol(declaration)
            .unwrap();
        let order = if reverse { [1, 0] } else { [0, 1] };
        let mut selected = [None, None];
        for index in order {
            let (access, name) = accesses[index];
            selected[index] = context
                .get_symbol_at_location(if reverse { name } else { access })
                .unwrap();
        }
        let properties = selected.map(Option::unwrap);
        assert_ne!(properties[0], properties[1]);
        let states = properties.map(|property| {
            context
                .store()
                .synthetic_namespace_property_state(property)
                .unwrap()
                .clone()
        });
        let origins = properties.map(|property| {
            context
                .store()
                .synthetic_namespace_property_origin(property)
                .unwrap()
                .clone()
        });
        assert_ne!(origins[0].namespace, origins[1].namespace);
        assert_ne!(origins[0].namespace_type, origins[1].namespace_type);
        assert_ne!(origins[0].alias, origins[1].alias);
        assert_ne!(origins[0].originating_import, origins[1].originating_import);
        assert_eq!(origins[0].source, origins[1].source);
        for &file in &files[3..] {
            context.check_source_file(file).unwrap();
        }
        for _ in 0..2 {
            for index in order {
                let (access, name) = accesses[index];
                namespace_identity_assert_property(
                    &mut context,
                    access,
                    name,
                    source,
                    declaration,
                    properties[index],
                );
            }
            let before = namespace_identity_snapshot(&context);
            for &file in files[3..].iter().rev() {
                context.recheck_source_file(file).unwrap();
            }
            assert_eq!(namespace_identity_snapshot(&context), before);
            assert!(context.diagnostics().is_empty());
        }
        let before_damage = namespace_identity_snapshot(&context);
        assert_eq!(
            context
                .store_mut_for_test()
                .replace_synthetic_namespace_property_state_for_test(properties[0], None),
            Some(states[0].clone()),
        );
        let damaged = namespace_identity_snapshot(&context);
        for _ in 0..2 {
            for location in [accesses[0].0, accesses[0].1] {
                assert!(
                    context
                        .symbol_to_string_at_location(properties[0], location)
                        .is_err()
                );
                assert_eq!(namespace_identity_snapshot(&context), damaged);
            }
        }
        assert_eq!(
            context
                .store_mut_for_test()
                .replace_synthetic_namespace_property_state_for_test(
                    properties[0],
                    Some(states[0].clone())
                ),
            None,
        );
        namespace_identity_assert_property(
            &mut context,
            accesses[0].0,
            accesses[0].1,
            source,
            declaration,
            properties[0],
        );
        assert_eq!(namespace_identity_snapshot(&context), before_damage);
    }
}

fn namespace_identity_raw_fixture() -> Fixture {
    fixture_with_module_states_and_wrapper_flags(
        &[
            "import * as first from './foo'; const value = first;",
            "import * as second from './foo'; const value = second;",
            "declare function foo(): void; declare namespace foo { export const items: string[]; } export = foo;",
            "interface Array<T> {}",
        ],
        &[
            Route {
                source: 0,
                specifier: 0,
                target: Some(2),
            },
            Route {
                source: 1,
                specifier: 0,
                target: Some(2),
            },
        ],
        &[
            CanonicalModuleState::External,
            CanonicalModuleState::External,
            CanonicalModuleState::External,
            CanonicalModuleState::Script,
        ],
        None,
        &[2],
    )
}

fn namespace_identity_private_fixture() -> (Fixture, [SyntheticNamespacePropertyOrigin; 2]) {
    let mut fixture = namespace_identity_raw_fixture();
    let origins = ["first", "second"]
        .into_iter()
        .enumerate()
        .map(|(index, name)| {
            let plan = fixture.plan_import(index, 0);
            let file = &fixture.files[index];
            let read = plan_source_import_identifier_read(
                &file.parsed.arena,
                fixture.bound.get(&file.file).unwrap(),
                &fixture.store,
                &plan.bindings[0],
                identifier_initializer(&fixture, index, name),
                name,
                plan.bindings[0].alias_symbol,
            )
            .unwrap();
            let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
            resolve_namespace_exports(&mut fixture, &resolved[0]).unwrap();
            let value = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
            publish_for_test(&mut fixture.store, std::slice::from_ref(&value));
            let PreparedSourceImportTarget::ModuleNamespace { properties } = value.target else {
                unreachable!()
            };
            let property = properties
                .iter()
                .find(|property| property.name.as_utf8() == Some("items"))
                .unwrap();
            fixture
                .store
                .synthetic_namespace_property_origin(property.symbol)
                .unwrap()
                .clone()
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    (fixture, origins)
}

fn namespace_identity_set_members(
    store: &mut CanonicalTypeMapperStore,
    origin: &SyntheticNamespacePropertyOrigin,
    replacement: SemanticSymbolId,
) {
    let mut properties = origin.namespace_properties.to_vec();
    let selected = properties
        .iter_mut()
        .find(|symbol| **symbol == origin.property)
        .unwrap();
    *selected = replacement;
    assert!(
        store
            .insert_symbol(
                origin.namespace_members,
                EscapedName::source("items"),
                replacement
            )
            .unwrap()
            .is_some()
    );
    assert!(store.set_structured_type_members(
        origin.namespace_type,
        Some(origin.namespace_members),
        Some(properties),
        None,
        None,
        None
    ));
}

#[allow(clippy::too_many_lines)] // Follow pending preparation, actual publication and damaged replay.
fn namespace_identity_assert_publication_lifecycle() {
    let mut fixture = namespace_identity_raw_fixture();
    let mut requests = Vec::new();
    for (index, name) in ["first", "second"].into_iter().enumerate() {
        let plan = fixture.plan_import(index, 0);
        let file = &fixture.files[index];
        let read = plan_source_import_identifier_read(
            &file.parsed.arena,
            fixture.bound.get(&file.file).unwrap(),
            &fixture.store,
            &plan.bindings[0],
            identifier_initializer(&fixture, index, name),
            name,
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        resolve_namespace_exports(&mut fixture, &resolved[0]).unwrap();
        let value = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        requests.push((resolved[0].clone(), read, value));
    }
    let states = requests
        .iter()
        .map(|(_, _, value)| {
            let PreparedSourceImportTarget::ModuleNamespace { properties } = &value.target else {
                unreachable!()
            };
            let property = properties
                .iter()
                .find(|property| property.name.as_utf8() == Some("items"))
                .unwrap();
            fixture
                .store
                .synthetic_namespace_property_state(property.symbol)
                .unwrap()
                .clone()
        })
        .collect::<Vec<_>>();
    for state in &states {
        assert!(!state.namespace_published);
        assert!(!state.alias_published);
    }
    assert_ne!(states[0].origin.property, states[1].origin.property);
    assert_ne!(
        states[0].origin.namespace_type,
        states[1].origin.namespace_type
    );
    for (resolved, read, value) in &requests {
        let before = synthetic_namespace_display_state(&fixture);
        let origin_count = fixture.store.synthetic_namespace_property_origin_len();
        for _ in 0..2 {
            assert_eq!(prepare_one(&mut fixture, resolved, read), Ok(value.clone()));
            assert_eq!(synthetic_namespace_display_state(&fixture), before);
            assert_eq!(
                fixture.store.synthetic_namespace_property_origin_len(),
                origin_count
            );
            for state in &states {
                assert_eq!(
                    fixture
                        .store
                        .synthetic_namespace_property_state(state.origin.property),
                    Some(state)
                );
            }
        }
    }

    // A rejected setter cannot mark. Successful unrelated or incomplete payloads
    // also cannot mark either pending import.
    let foreign = namespace_identity_raw_fixture();
    let foreign_alias = foreign.plan_import(0, 0).bindings[0].alias_symbol;
    let foreign_type = foreign.store.intrinsic_bootstrap().unwrap().boolean_type;
    let first = &states[0].origin;
    let boolean = fixture.store.intrinsic_bootstrap().unwrap().boolean_type;
    let mut duplicate = first.clone();
    duplicate.property = fixture
        .store
        .symbol_table(first.namespace_members)
        .unwrap()
        .get(InternalSymbolName::Default.as_ref())
        .unwrap();
    let before_duplicate = format!("{:?}", fixture.store);
    assert!(
        !fixture
            .store
            .record_synthetic_namespace_property_origin(duplicate)
    );
    assert_eq!(format!("{:?}", fixture.store), before_duplicate);
    let expected = ValueSymbolLinks {
        resolved_type: Some(first.namespace_type),
        ..ValueSymbolLinks::default()
    };
    for (owner, links) in [
        (foreign_alias, expected.clone()),
        (
            first.namespace,
            ValueSymbolLinks {
                resolved_type: Some(foreign_type),
                ..ValueSymbolLinks::default()
            },
        ),
    ] {
        let before = format!("{:?}", fixture.store);
        assert!(!fixture.store.set_value_symbol_links(owner, links));
        assert_eq!(format!("{:?}", fixture.store), before);
    }
    for owner in [
        first.namespace,
        first.alias,
        first.source,
        states[1].origin.namespace,
        states[1].origin.alias,
    ] {
        let original = fixture.store.value_symbol_links(owner).cloned();
        for links in [
            ValueSymbolLinks::default(),
            ValueSymbolLinks {
                resolved_type: Some(boolean),
                ..ValueSymbolLinks::default()
            },
            ValueSymbolLinks {
                target: Some(first.source),
                ..expected.clone()
            },
        ] {
            assert!(fixture.store.set_value_symbol_links(owner, links));
            for state in &states {
                assert_eq!(
                    fixture
                        .store
                        .synthetic_namespace_property_state(state.origin.property),
                    Some(state)
                );
            }
        }
        if owner == first.source
            || owner == states[1].origin.namespace
            || owner == states[1].origin.alias
        {
            assert!(
                fixture
                    .store
                    .set_value_symbol_links(owner, expected.clone())
            );
            for state in &states {
                assert_eq!(
                    fixture
                        .store
                        .synthetic_namespace_property_state(state.origin.property),
                    Some(state)
                );
            }
        }
        assert!(
            fixture
                .store
                .set_value_symbol_links(owner, original.unwrap_or_default())
        );
    }
    for (index, (resolved, read, value)) in requests.iter().enumerate() {
        let origin = &states[index].origin;
        let publications = preflight_prepared_source_import_publications(
            &fixture.store,
            std::slice::from_ref(value),
        )
        .unwrap();
        assert_eq!(
            publications
                .iter()
                .map(|item| item.symbol)
                .collect::<Vec<_>>(),
            [origin.namespace, origin.alias]
        );
        for (step, publication) in publications.into_iter().enumerate() {
            assert!(
                fixture
                    .store
                    .set_value_symbol_links(publication.symbol, publication.links)
            );
            let current = fixture
                .store
                .synthetic_namespace_property_state(origin.property)
                .unwrap();
            assert_eq!(current.origin, *origin);
            assert!(current.namespace_published);
            assert_eq!(current.alias_published, step == 1);
            let other = fixture
                .store
                .synthetic_namespace_property_state(states[1 - index].origin.property)
                .unwrap();
            assert_eq!(other.namespace_published, index == 1);
            assert_eq!(other.alias_published, index == 1);
            let before = synthetic_namespace_display_state(&fixture);
            let saved = current.clone();
            assert_eq!(prepare_one(&mut fixture, resolved, read), Ok(value.clone()));
            assert_eq!(synthetic_namespace_display_state(&fixture), before);
            assert_eq!(
                fixture
                    .store
                    .synthetic_namespace_property_state(origin.property),
                Some(&saved)
            );
        }
    }
    let completed = states
        .iter()
        .map(|state| {
            fixture
                .store
                .synthetic_namespace_property_state(state.origin.property)
                .unwrap()
                .clone()
        })
        .collect::<Vec<_>>();
    for state in &completed {
        assert!(state.namespace_published && state.alias_published);
    }
    fixture.store.mark_relation_inputs_dirty();
    fixture.store.mark_union_cache_validation_dirty();
    let original = format!("{:?}", fixture.store);
    for (index, (resolved, read, _)) in requests.iter().enumerate() {
        let state = &completed[index];
        for clear_namespace in [false, true] {
            let mut changed = state.clone();
            if clear_namespace {
                changed.namespace_published = false;
            } else {
                changed.alias_published = false;
            }
            assert_eq!(
                fixture
                    .store
                    .replace_synthetic_namespace_property_state_for_test(
                        state.origin.property,
                        Some(changed),
                    ),
                Some(state.clone())
            );
            let damaged = format!("{:?}", fixture.store);
            for _ in 0..2 {
                assert!(
                    fixture
                        .store
                        .record_synthetic_namespace_property_origin(state.origin.clone())
                );
                assert_eq!(format!("{:?}", fixture.store), damaged);
                assert!(prepare_one(&mut fixture, resolved, read).is_err());
                assert_eq!(format!("{:?}", fixture.store), damaged);
            }
            fixture
                .store
                .replace_synthetic_namespace_property_state_for_test(
                    state.origin.property,
                    Some(state.clone()),
                );
            assert_eq!(format!("{:?}", fixture.store), original);
        }
    }
    for (index, (resolved, read, value)) in requests.iter().enumerate() {
        let origin = &completed[index].origin;
        let namespace_links = fixture
            .store
            .value_symbol_links(origin.namespace)
            .unwrap()
            .clone();
        let alias_links = fixture
            .store
            .value_symbol_links(origin.alias)
            .unwrap()
            .clone();
        for missing in ["alias", "namespace", "both"] {
            let before_damage = format!("{:?}", fixture.store);
            if missing != "alias" {
                assert!(
                    fixture
                        .store
                        .set_value_symbol_links(origin.namespace, ValueSymbolLinks::default())
                );
            }
            if missing != "namespace" {
                assert!(
                    fixture
                        .store
                        .set_value_symbol_links(origin.alias, ValueSymbolLinks::default())
                );
            }
            assert_eq!(
                fixture
                    .store
                    .synthetic_namespace_property_state(origin.property),
                Some(&completed[index])
            );
            let damaged = format!("{:?}", fixture.store);
            for _ in 0..2 {
                assert!(
                    prepare_one(&mut fixture, resolved, read).is_err(),
                    "{index} {missing}"
                );
                assert_eq!(format!("{:?}", fixture.store), damaged);
                let host = property_type_import_host(
                    &fixture.files,
                    &fixture.bound,
                    Some(&fixture.manifest),
                );
                assert!(
                    validated_synthetic_namespace_property_source(
                        &fixture.store,
                        &host,
                        origin.property
                    )
                    .is_err()
                );
                assert!(
                    synthetic_namespace_value_property(
                        &fixture.store,
                        origin.namespace,
                        origin.namespace_type,
                        origin.source,
                        origin.property,
                        Some(origin.array_targets)
                    )
                    .is_err()
                );
                assert_eq!(format!("{:?}", fixture.store), damaged);
            }
            assert!(
                fixture
                    .store
                    .set_value_symbol_links(origin.namespace, namespace_links.clone())
            );
            assert!(
                fixture
                    .store
                    .set_value_symbol_links(origin.alias, alias_links.clone())
            );
            assert_eq!(
                fixture
                    .store
                    .replace_synthetic_namespace_property_state_for_test(
                        origin.property,
                        Some(completed[index].clone())
                    ),
                Some(completed[index].clone())
            );
            assert_eq!(format!("{:?}", fixture.store), before_damage);
            let before = synthetic_namespace_display_state(&fixture);
            assert_eq!(prepare_one(&mut fixture, resolved, read), Ok(value.clone()));
            assert_eq!(synthetic_namespace_display_state(&fixture), before);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Each real source/cache mutation has an exact restoration below.
fn synthetic_namespace_property_identity_rejects_damage_and_cross_import_swaps_without_writes() {
    let (mut fixture, origins) = namespace_identity_private_fixture();
    let [first, second] = &origins;
    let states = origins.each_ref().map(|origin| {
        fixture
            .store
            .synthetic_namespace_property_state(origin.property)
            .unwrap()
            .clone()
    });
    assert_ne!(first.property, second.property);
    assert_ne!(first.namespace, second.namespace);
    assert_ne!(first.namespace_type, second.namespace_type);
    assert_ne!(first.alias, second.alias);
    assert_eq!(first.source, second.source);
    assert_eq!(first.declaration, second.declaration);
    let original = first.source_record.parent().unwrap();
    let source_record = fixture.store.symbol(first.source).unwrap().clone();
    let property_record = fixture.store.symbol(first.property).unwrap().clone();
    let property_links = fixture
        .store
        .value_symbol_links(first.property)
        .unwrap()
        .clone();
    let alias_links = fixture
        .store
        .alias_symbol_links(first.alias)
        .unwrap()
        .clone();
    let namespace_links = fixture
        .store
        .value_symbol_links(first.namespace)
        .unwrap()
        .clone();
    let annotation_links = fixture
        .store
        .type_node_links(first.annotation)
        .unwrap()
        .clone();
    let boolean = fixture.store.intrinsic_bootstrap().unwrap().boolean_type;
    // Mutation setters invalidate these caches. Keep that state in the baseline,
    // then compare every store byte after each rejection and exact restoration.
    fixture.store.mark_relation_inputs_dirty();
    fixture.store.mark_union_cache_validation_dirty();
    let before = format!("{:?}", fixture.store);
    for origin in &origins {
        for _ in 0..2 {
            assert!(
                fixture
                    .store
                    .record_synthetic_namespace_property_origin(origin.clone())
            );
            assert_eq!(format!("{:?}", fixture.store), before);
            let mut changed = origin.clone();
            changed.source = origin.alias;
            assert!(
                !fixture
                    .store
                    .record_synthetic_namespace_property_origin(changed)
            );
            assert_eq!(format!("{:?}", fixture.store), before);
            assert!(
                synthetic_namespace_value_property(
                    &fixture.store,
                    origin.namespace,
                    origin.namespace_type,
                    origin.source,
                    origin.property,
                    Some(CanonicalArrayTargets::for_test(boolean, boolean)),
                )
                .is_err()
            );
            assert_eq!(format!("{:?}", fixture.store), before);
        }
    }
    for damage in [
        "missing origin",
        "origin namespace",
        "origin type",
        "origin alias",
        "origin import",
        "origin source",
        "origin declaration",
        "origin annotation",
        "source declaration",
        "source parent",
        "source export",
        "namespace export",
        "member row",
        "member vector",
        "property type",
        "property parent",
        "property declaration",
        "alias target",
        "namespace type",
        "annotation",
        "canonical redirect",
        "duplicate property",
        "two-way swap",
    ] {
        let mut changed = states[0].clone();
        match damage {
            "missing origin" => {
                assert_eq!(
                    fixture
                        .store
                        .replace_synthetic_namespace_property_state_for_test(first.property, None),
                    Some(states[0].clone())
                );
            }
            "origin namespace" => changed.origin.namespace = second.namespace,
            "origin type" => changed.origin.namespace_type = second.namespace_type,
            "origin alias" => changed.origin.alias = second.alias,
            "origin import" => changed.origin.originating_import = second.originating_import,
            "origin source" => changed.origin.source = second.alias,
            "origin declaration" => changed.origin.declaration = second.originating_import,
            "origin annotation" => changed.origin.annotation = second.originating_import,
            "source declaration" => {
                assert!(fixture.store.set_symbol_declarations(
                    first.source,
                    Some(vec![second.originating_import]),
                    Some(second.originating_import)
                ));
            }
            "source parent" => {
                assert!(fixture.store.set_symbol_relationships(
                    first.source,
                    source_record.members(),
                    source_record.exports(),
                    Some(second.namespace),
                    source_record.export_symbol()
                ));
            }
            "source export" => {
                assert_eq!(
                    fixture.store.insert_symbol(
                        first.source_exports,
                        EscapedName::source("items"),
                        original
                    ),
                    Some(Some(first.source))
                );
            }
            "namespace export" => {
                assert_eq!(
                    fixture.store.insert_symbol(
                        first.namespace_exports,
                        EscapedName::source("items"),
                        first.property
                    ),
                    Some(Some(first.source))
                );
            }
            "member row" => {
                assert_eq!(
                    fixture.store.insert_symbol(
                        first.namespace_members,
                        EscapedName::source("items"),
                        first.source
                    ),
                    Some(Some(first.property))
                );
            }
            "member vector" => {
                let mut properties = first.namespace_properties.to_vec();
                *properties
                    .iter_mut()
                    .find(|symbol| **symbol == first.property)
                    .unwrap() = first.source;
                assert!(fixture.store.set_structured_type_members(
                    first.namespace_type,
                    Some(first.namespace_members),
                    Some(properties),
                    None,
                    None,
                    None
                ));
            }
            "property type" => {
                let mut links = property_links.clone();
                links.resolved_type = Some(boolean);
                assert!(fixture.store.set_value_symbol_links(first.property, links));
            }
            "property parent" => {
                assert!(fixture.store.set_symbol_relationships(
                    first.property,
                    None,
                    None,
                    Some(original),
                    None
                ));
            }
            "property declaration" => {
                assert!(fixture.store.set_symbol_declarations(
                    first.property,
                    Some(vec![second.originating_import]),
                    None
                ));
            }
            "alias target" => {
                let mut links = alias_links.clone();
                links.alias_target = AliasTargetState::Resolved(second.namespace);
                assert!(fixture.store.set_alias_symbol_links(first.alias, links));
            }
            "namespace type" => {
                let mut links = namespace_links.clone();
                links.resolved_type = Some(second.namespace_type);
                assert!(fixture.store.set_value_symbol_links(first.namespace, links));
            }
            "annotation" => {
                assert!(fixture.store.set_type_node_links(
                    first.annotation,
                    TypeNodeLinks {
                        resolved_type: Some(boolean),
                        ..TypeNodeLinks::default()
                    }
                ));
            }
            "canonical redirect" => {
                assert_eq!(
                    fixture
                        .store
                        .replace_merged_symbol_for_test(first.property, Some(first.source)),
                    None
                );
            }
            "duplicate property" => {
                namespace_identity_set_members(&mut fixture.store, first, second.property)
            }
            "two-way swap" => {
                namespace_identity_set_members(&mut fixture.store, first, second.property);
                namespace_identity_set_members(&mut fixture.store, second, first.property);
            }
            _ => unreachable!(),
        }
        if damage.starts_with("origin ") {
            assert_eq!(
                fixture
                    .store
                    .replace_synthetic_namespace_property_state_for_test(
                        first.property,
                        Some(changed)
                    ),
                Some(states[0].clone())
            );
        }
        let damaged = format!("{:?}", fixture.store);
        let counts = (
            store_state(&fixture.store),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            fixture.store.synthetic_namespace_property_origin_len(),
        );
        {
            let host =
                property_type_import_host(&fixture.files, &fixture.bound, Some(&fixture.manifest));
            for _ in 0..2 {
                assert!(
                    validated_synthetic_namespace_property_source(
                        &fixture.store,
                        &host,
                        first.property
                    )
                    .is_err(),
                    "{damage}"
                );
                assert!(
                    synthetic_namespace_value_property(
                        &fixture.store,
                        first.namespace,
                        first.namespace_type,
                        first.source,
                        if matches!(damage, "duplicate property" | "two-way swap") {
                            second.property
                        } else {
                            first.property
                        },
                        Some(first.array_targets)
                    )
                    .is_err(),
                    "{damage}"
                );
                if matches!(damage, "duplicate property" | "two-way swap") {
                    assert!(
                        validated_synthetic_namespace_property_source(
                            &fixture.store,
                            &host,
                            second.property,
                        )
                        .is_err()
                    );
                    assert!(
                        synthetic_namespace_value_property(
                            &fixture.store,
                            second.namespace,
                            second.namespace_type,
                            second.source,
                            second.property,
                            Some(second.array_targets),
                        )
                        .is_err()
                    );
                }
                assert_eq!(format!("{:?}", fixture.store), damaged, "{damage}");
                assert_eq!(
                    (
                        store_state(&fixture.store),
                        fixture.store.symbol_len(),
                        fixture.store.signature_len(),
                        fixture.store.synthetic_namespace_property_origin_len()
                    ),
                    counts,
                    "{damage}"
                );
            }
        }
        fixture
            .store
            .replace_synthetic_namespace_property_state_for_test(
                first.property,
                Some(states[0].clone()),
            );
        assert!(fixture.store.set_symbol_declarations(
            first.source,
            source_record.declarations().map(<[NodeRef]>::to_vec),
            source_record.value_declaration()
        ));
        assert!(fixture.store.set_symbol_relationships(
            first.source,
            source_record.members(),
            source_record.exports(),
            source_record.parent(),
            source_record.export_symbol()
        ));
        assert!(fixture.store.set_symbol_declarations(
            first.property,
            property_record.declarations().map(<[NodeRef]>::to_vec),
            property_record.value_declaration()
        ));
        assert!(fixture.store.set_symbol_relationships(
            first.property,
            property_record.members(),
            property_record.exports(),
            property_record.parent(),
            property_record.export_symbol()
        ));
        assert!(
            fixture
                .store
                .set_value_symbol_links(first.property, property_links.clone())
        );
        assert!(
            fixture
                .store
                .set_alias_symbol_links(first.alias, alias_links.clone())
        );
        assert!(
            fixture
                .store
                .set_value_symbol_links(first.namespace, namespace_links.clone())
        );
        assert!(
            fixture
                .store
                .set_type_node_links(first.annotation, annotation_links.clone())
        );
        fixture
            .store
            .insert_symbol(
                first.source_exports,
                EscapedName::source("items"),
                first.source,
            )
            .unwrap();
        fixture
            .store
            .insert_symbol(
                first.namespace_exports,
                EscapedName::source("items"),
                first.source,
            )
            .unwrap();
        for origin in &origins {
            assert!(fixture.store.set_structured_type_members(
                origin.namespace_type,
                Some(origin.namespace_members),
                Some(origin.namespace_properties.to_vec()),
                None,
                None,
                None
            ));
            fixture
                .store
                .insert_symbol(
                    origin.namespace_members,
                    EscapedName::source("items"),
                    origin.property,
                )
                .unwrap();
        }
        if damage == "canonical redirect" {
            assert_eq!(
                fixture
                    .store
                    .replace_merged_symbol_for_test(first.property, None),
                Some(first.source)
            );
        }
        let host =
            property_type_import_host(&fixture.files, &fixture.bound, Some(&fixture.manifest));
        for origin in &origins {
            assert_eq!(
                validated_synthetic_namespace_property_source(
                    &fixture.store,
                    &host,
                    origin.property
                ),
                Ok(Some(origin.source)),
                "{damage}"
            );
            assert_eq!(
                synthetic_namespace_value_property(
                    &fixture.store,
                    origin.namespace,
                    origin.namespace_type,
                    origin.source,
                    origin.property,
                    Some(origin.array_targets)
                ),
                Ok(Some(origin.property)),
                "{damage}"
            );
            assert_eq!(
                fixture
                    .store
                    .symbol(origin.property)
                    .unwrap()
                    .declarations(),
                Some(&[origin.declaration][..])
            );
        }
        assert_eq!(format!("{:?}", fixture.store), before, "{damage}");
    }
    namespace_identity_assert_publication_lifecycle();
}
