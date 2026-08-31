use ts_binder::{CanonicalNameResolutionError, CanonicalNameResolverOptions, EscapedNameRef};

use super::*;

const GLOBAL_CLASS: &str = "declare class Value { value: number; }";
const GLOBAL_CONSUMER: &str = "const observed = Value; export = Value;";

fn capture_snapshot(
    context: &CanonicalCheckerContext<'_>,
    fixture: &Fixture,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    let current = store.intrinsic_bootstrap().unwrap().globals;
    (
        snapshot(context, fixture),
        context.globals(),
        current,
        store.symbol_table(context.globals()).cloned(),
        store.symbol_table(current).cloned(),
        format!("{:?}", store.source_global_bindings()),
    )
}

fn record_rejected_reads(
    context: &mut CanonicalCheckerContext<'_>,
    fixture: &Fixture,
    label: &str,
    failures: &mut Vec<String>,
) {
    let before = capture_snapshot(context, fixture);
    for attempt in 0..2 {
        let route = context.export_equals_declared_artifact_type(fixture.exported);
        let actual = context.get_type_at_location(fixture.exported);
        eprintln!(
            "global capture review: {label}, attempt {attempt}: route={route:?}, actual={actual:?}"
        );
        if route.is_ok() || actual.is_ok() {
            failures.push(format!(
                "{label}, attempt {attempt}: route={route:?}, actual={actual:?}"
            ));
        }
        if capture_snapshot(context, fixture) != before {
            failures.push(format!("{label}, attempt {attempt}: query changed state"));
        }
    }
}

#[test]
fn review_global_binding_capture_rejects_replacement_tables_before_cached_reads() {
    for omit_requested_entry in [false, true] {
        with_sources(
            &[
                (GLOBAL_CLASS, true, CanonicalModuleState::Script),
                (GLOBAL_CONSUMER, false, CanonicalModuleState::External),
            ],
            1,
            |context, fixture| {
                let owner = fixture.owner(context, "Value");
                let (declared, value) = identities(context, owner);
                assert_healthy(context, fixture, owner, declared, value);
                let globals = context.globals();
                let entries = context
                    .store()
                    .symbol_table(globals)
                    .unwrap()
                    .iter()
                    .filter(|(name, _)| {
                        !omit_requested_entry || *name != EscapedNameRef::source("Value")
                    })
                    .map(|(name, symbol)| (name.to_owned(), symbol))
                    .collect::<Vec<_>>();
                let original_node = context
                    .store()
                    .type_node_links(fixture.exported)
                    .cloned()
                    .unwrap_or_default();
                let number = context.global_types().number_type;
                let store = context.store_mut_for_test();
                let replacement = store.alloc_symbol_table();
                for (name, symbol) in entries {
                    assert_eq!(store.insert_symbol(replacement, name, symbol), Some(None));
                }
                assert_ne!(replacement, globals);
                assert_eq!(
                    store.symbol_table(replacement).unwrap().get_source("Value"),
                    (!omit_requested_entry).then_some(owner)
                );
                if !omit_requested_entry {
                    assert_eq!(store.symbol_table(replacement), store.symbol_table(globals));
                }
                store.intrinsic_bootstrap.as_mut().unwrap().globals = replacement;
                assert!(store.set_type_node_links(
                    fixture.exported,
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        ..TypeNodeLinks::default()
                    }
                ));

                let before = capture_snapshot(context, fixture);
                let host = context
                    .name_resolver_host(CanonicalNameResolverOptions::default())
                    .unwrap()
                    .with_class_enum_source_validation();
                for table in [globals, replacement] {
                    assert_eq!(
                        host.lookup_name(
                            table,
                            EscapedNameRef::source("Value"),
                            SymbolFlags::VALUE
                        ),
                        Err(CanonicalNameResolutionError::InvalidHostTable(table))
                    );
                    assert_eq!(
                        host.lookup_name(
                            table,
                            EscapedNameRef::source("Absent"),
                            SymbolFlags::VALUE
                        ),
                        Err(CanonicalNameResolutionError::InvalidHostTable(table))
                    );
                }
                assert_eq!(capture_snapshot(context, fixture), before);
                let mut failures = Vec::new();
                record_rejected_reads(
                    context,
                    fixture,
                    if omit_requested_entry {
                        "missing entry in replacement"
                    } else {
                        "identical replacement"
                    },
                    &mut failures,
                );

                let store = context.store_mut_for_test();
                store.intrinsic_bootstrap.as_mut().unwrap().globals = globals;
                assert!(store.set_type_node_links(fixture.exported, original_node));
                let restored = capture_snapshot(context, fixture);
                assert_healthy(context, fixture, owner, declared, value);
                assert_eq!(capture_snapshot(context, fixture), restored);
                assert!(failures.is_empty(), "{}", failures.join("\n"));
            },
        );
    }
}

#[test]
fn review_global_binding_capture_rejects_new_names_before_cached_reads() {
    with_sources(
        &[
            (GLOBAL_CLASS, true, CanonicalModuleState::Script),
            (
                "declare class Absent { hidden: string; } export { Absent };",
                true,
                CanonicalModuleState::External,
            ),
            (
                "declare const marker: number; export = Absent;",
                true,
                CanonicalModuleState::External,
            ),
        ],
        2,
        |context, fixture| {
            let globals = context.globals();
            let absent = fixture.owner(context, "Absent");
            let visible = fixture.owner(context, "Value");
            context.get_nongeneric_class_members(absent).unwrap();
            assert!(context.store().source_symbol_declarations_match(absent));
            assert!(
                context
                    .store()
                    .source_global_bindings()
                    .unwrap()
                    .get(EscapedNameRef::source("Absent"))
                    .is_none()
            );
            let before = capture_snapshot(context, fixture);
            for _ in 0..2 {
                let host = context
                    .name_resolver_host(CanonicalNameResolverOptions::default())
                    .unwrap()
                    .with_class_enum_source_validation();
                assert_eq!(
                    host.lookup_name(
                        globals,
                        EscapedNameRef::source("Absent"),
                        SymbolFlags::VALUE
                    ),
                    Ok(None)
                );
                assert_eq!(
                    context.export_equals_declared_artifact_type(fixture.exported),
                    Ok(None)
                );
                assert!(matches!(context.get_type_at_location(fixture.exported),
                    Err(CanonicalArtifactQueryError::MissingType { node, .. }) if node == fixture.exported));
                assert_eq!(capture_snapshot(context, fixture), before);
            }

            let number = context.global_types().number_type;
            let store = context.store_mut_for_test();
            assert_eq!(
                store.insert_symbol(globals, EscapedName::source("Absent"), absent),
                Some(None)
            );
            assert!(store.set_type_node_links(
                fixture.exported,
                TypeNodeLinks {
                    resolved_type: Some(number),
                    ..TypeNodeLinks::default()
                }
            ));
            assert!(store.set_symbol_node_links(
                fixture.exported,
                SymbolNodeLinks {
                    resolved_symbol: Some(absent)
                }
            ));
            let before = capture_snapshot(context, fixture);
            assert!(
                !context
                    .store_mut_for_test()
                    .record_source_global_bindings(globals)
            );
            assert_eq!(capture_snapshot(context, fixture), before);
            let host = context
                .name_resolver_host(CanonicalNameResolverOptions::default())
                .unwrap()
                .with_class_enum_source_validation();
            assert_eq!(
                host.lookup_name(
                    globals,
                    EscapedNameRef::source("Absent"),
                    SymbolFlags::VALUE
                ),
                Err(CanonicalNameResolutionError::InvalidHostSymbol(absent))
            );
            assert_eq!(
                host.lookup_name(globals, EscapedNameRef::source("Value"), SymbolFlags::VALUE),
                Ok(Some(visible))
            );
            let mut failures = Vec::new();
            record_rejected_reads(context, fixture, "new name", &mut failures);
            assert!(failures.is_empty(), "{}", failures.join("\n"));
        },
    );
}

#[test]
fn review_global_binding_capture_keeps_local_shadows_independent() {
    for replace_table in [false, true] {
        with_sources(
            &[
                (GLOBAL_CLASS, true, CanonicalModuleState::Script),
                (CLASS_SOURCE, false, CanonicalModuleState::External),
            ],
            1,
            |context, fixture| {
                let globals = context.globals();
                let bound = context.file(fixture.exported.file).unwrap().1;
                let locals = bound.locals(bound.source_file()).unwrap();
                let local = context
                    .store()
                    .symbol_table(locals)
                    .unwrap()
                    .get_source("Value")
                    .unwrap();
                let global = context
                    .store()
                    .symbol_table(globals)
                    .unwrap()
                    .get_source("Value")
                    .unwrap();
                assert_ne!(local, global);
                let other = fixture.owner(context, "Other");
                let (declared, value) = identities(context, local);
                assert_healthy(context, fixture, local, declared, value);

                let store = context.store_mut_for_test();
                if replace_table {
                    let replacement = store.alloc_symbol_table();
                    store.intrinsic_bootstrap.as_mut().unwrap().globals = replacement;
                } else {
                    assert_eq!(
                        store.insert_symbol(globals, EscapedName::source("Value"), other),
                        Some(Some(global))
                    );
                }
                let changed = capture_snapshot(context, fixture);
                assert_healthy(context, fixture, local, declared, value);
                assert_eq!(capture_snapshot(context, fixture), changed);

                let store = context.store_mut_for_test();
                if replace_table {
                    store.intrinsic_bootstrap.as_mut().unwrap().globals = globals;
                } else {
                    assert_eq!(
                        store.insert_symbol(globals, EscapedName::source("Value"), global),
                        Some(Some(other))
                    );
                }
                let restored = capture_snapshot(context, fixture);
                assert_healthy(context, fixture, local, declared, value);
                assert_eq!(capture_snapshot(context, fixture), restored);
            },
        );
    }
}

#[test]
fn review_global_binding_capture_records_initialized_bindings_in_source_order() {
    for namespace_first in [false, true] {
        let class = (
            "declare class Value { value: number; } interface Shared { first: string; }",
            true,
            CanonicalModuleState::Script,
        );
        let namespace = (
            "declare namespace Value {}",
            true,
            CanonicalModuleState::Script,
        );
        let scripts = if namespace_first {
            [namespace, class]
        } else {
            [class, namespace]
        };
        with_sources(
            &[
                scripts[0],
                scripts[1],
                (
                    "export {}; declare global { interface Shared { second: number; } interface Added {} }",
                    true,
                    CanonicalModuleState::External,
                ),
                (
                    "export as namespace Umd; export {};",
                    true,
                    CanonicalModuleState::External,
                ),
                (GLOBAL_CONSUMER, false, CanonicalModuleState::External),
            ],
            4,
            |context, fixture| {
                let owner = fixture.owner(context, "Value");
                let (declared, value) = identities(context, owner);
                assert_healthy(context, fixture, owner, declared, value);
                let before = capture_snapshot(context, fixture);
                let store = context.store();
                let retained = store.source_global_bindings().unwrap();
                assert_eq!(retained.table, context.globals());
                let host = context
                    .name_resolver_host(CanonicalNameResolverOptions::default())
                    .unwrap()
                    .with_class_enum_source_validation();
                for name in ["Value", "Shared", "Added", "Umd", "undefined"] {
                    let key = EscapedNameRef::source(name);
                    let raw = store
                        .symbol_table(context.globals())
                        .unwrap()
                        .get(key)
                        .unwrap();
                    let symbol = store.get_merged_symbol(raw).unwrap();
                    let saved = retained.get(key).unwrap();
                    assert_eq!(saved.table_symbol, raw, "{name}");
                    assert_eq!(saved.symbol, symbol, "{name}");
                    assert_eq!(saved.flags, store.symbol(symbol).unwrap().flags(), "{name}");
                    assert_eq!(
                        host.lookup_name(context.globals(), key, SymbolFlags::ALL),
                        Ok(Some(symbol)),
                        "{name}"
                    );
                }
                let declarations = store.symbol(owner).unwrap().declarations().unwrap();
                assert_eq!(declarations.len(), 2);
                assert_eq!(declarations[0].file, fixture.files[0]);
                assert_eq!(declarations[1].file, fixture.files[1]);
                assert_eq!(capture_snapshot(context, fixture), before);
            },
        );
    }
}

#[test]
fn review_global_binding_capture_refuses_repeated_capture_without_writes() {
    with_sources(
        &[
            (GLOBAL_CLASS, true, CanonicalModuleState::Script),
            (GLOBAL_CONSUMER, false, CanonicalModuleState::External),
        ],
        1,
        |context, fixture| {
            let globals = context.globals();
            let owner = fixture.owner(context, "Value");
            let (declared, value) = identities(context, owner);
            assert_healthy(context, fixture, owner, declared, value);
            let duplicate = context
                .store_mut_for_test()
                .clone_symbol_table(globals)
                .unwrap();
            for current in [globals, duplicate] {
                context
                    .store_mut_for_test()
                    .intrinsic_bootstrap
                    .as_mut()
                    .unwrap()
                    .globals = current;
                let before = capture_snapshot(context, fixture);
                for _ in 0..2 {
                    for requested in [globals, duplicate] {
                        assert!(
                            !context
                                .store_mut_for_test()
                                .record_source_global_bindings(requested)
                        );
                        assert_eq!(capture_snapshot(context, fixture), before);
                    }
                }
            }
            context
                .store_mut_for_test()
                .intrinsic_bootstrap
                .as_mut()
                .unwrap()
                .globals = globals;
            let record = context.store().symbol(owner).unwrap();
            let flags = record.flags();
            let check_flags = record.check_flags();
            assert!(context.store_mut_for_test().set_symbol_flags(
                owner,
                SymbolFlags::TYPE_ALIAS,
                check_flags
            ));
            let before = capture_snapshot(context, fixture);
            assert!(
                !context
                    .store_mut_for_test()
                    .record_source_global_bindings(globals)
            );
            assert_eq!(capture_snapshot(context, fixture), before);
            assert_eq!(
                context
                    .store()
                    .source_global_bindings()
                    .unwrap()
                    .get(EscapedNameRef::source("Value"))
                    .unwrap()
                    .flags,
                flags
            );
            assert!(
                context
                    .store_mut_for_test()
                    .set_symbol_flags(owner, flags, check_flags)
            );
            let restored = capture_snapshot(context, fixture);
            assert_healthy(context, fixture, owner, declared, value);
            assert_eq!(capture_snapshot(context, fixture), restored);
        },
    );
}

#[test]
fn review_global_binding_capture_keeps_exports_valid_after_ambient_module_checks() {
    for check_order in [[1, 2], [2, 1]] {
        with_sources(
            &[
                (GLOBAL_CLASS, true, CanonicalModuleState::Script),
                (
                    "declare module 'pkg' { export interface First {} }",
                    true,
                    CanonicalModuleState::Script,
                ),
                (
                    "declare module 'pkg' { export interface Second {} }",
                    true,
                    CanonicalModuleState::Script,
                ),
                (GLOBAL_CONSUMER, false, CanonicalModuleState::External),
            ],
            3,
            |context, fixture| {
                let globals = context.globals();
                let module_name = EscapedNameRef::source("\"pkg\"");
                let owner = fixture.owner(context, "Value");
                let (declared, value) = identities(context, owner);
                assert_healthy(context, fixture, owner, declared, value);
                {
                    let store = context.store();
                    let source_modules = [1, 2].map(|index| {
                        let (_, bound) = context.file(fixture.files[index]).unwrap();
                        let locals = bound.locals(bound.source_file()).unwrap();
                        store
                            .symbol_table(locals)
                            .unwrap()
                            .get(module_name)
                            .unwrap()
                    });
                    assert_ne!(source_modules[0], source_modules[1]);
                    let module = store.get_merged_symbol(source_modules[0]).unwrap();
                    assert_eq!(store.get_merged_symbol(source_modules[1]), Some(module));

                    let raw = store
                        .symbol_table(globals)
                        .unwrap()
                        .get(module_name)
                        .unwrap();
                    assert_eq!(store.get_merged_symbol(raw), Some(module));
                    let record = store.symbol(module).unwrap();
                    assert_eq!(record.name(), module_name);

                    let captured = store.source_global_bindings().unwrap();
                    assert_eq!(captured.table, globals);
                    let binding = captured.get(module_name).unwrap();
                    assert_eq!(binding.table_symbol, raw);
                    assert_eq!(binding.symbol, module);
                    assert_eq!(binding.flags, record.flags());
                    assert_eq!(binding.declarations(), record.declarations());
                }
                let retained = format!("{:?}", context.store().source_global_bindings());
                for index in check_order {
                    context.check_source_file(fixture.files[index]).unwrap();
                    assert!(
                        context.diagnostics().is_empty(),
                        "{:?}",
                        context.diagnostics()
                    );
                    assert_eq!(
                        format!("{:?}", context.store().source_global_bindings()),
                        retained
                    );
                    let before = capture_snapshot(context, fixture);
                    assert_healthy(context, fixture, owner, declared, value);
                    let raw = context
                        .store()
                        .symbol_table(globals)
                        .unwrap()
                        .get(module_name)
                        .unwrap();
                    let module = context.store().get_merged_symbol(raw).unwrap();
                    let host = context
                        .name_resolver_host(CanonicalNameResolverOptions::default())
                        .unwrap();
                    assert_eq!(
                        host.lookup_name(globals, module_name, SymbolFlags::NAMESPACE),
                        Ok(Some(module))
                    );
                    eprintln!(
                        "global capture review: ambient module after file {index}: guarded={:?}",
                        host.with_class_enum_source_validation().lookup_name(
                            globals,
                            module_name,
                            SymbolFlags::NAMESPACE
                        )
                    );
                    assert_eq!(capture_snapshot(context, fixture), before);
                }
                let module = context
                    .store()
                    .symbol_table(globals)
                    .unwrap()
                    .get(module_name)
                    .and_then(|symbol| context.store().get_merged_symbol(symbol))
                    .unwrap();
                let exports = context.store().symbol(module).unwrap().exports().unwrap();
                let exports = context.store().symbol_table(exports).unwrap();
                assert!(exports.get_source("First").is_some());
                assert!(exports.get_source("Second").is_some());
            },
        );
    }
}
