use crate::semantic::{AliasSymbolLinks, AliasTargetState};

use super::*;

fn alias_snapshot(
    context: &CanonicalCheckerContext<'_>,
    fixture: &Fixture,
) -> impl std::fmt::Debug + PartialEq + use<> {
    (
        snapshot(context, fixture),
        context.store().symbol_table(context.globals()).cloned(),
        format!("{:?}", context.store().source_global_bindings()),
    )
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the invalid lookup, local control, and restoration together.
fn review_standalone_global_alias_keeps_the_requested_name_and_local_owner() {
    let mut failures = Vec::new();
    for consumer in [
        "export = Value;",
        "class Value { local: boolean = true; } export = Value;",
    ] {
        with_sources(
            &[
                (
                    "declare class Value { value: number; } declare class Other { other: string; }",
                    true,
                    CanonicalModuleState::Script,
                ),
                (consumer, false, CanonicalModuleState::External),
            ],
            1,
            |context, fixture| {
                let globals = context.globals();
                let global = context
                    .store()
                    .symbol_table(globals)
                    .unwrap()
                    .get_source("Value")
                    .unwrap();
                let other = context
                    .store()
                    .symbol_table(globals)
                    .unwrap()
                    .get_source("Other")
                    .unwrap();
                let local = fixture.local_table.and_then(|locals| {
                    context
                        .store()
                        .symbol_table(locals)
                        .unwrap()
                        .get_source("Value")
                });
                let expected = local.unwrap_or(global);
                let (declared, value) = identities(context, expected);
                let alias = fixture
                    .nodes
                    .iter()
                    .copied()
                    .find_map(|node| {
                        (node.file == fixture.exported.file
                            && context.store().source_node_kind(node)
                                == Some(ts_ast::SyntaxKind::ExportAssignment))
                        .then(|| context.file(node.file).unwrap().1.symbol(node).unwrap())
                    })
                    .unwrap();
                assert_ne!(global, other);
                assert_eq!(
                    context.store().symbol(global).unwrap().flags(),
                    SymbolFlags::CLASS
                );
                assert_eq!(
                    context.store().symbol(other).unwrap().flags(),
                    SymbolFlags::CLASS
                );
                assert!(
                    context
                        .store_mut_for_test()
                        .set_alias_symbol_links(alias, AliasSymbolLinks::default())
                );
                let healthy = context.resolve_alias(alias).unwrap();
                assert_eq!(healthy.target, AliasTargetState::Resolved(expected));
                assert!(healthy.events.is_empty());
                assert_healthy(context, fixture, expected, declared, value);
                let good_links = context.store().alias_symbol_links(alias).cloned().unwrap();
                let before = alias_snapshot(context, fixture);
                for _ in 0..2 {
                    assert_eq!(context.resolve_alias(alias).unwrap(), healthy);
                    assert_eq!(alias_snapshot(context, fixture), before);
                }

                let store = context.store_mut_for_test();
                assert_eq!(
                    store.insert_symbol(globals, EscapedName::source("Value"), other),
                    Some(Some(global))
                );
                assert!(store.set_alias_symbol_links(alias, AliasSymbolLinks::default()));
                assert!(
                    crate::semantic::classes::global_ambient_class_declaration(
                        store,
                        global,
                        store.symbol(global).unwrap()
                    )
                    .is_none()
                );
                assert!(
                    crate::semantic::classes::global_ambient_class_declaration(
                        store,
                        other,
                        store.symbol(other).unwrap()
                    )
                    .is_some()
                );

                if local.is_some() {
                    let resolved = context.resolve_alias(alias).unwrap();
                    assert_eq!(resolved.target, AliasTargetState::Resolved(expected));
                    assert!(resolved.events.is_empty());
                    let before = alias_snapshot(context, fixture);
                    for _ in 0..2 {
                        assert_eq!(context.resolve_alias(alias).unwrap(), resolved);
                        assert_eq!(alias_snapshot(context, fixture), before);
                    }
                    assert_healthy(context, fixture, expected, declared, value);
                } else {
                    assert!(fixture.local_table.is_none());
                    let damaged = alias_snapshot(context, fixture);
                    for attempt in 0..2 {
                        let actual = context.resolve_alias(alias);
                        eprintln!(
                            "standalone alias review: attempt {attempt}: actual={actual:?}, original={global:?}, substituted={other:?}"
                        );
                        if actual.is_ok() {
                            failures.push(format!("attempt {attempt}: accepted {actual:?}"));
                        }
                        if alias_snapshot(context, fixture) != damaged {
                            failures
                                .push(format!("attempt {attempt}: invalid lookup published state"));
                        }
                    }
                }

                let store = context.store_mut_for_test();
                assert_eq!(
                    store.insert_symbol(globals, EscapedName::source("Value"), global),
                    Some(Some(other))
                );
                assert!(store.set_alias_symbol_links(alias, good_links));
                let restored = alias_snapshot(context, fixture);
                for _ in 0..2 {
                    assert_eq!(context.resolve_alias(alias).unwrap(), healthy);
                    assert_healthy(context, fixture, expected, declared, value);
                    assert_eq!(alias_snapshot(context, fixture), restored);
                }
            },
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
