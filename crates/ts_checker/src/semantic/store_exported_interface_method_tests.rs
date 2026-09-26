use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
};
use ts_parser::{ParseResult, parse_source_file};

use super::*;
use crate::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeMapperStore, DeclaredTypeError,
    DeclaredTypeHost, DeclaredTypeUnavailable, IntrinsicBootstrapOptions,
    declared::get_declared_class_interface_or_type_parameter,
    object_members::{self, PropertyObjectError, ResolvedCallSignatureTypes},
    production::GlobalMergeCompletion,
    type_records::StructuredTypeData,
};

const SOURCE: &str = concat!(
    "export interface LambdaContext {\n",
    "  getRemainingTimeInMillis(): number\n",
    "}\n",
    "export interface OtherContext { getRemainingTimeInMillis(): number }\n",
    "export interface ParameterContext { getRemainingTimeInMillis(value: string): number }\n",
);
const GLOBAL_SOURCE: &str = "interface LambdaContext { getRemainingTimeInMillis(): number }";
const FILE: FileId = FileId::new(286_100);
const GLOBAL_FILE: FileId = FileId::new(286_101);

fn context<'a>(parsed: &'a ParseResult, global: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (parsed, file, name, module) in [
        (
            global,
            GLOBAL_FILE,
            "\"/global.ts\"",
            CanonicalModuleState::Script,
        ),
        (
            parsed,
            FILE,
            "\"/lambda-types.ts\"",
            CanonicalModuleState::External,
        ),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(name),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    module,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(GLOBAL_FILE, &global.arena), (FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

struct Method {
    owner: SemanticSymbolId,
    local: SemanticSymbolId,
    module: SemanticSymbolId,
    owner_declaration: NodeRef,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    return_annotation: NodeRef,
    parameters: Vec<(SemanticSymbolId, NodeRef)>,
}

fn method(parsed: &ParseResult, checker: &CanonicalCheckerContext<'_>, name: &str) -> Method {
    let (owner_declaration, interface) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (identifier.text == name)
                .then_some((NodeRef::new(parsed.arena.id(), FILE, node), interface))
        })
        .unwrap();
    let [declaration] = interface.members.nodes.as_slice() else {
        panic!("each source interface has one method")
    };
    let declaration = NodeRef::new(parsed.arena.id(), FILE, *declaration);
    let NodeData::MethodSignatureDeclaration(data) =
        &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("the source member is a method signature")
    };
    let bound = checker.file(FILE).unwrap().1;
    let owner = bound.symbol(owner_declaration).unwrap();
    let local = bound.local_symbol(owner_declaration).unwrap();
    let module = bound.symbol(bound.source_file()).unwrap();
    let symbol = bound.symbol(declaration).unwrap();
    let parameters = data
        .parameters
        .nodes
        .iter()
        .map(|node| {
            let node = NodeRef::new(parsed.arena.id(), FILE, *node);
            let NodeData::ParameterDeclaration(parameter) =
                &parsed.arena.get(node.node).unwrap().data
            else {
                panic!("the method has an ordinary parameter")
            };
            (
                bound.symbol(node).unwrap(),
                NodeRef::new(parsed.arena.id(), FILE, parameter.type_.unwrap()),
            )
        })
        .collect();
    assert_eq!(checker.store().get_merged_symbol(owner), Some(owner));
    assert_eq!(
        checker
            .store()
            .symbol_store()
            .source_binding_symbols(owner_declaration),
        Some([Some(owner), Some(local)]),
    );
    assert_eq!(
        checker
            .store()
            .symbol_store()
            .source_binding_symbols(declaration),
        Some([Some(symbol), None]),
    );
    Method {
        owner,
        local,
        module,
        owner_declaration,
        declaration,
        symbol,
        return_annotation: NodeRef::new(parsed.arena.id(), FILE, data.type_.unwrap()),
        parameters,
    }
}

#[derive(Debug, Eq, PartialEq)]
struct State {
    counts: [usize; 7],
    links: [usize; 26],
    resolution: (usize, usize),
    records: Vec<String>,
}

fn state(checker: &CanonicalCheckerContext<'_>, methods: &[&Method]) -> State {
    let store = checker.store();
    let mut records = vec![format!("{:?}", checker.diagnostics())];
    records.push(format!(
        "{:?}",
        store.symbol_table(store.intrinsic_bootstrap().unwrap().globals)
    ));
    for method in methods {
        for symbol in [method.owner, method.local, method.module, method.symbol] {
            records.push(format!("{:?}", store.symbol(symbol)));
            records.push(format!("{:?}", store.value_symbol_links(symbol)));
        }
        records.push(format!("{:?}", store.declared_type_links(method.owner)));
        records.push(format!("{:?}", store.signature_links(method.declaration)));
        records.push(format!(
            "{:?}",
            store.type_node_links(method.return_annotation)
        ));
        records.push(format!("{:?}", store.symbol_node_links(method.declaration)));
        for table in [
            store.symbol(method.owner).unwrap().members(),
            store.symbol(method.module).unwrap().exports(),
        ] {
            records.push(format!("{:?}", table.and_then(|id| store.symbol_table(id))));
        }
        for type_ in [
            store
                .declared_type_links(method.owner)
                .and_then(|links| links.declared_type),
            store
                .value_symbol_links(method.symbol)
                .and_then(|links| links.resolved_type),
        ] {
            records.push(format!("{:?}", type_.and_then(|id| store.type_payload(id))));
        }
        if let Some(signature) = store
            .signature_links(method.declaration)
            .and_then(|links| links.resolved_signature.signature())
        {
            records.push(format!("{:?}", store.signature(signature)));
            records.push(format!(
                "{:?}",
                store.callable_signature_parameter_types(signature)
            ));
        }
        for (symbol, annotation) in &method.parameters {
            records.push(format!("{:?}", store.value_symbol_links(*symbol)));
            records.push(format!("{:?}", store.type_node_links(*annotation)));
        }
    }
    State {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.signature_len(),
            store.mapper_len(),
            store.callable_signature_parameter_types_len(),
            checker.diagnostics().len(),
        ],
        links: store.checker_link_allocated_lengths(),
        resolution: (store.type_resolution_len(), store.type_resolution_start()),
        records,
    }
}

fn assert_cold(checker: &CanonicalCheckerContext<'_>, method: &Method) {
    let store = checker.store();
    assert!(store.declared_type_links(method.owner).is_none());
    assert!(store.value_symbol_links(method.symbol).is_none());
    assert!(store.signature_links(method.declaration).is_none());
    assert_eq!(
        store.interface_method_for_declaration(method.declaration),
        None
    );
}

fn assert_method(
    checker: &CanonicalCheckerContext<'_>,
    method: &Method,
    parameter_types: &[TypeId],
) -> (TypeId, TypeId, SignatureId) {
    let store = checker.store();
    let owner = store
        .declared_type_links(method.owner)
        .unwrap()
        .declared_type
        .unwrap();
    let value = store
        .value_symbol_links(method.symbol)
        .unwrap()
        .resolved_type
        .unwrap();
    let signature = store
        .signature_links(method.declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let record = store.signature(signature).unwrap();
    let parameters = method
        .parameters
        .iter()
        .map(|(symbol, _)| *symbol)
        .collect::<Vec<_>>();
    assert_eq!(record.declaration(), Some(method.declaration));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert_eq!(record.parameters(), parameters.as_slice());
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(parameters.len()).unwrap()
    );
    assert_eq!(record.resolved_min_argument_count(), -1);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.this_parameter(), None);
    assert_eq!(
        record.resolved_return_type(),
        Some(store.intrinsic_bootstrap().unwrap().number_type)
    );
    assert_eq!(record.resolved_type_predicate(), None);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.isolated_signature_type(), None);
    assert_eq!(record.composite(), None);
    assert_eq!(
        store.callable_signature_parameter_types(signature),
        Some(parameter_types)
    );
    assert_eq!(
        store.type_payload(value).unwrap().symbol(),
        Some(method.symbol)
    );
    let callable = store
        .type_payload(value)
        .unwrap()
        .data()
        .structured()
        .unwrap();
    assert_eq!(callable.signatures.as_deref(), Some([signature].as_slice()));
    assert_eq!(callable.call_signature_count, 1);
    assert_eq!(
        store.source_direct_type_annotation(method.declaration),
        Some(method.return_annotation)
    );
    assert_eq!(
        store.authenticated_interface_method_owner(method.symbol),
        Some((method.owner, owner))
    );
    assert_eq!(
        store.interface_method_for_declaration(method.declaration),
        Some(method.symbol)
    );
    assert!(store.signature_owns_callable_type(signature));
    assert_eq!(store.interface_method_linked_type(signature), Some(value));
    for ((symbol, _), type_) in method.parameters.iter().zip(parameter_types) {
        assert_eq!(
            store.value_symbol_links(*symbol),
            Some(&ValueSymbolLinks {
                resolved_type: Some(*type_),
                ..ValueSymbolLinks::default()
            })
        );
    }
    assert!(checker.diagnostics().is_empty());
    (owner, value, signature)
}

#[test]
fn exported_parameterless_method_publishes_from_each_cold_entry_and_reuses_its_signature() {
    let parsed = parse_source_file(SOURCE);
    let global = parse_source_file(GLOBAL_SOURCE);
    for first in ["declared", "method", "source"] {
        let mut checker = context(&parsed, &global);
        let method = method(&parsed, &checker, "LambdaContext");
        assert_cold(&checker, &method);
        match first {
            "declared" => {
                checker.get_declared_type_of_symbol(method.owner).unwrap();
            }
            "method" => {
                checker
                    .artifact_interface_method_type(method.symbol)
                    .unwrap();
            }
            "source" => checker.check_source_file(FILE).unwrap(),
            _ => unreachable!(),
        }
        let (owner, value, signature) = assert_method(&checker, &method, &[]);
        assert_eq!(checker.get_declared_type_of_symbol(method.owner), Ok(owner));
        checker.check_source_file(FILE).unwrap();
        let TypeData::Interface(interface) = checker.store().type_payload(owner).unwrap().data()
        else {
            panic!("the real declaration retains an interface type")
        };
        assert!(interface.declared_members_resolved);
        assert_eq!(
            interface.reference.object.structured.properties.as_deref(),
            Some([method.symbol].as_slice())
        );
        let before = state(&checker, &[&method]);
        for _ in 0..2 {
            assert_eq!(
                checker.artifact_interface_method_type(method.symbol),
                Ok(value)
            );
            assert_eq!(checker.get_declared_type_of_symbol(method.owner), Ok(owner));
            assert_eq!(
                checker.get_return_type_of_signature(signature),
                Ok(checker.store().intrinsic_bootstrap().unwrap().number_type)
            );
            checker.check_source_file(FILE).unwrap();
            assert_eq!(
                assert_method(&checker, &method, &[]),
                (owner, value, signature)
            );
            assert_eq!(state(&checker, &[&method]), before);
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Damage {
    MissingMethodOwner,
    MethodOwner,
    MemberEntry,
    ExportEntryAndGlobalEntry,
    LocalExport,
    OptionalFlag,
}

fn restore_relationships(
    store: &mut CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    saved: &Symbol,
) {
    assert!(store.set_symbol_relationships(
        symbol,
        saved.members(),
        saved.exports(),
        saved.parent(),
        saved.export_symbol()
    ));
    assert_eq!(store.symbol(symbol), Some(saved));
}

#[test]
#[allow(clippy::too_many_lines)] // Each real identity change is rejected and exactly restored.
fn exported_method_owner_member_and_export_damage_reject_without_writes() {
    let parsed = parse_source_file(SOURCE);
    let global = parse_source_file(GLOBAL_SOURCE);
    for damage in [
        Damage::MissingMethodOwner,
        Damage::MethodOwner,
        Damage::MemberEntry,
        Damage::ExportEntryAndGlobalEntry,
        Damage::LocalExport,
        Damage::OptionalFlag,
    ] {
        let mut checker = context(&parsed, &global);
        let selected = method(&parsed, &checker, "LambdaContext");
        let other = method(&parsed, &checker, "OtherContext");
        checker.get_declared_type_of_symbol(selected.owner).unwrap();
        checker.get_declared_type_of_symbol(other.owner).unwrap();
        let published = assert_method(&checker, &selected, &[]);
        let other_published = assert_method(&checker, &other, &[]);
        assert_ne!(selected.owner, other.owner);
        assert_ne!(selected.symbol, other.symbol);
        assert_eq!(
            checker
                .store()
                .signature(published.2)
                .unwrap()
                .resolved_return_type(),
            checker
                .store()
                .signature(other_published.2)
                .unwrap()
                .resolved_return_type()
        );
        let saved_method = checker.store().symbol(selected.symbol).unwrap().clone();
        let saved_local = checker.store().symbol(selected.local).unwrap().clone();
        let members = checker
            .store()
            .symbol(selected.owner)
            .unwrap()
            .members()
            .unwrap();
        let exports = checker
            .store()
            .symbol(selected.module)
            .unwrap()
            .exports()
            .unwrap();
        let globals = checker.store().intrinsic_bootstrap().unwrap().globals;
        let original_export = checker
            .store()
            .symbol_table(exports)
            .unwrap()
            .get_source("LambdaContext")
            .unwrap();
        let original_global = checker
            .store()
            .symbol_table(globals)
            .unwrap()
            .get_source("LambdaContext")
            .unwrap();
        assert_eq!(original_export, selected.owner);
        assert_ne!(original_global, selected.owner);
        match damage {
            Damage::MissingMethodOwner => {
                assert!(checker.store_mut_for_test().set_symbol_relationships(
                    selected.symbol,
                    saved_method.members(),
                    saved_method.exports(),
                    None,
                    saved_method.export_symbol()
                ));
            }
            Damage::MethodOwner => assert!(checker.store_mut_for_test().set_symbol_relationships(
                selected.symbol,
                saved_method.members(),
                saved_method.exports(),
                Some(other.owner),
                saved_method.export_symbol()
            )),
            Damage::MemberEntry => assert_eq!(
                checker.store_mut_for_test().insert_symbol(
                    members,
                    EscapedName::source("getRemainingTimeInMillis"),
                    other.symbol
                ),
                Some(Some(selected.symbol))
            ),
            Damage::ExportEntryAndGlobalEntry => {
                assert_eq!(
                    checker.store_mut_for_test().insert_symbol(
                        exports,
                        EscapedName::source("LambdaContext"),
                        other.owner
                    ),
                    Some(Some(original_export))
                );
                assert_eq!(
                    checker.store_mut_for_test().insert_symbol(
                        globals,
                        EscapedName::source("LambdaContext"),
                        selected.owner
                    ),
                    Some(Some(original_global))
                );
                // The old known-symbol check alone does not prove this export row.
                assert_eq!(
                    checker
                        .store()
                        .authenticated_interface_method_owner(selected.symbol),
                    Some((selected.owner, published.0))
                );
            }
            Damage::LocalExport => assert!(checker.store_mut_for_test().set_symbol_relationships(
                selected.local,
                saved_local.members(),
                saved_local.exports(),
                saved_local.parent(),
                Some(other.owner)
            )),
            Damage::OptionalFlag => assert!(checker.store_mut_for_test().set_symbol_flags(
                selected.symbol,
                saved_method.flags() | SymbolFlags::OPTIONAL,
                saved_method.check_flags()
            )),
        }
        let before = state(&checker, &[&selected, &other]);
        let resolution = checker.store().type_resolution_internal_state();
        for _ in 0..2 {
            assert_eq!(
                checker
                    .store()
                    .interface_method_for_declaration(selected.declaration),
                None,
                "{damage:?}"
            );
            assert!(
                !checker.store().signature_owns_callable_type(published.2),
                "{damage:?}"
            );
            assert_eq!(state(&checker, &[&selected, &other]), before, "{damage:?}");
            assert_eq!(checker.store().type_resolution_internal_state(), resolution);
        }
        match damage {
            Damage::MissingMethodOwner | Damage::MethodOwner => {
                restore_relationships(checker.store_mut_for_test(), selected.symbol, &saved_method)
            }
            Damage::MemberEntry => assert_eq!(
                checker.store_mut_for_test().insert_symbol(
                    members,
                    EscapedName::source("getRemainingTimeInMillis"),
                    selected.symbol
                ),
                Some(Some(other.symbol))
            ),
            Damage::ExportEntryAndGlobalEntry => {
                assert_eq!(
                    checker.store_mut_for_test().insert_symbol(
                        exports,
                        EscapedName::source("LambdaContext"),
                        original_export
                    ),
                    Some(Some(other.owner))
                );
                assert_eq!(
                    checker.store_mut_for_test().insert_symbol(
                        globals,
                        EscapedName::source("LambdaContext"),
                        original_global
                    ),
                    Some(Some(selected.owner))
                );
            }
            Damage::LocalExport => {
                restore_relationships(checker.store_mut_for_test(), selected.local, &saved_local)
            }
            Damage::OptionalFlag => assert!(checker.store_mut_for_test().set_symbol_flags(
                selected.symbol,
                saved_method.flags(),
                saved_method.check_flags()
            )),
        }
        assert_eq!(checker.store().symbol(selected.symbol), Some(&saved_method));
        assert_eq!(checker.store().symbol(selected.local), Some(&saved_local));
        assert_eq!(
            checker
                .store()
                .symbol_table(members)
                .unwrap()
                .get_source("getRemainingTimeInMillis"),
            Some(selected.symbol)
        );
        assert_eq!(
            checker
                .store()
                .symbol_table(exports)
                .unwrap()
                .get_source("LambdaContext"),
            Some(original_export)
        );
        assert_eq!(
            checker
                .store()
                .symbol_table(globals)
                .unwrap()
                .get_source("LambdaContext"),
            Some(original_global)
        );
        let restored = state(&checker, &[&selected, &other]);
        assert_eq!(
            checker.artifact_interface_method_type(selected.symbol),
            Ok(published.1)
        );
        assert_eq!(
            checker.get_declared_type_of_symbol(selected.owner),
            Ok(published.0)
        );
        assert_eq!(assert_method(&checker, &selected, &[]), published);
        assert_eq!(state(&checker, &[&selected, &other]), restored);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the actual partial publication and retry state visible.
fn export_damage_at_the_parameter_batch_keeps_partial_methods_unusable_after_restore() {
    let parsed = parse_source_file(SOURCE);
    let global = parse_source_file(GLOBAL_SOURCE);
    for name in ["LambdaContext", "ParameterContext"] {
        let mut checker = context(&parsed, &global);
        let selected = method(&parsed, &checker, name);
        let other = method(&parsed, &checker, "OtherContext");
        assert_cold(&checker, &selected);
        let bound = checker.file(FILE).unwrap().1.clone();
        let global_bound = checker.file(GLOBAL_FILE).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&global.arena, &global_bound), (&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(checker.options().name_resolution),
        )
        .unwrap();
        let plan = object_members::plan_interface(checker.store(), &host, selected.owner).unwrap();
        let flags = checker.store().symbol(selected.owner).unwrap().flags();
        let owner = get_declared_class_interface_or_type_parameter(
            checker.store_mut_for_test(),
            &host,
            selected.owner,
            flags,
        )
        .unwrap()
        .unwrap();
        let parameter_types = selected
            .parameters
            .iter()
            .map(|(_, node)| checker.get_type_from_type_node(*node).unwrap())
            .collect::<Vec<_>>();
        let return_type = checker
            .get_type_from_type_node(selected.return_annotation)
            .unwrap();
        assert_eq!(
            return_type,
            checker.store().intrinsic_bootstrap().unwrap().number_type
        );
        let resolved = [ResolvedCallSignatureTypes {
            parameter_types: parameter_types.clone(),
            return_type,
        }];
        let exports = checker
            .store()
            .symbol(selected.module)
            .unwrap()
            .exports()
            .unwrap();
        let original_export = checker
            .store()
            .symbol_table(exports)
            .unwrap()
            .get_source(name)
            .unwrap();
        assert_eq!(original_export, selected.owner);
        assert_eq!(
            checker
                .store()
                .interface_method_for_declaration(selected.declaration),
            Some(selected.symbol)
        );
        assert_eq!(
            checker.store_mut_for_test().insert_symbol(
                exports,
                EscapedName::source(name),
                other.owner
            ),
            Some(Some(original_export))
        );
        assert_eq!(
            checker
                .store()
                .authenticated_interface_method_owner(selected.symbol),
            Some((selected.owner, owner))
        );
        let before = state(&checker, &[&selected]);
        assert_eq!(
            object_members::publish_interface_method_values(
                checker.store_mut_for_test(),
                &plan,
                &resolved
            ),
            Err(PropertyObjectError::UnsupportedMember {
                node: selected.declaration,
                kind: SyntaxKind::MethodSignature
            }),
        );
        let store = checker.store();
        let value = store
            .value_symbol_links(selected.symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        let signature = store
            .signature_links(selected.declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        assert_eq!(store.type_len(), before.counts[0] + 1);
        assert_eq!(store.signature_len(), before.counts[3] + 1);
        assert_eq!(
            store.callable_signature_parameter_types_len(),
            before.counts[5]
        );
        assert_eq!(store.callable_signature_parameter_types(signature), None);
        assert_eq!(
            store.signature_links(selected.declaration),
            Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            })
        );
        assert_eq!(
            store.value_symbol_links(selected.symbol),
            Some(&ValueSymbolLinks {
                resolved_type: Some(value),
                ..ValueSymbolLinks::default()
            })
        );
        assert_eq!(
            store.type_payload(value).unwrap().symbol(),
            Some(selected.symbol)
        );
        assert_eq!(
            store
                .type_payload(value)
                .unwrap()
                .data()
                .structured()
                .unwrap()
                .signatures
                .as_deref(),
            Some([signature].as_slice())
        );
        assert_eq!(
            store.signature(signature).unwrap().declaration(),
            Some(selected.declaration)
        );
        let signature_record = store.signature(signature).unwrap();
        assert_eq!(signature_record.flags(), SignatureFlags::NONE);
        assert_eq!(
            signature_record.parameters(),
            selected
                .parameters
                .iter()
                .map(|(symbol, _)| *symbol)
                .collect::<Vec<_>>()
                .as_slice()
        );
        assert!(signature_record.type_parameters().is_empty());
        assert_eq!(signature_record.this_parameter(), None);
        assert_eq!(signature_record.target(), None);
        assert_eq!(signature_record.mapper(), None);
        assert_eq!(
            store.signature(signature).unwrap().resolved_return_type(),
            Some(return_type)
        );
        assert_eq!(
            store.signature(signature).unwrap().min_argument_count(),
            i32::try_from(selected.parameters.len()).unwrap()
        );
        for ((symbol, _), type_) in selected.parameters.iter().zip(&parameter_types) {
            assert_eq!(
                store.value_symbol_links(*symbol),
                Some(&ValueSymbolLinks {
                    resolved_type: Some(*type_),
                    ..ValueSymbolLinks::default()
                })
            );
        }
        let TypeData::Interface(interface) = store.type_payload(owner).unwrap().data() else {
            panic!("the normal identity query retains its interface")
        };
        assert!(!interface.declared_members_resolved);
        assert_eq!(
            interface.reference.object.structured,
            StructuredTypeData::default()
        );
        assert!(!store.signature_owns_callable_type(signature));
        assert_eq!(
            checker.store_mut_for_test().insert_symbol(
                exports,
                EscapedName::source(name),
                original_export
            ),
            Some(Some(other.owner))
        );
        assert_eq!(
            checker
                .store()
                .symbol_table(exports)
                .unwrap()
                .get_source(name),
            Some(original_export)
        );
        assert_eq!(
            checker
                .store()
                .interface_method_for_declaration(selected.declaration),
            Some(selected.symbol)
        );
        let partial = state(&checker, &[&selected]);
        for _ in 0..2 {
            assert_eq!(
                checker.artifact_interface_method_type(selected.symbol),
                Err(DeclaredTypeError::Unavailable(
                    DeclaredTypeUnavailable::InvalidInterfaceDeclaration(
                        selected.owner_declaration
                    )
                )),
            );
            assert_eq!(state(&checker, &[&selected]), partial);
        }
        assert_eq!(
            checker
                .store()
                .callable_signature_parameter_types(signature),
            None
        );
        assert!(checker.diagnostics().is_empty());
    }
}
