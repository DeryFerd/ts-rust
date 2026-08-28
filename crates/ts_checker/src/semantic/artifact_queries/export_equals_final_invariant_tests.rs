use std::collections::HashSet;

use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags, SymbolTableId,
};
use ts_parser::{ParseResult, parse_source_file};

use super::{CanonicalArtifactQueryError, CanonicalCheckerContext};
use crate::semantic::{
    CanonicalCheckerOptions, DeclaredTypeLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks,
    ValueSymbolLinks,
};

const CLASS_SOURCE: &str = concat!(
    "class Value { value: number = 1; } ",
    "class Other { other: string = 'other'; } ",
    "const observed = Value; export = Value;",
);
const ENUM_SOURCE: &str = concat!(
    "enum Value { One = 0, Two = 1 } ",
    "enum Other { One = 10, Two = 20 } ",
    "const observed = Value; export = Value;",
);

struct Fixture {
    files: Vec<FileId>,
    nodes: Vec<NodeRef>,
    owners: Vec<SemanticSymbolId>,
    tables: Vec<SymbolTableId>,
    local_table: SymbolTableId,
    exported: NodeRef,
    read: Option<NodeRef>,
}

impl Fixture {
    fn owner(&self, context: &CanonicalCheckerContext<'_>, name: &str) -> SemanticSymbolId {
        self.owners
            .iter()
            .copied()
            .find(|owner| context.store().symbol(*owner).unwrap().name().as_utf8() == Some(name))
            .and_then(|owner| context.store().get_merged_symbol(owner))
            .unwrap()
    }
}

fn with_source(
    text: &str,
    declaration_file: bool,
    check: impl FnOnce(&mut CanonicalCheckerContext<'_>, &Fixture),
) {
    with_sources(
        &[(text, declaration_file, CanonicalModuleState::External)],
        0,
        check,
    );
}

fn with_sources(
    inputs: &[(&str, bool, CanonicalModuleState)],
    queried_file: usize,
    check: impl FnOnce(&mut CanonicalCheckerContext<'_>, &Fixture),
) {
    let parsed = inputs
        .iter()
        .map(|(text, _, _)| {
            let parsed = parse_source_file(text);
            assert!(
                parsed.diagnostics.is_empty(),
                "{text}: {:?}",
                parsed.diagnostics
            );
            parsed
        })
        .collect::<Vec<_>>();
    let files = (0..inputs.len())
        .map(|index| FileId::new(148_100 + u32::try_from(index).unwrap()))
        .collect::<Vec<_>>();
    let mut binder = CanonicalBinder::new();
    for ((source, file), (_, declaration_file, module_state)) in
        parsed.iter().zip(&files).zip(inputs)
    {
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                *file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/project/export-review-{}.ts\"", file.index())),
                    CanonicalSourceLanguage::TypeScript,
                    *declaration_file,
                    *module_state,
                ),
            )
            .unwrap();
    }
    for (source, file) in parsed.iter().zip(&files) {
        binder
            .bind_typescript_declaration_slice(&source.arena, *file)
            .unwrap();
    }
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        parsed
            .iter()
            .zip(&files)
            .map(|(source, file)| (*file, &source.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();
    for ((text, declaration_file, _), file) in inputs.iter().zip(&files) {
        if !declaration_file {
            context
                .check_source_file(*file)
                .unwrap_or_else(|error| panic!("{text}: {error:?}"));
        }
    }
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let fixture = fixture(&context, &parsed, &files, queried_file);
    check(&mut context, &fixture);
}

fn fixture(
    context: &CanonicalCheckerContext<'_>,
    parsed: &[ParseResult],
    files: &[FileId],
    queried_file: usize,
) -> Fixture {
    let source = &parsed[queried_file];
    let file = files[queried_file];
    let reference = |node| NodeRef::new(source.arena.id(), file, node);
    let exported = source
        .arena
        .iter()
        .find_map(|(_, node)| {
            let NodeData::ExportAssignment(export) = &node.data else {
                return None;
            };
            Some(reference(export.expression))
        })
        .unwrap();
    let read = source.arena.iter().find_map(|(_, node)| {
        let NodeData::VariableDeclaration(variable) = &node.data else {
            return None;
        };
        matches!(&source.arena.get(variable.name).unwrap().data,
            NodeData::Identifier(identifier) if identifier.text == "observed")
        .then(|| reference(variable.initializer.unwrap()))
    });
    let nodes = parsed
        .iter()
        .zip(files)
        .flat_map(|(source, file)| {
            source
                .arena
                .iter()
                .map(move |(node, _)| NodeRef::new(source.arena.id(), *file, node))
        })
        .collect::<Vec<_>>();
    let mut seen = HashSet::new();
    let owners = nodes
        .iter()
        .filter_map(|node| context.file(node.file).unwrap().1.symbol(*node))
        .flat_map(|owner| [owner, context.store().get_merged_symbol(owner).unwrap()])
        .filter(|owner| seen.insert(*owner))
        .collect();
    let tables = parsed
        .iter()
        .zip(files)
        .filter_map(|(source, file)| {
            context.file(*file).unwrap().1.locals(NodeRef::new(
                source.arena.id(),
                *file,
                source.source_file,
            ))
        })
        .collect::<Vec<_>>();
    let local_table = context
        .file(file)
        .unwrap()
        .1
        .locals(reference(source.source_file))
        .unwrap();
    Fixture {
        files: files.to_vec(),
        nodes,
        owners,
        tables,
        local_table,
        exported,
        read,
    }
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    fixture: &Fixture,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    let mut types = fixture
        .owners
        .iter()
        .flat_map(|owner| {
            [
                store
                    .declared_type_links(*owner)
                    .and_then(|links| links.declared_type),
                store
                    .value_symbol_links(*owner)
                    .and_then(|links| links.resolved_type),
            ]
            .into_iter()
            .flatten()
        })
        .collect::<Vec<_>>();
    let this_types = types
        .iter()
        .filter_map(|type_| {
            let TypeData::Interface(interface) = store.type_payload(*type_)?.data() else {
                return None;
            };
            interface.this_type
        })
        .collect::<Vec<_>>();
    types.extend(this_types);
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.symbol_store().symbol_table_len(),
            store.merged_symbol_len(),
        ],
        store.checker_link_allocated_lengths(),
        store.relation_state_snapshot(),
        fixture
            .files
            .iter()
            .map(|file| {
                store
                    .source_file_links(context.source_file(*file).unwrap())
                    .cloned()
            })
            .collect::<Vec<_>>(),
        context.diagnostics().as_slice().to_vec(),
        fixture
            .owners
            .iter()
            .map(|owner| {
                let record = store.symbol(*owner).unwrap();
                (
                    *owner,
                    (
                        store.get_merged_symbol(*owner),
                        record.flags(),
                        record.check_flags(),
                        record.parent(),
                        record.export_symbol(),
                        record.members(),
                        record.exports(),
                        record.declarations().map(<[_]>::to_vec),
                        record.value_declaration(),
                    ),
                    (
                        store.declared_type_links(*owner).cloned(),
                        store.value_symbol_links(*owner).cloned(),
                        store.alias_symbol_links(*owner).cloned(),
                        store.module_symbol_links(*owner).cloned(),
                        store.declared_value_provenance(*owner),
                    ),
                )
            })
            .collect::<Vec<_>>(),
        fixture
            .nodes
            .iter()
            .map(|node| {
                (
                    *node,
                    store.type_node_links(*node).cloned(),
                    store.symbol_node_links(*node).cloned(),
                    store.node_links(*node).cloned(),
                    store.enum_member_links(*node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        fixture
            .tables
            .iter()
            .map(|table| {
                (
                    *table,
                    store
                        .symbol_table(*table)
                        .unwrap()
                        .iter()
                        .map(|(name, symbol)| (name.to_owned(), symbol))
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>(),
        // Type records do not implement Clone. Keep their complete debug state in the snapshot.
        types
            .into_iter()
            .map(|type_| (type_, format!("{:?}", store.type_payload(type_))))
            .collect::<Vec<_>>(),
    )
}

fn identities(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> (TypeId, TypeId) {
    let declared = context
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap();
    let value = context
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_ne!(declared, value);
    (declared, value)
}

fn assert_healthy(
    context: &mut CanonicalCheckerContext<'_>,
    fixture: &Fixture,
    owner: SemanticSymbolId,
    declared: TypeId,
    value: TypeId,
) {
    let before = snapshot(context, fixture);
    for _ in 0..2 {
        assert_eq!(
            context.export_equals_declared_artifact_type(fixture.exported),
            Ok(Some(declared))
        );
        assert_eq!(context.get_type_at_location(fixture.exported), Ok(declared));
        assert_eq!(
            context.get_symbol_at_location(fixture.exported),
            Ok(Some(owner))
        );
        if let Some(read) = fixture.read {
            assert_eq!(context.export_equals_declared_artifact_type(read), Ok(None));
            assert_eq!(context.get_type_at_location(read), Ok(value));
        }
        assert_eq!(snapshot(context, fixture), before);
    }
}

#[test]
fn export_equals_final_invariant_checked_reads_keep_both_identities() {
    for text in [CLASS_SOURCE, ENUM_SOURCE] {
        with_source(text, false, |context, fixture| {
            let owner = fixture.owner(context, "Value");
            let (declared, value) = identities(context, owner);
            assert_healthy(context, fixture, owner, declared, value);
            context.recheck_source_file(fixture.files[0]).unwrap();
            assert_healthy(context, fixture, owner, declared, value);
        });
    }
}

#[test]
fn export_equals_final_invariant_cold_declarations_do_not_publish() {
    for text in [
        "declare class Value { value: number; } export = Value;",
        "declare enum Value { One = 0, Two = 1 } export = Value;",
    ] {
        with_source(text, true, |context, fixture| {
            let owner = fixture.owner(context, "Value");
            assert!(context.store().declared_type_links(owner).is_none());
            assert!(context.store().value_symbol_links(owner).is_none());
            let before = snapshot(context, fixture);
            for _ in 0..2 {
                assert_eq!(
                    context.export_equals_declared_artifact_type(fixture.exported),
                    Ok(None)
                );
                assert!(matches!(context.get_type_at_location(fixture.exported),
                    Err(CanonicalArtifactQueryError::MissingType { node, .. }) if node == fixture.exported));
                assert_eq!(context.get_symbol_at_location(fixture.exported), Ok(None));
                assert_eq!(snapshot(context, fixture), before);
            }
        });
    }
}

#[derive(Clone, Copy, Debug)]
enum OwnerChange {
    Parent,
    Flags,
    CheckFlags,
    Members,
    ExportSymbol,
    ValueDeclaration,
    Declarations,
    DeclarationsAndCaches,
    LexicalTarget,
    LexicalTargetAndCaches,
}

#[allow(clippy::too_many_lines)] // Keep each changed owner, failed read, and restoration together.
fn check_owner_changes(text: &str) {
    let mut failures = Vec::new();
    for change in [
        OwnerChange::Parent,
        OwnerChange::Flags,
        OwnerChange::CheckFlags,
        OwnerChange::Members,
        OwnerChange::ExportSymbol,
        OwnerChange::ValueDeclaration,
        OwnerChange::Declarations,
        OwnerChange::DeclarationsAndCaches,
        OwnerChange::LexicalTarget,
        OwnerChange::LexicalTargetAndCaches,
    ] {
        with_source(text, false, |context, fixture| {
            let owner = fixture.owner(context, "Value");
            let other = fixture.owner(context, "Other");
            let (declared, value) = identities(context, owner);
            let (other_declared, other_value) = identities(context, other);
            assert_healthy(context, fixture, owner, declared, value);
            let record = context.store().symbol(owner).unwrap();
            let (flags, check_flags, members, exports, parent, export_symbol) = (
                record.flags(),
                record.check_flags(),
                record.members(),
                record.exports(),
                record.parent(),
                record.export_symbol(),
            );
            let declarations = record.declarations().unwrap().to_vec();
            let value_declaration = record.value_declaration();
            let other_record = context.store().symbol(other).unwrap();
            let other_declarations = other_record.declarations().unwrap().to_vec();
            let other_value_declaration = other_record.value_declaration();
            let other_members = other_record.members();
            let other_exports = other_record.exports();
            let declared_links = context.store().declared_type_links(owner).cloned().unwrap();
            let value_links = context.store().value_symbol_links(owner).cloned().unwrap();
            let node_links = context
                .store()
                .type_node_links(fixture.exported)
                .cloned()
                .unwrap_or_default();
            let symbol_links = context
                .store()
                .symbol_node_links(fixture.exported)
                .cloned()
                .unwrap_or_default();
            let local = context
                .store()
                .symbol_table(fixture.local_table)
                .unwrap()
                .get_source("Value")
                .unwrap();
            let before_change = snapshot(context, fixture);
            let store = context.store_mut_for_test();
            match change {
                OwnerChange::Parent => assert!(store.set_symbol_relationships(
                    owner,
                    members,
                    exports,
                    Some(other),
                    export_symbol
                )),
                OwnerChange::Flags => assert!(store.set_symbol_flags(
                    owner,
                    flags | SymbolFlags::INTERFACE,
                    check_flags
                )),
                OwnerChange::CheckFlags => {
                    if !store.set_symbol_flags(owner, flags, check_flags | CheckFlags::READONLY) {
                        assert_eq!(snapshot(context, fixture), before_change);
                        assert_healthy(context, fixture, owner, declared, value);
                        eprintln!("export owner review: CheckFlags rejected by the symbol store");
                        return;
                    }
                }
                OwnerChange::Members => {
                    let (changed_members, changed_exports) = if flags.intersects(SymbolFlags::ENUM)
                    {
                        assert_ne!(exports, other_exports);
                        (members, other_exports)
                    } else {
                        assert_ne!(members, other_members);
                        (other_members, exports)
                    };
                    assert!(store.set_symbol_relationships(
                        owner,
                        changed_members,
                        changed_exports,
                        parent,
                        export_symbol
                    ));
                }
                OwnerChange::ExportSymbol => assert!(store.set_symbol_relationships(
                    owner,
                    members,
                    exports,
                    parent,
                    Some(other)
                )),
                OwnerChange::ValueDeclaration => assert!(store.set_symbol_declarations(
                    owner,
                    Some(declarations.clone()),
                    other_value_declaration
                )),
                OwnerChange::Declarations | OwnerChange::DeclarationsAndCaches => {
                    assert!(store.set_symbol_declarations(
                        owner,
                        Some(other_declarations),
                        other_value_declaration
                    ));
                    if matches!(change, OwnerChange::DeclarationsAndCaches) {
                        assert!(store.set_declared_type_links(
                            owner,
                            DeclaredTypeLinks {
                                declared_type: Some(other_declared),
                                ..DeclaredTypeLinks::default()
                            }
                        ));
                        assert!(store.set_value_symbol_links(
                            owner,
                            ValueSymbolLinks {
                                resolved_type: Some(other_value),
                                ..ValueSymbolLinks::default()
                            }
                        ));
                        assert!(store.set_type_node_links(
                            fixture.exported,
                            TypeNodeLinks {
                                resolved_type: Some(other_declared),
                                ..TypeNodeLinks::default()
                            }
                        ));
                        assert!(store.set_symbol_node_links(
                            fixture.exported,
                            SymbolNodeLinks {
                                resolved_symbol: Some(other)
                            }
                        ));
                    }
                }
                OwnerChange::LexicalTarget | OwnerChange::LexicalTargetAndCaches => {
                    assert_eq!(
                        store.insert_symbol(
                            fixture.local_table,
                            EscapedName::source("Value"),
                            other
                        ),
                        Some(Some(local))
                    );
                    if matches!(change, OwnerChange::LexicalTargetAndCaches) {
                        assert!(store.set_type_node_links(
                            fixture.exported,
                            TypeNodeLinks {
                                resolved_type: Some(other_declared),
                                ..TypeNodeLinks::default()
                            }
                        ));
                        assert!(store.set_symbol_node_links(
                            fixture.exported,
                            SymbolNodeLinks {
                                resolved_symbol: Some(other)
                            }
                        ));
                    }
                }
            }
            let before = snapshot(context, fixture);
            for attempt in 0..2 {
                let route = context.export_equals_declared_artifact_type(fixture.exported);
                let actual = context.get_type_at_location(fixture.exported);
                eprintln!(
                    "export owner review: {change:?}, attempt {attempt}: route={route:?}, actual={actual:?}, expected={declared:?}"
                );
                if actual.is_ok() || route.is_ok() {
                    failures.push(format!(
                        "{change:?}, attempt {attempt}: accepted {actual:?}, route={route:?}"
                    ));
                }
                if snapshot(context, fixture) != before {
                    failures.push(format!(
                        "{change:?}, attempt {attempt}: query changed state"
                    ));
                }
            }
            let store = context.store_mut_for_test();
            assert!(store.set_symbol_flags(owner, flags, check_flags));
            assert!(store.set_symbol_relationships(owner, members, exports, parent, export_symbol));
            assert!(store.set_symbol_declarations(owner, Some(declarations), value_declaration));
            assert!(store.set_declared_type_links(owner, declared_links));
            assert!(store.set_value_symbol_links(owner, value_links));
            assert!(store.set_type_node_links(fixture.exported, node_links));
            assert!(store.set_symbol_node_links(fixture.exported, symbol_links));
            assert!(
                store
                    .insert_symbol(fixture.local_table, EscapedName::source("Value"), local)
                    .is_some()
            );
            assert_healthy(context, fixture, owner, declared, value);
        });
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn export_equals_final_invariant_class_owners_follow_bound_source() {
    check_owner_changes(CLASS_SOURCE);
}

#[test]
fn export_equals_final_invariant_enum_owners_follow_bound_source() {
    check_owner_changes(ENUM_SOURCE);
}

#[derive(Clone, Copy, Debug)]
enum CacheChange {
    MissingDeclared,
    OtherDeclared,
    ValueAsDeclared,
    OtherDeclaredAndNode,
    OtherSymbolAndNode,
    OtherSymbol,
    ValueNode,
    OtherNode,
    RetargetedClass,
}

#[allow(clippy::too_many_lines)] // Check borrowed caches and their recovery in the same fixture.
fn check_declared_cache_changes(text: &str, class: bool) {
    let mut failures = Vec::new();
    for change in [
        CacheChange::MissingDeclared,
        CacheChange::OtherDeclared,
        CacheChange::ValueAsDeclared,
        CacheChange::OtherDeclaredAndNode,
        CacheChange::OtherSymbolAndNode,
        CacheChange::OtherSymbol,
        CacheChange::ValueNode,
        CacheChange::OtherNode,
        CacheChange::RetargetedClass,
    ] {
        if matches!(change, CacheChange::RetargetedClass) && !class {
            continue;
        }
        with_source(text, false, |context, fixture| {
            let owner = fixture.owner(context, "Value");
            let other = fixture.owner(context, "Other");
            let (declared, value) = identities(context, owner);
            let (other_declared, _) = identities(context, other);
            assert_healthy(context, fixture, owner, declared, value);
            let original = context.store().declared_type_links(owner).cloned().unwrap();
            let type_node = context
                .store()
                .type_node_links(fixture.exported)
                .cloned()
                .unwrap_or_default();
            let symbol_node = context
                .store()
                .symbol_node_links(fixture.exported)
                .cloned()
                .unwrap_or_default();
            let other_this = match context.store().type_payload(other_declared).unwrap().data() {
                TypeData::Interface(interface) => interface.this_type,
                _ => None,
            };
            let store = context.store_mut_for_test();
            match change {
                CacheChange::MissingDeclared => {
                    assert!(store.set_declared_type_links(owner, DeclaredTypeLinks::default()))
                }
                CacheChange::OtherDeclared
                | CacheChange::OtherDeclaredAndNode
                | CacheChange::RetargetedClass => {
                    assert!(store.set_declared_type_links(
                        owner,
                        DeclaredTypeLinks {
                            declared_type: Some(other_declared),
                            ..DeclaredTypeLinks::default()
                        }
                    ));
                    if !matches!(change, CacheChange::OtherDeclared) {
                        assert!(store.set_type_node_links(
                            fixture.exported,
                            TypeNodeLinks {
                                resolved_type: Some(other_declared),
                                ..TypeNodeLinks::default()
                            }
                        ));
                    }
                    if matches!(change, CacheChange::RetargetedClass) {
                        assert!(store.set_type_symbol(other_declared, Some(owner)));
                        assert!(store.set_type_symbol(other_this.unwrap(), Some(owner)));
                        assert!(store.set_symbol_node_links(
                            fixture.exported,
                            SymbolNodeLinks {
                                resolved_symbol: Some(owner)
                            }
                        ));
                    }
                }
                CacheChange::ValueAsDeclared => assert!(store.set_declared_type_links(
                    owner,
                    DeclaredTypeLinks {
                        declared_type: Some(value),
                        ..DeclaredTypeLinks::default()
                    }
                )),
                CacheChange::OtherSymbol | CacheChange::OtherSymbolAndNode => {
                    assert!(store.set_symbol_node_links(
                        fixture.exported,
                        SymbolNodeLinks {
                            resolved_symbol: Some(other)
                        }
                    ));
                    if matches!(change, CacheChange::OtherSymbolAndNode) {
                        assert!(store.set_type_node_links(
                            fixture.exported,
                            TypeNodeLinks {
                                resolved_type: Some(other_declared),
                                ..TypeNodeLinks::default()
                            }
                        ));
                    }
                }
                CacheChange::ValueNode | CacheChange::OtherNode => {
                    let wrong = if matches!(change, CacheChange::ValueNode) {
                        value
                    } else {
                        other_declared
                    };
                    assert!(store.set_type_node_links(
                        fixture.exported,
                        TypeNodeLinks {
                            resolved_type: Some(wrong),
                            ..TypeNodeLinks::default()
                        }
                    ));
                }
            }
            let before = snapshot(context, fixture);
            for attempt in 0..2 {
                let actual = context.get_type_at_location(fixture.exported);
                eprintln!(
                    "export declared-cache review: {change:?}, attempt {attempt}: {actual:?}"
                );
                if actual.is_ok() {
                    failures.push(format!(
                        "{change:?}, attempt {attempt}: accepted {actual:?}"
                    ));
                }
                if snapshot(context, fixture) != before {
                    failures.push(format!(
                        "{change:?}, attempt {attempt}: query changed state"
                    ));
                }
            }
            let store = context.store_mut_for_test();
            if matches!(change, CacheChange::RetargetedClass) {
                assert!(store.set_type_symbol(other_declared, Some(other)));
                assert!(store.set_type_symbol(other_this.unwrap(), Some(other)));
            }
            assert!(store.set_declared_type_links(owner, original));
            assert!(store.set_type_node_links(fixture.exported, type_node));
            assert!(store.set_symbol_node_links(fixture.exported, symbol_node));
            assert_healthy(context, fixture, owner, declared, value);
        });
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn export_equals_final_invariant_class_declared_caches_keep_source_identity() {
    check_declared_cache_changes(CLASS_SOURCE, true);
}

#[test]
fn export_equals_final_invariant_enum_declared_caches_keep_source_identity() {
    check_declared_cache_changes(ENUM_SOURCE, false);
}

#[derive(Clone, Copy, Debug)]
enum ValueChange {
    Missing,
    Borrowed,
    Primitive,
    ExtraTarget,
    MissingWithBorrowedNode,
    MissingWithChangedOwnerAndNode,
    MissingBothWithReference,
}

#[allow(clippy::too_many_lines)] // Keep value-cache rejection, state checks, and restoration together.
fn check_value_cache_changes(text: &str) {
    let mut failures = Vec::new();
    for change in [
        ValueChange::Missing,
        ValueChange::Borrowed,
        ValueChange::Primitive,
        ValueChange::ExtraTarget,
        ValueChange::MissingWithBorrowedNode,
        ValueChange::MissingWithChangedOwnerAndNode,
        ValueChange::MissingBothWithReference,
    ] {
        with_source(text, false, |context, fixture| {
            let owner = fixture.owner(context, "Value");
            let other = fixture.owner(context, "Other");
            let (declared, value) = identities(context, owner);
            let (other_declared, other_value) = identities(context, other);
            assert_healthy(context, fixture, owner, declared, value);
            let original_value = context.store().value_symbol_links(owner).cloned().unwrap();
            let original_declared = context.store().declared_type_links(owner).cloned().unwrap();
            let type_node = context
                .store()
                .type_node_links(fixture.exported)
                .cloned()
                .unwrap_or_default();
            let symbol_node = context
                .store()
                .symbol_node_links(fixture.exported)
                .cloned()
                .unwrap_or_default();
            let record = context.store().symbol(owner).unwrap();
            let declarations = record.declarations().unwrap().to_vec();
            let value_declaration = record.value_declaration();
            let other_record = context.store().symbol(other).unwrap();
            let other_declarations = other_record.declarations().unwrap().to_vec();
            let other_value_declaration = other_record.value_declaration();
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let store = context.store_mut_for_test();
            let changed = match change {
                ValueChange::Borrowed => ValueSymbolLinks {
                    resolved_type: Some(other_value),
                    ..ValueSymbolLinks::default()
                },
                ValueChange::Primitive => ValueSymbolLinks {
                    resolved_type: Some(number),
                    ..ValueSymbolLinks::default()
                },
                ValueChange::ExtraTarget => ValueSymbolLinks {
                    target: Some(other),
                    ..original_value.clone()
                },
                _ => ValueSymbolLinks::default(),
            };
            assert!(store.set_value_symbol_links(owner, changed));
            if matches!(
                change,
                ValueChange::MissingWithBorrowedNode | ValueChange::MissingWithChangedOwnerAndNode
            ) {
                assert!(store.set_type_node_links(
                    fixture.exported,
                    TypeNodeLinks {
                        resolved_type: Some(other_declared),
                        ..TypeNodeLinks::default()
                    }
                ));
            }
            if matches!(change, ValueChange::MissingWithChangedOwnerAndNode) {
                assert!(store.set_symbol_declarations(
                    owner,
                    Some(other_declarations),
                    other_value_declaration
                ));
                assert!(store.set_symbol_node_links(
                    fixture.exported,
                    SymbolNodeLinks {
                        resolved_symbol: Some(other)
                    }
                ));
            }
            if matches!(change, ValueChange::MissingBothWithReference) {
                assert!(store.set_declared_type_links(owner, DeclaredTypeLinks::default()));
                assert!(store.set_symbol_node_links(
                    fixture.exported,
                    SymbolNodeLinks {
                        resolved_symbol: Some(owner)
                    }
                ));
            }
            let before = snapshot(context, fixture);
            for attempt in 0..2 {
                let route = context.export_equals_declared_artifact_type(fixture.exported);
                let actual = context.get_type_at_location(fixture.exported);
                eprintln!(
                    "export value-cache review: {change:?}, attempt {attempt}: route={route:?}, actual={actual:?}"
                );
                if actual.is_ok() {
                    failures.push(format!(
                        "{change:?}, attempt {attempt}: accepted {actual:?}, route={route:?}"
                    ));
                }
                if snapshot(context, fixture) != before {
                    failures.push(format!(
                        "{change:?}, attempt {attempt}: query changed state"
                    ));
                }
            }
            let store = context.store_mut_for_test();
            assert!(store.set_symbol_declarations(owner, Some(declarations), value_declaration));
            assert!(store.set_declared_type_links(owner, original_declared));
            assert!(store.set_value_symbol_links(owner, original_value));
            assert!(store.set_type_node_links(fixture.exported, type_node));
            assert!(store.set_symbol_node_links(fixture.exported, symbol_node));
            assert_healthy(context, fixture, owner, declared, value);
        });
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn export_equals_final_invariant_class_value_caches_do_not_bypass_checks() {
    check_value_cache_changes(CLASS_SOURCE);
}

#[test]
fn export_equals_final_invariant_enum_value_caches_do_not_bypass_checks() {
    check_value_cache_changes(ENUM_SOURCE);
}

#[test]
fn export_equals_final_invariant_local_class_namespace_merge_keeps_identity() {
    let text = format!("{CLASS_SOURCE} namespace Value {{}}");
    with_source(&text, false, |context, fixture| {
        let owner = fixture.owner(context, "Value");
        assert_eq!(
            context
                .store()
                .symbol(owner)
                .unwrap()
                .declarations()
                .unwrap()
                .len(),
            2
        );
        let (declared, value) = identities(context, owner);
        assert_healthy(context, fixture, owner, declared, value);
    });
}

#[test]
fn export_equals_final_invariant_global_class_namespace_merge_keeps_identity() {
    with_sources(
        &[
            (
                "declare class Value { value: number; }",
                true,
                CanonicalModuleState::Script,
            ),
            (
                "declare namespace Value {}",
                true,
                CanonicalModuleState::Script,
            ),
            (
                "const observed = Value; export = Value;",
                false,
                CanonicalModuleState::External,
            ),
        ],
        2,
        |context, fixture| {
            let owner = fixture.owner(context, "Value");
            assert_eq!(
                context
                    .store()
                    .symbol(owner)
                    .unwrap()
                    .declarations()
                    .unwrap()
                    .len(),
                2
            );
            let (declared, value) = identities(context, owner);
            assert_healthy(context, fixture, owner, declared, value);
        },
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Each changed merged owner must reject cached reads and recover.
fn export_equals_merged_class_sources_reject_changed_owners_before_cache_reads() {
    #[derive(Clone, Copy, Debug)]
    enum Change {
        Flags(SymbolFlags),
        ValueDeclaration,
        DeclarationOrder,
        MissingNamespace,
    }

    for change in [
        Change::Flags(SymbolFlags::NONE),
        Change::Flags(SymbolFlags::TYPE_ALIAS),
        Change::Flags(SymbolFlags::INTERFACE),
        Change::Flags(SymbolFlags::CLASS),
        Change::ValueDeclaration,
        Change::DeclarationOrder,
        Change::MissingNamespace,
    ] {
        with_sources(
            &[
                (
                    "declare class Value { value: number; }",
                    true,
                    CanonicalModuleState::Script,
                ),
                (
                    "declare namespace Value {}",
                    true,
                    CanonicalModuleState::Script,
                ),
                (
                    "const observed = Value; export = Value;",
                    false,
                    CanonicalModuleState::External,
                ),
            ],
            2,
            |context, fixture| {
                let owner = fixture.owner(context, "Value");
                let (declared, value) = identities(context, owner);
                assert_healthy(context, fixture, owner, declared, value);
                assert!(!context.store().source_symbol_declarations_match(owner));
                assert!(
                    context
                        .store()
                        .source_merged_symbol_declarations_match(owner)
                );

                let record = context.store().symbol(owner).unwrap();
                let flags = record.flags();
                let check_flags = record.check_flags();
                let declarations = record.declarations().unwrap().to_vec();
                let value_declaration = record.value_declaration();
                let namespace = declarations
                    .iter()
                    .copied()
                    .find(|declaration| {
                        context.store().source_node_kind(*declaration)
                            == Some(ts_ast::SyntaxKind::ModuleDeclaration)
                    })
                    .unwrap();
                let original_node_links = context
                    .store()
                    .type_node_links(fixture.exported)
                    .cloned()
                    .unwrap_or_default();
                let number = context.global_types().number_type;
                assert_ne!(number, declared);
                let store = context.store_mut_for_test();
                match change {
                    Change::Flags(changed) => {
                        assert!(store.set_symbol_flags(owner, changed, check_flags));
                    }
                    Change::ValueDeclaration => {
                        assert!(store.set_symbol_declarations(
                            owner,
                            Some(declarations.clone()),
                            Some(namespace),
                        ));
                    }
                    Change::DeclarationOrder => {
                        let mut changed = declarations.clone();
                        changed.reverse();
                        assert!(store.set_symbol_declarations(
                            owner,
                            Some(changed),
                            value_declaration,
                        ));
                    }
                    Change::MissingNamespace => {
                        let changed = declarations
                            .iter()
                            .copied()
                            .filter(|declaration| *declaration != namespace)
                            .collect();
                        assert!(store.set_symbol_declarations(
                            owner,
                            Some(changed),
                            value_declaration,
                        ));
                    }
                }
                assert!(store.set_type_node_links(
                    fixture.exported,
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        ..original_node_links.clone()
                    },
                ));
                let before = snapshot(context, fixture);
                for _ in 0..2 {
                    assert!(
                        context
                            .export_equals_declared_artifact_type(fixture.exported)
                            .is_err(),
                        "{change:?}",
                    );
                    assert!(
                        context.get_type_at_location(fixture.exported).is_err(),
                        "{change:?}",
                    );
                    assert_eq!(snapshot(context, fixture), before, "{change:?}");
                }
                let store = context.store_mut_for_test();
                assert!(store.set_symbol_flags(owner, flags, check_flags));
                assert!(store.set_symbol_declarations(
                    owner,
                    Some(declarations),
                    value_declaration,
                ));
                assert!(store.set_type_node_links(fixture.exported, original_node_links));
                assert_healthy(context, fixture, owner, declared, value);
            },
        );
    }
}

#[test]
fn export_equals_final_invariant_class_flags_cannot_hide_from_value_lookup() {
    let mut failures = Vec::new();
    for (source_kind, text, declaration_file) in [
        ("checked", CLASS_SOURCE, false),
        (
            "prepared declaration",
            "declare class Value { value: number; } export = Value;",
            true,
        ),
    ] {
        for (flag_name, changed_flags) in [
            ("type alias", SymbolFlags::TYPE_ALIAS),
            ("interface", SymbolFlags::INTERFACE),
            ("none", SymbolFlags::NONE),
        ] {
            assert!(
                !changed_flags.intersects(
                    SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE | SymbolFlags::ALIAS
                )
            );
            with_source(text, declaration_file, |context, fixture| {
                let owner = fixture.owner(context, "Value");
                if declaration_file {
                    context.get_nongeneric_class_members(owner).unwrap();
                }
                let (declared, value) = identities(context, owner);
                assert_healthy(context, fixture, owner, declared, value);
                let record = context.store().symbol(owner).unwrap();
                let flags = record.flags();
                let check_flags = record.check_flags();
                assert!(flags.intersects(SymbolFlags::CLASS));
                let node_links = context
                    .store()
                    .type_node_links(fixture.exported)
                    .cloned()
                    .unwrap_or_default();
                let number = context.store().intrinsic_bootstrap().unwrap().number_type;
                assert_ne!(number, declared);
                assert_ne!(number, value);
                let store = context.store_mut_for_test();
                assert!(store.set_symbol_flags(owner, changed_flags, check_flags));
                assert!(store.set_type_node_links(
                    fixture.exported,
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        ..TypeNodeLinks::default()
                    }
                ));
                assert_eq!(context.store().source_symbol_flags(owner), Some(flags));
                assert_eq!(
                    context
                        .store()
                        .symbol_table(fixture.local_table)
                        .unwrap()
                        .get_source("Value"),
                    Some(owner)
                );
                let before = snapshot(context, fixture);
                for attempt in 0..2 {
                    let route = context.export_equals_declared_artifact_type(fixture.exported);
                    let actual = context.get_type_at_location(fixture.exported);
                    eprintln!(
                        "export flag-filter review: {source_kind}, {flag_name}, attempt {attempt}: route={route:?}, actual={actual:?}, declared={declared:?}, cached={number:?}"
                    );
                    if actual.is_ok() {
                        failures.push(format!(
                            "{source_kind}, {flag_name}, attempt {attempt}: accepted {actual:?}, route={route:?}"
                        ));
                    }
                    if snapshot(context, fixture) != before {
                        failures.push(format!(
                            "{source_kind}, {flag_name}, attempt {attempt}: query changed state"
                        ));
                    }
                }
                let store = context.store_mut_for_test();
                assert!(store.set_symbol_flags(owner, flags, check_flags));
                assert!(store.set_type_node_links(fixture.exported, node_links));
                assert_healthy(context, fixture, owner, declared, value);
            });
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn export_equals_type_only_locals_do_not_hide_a_global_class_value() {
    for local in [
        "interface Value { other: string; } export = Value;",
        "type Value = string; export = Value;",
    ] {
        with_sources(
            &[
                (
                    "declare class Value { value: number; }",
                    true,
                    CanonicalModuleState::Script,
                ),
                (local, true, CanonicalModuleState::External),
            ],
            1,
            |context, fixture| {
                let owner = fixture.owner(context, "Value");
                assert!(
                    context
                        .store()
                        .symbol(owner)
                        .unwrap()
                        .flags()
                        .contains(SymbolFlags::CLASS)
                );
                context.get_nongeneric_class_members(owner).unwrap();
                let (declared, value) = identities(context, owner);
                assert_healthy(context, fixture, owner, declared, value);
            },
        );
    }
}

#[test]
fn review_merged_export_guard_keeps_cold_global_declarations_unpublished() {
    for namespace_first in [false, true] {
        let class = (
            "declare class Value { value: number; }",
            true,
            CanonicalModuleState::Script,
        );
        let namespace = (
            "declare namespace Value {}",
            true,
            CanonicalModuleState::Script,
        );
        let declarations = if namespace_first {
            [namespace, class]
        } else {
            [class, namespace]
        };
        with_sources(
            &[
                declarations[0],
                declarations[1],
                ("export = Value;", true, CanonicalModuleState::External),
            ],
            2,
            |context, fixture| {
                let owner = fixture.owner(context, "Value");
                assert!(
                    crate::semantic::classes::global_class_namespace_declaration(
                        context.store(),
                        owner,
                        context.store().symbol(owner).unwrap(),
                    )
                    .is_some()
                );
                assert!(context.store().declared_type_links(owner).is_none());
                assert!(context.store().value_symbol_links(owner).is_none());
                let before = snapshot(context, fixture);
                for _ in 0..2 {
                    assert_eq!(
                        context.export_equals_declared_artifact_type(fixture.exported),
                        Ok(None)
                    );
                    assert!(matches!(
                        context.get_type_at_location(fixture.exported),
                        Err(CanonicalArtifactQueryError::MissingType { node, .. })
                            if node == fixture.exported
                    ));
                    assert_eq!(context.get_symbol_at_location(fixture.exported), Ok(None));
                    assert_eq!(snapshot(context, fixture), before);
                }
                context.get_nongeneric_class_members(owner).unwrap();
                let (declared, value) = identities(context, owner);
                assert_healthy(context, fixture, owner, declared, value);
            },
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Compare separate and paired changes, then restore the same source.
fn review_merged_export_guard_rejects_redirect_and_flag_pairs_before_cache_reads() {
    let mut failures = Vec::new();
    with_sources(
        &[
            (
                "declare class Value { value: number; }",
                true,
                CanonicalModuleState::Script,
            ),
            (
                "declare namespace Value {}",
                true,
                CanonicalModuleState::Script,
            ),
            (
                "const observed = Value; export = Value;",
                false,
                CanonicalModuleState::External,
            ),
        ],
        2,
        |context, fixture| {
            let owner = fixture.owner(context, "Value");
            let (declared, value) = identities(context, owner);
            assert_healthy(context, fixture, owner, declared, value);
            let record = context.store().symbol(owner).unwrap();
            let flags = record.flags();
            let check_flags = record.check_flags();
            let class = record.value_declaration().unwrap();
            let namespace = record
                .declarations()
                .unwrap()
                .iter()
                .copied()
                .find(|node| {
                    context.store().source_node_kind(*node)
                        == Some(ts_ast::SyntaxKind::ModuleDeclaration)
                })
                .unwrap();
            let raw_class = context.file(class.file).unwrap().1.symbol(class).unwrap();
            let raw_namespace = context
                .file(namespace.file)
                .unwrap()
                .1
                .symbol(namespace)
                .unwrap();
            assert_ne!(raw_class, owner);
            assert_ne!(raw_namespace, owner);
            assert_eq!(context.store().get_merged_symbol(raw_class), Some(owner));
            assert_eq!(
                context.store().get_merged_symbol(raw_namespace),
                Some(owner)
            );
            let original_node = context
                .store()
                .type_node_links(fixture.exported)
                .cloned()
                .unwrap_or_default();
            let number = context.global_types().number_type;
            assert_ne!(number, declared);
            assert_ne!(number, value);

            for mask in [1, 2, 3] {
                let store = context.store_mut_for_test();
                if mask & 1 != 0 {
                    assert_eq!(
                        store.record_merged_symbol(raw_namespace, raw_class),
                        Ok(Some(owner))
                    );
                    assert_eq!(store.get_merged_symbol(raw_class), Some(raw_namespace));
                }
                if mask & 2 != 0 {
                    assert!(store.set_symbol_flags(owner, SymbolFlags::NONE, check_flags));
                }
                assert!(store.set_type_node_links(
                    fixture.exported,
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        ..original_node.clone()
                    },
                ));
                let source_flags = store.source_symbol_flags(owner).unwrap();
                assert_eq!(source_flags.intersects(SymbolFlags::CLASS), mask & 1 == 0);
                let before = snapshot(context, fixture);
                for attempt in 0..2 {
                    let route = context.export_equals_declared_artifact_type(fixture.exported);
                    let actual = context.get_type_at_location(fixture.exported);
                    if route.is_ok() || actual.is_ok() {
                        failures.push(format!(
                            "mask={mask}, attempt={attempt}, source_flags={source_flags:?}: route={route:?}, actual={actual:?}, planted={number:?}"
                        ));
                    }
                    assert_eq!(snapshot(context, fixture), before);
                }
                let store = context.store_mut_for_test();
                if mask & 1 != 0 {
                    assert_eq!(
                        store.record_merged_symbol(owner, raw_class),
                        Ok(Some(raw_namespace))
                    );
                }
                assert!(store.set_symbol_flags(owner, flags, check_flags));
                assert!(store.set_type_node_links(fixture.exported, original_node.clone()));
                assert_healthy(context, fixture, owner, declared, value);
            }
        },
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
#[allow(clippy::too_many_lines)] // The global entry and cached identities are tested alone and together.
fn review_merged_export_guard_rejects_foreign_same_name_global_targets() {
    let mut failures = Vec::new();
    with_sources(
        &[
            (
                "declare class Value { value: number; }",
                true,
                CanonicalModuleState::Script,
            ),
            (
                "declare namespace Value {}",
                true,
                CanonicalModuleState::Script,
            ),
            (
                "class Value { other: string = 'other'; } export = Value;",
                false,
                CanonicalModuleState::External,
            ),
            (
                "const observed = Value; export = Value;",
                false,
                CanonicalModuleState::External,
            ),
        ],
        3,
        |context, fixture| {
            let owner = fixture.owner(context, "Value");
            let (declared, value) = identities(context, owner);
            assert_healthy(context, fixture, owner, declared, value);
            let foreign_declaration = fixture
                .nodes
                .iter()
                .copied()
                .find(|node| {
                    node.file == fixture.files[2]
                        && context.store().source_node_kind(*node)
                            == Some(ts_ast::SyntaxKind::ClassDeclaration)
                })
                .unwrap();
            let foreign = context
                .file(foreign_declaration.file)
                .unwrap()
                .1
                .symbol(foreign_declaration)
                .unwrap();
            assert_eq!(context.store().get_merged_symbol(foreign), Some(foreign));
            assert_ne!(foreign, owner);
            assert!(context.store().source_symbol_declarations_match(foreign));
            assert!(
                context
                    .store()
                    .source_merged_symbol_declarations_match(foreign)
            );
            let (foreign_declared, foreign_value) = identities(context, foreign);
            assert_ne!(foreign_declared, declared);
            assert_ne!(foreign_value, value);
            let globals = context.store().intrinsic_bootstrap().unwrap().globals;
            assert_eq!(
                context
                    .store()
                    .symbol_table(globals)
                    .unwrap()
                    .get_source("Value"),
                Some(owner)
            );
            let original_node = context
                .store()
                .type_node_links(fixture.exported)
                .cloned()
                .unwrap_or_default();
            let original_symbol = context
                .store()
                .symbol_node_links(fixture.exported)
                .cloned()
                .unwrap_or_default();
            let state = |context: &CanonicalCheckerContext<'_>| {
                (
                    snapshot(context, fixture),
                    context
                        .store()
                        .symbol_table(globals)
                        .unwrap()
                        .iter()
                        .map(|(name, symbol)| (name.to_owned(), symbol))
                        .collect::<Vec<_>>(),
                )
            };
            for mask in [1, 2, 3] {
                let store = context.store_mut_for_test();
                if mask & 1 != 0 {
                    assert_eq!(
                        store.insert_symbol(globals, EscapedName::source("Value"), foreign),
                        Some(Some(owner))
                    );
                }
                if mask & 2 != 0 {
                    assert!(store.set_type_node_links(
                        fixture.exported,
                        TypeNodeLinks {
                            resolved_type: Some(foreign_declared),
                            ..original_node.clone()
                        },
                    ));
                    assert!(store.set_symbol_node_links(
                        fixture.exported,
                        SymbolNodeLinks {
                            resolved_symbol: Some(foreign),
                        },
                    ));
                }
                let before = state(context);
                for attempt in 0..2 {
                    let route = context.export_equals_declared_artifact_type(fixture.exported);
                    let actual = context.get_type_at_location(fixture.exported);
                    if route.is_ok() || actual.is_ok() {
                        failures.push(format!(
                            "mask={mask}, attempt={attempt}: route={route:?}, actual={actual:?}, foreign={foreign_declared:?}"
                        ));
                    }
                    assert_eq!(state(context), before);
                }
                let store = context.store_mut_for_test();
                if mask & 1 != 0 {
                    assert_eq!(
                        store.insert_symbol(globals, EscapedName::source("Value"), owner),
                        Some(Some(foreign))
                    );
                }
                assert!(store.set_type_node_links(fixture.exported, original_node.clone()));
                assert!(store.set_symbol_node_links(fixture.exported, original_symbol.clone()));
                assert_healthy(context, fixture, owner, declared, value);
            }
        },
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
