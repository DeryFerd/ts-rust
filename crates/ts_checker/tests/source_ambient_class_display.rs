use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, DeclaredTypeLinks, MembersAndExportsLinks, ModuleSymbolLinks,
    NodeLinks, SignatureLinks, SourceFileLinks, SymbolNodeLinks, SymbolReferenceLinks, TypeData,
    TypeId, TypeNodeLinks, ValueSymbolLinks,
    type_records::{InterfaceTypeData, StructuredTypeData, TypeCacheState, TypeParameterData},
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const DECLARATIONS: FileId = FileId::new(202_910);
const CONSUMER: FileId = FileId::new(202_911);
const REACT_DECLARATIONS: &str = concat!(
    "declare namespace React {\n",
    "    class Component {}\n",
    "    class PureComponent {}\n",
    "}\n",
);

fn context<'arena>(
    declarations: &'arena ParseResult,
    consumer: &'arena ParseResult,
    consumer_first: bool,
) -> CanonicalCheckerContext<'arena> {
    let mut sources = [
        (DECLARATIONS, declarations, "\"/project/react.d.ts\"", true),
        (CONSUMER, consumer, "\"/project/consumer.ts\"", false),
    ];
    if consumer_first {
        sources.reverse();
    }
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, declaration_file) in sources {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration_file,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for (file, parsed, _, _) in sources {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        sources
            .into_iter()
            .map(|(file, parsed, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ClassIdentity {
    declaration: NodeRef,
    name: NodeRef,
    namespace: SemanticSymbolId,
    owner: SemanticSymbolId,
    local: SemanticSymbolId,
    prototype: SemanticSymbolId,
}

#[allow(clippy::too_many_lines)] // Check the complete binder identity without resolving a class value.
fn class_identity(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    namespace_name: &str,
    class_name: &str,
) -> ClassIdentity {
    let (declaration, name) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let name = class.name?;
            matches!(&parsed.arena.get(name)?.data,
                NodeData::Identifier(identifier) if identifier.text == class_name)
            .then_some((
                NodeRef::new(parsed.arena.id(), DECLARATIONS, node),
                NodeRef::new(parsed.arena.id(), DECLARATIONS, name),
            ))
        })
        .unwrap();
    let body = parsed.arena.get(declaration.node).unwrap().parent.unwrap();
    let body_record = parsed.arena.get(body).unwrap();
    assert_eq!(body_record.kind, SyntaxKind::ModuleBlock);
    let namespace_declaration =
        NodeRef::new(parsed.arena.id(), DECLARATIONS, body_record.parent.unwrap());
    let namespace_node = parsed.arena.get(namespace_declaration.node).unwrap();
    let NodeData::ModuleDeclaration(module) = &namespace_node.data else {
        panic!("the class belongs to its written namespace")
    };
    assert_eq!(module.body, Some(body));
    assert!(matches!(&parsed.arena.get(module.name).unwrap().data,
        NodeData::Identifier(identifier) if identifier.text == namespace_name));
    let bound = context.file(DECLARATIONS).unwrap().1;
    assert_eq!(namespace_node.parent, Some(bound.source_file().node));
    let store = context.store();
    let namespace = bound.symbol(namespace_declaration).unwrap();
    let namespace_record = store.symbol(namespace).unwrap();
    assert_eq!(namespace_record.flags(), SymbolFlags::VALUE_MODULE);
    assert_eq!(namespace_record.check_flags(), CheckFlags::NONE);
    assert_eq!(namespace_record.parent(), None);
    assert_eq!(namespace_record.export_symbol(), None);
    assert_eq!(
        namespace_record.value_declaration(),
        Some(namespace_declaration)
    );
    assert_eq!(
        namespace_record.declarations(),
        Some(&[namespace_declaration][..])
    );
    assert_eq!(store.get_merged_symbol(namespace), Some(namespace));
    assert_eq!(
        store
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap()
            .get_source(namespace_name),
        Some(namespace),
    );

    let owner = bound.symbol(declaration).unwrap();
    let local = bound.local_symbol(declaration).unwrap();
    assert_ne!(owner, local);
    let owner_record = store.symbol(owner).unwrap();
    let local_record = store.symbol(local).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::CLASS);
    assert_eq!(owner_record.check_flags(), CheckFlags::NONE);
    assert_eq!(owner_record.name().as_utf8(), Some(class_name));
    assert_eq!(owner_record.declarations(), Some(&[declaration][..]));
    assert_eq!(owner_record.value_declaration(), Some(declaration));
    assert_eq!(owner_record.parent(), Some(namespace));
    assert_eq!(owner_record.export_symbol(), None);
    assert_eq!(owner_record.members(), None);
    assert_eq!(store.get_parent_of_symbol(owner), Some(namespace));
    assert_eq!(store.get_merged_symbol(owner), Some(owner));
    assert_eq!(local_record.flags(), SymbolFlags::EXPORT_VALUE);
    assert_eq!(local_record.check_flags(), CheckFlags::NONE);
    assert_eq!(local_record.name().as_utf8(), Some(class_name));
    assert_eq!(local_record.declarations(), Some(&[declaration][..]));
    assert_eq!(local_record.value_declaration(), None);
    assert_eq!(local_record.parent(), None);
    assert_eq!(local_record.members(), None);
    assert_eq!(local_record.exports(), None);
    assert_eq!(local_record.export_symbol(), Some(owner));
    assert_eq!(store.get_merged_symbol(local), Some(local));
    let namespace_exports = store
        .symbol_table(namespace_record.exports().unwrap())
        .unwrap();
    let namespace_locals = store
        .symbol_table(bound.locals(namespace_declaration).unwrap())
        .unwrap();
    assert_eq!(namespace_exports.len(), 2);
    assert_eq!(namespace_locals.len(), 2);
    assert_eq!(namespace_exports.get_source(class_name), Some(owner));
    assert_eq!(namespace_locals.get_source(class_name), Some(local));

    let exports = store.symbol_table(owner_record.exports().unwrap()).unwrap();
    assert_eq!(exports.len(), 1);
    let prototype = exports.get_source("prototype").unwrap();
    let prototype_record = store.symbol(prototype).unwrap();
    assert_eq!(
        prototype_record.flags(),
        SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE
    );
    assert_eq!(prototype_record.check_flags(), CheckFlags::NONE);
    assert_eq!(prototype_record.parent(), Some(owner));
    assert_eq!(prototype_record.declarations(), None);
    assert_eq!(prototype_record.value_declaration(), None);
    assert_eq!(prototype_record.members(), None);
    assert_eq!(prototype_record.exports(), None);
    assert_eq!(prototype_record.export_symbol(), None);
    assert_eq!(store.get_merged_symbol(prototype), Some(prototype));
    ClassIdentity {
        declaration,
        name,
        namespace,
        owner,
        local,
        prototype,
    }
}

fn assert_cold_instance(
    context: &CanonicalCheckerContext<'_>,
    class: ClassIdentity,
    instance: TypeId,
) {
    let store = context.store();
    assert_eq!(
        store
            .declared_type_links(class.owner)
            .and_then(|links| links.declared_type),
        Some(instance),
    );
    assert!(store.declared_type_links(class.local).is_none());
    for symbol in [class.owner, class.local, class.prototype] {
        assert!(
            store
                .value_symbol_links(symbol)
                .is_none_or(|links| links == &ValueSymbolLinks::default())
        );
    }
    let record = store.type_payload(instance).unwrap();
    assert_eq!(record.flags(), TypeFlags::OBJECT);
    assert_eq!(
        record.object_flags(),
        ObjectFlags::CLASS | ObjectFlags::REFERENCE
    );
    assert_eq!(record.symbol(), Some(class.owner));
    assert_eq!(record.alias(), None);
    let TypeData::Interface(interface) = record.data() else {
        panic!("the declared class has its real instance record")
    };
    assert!(!interface.base_types_resolved);
    assert!(!interface.declared_members_resolved);
    assert_eq!(interface.resolved_base_constructor_type, None);
    assert_eq!(interface.resolved_base_types, None);
    assert_eq!(interface.declared_members, None);
    assert_eq!(interface.declared_call_signatures, None);
    assert_eq!(interface.declared_construct_signatures, None);
    assert_eq!(interface.declared_index_infos, None);
    assert_eq!(interface.outer_type_parameter_count, 0);
    assert_eq!(interface.reference.node, None);
    assert_eq!(
        interface.reference.resolved_type_arguments.as_deref(),
        Some(&[][..])
    );
    assert_eq!(interface.reference.object.target, Some(instance));
    assert_eq!(interface.reference.object.mapper, None);
    assert_eq!(
        interface.reference.object.structured,
        StructuredTypeData::default()
    );
    let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
    else {
        panic!("the declared class retains its self-instantiation")
    };
    assert_eq!(instantiations.len(), 1);
    assert_eq!(
        instantiations.values().copied().collect::<Vec<_>>(),
        [instance]
    );
    let this = interface.this_type.unwrap();
    assert_ne!(instance, this);
    assert_eq!(interface.all_type_parameters.as_deref(), Some(&[this][..]));
    let this_record = store.type_payload(this).unwrap();
    assert_eq!(this_record.flags(), TypeFlags::TYPE_PARAMETER);
    assert_eq!(this_record.object_flags(), ObjectFlags::NONE);
    assert_eq!(this_record.symbol(), Some(class.owner));
    assert_eq!(this_record.alias(), None);
    assert_eq!(
        this_record.data(),
        &TypeData::TypeParameter(TypeParameterData {
            constraint: Some(instance),
            is_this_type: true,
            ..TypeParameterData::default()
        }),
    );
}

type NodeSnapshot = (
    NodeRef,
    Option<NodeLinks>,
    Option<TypeNodeLinks>,
    Option<SymbolNodeLinks>,
    Option<SignatureLinks>,
);

#[derive(Debug, Eq, PartialEq)]
struct SymbolSnapshot {
    symbol: SemanticSymbolId,
    declared: Option<DeclaredTypeLinks>,
    value: Option<ValueSymbolLinks>,
    alias: Option<AliasSymbolLinks>,
    references: Option<SymbolReferenceLinks>,
    module: Option<ModuleSymbolLinks>,
    members: Option<MembersAndExportsLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 8],
    nodes: Vec<NodeSnapshot>,
    symbols: Vec<SymbolSnapshot>,
    interfaces: Vec<(TypeId, InterfaceTypeData)>,
    sources: [Option<SourceFileLinks>; 2],
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    declarations: &ParseResult,
    consumer: &ParseResult,
) -> Snapshot {
    let store = context.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
            store.merged_symbol_len(),
        ],
        nodes: [(DECLARATIONS, declarations), (CONSUMER, consumer)]
            .into_iter()
            .flat_map(|(file, parsed)| {
                parsed.arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(parsed.arena.id(), file, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| SymbolSnapshot {
                symbol,
                declared: store.declared_type_links(symbol).cloned(),
                value: store.value_symbol_links(symbol).cloned(),
                alias: store.alias_symbol_links(symbol).cloned(),
                references: store.symbol_reference_links(symbol).cloned(),
                module: store.module_symbol_links(symbol).cloned(),
                members: store.members_and_exports_links(symbol).cloned(),
            })
            .collect(),
        interfaces: store
            .types()
            .filter_map(|(type_, record)| {
                let TypeData::Interface(interface) = record.data() else {
                    return None;
                };
                Some((type_, interface.clone()))
            })
            .collect(),
        sources: [DECLARATIONS, CONSUMER].map(|file| {
            store
                .source_file_links(context.source_file(file).unwrap())
                .cloned()
        }),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_display_without_writes(
    context: &mut CanonicalCheckerContext<'_>,
    declarations: &ParseResult,
    consumer: &ParseResult,
    class: ClassIdentity,
    instance: TypeId,
    name: &str,
    qualified: &str,
) {
    assert_cold_instance(context, class, instance);
    let before = snapshot(context, declarations, consumer);
    assert_eq!(context.type_to_string(instance).unwrap(), name);
    assert_eq!(
        context
            .type_to_string_at_location(instance, class.name)
            .unwrap(),
        name,
    );
    let outside = context.source_file(CONSUMER).unwrap().node_ref();
    assert_eq!(
        context
            .type_to_string_at_location(instance, outside)
            .unwrap(),
        qualified,
    );
    assert_eq!(snapshot(context, declarations, consumer), before);
    assert_cold_instance(context, class, instance);
}

#[allow(clippy::too_many_lines)] // Keep both source and query orders under the same identity checks.
fn assert_display_orders(source: &str, namespace: &str, names: [(&str, &str); 2]) {
    let declarations = parse_source_file(source);
    let consumer = parse_source_file("const outside = 0;");
    for source_first in [false, true] {
        for reverse in [false, true] {
            let mut context = context(&declarations, &consumer, reverse);
            let classes =
                names.map(|(name, _)| class_identity(&context, &declarations, namespace, name));
            assert_eq!(classes[0].namespace, classes[1].namespace);
            assert_ne!(classes[0].owner, classes[1].owner);
            for class in classes {
                assert!(context.store().declared_type_links(class.owner).is_none());
            }
            if source_first {
                context.check_source_file(DECLARATIONS).unwrap();
                for class in classes {
                    assert!(context.store().declared_type_links(class.owner).is_none());
                }
            }
            let order = if reverse { [1, 0] } else { [0, 1] };
            let mut instances = [None; 2];
            for index in order {
                let class = classes[index];
                let instance = if reverse {
                    context.get_type_at_location(class.name).unwrap()
                } else {
                    context.get_declared_type_of_symbol(class.owner).unwrap()
                };
                assert_eq!(
                    context.get_declared_type_of_symbol(class.owner),
                    Ok(instance)
                );
                assert_eq!(
                    context.get_type_at_location(class.declaration),
                    Ok(instance)
                );
                assert_eq!(context.get_type_at_location(class.name), Ok(instance));
                instances[index] = Some(instance);
                if instances[1 - index].is_none() {
                    assert!(
                        context
                            .store()
                            .declared_type_links(classes[1 - index].owner)
                            .is_none()
                    );
                }
                assert_display_without_writes(
                    &mut context,
                    &declarations,
                    &consumer,
                    class,
                    instance,
                    names[index].0,
                    names[index].1,
                );
            }
            let instances = instances.map(Option::unwrap);
            assert_ne!(instances[0], instances[1]);
            context.check_source_file(DECLARATIONS).unwrap();
            assert!(context.diagnostics().is_empty());
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(CONSUMER).unwrap())
                    .is_none()
            );
            let warm = snapshot(&context, &declarations, &consumer);
            for _ in 0..2 {
                for index in order.into_iter().rev() {
                    let class = classes[index];
                    let instance = instances[index];
                    assert_eq!(
                        class_identity(&context, &declarations, namespace, names[index].0),
                        class
                    );
                    assert_eq!(
                        context.get_declared_type_of_symbol(class.owner),
                        Ok(instance)
                    );
                    assert_eq!(context.get_type_at_location(class.name), Ok(instance));
                    assert_eq!(
                        context.get_type_at_location(class.declaration),
                        Ok(instance)
                    );
                    assert_display_without_writes(
                        &mut context,
                        &declarations,
                        &consumer,
                        class,
                        instance,
                        names[index].0,
                        names[index].1,
                    );
                }
                context.check_source_file(DECLARATIONS).unwrap();
                context.recheck_source_file(DECLARATIONS).unwrap();
                assert_eq!(snapshot(&context, &declarations, &consumer), warm);
                for (class, instance) in classes.into_iter().zip(instances) {
                    assert_cold_instance(&context, class, instance);
                }
            }
        }
    }
}

#[test]
fn ambient_react_class_display_preserves_cold_identity_and_qualified_names() {
    assert_display_orders(
        REACT_DECLARATIONS,
        "React",
        [
            ("Component", "React.Component"),
            ("PureComponent", "React.PureComponent"),
        ],
    );
}

#[test]
fn ambient_class_display_uses_source_names_in_both_query_and_file_orders() {
    assert_display_orders(
        "declare namespace Archive { class Entry {} class Cursor {} }",
        "Archive",
        [("Entry", "Archive.Entry"), ("Cursor", "Archive.Cursor")],
    );
}
