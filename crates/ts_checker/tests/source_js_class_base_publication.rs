use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, ClassMembers, DeclaredTypeLinks, MembersAndExportsLinks,
    ModuleSymbolLinks, NodeLinks, SignatureId, SignatureLinks, SourceFileLinks, SymbolNodeLinks,
    SymbolReferenceLinks, TypeAliasId, TypeData, TypeId, TypeMapperId, TypeNodeLinks,
    ValueSymbolLinks,
    signatures::SignatureFlags,
    type_records::{InterfaceTypeData, ObjectTypeData, TypeParameterData},
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

const AMBIENT_FILE: FileId = FileId::new(202_930);
const MAIN_FILE: FileId = FileId::new(202_931);

// Exact virtual files from jsdocExtendsClauseMismatch.ts at Go dc37b5249ab60e2bbce936f71b883e6c8136167e.
const AMBIENT: &str = concat!(
    "declare namespace React {\n",
    "    class Component {}\n",
    "    class PureComponent {}\n",
    "}\n",
);
const JAVASCRIPT: &str = concat!(
    "/**\n",
    " * @extends {React.Component}\n",
    " */\n",
    "class C extends React.PureComponent {}\n",
    "\n",
    "/**\n",
    " * @extends {React.Component}\n",
    " */\n",
    "class D extends React.Component {}\n",
);

fn context<'arena>(
    ambient: &'arena ParseResult,
    javascript: &'arena ParseResult,
    reverse: bool,
) -> CanonicalCheckerContext<'arena> {
    let mut sources = [
        (
            AMBIENT_FILE,
            ambient,
            "\"/.src/react.d.ts\"",
            CanonicalSourceLanguage::TypeScript,
            true,
        ),
        (
            MAIN_FILE,
            javascript,
            "\"/.src/main.js\"",
            CanonicalSourceLanguage::JavaScript,
            false,
        ),
    ];
    if reverse {
        sources.reverse();
    }
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, language, declaration_file) in sources {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    language,
                    declaration_file,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for (file, parsed, _, language, _) in sources {
        if language == CanonicalSourceLanguage::JavaScript {
            binder
                .bind_javascript_declaration_slice(&parsed.arena, file)
                .unwrap();
        } else {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
    }
    // JavaScript source facts and explicit source checking retain allowJs/checkJs.
    let options = CanonicalCheckerOptions {
        no_emit: true,
        ..CanonicalCheckerOptions::default()
    };
    CanonicalCheckerContext::new(
        binder.finish(),
        sources
            .into_iter()
            .map(|(file, parsed, _, _, _)| (file, &parsed.arena))
            .collect(),
        options,
    )
    .unwrap()
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ClassIdentity {
    declaration: NodeRef,
    name: NodeRef,
    owner: SemanticSymbolId,
    prototype: SemanticSymbolId,
}

fn class_identity(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    expected: &str,
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
                NodeData::Identifier(identifier) if identifier.text == expected)
            .then_some((
                NodeRef::new(parsed.arena.id(), file, node),
                NodeRef::new(parsed.arena.id(), file, name),
            ))
        })
        .unwrap();
    let bound = context.file(file).unwrap().1;
    let owner = bound.symbol(declaration).unwrap();
    let record = context.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::CLASS);
    assert_eq!(record.name().as_utf8(), Some(expected));
    assert_eq!(record.declarations(), Some(&[declaration][..]));
    assert_eq!(record.value_declaration(), Some(declaration));
    assert_eq!(context.store().get_merged_symbol(owner), Some(owner));
    let prototype = context
        .store()
        .symbol_table(record.exports().unwrap())
        .unwrap()
        .get_source("prototype")
        .unwrap();
    assert_eq!(
        context.store().symbol(prototype).unwrap().parent(),
        Some(owner)
    );
    ClassIdentity {
        declaration,
        name,
        owner,
        prototype,
    }
}

fn heritage_nodes(parsed: &ParseResult, identity: ClassIdentity) -> (NodeRef, NodeRef) {
    let NodeData::ClassDeclaration(class) =
        &parsed.arena.get(identity.declaration.node).unwrap().data
    else {
        panic!("the identity belongs to its source class")
    };
    let [clause_node] = class.heritage_clauses.as_ref().unwrap().nodes.as_slice() else {
        panic!("the original class has one extends clause")
    };
    let NodeData::HeritageClause(clause) = &parsed.arena.get(*clause_node).unwrap().data else {
        panic!("the class retains its heritage clause")
    };
    assert_eq!(clause.token, SyntaxKind::ExtendsKeyword);
    let [wrapper] = clause.types.nodes.as_slice() else {
        panic!("the original class has one base")
    };
    let NodeData::ExpressionWithTypeArguments(expression) =
        &parsed.arena.get(*wrapper).unwrap().data
    else {
        panic!("the base retains its real expression wrapper")
    };
    assert!(expression.type_arguments.is_none());
    let whole = NodeRef::new(parsed.arena.id(), MAIN_FILE, expression.expression);
    let NodeData::QualifiedName(qualified) = &parsed.arena.get(whole.node).unwrap().data else {
        panic!("the original base is a qualified name")
    };
    (
        whole,
        NodeRef::new(parsed.arena.id(), MAIN_FILE, qualified.right),
    )
}

fn assert_unpublished(context: &CanonicalCheckerContext<'_>, identity: ClassIdentity) {
    assert!(
        context
            .store()
            .declared_type_links(identity.owner)
            .is_none()
    );
    assert!(context.store().value_symbol_links(identity.owner).is_none());
}

fn is_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .store()
        .source_file_links(context.source_file(file).unwrap())
        .is_some_and(|links| links.type_checked)
}

fn assert_original_diagnostic(context: &CanonicalCheckerContext<'_>) {
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the original two files report only the mismatched class")
    };
    assert_eq!(diagnostic.node.unwrap().file, MAIN_FILE);
    assert_eq!(diagnostic.diagnostic.code(), 8023);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "JSDoc '@extends Component' does not match the 'extends PureComponent' clause."
    );
    assert_eq!(
        diagnostic.diagnostic.arguments,
        ["extends", "Component", "PureComponent"]
    );
    let range = diagnostic.range_override.unwrap();
    assert_eq!(range.anchor().file, MAIN_FILE);
    assert_eq!(range.range().start.get(), 23);
    assert_eq!(range.range().len(), 9);
    assert!(diagnostic.related_information.is_empty());
}

#[allow(clippy::too_many_lines)] // Check the real instance, constructor, prototype, and base together.
fn assert_published_class(
    context: &CanonicalCheckerContext<'_>,
    identity: ClassIdentity,
    members: &ClassMembers,
    base: Option<&ClassMembers>,
) {
    let store = context.store();
    let shells = members.shells();
    assert_eq!(shells.declaration(), identity.declaration);
    assert_eq!(shells.symbol(), identity.owner);
    assert_ne!(shells.instance_type(), shells.value_type());
    assert_eq!(members.prototype(), identity.prototype);
    assert!(members.instance_properties().is_empty());
    assert!(members.declared_instance_properties().is_empty());
    assert!(members.static_properties().is_empty());
    assert!(members.declared_static_properties().is_empty());
    assert_eq!(
        store
            .declared_type_links(identity.owner)
            .unwrap()
            .declared_type,
        Some(shells.instance_type())
    );
    assert_eq!(
        store
            .value_symbol_links(identity.owner)
            .unwrap()
            .resolved_type,
        Some(shells.value_type())
    );
    assert_eq!(
        store
            .value_symbol_links(identity.prototype)
            .unwrap()
            .resolved_type,
        Some(shells.instance_type())
    );
    let record = store.type_payload(shells.instance_type()).unwrap();
    assert_eq!(record.flags(), TypeFlags::OBJECT);
    assert_eq!(
        record.object_flags(),
        ObjectFlags::CLASS | ObjectFlags::REFERENCE | ObjectFlags::MEMBERS_RESOLVED
    );
    assert_eq!(record.symbol(), Some(identity.owner));
    assert_eq!(record.alias(), None);
    let TypeData::Interface(instance) = record.data() else {
        panic!("the class retains its canonical instance")
    };
    assert!(instance.base_types_resolved);
    assert!(instance.declared_members_resolved);
    assert_eq!(
        instance.reference.object.target,
        Some(shells.instance_type())
    );
    assert_eq!(instance.reference.object.mapper, None);
    assert_eq!(
        instance.reference.resolved_type_arguments.as_deref(),
        Some(&[][..])
    );
    if let Some(base) = base {
        let inherited = members.base().unwrap();
        assert_eq!(inherited.symbol(), base.shells().symbol());
        assert_eq!(inherited.instance_type(), base.shells().instance_type());
        assert_eq!(inherited.value_type(), base.shells().value_type());
        assert_ne!(shells.instance_type(), inherited.instance_type());
        assert_ne!(shells.value_type(), inherited.value_type());
        assert_eq!(
            instance.resolved_base_constructor_type,
            Some(inherited.value_type())
        );
        assert_eq!(
            instance.resolved_base_types.as_deref(),
            Some(&[inherited.instance_type()][..])
        );
        assert_ne!(
            members.default_construct_signature(),
            base.default_construct_signature()
        );
    } else {
        assert_eq!(members.base(), None);
        assert_eq!(instance.resolved_base_types, None);
        assert_eq!(
            instance.resolved_base_constructor_type,
            Some(store.intrinsic_bootstrap().unwrap().undefined_type)
        );
    }
    let record = store.type_payload(shells.value_type()).unwrap();
    assert_eq!(record.flags(), TypeFlags::OBJECT);
    assert_eq!(
        record.object_flags(),
        ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
    );
    assert_eq!(record.symbol(), Some(identity.owner));
    assert_eq!(record.alias(), None);
    let TypeData::Object(value) = record.data() else {
        panic!("the class has its own constructor value")
    };
    assert_eq!(value.structured.members, Some(members.static_members()));
    assert_eq!(
        value.structured.properties.as_deref(),
        Some(&[identity.prototype][..])
    );
    assert_eq!(value.structured.call_signature_count, 0);
    assert_eq!(
        value.structured.signatures.as_deref(),
        Some(&[members.default_construct_signature()][..])
    );
    let table = store.symbol_table(members.static_members()).unwrap();
    assert_eq!(table.len(), 1);
    assert_eq!(table.get_source("prototype"), Some(identity.prototype));
    let signature = store
        .signature(members.default_construct_signature())
        .unwrap();
    assert_eq!(signature.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(signature.declaration(), None);
    assert!(signature.type_parameters().is_empty());
    assert!(signature.parameters().is_empty());
    assert_eq!(signature.this_parameter(), None);
    assert_eq!(
        signature.resolved_return_type(),
        Some(shells.instance_type())
    );
    assert_eq!(signature.target(), None);
    assert_eq!(signature.mapper(), None);
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
enum ClassPayload {
    Instance(InterfaceTypeData),
    Object(ObjectTypeData),
    Parameter(TypeParameterData),
}

#[derive(Debug, Eq, PartialEq)]
struct TypeSnapshot {
    id: TypeId,
    flags: TypeFlags,
    object_flags: ObjectFlags,
    symbol: Option<SemanticSymbolId>,
    alias: Option<TypeAliasId>,
    payload: ClassPayload,
}

#[derive(Debug, Eq, PartialEq)]
struct SignatureSnapshot {
    id: SignatureId,
    flags: SignatureFlags,
    declaration: Option<NodeRef>,
    parameters: Vec<SemanticSymbolId>,
    type_parameters: Vec<TypeId>,
    this_parameter: Option<SemanticSymbolId>,
    return_type: Option<TypeId>,
    target: Option<SignatureId>,
    mapper: Option<TypeMapperId>,
    minimum: (i32, i32),
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 9],
    nodes: Vec<NodeSnapshot>,
    symbols: Vec<SymbolSnapshot>,
    types: Vec<TypeSnapshot>,
    signatures: Vec<SignatureSnapshot>,
    sources: [Option<SourceFileLinks>; 2],
    diagnostics: CanonicalCheckerDiagnostics,
}

#[allow(clippy::too_many_lines)] // Keep all published class state in one replay snapshot.
fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    ambient: &ParseResult,
    javascript: &ParseResult,
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
            store.type_resolution_len(),
        ],
        nodes: [(AMBIENT_FILE, ambient), (MAIN_FILE, javascript)]
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
        types: store
            .types()
            .filter_map(|(id, record)| {
                let payload = match record.data() {
                    TypeData::Interface(data) => ClassPayload::Instance(data.clone()),
                    TypeData::Object(data) => ClassPayload::Object(data.clone()),
                    TypeData::TypeParameter(data) => ClassPayload::Parameter(data.clone()),
                    _ => return None,
                };
                Some(TypeSnapshot {
                    id,
                    flags: record.flags(),
                    object_flags: record.object_flags(),
                    symbol: record.symbol(),
                    alias: record.alias(),
                    payload,
                })
            })
            .collect(),
        signatures: store
            .signatures()
            .map(|(id, signature)| SignatureSnapshot {
                id,
                flags: signature.flags(),
                declaration: signature.declaration(),
                parameters: signature.parameters().to_vec(),
                type_parameters: signature.type_parameters().to_vec(),
                this_parameter: signature.this_parameter(),
                return_type: signature.resolved_return_type(),
                target: signature.target(),
                mapper: signature.mapper(),
                minimum: (
                    signature.min_argument_count(),
                    signature.resolved_min_argument_count(),
                ),
            })
            .collect(),
        sources: [AMBIENT_FILE, MAIN_FILE].map(|file| {
            store
                .source_file_links(context.source_file(file).unwrap())
                .cloned()
        }),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_location_queries(
    context: &mut CanonicalCheckerContext<'_>,
    javascript: &ParseResult,
    identity: ClassIdentity,
    members: &ClassMembers,
    base: &ClassMembers,
) {
    assert_eq!(
        context.get_declared_type_of_symbol(identity.owner),
        Ok(members.shells().instance_type())
    );
    for node in [identity.declaration, identity.name] {
        assert_eq!(
            context.get_type_at_location(node),
            Ok(members.shells().instance_type())
        );
        assert_eq!(
            context.get_symbol_at_location(node),
            Ok(Some(identity.owner))
        );
    }
    let (whole, leaf) = heritage_nodes(javascript, identity);
    assert_eq!(
        context.get_type_at_location(whole),
        Ok(base.shells().instance_type())
    );
    assert_eq!(
        context.get_type_at_location(leaf),
        Ok(base.shells().value_type())
    );
    assert_eq!(
        context.get_symbol_at_location(whole),
        Ok(Some(base.shells().symbol()))
    );
    assert_eq!(
        context.get_symbol_at_location(leaf),
        Ok(Some(base.shells().symbol()))
    );
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum FirstDemand {
    SourceCheck,
    Members,
    Heritage,
}

#[allow(clippy::too_many_lines)] // Each original class is checked in both file/query orders and replayed warm.
fn assert_publication_order(first: FirstDemand, reverse: bool) {
    let ambient = parse_source_file(AMBIENT);
    let javascript = parse_javascript_source_file(JAVASCRIPT);
    let mut context = context(&ambient, &javascript, reverse);
    assert!(context.options().no_emit);
    let identities = ["C", "D"].map(|name| class_identity(&context, &javascript, MAIN_FILE, name));
    let providers = ["PureComponent", "Component"]
        .map(|name| class_identity(&context, &ambient, AMBIENT_FILE, name));
    let order = if reverse { [1, 0] } else { [0, 1] };
    let files = if reverse {
        [MAIN_FILE, AMBIENT_FILE]
    } else {
        [AMBIENT_FILE, MAIN_FILE]
    };
    for identity in identities.into_iter().chain(providers) {
        assert_unpublished(&context, identity);
    }
    if first == FirstDemand::SourceCheck {
        for file in files {
            context.check_source_file(file).unwrap();
        }
        assert_original_diagnostic(&context);
        for identity in identities.into_iter().chain(providers) {
            assert_unpublished(&context, identity);
        }
    }

    let mut children = [None, None];
    let mut bases = [None, None];
    for index in order {
        let identity = identities[index];
        let provider = providers[index];
        let queried = if first == FirstDemand::Heritage {
            let (whole, _) = heritage_nodes(&javascript, identity);
            let result = context.get_type_at_location(whole).unwrap();
            assert_original_diagnostic(&context);
            let instance = context
                .store()
                .declared_type_links(provider.owner)
                .and_then(|links| links.declared_type)
                .unwrap();
            assert_eq!(result, instance);
            Some(snapshot(&context, &ambient, &javascript))
        } else {
            let instance = context.get_declared_type_of_symbol(identity.owner).unwrap();
            assert_eq!(
                context.store().type_payload(instance).unwrap().symbol(),
                Some(identity.owner)
            );
            assert!(context.store().value_symbol_links(identity.owner).is_none());
            None
        };
        let declared = context
            .store()
            .declared_type_links(identity.owner)
            .and_then(|links| links.declared_type)
            .unwrap();
        let members = context
            .get_nongeneric_class_members(identity.owner)
            .unwrap();
        assert_eq!(members.shells().instance_type(), declared);
        let base = context
            .get_nongeneric_class_members(provider.owner)
            .unwrap();
        if let Some(queried) = queried {
            assert_eq!(snapshot(&context, &ambient, &javascript), queried);
        }
        assert_published_class(&context, provider, &base, None);
        assert_published_class(&context, identity, &members, Some(&base));
        if children[1 - index].is_none() {
            assert_unpublished(&context, identities[1 - index]);
            assert_unpublished(&context, providers[1 - index]);
        }
        children[index] = Some(members);
        bases[index] = Some(base);
    }
    let children = children.map(Option::unwrap);
    let bases = bases.map(Option::unwrap);
    assert_ne!(
        children[0].shells().instance_type(),
        children[1].shells().instance_type()
    );
    assert_ne!(
        bases[0].shells().instance_type(),
        bases[1].shells().instance_type()
    );
    assert_ne!(
        bases[0].shells().value_type(),
        bases[1].shells().value_type()
    );
    assert_ne!(
        children[0].base().unwrap().symbol(),
        children[1].base().unwrap().symbol()
    );
    if first == FirstDemand::Members {
        assert!(!is_checked(&context, AMBIENT_FILE));
        assert!(!is_checked(&context, MAIN_FILE));
        assert!(context.diagnostics().is_empty());
    }
    for file in files {
        context.check_source_file(file).unwrap();
    }
    assert!(is_checked(&context, AMBIENT_FILE));
    assert!(is_checked(&context, MAIN_FILE));
    assert_original_diagnostic(&context);
    for index in order {
        assert_location_queries(
            &mut context,
            &javascript,
            identities[index],
            &children[index],
            &bases[index],
        );
    }
    let warm = snapshot(&context, &ambient, &javascript);
    for _ in 0..2 {
        for index in order.into_iter().rev() {
            assert_eq!(
                context
                    .get_nongeneric_class_members(identities[index].owner)
                    .unwrap(),
                children[index]
            );
            assert_eq!(
                context
                    .get_nongeneric_class_members(providers[index].owner)
                    .unwrap(),
                bases[index]
            );
            assert_published_class(&context, providers[index], &bases[index], None);
            assert_published_class(
                &context,
                identities[index],
                &children[index],
                Some(&bases[index]),
            );
            assert_location_queries(
                &mut context,
                &javascript,
                identities[index],
                &children[index],
                &bases[index],
            );
        }
        for file in files {
            context.check_source_file(file).unwrap();
            context.recheck_source_file(file).unwrap();
        }
        assert_original_diagnostic(&context);
        assert_eq!(snapshot(&context, &ambient, &javascript), warm);
    }
}

#[test]
fn js_class_base_publication_keeps_written_bases_after_source_checking() {
    for reverse in [false, true] {
        assert_publication_order(FirstDemand::SourceCheck, reverse);
    }
}

#[test]
fn js_class_base_publication_keeps_written_bases_before_source_checking() {
    for reverse in [false, true] {
        assert_publication_order(FirstDemand::Members, reverse);
    }
}

#[test]
fn js_class_base_publication_heritage_queries_demand_the_real_class_pair() {
    for reverse in [false, true] {
        assert_publication_order(FirstDemand::Heritage, reverse);
    }
}
