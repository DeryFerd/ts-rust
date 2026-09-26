use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, ClassMembers, DeclaredTypeLinks, IntrinsicBootstrapOptions,
    NodeLinks, SignatureId, SignatureLinks, SourceCheckError, SourceFileLinks, SymbolNodeLinks,
    TypeData, TypeId, TypeMapperId, TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
    signatures::SignatureFlags,
    type_records::{InterfaceTypeData, ObjectTypeData, TypeParameterData},
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const PROVIDER: FileId = FileId::new(202_960);
const CONSUMER: FileId = FileId::new(202_961);
const BARREL: FileId = FileId::new(202_962);
const UNUSED: FileId = FileId::new(202_963);
const AMBIENT: FileId = FileId::new(202_964);
const CYCLE_A: FileId = FileId::new(202_965);
const CYCLE_B: FileId = FileId::new(202_966);
const BASE: &str = concat!(
    "export class Base {\n",
    "  value = 1;\n",
    "  constructor() {}\n",
    "  read() { return this.value; }\n",
    "}\n",
);
const DIRECT: &str = "import { Base as ImportedBase } from './base'; const Saved = ImportedBase;";

type SourceInput<'arena> = (FileId, &'arena ParseResult, &'static str, bool);

fn module_specifier(parsed: &ParseResult, file: FileId, text: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let specifier = match &record.data {
                NodeData::ImportDeclaration(import) => import.module_specifier,
                NodeData::ExportDeclaration(export) => export.module_specifier?,
                _ => return None,
            };
            let NodeData::StringLiteral(literal) = &parsed.arena.get(specifier)?.data else {
                return None;
            };
            (literal.text == text).then_some(NodeRef::new(parsed.arena.id(), file, specifier))
        })
        .unwrap_or_else(|| panic!("missing module specifier {text}"))
}

fn context<'arena>(
    sources: &[SourceInput<'arena>],
    routes: &[(FileId, &str, FileId)],
    reverse: bool,
) -> CanonicalCheckerContext<'arena> {
    let mut sources = sources.to_vec();
    if reverse {
        sources.reverse();
    }
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, declaration_file) in &sources {
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
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _, _) in &sources {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let resolutions = routes.iter().map(|&(file, text, target)| {
        let parsed = sources.iter().find(|source| source.0 == file).unwrap().1;
        CanonicalModuleResolutionEntry::resolved(
            module_specifier(parsed, file, text),
            CanonicalResolvedModuleInput::new(
                target,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )
    });
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        sources
            .iter()
            .map(|(file, parsed, _, _)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            no_implicit_any: true,
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(resolutions),
    )
    .unwrap()
}

fn declaration(parsed: &ParseResult, file: FileId, kind: SyntaxKind, text: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::ClassDeclaration(class) => class.name?,
                NodeData::ImportSpecifier(import) => import.name,
                NodeData::ExportSpecifier(export) => export.name,
                NodeData::VariableDeclaration(variable) => variable.name,
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::MethodDeclaration(method) => method.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == text).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {text}"))
}

fn only_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
    });
    let node = nodes.next().unwrap_or_else(|| panic!("missing {kind:?}"));
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    node
}

fn initializer(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
    let node = declaration(parsed, file, SyntaxKind::VariableDeclaration, name);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(node.node).unwrap().data else {
        unreachable!()
    };
    NodeRef::new(parsed.arena.id(), file, variable.initializer.unwrap())
}

fn return_expression(parsed: &ParseResult, file: FileId) -> NodeRef {
    let node = only_node(parsed, file, SyntaxKind::ReturnStatement);
    let NodeData::ReturnStatement(statement) = &parsed.arena.get(node.node).unwrap().data else {
        unreachable!()
    };
    NodeRef::new(parsed.arena.id(), file, statement.expression.unwrap())
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn class_symbols(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    name: &str,
) -> (SemanticSymbolId, SemanticSymbolId) {
    let declaration = declaration(parsed, file, SyntaxKind::ClassDeclaration, name);
    let bound = context.file(file).unwrap().1;
    let store = context.store();
    let owner = symbol(context, declaration);
    let module = symbol(context, bound.source_file());
    let owner_record = store.symbol(owner).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::CLASS);
    assert_eq!(owner_record.parent(), Some(module));
    assert_eq!(owner_record.declarations(), Some(&[declaration][..]));
    assert_eq!(owner_record.value_declaration(), Some(declaration));
    assert_eq!(
        store
            .symbol_table(store.symbol(module).unwrap().exports().unwrap())
            .unwrap()
            .get_source(name),
        Some(owner)
    );
    let local = store
        .symbol_table(bound.locals(bound.source_file()).unwrap())
        .unwrap()
        .get_source(name)
        .unwrap();
    let local_record = store.symbol(local).unwrap();
    assert_ne!(local, owner);
    assert_eq!(local_record.flags(), SymbolFlags::EXPORT_VALUE);
    assert_eq!(local_record.export_symbol(), Some(owner));
    assert_eq!(local_record.declarations(), Some(&[declaration][..]));
    (owner, local)
}

fn checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .store()
        .source_file_links(context.source_file(file).unwrap())
        .is_some_and(|links| links.type_checked)
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn cached_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .unwrap()
        .resolved_type
        .unwrap()
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

type NodeSnapshot = (
    NodeRef,
    Option<NodeLinks>,
    Option<TypeNodeLinks>,
    Option<SymbolNodeLinks>,
    Option<SignatureLinks>,
);
type SymbolSnapshot = (
    SemanticSymbolId,
    Option<DeclaredTypeLinks>,
    Option<ValueSymbolLinks>,
    Option<AliasSymbolLinks>,
);

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 9],
    nodes: Vec<NodeSnapshot>,
    symbols: Vec<SymbolSnapshot>,
    types: Vec<TypeSnapshot>,
    signatures: Vec<SignatureSnapshot>,
    sources: Vec<(FileId, Option<SourceFileLinks>)>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(context: &CanonicalCheckerContext<'_>, sources: &[SourceInput<'_>]) -> Snapshot {
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
        nodes: sources
            .iter()
            .flat_map(|&(file, parsed, _, _)| {
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
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.declared_type_links(symbol).cloned(),
                    store.value_symbol_links(symbol).cloned(),
                    store.alias_symbol_links(symbol).cloned(),
                )
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
        sources: sources
            .iter()
            .map(|&(file, _, _, _)| {
                (
                    file,
                    store
                        .source_file_links(context.source_file(file).unwrap())
                        .cloned(),
                )
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

#[allow(clippy::too_many_lines)] // Check the provider's body results and both class identities together.
fn assert_completed_base(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> ClassMembers {
    assert!(checked(context, PROVIDER));
    let (owner, local) = class_symbols(context, parsed, PROVIDER, "Base");
    let class = declaration(parsed, PROVIDER, SyntaxKind::ClassDeclaration, "Base");
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let instance = members.shells().instance_type();
    let value = members.shells().value_type();
    assert_ne!(instance, value);
    assert_eq!(members.shells().symbol(), owner);
    assert_eq!(members.shells().declaration(), class);
    assert_eq!(
        context
            .store()
            .declared_type_links(owner)
            .unwrap()
            .declared_type,
        Some(instance)
    );
    for symbol in [owner, local] {
        assert_eq!(value_type(context, symbol), value);
    }
    for type_ in [instance, value] {
        let record = context.store().type_payload(type_).unwrap();
        assert_eq!(record.symbol(), Some(owner));
        assert_eq!(record.alias(), None);
    }
    let TypeData::Interface(data) = context.store().type_payload(instance).unwrap().data() else {
        panic!("Base retains its instance origin")
    };
    assert!(data.base_types_resolved && data.declared_members_resolved);
    assert_eq!(data.reference.object.target, Some(instance));
    assert_eq!(
        data.reference.resolved_type_arguments.as_deref(),
        Some(&[][..])
    );
    let this = data.this_type.unwrap();
    let record = context.store().type_payload(this).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::TypeParameter(parameter) = record.data() else {
        panic!("the class owns its synthetic this parameter")
    };
    assert!(parameter.is_this_type);
    assert_eq!(parameter.constraint, Some(instance));

    let field = declaration(parsed, PROVIDER, SyntaxKind::PropertyDeclaration, "value");
    let method = declaration(parsed, PROVIDER, SyntaxKind::MethodDeclaration, "read");
    let field_symbol = symbol(context, field);
    let method_symbol = symbol(context, method);
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(
        members.instance_properties(),
        &[field_symbol, method_symbol]
    );
    assert_eq!(value_type(context, field_symbol), number);
    let NodeData::PropertyDeclaration(property) = &parsed.arena.get(field.node).unwrap().data
    else {
        unreachable!()
    };
    let initializer = NodeRef::new(parsed.arena.id(), PROVIDER, property.initializer.unwrap());
    let initial_type = cached_type(context, initializer);
    assert_ne!(initial_type, number);
    assert_eq!(context.type_to_string(initial_type).unwrap(), "1");
    assert_eq!(
        context.store().symbol(field_symbol).unwrap().parent(),
        Some(owner)
    );
    assert_eq!(
        context.store().symbol(method_symbol).unwrap().parent(),
        Some(owner)
    );
    assert_eq!(
        context.store().symbol(method_symbol).unwrap().flags(),
        SymbolFlags::METHOD
    );
    let method_signature = context
        .store()
        .signature_links(method)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let signature = context.store().signature(method_signature).unwrap();
    assert_eq!(signature.declaration(), Some(method));
    assert!(signature.parameters().is_empty());
    assert!(signature.type_parameters().is_empty());
    assert_eq!(signature.resolved_return_type(), Some(number));
    let returned = return_expression(parsed, PROVIDER);
    assert_eq!(cached_type(context, returned), number);
    assert_eq!(
        context
            .store()
            .symbol_node_links(returned)
            .unwrap()
            .resolved_symbol,
        Some(field_symbol)
    );
    assert_eq!(context.get_type_at_location(returned), Ok(number));

    let constructor = only_node(parsed, PROVIDER, SyntaxKind::Constructor);
    let signature = context
        .store()
        .signature(members.default_construct_signature())
        .unwrap();
    assert_eq!(signature.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(signature.declaration(), Some(constructor));
    assert!(signature.parameters().is_empty());
    assert!(signature.type_parameters().is_empty());
    assert_eq!(signature.this_parameter(), None);
    assert_eq!(signature.resolved_return_type(), Some(instance));
    assert_eq!(signature.target(), None);
    assert_eq!(signature.mapper(), None);
    assert_eq!(signature.min_argument_count(), 0);
    let TypeData::Object(data) = context.store().type_payload(value).unwrap().data() else {
        panic!("Base retains its separate constructor value")
    };
    assert_eq!(data.structured.call_signature_count, 0);
    assert_eq!(
        data.structured.signatures.as_deref(),
        Some(&[members.default_construct_signature()][..])
    );
    assert_eq!(
        data.structured.properties.as_deref(),
        Some(&[members.prototype()][..])
    );
    assert_eq!(
        context
            .store()
            .symbol(members.prototype())
            .unwrap()
            .parent(),
        Some(owner)
    );
    assert_eq!(context.get_type_at_location(class), Ok(instance));
    members
}

fn assert_import_value(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    local_name: &str,
    immediate: SemanticSymbolId,
    target: SemanticSymbolId,
    value: TypeId,
) {
    let alias = symbol(
        context,
        declaration(parsed, CONSUMER, SyntaxKind::ImportSpecifier, local_name),
    );
    assert_ne!(alias, target);
    assert_eq!(
        context.store().symbol(alias).unwrap().flags(),
        SymbolFlags::ALIAS
    );
    let links = context.store().alias_symbol_links(alias).unwrap();
    assert_eq!(links.immediate_target, Some(immediate));
    assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    assert_eq!(links.type_only_declaration, None);
    assert_eq!(value_type(context, alias), value);
    let read = initializer(parsed, CONSUMER, "Saved");
    assert_eq!(cached_type(context, read), value);
    assert_eq!(
        context
            .store()
            .symbol_node_links(read)
            .unwrap()
            .resolved_symbol,
        Some(alias)
    );
    assert_eq!(context.get_type_at_location(read), Ok(value));
    assert_eq!(context.get_symbol_at_location(read), Ok(Some(alias)));
    let saved = symbol(
        context,
        declaration(parsed, CONSUMER, SyntaxKind::VariableDeclaration, "Saved"),
    );
    assert_eq!(value_type(context, saved), value);
}

#[derive(Clone, Copy)]
enum FirstDemand {
    ConsumerSource,
    ProviderSource,
    ConsumerQuery,
    ProviderHeader,
}

#[test]
#[allow(clippy::too_many_lines)] // The four demand orders share one source and exact replay checks.
fn executable_class_value_imports_complete_real_providers_in_each_query_order() {
    let provider = parse_source_file(BASE);
    let consumer = parse_source_file(DIRECT);
    let sources = [
        (PROVIDER, &provider, "\"/project/base.ts\"", false),
        (CONSUMER, &consumer, "\"/project/consumer.ts\"", false),
    ];
    for reverse in [false, true] {
        for first in [
            FirstDemand::ConsumerSource,
            FirstDemand::ProviderSource,
            FirstDemand::ConsumerQuery,
            FirstDemand::ProviderHeader,
        ] {
            let mut context = context(&sources, &[(CONSUMER, "./base", PROVIDER)], reverse);
            let (owner, local) = class_symbols(&context, &provider, PROVIDER, "Base");
            assert!(!checked(&context, PROVIDER));
            assert!(!checked(&context, CONSUMER));
            for symbol in [owner, local] {
                assert!(context.store().value_symbol_links(symbol).is_none());
            }
            let mut header = None;
            let mut queried = None;
            match first {
                FirstDemand::ConsumerSource => {}
                FirstDemand::ProviderSource => context.check_source_file(PROVIDER).unwrap(),
                FirstDemand::ConsumerQuery => {
                    queried = Some(
                        context
                            .get_type_at_location(initializer(&consumer, CONSUMER, "Saved"))
                            .unwrap(),
                    );
                }
                FirstDemand::ProviderHeader => {
                    header = Some(context.get_nongeneric_class_members(owner).unwrap());
                    assert!(!checked(&context, PROVIDER));
                    assert!(!checked(&context, CONSUMER));
                    assert!(context.store().value_symbol_links(local).is_none());
                    let method =
                        declaration(&provider, PROVIDER, SyntaxKind::MethodDeclaration, "read");
                    let signature = context
                        .store()
                        .signature_links(method)
                        .unwrap()
                        .resolved_signature
                        .signature()
                        .unwrap();
                    assert_eq!(
                        context
                            .store()
                            .signature(signature)
                            .unwrap()
                            .resolved_return_type(),
                        None
                    );
                    assert!(
                        context
                            .store()
                            .type_node_links(return_expression(&provider, PROVIDER))
                            .is_none()
                    );
                }
            }
            context.check_source_file(CONSUMER).unwrap();
            assert!(checked(&context, CONSUMER));
            let members = assert_completed_base(&mut context, &provider);
            if let Some(header) = header {
                assert_eq!(members.shells(), header.shells());
                assert_eq!(
                    members.default_construct_signature(),
                    header.default_construct_signature()
                );
            }
            if let Some(queried) = queried {
                assert_eq!(queried, members.shells().value_type());
            }
            assert_import_value(
                &mut context,
                &consumer,
                "ImportedBase",
                owner,
                owner,
                members.shells().value_type(),
            );
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let warm = snapshot(&context, &sources);
            for _ in 0..2 {
                context.recheck_source_file(CONSUMER).unwrap();
                context.recheck_source_file(PROVIDER).unwrap();
                assert_eq!(assert_completed_base(&mut context, &provider), members);
                assert_import_value(
                    &mut context,
                    &consumer,
                    "ImportedBase",
                    owner,
                    owner,
                    members.shells().value_type(),
                );
                assert_eq!(snapshot(&context, &sources), warm);
            }
        }
    }
}

#[test]
fn executable_class_reexports_keep_immediate_alias_and_final_class() {
    let provider = parse_source_file(BASE);
    let barrel = parse_source_file("export { Base as PublicBase } from './base';");
    let consumer = parse_source_file(
        "import { PublicBase as ImportedBase } from './barrel'; const Saved = ImportedBase;",
    );
    let sources = [
        (PROVIDER, &provider, "\"/project/base.ts\"", false),
        (BARREL, &barrel, "\"/project/barrel.ts\"", false),
        (CONSUMER, &consumer, "\"/project/consumer.ts\"", false),
    ];
    for reverse in [false, true] {
        let mut context = context(
            &sources,
            &[(CONSUMER, "./barrel", BARREL), (BARREL, "./base", PROVIDER)],
            reverse,
        );
        let (owner, _) = class_symbols(&context, &provider, PROVIDER, "Base");
        let exported = symbol(
            &context,
            declaration(&barrel, BARREL, SyntaxKind::ExportSpecifier, "PublicBase"),
        );
        assert_ne!(exported, owner);
        context.check_source_file(CONSUMER).unwrap();
        let members = assert_completed_base(&mut context, &provider);
        let links = context.store().alias_symbol_links(exported).unwrap();
        assert_eq!(links.immediate_target, None);
        assert_eq!(links.alias_target, AliasTargetState::Resolved(owner));
        assert_import_value(
            &mut context,
            &consumer,
            "ImportedBase",
            exported,
            owner,
            members.shells().value_type(),
        );
        assert!(context.diagnostics().is_empty());
        let warm = snapshot(&context, &sources);
        for _ in 0..2 {
            context.recheck_source_file(CONSUMER).unwrap();
            context.recheck_source_file(PROVIDER).unwrap();
            assert_import_value(
                &mut context,
                &consumer,
                "ImportedBase",
                exported,
                owner,
                members.shells().value_type(),
            );
            assert_eq!(snapshot(&context, &sources), warm);
        }
    }
}

#[test]
fn unused_executable_class_imports_stay_lazy_beside_ambient_values() {
    let unused = parse_source_file("export class Unused { constructor() { debugger; } }");
    let ambient = parse_source_file("export declare class Ambient { value: number; }");
    let consumer = parse_source_file(concat!(
        "import { Unused } from './unused'; ",
        "import { Ambient as ImportedAmbient } from './ambient'; ",
        "const Saved = ImportedAmbient;",
    ));
    let sources = [
        (UNUSED, &unused, "\"/project/unused.ts\"", false),
        (AMBIENT, &ambient, "\"/project/ambient.d.ts\"", true),
        (CONSUMER, &consumer, "\"/project/consumer.ts\"", false),
    ];
    let mut context = context(
        &sources,
        &[
            (CONSUMER, "./unused", UNUSED),
            (CONSUMER, "./ambient", AMBIENT),
        ],
        false,
    );
    let (unused_owner, unused_local) = class_symbols(&context, &unused, UNUSED, "Unused");
    let (ambient_owner, _) = class_symbols(&context, &ambient, AMBIENT, "Ambient");
    let unused_alias = symbol(
        &context,
        declaration(&consumer, CONSUMER, SyntaxKind::ImportSpecifier, "Unused"),
    );
    context.check_source_file(CONSUMER).unwrap();
    assert!(checked(&context, CONSUMER));
    assert!(!checked(&context, UNUSED));
    assert!(!checked(&context, AMBIENT));
    for symbol in [unused_owner, unused_local, unused_alias] {
        assert!(context.store().value_symbol_links(symbol).is_none());
        assert!(context.store().declared_type_links(symbol).is_none());
    }
    assert_eq!(
        context
            .store()
            .alias_symbol_links(unused_alias)
            .unwrap()
            .alias_target,
        AliasTargetState::Resolved(unused_owner)
    );
    assert!(
        context
            .store()
            .signature_links(only_node(&unused, UNUSED, SyntaxKind::Constructor))
            .is_none()
    );
    let ambient_value = value_type(&context, ambient_owner);
    assert_import_value(
        &mut context,
        &consumer,
        "ImportedAmbient",
        ambient_owner,
        ambient_owner,
        ambient_value,
    );
    assert!(context.diagnostics().is_empty());
    let warm = snapshot(&context, &sources);
    for _ in 0..2 {
        context.recheck_source_file(CONSUMER).unwrap();
        assert_eq!(snapshot(&context, &sources), warm);
    }
}

#[test]
fn type_only_executable_class_imports_reject_values_without_checking_provider() {
    let provider = parse_source_file(BASE);
    let consumer = parse_source_file(
        "import type { Base as ImportedBase } from './base'; const invalid = ImportedBase;",
    );
    let sources = [
        (PROVIDER, &provider, "\"/project/base.ts\"", false),
        (CONSUMER, &consumer, "\"/project/consumer.ts\"", false),
    ];
    let mut context = context(&sources, &[(CONSUMER, "./base", PROVIDER)], false);
    let (owner, local) = class_symbols(&context, &provider, PROVIDER, "Base");
    let alias = symbol(
        &context,
        declaration(
            &consumer,
            CONSUMER,
            SyntaxKind::ImportSpecifier,
            "ImportedBase",
        ),
    );
    let read = initializer(&consumer, CONSUMER, "invalid");
    context.check_source_file(CONSUMER).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the type-only value use has one diagnostic")
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
    assert_eq!(
        cached_type(&context, read),
        context.store().intrinsic_bootstrap().unwrap().error_type
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(read)
            .unwrap()
            .resolved_symbol,
        Some(alias)
    );
    assert!(!checked(&context, PROVIDER));
    for symbol in [owner, local, alias] {
        assert!(context.store().value_symbol_links(symbol).is_none());
    }
    let warm = snapshot(&context, &sources);
    for _ in 0..2 {
        context.recheck_source_file(CONSUMER).unwrap();
        assert_eq!(snapshot(&context, &sources), warm);
    }
}

#[test]
fn executable_class_imports_keep_provider_diagnostics_and_replay() {
    let provider = parse_source_file(&format!("{BASE}const bad: string = 1;"));
    let consumer = parse_source_file(DIRECT);
    let sources = [
        (PROVIDER, &provider, "\"/project/base.ts\"", false),
        (CONSUMER, &consumer, "\"/project/consumer.ts\"", false),
    ];
    let bad = declaration(&provider, PROVIDER, SyntaxKind::VariableDeclaration, "bad");
    let NodeData::VariableDeclaration(variable) = &provider.arena.get(bad.node).unwrap().data
    else {
        unreachable!()
    };
    let bad_name = NodeRef::new(provider.arena.id(), PROVIDER, variable.name);
    for provider_first in [false, true] {
        let mut context = context(&sources, &[(CONSUMER, "./base", PROVIDER)], false);
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        context.check_source_file(CONSUMER).unwrap();
        let members = assert_completed_base(&mut context, &provider);
        let owner = members.shells().symbol();
        assert_import_value(
            &mut context,
            &consumer,
            "ImportedBase",
            owner,
            owner,
            members.shells().value_type(),
        );
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("provider checking retains its one assignment diagnostic")
        };
        assert_eq!(diagnostic.node, Some(bad_name));
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        let warm = snapshot(&context, &sources);
        for _ in 0..2 {
            context.recheck_source_file(CONSUMER).unwrap();
            context.recheck_source_file(PROVIDER).unwrap();
            assert_eq!(snapshot(&context, &sources), warm);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep alias, base, inherited member and constructor identities together.
fn imported_executable_class_heritage_keeps_base_values_and_members() {
    let provider = parse_source_file(BASE);
    let consumer = parse_source_file(concat!(
        "import { Base as ImportedBase } from './base'; ",
        "export class Derived extends ImportedBase { ",
        "readAgain(): number { return this.value; } }",
    ));
    let sources = [
        (PROVIDER, &provider, "\"/project/base.ts\"", false),
        (CONSUMER, &consumer, "\"/project/consumer.ts\"", false),
    ];
    let wrapper = only_node(&consumer, CONSUMER, SyntaxKind::ExpressionWithTypeArguments);
    let NodeData::ExpressionWithTypeArguments(expression) =
        &consumer.arena.get(wrapper.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(expression.type_arguments.is_none());
    let base_expression = NodeRef::new(consumer.arena.id(), CONSUMER, expression.expression);
    let read = return_expression(&consumer, CONSUMER);
    for provider_first in [false, true] {
        let mut context = context(&sources, &[(CONSUMER, "./base", PROVIDER)], provider_first);
        let alias = symbol(
            &context,
            declaration(
                &consumer,
                CONSUMER,
                SyntaxKind::ImportSpecifier,
                "ImportedBase",
            ),
        );
        let (derived_owner, derived_local) =
            class_symbols(&context, &consumer, CONSUMER, "Derived");
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        context.check_source_file(CONSUMER).unwrap();
        let base = assert_completed_base(&mut context, &provider);
        let derived = context.get_nongeneric_class_members(derived_owner).unwrap();
        let inherited = derived.base().unwrap();
        assert_eq!(inherited.symbol(), base.shells().symbol());
        assert_eq!(inherited.instance_type(), base.shells().instance_type());
        assert_eq!(inherited.value_type(), base.shells().value_type());
        assert_ne!(derived.shells().instance_type(), inherited.instance_type());
        assert_ne!(derived.shells().value_type(), inherited.value_type());
        assert_eq!(
            value_type(&context, derived_local),
            derived.shells().value_type()
        );
        assert_eq!(value_type(&context, alias), inherited.value_type());
        let links = context.store().alias_symbol_links(alias).unwrap();
        assert_eq!(links.immediate_target, Some(base.shells().symbol()));
        assert_eq!(
            links.alias_target,
            AliasTargetState::Resolved(base.shells().symbol())
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(base_expression)
                .unwrap()
                .resolved_symbol,
            Some(alias)
        );
        assert_eq!(
            cached_type(&context, base_expression),
            inherited.value_type()
        );
        let field = symbol(
            &context,
            declaration(
                &provider,
                PROVIDER,
                SyntaxKind::PropertyDeclaration,
                "value",
            ),
        );
        let method = symbol(
            &context,
            declaration(&provider, PROVIDER, SyntaxKind::MethodDeclaration, "read"),
        );
        assert!(derived.instance_properties().contains(&field));
        assert!(derived.instance_properties().contains(&method));
        assert_eq!(
            context
                .store()
                .symbol_node_links(read)
                .unwrap()
                .resolved_symbol,
            Some(field)
        );
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(context.get_type_at_location(read), Ok(number));
        let TypeData::Interface(instance) = context
            .store()
            .type_payload(derived.shells().instance_type())
            .unwrap()
            .data()
        else {
            panic!("Derived retains its own instance and actual base")
        };
        assert_eq!(
            instance.resolved_base_constructor_type,
            Some(inherited.value_type())
        );
        assert_eq!(
            instance.resolved_base_types.as_deref(),
            Some(&[inherited.instance_type()][..])
        );
        assert_ne!(
            derived.default_construct_signature(),
            base.default_construct_signature()
        );
        assert_eq!(
            context
                .store()
                .signature(derived.default_construct_signature())
                .unwrap()
                .resolved_return_type(),
            Some(derived.shells().instance_type())
        );
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let warm = snapshot(&context, &sources);
        for _ in 0..2 {
            context.recheck_source_file(CONSUMER).unwrap();
            context.recheck_source_file(PROVIDER).unwrap();
            assert_eq!(
                context.get_nongeneric_class_members(derived_owner),
                Ok(derived.clone())
            );
            assert_eq!(context.get_type_at_location(read), Ok(number));
            assert_eq!(snapshot(&context, &sources), warm);
        }
    }
}

#[test]
fn executable_class_dependency_cycles_close_before_an_independent_import() {
    let first = parse_source_file(concat!(
        "import { Other } from './other'; ",
        "export class Cycle { constructor() {} } ",
        "const selected = Other;",
    ));
    let second = parse_source_file(concat!(
        "import { Cycle } from './cycle'; ",
        "export class Other { constructor() {} } ",
        "const selected = Cycle;",
    ));
    let provider = parse_source_file(BASE);
    let consumer = parse_source_file(DIRECT);
    let sources = [
        (CYCLE_A, &first, "\"/project/cycle.ts\"", false),
        (CYCLE_B, &second, "\"/project/other.ts\"", false),
        (PROVIDER, &provider, "\"/project/base.ts\"", false),
        (CONSUMER, &consumer, "\"/project/consumer.ts\"", false),
    ];
    let mut context = context(
        &sources,
        &[
            (CYCLE_A, "./other", CYCLE_B),
            (CYCLE_B, "./cycle", CYCLE_A),
            (CONSUMER, "./base", PROVIDER),
        ],
        false,
    );
    let closing_read = initializer(&second, CYCLE_B, "selected");
    let expected = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Import(closing_read));
    let aliases =
        [(CYCLE_A, &first, "Other"), (CYCLE_B, &second, "Cycle")].map(|(file, parsed, name)| {
            symbol(
                &context,
                declaration(parsed, file, SyntaxKind::ImportSpecifier, name),
            )
        });
    assert_eq!(context.check_source_file(CYCLE_A), Err(expected));
    for file in [CYCLE_A, CYCLE_B] {
        assert!(!checked(&context, file));
    }
    for alias in aliases {
        assert!(context.store().value_symbol_links(alias).is_none());
    }
    assert!(context.diagnostics().is_empty());
    let failed = snapshot(&context, &sources);
    assert_eq!(context.check_source_file(CYCLE_A), Err(expected));
    assert_eq!(snapshot(&context, &sources), failed);

    context.check_source_file(CONSUMER).unwrap();
    let members = assert_completed_base(&mut context, &provider);
    let owner = members.shells().symbol();
    assert_import_value(
        &mut context,
        &consumer,
        "ImportedBase",
        owner,
        owner,
        members.shells().value_type(),
    );
    assert!(checked(&context, CONSUMER));
    let warm = snapshot(&context, &sources);
    for _ in 0..2 {
        assert_eq!(context.check_source_file(CYCLE_A), Err(expected));
        context.recheck_source_file(CONSUMER).unwrap();
        context.recheck_source_file(PROVIDER).unwrap();
        assert_eq!(snapshot(&context, &sources), warm);
    }
}

#[test]
fn imported_executable_construction_keeps_its_separate_unsupported_boundary() {
    let provider = parse_source_file(BASE);
    let consumer = parse_source_file(
        "import { Base as ImportedBase } from './base'; const made = new ImportedBase();",
    );
    let sources = [
        (PROVIDER, &provider, "\"/project/base.ts\"", false),
        (CONSUMER, &consumer, "\"/project/consumer.ts\"", false),
    ];
    let new = only_node(&consumer, CONSUMER, SyntaxKind::NewExpression);
    let NodeData::NewExpression(construction) = &consumer.arena.get(new.node).unwrap().data else {
        unreachable!()
    };
    let callee = NodeRef::new(consumer.arena.id(), CONSUMER, construction.expression);
    let expected = SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(callee));
    for provider_first in [false, true] {
        let mut context = context(&sources, &[(CONSUMER, "./base", PROVIDER)], false);
        let alias = symbol(
            &context,
            declaration(
                &consumer,
                CONSUMER,
                SyntaxKind::ImportSpecifier,
                "ImportedBase",
            ),
        );
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        assert_eq!(context.check_source_file(CONSUMER), Err(expected));
        assert!(!checked(&context, CONSUMER));
        assert_eq!(checked(&context, PROVIDER), provider_first);
        if !provider_first {
            let (owner, local) = class_symbols(&context, &provider, PROVIDER, "Base");
            for symbol in [owner, local] {
                assert!(context.store().value_symbol_links(symbol).is_none());
            }
        }
        assert!(context.store().value_symbol_links(alias).is_none());
        assert!(context.store().type_node_links(new).is_none());
        assert!(context.store().signature_links(new).is_none());
        assert!(context.diagnostics().is_empty());
        let failed = snapshot(&context, &sources);
        assert_eq!(context.check_source_file(CONSUMER), Err(expected));
        assert_eq!(snapshot(&context, &sources), failed);
    }
}
