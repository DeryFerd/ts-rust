use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
    canonical_has_syntactic_modifier,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    DeclaredTypeLinks, IntrinsicBootstrapOptions, SignatureLinks, SourceFileLinks, SymbolNodeLinks,
    TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
    signatures::SignatureFlags,
    types::{ObjectFlags, TypeFlags},
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(202_450);
const FILE: FileId = FileId::new(202_451);
const LIBRARY: &str = "interface Array<T> {} interface ReadonlyArray<T> {}";
const SELF_CLASS: &str =
    "class A { next: A | null = null; constructor(readonly children: (A | null)[]) {} }";

fn context<'a>(library: &'a ParseResult, parsed: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (source, file, path, declaration, default_library) in [
        (library, LIBRARY_FILE, "\"/project/lib.d.ts\"", true, true),
        (
            parsed,
            FILE,
            "\"/project/class-field-annotations.ts\"",
            false,
            false,
        ),
    ] {
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    default_library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&source.arena, file)
            .unwrap();
    }
    let context = CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY_FILE, &library.arena), (FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_property_initialization: true,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();
    let store = context.store();
    let bound = context.file(LIBRARY_FILE).unwrap().1;
    let locals = store
        .symbol_table(bound.locals(bound.source_file()).unwrap())
        .unwrap();
    let globals = store.symbol_table(context.globals()).unwrap();
    for (name, target) in [
        ("Array", context.global_types().array_type),
        ("ReadonlyArray", context.global_types().readonly_array_type),
    ] {
        let symbol = store
            .get_merged_symbol(locals.get_source(name).unwrap())
            .unwrap();
        assert_eq!(globals.get_source(name), Some(symbol));
        assert_eq!(
            store.symbol(symbol).unwrap().flags(),
            SymbolFlags::INTERFACE
        );
        let [declaration] = store.symbol(symbol).unwrap().declarations().unwrap() else {
            panic!("the array target must retain its real library declaration")
        };
        assert!(declaration.is_for(library.arena.id(), LIBRARY_FILE));
        assert_eq!(bound.symbol(*declaration), Some(symbol));
        assert_eq!(
            store.declared_type_links(symbol).unwrap().declared_type,
            Some(target)
        );
        assert_eq!(store.type_payload(target).unwrap().symbol(), Some(symbol));
        assert_ne!(
            target,
            store.intrinsic_bootstrap().unwrap().empty_object_type
        );
    }
    assert_ne!(
        context.global_types().array_type,
        context.global_types().readonly_array_type
    );
    context
}

fn class(
    parsed: &ParseResult,
    context: &CanonicalCheckerContext<'_>,
    name: &str,
) -> (NodeRef, SemanticSymbolId) {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(class.name?).unwrap().data
            else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap();
    let symbol = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    (
        declaration,
        context.store().get_merged_symbol(symbol).unwrap(),
    )
}

struct Field {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
    initializer: Option<NodeRef>,
    is_static: bool,
    readonly: bool,
}

fn field(parsed: &ParseResult, class: NodeRef, name: &str, is_static: bool) -> Field {
    let NodeData::ClassDeclaration(class) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    class
        .members
        .nodes
        .iter()
        .find_map(|node| {
            let NodeData::PropertyDeclaration(property) = &parsed.arena.get(*node).unwrap().data
            else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(property.name).unwrap().data
            else {
                return None;
            };
            if identifier.text != name
                || canonical_has_syntactic_modifier(&parsed.arena, *node, SyntaxKind::StaticKeyword)
                    != is_static
            {
                return None;
            }
            let reference = |node| NodeRef::new(parsed.arena.id(), FILE, node);
            Some(Field {
                declaration: reference(*node),
                name: reference(property.name),
                annotation: reference(property.type_.unwrap()),
                initializer: property.initializer.map(reference),
                is_static,
                readonly: canonical_has_syntactic_modifier(
                    &parsed.arena,
                    *node,
                    SyntaxKind::ReadonlyKeyword,
                ),
            })
        })
        .unwrap()
}

fn field_type(
    context: &mut CanonicalCheckerContext<'_>,
    owner: SemanticSymbolId,
    field: &Field,
) -> (SemanticSymbolId, TypeId) {
    let store = context.store();
    let symbol = context
        .file(FILE)
        .unwrap()
        .1
        .symbol(field.declaration)
        .unwrap();
    let record = store.symbol(symbol).unwrap();
    let class = store.symbol(owner).unwrap();
    let (table, other) = if field.is_static {
        (class.exports(), class.members())
    } else {
        (class.members(), class.exports())
    };
    assert_eq!(
        store
            .symbol_table(table.unwrap())
            .unwrap()
            .get_source(record.name()),
        Some(symbol)
    );
    assert_ne!(
        other
            .and_then(|table| store.symbol_table(table))
            .and_then(|table| table.get_source(record.name())),
        Some(symbol)
    );
    assert_eq!(record.flags(), SymbolFlags::PROPERTY);
    assert_eq!(record.parent(), Some(owner));
    assert_eq!(record.declarations(), Some(&[field.declaration][..]));
    assert_eq!(record.value_declaration(), Some(field.declaration));
    assert_eq!(
        record.check_flags().contains(CheckFlags::READONLY),
        field.readonly
    );
    let type_ = store
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(
        context.get_type_at_location(field.annotation).unwrap(),
        type_
    );
    assert_eq!(context.get_type_at_location(field.name).unwrap(), type_);
    assert_eq!(
        context.get_symbol_at_location(field.name).unwrap(),
        Some(symbol)
    );
    (symbol, type_)
}

fn assert_union(context: &CanonicalCheckerContext<'_>, type_: TypeId, expected: &[TypeId]) {
    let record = context.store().type_payload(type_).unwrap();
    let TypeData::Union(union) = record.data() else {
        panic!("the written union must remain a union")
    };
    assert_eq!(record.flags(), TypeFlags::UNION);
    assert_eq!(union.union.types, expected);
}

fn assert_array(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    element: TypeId,
    readonly: bool,
) {
    let record = context.store().type_payload(type_).unwrap();
    let TypeData::TypeReference(reference) = record.data() else {
        panic!("the array must use its canonical reference")
    };
    let target = if readonly {
        context.global_types().readonly_array_type
    } else {
        context.global_types().array_type
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[element][..])
    );
}

type NodePublication = (
    NodeRef,
    Option<TypeNodeLinks>,
    Option<SymbolNodeLinks>,
    Option<SignatureLinks>,
);
type SymbolPublication = (
    SemanticSymbolId,
    Option<DeclaredTypeLinks>,
    Option<ValueSymbolLinks>,
);

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 7],
    nodes: Vec<NodePublication>,
    symbols: Vec<SymbolPublication>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn publication(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Publication {
    let store = context.store();
    Publication {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = NodeRef::new(parsed.arena.id(), FILE, node);
                (
                    node,
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
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
                )
            })
            .collect(),
        source: store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let warm = publication(context, parsed);
    context.check_source_file(FILE).unwrap();
    assert_eq!(publication(context, parsed), warm);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(publication(context, parsed), warm);
}

#[test]
#[allow(clippy::too_many_lines)] // The self union, parameter property, and construction share one source identity.
fn self_class_array_annotations_keep_parameter_property_and_construction_identity() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(&format!("{SELF_CLASS}\nconst root = new A([]);\n"));
    let mut context = context(&library, &parsed);
    let (declaration, owner) = class(&parsed, &context, "A");
    let next = field(&parsed, declaration, "next", false);
    let constructor = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::Constructor && record.parent == Some(declaration.node))
                .then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap();
    let NodeData::ConstructorDeclaration(data) = &parsed.arena.get(constructor.node).unwrap().data
    else {
        unreachable!()
    };
    let [parameter] = data.parameters.nodes.as_slice() else {
        panic!("the original constructor has one parameter")
    };
    let parameter = NodeRef::new(parsed.arena.id(), FILE, *parameter);
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    let annotation = NodeRef::new(parsed.arena.id(), FILE, data.type_.unwrap());
    let name = NodeRef::new(parsed.arena.id(), FILE, data.name);
    let bound = context.file(FILE).unwrap().1;
    let property = bound.symbol(parameter).unwrap();
    let local = context
        .store()
        .symbol_table(bound.locals(constructor).unwrap())
        .unwrap()
        .get_source("children")
        .unwrap();
    assert_ne!(local, property);

    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let instance = members.shells().instance_type();
    let (_, next_type) = field_type(&mut context, owner, &next);
    let null = context.store().intrinsic_bootstrap().unwrap().null_type;
    let raw_null = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .null_widening_type;
    assert_union(&context, next_type, &[null, instance]);
    assert_eq!(
        context
            .get_type_at_location(next.initializer.unwrap())
            .unwrap(),
        raw_null
    );
    assert_eq!(
        context
            .store()
            .type_node_links(next.initializer.unwrap())
            .unwrap()
            .resolved_type,
        Some(raw_null)
    );
    assert_eq!(
        context
            .store()
            .declared_type_links(owner)
            .unwrap()
            .declared_type,
        Some(instance)
    );
    let TypeData::Interface(instance_data) = context.store().type_payload(instance).unwrap().data()
    else {
        panic!("the class must retain its instance")
    };
    assert_ne!(instance_data.this_type, Some(instance));

    let children = context
        .store()
        .value_symbol_links(property)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_array(&context, children, next_type, false);
    assert_eq!(context.get_type_at_location(annotation).unwrap(), children);
    assert_eq!(context.get_type_at_location(name).unwrap(), children);
    assert_eq!(
        context
            .store()
            .value_symbol_links(local)
            .unwrap()
            .resolved_type,
        Some(children)
    );
    let local_record = context.store().symbol(local).unwrap();
    assert_eq!(local_record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
    assert_eq!(local_record.check_flags(), CheckFlags::NONE);
    assert_eq!(local_record.parent(), None);
    assert_eq!(local_record.declarations(), Some(&[parameter][..]));
    let property_record = context.store().symbol(property).unwrap();
    assert_eq!(property_record.flags(), SymbolFlags::PROPERTY);
    assert_eq!(property_record.check_flags(), CheckFlags::READONLY);
    assert_eq!(property_record.parent(), Some(owner));
    assert_eq!(property_record.declarations(), Some(&[parameter][..]));
    assert_eq!(property_record.value_declaration(), Some(parameter));
    assert_eq!(
        context
            .store()
            .symbol_table(members.instance_members().unwrap())
            .unwrap()
            .get_source("children"),
        Some(property)
    );
    assert_eq!(
        context
            .store()
            .symbol_table(members.static_members())
            .unwrap()
            .get_source("children"),
        None
    );

    let signature = members.default_construct_signature();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(record.declaration(), Some(constructor));
    assert_eq!(record.parameters(), [local]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.resolved_return_type(), Some(instance));
    assert_eq!(
        context
            .store()
            .signature_links(constructor)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(signature)
    );
    let construction = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::NewExpression(new) = &record.data else {
                return None;
            };
            Some((NodeRef::new(parsed.arena.id(), FILE, node), new))
        })
        .unwrap();
    let [argument] = construction.1.arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("the original construction passes one array")
    };
    let argument = NodeRef::new(parsed.arena.id(), FILE, *argument);
    assert_eq!(
        parsed.arena.get(argument.node).unwrap().kind,
        SyntaxKind::ArrayLiteralExpression
    );
    let argument_type = context.get_type_at_location(argument).unwrap();
    let never = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .implicit_never_type;
    assert_array(&context, argument_type, never, false);
    assert!(
        context
            .store()
            .type_payload(argument_type)
            .unwrap()
            .object_flags()
            .contains(ObjectFlags::ARRAY_LITERAL)
    );
    assert_eq!(
        context.get_type_at_location(construction.0).unwrap(),
        instance
    );
    assert_eq!(
        context
            .store()
            .signature_links(construction.0)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(signature)
    );
    assert_eq!(
        context
            .get_type_at_location(NodeRef::new(
                parsed.arena.id(),
                FILE,
                construction.1.expression
            ))
            .unwrap(),
        members.shells().value_type()
    );
    let references = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            matches!(&record.data, NodeData::TypeReferenceNode(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                FILE,
                node,
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(references.len(), 2);
    for reference in references {
        assert_eq!(context.get_type_at_location(reference).unwrap(), instance);
    }
    assert_replay(&mut context, &parsed);
    assert_eq!(
        context.get_nongeneric_class_members(owner).unwrap(),
        members
    );
}

#[test]
fn declaration_only_class_annotations_keep_initialization_and_static_ownership() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(concat!(
        "class Fields {\n",
        "  choice!: string | null;\n",
        "  values!: number[];\n",
        "  readonly frozen!: readonly string[];\n",
        "  missingUnion: string | null;\n",
        "  missingArray: number[];\n",
        "  static values: number[];\n",
        "}\n",
    ));
    let mut context = context(&library, &parsed);
    let (declaration, owner) = class(&parsed, &context, "Fields");
    let choice = field(&parsed, declaration, "choice", false);
    let values = field(&parsed, declaration, "values", false);
    let frozen = field(&parsed, declaration, "frozen", false);
    let missing_union = field(&parsed, declaration, "missingUnion", false);
    let missing_array = field(&parsed, declaration, "missingArray", false);
    let static_values = field(&parsed, declaration, "values", true);
    for field in [
        &choice,
        &values,
        &frozen,
        &missing_union,
        &missing_array,
        &static_values,
    ] {
        assert!(field.initializer.is_none());
    }

    context.check_source_file(FILE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    for (diagnostic, field, name) in [
        (&diagnostics[0], &missing_union, "missingUnion"),
        (&diagnostics[1], &missing_array, "missingArray"),
    ] {
        assert_eq!(diagnostic.node, Some(field.name));
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(diagnostic.diagnostic.code(), 2564);
        assert_eq!(diagnostic.diagnostic.arguments, [name]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            format!(
                "Property '{name}' has no initializer and is not definitely assigned in the constructor."
            )
        );
    }
    let (_, choice_type) = field_type(&mut context, owner, &choice);
    let (value_symbol, value_type) = field_type(&mut context, owner, &values);
    let (_, frozen_type) = field_type(&mut context, owner, &frozen);
    assert_eq!(
        field_type(&mut context, owner, &missing_union).1,
        choice_type
    );
    assert_eq!(
        field_type(&mut context, owner, &missing_array).1,
        value_type
    );
    let (static_symbol, static_type) = field_type(&mut context, owner, &static_values);
    assert_ne!(static_symbol, value_symbol);
    assert_eq!(static_type, value_type);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_union(
        &context,
        choice_type,
        &[bootstrap.null_type, bootstrap.string_type],
    );
    assert_array(&context, value_type, bootstrap.number_type, false);
    assert_array(&context, frozen_type, bootstrap.string_type, true);
    let members = context.get_nongeneric_class_members(owner).unwrap();
    assert_eq!(
        context
            .store()
            .symbol_table(members.instance_members().unwrap())
            .unwrap()
            .get_source("values"),
        Some(value_symbol)
    );
    assert_eq!(
        context
            .store()
            .symbol_table(members.static_members())
            .unwrap()
            .get_source("values"),
        Some(static_symbol)
    );
    assert_replay(&mut context, &parsed);
    assert_eq!(
        context.get_nongeneric_class_members(owner).unwrap(),
        members
    );
}

#[test]
fn invalid_class_annotation_writes_keep_exact_diagnostics_and_declared_types() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(concat!(
        "class Writes {\n",
        "  choice!: string | null;\n",
        "  items!: number[];\n",
        "  constructor(value: number) {\n",
        "    this.choice = value;\n",
        "    this.items = null;\n",
        "  }\n",
        "}\n",
    ));
    let mut context = context(&library, &parsed);
    let (declaration, owner) = class(&parsed, &context, "Writes");
    let choice = field(&parsed, declaration, "choice", false);
    let items = field(&parsed, declaration, "items", false);
    let mut assignments = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::BinaryExpression(binary) = &record.data else {
                return None;
            };
            let reference = |node| NodeRef::new(parsed.arena.id(), FILE, node);
            Some((
                reference(node),
                reference(binary.left),
                reference(binary.right),
            ))
        })
        .collect::<Vec<_>>();
    assignments.sort_by_key(|(node, _, _)| parsed.arena.get(node.node).unwrap().range.start);
    assert_eq!(assignments.len(), 2);

    context.check_source_file(FILE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    for (diagnostic, assignment, source, target) in [
        (&diagnostics[0], assignments[0], "number", "string"),
        (&diagnostics[1], assignments[1], "null", "number[]"),
    ] {
        assert_eq!(diagnostic.node, Some(assignment.1));
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, [source, target]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            format!("Type '{source}' is not assignable to type '{target}'.")
        );
    }
    let (choice_symbol, choice_type) = field_type(&mut context, owner, &choice);
    let (items_symbol, items_type) = field_type(&mut context, owner, &items);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_union(
        &context,
        choice_type,
        &[bootstrap.null_type, bootstrap.string_type],
    );
    assert_array(&context, items_type, bootstrap.number_type, false);
    let sources = [bootstrap.number_type, bootstrap.null_widening_type];
    for (assignment, symbol, declared, assigned) in [
        (assignments[0], choice_symbol, choice_type, sources[0]),
        (assignments[1], items_symbol, items_type, sources[1]),
    ] {
        assert_eq!(
            context
                .store()
                .symbol_node_links(assignment.1)
                .unwrap()
                .resolved_symbol,
            Some(symbol)
        );
        assert_eq!(
            context
                .store()
                .type_node_links(assignment.1)
                .unwrap()
                .resolved_type,
            Some(declared)
        );
        assert_eq!(
            context.get_type_at_location(assignment.2).unwrap(),
            assigned
        );
        assert_eq!(
            context.get_type_at_location(assignment.0).unwrap(),
            assigned
        );
    }
    assert_replay(&mut context, &parsed);
}
