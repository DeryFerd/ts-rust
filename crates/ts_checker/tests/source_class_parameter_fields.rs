use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions, ClassError,
    ClassMembers, ClassUnsupported, DeclaredTypeLinks, IntrinsicBootstrapOptions,
    RelationStateSnapshot, SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId,
    TypeNodeLinks, ValueSymbolLinks, types::TypeFlags,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

// Complete pinned source. This control queries ErrImpl, not the later alias operation.
const ORIGINAL_SOURCE: &str = r"// @target: es2015
// @strict: true

class ErrImpl<E> {
  e!: E;
}

declare const Err: typeof ErrImpl & (<T>() => T);

type ErrAlias<U> = typeof Err<U>;

declare const e: ErrAlias<number>;
e as ErrAlias<string>;
";

fn checker_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-parameter-fields.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_bind_call_apply: true,
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            strict_property_initialization: true,
            use_unknown_in_catch_variables: true,
            no_implicit_any: true,
            no_implicit_this: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn class_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(class.name?)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing class {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn class_parameters(parsed: &ParseResult, class: NodeRef) -> Vec<NodeRef> {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        panic!("expected a class declaration")
    };
    data.type_parameters
        .as_ref()
        .unwrap()
        .nodes
        .iter()
        .map(|node| NodeRef::new(class.arena, class.file, *node))
        .collect()
}

struct FieldNodes {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
}

fn field_nodes(parsed: &ParseResult, class: NodeRef, expected: &str) -> FieldNodes {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        panic!("expected a class declaration")
    };
    data.members
        .nodes
        .iter()
        .find_map(|node| {
            let NodeData::PropertyDeclaration(field) = &parsed.arena.get(*node)?.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(field.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| FieldNodes {
                declaration: NodeRef::new(class.arena, class.file, *node),
                name: NodeRef::new(class.arena, class.file, field.name),
                annotation: NodeRef::new(class.arena, class.file, field.type_.unwrap()),
            })
        })
        .unwrap_or_else(|| panic!("missing field {expected}"))
}

fn assert_parameters(
    context: &CanonicalCheckerContext<'_>,
    members: &ClassMembers,
    parameters: &[SemanticSymbolId],
    types: &[TypeId],
) {
    let store = context.store();
    let instance = members.shells().instance_type();
    let TypeData::Interface(data) = store.type_payload(instance).unwrap().data() else {
        panic!("the class origin must use interface storage")
    };
    assert_eq!(data.outer_type_parameter_count, 0);
    assert_eq!(
        data.reference.resolved_type_arguments.as_deref(),
        Some(types)
    );
    let Some((this, declared)) = data
        .all_type_parameters
        .as_deref()
        .and_then(<[TypeId]>::split_last)
    else {
        panic!("the class origin must retain its synthetic this parameter")
    };
    assert_eq!(declared, types);
    assert_eq!(data.this_type, Some(*this));
    let TypeData::TypeParameter(this) = store.type_payload(*this).unwrap().data() else {
        panic!("the class this type must remain a type parameter")
    };
    assert!(this.is_this_type);
    assert_eq!(this.constraint, Some(instance));
    assert_eq!(parameters.len(), types.len());
    for (&parameter, &type_) in parameters.iter().zip(types) {
        assert_eq!(
            store.declared_type_links(parameter).unwrap().declared_type,
            Some(type_)
        );
        let record = store.type_payload(type_).unwrap();
        assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
        assert_eq!(record.symbol(), Some(parameter));
        let TypeData::TypeParameter(data) = record.data() else {
            panic!("the field must retain its real class parameter")
        };
        assert!(!data.is_this_type);
        assert!(data.target.is_none());
        assert!(data.mapper.is_none());
    }
}

fn assert_field(
    context: &CanonicalCheckerContext<'_>,
    field: &FieldNodes,
    type_: TypeId,
    optional: bool,
    readonly: bool,
) {
    let property = symbol(context, field.declaration);
    let record = context.store().symbol(property).unwrap();
    let flags = if optional {
        SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL
    } else {
        SymbolFlags::PROPERTY
    };
    assert_eq!(record.flags(), flags);
    assert_eq!(
        record.check_flags(),
        if readonly {
            CheckFlags::READONLY
        } else {
            CheckFlags::NONE
        }
    );
    assert_eq!(record.declarations(), Some(&[field.declaration][..]));
    assert_eq!(record.value_declaration(), Some(field.declaration));
    assert_eq!(
        context.store().value_symbol_links(property),
        Some(&ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        })
    );
    assert_eq!(
        context.store().type_node_links(field.annotation),
        Some(&TypeNodeLinks {
            resolved_type: Some(type_),
            ..TypeNodeLinks::default()
        })
    );
}

#[derive(Debug, PartialEq)]
struct NodeState {
    node: NodeRef,
    symbol: Option<SemanticSymbolId>,
    flags: Option<(SymbolFlags, CheckFlags)>,
    type_links: Option<TypeNodeLinks>,
    symbol_links: Option<SymbolNodeLinks>,
    signature_links: Option<SignatureLinks>,
    declared_links: Option<DeclaredTypeLinks>,
    value_links: Option<ValueSymbolLinks>,
}

#[derive(Debug, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    relations: RelationStateSnapshot,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
    nodes: Vec<NodeState>,
}

fn snapshot(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult, file: FileId) -> Snapshot {
    let store = context.store();
    let bound = context.file(file).unwrap().1;
    Snapshot {
        counts: [
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        relations: store.relation_state_snapshot(),
        source: store
            .source_file_links(context.source_file(file).unwrap())
            .cloned(),
        diagnostics: context.diagnostics().clone(),
        nodes: parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = NodeRef::new(parsed.arena.id(), file, node);
                let symbol = bound
                    .symbol(node)
                    .and_then(|raw| store.get_merged_symbol(raw));
                NodeState {
                    node,
                    symbol,
                    flags: symbol.map(|symbol| {
                        let record = store.symbol(symbol).unwrap();
                        (record.flags(), record.check_flags())
                    }),
                    type_links: store.type_node_links(node).cloned(),
                    symbol_links: store.symbol_node_links(node).cloned(),
                    signature_links: store.signature_links(node).cloned(),
                    declared_links: symbol
                        .and_then(|symbol| store.declared_type_links(symbol).cloned()),
                    value_links: symbol
                        .and_then(|symbol| store.value_symbol_links(symbol).cloned()),
                }
            })
            .collect(),
    }
}

#[test]
fn original_alias_fixture_retains_own_parameter_field_in_both_query_orders() {
    let parsed = parse_source_file(ORIGINAL_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let class = class_declaration(&parsed, file, "ErrImpl");
    let field = field_nodes(&parsed, class, "e");

    for parameter_first in [false, true] {
        let mut context = checker_context(&parsed, file);
        let owner = symbol(&context, class);
        let parameter = symbol(&context, class_parameters(&parsed, class)[0]);
        let earlier =
            parameter_first.then(|| context.get_declared_type_of_symbol(parameter).unwrap());

        let members = context.get_nongeneric_class_members(owner).unwrap();
        let type_ = context.get_declared_type_of_symbol(parameter).unwrap();
        assert!(earlier.is_none_or(|earlier| earlier == type_));
        assert_parameters(&context, &members, &[parameter], &[type_]);
        assert_eq!(
            members.instance_properties(),
            &[symbol(&context, field.declaration)]
        );
        assert!(members.static_properties().is_empty());
        assert_field(&context, &field, type_, false, false);
        assert!(context.diagnostics().is_empty());
        assert!(
            context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .is_none_or(|links| !links.type_checked)
        );

        let warm = snapshot(&context, &parsed, file);
        for _ in 0..2 {
            assert_eq!(
                context.get_nongeneric_class_members(owner).unwrap(),
                members
            );
            assert_eq!(
                context.get_declared_type_of_symbol(parameter).unwrap(),
                type_
            );
            assert_field(&context, &field, type_, false, false);
            assert_eq!(snapshot(&context, &parsed, file), warm);
        }
    }
}

#[test]
fn pair_fields_keep_distinct_parameters_in_source_order_and_replay() {
    let parsed = parse_source_file("class Pair<L, R> { right!: R; left!: L; again!: L; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let class = class_declaration(&parsed, file, "Pair");
    let mut context = checker_context(&parsed, file);
    let owner = symbol(&context, class);
    let parameters = class_parameters(&parsed, class)
        .into_iter()
        .map(|node| symbol(&context, node))
        .collect::<Vec<_>>();
    assert!(context.store().declared_type_links(owner).is_none());
    assert!(
        parameters
            .iter()
            .all(|parameter| context.store().declared_type_links(*parameter).is_none())
    );

    context.check_source_file(file).unwrap();
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let types = parameters
        .iter()
        .map(|parameter| context.get_declared_type_of_symbol(*parameter).unwrap())
        .collect::<Vec<_>>();
    let [left, right] = types.as_slice() else {
        panic!("Pair must retain both class parameters")
    };
    assert_ne!(left, right);
    assert_parameters(&context, &members, &parameters, &types);
    let fields = [
        (field_nodes(&parsed, class, "right"), *right),
        (field_nodes(&parsed, class, "left"), *left),
        (field_nodes(&parsed, class, "again"), *left),
    ];
    assert_eq!(
        members.instance_properties(),
        fields
            .iter()
            .map(|(field, _)| symbol(&context, field.declaration))
            .collect::<Vec<_>>()
    );
    assert!(members.static_properties().is_empty());
    for (field, type_) in &fields {
        assert_field(&context, field, *type_, false, false);
    }
    assert!(context.diagnostics().is_empty());
    assert!(
        context
            .store()
            .source_file_links(context.source_file(file).unwrap())
            .unwrap()
            .type_checked
    );

    let warm = snapshot(&context, &parsed, file);
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        context.get_nongeneric_class_members(owner).unwrap(),
        members
    );
    assert_parameters(&context, &members, &parameters, &types);
    for (field, type_) in &fields {
        assert_field(&context, field, *type_, false, false);
    }
    assert_eq!(snapshot(&context, &parsed, file), warm);
}

#[test]
fn own_parameter_fields_preserve_modifiers_and_strict_initialization_diagnostic() {
    let parsed = parse_source_file(concat!(
        "class Fields<E> {\n",
        "  readonly optional?: E;\n",
        "  definite!: E;\n",
        "  missing: E;\n",
        "}\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let class = class_declaration(&parsed, file, "Fields");
    let mut context = checker_context(&parsed, file);
    let owner = symbol(&context, class);
    let parameter = symbol(&context, class_parameters(&parsed, class)[0]);

    context.check_source_file(file).unwrap();
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let type_ = context.get_declared_type_of_symbol(parameter).unwrap();
    assert_parameters(&context, &members, &[parameter], &[type_]);
    let optional = field_nodes(&parsed, class, "optional");
    let definite = field_nodes(&parsed, class, "definite");
    let missing = field_nodes(&parsed, class, "missing");
    assert_field(&context, &optional, type_, true, true);
    assert_field(&context, &definite, type_, false, false);
    assert_field(&context, &missing, type_, false, false);
    assert_eq!(members.instance_properties().len(), 3);

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("only the uninitialized required field must report TS2564")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2564);
    assert_eq!(diagnostic.diagnostic.arguments, ["missing"]);
    assert_eq!(diagnostic.node, Some(missing.name));
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Property 'missing' has no initializer and is not definitely assigned in the constructor."
    );

    let warm = snapshot(&context, &parsed, file);
    for _ in 0..2 {
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
        assert_field(&context, &optional, type_, true, true);
        assert_field(&context, &definite, type_, false, false);
        assert_field(&context, &missing, type_, false, false);
        assert_eq!(snapshot(&context, &parsed, file), warm);
    }
}

fn assert_unsupported(
    source: &str,
    class_name: &str,
    error: impl FnOnce(&ParseResult, NodeRef) -> ClassUnsupported,
) {
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let class = class_declaration(&parsed, file, class_name);
    let mut context = checker_context(&parsed, file);
    let owner = symbol(&context, class);
    let expected = ClassError::Unsupported(error(&parsed, class));
    assert!(context.store().declared_type_links(owner).is_none());
    assert!(context.store().value_symbol_links(owner).is_none());
    let cold = snapshot(&context, &parsed, file);
    for _ in 0..2 {
        assert_eq!(context.get_nongeneric_class_members(owner), Err(expected));
        assert_eq!(snapshot(&context, &parsed, file), cold);
    }
}

#[test]
fn unsupported_parameter_fields_leave_static_initialized_and_inherited_queries_cold() {
    assert_unsupported(
        "class Static<E> { static value: E; }",
        "Static",
        |parsed, class| ClassUnsupported::PropertyType {
            node: field_nodes(parsed, class, "value").annotation,
            kind: SyntaxKind::TypeReference,
        },
    );
    assert_unsupported(
        "class Initialized<E> { value: E = 1; }",
        "Initialized",
        |parsed, class| {
            ClassUnsupported::PropertyInitializer(field_nodes(parsed, class, "value").declaration)
        },
    );
    assert_unsupported(
        "class Base<E> { value!: E; } class Derived<E> extends Base<E> {}",
        "Derived",
        |parsed, class| {
            let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data
            else {
                panic!("expected the derived class")
            };
            let clause = data.heritage_clauses.as_ref().unwrap().nodes[0];
            let NodeData::HeritageClause(data) = &parsed.arena.get(clause).unwrap().data else {
                panic!("expected the extends clause")
            };
            ClassUnsupported::Heritage(NodeRef::new(class.arena, class.file, data.types.nodes[0]))
        },
    );
}
