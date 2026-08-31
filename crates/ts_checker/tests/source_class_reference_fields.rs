use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, RelationStateSnapshot, SourceFileLinks, SymbolNodeLinks, TypeData,
    TypeId, TypeMapperId, TypeMapperKind, TypeNodeLinks, ValueSymbolLinks,
    types::{ObjectFlags, TypeFlags},
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "class Box<T> { value!: T; }\n",
    "declare const text: Box<string>;\n",
    "declare const count: Box<number>;\n",
    "const s: string = text.value;\n",
    "const n: number = count.value;\n",
    "const bad: number = text.value;\n",
);

fn checker_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-reference-fields.ts\""),
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
                exact_optional_property_types: false,
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

fn class_declaration(parsed: &ParseResult, file: FileId) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::ClassDeclaration(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

struct VariableNodes {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
    initializer: Option<NodeRef>,
}

fn variable(parsed: &ParseResult, file: FileId, expected: &str) -> VariableNodes {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| VariableNodes {
                declaration: NodeRef::new(parsed.arena.id(), file, node),
                name: NodeRef::new(parsed.arena.id(), file, variable.name),
                annotation: NodeRef::new(parsed.arena.id(), file, variable.type_.unwrap()),
                initializer: variable
                    .initializer
                    .map(|node| NodeRef::new(parsed.arena.id(), file, node)),
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

struct FieldNodes {
    declaration: NodeRef,
    annotation: NodeRef,
}

fn field(parsed: &ParseResult, class: NodeRef, expected: &str) -> FieldNodes {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        panic!("expected the class declaration")
    };
    data.members
        .nodes
        .iter()
        .find_map(|&node| {
            let NodeData::PropertyDeclaration(property) = &parsed.arena.get(node)?.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(property.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| FieldNodes {
                declaration: NodeRef::new(class.arena, class.file, node),
                annotation: NodeRef::new(class.arena, class.file, property.type_.unwrap()),
            })
        })
        .unwrap_or_else(|| panic!("missing field {expected}"))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ClassTarget {
    owner: SemanticSymbolId,
    type_: TypeId,
    parameter: TypeId,
    this_type: TypeId,
}

fn class_target(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    class: NodeRef,
) -> ClassTarget {
    let owner = symbol(context, class);
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        panic!("expected the class declaration")
    };
    let [parameter_node] = data.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("Box must retain one declared parameter")
    };
    let parameter_symbol = symbol(
        context,
        NodeRef::new(class.arena, class.file, *parameter_node),
    );
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let type_ = context.get_declared_type_of_symbol(owner).unwrap();
    assert_eq!(members.shells().instance_type(), type_);
    assert_eq!(members.base(), None);
    let parameter = context
        .get_declared_type_of_symbol(parameter_symbol)
        .unwrap();
    let TypeData::Interface(data) = context.store().type_payload(type_).unwrap().data() else {
        panic!("Box must retain the original class interface payload")
    };
    let this_type = data.this_type.unwrap();
    assert_eq!(data.outer_type_parameter_count, 0);
    assert_eq!(
        data.all_type_parameters.as_deref(),
        Some(&[parameter, this_type][..])
    );
    assert_eq!(
        data.reference.resolved_type_arguments.as_deref(),
        Some(&[parameter][..])
    );
    let parameter_record = context.store().type_payload(parameter).unwrap();
    assert_eq!(parameter_record.flags(), TypeFlags::TYPE_PARAMETER);
    assert_eq!(parameter_record.symbol(), Some(parameter_symbol));
    let TypeData::TypeParameter(this) = context.store().type_payload(this_type).unwrap().data()
    else {
        panic!("Box.this must remain a type parameter")
    };
    assert!(this.is_this_type);
    assert_eq!(this.constraint, Some(type_));
    ClassTarget {
        owner,
        type_,
        parameter,
        this_type,
    }
}

fn assert_source_field(
    context: &CanonicalCheckerContext<'_>,
    target: ClassTarget,
    field: &FieldNodes,
    optional: bool,
    readonly: bool,
) {
    let store = context.store();
    let property = symbol(context, field.declaration);
    let record = store.symbol(property).unwrap();
    assert_eq!(record.parent(), Some(target.owner));
    assert_eq!(
        record.flags(),
        SymbolFlags::PROPERTY
            | if optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            }
    );
    assert_eq!(
        record.check_flags(),
        if readonly {
            CheckFlags::READONLY
        } else {
            CheckFlags::NONE
        }
    );
    assert_eq!(
        store.value_symbol_links(property),
        Some(&ValueSymbolLinks {
            resolved_type: Some(target.parameter),
            ..ValueSymbolLinks::default()
        })
    );
    assert_eq!(
        store.type_node_links(field.annotation),
        Some(&TypeNodeLinks {
            resolved_type: Some(target.parameter),
            ..TypeNodeLinks::default()
        })
    );
}

fn assert_field_copy(
    context: &CanonicalCheckerContext<'_>,
    target: ClassTarget,
    field: &FieldNodes,
    reference: TypeId,
    expected: TypeId,
) -> (SemanticSymbolId, TypeMapperId) {
    let store = context.store();
    let original = symbol(context, field.declaration);
    let original_record = store.symbol(original).unwrap();
    let record = store.type_payload(reference).unwrap();
    assert_ne!(reference, target.type_);
    assert_eq!(record.symbol(), Some(target.owner));
    assert!(
        record
            .object_flags()
            .contains(ObjectFlags::REFERENCE | ObjectFlags::MEMBERS_RESOLVED)
    );
    let TypeData::TypeReference(data) = record.data() else {
        panic!("the source annotation must retain a concrete reference")
    };
    assert_eq!(data.object.target, Some(target.type_));
    assert_eq!(
        data.resolved_type_arguments.as_deref(),
        Some(&[expected][..])
    );
    let table = store
        .symbol_table(data.object.structured.members.unwrap())
        .unwrap();
    let copied = table
        .get_source(original_record.name().as_utf8().unwrap())
        .unwrap();
    assert_ne!(copied, original);
    assert!(
        data.object
            .structured
            .properties
            .as_ref()
            .unwrap()
            .contains(&copied)
    );
    let copied_record = store.symbol(copied).unwrap();
    assert_eq!(
        copied_record.flags(),
        original_record.flags() | SymbolFlags::TRANSIENT
    );
    assert_eq!(
        copied_record.check_flags(),
        CheckFlags::INSTANTIATED | original_record.check_flags()
    );
    assert_eq!(copied_record.parent(), original_record.parent());
    assert_eq!(copied_record.declarations(), Some(&[field.declaration][..]));
    assert_eq!(copied_record.value_declaration(), Some(field.declaration));
    let links = store.value_symbol_links(copied).unwrap();
    let mapper = links.mapper.unwrap();
    assert_eq!(
        links,
        &ValueSymbolLinks {
            resolved_type: Some(expected),
            target: Some(original),
            mapper: Some(mapper),
            ..ValueSymbolLinks::default()
        }
    );
    assert_eq!(store.mapper_kind(mapper), Some(TypeMapperKind::Array));
    assert_eq!(store.mapper_maps_this_only(mapper), Some(false));
    assert_eq!(store.map_type(mapper, target.parameter), Some(expected));
    assert_eq!(store.map_type(mapper, target.this_type), Some(reference));
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    for scalar in [bootstrap.string_type, bootstrap.number_type] {
        assert_eq!(store.map_type(mapper, scalar), Some(scalar));
    }
    (copied, mapper)
}

fn assert_read(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    variable: &VariableNodes,
    type_: TypeId,
    property: SemanticSymbolId,
) {
    let access = variable.initializer.unwrap();
    let NodeData::PropertyAccessExpression(data) = &parsed.arena.get(access.node).unwrap().data
    else {
        panic!("the initializer must remain the actual field read")
    };
    assert_eq!(context.get_type_at_location(access).unwrap(), type_);
    assert_eq!(
        context
            .get_symbol_at_location(NodeRef::new(access.arena, access.file, data.name))
            .unwrap(),
        Some(property)
    );
}

#[derive(Debug, Eq, PartialEq)]
struct WarmState {
    counts: [usize; 7],
    relations: RelationStateSnapshot,
    diagnostics: CanonicalCheckerDiagnostics,
    source: Option<SourceFileLinks>,
    nodes: Vec<(NodeRef, Option<TypeNodeLinks>, Option<SymbolNodeLinks>)>,
    values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
}

fn warm_state(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    properties: &[SemanticSymbolId],
) -> WarmState {
    let store = context.store();
    WarmState {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        relations: store.relation_state_snapshot(),
        diagnostics: context.diagnostics().clone(),
        source: store
            .source_file_links(context.source_file(file).unwrap())
            .cloned(),
        nodes: parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = NodeRef::new(parsed.arena.id(), file, node);
                (
                    node,
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                )
            })
            .collect(),
        values: properties
            .iter()
            .map(|&property| (property, store.value_symbol_links(property).cloned()))
            .collect(),
    }
}

#[allow(clippy::too_many_lines)] // Cold queries, source checking, and replay share one source.
fn check_reference_reads(query_first: bool) {
    let parsed = parse_source_file(SOURCE);
    let file = FileId::new(0);
    let mut context = checker_context(&parsed, file);
    let class = class_declaration(&parsed, file);
    let value = field(&parsed, class, "value");
    let text = variable(&parsed, file, "text");
    let count = variable(&parsed, file, "count");
    let s = variable(&parsed, file, "s");
    let n = variable(&parsed, file, "n");
    let bad = variable(&parsed, file, "bad");
    let cold_references = query_first.then(|| {
        let references = [
            context.get_type_from_type_node(text.annotation).unwrap(),
            context.get_type_from_type_node(count.annotation).unwrap(),
        ];
        assert_ne!(references[0], references[1]);
        for reference in references {
            let TypeData::TypeReference(data) =
                context.store().type_payload(reference).unwrap().data()
            else {
                panic!("annotation query must publish a reference identity")
            };
            assert!(data.object.structured.members.is_none());
            assert!(data.object.structured.properties.is_none());
        }
        assert!(
            context
                .store()
                .value_symbol_links(symbol(&context, value.declaration))
                .is_none_or(|links| links.resolved_type.is_none())
        );
        assert!(
            context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
        assert!(context.diagnostics().is_empty());
        references
    });
    if query_first {
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            context
                .get_type_at_location(s.initializer.unwrap())
                .unwrap(),
            string
        );
    } else {
        context.check_source_file(file).unwrap();
    }
    let target = class_target(&mut context, &parsed, class);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let references = [
        context.get_type_from_type_node(text.annotation).unwrap(),
        context.get_type_from_type_node(count.annotation).unwrap(),
    ];
    assert!(cold_references.is_none_or(|cold| cold == references));
    let text_copy = assert_field_copy(&context, target, &value, references[0], string);
    let count_copy = assert_field_copy(&context, target, &value, references[1], number);
    assert_ne!(text_copy.0, count_copy.0);
    assert_ne!(text_copy.1, count_copy.1);
    assert_source_field(&context, target, &value, false, false);
    for (variable, reference) in [(&text, references[0]), (&count, references[1])] {
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol(&context, variable.declaration))
                .unwrap()
                .resolved_type,
            Some(reference)
        );
    }
    assert_read(&mut context, &parsed, &s, string, text_copy.0);
    assert_read(&mut context, &parsed, &n, number, count_copy.0);
    assert_read(&mut context, &parsed, &bad, string, text_copy.0);
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "expected only the bad assignment diagnostic: {:?}",
            context.diagnostics()
        )
    };
    assert_eq!(diagnostic.node, Some(bad.name));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
    assert!(diagnostic.related_information.is_empty());

    let properties = [
        symbol(&context, value.declaration),
        text_copy.0,
        count_copy.0,
    ];
    let warm = warm_state(&context, &parsed, file, &properties);
    for _ in 0..2 {
        context.recheck_source_file(file).unwrap();
        assert_eq!(class_target(&mut context, &parsed, class), target);
        assert_eq!(
            context.get_type_from_type_node(text.annotation).unwrap(),
            references[0]
        );
        assert_eq!(
            context.get_type_from_type_node(count.annotation).unwrap(),
            references[1]
        );
        assert_eq!(
            assert_field_copy(&context, target, &value, references[0], string),
            text_copy
        );
        assert_eq!(
            assert_field_copy(&context, target, &value, references[1], number),
            count_copy
        );
        assert_source_field(&context, target, &value, false, false);
        assert_read(&mut context, &parsed, &s, string, text_copy.0);
        assert_read(&mut context, &parsed, &n, number, count_copy.0);
        assert_read(&mut context, &parsed, &bad, string, text_copy.0);
        assert_eq!(warm_state(&context, &parsed, file, &properties), warm);
    }
}

#[test]
fn source_first_class_references_keep_independent_field_substitutions() {
    check_reference_reads(false);
}

#[test]
fn query_first_class_references_keep_cold_identities_and_replay_source_reads() {
    check_reference_reads(true);
}

#[test]
fn class_reference_fields_preserve_readonly_and_optional_read_types() {
    let parsed = parse_source_file(concat!(
        "class Box<T> { readonly value!: T; optional?: T; }\n",
        "declare const text: Box<string>;\n",
        "const exact: string = text.value;\n",
        "const maybe: string | undefined = text.optional;\n",
    ));
    let file = FileId::new(1);
    let mut context = checker_context(&parsed, file);
    let class = class_declaration(&parsed, file);
    let value = field(&parsed, class, "value");
    let optional = field(&parsed, class, "optional");
    let text = variable(&parsed, file, "text");
    let exact = variable(&parsed, file, "exact");
    let maybe = variable(&parsed, file, "maybe");

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let target = class_target(&mut context, &parsed, class);
    let reference = context.get_type_from_type_node(text.annotation).unwrap();
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let undefined = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .undefined_type;
    let value_copy = assert_field_copy(&context, target, &value, reference, string);
    let optional_copy = assert_field_copy(&context, target, &optional, reference, string);
    assert_ne!(value_copy.0, optional_copy.0);
    assert_eq!(value_copy.1, optional_copy.1);
    assert_source_field(&context, target, &value, false, true);
    assert_source_field(&context, target, &optional, true, false);
    let maybe_type = context.get_type_from_type_node(maybe.annotation).unwrap();
    let TypeData::Union(union) = context.store().type_payload(maybe_type).unwrap().data() else {
        panic!("optional field reads must include undefined")
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&string));
    assert!(union.union.types.contains(&undefined));
    assert_read(&mut context, &parsed, &exact, string, value_copy.0);
    assert_read(&mut context, &parsed, &maybe, maybe_type, optional_copy.0);
    let properties = [
        symbol(&context, value.declaration),
        symbol(&context, optional.declaration),
        value_copy.0,
        optional_copy.0,
    ];
    let warm = warm_state(&context, &parsed, file, &properties);

    context.recheck_source_file(file).unwrap();
    assert_eq!(class_target(&mut context, &parsed, class), target);
    assert_eq!(
        context.get_type_from_type_node(text.annotation).unwrap(),
        reference
    );
    assert_eq!(
        assert_field_copy(&context, target, &value, reference, string),
        value_copy
    );
    assert_eq!(
        assert_field_copy(&context, target, &optional, reference, string),
        optional_copy
    );
    assert_source_field(&context, target, &value, false, true);
    assert_source_field(&context, target, &optional, true, false);
    assert_read(&mut context, &parsed, &exact, string, value_copy.0);
    assert_read(&mut context, &parsed, &maybe, maybe_type, optional_copy.0);
    assert_eq!(warm_state(&context, &parsed, file, &properties), warm);
}
