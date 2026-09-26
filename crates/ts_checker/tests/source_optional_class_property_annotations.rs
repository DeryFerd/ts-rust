use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags, SymbolTableId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions, ClassMembers,
    DeclaredTypeLinks, IntrinsicBootstrapOptions, SignatureLinks, SourceFileLinks, SymbolNodeLinks,
    TypeAliasLinks, TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
    type_records::LiteralValue,
    types::{ObjectFlags, TypeFlags},
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(203_460);
const SOURCE: FileId = FileId::new(203_461);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(
    library: &'a ParseResult,
    source: &'a ParseResult,
    strict: bool,
    exact: bool,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, default_library) in [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\"", true),
        (
            SOURCE,
            source,
            "\"/project/optional-class-properties.ts\"",
            false,
        ),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    default_library,
                    default_library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY, &library.arena), (SOURCE, &source.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: strict,
                exact_optional_property_types: exact,
            },
            strict_property_initialization: strict,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn named_declaration(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let name_node = match &record.data {
                NodeData::ClassDeclaration(class) => class.name?,
                NodeData::InterfaceDeclaration(interface) => interface.name,
                NodeData::TypeAliasDeclaration(alias) => alias.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(node(parsed, file, id))
        })
        .unwrap_or_else(|| panic!("missing written declaration {name}"))
}

#[derive(Debug)]
struct Field {
    declaration: NodeRef,
    name_node: NodeRef,
    annotation: NodeRef,
    name: String,
    is_static: bool,
    readonly: bool,
}

fn fields(parsed: &ParseResult, class: NodeRef) -> Vec<Field> {
    let NodeData::ClassDeclaration(class) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    class
        .members
        .nodes
        .iter()
        .filter_map(|&id| {
            let NodeData::PropertyDeclaration(property) = &parsed.arena.get(id)?.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(property.name)?.data else {
                panic!("each control keeps its written named property")
            };
            assert!(property.initializer.is_none());
            assert_eq!(
                parsed
                    .arena
                    .get(property.postfix_token.unwrap())
                    .unwrap()
                    .kind,
                SyntaxKind::QuestionToken
            );
            let annotation = property.type_.unwrap();
            assert_eq!(
                parsed.arena.get(annotation).unwrap().kind,
                SyntaxKind::TypeReference
            );
            let has_modifier = |kind| {
                property.modifiers.as_ref().is_some_and(|modifiers| {
                    modifiers
                        .list
                        .nodes
                        .iter()
                        .any(|&modifier| parsed.arena.get(modifier).unwrap().kind == kind)
                })
            };
            Some(Field {
                declaration: node(parsed, SOURCE, id),
                name_node: node(parsed, SOURCE, property.name),
                annotation: node(parsed, SOURCE, annotation),
                name: name.text.clone(),
                is_static: has_modifier(SyntaxKind::StaticKeyword),
                readonly: has_modifier(SyntaxKind::ReadonlyKeyword),
            })
        })
        .collect()
}

fn initializer(parsed: &ParseResult, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (identifier.text == name).then(|| node(parsed, SOURCE, variable.initializer.unwrap()))
        })
        .unwrap()
}

fn assignments(parsed: &ParseResult) -> Vec<(NodeRef, NodeRef, NodeRef)> {
    let mut assignments = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::BinaryExpression(binary) = &record.data else {
                return None;
            };
            matches!(
                parsed.arena.get(binary.left)?.data,
                NodeData::PropertyAccessExpression(_)
            )
            .then_some((
                node(parsed, SOURCE, id),
                node(parsed, SOURCE, binary.left),
                node(parsed, SOURCE, binary.right),
            ))
        })
        .collect::<Vec<_>>();
    assignments
        .sort_by_key(|(expression, _, _)| parsed.arena.get(expression.node).unwrap().range.start);
    assignments
}

fn checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .store()
        .source_file_links(context.source_file(file).unwrap())
        .is_some_and(|links| links.type_checked)
}

#[derive(Debug, Eq, PartialEq)]
struct SymbolState {
    symbol: SemanticSymbolId,
    flags: SymbolFlags,
    checks: CheckFlags,
    parent: Option<SemanticSymbolId>,
    members: Option<SymbolTableId>,
    exports: Option<SymbolTableId>,
    value: Option<ValueSymbolLinks>,
    declared: Option<DeclaredTypeLinks>,
    alias: Option<TypeAliasLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    nodes: Vec<NodeState>,
    symbols: Vec<SymbolState>,
    sources: Vec<Option<SourceFileLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(context: &CanonicalCheckerContext<'_>) -> Snapshot {
    let store = context.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: context
            .file_order()
            .iter()
            .flat_map(|&file| {
                let (arena, _) = context.file(file).unwrap();
                arena.iter().map(move |(id, _)| {
                    let node = NodeRef::new(arena.id(), file, id);
                    NodeState {
                        node,
                        type_: store.type_node_links(node).cloned(),
                        symbol: store.symbol_node_links(node).cloned(),
                        signature: store.signature_links(node).cloned(),
                    }
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, record)| SymbolState {
                symbol,
                flags: record.flags(),
                checks: record.check_flags(),
                parent: record.parent(),
                members: record.members(),
                exports: record.exports(),
                value: store.value_symbol_links(symbol).cloned(),
                declared: store.declared_type_links(symbol).cloned(),
                alias: store.type_alias_links(symbol).cloned(),
            })
            .collect(),
        sources: context
            .file_order()
            .iter()
            .map(|&file| {
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn enter(context: &mut CanonicalCheckerContext<'_>, fields: &[Field], member_first: bool) {
    assert!(!checked(context, SOURCE));
    let first = symbol(context, fields[0].declaration);
    assert!(context.store().value_symbol_links(first).is_none());
    assert!(
        context
            .store()
            .type_node_links(fields[0].annotation)
            .is_none()
    );
    let cold_result = member_first.then(|| {
        let type_ = context.get_class_query_member_type(first).unwrap();
        assert!(!checked(context, SOURCE));
        assert!(!checked(context, LIBRARY));
        assert!(context.diagnostics().is_empty());
        let warm_member = snapshot(context);
        assert_eq!(context.get_class_query_member_type(first), Ok(type_));
        assert_eq!(snapshot(context), warm_member);
        type_
    });
    context.check_source_file(SOURCE).unwrap();
    assert!(checked(context, SOURCE));
    assert!(!checked(context, LIBRARY));
    if let Some(type_) = cold_result {
        assert_eq!(
            context
                .store()
                .value_symbol_links(first)
                .unwrap()
                .resolved_type,
            Some(type_)
        );
    }
}

fn assert_fields(
    context: &mut CanonicalCheckerContext<'_>,
    class: NodeRef,
    fields: &[Field],
    expected: TypeId,
) -> ClassMembers {
    let owner = symbol(context, class);
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let shells = members.shells();
    assert_ne!(shells.instance_type(), shells.value_type());
    assert_eq!(
        context
            .store()
            .type_payload(shells.instance_type())
            .unwrap()
            .symbol(),
        Some(owner)
    );
    assert_eq!(
        context
            .store()
            .type_payload(shells.value_type())
            .unwrap()
            .symbol(),
        Some(owner)
    );
    for field in fields {
        let property = symbol(context, field.declaration);
        let store = context.store();
        let record = store.symbol(property).unwrap();
        assert_eq!(
            record.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL
        );
        assert_eq!(
            record.check_flags(),
            if field.readonly {
                CheckFlags::READONLY
            } else {
                CheckFlags::NONE
            }
        );
        assert_eq!(record.parent(), Some(owner));
        assert_eq!(record.declarations(), Some(&[field.declaration][..]));
        assert_eq!(record.value_declaration(), Some(field.declaration));
        let (table, opposite) = if field.is_static {
            (Some(members.static_members()), members.instance_members())
        } else {
            (members.instance_members(), Some(members.static_members()))
        };
        assert_eq!(
            store
                .symbol_table(table.unwrap())
                .unwrap()
                .get_source(&field.name),
            Some(property)
        );
        assert_ne!(
            opposite
                .and_then(|table| store.symbol_table(table))
                .and_then(|table| table.get_source(&field.name)),
            Some(property)
        );
        assert_eq!(
            store.value_symbol_links(property),
            Some(&ValueSymbolLinks {
                resolved_type: Some(expected),
                ..ValueSymbolLinks::default()
            })
        );
        assert_eq!(context.get_class_query_member_type(property), Ok(expected));
        assert_eq!(
            context.get_type_from_type_node(field.annotation),
            Ok(expected)
        );
        assert_eq!(context.get_type_at_location(field.annotation), Ok(expected));
        let strict = context.options().intrinsic.strict_null_checks;
        assert_optional_read(context, field.name_node, expected, strict);
        assert_eq!(
            context.get_symbol_at_location(field.name_node),
            Ok(Some(property))
        );
    }
    members
}

fn assert_optional_read(
    context: &mut CanonicalCheckerContext<'_>,
    location: NodeRef,
    declared: TypeId,
    strict: bool,
) -> TypeId {
    let read = context.get_type_at_location(location).unwrap();
    if !strict {
        assert_eq!(read, declared);
        return read;
    }
    let store = context.store();
    let undefined = store
        .intrinsic_bootstrap()
        .unwrap()
        .undefined_or_missing_type;
    let expected = match store.type_payload(declared).unwrap().data() {
        TypeData::Union(union) => union.union.types.clone(),
        _ => vec![declared],
    };
    let TypeData::Union(union) = store.type_payload(read).unwrap().data() else {
        panic!("the strict optional read must keep its canonical union")
    };
    assert_eq!(union.union.types.len(), expected.len() + 1);
    assert!(union.union.types.contains(&undefined));
    assert!(
        expected
            .iter()
            .all(|type_| union.union.types.contains(type_))
    );
    assert_ne!(read, declared);
    read
}

fn error_type(context: &mut CanonicalCheckerContext<'_>, library: &ParseResult) -> TypeId {
    let declaration = named_declaration(library, LIBRARY, "Error");
    let owner = symbol(context, declaration);
    let constructor = named_declaration(library, LIBRARY, "ErrorConstructor");
    let constructor_owner = symbol(context, constructor);
    assert_ne!(owner, constructor_owner);
    let record = context.store().symbol(owner).unwrap();
    assert!(record.flags().contains(SymbolFlags::INTERFACE));
    assert!(
        record
            .flags()
            .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
    );
    assert!(record.declarations().unwrap().contains(&declaration));
    let value = record.value_declaration().unwrap();
    let NodeData::VariableDeclaration(variable) = &library.arena.get(value.node).unwrap().data
    else {
        panic!("the real Error value must retain its library variable declaration")
    };
    let NodeData::TypeReferenceNode(reference) =
        &library.arena.get(variable.type_.unwrap()).unwrap().data
    else {
        unreachable!()
    };
    let NodeData::Identifier(name) = &library.arena.get(reference.type_name).unwrap().data else {
        unreachable!()
    };
    assert_eq!(name.text, "ErrorConstructor");
    let type_ = context.get_declared_type_of_symbol(owner).unwrap();
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.flags(), TypeFlags::OBJECT);
    assert!(record.object_flags().contains(ObjectFlags::INTERFACE));
    assert_eq!(record.symbol(), Some(owner));
    assert!(matches!(record.data(), TypeData::Interface(_)));
    assert_eq!(
        context
            .store()
            .declared_type_links(owner)
            .unwrap()
            .declared_type,
        Some(type_)
    );
    type_
}

fn replay(
    context: &mut CanonicalCheckerContext<'_>,
    class: NodeRef,
    fields: &[Field],
    declared: TypeId,
    members: &ClassMembers,
) {
    let warm = snapshot(context);
    for _ in 0..2 {
        context.check_source_file(SOURCE).unwrap();
        context.recheck_source_file(SOURCE).unwrap();
        assert_eq!(&assert_fields(context, class, fields, declared), members);
        assert_eq!(snapshot(context), warm);
    }
}

#[test]
fn optional_library_fields_keep_real_owners_and_reads_in_both_query_orders() {
    let library = parse_source_file(ES5);
    let source = parse_source_file(concat!(
        "class Model {\n",
        "  value?: Error;\n",
        "  readonly fixed?: Error;\n",
        "  static value?: Error;\n",
        "  static readonly fixed?: Error;\n",
        "}\n",
        "declare const model: Model;\n",
        "const instanceRead = model.value;\n",
        "const readonlyRead = model.fixed;\n",
        "const staticRead = Model.value;\n",
        "const staticReadonlyRead = Model.fixed;\n",
    ));
    let class = named_declaration(&source, SOURCE, "Model");
    let fields = fields(&source, class);
    assert_eq!(fields.len(), 4);
    for strict in [false, true] {
        for member_first in [false, true] {
            let mut context = context(&library, &source, strict, false);
            enter(&mut context, &fields, member_first);
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let declared = error_type(&mut context, &library);
            let members = assert_fields(&mut context, class, &fields, declared);
            assert_eq!(members.instance_properties().len(), 2);
            assert_eq!(members.static_properties().len(), 2);
            for (name, field) in [
                ("instanceRead", &fields[0]),
                ("readonlyRead", &fields[1]),
                ("staticRead", &fields[2]),
                ("staticReadonlyRead", &fields[3]),
            ] {
                let location = initializer(&source, name);
                assert_optional_read(&mut context, location, declared, strict);
                assert_eq!(
                    context.get_symbol_at_location(location),
                    Ok(Some(symbol(&context, field.declaration)))
                );
            }
            replay(&mut context, class, &fields, declared, &members);
        }
    }
}

#[test]
fn optional_alias_fields_check_real_writes_without_changing_the_annotation() {
    let library = parse_source_file(ES5);
    let source = parse_source_file(concat!(
        "type Status = 200 | 500;\n",
        "class Reply {\n",
        "  status?: Status;\n",
        "  constructor() {\n",
        "    const before = this.status;\n",
        "    this.status = 200;\n",
        "    const assigned: Status = this.status;\n",
        "    this.status = undefined;\n",
        "    this.status = 'bad';\n",
        "  }\n",
        "}\n",
    ));
    let class = named_declaration(&source, SOURCE, "Reply");
    let fields = fields(&source, class);
    let alias = named_declaration(&source, SOURCE, "Status");
    let writes = assignments(&source);
    assert_eq!(writes.len(), 3);
    for strict in [false, true] {
        for member_first in [false, true] {
            let mut context = context(&library, &source, strict, false);
            enter(&mut context, &fields, member_first);
            let alias_owner = symbol(&context, alias);
            let declared = context.get_declared_type_of_symbol(alias_owner).unwrap();
            let members = assert_fields(&mut context, class, &fields, declared);
            assert_eq!(
                context
                    .store()
                    .type_alias_links(alias_owner)
                    .unwrap()
                    .declared_type,
                Some(declared)
            );
            let record = context.store().type_payload(declared).unwrap();
            let alias_record = context.store().type_alias(record.alias().unwrap()).unwrap();
            assert_eq!(alias_record.symbol(), Some(alias_owner));
            let TypeData::Union(union) = record.data() else {
                panic!("the user alias must retain its written numeric union")
            };
            let mut values = union
                .union
                .types
                .iter()
                .map(|type_| {
                    let TypeData::Literal(literal) =
                        context.store().type_payload(*type_).unwrap().data()
                    else {
                        panic!("each Status member must retain its numeric literal")
                    };
                    let LiteralValue::Number(number) = literal.value else {
                        unreachable!()
                    };
                    assert_eq!(literal.regular_type, *type_);
                    number.to_string()
                })
                .collect::<Vec<_>>();
            values.sort();
            assert_eq!(values, ["200", "500"]);
            let read = assert_optional_read(
                &mut context,
                initializer(&source, "before"),
                declared,
                strict,
            );
            let expected_target = context.type_to_string(read).unwrap();
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!(
                    "only the actual string assignment must fail: {:?}",
                    context.diagnostics()
                )
            };
            assert_eq!(diagnostic.node, Some(writes[2].1));
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.arguments,
                ["\"bad\"".to_owned(), expected_target.clone()]
            );
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!("Type '\"bad\"' is not assignable to type '{expected_target}'.")
            );
            assert!(diagnostic.range_override.is_none());
            assert!(diagnostic.related_information.is_empty());
            let property = symbol(&context, fields[0].declaration);
            for &(expression, left, right) in &writes {
                assert_eq!(context.get_symbol_at_location(left), Ok(Some(property)));
                let rhs = context.get_type_at_location(right).unwrap();
                assert_eq!(context.get_type_at_location(expression), Ok(rhs));
            }
            replay(&mut context, class, &fields, declared, &members);
        }
    }
}

#[test]
fn optional_readonly_library_fields_keep_exact_optional_constructor_writes() {
    let library = parse_source_file(ES5);
    let source = parse_source_file(concat!(
        "class Failure {\n",
        "  readonly cause?: Error;\n",
        "  constructor(input: Error) {\n",
        "    const before = this.cause;\n",
        "    this.cause = input;\n",
        "    const assigned: Error = this.cause;\n",
        "    this.cause = undefined;\n",
        "  }\n",
        "}\n",
    ));
    let class = named_declaration(&source, SOURCE, "Failure");
    let fields = fields(&source, class);
    let writes = assignments(&source);
    assert_eq!(writes.len(), 2);
    for exact in [false, true] {
        for member_first in [false, true] {
            let mut context = context(&library, &source, true, exact);
            enter(&mut context, &fields, member_first);
            let declared = error_type(&mut context, &library);
            let members = assert_fields(&mut context, class, &fields, declared);
            assert_optional_read(&mut context, initializer(&source, "before"), declared, true);
            assert_eq!(
                context.get_type_at_location(initializer(&source, "assigned")),
                Ok(declared)
            );
            if exact {
                let [diagnostic] = context.diagnostics().as_slice() else {
                    panic!(
                        "only the actual undefined write must fail: {:?}",
                        context.diagnostics()
                    )
                };
                assert_eq!(diagnostic.node, Some(writes[1].1));
                assert_eq!(diagnostic.diagnostic.code(), 2412);
                assert_eq!(diagnostic.diagnostic.arguments, ["undefined", "Error"]);
                assert!(diagnostic.range_override.is_none());
                assert!(diagnostic.related_information.is_empty());
            } else {
                assert!(
                    context.diagnostics().is_empty(),
                    "{:?}",
                    context.diagnostics()
                );
            }
            replay(&mut context, class, &fields, declared, &members);
        }
    }
}
