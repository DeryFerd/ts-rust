use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, ClassMembers, IntrinsicBootstrapOptions,
    SignatureId, TypeData, TypeId,
    signatures::SignatureFlags,
    types::{ObjectFlags, TypeFlags},
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(205_440);
const SOURCE: FileId = FileId::new(205_441);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (SOURCE, parsed, "\"/project/constructor-object-defaults.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file == LIBRARY,
                    file == LIBRARY,
                    if file == LIBRARY {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            no_implicit_this: true,
            strict_function_types: true,
            strict_property_initialization: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), SOURCE, id)
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == kind).then_some((record.range.start, node(parsed, id)))
        })
        .collect::<Vec<_>>();
    found.sort_by_key(|(start, _)| *start);
    found.into_iter().map(|(_, node)| node).collect()
}

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let found = nodes(parsed, kind);
    let [node] = found.as_slice() else {
        panic!("expected one {kind:?}")
    };
    *node
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let record = parsed.arena.get(id).unwrap();
    let parent_record = parsed.arena.get(parent.node).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(record.range.start >= parent_record.range.start);
    assert!(record.range.end <= parent_record.range.end);
    node(parsed, id)
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(SOURCE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

struct Parts {
    class: NodeRef,
    constructor: NodeRef,
    parameter: NodeRef,
    parameter_name: NodeRef,
    annotation: NodeRef,
    initializer: NodeRef,
    config: NodeRef,
    property: NodeRef,
    property_name: NodeRef,
    field: NodeRef,
    field_annotation: NodeRef,
    assignment: NodeRef,
    write: NodeRef,
    read: NodeRef,
    receiver: NodeRef,
    read_name: NodeRef,
    calls: Vec<NodeRef>,
}

fn parts(parsed: &ParseResult, interface: bool) -> Parts {
    let class = only(parsed, SyntaxKind::ClassDeclaration);
    let constructor = only(parsed, SyntaxKind::Constructor);
    assert_eq!(
        parsed.arena.get(constructor.node).unwrap().parent,
        Some(class.node)
    );
    let NodeData::ConstructorDeclaration(data) = &parsed.arena.get(constructor.node).unwrap().data
    else {
        unreachable!()
    };
    let [parameter] = data.parameters.nodes.as_slice() else {
        panic!("Model has one defaulted parameter")
    };
    let parameter = child(parsed, constructor, *parameter);
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(data.question_token.is_none());
    assert!(data.modifiers.is_none());
    assert!(data.dot_dot_dot_token.is_none());
    let parameter_name = child(parsed, parameter, data.name);
    let annotation = child(parsed, parameter, data.type_.unwrap());
    let initializer = child(parsed, parameter, data.initializer.unwrap());
    let NodeData::ObjectLiteralExpression(object) =
        &parsed.arena.get(initializer.node).unwrap().data
    else {
        panic!("the default must remain a direct object literal")
    };
    assert!(object.properties.nodes.is_empty());
    assert!(!object.properties.has_trailing_comma);

    let config = only(
        parsed,
        if interface {
            SyntaxKind::InterfaceDeclaration
        } else {
            SyntaxKind::TypeAliasDeclaration
        },
    );
    let property = only(parsed, SyntaxKind::PropertySignature);
    let NodeData::PropertySignatureDeclaration(data) =
        &parsed.arena.get(property.node).unwrap().data
    else {
        unreachable!()
    };
    let property_name = child(parsed, property, data.name);
    let field = only(parsed, SyntaxKind::PropertyDeclaration);
    let NodeData::PropertyDeclaration(data) = &parsed.arena.get(field.node).unwrap().data else {
        unreachable!()
    };
    let field_annotation = child(parsed, field, data.type_.unwrap());
    let assignment = only(parsed, SyntaxKind::BinaryExpression);
    let NodeData::BinaryExpression(data) = &parsed.arena.get(assignment.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(
        parsed.arena.get(data.operator_token).unwrap().kind,
        SyntaxKind::EqualsToken
    );
    let write = child(parsed, assignment, data.left);
    let read = child(parsed, assignment, data.right);
    let NodeData::PropertyAccessExpression(data) = &parsed.arena.get(read.node).unwrap().data else {
        unreachable!()
    };
    let receiver = child(parsed, read, data.expression);
    let read_name = child(parsed, read, data.name);
    Parts {
        class,
        constructor,
        parameter,
        parameter_name,
        annotation,
        initializer,
        config,
        property,
        property_name,
        field,
        field_annotation,
        assignment,
        write,
        read,
        receiver,
        read_name,
        calls: nodes(parsed, SyntaxKind::NewExpression),
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Case {
    Valid,
    BadDefault,
    BadArgument,
}

#[derive(Debug, Eq, PartialEq)]
struct Checked {
    members: ClassMembers,
    signature: SignatureId,
    annotation: TypeId,
    initializer: TypeId,
    read: TypeId,
}

#[allow(clippy::too_many_lines)] // Keep the real parameter, default, body read, and call identities together.
fn checked_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parts: &Parts,
    interface: bool,
    case: Case,
) -> Checked {
    let owner = symbol(checker, parts.class);
    let parameter = symbol(checker, parts.parameter);
    let members = checker.get_nongeneric_class_members(owner).unwrap();
    assert_eq!(
        members.declared_instance_properties(),
        [symbol(checker, parts.field)]
    );
    let signature = members.default_construct_signature();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(parts.constructor));
    assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(record.parameters(), [parameter]);
    assert_eq!(record.min_argument_count(), 0);
    assert!(record.type_parameters().is_empty());
    assert_eq!(
        record.resolved_return_type(),
        Some(members.shells().instance_type())
    );
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    let record = checker.store().symbol(parameter).unwrap();
    assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
    assert_eq!(record.declarations(), Some(&[parts.parameter][..]));
    assert_eq!(record.value_declaration(), Some(parts.parameter));

    let annotation = checker.get_type_from_type_node(parts.annotation).unwrap();
    assert_eq!(
        checker
            .store()
            .value_symbol_links(parameter)
            .unwrap()
            .resolved_type,
        Some(annotation)
    );
    for location in [parts.parameter, parts.parameter_name, parts.receiver] {
        assert_eq!(checker.get_type_at_location(location), Ok(annotation));
    }
    for location in [parts.parameter_name, parts.receiver] {
        assert_eq!(checker.get_symbol_at_location(location), Ok(Some(parameter)));
    }
    let config_owner = symbol(checker, parts.config);
    let record = checker.store().type_payload(annotation).unwrap();
    if interface {
        assert_eq!(record.symbol(), Some(config_owner));
    } else {
        assert_eq!(
            checker
                .store()
                .type_alias(record.alias().unwrap())
                .unwrap()
                .symbol(),
            Some(config_owner)
        );
    }
    assert_eq!(checker.type_to_string(annotation).unwrap(), "Config");

    let initializer = checker.get_type_at_location(parts.initializer).unwrap();
    assert_ne!(initializer, annotation);
    let object_owner = symbol(checker, parts.initializer);
    let record = checker.store().type_payload(initializer).unwrap();
    assert_eq!(record.flags(), TypeFlags::OBJECT);
    assert!(
        record
            .object_flags()
            .contains(ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL)
    );
    assert_eq!(record.symbol(), Some(object_owner));
    assert!(record.alias().is_none());
    let TypeData::Object(object) = record.data() else {
        panic!("the default must retain its own object type")
    };
    assert!(object.structured.properties.is_none());
    assert!(
        checker
            .store()
            .symbol_table(object.structured.members.unwrap())
            .unwrap()
            .is_empty()
    );
    let record = checker.store().symbol(object_owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::OBJECT_LITERAL);
    assert_eq!(record.declarations(), Some(&[parts.initializer][..]));
    assert_eq!(record.value_declaration(), Some(parts.initializer));

    let read = checker.get_type_at_location(parts.read).unwrap();
    assert_eq!(checker.get_type_at_location(parts.read_name), Ok(read));
    assert_eq!(checker.get_type_at_location(parts.write), Ok(read));
    assert_eq!(checker.get_type_at_location(parts.assignment), Ok(read));
    assert_eq!(
        checker.get_type_from_type_node(parts.field_annotation),
        Ok(read)
    );
    assert_eq!(
        checker.get_symbol_at_location(parts.read_name),
        Ok(Some(symbol(checker, parts.property)))
    );
    assert_eq!(
        checker.get_symbol_at_location(parts.write),
        Ok(Some(symbol(checker, parts.field)))
    );
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    if case == Case::BadDefault {
        assert_eq!(read, bootstrap.string_type);
    } else {
        let TypeData::Union(union) = checker.store().type_payload(read).unwrap().data() else {
            panic!("reading the optional property must retain undefined")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&bootstrap.string_type));
        assert!(union.union.types.contains(&bootstrap.undefined_type));
    }
    for location in std::iter::once(parts.constructor).chain(parts.calls.iter().copied()) {
        assert_eq!(
            checker
                .store()
                .signature_links(location)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(signature)
        );
    }
    for &call in &parts.calls {
        assert_eq!(
            checker.get_type_at_location(call),
            Ok(members.shells().instance_type())
        );
    }
    Checked {
        members,
        signature,
        annotation,
        initializer,
        read,
    }
}

fn assert_diagnostics(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    parts: &Parts,
    checked: &Checked,
    case: Case,
) {
    if case == Case::Valid {
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        return;
    }
    let argument = if case == Case::BadArgument {
        let NodeData::NewExpression(call) = &parsed.arena.get(parts.calls[0].node).unwrap().data
        else {
            unreachable!()
        };
        let [argument] = call.arguments.as_ref().unwrap().nodes.as_slice() else {
            panic!("the invalid call has one argument")
        };
        let argument = child(parsed, parts.calls[0], *argument);
        let type_ = checker.get_type_at_location(argument).unwrap();
        Some((argument, checker.type_to_string(type_).unwrap()))
    } else {
        None
    };
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected one diagnostic for the actual default or argument")
    };
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert!(diagnostic.range_override.is_none());
    if let Some((argument, display)) = argument {
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.node, Some(argument));
        assert_eq!(
            diagnostic.diagnostic.arguments,
            [display, "Config".to_owned()]
        );
    } else {
        assert_eq!(diagnostic.diagnostic.code(), 2741);
        assert_eq!(diagnostic.node, Some(parts.parameter_name));
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Property 'label' is missing in type '{}' but required in type 'Config'."
        );
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("the missing property must point to its actual declaration")
        };
        assert_eq!(related.node, Some(parts.property_name));
        assert_eq!(related.diagnostic.code(), 2728);
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "'label' is declared here."
        );
        assert_ne!(checked.annotation, checked.initializer);
    }
}

#[allow(clippy::too_many_lines)] // Each query order checks the same source and retained state.
fn check_case(interface: bool, case: Case) {
    let member = if case == Case::BadDefault {
        "label: string"
    } else {
        "label?: string"
    };
    let config = if interface {
        format!("interface Config {{ {member}; }}\n")
    } else {
        format!("type Config = {{ {member} }};\n")
    };
    let field_type = if case == Case::BadDefault {
        "string"
    } else {
        "string | undefined"
    };
    let calls = match case {
        Case::Valid => "new Model();\nnew Model({});\nnew Model({ label: 'ok' });\nnew Model(undefined);\n",
        // The default is checked even when the only call supplies a valid config.
        Case::BadDefault => "new Model({ label: 'ok' });\n",
        Case::BadArgument => "const wrong = { label: 1 };\nnew Model(wrong);\n",
    };
    let text = format!(
        "{config}export class Model {{\n  label: {field_type};\n  constructor(config: Config = {{}}) {{\n    this.label = config.label;\n  }}\n}}\n{calls}"
    );
    let parsed = parse_source_file(&text);
    let library = parse_source_file(ES5);
    let parts = parts(&parsed, interface);
    assert_eq!(parts.calls.len(), if case == Case::Valid { 4 } else { 1 });
    for first in [None, Some(parts.class), Some(parts.initializer)] {
        let mut checker = context(&parsed, &library);
        assert!(checker.global_types().diagnostics().is_empty());
        let root = checker.source_file(SOURCE).unwrap();
        let owner = symbol(&checker, parts.class);
        let header = if first == Some(parts.class) {
            let header = checker.get_nongeneric_class_members(owner).unwrap();
            assert_eq!(
                checker
                    .store()
                    .signature(header.default_construct_signature())
                    .unwrap()
                    .min_argument_count(),
                0
            );
            assert!(checker.store().type_node_links(parts.initializer).is_none());
            assert!(checker.store().type_node_links(parts.read).is_none());
            assert!(
                !checker
                    .store()
                    .source_file_links(root)
                    .is_some_and(|links| links.type_checked)
            );
            assert!(checker.diagnostics().is_empty());
            assert_eq!(
                checker.get_nongeneric_class_members(owner),
                Ok(header.clone())
            );
            Some(header)
        } else {
            None
        };
        let early = if first == Some(parts.initializer) {
            let type_ = checker.get_type_at_location(parts.initializer).unwrap();
            assert!(checker.store().source_file_links(root).unwrap().type_checked);
            Some(type_)
        } else {
            None
        };
        checker.check_source_file(SOURCE).unwrap();
        assert!(checker.store().source_file_links(root).unwrap().type_checked);
        let checked = checked_state(&mut checker, &parts, interface, case);
        if let Some(header) = header {
            assert_eq!(checked.members, header);
        }
        if let Some(early) = early {
            assert_eq!(checked.initializer, early);
        }
        assert_diagnostics(&mut checker, &parsed, &parts, &checked, case);
        let owners = [
            parts.class,
            parts.config,
            parts.parameter,
            parts.property,
            parts.field,
            parts.initializer,
        ]
        .map(|declaration| symbol(&checker, declaration));
        let snapshot = |checker: &CanonicalCheckerContext<'_>| {
            let store = checker.store();
            (
                [
                    store.type_len(),
                    store.type_alias_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.index_info_len(),
                ],
                parsed
                    .arena
                    .iter()
                    .map(|(id, _)| {
                        let location = node(&parsed, id);
                        (
                            store.type_node_links(location).cloned(),
                            store.symbol_node_links(location).cloned(),
                            store.signature_links(location).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                owners.map(|owner| {
                    (
                        store.value_symbol_links(owner).cloned(),
                        store.declared_type_links(owner).cloned(),
                        store.type_alias_links(owner).cloned(),
                    )
                }),
                store.source_file_links(root).cloned(),
                checker.diagnostics().clone(),
            )
        };
        let warm = snapshot(&checker);
        for _ in 0..2 {
            checker.check_source_file(SOURCE).unwrap();
            assert_eq!(checked_state(&mut checker, &parts, interface, case), checked);
            checker.recheck_source_file(SOURCE).unwrap();
            assert_eq!(checked_state(&mut checker, &parts, interface, case), checked);
            assert_diagnostics(&mut checker, &parsed, &parts, &checked, case);
            assert_eq!(snapshot(&checker), warm);
        }
    }
}

#[test]
fn empty_constructor_defaults_keep_alias_and_interface_types_for_body_reads_and_calls() {
    for interface in [false, true] {
        check_case(interface, Case::Valid);
    }
}

#[test]
fn empty_constructor_defaults_report_the_required_property_without_retyping_the_parameter() {
    check_case(false, Case::BadDefault);
}

#[test]
fn empty_constructor_defaults_reject_incompatible_supplied_arguments_and_keep_replay() {
    check_case(false, Case::BadArgument);
}
