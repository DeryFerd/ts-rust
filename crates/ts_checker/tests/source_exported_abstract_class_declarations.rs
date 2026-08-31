use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, ClassMembers, IntrinsicBootstrapOptions,
    TypeData, TypeId, ValueSymbolLinks, signatures::SignatureFlags, types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(68_410);
const BASE: &str = concat!(
    "export abstract class Base {\n",
    "  abstract value: number;\n",
    "  abstract read(): number;\n",
    "  protected seed(): number { return 1; }\n",
    "}\n",
);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/exported-abstract.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::External,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(FILE, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_property_initialization: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn reference(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, node)
}

fn class_declaration(parsed: &ParseResult, expected: &str) -> NodeRef {
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
            (name.text == expected).then_some(reference(parsed, node))
        })
        .unwrap_or_else(|| panic!("missing class {expected}"))
}

fn member(parsed: &ParseResult, class: NodeRef, expected: &str) -> NodeRef {
    let NodeData::ClassDeclaration(class) = &parsed.arena.get(class.node).unwrap().data else {
        panic!("the owner must remain a class declaration")
    };
    class
        .members
        .nodes
        .iter()
        .find_map(|&node| {
            let name = match &parsed.arena.get(node)?.data {
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::MethodDeclaration(method) => method.name,
                _ => return None,
            };
            matches!(&parsed.arena.get(name)?.data, NodeData::Identifier(name) if name.text == expected)
                .then_some(reference(parsed, node))
        })
        .unwrap_or_else(|| panic!("missing member {expected}"))
}

fn variable_initializer(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| reference(parsed, variable.initializer.unwrap()))
        })
        .unwrap_or_else(|| panic!("missing initializer for {expected}"))
}

fn returned_expression(parsed: &ParseResult, method: NodeRef) -> NodeRef {
    let NodeData::MethodDeclaration(method) = &parsed.arena.get(method.node).unwrap().data else {
        panic!("the implementation must remain a method")
    };
    let NodeData::Block(body) = &parsed.arena.get(method.body.unwrap()).unwrap().data else {
        panic!("the method must keep its written body")
    };
    let [statement] = body.statements.nodes.as_slice() else {
        panic!("the body must keep its one return statement")
    };
    let NodeData::ReturnStatement(returned) = &parsed.arena.get(*statement).unwrap().data else {
        panic!("the body statement must remain a return")
    };
    reference(parsed, returned.expression.unwrap())
}

fn bound_symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn checked_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("source checking must retain the type at {node:?}"))
}

fn is_type_checked(context: &CanonicalCheckerContext<'_>) -> bool {
    context
        .source_file(FILE)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

// Check the real export/local pair, not a second class with the same name.
#[allow(clippy::too_many_lines)]
fn assert_exported_identity(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    expected: &str,
    members: &ClassMembers,
    is_abstract: bool,
) {
    let declaration = class_declaration(parsed, expected);
    let bound = context.file(FILE).unwrap().1;
    let owner = bound_symbol(context, declaration);
    let local = bound.local_symbol(declaration).unwrap();
    let module = bound.symbol(bound.source_file()).unwrap();
    let store = context.store();
    let owner_record = store.symbol(owner).unwrap();
    let local_record = store.symbol(local).unwrap();
    assert_ne!(local, owner);
    assert_eq!(store.get_merged_symbol(local), Some(local));
    assert_eq!(owner_record.flags(), SymbolFlags::CLASS);
    assert_eq!(owner_record.parent(), Some(module));
    assert_eq!(owner_record.declarations(), Some(&[declaration][..]));
    assert_eq!(owner_record.value_declaration(), Some(declaration));
    assert_eq!(local_record.flags(), SymbolFlags::EXPORT_VALUE);
    assert_eq!(local_record.declarations(), Some(&[declaration][..]));
    assert_eq!(local_record.export_symbol(), Some(owner));
    assert!(local_record.value_declaration().is_none());
    assert_eq!(
        store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source(expected)),
        Some(owner),
    );
    assert_eq!(
        bound
            .locals(bound.source_file())
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(expected)),
        Some(local),
    );

    let shells = members.shells();
    assert_eq!(shells.symbol(), owner);
    assert_eq!(shells.declaration(), declaration);
    assert_ne!(shells.instance_type(), shells.value_type());
    assert_eq!(
        store.declared_type_links(owner).unwrap().declared_type,
        Some(shells.instance_type()),
    );
    assert!(
        store
            .declared_type_links(local)
            .and_then(|links| links.declared_type)
            .is_none()
    );
    let expected_value = ValueSymbolLinks {
        resolved_type: Some(shells.value_type()),
        ..ValueSymbolLinks::default()
    };
    for symbol in [owner, local] {
        assert_eq!(store.value_symbol_links(symbol), Some(&expected_value));
    }
    let instance = store.type_payload(shells.instance_type()).unwrap();
    assert_eq!(instance.symbol(), Some(owner));
    assert!(instance.object_flags().contains(ObjectFlags::CLASS));
    assert!(matches!(instance.data(), TypeData::Interface(_)));
    let value = store.type_payload(shells.value_type()).unwrap();
    assert_eq!(value.symbol(), Some(owner));
    let TypeData::Object(value) = value.data() else {
        panic!("the constructor value must retain its class object")
    };
    let signature = members.default_construct_signature();
    assert_eq!(value.structured.call_signature_count, 0);
    assert_eq!(
        value.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    let signature = store.signature(signature).unwrap();
    assert_eq!(
        signature.flags(),
        if is_abstract {
            SignatureFlags::CONSTRUCT | SignatureFlags::ABSTRACT
        } else {
            SignatureFlags::CONSTRUCT
        },
    );
    assert!(signature.parameters().is_empty());
    assert!(signature.type_parameters().is_empty());
    assert_eq!(
        signature.resolved_return_type(),
        Some(shells.instance_type())
    );
}

// Keep source links, original symbol links, and allocation counts stable on replay.
fn snapshot(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> String {
    let store = context.store();
    let bound = context.file(FILE).unwrap().1;
    let nodes = parsed
        .arena
        .iter()
        .map(|(node, _)| {
            let node = reference(parsed, node);
            (
                store.type_node_links(node).cloned(),
                store.symbol_node_links(node).cloned(),
                store.signature_links(node).cloned(),
            )
        })
        .collect::<Vec<_>>();
    let symbols = parsed
        .arena
        .iter()
        .flat_map(|(node, _)| {
            let node = reference(parsed, node);
            [bound.symbol(node), bound.local_symbol(node)]
                .into_iter()
                .flatten()
        })
        .map(|symbol| {
            (
                symbol,
                store.symbol(symbol),
                store.declared_type_links(symbol),
                store.value_symbol_links(symbol),
            )
        })
        .collect::<Vec<_>>();
    format!(
        "{:?}",
        (
            [
                store.type_len(),
                store.signature_len(),
                store.symbol_len(),
                store.mapper_len(),
                store.symbol_store().symbol_table_len(),
            ],
            nodes,
            symbols,
            store.source_file_links(bound.source_file()),
            context.diagnostics(),
        )
    )
}

#[test]
#[allow(clippy::too_many_lines)] // Both query orders check the same exported class identities.
fn exported_abstract_identity_survives_source_and_member_query_orders() {
    for members_first in [false, true] {
        let parsed = parse_source_file(BASE);
        let mut context = context(&parsed);
        let declaration = class_declaration(&parsed, "Base");
        let owner = bound_symbol(&context, declaration);
        let bound = context.file(FILE).unwrap().1;
        let local = bound.local_symbol(declaration).unwrap();
        let facts = bound.source_facts().unwrap();
        assert!(facts.is_external_module());
        assert!(!facts.is_declaration_file());
        assert!(!facts.is_javascript_file());
        let NodeData::ClassDeclaration(class) = &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(
            class
                .modifiers
                .as_ref()
                .unwrap()
                .list
                .nodes
                .iter()
                .map(|&node| parsed.arena.get(node).unwrap().kind)
                .collect::<Vec<_>>(),
            [SyntaxKind::ExportKeyword, SyntaxKind::AbstractKeyword],
        );
        for symbol in [owner, local] {
            assert!(context.store().value_symbol_links(symbol).is_none());
        }
        assert!(context.store().declared_type_links(owner).is_none());
        assert!(!is_type_checked(&context));

        let first = members_first.then(|| context.get_nongeneric_class_members(owner).unwrap());
        assert!(!is_type_checked(&context));
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let members = context.get_nongeneric_class_members(owner).unwrap();
        if let Some(first) = first {
            assert_eq!(first, members);
        }
        assert_exported_identity(&context, &parsed, "Base", &members, true);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let value = bound_symbol(&context, member(&parsed, declaration, "value"));
        assert_eq!(
            context
                .store()
                .value_symbol_links(value)
                .unwrap()
                .resolved_type,
            Some(number),
        );
        let read = member(&parsed, declaration, "read");
        let NodeData::MethodDeclaration(read_data) = &parsed.arena.get(read.node).unwrap().data
        else {
            unreachable!()
        };
        assert!(read_data.body.is_none());
        let signature = context
            .store()
            .signature_links(read)
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
            Some(number),
        );
        let returned = returned_expression(&parsed, member(&parsed, declaration, "seed"));
        assert_eq!(
            context
                .type_to_string(checked_type(&context, returned))
                .unwrap(),
            "1",
        );
        assert!(is_type_checked(&context));

        let warm = snapshot(&context, &parsed);
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
        assert_exported_identity(&context, &parsed, "Base", &members, true);
        assert_eq!(snapshot(&context, &parsed), warm);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // The derived member and constructor reads share one base class.
fn concrete_derived_class_implements_abstract_members_and_reads_protected_base_method() {
    let source = format!(
        "{BASE}{}",
        concat!(
            "export class Derived extends Base {\n",
            "  value = 2;\n",
            "  read(): number { return this.seed(); }\n",
            "}\n",
            "const instance = new Derived();\n",
            "const value = instance.value;\n",
            "const result = instance.read();\n",
        ),
    );
    let parsed = parse_source_file(&source);
    let mut context = context(&parsed);
    let base_declaration = class_declaration(&parsed, "Base");
    let derived_declaration = class_declaration(&parsed, "Derived");
    let base_owner = bound_symbol(&context, base_declaration);
    let derived_owner = bound_symbol(&context, derived_declaration);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let base = context.get_nongeneric_class_members(base_owner).unwrap();
    let derived = context.get_nongeneric_class_members(derived_owner).unwrap();
    assert_exported_identity(&context, &parsed, "Base", &base, true);
    assert_exported_identity(&context, &parsed, "Derived", &derived, false);
    let inherited = derived.base().unwrap();
    assert_eq!(inherited.symbol(), base_owner);
    assert_eq!(inherited.instance_type(), base.shells().instance_type());
    assert_eq!(inherited.value_type(), base.shells().value_type());

    let seed = bound_symbol(&context, member(&parsed, base_declaration, "seed"));
    let value = bound_symbol(&context, member(&parsed, derived_declaration, "value"));
    let read = member(&parsed, derived_declaration, "read");
    let read_symbol = bound_symbol(&context, read);
    let table = context
        .store()
        .symbol_table(derived.instance_members().unwrap())
        .unwrap();
    assert_eq!(table.get_source("value"), Some(value));
    assert_eq!(table.get_source("read"), Some(read_symbol));
    assert_eq!(table.get_source("seed"), Some(seed));
    assert_ne!(
        value,
        bound_symbol(&context, member(&parsed, base_declaration, "value"))
    );
    assert_ne!(
        read_symbol,
        bound_symbol(&context, member(&parsed, base_declaration, "read"))
    );
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let inherited_call = returned_expression(&parsed, read);
    let NodeData::CallExpression(call) = &parsed.arena.get(inherited_call.node).unwrap().data
    else {
        panic!("the implementation must call the real inherited method")
    };
    let access = reference(&parsed, call.expression);
    let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(access.node).unwrap().data
    else {
        panic!("the inherited call must keep its property access")
    };
    assert_eq!(
        parsed.arena.get(property.expression).unwrap().kind,
        SyntaxKind::ThisKeyword
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(access)
            .unwrap()
            .resolved_symbol,
        Some(seed)
    );
    for node in [
        inherited_call,
        variable_initializer(&parsed, "value"),
        variable_initializer(&parsed, "result"),
    ] {
        assert_eq!(checked_type(&context, node), number);
        assert_eq!(context.get_type_at_location(node).unwrap(), number);
    }
    let construction = variable_initializer(&parsed, "instance");
    assert_eq!(
        checked_type(&context, construction),
        derived.shells().instance_type()
    );
    assert_eq!(
        context.get_type_at_location(construction).unwrap(),
        derived.shells().instance_type()
    );
    assert_eq!(
        context
            .store()
            .signature_links(construction)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(derived.default_construct_signature()),
    );

    let warm = snapshot(&context, &parsed);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(
        context.get_nongeneric_class_members(base_owner).unwrap(),
        base
    );
    assert_eq!(
        context.get_nongeneric_class_members(derived_owner).unwrap(),
        derived
    );
    assert_eq!(
        context.get_type_at_location(construction).unwrap(),
        derived.shells().instance_type()
    );
    assert_eq!(snapshot(&context, &parsed), warm);
}

#[test]
#[allow(clippy::too_many_lines)] // Each diagnostic retains its source node and published class.
fn exported_abstract_classes_keep_initialization_construction_and_access_errors() {
    let parsed = parse_source_file(concat!(
        "export abstract class Blocked {\n",
        "  abstract value: number;\n",
        "  abstract read(): number;\n",
        "  missing: number;\n",
        "  protected seed(): number { return 1; }\n",
        "}\n",
        "const bad = new Blocked();\n",
        "declare const instance: Blocked;\n",
        "const denied = instance.seed;\n",
    ));
    let mut context = context(&parsed);
    let declaration = class_declaration(&parsed, "Blocked");
    let owner = bound_symbol(&context, declaration);
    let local = context
        .file(FILE)
        .unwrap()
        .1
        .local_symbol(declaration)
        .unwrap();
    let missing = member(&parsed, declaration, "missing");
    let NodeData::PropertyDeclaration(missing) = &parsed.arena.get(missing.node).unwrap().data
    else {
        unreachable!()
    };
    let missing_name = reference(&parsed, missing.name);
    let construction = variable_initializer(&parsed, "bad");
    let NodeData::NewExpression(new) = &parsed.arena.get(construction.node).unwrap().data else {
        panic!("the rejected construction must remain a new expression")
    };
    let callee = reference(&parsed, new.expression);
    let denied = variable_initializer(&parsed, "denied");
    let NodeData::PropertyAccessExpression(access) = &parsed.arena.get(denied.node).unwrap().data
    else {
        panic!("the rejected access must retain its written property name")
    };
    let denied_name = reference(&parsed, access.name);

    context.check_source_file(FILE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 3);
    for (diagnostic, node, code, arguments, message) in [
        (
            &diagnostics[0],
            missing_name,
            2564,
            vec!["missing"],
            "Property 'missing' has no initializer and is not definitely assigned in the constructor.",
        ),
        (
            &diagnostics[1],
            construction,
            2511,
            vec![],
            "Cannot create an instance of an abstract class.",
        ),
        (
            &diagnostics[2],
            denied_name,
            2445,
            vec!["seed", "Blocked"],
            "Property 'seed' is protected and only accessible within class 'Blocked' and its subclasses.",
        ),
    ] {
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
    }
    let members = context.get_nongeneric_class_members(owner).unwrap();
    assert_exported_identity(&context, &parsed, "Blocked", &members, true);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let error_type = bootstrap.error_type;
    let unknown_signature = bootstrap.unknown_signature;
    assert_eq!(checked_type(&context, construction), error_type);
    assert_eq!(
        context.get_type_at_location(construction).unwrap(),
        error_type
    );
    assert_eq!(
        context
            .store()
            .signature_links(construction)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(unknown_signature),
    );
    assert_eq!(
        checked_type(&context, callee),
        members.shells().value_type()
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(callee)
            .unwrap()
            .resolved_symbol,
        Some(local)
    );
    let seed = bound_symbol(&context, member(&parsed, declaration, "seed"));
    assert_eq!(
        context
            .store()
            .symbol_node_links(denied)
            .unwrap()
            .resolved_symbol,
        Some(seed)
    );
    assert!(is_type_checked(&context));

    let warm = snapshot(&context, &parsed);
    context.check_source_file(FILE).unwrap();
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(
        context.get_nongeneric_class_members(owner).unwrap(),
        members
    );
    assert_eq!(
        context.get_type_at_location(construction).unwrap(),
        error_type
    );
    assert_eq!(snapshot(&context, &parsed), warm);
}
