use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    TypeData, TypeId, UnsupportedSourceSyntax,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

const SOURCE_FILE: FileId = FileId::new(61_201);
const LIBRARY_FILE: FileId = FileId::new(61_200);

fn context<'a>(
    parsed: &'a ParseResult,
    language: CanonicalSourceLanguage,
    library: Option<&'a ParseResult>,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    let mut sources = Vec::new();
    if let Some(library) = library {
        binder
            .bind_source_file_with_facts(
                &library.arena,
                library.source_file,
                LIBRARY_FILE,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source("\"/project/lib.d.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    true,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&library.arena, LIBRARY_FILE)
            .unwrap();
        sources.push((LIBRARY_FILE, &library.arena));
    }
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            SOURCE_FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-bodies.ts\""),
                language,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    if language == CanonicalSourceLanguage::JavaScript {
        binder
            .bind_javascript_declaration_slice(&parsed.arena, SOURCE_FILE)
            .unwrap();
    } else {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, SOURCE_FILE)
            .unwrap();
    }
    sources.push((SOURCE_FILE, &parsed.arena));
    CanonicalCheckerContext::new(
        binder.finish(),
        sources,
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_property_initialization: true,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: if language == CanonicalSourceLanguage::JavaScript {
                    ScriptTarget::EsNext
                } else {
                    ScriptTarget::Es2015
                },
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), SOURCE_FILE, node),
            ))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|(start, _)| *start);
    nodes.into_iter().map(|(_, node)| node).collect()
}

fn class_symbol(
    parsed: &ParseResult,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = nodes(parsed, SyntaxKind::ClassDeclaration)
        .into_iter()
        .find(|node| {
            let NodeData::ClassDeclaration(class) = &parsed.arena.get(node.node).unwrap().data
            else {
                return false;
            };
            matches!(class.name.and_then(|name| parsed.arena.get(name)).map(|name| &name.data),
            Some(NodeData::Identifier(name)) if name.text == expected)
        })
        .unwrap();
    context
        .file(SOURCE_FILE)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap()
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type at {node:?}"))
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().mapper_len(),
    )
}

#[test]
#[allow(clippy::too_many_lines)] // Constructor, method, and replay checks share the base class identities.
fn constructors_and_overridden_methods_keep_base_identities() {
    let parsed = parse_source_file(concat!(
        "class Point {\n",
        "  constructor(public x: number, public y: number) {}\n",
        "  public toString() { return \"x=\" + this.x + \" y=\" + this.y; }\n",
        "}\n",
        "class ColoredPoint extends Point {\n",
        "  constructor(x: number, y: number, public color: string) { super(x, y); }\n",
        "  public toString() { return super.toString() + \" color=\" + this.color; }\n",
        "}\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut context = context(&parsed, CanonicalSourceLanguage::TypeScript, None);
    context.check_source_file(SOURCE_FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let point = class_symbol(&parsed, &context, "Point");
    let point_instance = context
        .store()
        .declared_type_links(point)
        .unwrap()
        .declared_type
        .unwrap();
    let colored = class_symbol(&parsed, &context, "ColoredPoint");
    let colored_instance = context
        .store()
        .declared_type_links(colored)
        .unwrap()
        .declared_type
        .unwrap();
    let TypeData::Interface(colored_class) = context
        .store()
        .type_payload(colored_instance)
        .unwrap()
        .data()
    else {
        panic!("ColoredPoint retains its class instance type")
    };
    let colored_this = colored_class.this_type.unwrap();
    let point_method = context
        .store()
        .symbol(point)
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| context.store().symbol_table(members))
        .and_then(|members| members.get_source("toString"))
        .unwrap();
    let methods = nodes(&parsed, SyntaxKind::MethodDeclaration);
    for method in &methods {
        let signature = context
            .store()
            .signature_links(*method)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        let return_type = context
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type()
            .unwrap();
        assert_eq!(context.type_to_string(return_type).unwrap(), "string");
    }
    for access in nodes(&parsed, SyntaxKind::PropertyAccessExpression) {
        let NodeData::PropertyAccessExpression(property) =
            &parsed.arena.get(access.node).unwrap().data
        else {
            unreachable!();
        };
        let name = parsed.arena.get(property.name).unwrap();
        let NodeData::Identifier(name) = &name.data else {
            unreachable!()
        };
        let expected = if name.text == "toString" {
            "() => string"
        } else if name.text == "color" {
            "string"
        } else {
            "number"
        };
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, access))
                .unwrap(),
            expected
        );
        if parsed.arena.get(property.expression).unwrap().kind == SyntaxKind::SuperKeyword {
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(access)
                    .unwrap()
                    .resolved_symbol,
                Some(point_method)
            );
            let receiver = NodeRef::new(parsed.arena.id(), SOURCE_FILE, property.expression);
            let receiver_type = resolved_type(&context, receiver);
            assert_ne!(receiver_type, point_instance);
            let TypeData::TypeReference(reference) =
                context.store().type_payload(receiver_type).unwrap().data()
            else {
                panic!("instance super retains a base type reference")
            };
            assert_eq!(reference.object.target, Some(point_instance));
            assert_eq!(
                reference.resolved_type_arguments.as_deref(),
                Some(&[colored_this][..]),
            );
        }
    }
    let super_call = nodes(&parsed, SyntaxKind::CallExpression)
        .into_iter()
        .find(|call| {
            matches!(&parsed.arena.get(call.node).unwrap().data, NodeData::CallExpression(data)
            if parsed.arena.get(data.expression).unwrap().kind == SyntaxKind::SuperKeyword)
        })
        .unwrap();
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, super_call))
            .unwrap(),
        "void"
    );
    let signature = context
        .store()
        .signature_links(super_call)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let construct = context.store().signature(signature).unwrap();
    assert_eq!(construct.parameters().len(), 2);
    assert_eq!(construct.resolved_return_type(), Some(point_instance));
    assert_eq!(
        construct.declaration(),
        Some(nodes(&parsed, SyntaxKind::Constructor)[0])
    );
    let warm = counts(&context);
    context.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert!(context.diagnostics().is_empty());
    assert_eq!(
        context
            .store()
            .signature_links(super_call)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(signature)
    );
}

#[test]
fn forward_method_return_demand_checks_the_real_body_once() {
    let parsed = parse_source_file(concat!(
        "class Text {\n",
        "  first() { return this.second(); }\n",
        "  second() { const prefix = \"checked\"; { prefix; } return prefix; }\n",
        "}\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut context = context(&parsed, CanonicalSourceLanguage::TypeScript, None);
    context.check_source_file(SOURCE_FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let call = nodes(&parsed, SyntaxKind::CallExpression)[0];
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, call))
            .unwrap(),
        "string"
    );
    let signature = context
        .store()
        .signature_links(call)
        .unwrap()
        .resolved_signature
        .signature();
    let second = nodes(&parsed, SyntaxKind::MethodDeclaration)[1];
    assert_eq!(
        signature,
        context
            .store()
            .signature_links(second)
            .unwrap()
            .resolved_signature
            .signature()
    );
    let warm = counts(&context);
    context.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(counts(&context), warm);
}

#[test]
fn inferred_method_cycles_do_not_publish_a_guessed_return() {
    let parsed = parse_source_file(
        "class Cycle { first() { return this.second(); } second() { return this.first(); } }",
    );
    let mut context = context(&parsed, CanonicalSourceLanguage::TypeScript, None);
    assert!(matches!(
        context.check_source_file(SOURCE_FILE),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Class(_)
        ))
    ));
    for method in nodes(&parsed, SyntaxKind::MethodDeclaration) {
        if let Some(signature) = context
            .store()
            .signature_links(method)
            .and_then(|links| links.resolved_signature.signature())
        {
            assert!(
                context
                    .store()
                    .signature(signature)
                    .unwrap()
                    .resolved_return_type()
                    .is_none()
            );
        }
    }
    assert!(context.diagnostics().is_empty());
}

#[test]
fn derived_receiver_flow_changes_only_after_the_checked_super_call() {
    let parsed = parse_source_file(concat!(
        "class Base { constructor(public value: number, public other: number) {} }\n",
        "class Derived extends Base { constructor(x: number, y: number) {\n",
        "  this.value; super(x, y); this.value;\n",
        "} }\n",
    ));
    let mut context = context(&parsed, CanonicalSourceLanguage::TypeScript, None);
    context.check_source_file(SOURCE_FILE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].diagnostic.code(), 17009);
    assert_eq!(
        diagnostics[0].node,
        Some(nodes(&parsed, SyntaxKind::ThisKeyword)[0])
    );
    for access in nodes(&parsed, SyntaxKind::PropertyAccessExpression) {
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, access))
                .unwrap(),
            "number"
        );
    }
    let diagnostics = context.diagnostics().clone();
    let warm = counts(&context);
    context.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(counts(&context), warm);
}

#[test]
fn lazy_method_checks_keep_diagnostics_in_declaration_order() {
    let parsed = parse_source_file(concat!(
        "class Text {\n",
        "  first() { this.second(); const first: number = \"bad\"; return first; }\n",
        "  second() { const second: string = 1; return second; }\n",
        "}\n",
    ));
    let mut context = context(&parsed, CanonicalSourceLanguage::TypeScript, None);
    context.check_source_file(SOURCE_FILE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.diagnostic.code() == 2322)
    );
    let positions = diagnostics
        .iter()
        .map(|diagnostic| {
            parsed
                .arena
                .get(diagnostic.node.unwrap().node)
                .unwrap()
                .range
                .start
        })
        .collect::<Vec<_>>();
    assert!(positions[0] < positions[1]);
    let diagnostics = context.diagnostics().clone();
    context.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn non_callable_class_fields_use_the_existing_call_diagnostic() {
    let parsed = parse_source_file("class Counter { count = 1; run() { this.count(); } }");
    let mut context = context(&parsed, CanonicalSourceLanguage::TypeScript, None);
    context.check_source_file(SOURCE_FILE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].diagnostic.code(), 2349);
    let call = nodes(&parsed, SyntaxKind::CallExpression)[0];
    assert_eq!(
        resolved_type(&context, call),
        context.store().intrinsic_bootstrap().unwrap().error_type
    );
    let diagnostics = context.diagnostics().clone();
    let warm = counts(&context);
    context.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn lazy_method_checks_keep_missing_property_diagnostics_in_order() {
    let parsed = parse_source_file(concat!(
        "class Model {\n",
        "  value = 1;\n",
        "  first() { this.missing; this.second(); const n: number = 'bad'; return this.valu; }\n",
        "  second() { const label: string = 1; return label; }\n",
        "}\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut context = context(&parsed, CanonicalSourceLanguage::TypeScript, None);
    context.check_source_file(SOURCE_FILE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2339, 2322, 2551, 2322],
        "{diagnostics:?}"
    );
    assert_eq!(diagnostics[0].diagnostic.arguments, ["missing", "Model"]);
    assert_eq!(
        diagnostics[2].diagnostic.arguments,
        ["valu", "Model", "value"]
    );
    let owner = class_symbol(&parsed, &context, "Model");
    let instance = context
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap();
    for receiver in nodes(&parsed, SyntaxKind::ThisKeyword) {
        assert_ne!(resolved_type(&context, receiver), instance);
    }
    let diagnostics = context.diagnostics().clone();
    let warm = counts(&context);
    context.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn inaccessible_private_callees_keep_the_existing_error_recovery() {
    let parsed = parse_source_file(concat!(
        "class Base { #secret() {} }\n",
        "class Derived extends Base { run() { this.#secret(); } }\n",
    ));
    let mut context = context(&parsed, CanonicalSourceLanguage::TypeScript, None);
    context.check_source_file(SOURCE_FILE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].diagnostic.code(), 18013);
    let call = nodes(&parsed, SyntaxKind::CallExpression)[0];
    assert_eq!(
        resolved_type(&context, call),
        context.store().intrinsic_bootstrap().unwrap().error_type
    );
    let diagnostics = context.diagnostics().clone();
    let warm = counts(&context);
    context.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn property_initialization_uses_the_real_constructor_exit() {
    for (source, expected) in [
        (
            "class Model { value: number; read() { return this.value; } }",
            vec![2564],
        ),
        (
            "class Model { value: number; constructor(x: number, y: number) { throw 1; } read() { return this.value; } }",
            vec![],
        ),
    ] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed, CanonicalSourceLanguage::TypeScript, None);
        context.check_source_file(SOURCE_FILE).unwrap();
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            expected
        );
        let diagnostics = context.diagnostics().clone();
        let warm = counts(&context);
        context.recheck_source_file(SOURCE_FILE).unwrap();
        assert_eq!(counts(&context), warm);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
fn defaults_outside_the_metadata_domain_fail_before_class_headers() {
    for source in [
        "class Model { value = 1; method(input: number = this.value) { return input; } }",
        "class Model { static value = 1; static method(input: number = this.value) { return input; } }",
        "class Model { value = 1; constructor(input: number = this.value) {} }",
    ] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed, CanonicalSourceLanguage::TypeScript, None);
        let owner = class_symbol(&parsed, &context, "Model");
        let cold = counts(&context);
        assert!(matches!(
            context.check_source_file(SOURCE_FILE),
            Err(SourceCheckError::Unsupported(_))
        ));
        assert!(context.store().declared_type_links(owner).is_none());
        assert!(context.store().value_symbol_links(owner).is_none());
        assert_eq!(counts(&context), cold);
    }
}

#[test]
fn constructor_defaults_keep_call_and_body_types_separate() {
    let parsed = parse_source_file(concat!(
        "class Base { constructor(public value: number = 1, label: string) {} }\n",
        "class Derived extends Base { constructor() { super(undefined, \"label\"); } }\n",
    ));
    let mut context = context(&parsed, CanonicalSourceLanguage::TypeScript, None);
    context.check_source_file(SOURCE_FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let parameter = nodes(&parsed, SyntaxKind::Parameter)[0];
    let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    let name = NodeRef::new(parsed.arena.id(), SOURCE_FILE, parameter.name);
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, name))
            .unwrap(),
        "number"
    );
    let warm = counts(&context);
    context.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn static_super_read_does_not_share_a_named_assignment_flow_reference() {
    let library = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {}\n",
        "interface Console { log(...data: any[]): void; }\n",
        "declare var console: Console;\n",
    ));
    let parsed = parse_javascript_source_file(concat!(
        "class C { static blah1 = 123; }\n",
        "C.blah2 = 456;\n",
        "class D extends C {\n",
        "  static { console.log(super.blah1); console.log(super.blah2); }\n",
        "}\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut context = context(&parsed, CanonicalSourceLanguage::JavaScript, Some(&library));
    context.check_source_file(SOURCE_FILE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].diagnostic.code(), 2565);
    assert_eq!(
        diagnostics[0].diagnostic.render().unwrap(),
        "Property 'blah2' is used before being assigned."
    );
    let c = class_symbol(&parsed, &context, "C");
    let c_value = context
        .store()
        .value_symbol_links(c)
        .unwrap()
        .resolved_type
        .unwrap();
    for access in nodes(&parsed, SyntaxKind::PropertyAccessExpression) {
        let NodeData::PropertyAccessExpression(property) =
            &parsed.arena.get(access.node).unwrap().data
        else {
            unreachable!()
        };
        if parsed.arena.get(property.expression).unwrap().kind != SyntaxKind::SuperKeyword {
            continue;
        }
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, access))
                .unwrap(),
            "number"
        );
        let receiver = NodeRef::new(parsed.arena.id(), SOURCE_FILE, property.expression);
        assert_eq!(resolved_type(&context, receiver), c_value);
        let name = NodeRef::new(parsed.arena.id(), SOURCE_FILE, property.name);
        if matches!(&parsed.arena.get(name.node).unwrap().data, NodeData::Identifier(name) if name.text == "blah2")
        {
            assert_eq!(diagnostics[0].node, Some(name));
        }
    }
    let assignment = nodes(&parsed, SyntaxKind::BinaryExpression)[0];
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, assignment))
            .unwrap(),
        "456"
    );
    let warm = counts(&context);
    let diagnostics = context.diagnostics().clone();
    context.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert_eq!(context.diagnostics(), &diagnostics);
}
