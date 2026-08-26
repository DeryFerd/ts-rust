use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    TypeData, TypeId, UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: &str = concat!(
    "interface Date { toISOString(): string; } ",
    "interface DateConstructor { new(): Date; readonly prototype: Date; } ",
    "declare var Date: DateConstructor; ",
    "interface LocalStamp { global: string; }",
);

fn context<'a>(library: &'a ParseResult, source: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path, declaration, module_state) in [
        (
            library,
            FileId::new(4_300),
            "\"/lib/es5.d.ts\"",
            true,
            CanonicalModuleState::Script,
        ),
        (
            source,
            FileId::new(4_301),
            "\"/project/parameters.ts\"",
            false,
            CanonicalModuleState::External,
        ),
    ] {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    declaration,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![
            (FileId::new(4_300), &library.arena),
            (FileId::new(4_301), &source.arena),
        ],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: true,
            },
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn named_symbol(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name_node = match &record.data {
                NodeData::ClassDeclaration(class) => class.name?,
                NodeData::InterfaceDeclaration(interface) => interface.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(
                parsed.arena.id(),
                FileId::new(4_301),
                node,
            ))
        })
        .unwrap();
    context
        .store()
        .get_merged_symbol(
            context
                .file(declaration.file)
                .unwrap()
                .1
                .symbol(declaration)
                .unwrap(),
        )
        .unwrap()
}

fn contains_type(context: &CanonicalCheckerContext<'_>, type_: TypeId, expected: TypeId) -> bool {
    type_ == expected
        || matches!(context.store().type_payload(type_).unwrap().data(), TypeData::Union(union) if union.union.types.contains(&expected))
}

fn check_source(context: &mut CanonicalCheckerContext<'_>, source: &ParseResult) {
    context
        .check_source_file(FileId::new(4_301))
        .unwrap_or_else(|error| {
            if let SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(node)) = error
                && node.is_for(source.arena.id(), FileId::new(4_301))
            {
                let record = source.arena.get(node.node).unwrap();
                let text = source.arena.source_text().unwrap();
                let text = &text[usize::try_from(record.range.start.get()).unwrap()
                    ..usize::try_from(record.range.end.get()).unwrap()];
                let owner = context.file(node.file).unwrap().1.symbol(node).unwrap();
                let direct = context.get_nongeneric_class_members(owner);
                panic!(
                    "{error:?} at {:?}: {text}. Direct query: {direct:?}",
                    record.kind
                );
            }
            panic!("{error:?}");
        });
}

#[test]
#[allow(clippy::too_many_lines)] // The upstream cases share one declared Date identity.
fn constructor_reference_annotations_keep_default_and_optional_types_distinct() {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file(concat!(
        "export class WithDefault { constructor(readonly timestamp = new Date()) {} } ",
        "export class WithoutDefault { constructor(readonly timestamp?: Date) {} } ",
        "export class ExplicitUndefined { constructor(readonly timestamp: Date | undefined = new Date()) {} } ",
        "export class PrivateWithDefault { constructor(private timestamp = new Date()) {} } ",
        "export class PublicWithDefault { constructor(public timestamp = new Date()) {} }",
    ));
    assert!(source.diagnostics.is_empty());
    let mut context = context(&library, &source);
    check_source(&mut context, &source);
    let date = {
        let store = context.store();
        let owner = store
            .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
            .and_then(|globals| globals.get_source("Date"))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .unwrap();
        store
            .declared_type_links(owner)
            .unwrap()
            .declared_type
            .unwrap()
    };
    let undefined = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .undefined_type;
    for (name, optional) in [
        ("WithDefault", false),
        ("WithoutDefault", true),
        ("ExplicitUndefined", true),
        ("PrivateWithDefault", false),
        ("PublicWithDefault", false),
    ] {
        let owner = named_symbol(&context, &source, name);
        let members = context.get_nongeneric_class_members(owner).unwrap();
        let [property] = members.declared_instance_properties() else {
            panic!("{name} must retain its parameter property");
        };
        let signature = context
            .store()
            .signature(members.default_construct_signature())
            .unwrap();
        let [local] = signature.parameters() else {
            panic!("{name} must retain its constructor parameter");
        };
        assert_eq!(signature.min_argument_count(), 0);
        let type_ = context
            .store()
            .value_symbol_links(*property)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            context
                .store()
                .value_symbol_links(*local)
                .unwrap()
                .resolved_type,
            Some(type_)
        );
        assert!(contains_type(&context, type_, date));
        assert_eq!(
            contains_type(&context, type_, undefined),
            optional,
            "{name}"
        );
        let declaration = context
            .store()
            .symbol(*local)
            .unwrap()
            .value_declaration()
            .unwrap();
        let NodeData::ParameterDeclaration(parameter) =
            &source.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        if let Some(initializer) = parameter.initializer {
            let initializer = NodeRef::new(source.arena.id(), declaration.file, initializer);
            assert_eq!(
                context
                    .store()
                    .type_node_links(initializer)
                    .unwrap()
                    .resolved_type,
                Some(date)
            );
        }
    }
    assert!(context.diagnostics().is_empty());
    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
    );
    context.recheck_source_file(FileId::new(4_301)).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len()
        ),
        warm
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Local names, aliases, and union order share the same source scope.
fn local_constructor_references_and_unions_use_canonical_names_and_order() {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file(concat!(
        "export const marker = 0; ",
        "interface LocalStamp { local: number; } ",
        "interface Zed { z: number; } interface Alpha { a: string; } ",
        "type MaybeStamp = LocalStamp | undefined; ",
        "class Named { constructor(readonly stamp?: LocalStamp) {} } ",
        "class Aliased { constructor(readonly stamp?: MaybeStamp) {} } ",
        "class Ordered { constructor(readonly stamp?: Zed | Alpha) {} } ",
        "new Named(); new Aliased(); new Ordered();",
    ));
    assert!(source.diagnostics.is_empty());
    let mut context = context(&library, &source);
    check_source(&mut context, &source);
    let local = named_symbol(&context, &source, "LocalStamp");
    let local_type = context
        .store()
        .declared_type_links(local)
        .unwrap()
        .declared_type
        .unwrap();
    let global = context
        .store()
        .symbol_table(context.store().intrinsic_bootstrap().unwrap().globals)
        .and_then(|globals| globals.get_source("LocalStamp"))
        .and_then(|symbol| context.store().get_merged_symbol(symbol))
        .unwrap();
    assert_ne!(local, global);
    for name in ["Named", "Aliased"] {
        let owner = named_symbol(&context, &source, name);
        let members = context.get_nongeneric_class_members(owner).unwrap();
        let property = members.declared_instance_properties()[0];
        let type_ = context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .resolved_type
            .unwrap();
        assert!(contains_type(&context, type_, local_type));
        assert!(contains_type(
            &context,
            type_,
            context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .undefined_type
        ));
    }
    let ordered = named_symbol(&context, &source, "Ordered");
    let members = context.get_nongeneric_class_members(ordered).unwrap();
    let property = members.declared_instance_properties()[0];
    let type_ = context
        .store()
        .value_symbol_links(property)
        .unwrap()
        .resolved_type
        .unwrap();
    let TypeData::Union(union) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the optional reference union must remain a union");
    };
    let names = union
        .union
        .types
        .iter()
        .filter_map(|type_| {
            let symbol = context.store().type_payload(*type_)?.symbol()?;
            context.store().symbol(symbol)?.name().as_utf8()
        })
        .collect::<Vec<_>>();
    assert_eq!(names, ["Alpha", "Zed"]);
    assert!(context.diagnostics().is_empty());
    let warm = (context.store().type_len(), context.store().signature_len());
    context.recheck_source_file(FileId::new(4_301)).unwrap();
    assert_eq!(
        (context.store().type_len(), context.store().signature_len()),
        warm
    );
}

#[test]
fn invalid_constructor_annotation_initializers_fail_before_publication() {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file(concat!(
        "interface Other { other: number; } ",
        "export class Invalid { constructor(readonly value: Other | undefined = new Date()) {} }",
    ));
    let mut context = context(&library, &source);
    let cold = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
    );
    assert!(matches!(
        context.check_source_file(FileId::new(4_301)),
        Err(SourceCheckError::Unsupported(_))
    ));
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len()
        ),
        cold
    );
    assert!(context.diagnostics().is_empty());
}

#[allow(clippy::too_many_lines)] // One case checks cold queries, relations, display, and warm state.
fn check_direct_constructor_annotation(prefix: &str, parameter: &str, display: &str) {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file(&format!(
        "{prefix} class First {{ constructor({parameter}) {{}} }} class Second {{ constructor({parameter}) {{}} }}",
    ));
    assert!(source.diagnostics.is_empty());
    let mut context = context(&library, &source);
    let first = named_symbol(&context, &source, "First");
    let second = named_symbol(&context, &source, "Second");
    let first_members = context
        .get_nongeneric_class_members(first)
        .unwrap_or_else(|error| panic!("{parameter}: {error:?}"));
    let second_members = context
        .get_nongeneric_class_members(second)
        .unwrap_or_else(|error| panic!("{parameter}: {error:?}"));
    let first_type = first_members.shells().instance_type();
    let second_type = second_members.shells().instance_type();
    assert_eq!(
        context.is_type_assignable_to(first_type, second_type),
        Ok(true),
        "{parameter}"
    );
    assert_eq!(
        context.is_type_assignable_to(second_type, first_type),
        Ok(true),
        "{parameter}"
    );
    assert_eq!(context.type_to_string(first_type).unwrap(), "First");
    assert_eq!(context.type_to_string(second_type).unwrap(), "Second");
    for members in [&first_members, &second_members] {
        let signature = context
            .store()
            .signature(members.default_construct_signature())
            .unwrap();
        let [local] = signature.parameters() else {
            panic!("{parameter} must retain its constructor parameter");
        };
        let parameter_type = context
            .store()
            .value_symbol_links(*local)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            context
                .type_to_string(parameter_type)
                .unwrap_or_else(|error| {
                    let record = context.store().type_payload(parameter_type).unwrap();
                    let alias = record
                        .alias()
                        .and_then(|alias| context.store().type_alias(alias));
                    panic!("{parameter}: {error:?}. Type: {record:?}. Alias: {alias:?}");
                }),
            display,
            "{parameter}"
        );
    }
    for (node, record) in source.arena.iter() {
        let uncached = record.kind == ts_ast::SyntaxKind::ParenthesizedType
            || matches!(&record.data, NodeData::LiteralTypeNode(literal)
                if source.arena.get(literal.literal).unwrap().kind == ts_ast::SyntaxKind::NullKeyword);
        if uncached {
            assert!(
                context
                    .store()
                    .type_node_links(NodeRef::new(source.arena.id(), FileId::new(4_301), node))
                    .is_none_or(|links| links.resolved_type.is_none()),
                "{parameter} must keep {:?} uncached",
                record.kind,
            );
        }
    }
    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
    );
    assert_eq!(
        context.get_nongeneric_class_members(first).unwrap(),
        first_members
    );
    assert_eq!(
        context.get_nongeneric_class_members(second).unwrap(),
        second_members
    );
    assert_eq!(
        context.is_type_assignable_to(first_type, second_type),
        Ok(true)
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len()
        ),
        warm,
    );
    assert!(context.diagnostics().is_empty());
}

#[test]
fn constructor_parentheses_and_null_preserve_direct_queries_relations_and_display() {
    for (parameter, display) in [
        ("value: (number)", "number"),
        ("value: (null)", "null"),
        ("readonly value?: (LocalStamp)", "LocalStamp | undefined"),
        ("readonly value: LocalStamp | null", "LocalStamp | null"),
    ] {
        check_direct_constructor_annotation("", parameter, display);
    }
}

#[test]
fn constructor_aliases_and_qualified_names_preserve_direct_queries_relations_and_display() {
    for (prefix, parameter, display) in [
        (
            "type Stamp = LocalStamp;",
            "readonly value?: Stamp",
            "LocalStamp | undefined",
        ),
        (
            "type MaybeStamp = LocalStamp | undefined;",
            "readonly value: MaybeStamp",
            "MaybeStamp",
        ),
        (
            "type MaybeStamp = LocalStamp | undefined;",
            "readonly value?: MaybeStamp",
            "MaybeStamp",
        ),
        (
            "declare namespace Namespace { interface Token { value: number; } }",
            "readonly value?: Namespace.Token",
            "Token | undefined",
        ),
    ] {
        check_direct_constructor_annotation(prefix, parameter, display);
    }
}

#[test]
fn constructor_namespace_annotations_preserve_source_checks_and_display() {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file(concat!(
        "declare namespace Namespace { interface Token { value: number; } } ",
        "class Model { constructor(readonly token?: Namespace.Token) {} } ",
        "new Model();",
    ));
    assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
    let mut context = context(&library, &source);
    check_source(&mut context, &source);
    let owner = named_symbol(&context, &source, "Model");
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let property = members.declared_instance_properties()[0];
    let type_ = context
        .store()
        .value_symbol_links(property)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(context.type_to_string(type_).unwrap(), "Token | undefined");
    let before = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
    );

    context.recheck_source_file(FileId::new(4_301)).unwrap();

    assert_eq!(context.type_to_string(type_).unwrap(), "Token | undefined");
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
        ),
        before
    );
    assert!(context.diagnostics().is_empty());
}

#[test]
fn constructor_date_annotations_preserve_direct_queries_relations_and_display() {
    for (parameter, display) in [
        ("readonly value?: Date", "Date | undefined"),
        ("readonly value: Date | null", "Date | null"),
        ("readonly value: (Date | null) = new Date()", "Date | null"),
    ] {
        check_direct_constructor_annotation("", parameter, display);
    }
    check_direct_constructor_annotation(
        "type Stamp = Date;",
        "readonly value: Stamp = new Date()",
        "Date",
    );
}
