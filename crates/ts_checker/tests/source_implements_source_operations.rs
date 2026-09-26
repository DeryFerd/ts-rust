use ts_ast::{FileId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    SignatureId, TypeId,
    bootstrap::IntrinsicBootstrapOptions,
    production::{CanonicalCheckerContext, CanonicalCheckerOptions},
    type_records::{StructuredTypeData, TypeData},
};
use ts_ast::NodeData;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(0);
const SOURCE_FILE: FileId = FileId::new(1);

const LIBRARY: &str = "interface IArguments {} interface Object {} interface Function {} interface String {} interface Number {} interface Boolean {} interface RegExp {} interface Array<T> { length: number; [index: number]: T; } interface ReadonlyArray<T> { readonly length: number; readonly [index: number]: T; } interface ThisType<T> {}\n";

const DIRECT_POSITIVE: &str = "export type Shape<T> = { value: T; read: () => T };\nexport class Reader implements Shape<number> {\n  value: number = 1;\n  read(): number { return 1; }\n}\n";

const DIRECT_NEGATIVE: &str = "export type Shape<T> = { value: T; read: () => T };\nexport class Reader implements Shape<number> {\n  value: number = 1;\n  read(): string { return \"bad\"; }\n}\n";

const MAPPED_POSITIVE: &str = "export type Shape<T> = { value: T; read: () => T };\nexport type Copy<T> = { [K in keyof T]: T[K] };\nexport class Reader implements Copy<Shape<number>> {\n  value: number = 1;\n  read(): number { return 1; }\n}\n";

const MAPPED_NEGATIVE: &str = "export type Shape<T> = { value: T; read: () => T };\nexport type Copy<T> = { [K in keyof T]: T[K] };\nexport class Reader implements Copy<Shape<number>> {\n  value: number = 1;\n  read(): string { return \"bad\"; }\n}\n";

const CONDITIONAL_POSITIVE: &str = "export type Shape<T> = { value: T; read: () => T };\nexport type Choose<C> = C extends true ? Shape<number> : never;\nexport class Reader implements Choose<true> {\n  value: number = 1;\n  read(): number { return 1; }\n}\n";

const CONDITIONAL_NEGATIVE: &str = "export type Shape<T> = { value: T; read: () => T };\nexport type Choose<C> = C extends true ? Shape<number> : never;\nexport class Reader implements Choose<true> {\n  value: number = 1;\n  read(): string { return \"bad\"; }\n}\n";

// These exact inputs and options have pinned Go results in implements-go-controls-1.
fn make_checker<'arena>(
    library: &'arena ParseResult,
    consumer: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    assert!(library.diagnostics.is_empty());
    assert!(consumer.diagnostics.is_empty());
    let mut binder = CanonicalBinder::new();
    for (file, parsed, declaration, module_state, name) in [
        (LIBRARY_FILE, library, true, CanonicalModuleState::Script, "lib.d.ts"),
        (SOURCE_FILE, consumer, false, CanonicalModuleState::External, "consumer.ts"),
    ] {
        binder.bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source(name),
                CanonicalSourceLanguage::TypeScript,
                declaration,
                module_state,
            ),
        ).expect("source binding");
    }
    for (file, parsed) in [(LIBRARY_FILE, library), (SOURCE_FILE, consumer)] {
        binder.bind_typescript_declaration_slice(&parsed.arena, file)
            .expect("declaration binding");
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY_FILE, &library.arena), (SOURCE_FILE, &consumer.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            strict_bind_call_apply: false,
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
    ).expect("checker context")
}

fn is_checked(checker: &CanonicalCheckerContext<'_>) -> bool {
    let source = checker.source_file(SOURCE_FILE).expect("retained source");
    checker.store().source_file_links(source).is_some_and(|links| links.type_checked)
}

fn bound_symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let symbol = checker.file(SOURCE_FILE).expect("source binding").1
        .symbol(node).expect("declaration symbol");
    checker.store().get_merged_symbol(symbol).expect("canonical symbol")
}

fn structure<'a>(
    checker: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a StructuredTypeData {
    match checker.store().type_payload(type_).expect("type record").data() {
        TypeData::Object(object) => &object.structured,
        TypeData::Mapped(mapped) => &mapped.object.structured,
        TypeData::TypeReference(reference) => &reference.object.structured,
        TypeData::Interface(interface) => &interface.reference.object.structured,
        other => panic!("expected object, got {:?}", other.kind()),
    }
}

fn target_property(
    checker: &CanonicalCheckerContext<'_>,
    target: TypeId,
    name: &str,
) -> (SemanticSymbolId, TypeId) {
    let members = structure(checker, target).members.expect("completed target members");
    let symbol = checker.store().symbol_table(members).expect("target member table")
        .get_source(name).expect("target property");
    let type_ = checker.store().value_symbol_links(symbol)
        .and_then(|links| links.resolved_type).expect("source-produced property value");
    (symbol, type_)
}

fn callable_return(
    checker: &mut CanonicalCheckerContext<'_>,
    callable: TypeId,
) -> (SignatureId, TypeId) {
    let data = structure(checker, callable);
    assert_eq!(data.call_signature_count, 1);
    let signatures = data.signatures.as_ref().expect("callable signatures");
    assert_eq!(signatures.len(), 1);
    let signature = signatures[0];
    let return_type = checker.get_return_type_of_signature(signature).expect("callable return");
    (signature, return_type)
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    instance: TypeId,
    static_type: TypeId,
    target: TypeId,
    symbols: [SemanticSymbolId; 4],
    values: [TypeId; 4],
    signatures: [SignatureId; 2],
    returns: [TypeId; 2],
}

fn observe(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    reader: NodeRef,
    heritage: NodeRef,
    field: NodeRef,
    method: NodeRef,
    negative: bool,
) -> Snapshot {
    let reader_symbol = bound_symbol(checker, reader);
    let instance = checker.get_declared_type_of_symbol(reader_symbol).expect("class instance");
    let target = checker.get_type_from_type_node(heritage).expect("implements target");
    let members = checker.get_nongeneric_class_members(reader_symbol).expect("completed class");
    assert!(members.base().is_none());
    assert_eq!(members.shells().instance_type(), instance);
    let static_type = members.shells().value_type();
    assert_ne!(instance, static_type);
    let mut values = Vec::new();
    let mut symbols = Vec::new();
    for declaration in [field, method] {
        let name = match &parsed.arena.get(declaration.node).expect("member").data {
            NodeData::PropertyDeclaration(data) => data.name,
            NodeData::MethodDeclaration(data) => data.name,
            _ => panic!("expected class member"),
        };
        let name = NodeRef::new(parsed.arena.id(), SOURCE_FILE, name);
        let value = checker.get_type_at_location(declaration).expect("member type");
        assert_eq!(checker.get_type_at_location(name).expect("name type"), value);
        let symbol = bound_symbol(checker, declaration);
        assert_eq!(checker.get_symbol_at_location(declaration).expect("member symbol"), Some(symbol));
        assert_eq!(checker.get_symbol_at_location(name).expect("name symbol"), Some(symbol));
        values.push(value);
        symbols.push(symbol);
    }
    let (target_field_symbol, target_field) = target_property(checker, target, "value");
    let (target_method_symbol, target_method) = target_property(checker, target, "read");
    let (source_signature, source_return) = callable_return(checker, values[1]);
    let (target_signature, target_return) = callable_return(checker, target_method);
    let bootstrap = checker.store().intrinsic_bootstrap().expect("bootstrap");
    assert_eq!(values[0], bootstrap.number_type);
    assert_eq!(target_field, bootstrap.number_type);
    assert_eq!(target_return, bootstrap.number_type);
    assert_eq!(source_return, if negative { bootstrap.string_type } else { bootstrap.number_type });
    Snapshot {
        instance,
        static_type,
        target,
        symbols: [symbols[0], symbols[1], target_field_symbol, target_method_symbol],
        values: [values[0], values[1], target_field, target_method],
        signatures: [source_signature, target_signature],
        returns: [source_return, target_return],
    }
}

fn check_case(source: &str, target_name: &str, negative: bool) {
    for source_first in [true, false] {
        let library = parse_source_file(LIBRARY);
        let parsed = parse_source_file(source);
        let mut checker = make_checker(&library, &parsed);
        let (reader_id, class) = parsed.arena.iter().find_map(|(id, node)| {
            if let NodeData::ClassDeclaration(class) = &node.data {
                Some((id, class))
            } else {
                None
            }
        }).expect("Reader class");
        let node_ref = |node| NodeRef::new(parsed.arena.id(), SOURCE_FILE, node);
        let reader = node_ref(reader_id);
        let clause = class.heritage_clauses.as_ref().expect("implements clause").nodes[0];
        let NodeData::HeritageClause(clause) = &parsed.arena.get(clause).expect("clause").data else {
            panic!("expected heritage clause");
        };
        let heritage = node_ref(clause.types.nodes[0]);
        let field = node_ref(class.members.nodes[0]);
        let method = node_ref(class.members.nodes[1]);
        let NodeData::MethodDeclaration(method_data) = &parsed.arena.get(method.node).expect("read method").data else {
            panic!("expected read method");
        };
        let diagnostic_node = node_ref(method_data.name);
        assert!(!is_checked(&checker));
        let cold = if source_first {
            None
        } else {
            let symbol = bound_symbol(&checker, reader);
            let instance = checker.get_declared_type_of_symbol(symbol).expect("cold class instance");
            let target = checker.get_type_from_type_node(heritage).expect("cold implements target");
            assert_eq!(checker.get_declared_type_of_symbol(symbol).expect("warm class instance"), instance);
            assert_eq!(checker.get_type_from_type_node(heritage).expect("warm implements target"), target);
            assert!(!is_checked(&checker));
            Some((instance, target))
        };
        checker.check_source_file(SOURCE_FILE).unwrap_or_else(|error| {
            panic!("source_first={source_first}, negative={negative}: source check failed: {error:?}");
        });
        assert!(is_checked(&checker));
        let initial = observe(&mut checker, &parsed, reader, heritage, field, method, negative);
        if let Some((instance, target)) = cold {
            assert_eq!((initial.instance, initial.target), (instance, target));
        }
        let diagnostics = checker.diagnostics().as_slice().to_vec();
        if negative {
            assert_eq!(diagnostics.len(), 1);
            assert_eq!(diagnostics[0].node, Some(diagnostic_node));
            assert_eq!(diagnostics[0].diagnostic.code(), 2416);
            assert_eq!(
                diagnostics[0].diagnostic.render().expect("diagnostic text"),
                format!("Property 'read' in type 'Reader' is not assignable to the same property in base type '{target_name}'.\n  Type '() => string' is not assignable to type '() => number'.\n    Type 'string' is not assignable to type 'number'."),
            );
        } else {
            assert!(diagnostics.is_empty());
        }
        assert_eq!(observe(&mut checker, &parsed, reader, heritage, field, method, negative), initial);
        for _ in 0..2 {
            checker.recheck_source_file(SOURCE_FILE).expect("source recheck");
            assert!(is_checked(&checker));
            assert_eq!(observe(&mut checker, &parsed, reader, heritage, field, method, negative), initial);
            assert_eq!(checker.diagnostics().as_slice(), diagnostics.as_slice());
        }
    }
}

#[test]
fn direct_implements_positive_keeps_source_queries() {
    check_case(DIRECT_POSITIVE, "Shape<number>", false);
}

#[test]
fn direct_implements_negative_reports_go_diagnostic() {
    check_case(DIRECT_NEGATIVE, "Shape<number>", true);
}

#[test]
fn mapped_implements_positive_keeps_source_queries() {
    check_case(MAPPED_POSITIVE, "Copy<Shape<number>>", false);
}

#[test]
fn mapped_implements_negative_reports_go_diagnostic() {
    check_case(MAPPED_NEGATIVE, "Copy<Shape<number>>", true);
}

#[test]
fn conditional_implements_positive_keeps_source_queries() {
    check_case(CONDITIONAL_POSITIVE, "Shape<number>", false);
}

#[test]
fn conditional_implements_negative_reports_go_diagnostic() {
    check_case(CONDITIONAL_NEGATIVE, "Shape<number>", true);
}
