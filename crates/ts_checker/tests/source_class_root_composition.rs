use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions};
use ts_parser::parse_source_file;

// Check the original constructor inputs under the same default options.
fn check_constructor_admission(source: &str, expected_codes: &[u32]) {
    let parsed = parse_source_file(source);
    assert!(
        parsed.diagnostics.is_empty(),
        "{source}: {:?}",
        parsed.diagnostics
    );
    let file = FileId::new(61_480);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-second-wave.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(class.name?)?.data else {
                return None;
            };
            (name.text == "Model").then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap();
    let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
    let owner = context.store().get_merged_symbol(symbol).unwrap();

    context
        .check_source_file(file)
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        expected_codes,
        "{source}",
    );
    let instance = context
        .store()
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .expect("the checked constructor must retain its class instance");
    let value = context
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .expect("the checked constructor must retain its class value");
    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        context
            .store()
            .declared_type_links(owner)
            .unwrap()
            .declared_type,
        Some(instance),
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type,
        Some(value),
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
        "{source}",
    );
}

#[test]
fn composed_constructor_forwards_a_primitive_to_a_parameter_property_base() {
    check_constructor_admission(
        concat!(
            "class Base { constructor(public value: string) {} } ",
            "class Model extends Base { constructor(value: string) { super(value); } }",
        ),
        &[],
    );
}

#[test]
fn composed_constructor_checks_its_local_variable_body() {
    check_constructor_admission("class Model { constructor() { const value = 1; } }", &[]);
}

#[test]
fn composed_constructor_reports_missing_super_instead_of_rejecting_the_class() {
    check_constructor_admission(
        "class Base {} class Model extends Base { constructor() {} }",
        &[2377],
    );
}
