use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(4_530);

// Keep these prop-types declarations unchanged from the pinned react16.d.ts.
const SOURCE: &str = concat!(
    "interface Error { name: string; message: string; stack?: string; }\n",
    "declare module \"prop-types\" {\n",
    "  export const nominalTypeHack: unique symbol;\n",
    "  export type IsOptional<T> = undefined | null extends T ? true : ",
    "undefined extends T ? true : null extends T ? true : false;\n",
    "  export type RequiredKeys<V> = { [K in keyof V]: ",
    "V[K] extends Validator<infer T> ? IsOptional<T> extends true ? never : K : never ",
    "}[keyof V];\n",
    "  export interface Validator<T> {\n",
    "    (props: object, propName: string, componentName: string, ",
    "location: string, propFullName: string): Error | null;\n",
    "    [nominalTypeHack]?: T;\n",
    "  }\n",
    "  export type Required = RequiredKeys<{ value: Validator<string> }>;\n",
    "  export type Optional = RequiredKeys<{ value: Validator<string | undefined> }>;\n",
    "  export type Deferred<V> = RequiredKeys<V>;\n",
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
            CanonicalSourceFileFacts::new_with_default_library(
                EscapedName::source("\"/project/mapped-conditional-demand.d.ts\""),
                CanonicalSourceLanguage::TypeScript,
                true,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn alias_nodes(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (name.text == expected).then_some((
                NodeRef::new(parsed.arena.id(), FILE, node),
                NodeRef::new(parsed.arena.id(), FILE, alias.type_),
            ))
        })
        .unwrap_or_else(|| panic!("missing type alias {expected}"))
}

fn cached_lookup(context: &CanonicalCheckerContext<'_>, request: NodeRef) -> (TypeId, TypeId) {
    let store = context.store();
    let lookup = store
        .type_node_links(request)
        .and_then(|links| links.resolved_type)
        .expect("the source query must cache its whole lookup");
    let TypeData::IndexedAccess(access) = store.type_payload(lookup).unwrap().data() else {
        panic!("the source cache must retain the lookup, not its demanded value")
    };
    (lookup, access.object_type)
}

fn mapped_member(
    context: &CanonicalCheckerContext<'_>,
    mapped: TypeId,
) -> (SemanticSymbolId, TypeId) {
    let store = context.store();
    let TypeData::Mapped(mapped) = store.type_payload(mapped).unwrap().data() else {
        panic!("the lookup must retain its mapped child")
    };
    let property = mapped
        .object
        .structured
        .members
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source("value"))
        .expect("the lookup must demand the mapped value property");
    assert_eq!(
        mapped.object.structured.properties.as_deref(),
        Some([property].as_slice()),
    );
    let type_ = store
        .value_symbol_links(property)
        .and_then(|links| links.resolved_type)
        .expect("mapped property demand must cache its evaluated type");
    (property, type_)
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize, usize) {
    let store = context.store();
    (
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.conditional_root_len(),
    )
}

fn assert_concrete_query(name: &str, expected: &str) {
    let parsed = parse_source_file(SOURCE);
    let mut context = context(&parsed);
    let (_, request) = alias_nodes(&parsed, name);
    let (required_keys, _) = alias_nodes(&parsed, "RequiredKeys");
    let symbol = context.file(FILE).unwrap().1.symbol(required_keys).unwrap();
    let symbol = context.store().get_merged_symbol(symbol).unwrap();
    assert!(
        context
            .store()
            .type_node_links(request)
            .and_then(|links| links.resolved_type)
            .is_none()
    );

    let result = context.get_type_from_type_node(request).unwrap();
    assert_eq!(context.type_to_string(result).unwrap(), expected);
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let lookup = cached_lookup(&context, request);
    assert_ne!(result, lookup.0);
    let member = mapped_member(&context, lookup.1);
    assert_eq!(member.1, result);
    let alias_links = context.store().type_alias_links(symbol).unwrap().clone();
    assert!(
        alias_links
            .instantiations
            .as_ref()
            .unwrap()
            .values()
            .any(|cached| *cached == lookup.0),
        "the alias cache must retain the same whole lookup",
    );
    let request_links = context.store().type_node_links(request).unwrap().clone();
    let warm = counts(&context);

    assert_eq!(context.get_type_from_type_node(request).unwrap(), result);
    assert_eq!(context.type_to_string(result).unwrap(), expected);
    assert_eq!(cached_lookup(&context, request), lookup);
    assert_eq!(mapped_member(&context, lookup.1), member);
    assert_eq!(context.store().type_alias_links(symbol), Some(&alias_links));
    assert_eq!(
        context.store().type_node_links(request),
        Some(&request_links)
    );
    assert_eq!(counts(&context), warm);
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
}

#[test]
fn source_mapped_conditional_demand_required_member_cold_and_warm() {
    assert_concrete_query("Required", "\"value\"");
}

#[test]
fn source_mapped_conditional_demand_optional_member_cold_and_warm() {
    assert_concrete_query("Optional", "never");
}

#[test]
fn source_mapped_conditional_demand_generic_lookup_stays_deferred() {
    let parsed = parse_source_file(SOURCE);
    let mut context = context(&parsed);
    let (_, request) = alias_nodes(&parsed, "Deferred");
    let (required_keys, _) = alias_nodes(&parsed, "RequiredKeys");
    let symbol = context.file(FILE).unwrap().1.symbol(required_keys).unwrap();
    let symbol = context.store().get_merged_symbol(symbol).unwrap();

    let result = context.get_type_from_type_node(request).unwrap();
    let lookup = cached_lookup(&context, request);
    assert_eq!(result, lookup.0);
    let mapped_record = context.store().type_payload(lookup.1).unwrap();
    assert!(
        !mapped_record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
    );
    let TypeData::Mapped(mapped) = mapped_record.data() else {
        panic!("the generic lookup must keep its mapped child")
    };
    assert!(mapped.object.structured.members.is_none());
    assert!(mapped.object.structured.properties.is_none());
    let mapped = mapped.clone();
    let template = mapped.template_type.unwrap();
    let TypeData::Conditional(conditional) = context.store().type_payload(template).unwrap().data()
    else {
        panic!("the generic mapped template must stay conditional")
    };
    assert!(conditional.resolved_true_type.is_none());
    assert!(conditional.resolved_false_type.is_none());
    assert!(conditional.resolved_inferred_true_type.is_none());
    let conditional = conditional.clone();
    let alias_links = context.store().type_alias_links(symbol).unwrap().clone();
    let request_links = context.store().type_node_links(request).unwrap().clone();
    let warm = counts(&context);
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    assert_eq!(context.get_type_from_type_node(request).unwrap(), result);
    assert_eq!(cached_lookup(&context, request), lookup);
    assert_eq!(
        context.store().type_payload(lookup.1).unwrap().data(),
        &TypeData::Mapped(mapped),
    );
    assert_eq!(
        context.store().type_payload(template).unwrap().data(),
        &TypeData::Conditional(conditional),
    );
    assert_eq!(context.store().type_alias_links(symbol), Some(&alias_links));
    assert_eq!(
        context.store().type_node_links(request),
        Some(&request_links)
    );
    assert_eq!(counts(&context), warm);
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
}
