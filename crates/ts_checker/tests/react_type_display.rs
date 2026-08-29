use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    CanonicalTypeFormatFlags, IntrinsicBootstrapOptions, TypeAliasId, TypeAliasLinks, TypeData,
    TypeId, ValueSymbolLinks,
    type_records::{IntersectionTypeData, MappedTypeData, StructuredTypeData, TypeReferenceData},
    types::{ObjectFlags, TypeFlags},
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const REACT_FILE: FileId = FileId::new(4_600);
const CASE_FILE: FileId = FileId::new(4_601);

// These strings retain the authored project bytes, including spaces and no final newline.
const HERITAGE_VALID: &str = concat!(
    "declare namespace React { interface DOMAttributes<T> {} ",
    "interface HTMLAttributes<T> extends DOMAttributes<T> { id?: string; } ",
    "interface HTMLAttributes<T> extends DOMAttributes<T> { title?: string; } ",
    "interface MediaHTMLAttributes<T> extends HTMLAttributes<T> { src?: string; } ",
    "interface AudioHTMLAttributes<T> extends MediaHTMLAttributes<T> {} ",
    "interface Attributes { key?: string; } ",
    "interface ClassAttributes<T> extends Attributes { ref?: T; } ",
    "type DetailedHTMLProps<E extends HTMLAttributes<T>, T> = ClassAttributes<T> & E; }",
);
const HERITAGE_INVALID: &str = concat!(
    "declare namespace React { interface DOMAttributes<T> {} ",
    "interface HTMLAttributes<T> extends DOMAttributes<T> { id?: string; } ",
    "interface HTMLAttributes<T> extends DOMAttributes<T> { title?: string; } ",
    "interface MediaHTMLAttributes<T> extends HTMLAttributes<T> { src?: string; } ",
    "interface AudioHTMLAttributes<T> extends MediaHTMLAttributes<T> { id?: number; } ",
    "interface Attributes { key?: string; } ",
    "interface ClassAttributes<T> extends Attributes { ref?: T; } ",
    "type DetailedHTMLProps<E extends HTMLAttributes<T>, T> = ClassAttributes<T> & E; }",
);
const HERITAGE_CASE: &str =
    "type Probe = React.DetailedHTMLProps<React.AudioHTMLAttributes<number>, number>;";
const KEYOF_VALID: &str = concat!(
    "type Subset<Model, Keys extends keyof Model> = { [K in Keys]: Model[K] }; ",
    "interface Item { value: string; other: number; } ",
    "type Result = Subset<Item, 'value'>;",
);
const KEYOF_INVALID: &str = concat!(
    "type Subset<Model, Keys extends keyof Model> = { [K in Keys]: Model[K] }; ",
    "interface Item { value: string; other: number; } ",
    "type Result = Subset<Item, 'missing'>;",
);

fn context<'a>(files: &[(FileId, &'a ParseResult, &str, bool)]) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, declaration_file) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"{path}\"")),
                    CanonicalSourceLanguage::TypeScript,
                    declaration_file,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    // Project tests own lib loading and skipLibCheck. Declaration queries here stay lazy.
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, _, _)| (*file, &parsed.arena))
            .collect(),
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
            no_emit: true,
            check_bigint_target: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AliasQuery {
    declaration: NodeRef,
    name: NodeRef,
    body: NodeRef,
    symbol: SemanticSymbolId,
    type_: TypeId,
    parameters: Vec<TypeId>,
}

fn bound_symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let symbol = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(symbol).unwrap()
}

fn query_alias(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    expected: &str,
) -> AliasQuery {
    let (id, alias) = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (name.text == expected).then_some((id, alias))
        })
        .unwrap_or_else(|| panic!("missing alias {expected}"));
    let declaration = NodeRef::new(parsed.arena.id(), file, id);
    let name = NodeRef::new(parsed.arena.id(), file, alias.name);
    let body = NodeRef::new(parsed.arena.id(), file, alias.type_);
    let symbol = bound_symbol(context, declaration);
    assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
    assert_eq!(
        context.get_symbol_declarations(symbol).unwrap(),
        &[declaration]
    );
    let type_ = context.get_type_at_location(name).unwrap();
    assert_eq!(context.get_type_from_type_node(body).unwrap(), type_);
    let store = context.store();
    let links = store.type_alias_links(symbol).unwrap();
    assert_eq!(links.declared_type, Some(type_));
    assert_eq!(
        store.type_node_links(body).unwrap().resolved_type,
        Some(type_)
    );
    let parameters = links.type_parameters.clone().unwrap_or_default();
    let declarations = alias
        .type_parameters
        .as_ref()
        .map_or(&[][..], |list| &list.nodes);
    assert_eq!(parameters.len(), declarations.len());
    for (&parameter, &node) in parameters.iter().zip(declarations) {
        let owner = bound_symbol(context, NodeRef::new(parsed.arena.id(), file, node));
        let record = store.type_payload(parameter).unwrap();
        assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
        assert_eq!(record.symbol(), Some(owner));
        assert_eq!(
            store.declared_type_links(owner).unwrap().declared_type,
            Some(parameter)
        );
    }
    AliasQuery {
        declaration,
        name,
        body,
        symbol,
        type_,
        parameters,
    }
}

fn assert_alias_identity(context: &CanonicalCheckerContext<'_>, alias: &AliasQuery) {
    let store = context.store();
    let record = store.type_payload(alias.type_).unwrap();
    let identity = store.type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(identity.symbol(), Some(alias.symbol));
    assert_eq!(
        identity.type_arguments().unwrap_or_default(),
        alias.parameters
    );
}

fn query_type_arguments(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    reference: NodeRef,
) -> Vec<TypeId> {
    let NodeData::TypeReferenceNode(data) = &parsed.arena.get(reference.node).unwrap().data else {
        panic!("outer alias must reference the generic alias")
    };
    data.type_arguments
        .as_ref()
        .unwrap()
        .nodes
        .iter()
        .map(|&node| {
            context
                .get_type_from_type_node(NodeRef::new(reference.arena, reference.file, node))
                .unwrap()
        })
        .collect()
}

#[derive(Debug, Eq, PartialEq)]
enum AliasBody {
    Intersection(IntersectionTypeData),
    Mapped(MappedTypeData),
}

#[derive(Debug, Eq, PartialEq)]
struct AliasIdentity {
    id: TypeAliasId,
    symbol: Option<SemanticSymbolId>,
    arguments: Option<Vec<TypeId>>,
}

#[derive(Debug, Eq, PartialEq)]
struct AliasState {
    flags: TypeFlags,
    object_flags: ObjectFlags,
    symbol: Option<SemanticSymbolId>,
    identity: Option<AliasIdentity>,
    body: AliasBody,
}

fn alias_state(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> AliasState {
    let store = context.store();
    let record = store.type_payload(type_).unwrap();
    let body = match record.data() {
        TypeData::Intersection(data) => AliasBody::Intersection(data.clone()),
        TypeData::Mapped(data) => AliasBody::Mapped(data.clone()),
        other => panic!("unexpected alias body {other:?}"),
    };
    AliasState {
        flags: record.flags(),
        object_flags: record.object_flags(),
        symbol: record.symbol(),
        identity: record.alias().map(|id| {
            let identity = store.type_alias(id).unwrap();
            AliasIdentity {
                id,
                symbol: identity.symbol(),
                arguments: identity.type_arguments().map(<[TypeId]>::to_vec),
            }
        }),
        body,
    }
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 8] {
    let store = context.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.symbol_store().symbol_table_len(),
        store.mapper_len(),
        store.signature_len(),
        store.index_info_len(),
        store.properties_type_cache_len(),
    ]
}

fn source_and_reference_values(
    context: &CanonicalCheckerContext<'_>,
    files: &[(FileId, &ParseResult)],
    references: &[(TypeId, TypeReferenceData)],
) -> Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)> {
    let mut symbols = Vec::new();
    for &(file, parsed) in files {
        let bound = context.file(file).unwrap().1;
        for (id, _) in parsed.arena.iter() {
            if let Some(symbol) = bound.symbol(NodeRef::new(parsed.arena.id(), file, id)) {
                symbols.push(context.store().get_merged_symbol(symbol).unwrap());
            }
        }
    }
    for (_, reference) in references {
        symbols.extend(
            reference
                .object
                .structured
                .properties
                .iter()
                .flatten()
                .copied(),
        );
    }
    symbols.sort_unstable();
    symbols.dedup();
    symbols
        .into_iter()
        .map(|symbol| (symbol, context.store().value_symbol_links(symbol).cloned()))
        .collect()
}

fn intersection_references(
    context: &CanonicalCheckerContext<'_>,
    aliases: &[AliasQuery],
) -> Vec<(TypeId, TypeReferenceData)> {
    let mut references = Vec::new();
    for alias in aliases {
        let TypeData::Intersection(data) =
            context.store().type_payload(alias.type_).unwrap().data()
        else {
            continue;
        };
        for &type_ in &data.intersection.types {
            if let TypeData::TypeReference(reference) =
                context.store().type_payload(type_).unwrap().data()
            {
                references.push((type_, reference.clone()));
            }
        }
    }
    references
}

#[derive(Debug, Eq, PartialEq)]
struct DisplaySnapshot {
    counts: [usize; 8],
    diagnostics: CanonicalCheckerDiagnostics,
    values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
    references: Vec<(TypeId, TypeReferenceData)>,
    bodies: Vec<AliasState>,
    links: Vec<Option<TypeAliasLinks>>,
}

fn display_snapshot(
    context: &CanonicalCheckerContext<'_>,
    files: &[(FileId, &ParseResult)],
    aliases: &[AliasQuery],
) -> DisplaySnapshot {
    let references = intersection_references(context, aliases);
    DisplaySnapshot {
        counts: counts(context),
        diagnostics: context.diagnostics().clone(),
        values: source_and_reference_values(context, files, &references),
        references,
        bodies: aliases
            .iter()
            .map(|alias| alias_state(context, alias.type_))
            .collect(),
        links: aliases
            .iter()
            .map(|alias| context.store().type_alias_links(alias.symbol).cloned())
            .collect(),
    }
}

fn assert_stable_display(
    context: &mut CanonicalCheckerContext<'_>,
    files: &[(FileId, &ParseResult)],
    aliases: &[AliasQuery],
    names: &[&str],
) {
    assert_eq!(aliases.len(), names.len());
    let before = display_snapshot(context, files, aliases);
    for _ in 0..2 {
        for (alias, expected) in aliases.iter().zip(names) {
            let parsed = files
                .iter()
                .find(|(file, _)| *file == alias.name.file)
                .unwrap()
                .1;
            for node in [alias.name, alias.body] {
                let parent = parsed.arena.get(node.node).unwrap().parent.unwrap();
                let enclosing = NodeRef::new(node.arena, node.file, parent);
                assert_eq!(enclosing, alias.declaration);
                assert_eq!(
                    context
                        .type_to_string_at_location_with_flags(
                            alias.type_,
                            enclosing,
                            CanonicalTypeFormatFlags::NO_TRUNCATION
                                | CanonicalTypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE,
                        )
                        .unwrap(),
                    *expected,
                );
            }
            assert_eq!(
                context.get_type_at_location(alias.name).unwrap(),
                alias.type_
            );
            assert_eq!(
                context.get_type_from_type_node(alias.body).unwrap(),
                alias.type_
            );
            assert_eq!(
                context.get_symbol_at_location(alias.name).unwrap(),
                Some(alias.symbol)
            );
        }
        assert_eq!(display_snapshot(context, files, aliases), before);
    }
}

fn assert_diagnostics(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    expected: Option<(u32, u32, &str)>,
) {
    let diagnostics = context.diagnostics().as_slice();
    let Some((start, end, message)) = expected else {
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        return;
    };
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic.diagnostic.code(), 2344);
    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
    let node = diagnostic.node.unwrap();
    assert_eq!(node.file, CASE_FILE);
    assert_eq!(node.arena, parsed.arena.id());
    let range = diagnostic.range_override.map_or_else(
        || parsed.arena.get(node.node).unwrap().range,
        ts_checker::semantic::CanonicalCheckerDiagnosticRange::range,
    );
    assert_eq!((range.start.get(), range.end.get()), (start, end));
}

fn check_heritage_display(react: &str, expected: Option<(u32, u32, &str)>) {
    let react = parse_source_file(react);
    let case = parse_source_file(HERITAGE_CASE);
    let mut context = context(&[
        (REACT_FILE, &react, "/project/react.d.ts", true),
        (CASE_FILE, &case, "/project/case.ts", false),
    ]);
    context.check_source_file(CASE_FILE).unwrap();
    assert_diagnostics(&context, &case, expected);
    let generic = query_alias(&mut context, &react, REACT_FILE, "DetailedHTMLProps");
    let outer = query_alias(&mut context, &case, CASE_FILE, "Probe");
    assert_eq!(generic.parameters.len(), 2);
    assert!(outer.parameters.is_empty());
    assert_ne!(generic.type_, outer.type_);
    let arguments = query_type_arguments(&mut context, &case, outer.body);
    assert_eq!(arguments.len(), 2);
    for alias in [&generic, &outer] {
        assert_alias_identity(&context, alias);
        let record = context.store().type_payload(alias.type_).unwrap();
        assert_eq!(record.flags(), TypeFlags::INTERSECTION);
        assert!(
            !record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );
        let TypeData::Intersection(data) = record.data() else {
            unreachable!()
        };
        assert_eq!(data.intersection.types.len(), 2);
        assert_eq!(data.intersection.structured, StructuredTypeData::default());
        assert!(data.intersection.property_cache.is_none());
        assert!(data.intersection.resolved_properties.is_none());
        let expected = if alias.type_ == generic.type_ {
            &generic.parameters
        } else {
            &arguments
        };
        assert_eq!(data.intersection.types[1], expected[0]);
        let TypeData::TypeReference(reference) = context
            .store()
            .type_payload(data.intersection.types[0])
            .unwrap()
            .data()
        else {
            panic!("the first constituent must retain ClassAttributes")
        };
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&expected[1..])
        );
    }
    assert_stable_display(
        &mut context,
        &[(REACT_FILE, &react), (CASE_FILE, &case)],
        &[generic, outer],
        &["DetailedHTMLProps<E, T>", "Probe"],
    );
    let source = context.source_file(REACT_FILE).unwrap();
    assert!(
        !context
            .store()
            .source_file_links(source)
            .is_some_and(|links| links.type_checked)
    );
    assert_diagnostics(&context, &case, expected);
}

fn check_keyof_display(source: &str, expected: Option<(u32, u32, &str)>) {
    let parsed = parse_source_file(source);
    let mut context = context(&[(CASE_FILE, &parsed, "/project/case.ts", false)]);
    context.check_source_file(CASE_FILE).unwrap();
    assert_diagnostics(&context, &parsed, expected);
    let generic = query_alias(&mut context, &parsed, CASE_FILE, "Subset");
    let outer = query_alias(&mut context, &parsed, CASE_FILE, "Result");
    assert_eq!(generic.parameters.len(), 2);
    assert!(outer.parameters.is_empty());
    assert_ne!(generic.type_, outer.type_);
    assert_alias_identity(&context, &outer);
    let arguments = query_type_arguments(&mut context, &parsed, outer.body);
    assert_eq!(arguments.len(), 2);
    let store = context.store();
    let original_record = store.type_payload(generic.type_).unwrap();
    let TypeData::Mapped(original) = original_record.data() else {
        panic!("Subset must be mapped")
    };
    let TypeData::Mapped(clone) = store.type_payload(outer.type_).unwrap().data() else {
        panic!("Result must retain its mapped type")
    };
    assert!(original_record.alias().is_none());
    assert_eq!(
        original_record.symbol(),
        Some(bound_symbol(&context, generic.body))
    );
    assert_eq!(original.declaration, Some(generic.body));
    assert_eq!(clone.declaration, original.declaration);
    assert!(original.object.target.is_none());
    assert_eq!(clone.object.target, Some(generic.type_));
    assert_eq!(original.constraint_type, Some(generic.parameters[1]));
    assert_eq!(original.modifiers_type, Some(generic.parameters[0]));
    assert_eq!(clone.constraint_type, Some(arguments[1]));
    assert_eq!(clone.modifiers_type, Some(arguments[0]));
    assert_ne!(original.type_parameter, clone.type_parameter);
    let TypeData::TypeParameter(parameter) = store
        .type_payload(clone.type_parameter.unwrap())
        .unwrap()
        .data()
    else {
        panic!("mapped key must be a type parameter")
    };
    assert_eq!(parameter.target, original.type_parameter);
    assert_eq!(parameter.mapper, clone.object.mapper);
    assert_eq!(parameter.constraint, clone.constraint_type);
    assert!(store.mapper_payload(clone.object.mapper.unwrap()).is_some());
    let TypeData::IndexedAccess(template) = store
        .type_payload(clone.template_type.unwrap())
        .unwrap()
        .data()
    else {
        panic!("mapped template must retain indexed access")
    };
    assert_eq!(Some(template.object_type), clone.modifiers_type);
    assert_eq!(Some(template.index_type), clone.type_parameter);
    for data in [original, clone] {
        assert_eq!(data.object.structured, StructuredTypeData::default());
        assert!(data.resolved_apparent_type.is_none());
    }
    assert!(
        store
            .type_alias_links(generic.symbol)
            .unwrap()
            .instantiations
            .as_ref()
            .unwrap()
            .values()
            .any(|type_| *type_ == outer.type_)
    );
    assert_stable_display(
        &mut context,
        &[(CASE_FILE, &parsed)],
        &[generic, outer],
        &["Subset<Model, Keys>", "Result"],
    );
    assert_diagnostics(&context, &parsed, expected);
}

#[test]
fn heritage_valid_alias_queries_display_without_resolving_members() {
    check_heritage_display(HERITAGE_VALID, None);
}

#[test]
fn heritage_invalid_alias_queries_keep_the_constraint_diagnostic() {
    check_heritage_display(
        HERITAGE_INVALID,
        Some((
            37,
            70,
            "Type 'AudioHTMLAttributes<number>' does not satisfy the constraint 'HTMLAttributes<number>'.",
        )),
    );
}

#[test]
fn keyof_valid_alias_queries_display_without_resolving_members() {
    check_keyof_display(KEYOF_VALID, None);
}

#[test]
fn keyof_invalid_alias_queries_keep_the_constraint_diagnostic() {
    check_keyof_display(
        KEYOF_INVALID,
        Some((
            150,
            159,
            "Type '\"missing\"' does not satisfy the constraint 'keyof Item'.",
        )),
    );
}
