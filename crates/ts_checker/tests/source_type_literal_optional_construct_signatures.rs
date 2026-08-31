use std::collections::HashSet;

use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeError, DeclaredTypeLinks,
    IntrinsicBootstrapOptions, SignatureId, SignatureLinks, SymbolNodeLinks, TypeAliasLinks,
    TypeData, TypeId, TypeNodeLinks, TypeNodeUnavailable, ValueSymbolLinks,
    signatures::SignatureFlags, type_records::ObjectTypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(202_950);
const LIBRARY: FileId = FileId::new(202_951);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(
    parsed: &'a ParseResult,
    library: Option<&'a ParseResult>,
    strict_null_checks: bool,
) -> CanonicalCheckerContext<'a> {
    let mut files = Vec::new();
    if let Some(library) = library {
        files.push((LIBRARY, library, "\"/lib/lib.es5.d.ts\"", true));
    }
    files.push((SOURCE, parsed, "\"/project/constructors.ts\"", false));
    let mut binder = CanonicalBinder::new();
    for &(file, source, path, default_library) in &files {
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
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
    }
    for &(file, source, _, _) in &files {
        binder
            .bind_typescript_declaration_slice(&source.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .iter()
            .map(|(file, source, _, _)| (*file, &source.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn source_node(parsed: &ParseResult, node: ts_ast::NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), SOURCE, node)
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| (record.kind == kind).then_some(source_node(parsed, node)))
        .collect::<Vec<_>>();
    result.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    result
}

fn literal(parsed: &ParseResult) -> NodeRef {
    let literals = nodes(parsed, SyntaxKind::TypeLiteral);
    let [literal] = literals.as_slice() else {
        panic!("the source must contain one complete constructor type literal");
    };
    *literal
}

fn members(parsed: &ParseResult, literal: NodeRef) -> Vec<NodeRef> {
    let NodeData::TypeLiteralNode(data) = &parsed.arena.get(literal.node).unwrap().data else {
        panic!("expected the original TypeLiteral annotation");
    };
    data.members
        .nodes
        .iter()
        .map(|&node| source_node(parsed, node))
        .collect()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let bound = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(bound).unwrap()
}

fn named_symbol(context: &CanonicalCheckerContext<'_>, name: &str) -> SemanticSymbolId {
    let store = context.store();
    let globals = store.intrinsic_bootstrap().unwrap().globals;
    let bound = store
        .symbol_table(globals)
        .unwrap()
        .get_source(name)
        .unwrap();
    store.get_merged_symbol(bound).unwrap()
}

struct Parameter {
    declaration: NodeRef,
    annotation: NodeRef,
    optional: bool,
}

struct Callable {
    declaration: NodeRef,
    parameters: Vec<Parameter>,
    return_annotation: NodeRef,
    construct: bool,
}

fn callables(parsed: &ParseResult, literal: NodeRef) -> Vec<Callable> {
    members(parsed, literal)
        .into_iter()
        .filter_map(|declaration| {
            let (parameters, returned, construct) =
                match &parsed.arena.get(declaration.node).unwrap().data {
                    NodeData::ConstructSignatureDeclaration(data) => {
                        (&data.parameters, data.type_.unwrap(), true)
                    }
                    NodeData::MethodSignatureDeclaration(data) => {
                        (&data.parameters, data.type_.unwrap(), false)
                    }
                    _ => return None,
                };
            Some(Callable {
                declaration,
                parameters: parameters
                    .nodes
                    .iter()
                    .map(|&node| {
                        let NodeData::ParameterDeclaration(data) =
                            &parsed.arena.get(node).unwrap().data
                        else {
                            panic!("expected a source parameter");
                        };
                        assert!(data.initializer.is_none());
                        assert!(data.dot_dot_dot_token.is_none());
                        Parameter {
                            declaration: source_node(parsed, node),
                            annotation: source_node(parsed, data.type_.unwrap()),
                            optional: data.question_token.is_some(),
                        }
                    })
                    .collect(),
                return_annotation: source_node(parsed, returned),
                construct,
            })
        })
        .collect()
}

fn query_annotations(context: &mut CanonicalCheckerContext<'_>, rows: &[Callable]) {
    for row in rows {
        for parameter in &row.parameters {
            context
                .get_type_from_type_node(parameter.annotation)
                .unwrap();
        }
        context
            .get_type_from_type_node(row.return_annotation)
            .unwrap();
    }
}

fn assert_parameter_source(parsed: &ParseResult, row: &Callable, parameter: &Parameter) {
    let record = parsed.arena.get(parameter.declaration.node).unwrap();
    let NodeData::ParameterDeclaration(data) = &record.data else {
        unreachable!();
    };
    let name = parsed.arena.get(data.name).unwrap();
    let annotation = parsed.arena.get(parameter.annotation.node).unwrap();
    assert_eq!(record.kind, SyntaxKind::Parameter);
    assert_eq!(record.flags.0, 0);
    assert_eq!(record.parent, Some(row.declaration.node));
    assert_eq!(name.kind, SyntaxKind::Identifier);
    assert_eq!(name.parent, Some(parameter.declaration.node));
    assert_eq!(annotation.parent, Some(parameter.declaration.node));
    assert!(record.range.start <= name.range.start);
    assert!(name.range.end <= annotation.range.start);
    assert!(annotation.range.end <= record.range.end);
    if let Some(question) = data.question_token {
        let question = parsed.arena.get(question).unwrap();
        assert_eq!(question.kind, SyntaxKind::QuestionToken);
        assert_eq!(question.flags.0, 0);
        assert_eq!(question.parent, Some(parameter.declaration.node));
        assert!(name.range.end <= question.range.start);
        assert!(question.range.end <= annotation.range.start);
    }
}

fn assert_optional_type(
    context: &CanonicalCheckerContext<'_>,
    annotation: TypeId,
    parameter: TypeId,
    optional: bool,
) {
    let store = context.store();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    if !optional || !bootstrap.options.strict_null_checks {
        assert_eq!(parameter, annotation);
        return;
    }
    let annotation_record = store.type_payload(annotation).unwrap();
    let mut expected = match annotation_record.data() {
        TypeData::Union(data) => data.union.types.clone(),
        _ => vec![annotation],
    };
    expected.push(bootstrap.undefined_type);
    expected.sort_unstable();
    expected.dedup();
    let parameter_record = store.type_payload(parameter).unwrap();
    let TypeData::Union(data) = parameter_record.data() else {
        panic!("a typed optional parameter must retain its canonical undefined union");
    };
    assert!(parameter_record.alias().is_none());
    assert_eq!(data.union.types, expected);
    if matches!(annotation_record.data(), TypeData::Union(_)) && annotation_record.alias().is_some()
    {
        let origin = data
            .origin
            .expect("the wrapper must retain its named union origin");
        assert_ne!(origin, parameter);
        let origin_record = store.type_payload(origin).unwrap();
        let TypeData::Union(origin_data) = origin_record.data() else {
            panic!("the named union origin must retain the original union and undefined");
        };
        let mut expected_origin = vec![annotation, bootstrap.undefined_type];
        expected_origin.sort_unstable();
        assert_eq!(origin_data.union.types, expected_origin);
        assert!(origin_data.origin.is_none());
        assert!(origin_record.alias().is_none());
    } else {
        assert!(data.origin.is_none());
        assert_eq!(bootstrap.cached_union_type(&expected), Some(parameter));
    }
    assert!(!data.union.types.contains(&bootstrap.missing_type));
}

#[derive(Debug, Eq, PartialEq)]
struct RowState {
    declaration: NodeRef,
    signature: SignatureId,
    annotations: Vec<TypeId>,
    parameters: Vec<TypeId>,
    returned: TypeId,
}

fn assert_method_value(
    context: &CanonicalCheckerContext<'_>,
    declaration: NodeRef,
    signature: SignatureId,
) {
    let store = context.store();
    let owner = symbol(context, declaration);
    let value = store
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    let record = store.type_payload(value).unwrap();
    let TypeData::Object(object) = record.data() else {
        panic!("the static method must keep its own callable object");
    };
    assert_eq!(record.symbol(), Some(owner));
    assert_eq!(store.symbol(owner).unwrap().flags(), SymbolFlags::METHOD);
    assert_eq!(
        store.symbol(owner).unwrap().declarations(),
        Some(&[declaration][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert!(object.structured.members.is_none());
    assert!(object.structured.properties.is_none());
    assert!(object.structured.index_infos.is_none());
}

fn read_row(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    row: &Callable,
) -> RowState {
    let signature = context
        .store()
        .signature_links(row.declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let returned = context
        .get_type_from_type_node(row.return_annotation)
        .unwrap();
    assert_eq!(
        context.get_return_type_of_signature(signature),
        Ok(returned)
    );
    let mut annotations = Vec::new();
    let mut parameters = Vec::new();
    let mut parameter_symbols = Vec::new();
    for parameter in &row.parameters {
        assert_parameter_source(parsed, row, parameter);
        let owner = symbol(context, parameter.declaration);
        let annotation = context
            .get_type_from_type_node(parameter.annotation)
            .unwrap();
        let value = context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_optional_type(context, annotation, value, parameter.optional);
        let record = context.store().symbol(owner).unwrap();
        assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
        assert_eq!(record.declarations(), Some(&[parameter.declaration][..]));
        assert_eq!(record.value_declaration(), Some(parameter.declaration));
        assert_eq!(record.parent(), None);
        let NodeData::ParameterDeclaration(data) =
            &parsed.arena.get(parameter.declaration.node).unwrap().data
        else {
            unreachable!();
        };
        let NodeData::Identifier(name) = &parsed.arena.get(data.name).unwrap().data else {
            unreachable!();
        };
        assert_eq!(record.name().as_utf8(), Some(name.text.as_str()));
        annotations.push(annotation);
        parameters.push(value);
        parameter_symbols.push(owner);
    }
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(row.declaration));
    assert_eq!(record.parameters(), parameter_symbols);
    assert_eq!(record.resolved_return_type(), Some(returned));
    assert_eq!(
        record.flags(),
        if row.construct {
            SignatureFlags::CONSTRUCT
        } else {
            SignatureFlags::NONE
        }
    );
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(
            row.parameters
                .iter()
                .take_while(|row| !row.optional)
                .count()
        )
        .unwrap()
    );
    assert_eq!(record.resolved_min_argument_count(), -1);
    assert!(record.type_parameters().is_empty());
    assert!(record.this_parameter().is_none());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    assert!(record.composite().is_none());
    assert!(record.isolated_signature_type().is_none());
    assert!(record.resolved_type_predicate().is_none());
    if !row.construct {
        assert_method_value(context, row.declaration, signature);
    }
    RowState {
        declaration: row.declaration,
        signature,
        annotations,
        parameters,
        returned,
    }
}

fn assert_literal_owner(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    literal: NodeRef,
    resolved: TypeId,
    rows: &[RowState],
) {
    let store = context.store();
    let owner = symbol(context, literal);
    let record = store.symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::TYPE_LITERAL);
    assert_eq!(record.declarations(), Some(&[literal][..]));
    assert_eq!(record.value_declaration(), None);
    assert_eq!(store.type_payload(resolved).unwrap().symbol(), Some(owner));
    let TypeData::Object(object) = store.type_payload(resolved).unwrap().data() else {
        panic!("the constructor annotation must retain its anonymous object");
    };
    let members = members(parsed, literal);
    let constructs = members
        .iter()
        .filter(|node| parsed.arena.get(node.node).unwrap().kind == SyntaxKind::ConstructSignature)
        .copied()
        .collect::<Vec<_>>();
    let properties = members
        .iter()
        .filter(|node| !constructs.contains(node))
        .map(|&node| symbol(context, node))
        .collect::<Vec<_>>();
    let signatures = constructs
        .iter()
        .map(|declaration| {
            rows.iter()
                .find(|row| row.declaration == *declaration)
                .unwrap()
                .signature
        })
        .collect::<Vec<_>>();
    assert_eq!(object.structured.members, record.members());
    assert_eq!(
        object.structured.properties.as_deref(),
        Some(properties.as_slice())
    );
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(signatures.as_slice())
    );
    assert_eq!(object.structured.call_signature_count, 0);
    assert!(object.structured.index_infos.is_none());
    let table = store.symbol_table(record.members().unwrap()).unwrap();
    let constructor_owner = symbol(context, constructs[0]);
    assert_eq!(table.len(), properties.len() + 1);
    assert_eq!(
        table.get(InternalSymbolName::New.as_ref()),
        Some(constructor_owner)
    );
    assert_eq!(table.get(InternalSymbolName::Call.as_ref()), None);
    assert_eq!(store.get_parent_of_symbol(constructor_owner), Some(owner));
    assert_eq!(
        store.symbol(constructor_owner).unwrap().declarations(),
        Some(constructs.as_slice())
    );
    for declaration in constructs {
        assert_eq!(symbol(context, declaration), constructor_owner);
    }
    for property in properties {
        let record = store.symbol(property).unwrap();
        assert_eq!(table.get(record.name()), Some(property));
        assert_eq!(store.get_parent_of_symbol(property), Some(owner));
    }
    let prototype = table.get_source("prototype").unwrap();
    assert_eq!(
        store.symbol(prototype).unwrap().flags(),
        SymbolFlags::PROPERTY
    );
    assert_eq!(
        store.symbol(prototype).unwrap().check_flags(),
        CheckFlags::NONE
    );
    assert_eq!(
        store.value_symbol_links(prototype).unwrap().resolved_type,
        Some(rows[0].returned)
    );
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    annotation: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct SymbolState {
    symbol: SemanticSymbolId,
    value: Option<ValueSymbolLinks>,
    declared: Option<DeclaredTypeLinks>,
    alias: Option<TypeAliasLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 6],
    object: ObjectTypeData,
    nodes: Vec<NodeState>,
    symbols: Vec<SymbolState>,
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    resolved: TypeId,
) -> Snapshot {
    let store = context.store();
    let TypeData::Object(object) = store.type_payload(resolved).unwrap().data() else {
        unreachable!();
    };
    let mut seen = HashSet::new();
    let mut symbols = Vec::new();
    let mut nodes = Vec::new();
    for (node, _) in parsed.arena.iter() {
        let node = source_node(parsed, node);
        nodes.push(NodeState {
            node,
            annotation: store.type_node_links(node).cloned(),
            symbol: store.symbol_node_links(node).cloned(),
            signature: store.signature_links(node).cloned(),
        });
        if let Some(bound) = context.file(SOURCE).unwrap().1.symbol(node) {
            let bound = store.get_merged_symbol(bound).unwrap();
            if seen.insert(bound) {
                symbols.push(SymbolState {
                    symbol: bound,
                    value: store.value_symbol_links(bound).cloned(),
                    declared: store.declared_type_links(bound).cloned(),
                    alias: store.type_alias_links(bound).cloned(),
                });
            }
        }
    }
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        object: object.clone(),
        nodes,
        symbols,
    }
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    literal: NodeRef,
    resolved: TypeId,
    expected: &[RowState],
) {
    let rows = callables(parsed, literal);
    let warm = snapshot(context, parsed, resolved);
    for _ in 0..3 {
        assert_eq!(context.get_type_from_type_node(literal), Ok(resolved));
        let actual = rows
            .iter()
            .map(|row| read_row(context, parsed, row))
            .collect::<Vec<_>>();
        assert_eq!(actual, expected);
        assert_literal_owner(context, parsed, literal, resolved, &actual);
        assert_eq!(snapshot(context, parsed, resolved), warm);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn typed_optional_construct_rows_keep_their_real_owner_and_static_methods() {
    let parsed = parse_source_file(concat!(
        "interface Product { name: string; }\n",
        "interface BuildOptions { size: number; }\n",
        "type Label = string | number;\n",
        "declare var Maker: {\n",
        "  prototype: Product;\n",
        "  new(value?: (Label), options?: BuildOptions): Product;\n",
        "  new(value: number, options?: BuildOptions): Product;\n",
        "  empty(): Product;\n",
        "  create(value: string, options?: BuildOptions): Product;\n",
        "};\n",
    ));
    let literal = literal(&parsed);
    let rows = callables(&parsed, literal);
    assert_eq!(rows.len(), 4);
    for strict in [false, true] {
        for annotation_first in [false, true] {
            let mut context = context(&parsed, None, strict);
            let value_owner = named_symbol(&context, "Maker");
            let value_links = context.store().value_symbol_links(value_owner).cloned();
            if annotation_first {
                query_annotations(&mut context, &rows);
            }
            let resolved = context.get_type_from_type_node(literal).unwrap();
            let actual = rows
                .iter()
                .map(|row| read_row(&mut context, &parsed, row))
                .collect::<Vec<_>>();
            let instance = context
                .get_declared_type_of_symbol(named_symbol(&context, "Product"))
                .unwrap();
            assert!(actual.iter().all(|row| row.returned == instance));
            assert_ne!(resolved, instance);
            assert_ne!(symbol(&context, literal), value_owner);
            assert_ne!(actual[0].signature, actual[1].signature);
            assert_eq!(actual[0].parameters[1], actual[1].parameters[1]);
            assert_eq!(actual[0].parameters[1], actual[3].parameters[1]);
            let label = context
                .get_declared_type_of_symbol(named_symbol(&context, "Label"))
                .unwrap();
            assert_eq!(actual[0].annotations[0], label);
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let TypeData::Union(data) = context.store().type_payload(label).unwrap().data() else {
                panic!("the original Label alias must retain its string/number union");
            };
            assert!(
                context
                    .store()
                    .type_payload(label)
                    .unwrap()
                    .alias()
                    .is_some()
            );
            let mut expected = vec![bootstrap.string_type, bootstrap.number_type];
            expected.sort_unstable();
            assert_eq!(data.union.types, expected);
            assert_eq!(actual[1].parameters[0], bootstrap.number_type);
            assert_eq!(
                context.store().value_symbol_links(value_owner).cloned(),
                value_links
            );
            assert_literal_owner(&context, &parsed, literal, resolved, &actual);
            assert_replay(&mut context, &parsed, literal, resolved, &actual);
        }
    }
}

#[test]
fn optional_construct_parameter_keeps_a_direct_defaulted_reference() {
    let parsed = parse_source_file(concat!(
        "interface Product { name: string; }\n",
        "interface Box<T = string> { value: T; }\n",
        "declare var Maker: { prototype: Product; new(value?: Box): Product; };\n",
    ));
    let literal = literal(&parsed);
    let rows = callables(&parsed, literal);
    for annotation_first in [false, true] {
        let mut context = context(&parsed, None, true);
        if annotation_first {
            query_annotations(&mut context, &rows);
        }
        let resolved = context.get_type_from_type_node(literal).unwrap();
        let actual = vec![read_row(&mut context, &parsed, &rows[0])];
        let owner = named_symbol(&context, "Box");
        let target = context.get_declared_type_of_symbol(owner).unwrap();
        let TypeData::TypeReference(reference) = context
            .store()
            .type_payload(actual[0].annotations[0])
            .unwrap()
            .data()
        else {
            panic!("the written Box reference must use its real default argument");
        };
        assert_eq!(reference.object.target, Some(target));
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[context.store().intrinsic_bootstrap().unwrap().string_type][..])
        );
        assert_eq!(
            context.store().type_payload(target).unwrap().symbol(),
            Some(owner)
        );
        assert_literal_owner(&context, &parsed, literal, resolved, &actual);
        assert_replay(&mut context, &parsed, literal, resolved, &actual);
    }
}

#[test]
fn optional_construct_arrays_keep_real_es5_targets_on_warm_queries() {
    let library = parse_source_file(ES5);
    let parsed = parse_source_file(concat!(
        "interface Product { name: string; }\n",
        "declare var Maker: { prototype: Product;\n",
        "  new(values?: number[], readonlyValues?: readonly number[]): Product;\n",
        "};\n",
    ));
    let literal = literal(&parsed);
    let rows = callables(&parsed, literal);
    for annotation_first in [false, true] {
        let mut context = context(&parsed, Some(&library), true);
        if annotation_first {
            query_annotations(&mut context, &rows);
        }
        let resolved = context.get_type_from_type_node(literal).unwrap();
        let actual = vec![read_row(&mut context, &parsed, &rows[0])];
        let targets = [
            context.global_types().array_type,
            context.global_types().readonly_array_type,
        ];
        assert_ne!(targets[0], targets[1]);
        for (&annotation, target) in actual[0].annotations.iter().zip(targets) {
            let TypeData::TypeReference(reference) =
                context.store().type_payload(annotation).unwrap().data()
            else {
                panic!("the array annotation must retain its canonical reference");
            };
            assert_eq!(reference.object.target, Some(target));
            assert_eq!(
                reference.resolved_type_arguments.as_deref(),
                Some(&[context.store().intrinsic_bootstrap().unwrap().number_type][..])
            );
            let owner = context
                .store()
                .type_payload(target)
                .unwrap()
                .symbol()
                .unwrap();
            let declarations = context
                .store()
                .symbol(owner)
                .unwrap()
                .declarations()
                .unwrap();
            assert!(declarations.iter().all(|node| node.file == LIBRARY));
            assert!(
                declarations
                    .iter()
                    .all(|&node| symbol(&context, node) == owner)
            );
        }
        assert_literal_owner(&context, &parsed, literal, resolved, &actual);
        assert_replay(&mut context, &parsed, literal, resolved, &actual);
    }
}

#[test]
fn optional_construct_admission_keeps_mixed_generic_and_index_boundaries() {
    for (source, kind) in [
        (
            "type Mixed = { prototype: string; (value: string): string; new(value?: string): string; };",
            SyntaxKind::CallSignature,
        ),
        (
            "type Generic = { new<T>(value?: T): T; };",
            SyntaxKind::ConstructSignature,
        ),
        (
            "type Indexed = { new(value?: string): number; [key: string]: number; };",
            SyntaxKind::ConstructSignature,
        ),
    ] {
        let parsed = parse_source_file(source);
        let literal = literal(&parsed);
        let anchor = nodes(&parsed, kind)[0];
        let mut context = context(&parsed, None, true);
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
        );
        for _ in 0..2 {
            assert_eq!(
                context.get_type_from_type_node(literal),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::UnsupportedSyntax { node: anchor, kind }
                ))
            );
            assert!(context.store().type_node_links(literal).is_none());
            assert!(context.store().signature_links(anchor).is_none());
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len()
                ),
                before
            );
            assert!(context.diagnostics().is_empty());
        }
    }
}
