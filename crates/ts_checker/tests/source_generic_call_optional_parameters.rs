use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, TypeMapperId, ValueSymbolLinks, signatures::SignatureFlags,
    type_records::StructuredTypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(294_600);

fn context(parsed: &ParseResult, strict: bool) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-call-optional-parameters.ts\""),
                CanonicalSourceLanguage::TypeScript,
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
        [(FILE, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: strict,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    assert_eq!(parsed.arena.get(id).unwrap().parent, Some(parent.node));
    node(parsed, id)
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)))
        .collect::<Vec<_>>();
    found.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    found
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the source declaration or checked call must retain its signature")
}

struct Formal {
    declaration: NodeRef,
    constraint: NodeRef,
    default: Option<NodeRef>,
}

struct Parameter {
    declaration: NodeRef,
    annotation: NodeRef,
    optional: bool,
}

struct CallRow {
    owner: NodeRef,
    declaration: NodeRef,
    formals: Vec<Formal>,
    parameters: Vec<Parameter>,
    returned: NodeRef,
}

fn call_rows(parsed: &ParseResult) -> Vec<CallRow> {
    let mut rows = Vec::new();
    for owner in nodes(parsed, SyntaxKind::InterfaceDeclaration) {
        let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(owner.node).unwrap().data
        else {
            unreachable!();
        };
        for &member in &interface.members.nodes {
            let declaration = child(parsed, owner, member);
            let NodeData::CallSignatureDeclaration(call) = &parsed.arena.get(member).unwrap().data
            else {
                panic!("expected the interface's own call signature");
            };
            let formals = call
                .type_parameters
                .as_ref()
                .unwrap()
                .nodes
                .iter()
                .map(|&id| {
                    let declaration = child(parsed, declaration, id);
                    let NodeData::TypeParameterDeclaration(formal) =
                        &parsed.arena.get(id).unwrap().data
                    else {
                        panic!("expected the call's own formal");
                    };
                    Formal {
                        declaration,
                        constraint: child(parsed, declaration, formal.constraint.unwrap()),
                        default: formal.default_type.map(|id| child(parsed, declaration, id)),
                    }
                })
                .collect();
            let parameters = call
                .parameters
                .nodes
                .iter()
                .map(|&id| {
                    let declaration = child(parsed, declaration, id);
                    let NodeData::ParameterDeclaration(parameter) =
                        &parsed.arena.get(id).unwrap().data
                    else {
                        panic!("expected the call's own parameter");
                    };
                    assert!(parameter.initializer.is_none());
                    assert!(parameter.dot_dot_dot_token.is_none());
                    if let Some(question) = parameter.question_token {
                        child(parsed, declaration, question);
                        assert_eq!(
                            parsed.arena.get(question).unwrap().kind,
                            SyntaxKind::QuestionToken
                        );
                    }
                    Parameter {
                        declaration,
                        annotation: child(parsed, declaration, parameter.type_.unwrap()),
                        optional: parameter.question_token.is_some(),
                    }
                })
                .collect();
            rows.push(CallRow {
                owner,
                declaration,
                formals,
                parameters,
                returned: child(parsed, declaration, call.type_.unwrap()),
            });
        }
    }
    rows
}

#[derive(Debug, Eq, PartialEq)]
struct FormalState {
    type_: TypeId,
    symbol: Option<SemanticSymbolId>,
    constraint: Option<TypeId>,
    default: Option<TypeId>,
    target: Option<TypeId>,
    mapper: Option<TypeMapperId>,
}

#[derive(Debug, Eq, PartialEq)]
struct SignatureState {
    id: SignatureId,
    declaration: Option<NodeRef>,
    formals: Vec<FormalState>,
    parameters: Vec<(SemanticSymbolId, ValueSymbolLinks)>,
    returned: Option<TypeId>,
    target: Option<SignatureId>,
    mapper: Option<TypeMapperId>,
}

fn read_signature(context: &CanonicalCheckerContext<'_>, id: SignatureId) -> SignatureState {
    let store = context.store();
    let signature = store.signature(id).unwrap();
    assert_eq!(signature.flags(), SignatureFlags::NONE);
    assert_eq!(signature.min_argument_count(), 1);
    assert_eq!(signature.parameters().len(), 3);
    assert!(signature.this_parameter().is_none());
    assert!(signature.composite().is_none());
    let formals = signature
        .type_parameters()
        .iter()
        .map(|&type_| {
            let record = store.type_payload(type_).unwrap();
            let TypeData::TypeParameter(formal) = record.data() else {
                panic!("a signature formal must keep its canonical type parameter");
            };
            assert!(!formal.is_this_type);
            FormalState {
                type_,
                symbol: record.symbol(),
                constraint: formal.constraint,
                default: formal.resolved_default_type,
                target: formal.target,
                mapper: formal.mapper,
            }
        })
        .collect();
    SignatureState {
        id,
        declaration: signature.declaration(),
        formals,
        parameters: signature
            .parameters()
            .iter()
            .map(|&symbol| (symbol, store.value_symbol_links(symbol).unwrap().clone()))
            .collect(),
        returned: signature.resolved_return_type(),
        target: signature.target(),
        mapper: signature.mapper(),
    }
}

fn assert_optional(context: &CanonicalCheckerContext<'_>, annotation: TypeId, value: TypeId) {
    let store = context.store();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    if !bootstrap.options.strict_null_checks {
        assert_eq!(value, annotation);
        return;
    }
    let mut expected = vec![annotation, bootstrap.undefined_type];
    expected.sort_unstable();
    expected.dedup();
    let record = store.type_payload(value).unwrap();
    let TypeData::Union(union) = record.data() else {
        panic!("a strict optional parameter must use the canonical undefined union");
    };
    assert_eq!(union.union.types, expected);
    assert!(!union.union.types.contains(&bootstrap.missing_type));
    assert!(record.alias().is_none());
    assert_eq!(bootstrap.cached_union_type(&expected), Some(value));
}

fn read_row(context: &mut CanonicalCheckerContext<'_>, row: &CallRow) -> SignatureState {
    let id = signature(context, row.declaration);
    assert_eq!(row.formals.len(), 2);
    let mut formals = Vec::new();
    for formal in &row.formals {
        let owner = symbol(context, formal.declaration);
        let type_ = context.get_declared_type_of_symbol(owner).unwrap();
        let constraint = context.get_type_from_type_node(formal.constraint).unwrap();
        let default = formal
            .default
            .map(|node| context.get_type_from_type_node(node).unwrap());
        let record = context.store().type_payload(type_).unwrap();
        let TypeData::TypeParameter(data) = record.data() else {
            panic!("the real formal declaration must own a type parameter");
        };
        assert_eq!(record.symbol(), Some(owner));
        assert_eq!(data.constraint, Some(constraint));
        if let Some(default) = default {
            assert_eq!(data.resolved_default_type, Some(default));
        }
        assert!(data.target.is_none());
        assert!(data.mapper.is_none());
        formals.push(type_);
    }
    assert_ne!(formals[0], formals[1]);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    for (index, parameter) in row.parameters.iter().enumerate() {
        let annotation = context
            .get_type_from_type_node(parameter.annotation)
            .unwrap();
        assert_eq!(annotation, [formals[0], formals[1], string][index]);
        assert_eq!(parameter.optional, index != 0);
        let owner = symbol(context, parameter.declaration);
        let store = context.store();
        let record = store.symbol(owner).unwrap();
        assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
        assert_eq!(record.declarations(), Some(&[parameter.declaration][..]));
        assert_eq!(record.value_declaration(), Some(parameter.declaration));
        let links = store.value_symbol_links(owner).unwrap();
        assert!(links.target.is_none());
        assert!(links.mapper.is_none());
        if parameter.optional {
            assert_optional(context, annotation, links.resolved_type.unwrap());
        } else {
            assert_eq!(links.resolved_type, Some(annotation));
        }
        assert_eq!(store.signature(id).unwrap().parameters()[index], owner);
    }
    assert_eq!(
        context.get_type_from_type_node(row.returned),
        Ok(formals[0])
    );
    assert_eq!(context.get_return_type_of_signature(id), Ok(formals[0]));
    let actual = read_signature(context, id);
    assert_eq!(actual.declaration, Some(row.declaration));
    assert_eq!(
        actual.formals.iter().map(|f| f.type_).collect::<Vec<_>>(),
        formals
    );
    assert_eq!(actual.returned, Some(formals[0]));
    assert!(actual.target.is_none());
    assert!(actual.mapper.is_none());
    actual
}

fn query_annotations(context: &mut CanonicalCheckerContext<'_>, rows: &[CallRow]) {
    for row in rows {
        for parameter in &row.parameters {
            context
                .get_type_from_type_node(parameter.annotation)
                .unwrap();
        }
        context.get_type_from_type_node(row.returned).unwrap();
    }
}

const fn structured(data: &TypeData) -> &StructuredTypeData {
    match data {
        TypeData::Object(data) => &data.structured,
        TypeData::Interface(data) => &data.reference.object.structured,
        TypeData::TypeReference(data) => &data.object.structured,
        _ => panic!("the callable must retain its real structured receiver"),
    }
}

#[derive(Debug, Eq, PartialEq)]
struct CallState {
    callable: TypeId,
    returned: TypeId,
    selected: SignatureState,
    candidate: SignatureState,
}

fn read_call(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    call: NodeRef,
) -> CallState {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected the original call expression");
    };
    let callable = context
        .get_type_at_location(child(parsed, call, data.expression))
        .unwrap();
    let returned = context.get_type_at_location(call).unwrap();
    let id = signature(context, call);
    assert_eq!(context.get_return_type_of_signature(id), Ok(returned));
    let selected = read_signature(context, id);
    assert!(selected.formals.is_empty());
    assert_eq!(selected.returned, Some(returned));
    let candidate = read_signature(context, selected.target.unwrap());
    assert_eq!(candidate.formals.len(), 2);
    assert_eq!(selected.declaration, candidate.declaration);
    assert_ne!(selected.id, candidate.id);
    CallState {
        callable,
        returned,
        selected,
        candidate,
    }
}

fn assert_selected(context: &mut CanonicalCheckerContext<'_>, call: &CallState, status: &str) {
    let mapper = call.selected.mapper.unwrap();
    let data = context
        .store()
        .map_type(mapper, call.candidate.formals[0].type_)
        .unwrap();
    let code = context
        .store()
        .map_type(mapper, call.candidate.formals[1].type_)
        .unwrap();
    assert_eq!(call.returned, data);
    assert_eq!(context.type_to_string(code).unwrap(), status);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    for (index, ((_, links), annotation)) in call
        .selected
        .parameters
        .iter()
        .zip([data, code, string])
        .enumerate()
    {
        if let Some(value) = links.resolved_type {
            if index == 0 {
                assert_eq!(value, annotation);
            } else {
                assert_optional(context, annotation, value);
            }
        }
    }
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 6] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    rows: &[CallRow],
) {
    let calls = nodes(parsed, SyntaxKind::CallExpression);
    let expected_rows = rows
        .iter()
        .map(|row| read_row(context, row))
        .collect::<Vec<_>>();
    let expected_calls = calls
        .iter()
        .map(|&call| read_call(context, parsed, call))
        .collect::<Vec<_>>();
    let source = context.source_file(FILE).unwrap();
    let warm = (
        counts(context),
        context.diagnostics().clone(),
        context.store().source_file_links(source).cloned(),
    );
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(
            rows.iter()
                .map(|row| read_row(context, row))
                .collect::<Vec<_>>(),
            expected_rows
        );
        assert_eq!(
            calls
                .iter()
                .map(|&call| read_call(context, parsed, call))
                .collect::<Vec<_>>(),
            expected_calls
        );
        assert_eq!(
            (
                counts(context),
                context.diagnostics().clone(),
                context.store().source_file_links(source).cloned()
            ),
            warm
        );
        assert!(context.store().type_resolution_is_empty());
    }
}

fn assert_header_error(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult, call: NodeRef) {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!();
    };
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected only the invalid headers argument");
    };
    assert_eq!(
        diagnostic.node,
        Some(child(parsed, call, data.arguments.nodes[2]))
    );
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'number' is not assignable to parameter of type 'string'."
    );
}

#[test]
fn body_respond_owned_formals_keep_optional_types_defaults_and_call_diagnostics() {
    let parsed = parse_source_file(
        r"
interface BodyRespond {
  <T extends string, U extends number = 200>(data: T, status?: U, headers?: string): T;
}
declare const body: BodyRespond;
const first: 'one' = body('one');
const second: 'two' = body('two', 201);
const third: string = body<string, 202>('three', 202, 'headers');
const fourth: string = body<string, 200>('four', undefined, undefined);
body<string, 200>('bad', 200, 1);
",
    );
    let rows = call_rows(&parsed);
    assert_eq!(rows.len(), 1);
    let NodeData::InterfaceDeclaration(owner) = &parsed.arena.get(rows[0].owner.node).unwrap().data
    else {
        unreachable!();
    };
    assert!(owner.type_parameters.is_none());
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 5);
    for strict in [false, true] {
        for query_first in [false, true] {
            let mut context = context(&parsed, strict);
            if query_first {
                query_annotations(&mut context, &rows);
            }
            context.check_source_file(FILE).unwrap();
            assert_header_error(&context, &parsed, calls[4]);
            let row = read_row(&mut context, &rows[0]);
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            assert_eq!(row.formals[0].constraint, Some(bootstrap.string_type));
            assert_eq!(row.formals[1].constraint, Some(bootstrap.number_type));
            for (index, (&call, status)) in calls
                .iter()
                .zip(["200", "201", "202", "200", "200"])
                .enumerate()
            {
                let actual = read_call(&mut context, &parsed, call);
                assert_eq!(actual.candidate, row);
                assert_selected(&mut context, &actual, status);
                let expected = ["\"one\"", "\"two\"", "string", "string", "string"][index];
                assert_eq!(context.type_to_string(actual.returned).unwrap(), expected);
                if index == 0 {
                    assert_eq!(
                        context
                            .store()
                            .map_type(actual.selected.mapper.unwrap(), row.formals[1].type_),
                        row.formals[1].default
                    );
                }
                if index == 2 {
                    assert!(
                        actual
                            .selected
                            .parameters
                            .iter()
                            .all(|(_, links)| links.resolved_type.is_some())
                    );
                }
            }
            assert_replay(&mut context, &parsed, &rows);
        }
    }
}

fn assert_copied_candidate(
    context: &CanonicalCheckerContext<'_>,
    call: &CallState,
    original: &SignatureState,
    interface: TypeId,
    outer: TypeId,
    argument: TypeId,
) {
    let store = context.store();
    let TypeData::TypeReference(reference) = store.type_payload(call.callable).unwrap().data()
    else {
        panic!("the call must use its applied generic interface");
    };
    assert_eq!(reference.object.target, Some(interface));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[argument][..])
    );
    assert_eq!(reference.object.structured.call_signature_count, 1);
    assert_eq!(
        reference.object.structured.signatures.as_deref(),
        Some(&[call.candidate.id][..])
    );
    assert_eq!(call.candidate.target, Some(original.id));
    let mapper = call.candidate.mapper.unwrap();
    assert_eq!(store.map_type(mapper, outer), Some(argument));
    for (fresh, source) in call.candidate.formals.iter().zip(&original.formals) {
        assert_ne!(fresh.type_, source.type_);
        assert_eq!(fresh.symbol, source.symbol);
        assert_eq!(fresh.target, Some(source.type_));
        assert_eq!(fresh.mapper, Some(mapper));
        assert_eq!(store.map_type(mapper, source.type_), Some(fresh.type_));
    }
}

#[test]
fn generic_receivers_keep_independent_copied_optional_call_formals() {
    let parsed = parse_source_file(
        r"
interface Wrapped<V> {
  <T extends V, U extends number = 200>(data: T, status?: U, headers?: string): T;
}
declare const text: Wrapped<string>;
declare const count: Wrapped<number>;
const first: 'copy' = text('copy');
const second: 2 = count(2);
",
    );
    let rows = call_rows(&parsed);
    assert_eq!(rows.len(), 1);
    let row = &rows[0];
    let NodeData::InterfaceDeclaration(owner) = &parsed.arena.get(row.owner.node).unwrap().data
    else {
        unreachable!();
    };
    let [outer] = owner.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one real enclosing interface formal");
    };
    let outer = child(&parsed, row.owner, *outer);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    for strict in [false, true] {
        let mut context = context(&parsed, strict);
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let original = read_row(&mut context, row);
        let owner_symbol = symbol(&context, row.owner);
        let interface = context.get_declared_type_of_symbol(owner_symbol).unwrap();
        let outer_symbol = symbol(&context, outer);
        let outer = context.get_declared_type_of_symbol(outer_symbol).unwrap();
        assert_eq!(original.formals[0].constraint, Some(outer));
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let arguments = [bootstrap.string_type, bootstrap.number_type];
        let mut copied = Vec::new();
        for ((&call, argument), expected) in calls.iter().zip(arguments).zip(["\"copy\"", "2"]) {
            let actual = read_call(&mut context, &parsed, call);
            assert_copied_candidate(&context, &actual, &original, interface, outer, argument);
            assert_selected(&mut context, &actual, "200");
            assert_eq!(context.type_to_string(actual.returned).unwrap(), expected);
            copied.push(actual.candidate);
        }
        assert_ne!(copied[0].id, copied[1].id);
        assert_ne!(copied[0].mapper, copied[1].mapper);
        for (left, right) in copied[0].formals.iter().zip(&copied[1].formals) {
            assert_ne!(left.type_, right.type_);
        }
        assert_replay(&mut context, &parsed, &rows);
    }
}

#[test]
fn owned_generic_optional_overloads_keep_order_and_selected_declarations() {
    let parsed = parse_source_file(
        r"
interface BodyRespond {
  <T extends string, U extends number = 200>(data: T, status?: U, headers?: string): T;
  <T extends number, U extends number = 201>(data: T, status?: U, headers?: string): T;
}
declare const body: BodyRespond;
const first: 'text' = body('text');
const second: 2 = body(2, 202, 'headers');
",
    );
    let rows = call_rows(&parsed);
    assert_eq!(rows.len(), 2);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    for strict in [false, true] {
        let mut context = context(&parsed, strict);
        query_annotations(&mut context, &rows);
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let originals = rows
            .iter()
            .map(|row| read_row(&mut context, row))
            .collect::<Vec<_>>();
        assert_ne!(originals[0].id, originals[1].id);
        for (left, right) in originals[0].formals.iter().zip(&originals[1].formals) {
            assert_ne!(left.type_, right.type_);
            assert_ne!(left.symbol, right.symbol);
        }
        for (index, (&call, status)) in calls.iter().zip(["200", "202"]).enumerate() {
            let actual = read_call(&mut context, &parsed, call);
            assert_eq!(actual.candidate, originals[index]);
            assert_selected(&mut context, &actual, status);
            assert_eq!(
                context.type_to_string(actual.returned).unwrap(),
                ["\"text\"", "2"][index]
            );
            let stored = structured(
                context
                    .store()
                    .type_payload(actual.callable)
                    .unwrap()
                    .data(),
            );
            assert_eq!(stored.call_signature_count, 2);
            assert_eq!(
                stored.signatures.as_deref(),
                Some(&[originals[0].id, originals[1].id][..])
            );
        }
        assert_replay(&mut context, &parsed, &rows);
    }
}
