use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, ClassError, ClassMembers, DeclaredTypeError, DeclaredTypeLinks,
    IntrinsicBootstrapOptions, SignatureId, SignatureLinks, SourceCheckError, SourceFileLinks,
    SymbolNodeLinks, TypeAliasLinks, TypeData, TypeId, TypeNodeLinks, TypeNodeUnavailable,
    ValueSymbolLinks, artifact_queries::CanonicalArtifactQueryError, signatures::SignatureFlags,
    type_records::LiteralValue, types::TypeFlags,
};
use ts_jsnum::Number;
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(202_940);
const SOURCE: FileId = FileId::new(202_941);
const STATUS: FileId = FileId::new(202_942);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

// The complete src/utils/http-status.ts at Hono 06880c4a stays unchanged.
const HONO_STATUS: &str = r#"/**
 * @module
 * HTTP Status utility.
 */

export type InfoStatusCode = 100 | 101 | 102 | 103
export type SuccessStatusCode = 200 | 201 | 202 | 203 | 204 | 205 | 206 | 207 | 208 | 226
export type DeprecatedStatusCode = 305 | 306
export type RedirectStatusCode = 300 | 301 | 302 | 303 | 304 | DeprecatedStatusCode | 307 | 308
export type ClientErrorStatusCode =
  | 400
  | 401
  | 402
  | 403
  | 404
  | 405
  | 406
  | 407
  | 408
  | 409
  | 410
  | 411
  | 412
  | 413
  | 414
  | 415
  | 416
  | 417
  | 418
  | 421
  | 422
  | 423
  | 424
  | 425
  | 426
  | 428
  | 429
  | 431
  | 451
export type ServerErrorStatusCode = 500 | 501 | 502 | 503 | 504 | 505 | 506 | 507 | 508 | 510 | 511

/**
 * `UnofficialStatusCode` can be used to specify an unofficial status code.
 * @example
 *
 * ```ts
 * app.get('/unknown', (c) => {
 *   return c.text("Unknown Error", 520 as UnofficialStatusCode)
 * })
 * ```
 */
export type UnofficialStatusCode = -1

/**
 * @deprecated
 * Use `UnofficialStatusCode` instead.
 */
export type UnOfficalStatusCode = UnofficialStatusCode

/**
 * If you want to use an unofficial status, use `UnofficialStatusCode`.
 */
export type StatusCode =
  | InfoStatusCode
  | SuccessStatusCode
  | RedirectStatusCode
  | ClientErrorStatusCode
  | ServerErrorStatusCode
  | UnofficialStatusCode

export type ContentlessStatusCode = 101 | 204 | 205 | 304
export type ContentfulStatusCode = Exclude<StatusCode, ContentlessStatusCode>
"#;

// Keep the actual import and annotated default, without the separate Error heritage.
const HONO_CONSUMER: &str = concat!(
    "import type { ContentfulStatusCode } from './utils/http-status'\n",
    "export class Reply { constructor(status: ContentfulStatusCode = 500) {} }\n",
    "new Reply();\n",
);

fn context<'arena>(
    library: &'arena ParseResult,
    source: &'arena ParseResult,
    status: Option<&'arena ParseResult>,
) -> CanonicalCheckerContext<'arena> {
    let mut files = vec![
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\"", true),
        (SOURCE, source, "\"/project/src/http-exception.ts\"", false),
    ];
    if let Some(status) = status {
        files.push((
            STATUS,
            status,
            "\"/project/src/utils/http-status.ts\"",
            false,
        ));
    }
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, library) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    if library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for &(file, parsed, _, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let resolutions = status.map(|_| {
        let import = only_node(source, SOURCE, SyntaxKind::ImportDeclaration);
        let NodeData::ImportDeclaration(import) = &source.arena.get(import.node).unwrap().data
        else {
            unreachable!()
        };
        CanonicalModuleResolutionEntry::resolved(
            node(source, SOURCE, import.module_specifier),
            CanonicalResolvedModuleInput::new(
                STATUS,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )
    });
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _, _)| (file, &parsed.arena))
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
            // The imported control keeps Hono's effective build flags.
            no_unused_locals: status.is_some(),
            no_unused_parameters: status.is_some(),
            module_kind: ModuleKind::Es2020,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(resolutions),
    )
    .unwrap()
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn only_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, file, id)));
    let found = matches.next().expect("the source must contain this node");
    assert!(matches.next().is_none(), "expected one {kind:?}");
    found
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let record = parsed.arena.get(id).unwrap();
    let parent_record = parsed.arena.get(parent.node).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(parent_record.range.start <= record.range.start);
    assert!(record.range.end <= parent_record.range.end);
    node(parsed, parent.file, id)
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

#[derive(Clone, Copy)]
struct Parts {
    class: NodeRef,
    class_name: NodeRef,
    constructor: NodeRef,
    parameter: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
    initializer: NodeRef,
}

fn parts(parsed: &ParseResult) -> Parts {
    let class = only_node(parsed, SOURCE, SyntaxKind::ClassDeclaration);
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    assert!(data.heritage_clauses.is_none());
    let [constructor] = data.members.nodes.as_slice() else {
        panic!("Reply must retain its one constructor")
    };
    let constructor = child(parsed, class, *constructor);
    let NodeData::ConstructorDeclaration(data) = &parsed.arena.get(constructor.node).unwrap().data
    else {
        unreachable!()
    };
    let [parameter] = data.parameters.nodes.as_slice() else {
        panic!("the constructor must retain its one parameter")
    };
    let parameter = child(parsed, constructor, *parameter);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(parameter_data.question_token.is_none());
    assert!(parameter_data.modifiers.is_none());
    assert!(parameter_data.dot_dot_dot_token.is_none());
    let NodeData::ClassDeclaration(class_data) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    Parts {
        class,
        class_name: child(parsed, class, class_data.name.unwrap()),
        constructor,
        parameter,
        name: child(parsed, parameter, parameter_data.name),
        annotation: child(parsed, parameter, parameter_data.type_.unwrap()),
        initializer: child(parsed, parameter, parameter_data.initializer.unwrap()),
    }
}

fn alias(parsed: &ParseResult, file: FileId, name: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (identifier.text == name)
                .then_some((node(parsed, file, id), node(parsed, file, alias.type_)))
        })
        .unwrap_or_else(|| panic!("missing actual alias {name}"))
}

fn cached_type(context: &CanonicalCheckerContext<'_>, location: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(location)
        .and_then(|links| links.resolved_type)
        .expect("the checked source must publish this type")
}

fn value_type(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .expect("the real source owner must retain its declared type")
}

fn is_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .store()
        .source_file_links(context.source_file(file).unwrap())
        .is_some_and(|links| links.type_checked)
}

fn assert_number(context: &CanonicalCheckerContext<'_>, type_: TypeId, expected: i32) -> TypeId {
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.flags(), TypeFlags::NUMBER_LITERAL);
    let TypeData::Literal(literal) = record.data() else {
        panic!("the initializer must retain its numeric literal")
    };
    assert_eq!(
        literal.value,
        LiteralValue::Number(Number::new(f64::from(expected)))
    );
    literal.regular_type
}

#[derive(Debug, Eq, PartialEq)]
struct Checked {
    members: ClassMembers,
    parameter: SemanticSymbolId,
    declared: TypeId,
    initializer: TypeId,
    signature: SignatureId,
    constructions: Vec<NodeRef>,
}

#[allow(clippy::too_many_lines)] // Keep the constructor, alias, literal pair, and real calls in one identity check.
fn checked_state(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    parts: Parts,
    members: ClassMembers,
    default: i32,
) -> Checked {
    let class = symbol(context, parts.class);
    let parameter = symbol(context, parts.parameter);
    assert_eq!(
        context.store().symbol(class).unwrap().flags(),
        SymbolFlags::CLASS
    );
    let parameter_record = context.store().symbol(parameter).unwrap();
    assert_eq!(
        parameter_record.flags(),
        SymbolFlags::FUNCTION_SCOPED_VARIABLE
    );
    assert_eq!(
        parameter_record.declarations(),
        Some(&[parts.parameter][..])
    );
    assert_eq!(parameter_record.value_declaration(), Some(parts.parameter));
    assert!(members.declared_instance_properties().is_empty());
    let signature = members.default_construct_signature();
    let signature_record = context.store().signature(signature).unwrap();
    assert_eq!(signature_record.declaration(), Some(parts.constructor));
    assert_eq!(signature_record.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(signature_record.parameters(), &[parameter]);
    assert_eq!(signature_record.min_argument_count(), 0);
    assert!(signature_record.type_parameters().is_empty());
    assert_eq!(signature_record.target(), None);
    assert_eq!(signature_record.mapper(), None);
    assert_eq!(
        signature_record.resolved_return_type(),
        Some(members.shells().instance_type())
    );
    let (alias, body) = alias(parsed, SOURCE, "Status");
    let alias_owner = symbol(context, alias);
    let declared = value_type(context, parameter);
    assert_eq!(cached_type(context, parts.annotation), declared);
    assert_eq!(cached_type(context, parts.name), declared);
    assert_eq!(
        context
            .store()
            .type_alias_links(alias_owner)
            .unwrap()
            .declared_type,
        Some(declared)
    );
    assert_eq!(cached_type(context, body), declared);
    let record = context.store().type_payload(declared).unwrap();
    let named = context.store().type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(named.symbol(), Some(alias_owner));
    let TypeData::Union(union) = record.data() else {
        panic!("the parameter must keep the named union")
    };
    assert_eq!(union.union.types.len(), 2);
    let mut values = union
        .union
        .types
        .iter()
        .map(|&type_| {
            let TypeData::Literal(literal) = context.store().type_payload(type_).unwrap().data()
            else {
                panic!("Status must retain its numeric members")
            };
            assert_eq!(literal.regular_type, type_);
            let LiteralValue::Number(number) = &literal.value else {
                unreachable!()
            };
            number.to_string()
        })
        .collect::<Vec<_>>();
    values.sort();
    assert_eq!(values, ["400", "500"]);
    let initializer = cached_type(context, parts.initializer);
    let regular = assert_number(context, initializer, default);
    assert_eq!(
        context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .cached_number_literal_type(Number::new(f64::from(default))),
        Some(regular)
    );
    let TypeData::Literal(literal) = context.store().type_payload(initializer).unwrap().data()
    else {
        unreachable!()
    };
    assert_eq!(literal.fresh_type, Some(initializer));
    let TypeData::Literal(regular_literal) = context.store().type_payload(regular).unwrap().data()
    else {
        unreachable!()
    };
    assert_eq!(regular_literal.regular_type, regular);
    assert_eq!(regular_literal.fresh_type, Some(initializer));
    assert_eq!(regular_literal.value, literal.value);
    assert_ne!(regular, initializer);
    assert_ne!(declared, initializer);
    assert_eq!(union.union.types.contains(&regular), default == 500);
    let constructions = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::NewExpression).then_some(node(parsed, SOURCE, id))
        })
        .collect::<Vec<_>>();
    assert_eq!(constructions.len(), 2);
    for &construction in &constructions {
        assert_eq!(
            cached_type(context, construction),
            members.shells().instance_type()
        );
        assert_eq!(
            context
                .store()
                .signature_links(construction)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(signature)
        );
    }
    Checked {
        members,
        parameter,
        declared,
        initializer,
        signature,
        constructions,
    }
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct SymbolState {
    symbol: SemanticSymbolId,
    value: Option<ValueSymbolLinks>,
    declared: Option<DeclaredTypeLinks>,
    type_alias: Option<TypeAliasLinks>,
    import_alias: Option<AliasSymbolLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    nodes: Vec<NodeState>,
    symbols: Vec<SymbolState>,
    sources: Vec<Option<SourceFileLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(context: &CanonicalCheckerContext<'_>) -> Snapshot {
    let store = context.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: context
            .file_order()
            .iter()
            .flat_map(|&file| {
                let (arena, _) = context.file(file).unwrap();
                arena.iter().map(move |(id, _)| {
                    let node = NodeRef::new(arena.id(), file, id);
                    NodeState {
                        node,
                        type_: store.type_node_links(node).cloned(),
                        symbol: store.symbol_node_links(node).cloned(),
                        signature: store.signature_links(node).cloned(),
                    }
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| SymbolState {
                symbol,
                value: store.value_symbol_links(symbol).cloned(),
                declared: store.declared_type_links(symbol).cloned(),
                type_alias: store.type_alias_links(symbol).cloned(),
                import_alias: store.alias_symbol_links(symbol).cloned(),
            })
            .collect(),
        sources: context
            .file_order()
            .iter()
            .map(|&file| {
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn public_queries(context: &mut CanonicalCheckerContext<'_>, parts: Parts, checked: &Checked) {
    let class = symbol(context, parts.class);
    assert_eq!(
        context.get_nongeneric_class_members(class),
        Ok(checked.members.clone())
    );
    for location in [parts.annotation, parts.name, parts.parameter] {
        assert_eq!(context.get_type_at_location(location), Ok(checked.declared));
    }
    assert_eq!(
        context.get_type_from_type_node(parts.annotation),
        Ok(checked.declared)
    );
    assert_eq!(
        context.get_type_at_location(parts.initializer),
        Ok(checked.initializer)
    );
    assert_eq!(
        context.get_symbol_at_location(parts.name),
        Ok(Some(checked.parameter))
    );
    assert_eq!(
        context.get_symbol_declarations(checked.parameter).unwrap(),
        [parts.parameter]
    );
    // The return-query API does not yet admit a class Constructor declaration.
    assert_eq!(
        context.get_return_type_of_signature(checked.signature),
        Err(DeclaredTypeError::TypeNodeUnavailable(
            TypeNodeUnavailable::InvalidFunctionSignature(checked.signature)
        ))
    );
    assert_eq!(context.type_to_string(checked.declared).unwrap(), "Status");
    for &construction in &checked.constructions {
        assert_eq!(
            context.get_type_at_location(construction),
            Ok(checked.members.shells().instance_type())
        );
    }
    assert_eq!(
        context.get_symbol_at_location(parts.class_name),
        Ok(Some(class))
    );
}

#[derive(Clone, Copy)]
enum FirstQuery {
    Source,
    Header,
    Parameter,
    Initializer,
}

#[allow(clippy::too_many_lines)] // Keep each query order, diagnostic, and replay in the same source context.
fn check_local(default: i32) {
    let library = parse_source_file(ES5);
    let source = parse_source_file(&format!(
        "export type Status = 400 | 500;\nexport class Reply {{ constructor(status: Status = {default}) {{}} }}\nnew Reply(); new Reply(400);\n"
    ));
    let parts = parts(&source);
    for first in [
        FirstQuery::Source,
        FirstQuery::Header,
        FirstQuery::Parameter,
        FirstQuery::Initializer,
    ] {
        let mut context = context(&library, &source, None);
        let class = symbol(&context, parts.class);
        let header = match first {
            FirstQuery::Source => None,
            FirstQuery::Header => {
                let header = context.get_nongeneric_class_members(class).unwrap();
                let signature = context
                    .store()
                    .signature(header.default_construct_signature())
                    .unwrap();
                assert_eq!(signature.min_argument_count(), 0);
                assert_eq!(signature.declaration(), Some(parts.constructor));
                assert_eq!(signature.parameters(), &[symbol(&context, parts.parameter)]);
                let declared = value_type(&context, symbol(&context, parts.parameter));
                assert_eq!(cached_type(&context, parts.annotation), declared);
                assert!(matches!(
                    context.store().type_payload(declared).unwrap().data(),
                    TypeData::Union(union) if union.union.types.len() == 2
                ));
                assert!(context.store().type_node_links(parts.initializer).is_none());
                assert!(!is_checked(&context, SOURCE));
                assert!(context.diagnostics().is_empty());
                let cold_default = snapshot(&context);
                assert_eq!(
                    context.get_nongeneric_class_members(class),
                    Ok(header.clone())
                );
                assert_eq!(snapshot(&context), cold_default);
                Some((header, declared))
            }
            FirstQuery::Parameter => {
                context.get_type_at_location(parts.name).unwrap();
                assert!(is_checked(&context, SOURCE));
                None
            }
            FirstQuery::Initializer => {
                context.get_type_at_location(parts.initializer).unwrap();
                assert!(is_checked(&context, SOURCE));
                None
            }
        };
        context.check_source_file(SOURCE).unwrap();
        assert!(is_checked(&context, SOURCE));
        if default == 500 {
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
        } else {
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("the invalid default must produce one assignment error")
            };
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.node, Some(parts.name));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type '999' is not assignable to type 'Status'."
            );
            assert!(diagnostic.related_information.is_empty());
        }
        let members = context.get_nongeneric_class_members(class).unwrap();
        if let Some((header, declared)) = header {
            assert_eq!(members, header);
            assert_eq!(
                value_type(&context, symbol(&context, parts.parameter)),
                declared
            );
        }
        let checked = checked_state(&context, &source, parts, members, default);
        public_queries(&mut context, parts, &checked);
        let warm = snapshot(&context);
        for _ in 0..2 {
            context.check_source_file(SOURCE).unwrap();
            public_queries(&mut context, parts, &checked);
            context.recheck_source_file(SOURCE).unwrap();
            public_queries(&mut context, parts, &checked);
            assert_eq!(snapshot(&context), warm);
            assert_eq!(
                checked_state(&context, &source, parts, checked.members.clone(), default),
                checked
            );
        }
    }
}

#[test]
fn named_numeric_constructor_defaults_keep_annotation_and_fresh_initializer_identities() {
    check_local(500);
}

#[test]
fn invalid_named_constructor_defaults_report_the_real_assignment_without_changing_the_parameter() {
    check_local(999);
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the unchanged provider, real import owner, and unreached Exclude dependency together.
fn hono_contentful_status_default_keeps_the_import_alias_dependency_visible() {
    let library = parse_source_file(ES5);
    let provider = parse_source_file(HONO_STATUS);
    let source = parse_source_file(HONO_CONSUMER);
    let parts = parts(&source);
    let imported = only_node(&source, SOURCE, SyntaxKind::ImportSpecifier);
    let (contentful, body) = alias(&provider, STATUS, "ContentfulStatusCode");
    let NodeData::TypeReferenceNode(reference) = &provider.arena.get(body.node).unwrap().data
    else {
        panic!("the original ContentfulStatusCode must remain an Exclude reference")
    };
    let NodeData::Identifier(name) = &provider.arena.get(reference.type_name).unwrap().data else {
        unreachable!()
    };
    assert_eq!(name.text, "Exclude");
    let arguments = &reference.type_arguments.as_ref().unwrap().nodes;
    assert_eq!(arguments.len(), 2);
    for (&argument, expected) in arguments
        .iter()
        .zip(["StatusCode", "ContentlessStatusCode"])
    {
        let NodeData::TypeReferenceNode(reference) = &provider.arena.get(argument).unwrap().data
        else {
            unreachable!()
        };
        let NodeData::Identifier(name) = &provider.arena.get(reference.type_name).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(name.text, expected);
    }
    let (exclude, exclude_body) = alias(&library, LIBRARY, "Exclude");
    assert_eq!(
        library.arena.get(exclude_body.node).unwrap().kind,
        SyntaxKind::ConditionalType
    );
    for query_first in [false, true] {
        let mut context = context(&library, &source, Some(&provider));
        let class = symbol(&context, parts.class);
        let imported_owner = symbol(&context, imported);
        assert_eq!(
            context.store().symbol(imported_owner).unwrap().flags(),
            SymbolFlags::ALIAS
        );
        assert_ne!(imported_owner, symbol(&context, contentful));
        assert_eq!(
            context
                .store()
                .symbol(symbol(&context, exclude))
                .unwrap()
                .declarations(),
            Some(&[exclude][..])
        );
        let declared_error =
            DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::ImportAliasTypeReference {
                node: parts.annotation,
                alias: imported_owner,
            });
        let source_error = SourceCheckError::DeclaredType(declared_error);
        let cold = snapshot(&context);
        if query_first {
            assert_eq!(
                context.get_nongeneric_class_members(class),
                Err(ClassError::DeclaredType(declared_error))
            );
        }
        for _ in 0..2 {
            assert_eq!(context.check_source_file(SOURCE), Err(source_error));
            assert_eq!(
                context.get_type_at_location(parts.initializer),
                Err(CanonicalArtifactQueryError::SourceCheck(source_error))
            );
            assert_eq!(
                context.get_nongeneric_class_members(class),
                Err(ClassError::DeclaredType(declared_error))
            );
            assert_eq!(context.recheck_source_file(SOURCE), Err(source_error));
            assert_eq!(snapshot(&context), cold);
            assert!(!is_checked(&context, SOURCE));
            assert!(!is_checked(&context, STATUS));
            assert!(context.store().type_node_links(parts.initializer).is_none());
            assert!(context.store().type_node_links(parts.annotation).is_none());
        }
    }
}
