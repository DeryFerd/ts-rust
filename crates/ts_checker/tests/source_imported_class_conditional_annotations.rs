use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry, CanonicalModuleResolutionLookup,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, ClassMembers, ConditionalRootId, DeclaredTypeLinks,
    IntrinsicBootstrapOptions, SignatureId, SignatureLinks, SourceFileLinks, SymbolNodeLinks,
    TypeAliasId, TypeAliasLinks, TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
    signatures::SignatureFlags,
    type_records::{CacheHashKey, ConditionalTypeData, LiteralValue, TypeCacheState},
    types::TypeFlags,
};
use ts_jsnum::Number;
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(202_960);
const SOURCE: FileId = FileId::new(202_961);
const PROVIDER: FileId = FileId::new(202_962);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

// The complete Hono src/utils/http-status.ts at 06880c4a stays unchanged.
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

fn source_text(local_name: &str, default: i32) -> String {
    let rename = if local_name == "ContentfulStatusCode" {
        String::new()
    } else {
        format!(" as {local_name}")
    };
    format!(
        "import type {{ ContentfulStatusCode{rename} }} from './utils/http-status';\n\
         export class Reply {{\n\
           readonly status: {local_name};\n\
           constructor(status: {local_name} = {default}) {{ this.status = status; }}\n\
         }}\n\
         new Reply();\n\
         new Reply(-1);\n\
         new Reply(500);\n"
    )
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn only_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, file, id)));
    let result = matches
        .next()
        .expect("the real source must contain this node");
    assert!(matches.next().is_none(), "expected one {kind:?}");
    result
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let record = parsed.arena.get(id).unwrap();
    let owner = parsed.arena.get(parent.node).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(owner.range.start <= record.range.start);
    assert!(record.range.end <= owner.range.end);
    node(parsed, parent.file, id)
}

fn import_specifier(parsed: &ParseResult) -> NodeRef {
    let declaration = only_node(parsed, SOURCE, SyntaxKind::ImportDeclaration);
    let NodeData::ImportDeclaration(import) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    child(parsed, declaration, import.module_specifier)
}

fn context<'arena>(
    library: &'arena ParseResult,
    provider: &'arena ParseResult,
    source: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\"", true),
        (SOURCE, source, "\"/project/src/reply.ts\"", false),
        (
            PROVIDER,
            provider,
            "\"/project/src/utils/http-status.ts\"",
            false,
        ),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, library) in files {
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
    for (file, parsed, _, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
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
            no_unused_locals: true,
            no_unused_parameters: true,
            module_kind: ModuleKind::Es2020,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            import_specifier(source),
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .and_then(|symbol| context.store().get_merged_symbol(symbol))
        .unwrap()
}

fn cached_type(context: &CanonicalCheckerContext<'_>, location: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(location)
        .and_then(|links| links.resolved_type)
        .expect("the source query must publish its actual result")
}

fn value_type(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .expect("the real value owner must retain its type")
}

fn is_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .store()
        .source_file_links(context.source_file(file).unwrap())
        .is_some_and(|links| links.type_checked)
}

struct Alias {
    declaration: NodeRef,
    body: NodeRef,
    parameters: Vec<NodeRef>,
}

fn alias(parsed: &ParseResult, file: FileId, expected: &str) -> Alias {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            if name.text != expected {
                return None;
            }
            let declaration = node(parsed, file, id);
            Some(Alias {
                declaration,
                body: child(parsed, declaration, alias.type_),
                parameters: alias
                    .type_parameters
                    .as_ref()
                    .map_or_else(Vec::new, |parameters| {
                        parameters
                            .nodes
                            .iter()
                            .map(|&parameter| child(parsed, declaration, parameter))
                            .collect()
                    }),
            })
        })
        .unwrap_or_else(|| panic!("the real source declares {expected}"))
}

fn reference_arguments(parsed: &ParseResult, reference: NodeRef, expected: &str) -> Vec<NodeRef> {
    let NodeData::TypeReferenceNode(data) = &parsed.arena.get(reference.node).unwrap().data else {
        panic!("the original annotation must remain a type reference")
    };
    let name = child(parsed, reference, data.type_name);
    let NodeData::Identifier(identifier) = &parsed.arena.get(name.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(identifier.text, expected);
    data.type_arguments
        .as_ref()
        .map_or_else(Vec::new, |arguments| {
            arguments
                .nodes
                .iter()
                .map(|&argument| child(parsed, reference, argument))
                .collect()
        })
}

struct ClassParts {
    class: NodeRef,
    class_name: NodeRef,
    field: NodeRef,
    field_name: NodeRef,
    field_annotation: NodeRef,
    constructor: NodeRef,
    parameter: NodeRef,
    parameter_name: NodeRef,
    parameter_annotation: NodeRef,
    initializer: NodeRef,
    constructions: Vec<NodeRef>,
}

fn class_parts(parsed: &ParseResult, local_name: &str) -> ClassParts {
    let class = only_node(parsed, SOURCE, SyntaxKind::ClassDeclaration);
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    assert!(data.heritage_clauses.is_none());
    assert!(data.type_parameters.is_none());
    let [field, constructor] = data.members.nodes.as_slice() else {
        panic!("the class has one readonly field and one constructor")
    };
    let field = child(parsed, class, *field);
    let constructor = child(parsed, class, *constructor);
    let NodeData::PropertyDeclaration(property) = &parsed.arena.get(field.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(property.initializer.is_none());
    assert!(property.postfix_token.is_none());
    let field_annotation = child(parsed, field, property.type_.unwrap());
    assert!(reference_arguments(parsed, field_annotation, local_name).is_empty());
    let NodeData::ConstructorDeclaration(body) = &parsed.arena.get(constructor.node).unwrap().data
    else {
        unreachable!()
    };
    let [parameter] = body.parameters.nodes.as_slice() else {
        panic!("the actual constructor has one ordinary parameter")
    };
    let parameter = child(parsed, constructor, *parameter);
    let NodeData::ParameterDeclaration(argument) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(argument.modifiers.is_none());
    assert!(argument.question_token.is_none());
    assert!(argument.dot_dot_dot_token.is_none());
    let parameter_annotation = child(parsed, parameter, argument.type_.unwrap());
    assert!(reference_arguments(parsed, parameter_annotation, local_name).is_empty());
    let constructions = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::NewExpression).then_some(node(parsed, SOURCE, id))
        })
        .collect::<Vec<_>>();
    assert_eq!(constructions.len(), 3);
    ClassParts {
        class,
        class_name: child(parsed, class, data.name.unwrap()),
        field,
        field_name: child(parsed, field, property.name),
        field_annotation,
        constructor,
        parameter,
        parameter_name: child(parsed, parameter, argument.name),
        parameter_annotation,
        initializer: child(parsed, parameter, argument.initializer.unwrap()),
        constructions,
    }
}

fn regular_number(context: &CanonicalCheckerContext<'_>, value: i32) -> TypeId {
    context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .cached_number_literal_type(Number::new(f64::from(value)))
        .expect("the real provider must publish this regular number literal")
}

fn union_members(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> Vec<TypeId> {
    let TypeData::Union(union) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the actual status type must keep its canonical numeric union")
    };
    for &member in &union.union.types {
        let record = context.store().type_payload(member).unwrap();
        assert_eq!(record.flags(), TypeFlags::NUMBER_LITERAL);
        let TypeData::Literal(literal) = record.data() else {
            unreachable!()
        };
        assert!(matches!(literal.value, LiteralValue::Number(_)));
        assert_eq!(literal.regular_type, member);
    }
    union.union.types.clone()
}

// This is the existing alias/conditional request key, using real assigned owners.
fn request_key(arguments: &[TypeId], owner: u64) -> CacheHashKey {
    let mut hasher = xxhash_rust::xxh3::Xxh3::new();
    hasher.update(&u64::try_from(arguments.len()).unwrap().to_le_bytes());
    for argument in arguments {
        hasher.update(&argument.get().to_le_bytes());
    }
    hasher.update(&[1]);
    hasher.update(&owner.to_le_bytes());
    hasher.update(&0_u64.to_le_bytes());
    CacheHashKey::new(hasher.digest128())
}

#[derive(Debug, Eq, PartialEq)]
struct ProviderState {
    owner: SemanticSymbolId,
    result: TypeId,
    arguments: [TypeId; 2],
    root: ConditionalRootId,
    parameters: [TypeId; 2],
}

#[allow(clippy::too_many_lines)] // Keep the real provider, library root, and exact request rows together.
fn provider_state(
    context: &mut CanonicalCheckerContext<'_>,
    library: &ParseResult,
    provider: &ParseResult,
) -> ProviderState {
    let contentful = alias(provider, PROVIDER, "ContentfulStatusCode");
    assert!(contentful.parameters.is_empty());
    let owner = symbol(context, contentful.declaration);
    let result = context.get_declared_type_of_symbol(owner).unwrap();
    let arguments = reference_arguments(provider, contentful.body, "Exclude");
    let [all, excluded] = arguments.as_slice() else {
        panic!("the original Exclude request has two written arguments")
    };
    let mut argument_types = Vec::new();
    for (&reference, name) in [all, excluded]
        .into_iter()
        .zip(["StatusCode", "ContentlessStatusCode"])
    {
        assert!(reference_arguments(provider, reference, name).is_empty());
        let argument = alias(provider, PROVIDER, name);
        let argument_owner = symbol(context, argument.declaration);
        let type_ = context.get_declared_type_of_symbol(argument_owner).unwrap();
        assert_eq!(cached_type(context, reference), type_);
        assert_eq!(cached_type(context, argument.body), type_);
        assert_eq!(
            context
                .store()
                .symbol_node_links(reference)
                .unwrap()
                .resolved_symbol,
            Some(argument_owner)
        );
        argument_types.push(type_);
    }
    let arguments: [TypeId; 2] = argument_types.try_into().unwrap();
    let all_members = union_members(context, arguments[0]);
    let removed = union_members(context, arguments[1]);
    let expected_removed = [101, 204, 205, 304].map(|value| regular_number(context, value));
    assert_eq!(removed.len(), expected_removed.len());
    for member in expected_removed {
        assert!(removed.contains(&member));
        assert!(all_members.contains(&member));
    }
    let retained = union_members(context, result);
    assert_eq!(
        retained,
        all_members
            .into_iter()
            .filter(|member| !removed.contains(member))
            .collect::<Vec<_>>()
    );
    for value in [500, -1] {
        assert!(retained.contains(&regular_number(context, value)));
    }
    assert_eq!(cached_type(context, contentful.body), result);
    let named = context
        .store()
        .type_alias(
            context
                .store()
                .type_payload(result)
                .unwrap()
                .alias()
                .unwrap(),
        )
        .unwrap();
    assert_eq!(named.symbol(), Some(owner));
    assert!(named.type_arguments().unwrap_or_default().is_empty());
    assert_eq!(
        context.type_to_string(result).unwrap(),
        "ContentfulStatusCode"
    );

    let exclude = alias(library, LIBRARY, "Exclude");
    let exclude_owner = symbol(context, exclude.declaration);
    assert_ne!(owner, exclude_owner);
    let declared = context.get_declared_type_of_symbol(exclude_owner).unwrap();
    let [first, second] = exclude.parameters.as_slice() else {
        panic!("the real ES5 Exclude declaration owns T and U")
    };
    let parameters = [first, second].map(|&declaration| {
        let owner = symbol(context, declaration);
        assert_eq!(
            context.store().symbol(owner).unwrap().flags(),
            SymbolFlags::TYPE_PARAMETER
        );
        let type_ = context
            .store()
            .declared_type_links(owner)
            .unwrap()
            .declared_type
            .unwrap();
        assert_eq!(
            context.store().type_payload(type_).unwrap().symbol(),
            Some(owner)
        );
        type_
    });
    let TypeData::Conditional(data) = context.store().type_payload(declared).unwrap().data() else {
        panic!("the real generic Exclude template remains conditional")
    };
    let root = context.store().conditional_root(data.root).unwrap();
    assert_eq!(root.node(), exclude.body);
    assert_eq!(root.check_type(), parameters[0]);
    assert_eq!(root.extends_type(), parameters[1]);
    assert_eq!(root.outer_type_parameters(), Some(parameters.as_slice()));
    assert!(root.infer_type_parameters().is_none());
    assert!(root.is_distributive());
    let NodeData::ConditionalTypeNode(written) =
        &library.arena.get(exclude.body.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(
        reference_arguments(
            library,
            child(library, exclude.body, written.check_type),
            "T"
        )
        .is_empty()
    );
    assert!(
        reference_arguments(
            library,
            child(library, exclude.body, written.extends_type),
            "U"
        )
        .is_empty()
    );
    assert_eq!(
        library.arena.get(written.true_type).unwrap().kind,
        SyntaxKind::NeverKeyword
    );
    assert!(
        reference_arguments(
            library,
            child(library, exclude.body, written.false_type),
            "T"
        )
        .is_empty()
    );
    let global = context
        .store()
        .symbol_store()
        .assigned_global_symbol_id(owner)
        .unwrap();
    let key = request_key(&arguments, global);
    let links = context.store().type_alias_links(exclude_owner).unwrap();
    assert_eq!(
        links.type_parameters.as_deref(),
        Some(parameters.as_slice())
    );
    assert_eq!(
        links.instantiations.as_ref().unwrap().get(&key),
        Some(&result)
    );
    let TypeCacheState::Allocated(instantiations) = root.instantiations() else {
        panic!("the actual conditional root must retain its request cache")
    };
    assert_eq!(instantiations.get(&key), Some(&result));
    ProviderState {
        owner,
        result,
        arguments,
        root: root.id(),
        parameters,
    }
}

fn assert_import(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    parts: &ClassParts,
    provider: &ProviderState,
) {
    let binding = only_node(source, SOURCE, SyntaxKind::ImportSpecifier);
    let local = symbol(context, binding);
    assert_ne!(local, provider.owner);
    let record = context.store().symbol(local).unwrap();
    assert_eq!(record.flags(), SymbolFlags::ALIAS);
    assert_eq!(record.declarations(), Some([binding].as_slice()));
    let links = context.store().alias_symbol_links(local).unwrap();
    assert_eq!(links.immediate_target, Some(provider.owner));
    assert_eq!(
        links.alias_target,
        AliasTargetState::Resolved(provider.owner)
    );
    assert_eq!(links.type_only_declaration, Some(binding));
    let CanonicalModuleResolutionLookup::Resolved(resolution) =
        context.module_resolution(import_specifier(source))
    else {
        panic!("the real source import must keep its manifest entry")
    };
    assert_eq!(resolution.target_file(), PROVIDER);
    assert_eq!(resolution.usage_mode(), CanonicalModuleResolutionMode::Esm);
    assert_eq!(resolution.target_mode(), CanonicalModuleResolutionMode::Esm);
    assert!(!resolution.is_ambient_module());
    assert_eq!(
        context.get_module_export_by_name(resolution.target_symbol(), "ContentfulStatusCode"),
        Ok(Some(provider.owner))
    );
    for annotation in [parts.field_annotation, parts.parameter_annotation] {
        assert_eq!(cached_type(context, annotation), provider.result);
        assert_eq!(
            context
                .store()
                .symbol_node_links(annotation)
                .unwrap()
                .resolved_symbol,
            Some(provider.owner)
        );
    }
    assert!(context.store().value_symbol_links(local).is_none());
}

#[derive(Debug, Eq, PartialEq)]
struct Checked {
    members: ClassMembers,
    field: SemanticSymbolId,
    parameter: SemanticSymbolId,
    signature: SignatureId,
    initializer: TypeId,
}

fn checked_state(
    context: &CanonicalCheckerContext<'_>,
    parts: &ClassParts,
    members: ClassMembers,
    provider: &ProviderState,
    default: i32,
) -> Checked {
    let owner = symbol(context, parts.class);
    let field = symbol(context, parts.field);
    let parameter = symbol(context, parts.parameter);
    assert_eq!(members.declared_instance_properties(), &[field]);
    assert_eq!(context.store().symbol(field).unwrap().parent(), Some(owner));
    assert_eq!(
        context.store().symbol(field).unwrap().value_declaration(),
        Some(parts.field)
    );
    assert_eq!(value_type(context, field), provider.result);
    assert_eq!(value_type(context, parameter), provider.result);
    let signature = members.default_construct_signature();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(parts.constructor));
    assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(record.parameters(), &[parameter]);
    assert_eq!(record.min_argument_count(), 0);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(
        record.resolved_return_type(),
        Some(members.shells().instance_type())
    );
    assert_eq!(
        context
            .store()
            .type_payload(members.shells().instance_type())
            .unwrap()
            .symbol(),
        Some(owner)
    );
    let initializer = cached_type(context, parts.initializer);
    let regular = regular_number(context, default);
    let TypeData::Literal(fresh) = context.store().type_payload(initializer).unwrap().data() else {
        panic!("the initializer must remain the actual fresh number literal")
    };
    assert_eq!(
        fresh.value,
        LiteralValue::Number(Number::new(f64::from(default)))
    );
    assert_eq!(fresh.regular_type, regular);
    assert_eq!(fresh.fresh_type, Some(initializer));
    assert_ne!(initializer, regular);
    assert_ne!(initializer, provider.result);
    let TypeData::Literal(pair) = context.store().type_payload(regular).unwrap().data() else {
        unreachable!()
    };
    assert_eq!(pair.regular_type, regular);
    assert_eq!(pair.fresh_type, Some(initializer));
    assert_eq!(
        union_members(context, provider.result).contains(&regular),
        default == 500
    );
    for &construction in &parts.constructions {
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
        field,
        parameter,
        signature,
        initializer,
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
struct RootState {
    id: ConditionalRootId,
    node: NodeRef,
    check: TypeId,
    extends: TypeId,
    distributive: bool,
    outer: Option<Vec<TypeId>>,
    infer: Option<Vec<TypeId>>,
    alias: Option<TypeAliasId>,
    instantiations: TypeCacheState,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 8],
    nodes: Vec<NodeState>,
    symbols: Vec<SymbolState>,
    roots: Vec<(TypeId, ConditionalTypeData, RootState)>,
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
            store.conditional_root_len(),
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
        roots: store
            .types()
            .filter_map(|(type_, record)| {
                let TypeData::Conditional(data) = record.data() else {
                    return None;
                };
                let root = store.conditional_root(data.root).unwrap();
                Some((
                    type_,
                    data.clone(),
                    RootState {
                        id: root.id(),
                        node: root.node(),
                        check: root.check_type(),
                        extends: root.extends_type(),
                        distributive: root.is_distributive(),
                        outer: root.outer_type_parameters().map(<[_]>::to_vec),
                        infer: root.infer_type_parameters().map(<[_]>::to_vec),
                        alias: root.alias(),
                        instantiations: root.instantiations().clone(),
                    },
                ))
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

fn public_queries(
    context: &mut CanonicalCheckerContext<'_>,
    parts: &ClassParts,
    provider: &ProviderState,
    checked: &Checked,
) {
    assert_eq!(
        context.get_nongeneric_class_members(symbol(context, parts.class)),
        Ok(checked.members.clone())
    );
    for annotation in [parts.field_annotation, parts.parameter_annotation] {
        assert_eq!(
            context.get_type_from_type_node(annotation),
            Ok(provider.result)
        );
        assert_eq!(
            context.get_type_at_location(annotation),
            Ok(provider.result)
        );
    }
    assert_eq!(
        context.get_type_at_location(parts.parameter_name),
        Ok(provider.result)
    );
    assert_eq!(
        context.get_symbol_at_location(parts.class_name),
        Ok(Some(symbol(context, parts.class)))
    );
    assert_eq!(
        context.get_symbol_at_location(parts.field_name),
        Ok(Some(checked.field))
    );
    assert_eq!(
        context.get_symbol_at_location(parts.parameter_name),
        Ok(Some(checked.parameter))
    );
    assert_eq!(
        context.get_symbol_declarations(checked.parameter).unwrap(),
        [parts.parameter]
    );
    assert_eq!(
        context.get_type_at_location(parts.initializer),
        Ok(checked.initializer)
    );
    for &construction in &parts.constructions {
        assert_eq!(
            context.get_type_at_location(construction),
            Ok(checked.members.shells().instance_type())
        );
    }
}

#[derive(Clone, Copy)]
enum FirstQuery {
    Source,
    Header,
    Annotation,
}

fn check_source(local_name: &str, default: i32, first: FirstQuery) {
    let library = parse_source_file(ES5);
    let provider = parse_source_file(HONO_STATUS);
    let source = parse_source_file(&source_text(local_name, default));
    let parts = class_parts(&source, local_name);
    let mut context = context(&library, &provider, &source);
    let owner = symbol(&context, parts.class);
    let first_result = match first {
        FirstQuery::Source => None,
        FirstQuery::Header => {
            let members = context.get_nongeneric_class_members(owner).unwrap();
            let before = snapshot(&context);
            assert_eq!(context.get_nongeneric_class_members(owner), Ok(members));
            assert_eq!(snapshot(&context), before);
            Some(cached_type(&context, parts.field_annotation))
        }
        FirstQuery::Annotation => Some(
            context
                .get_type_from_type_node(parts.field_annotation)
                .unwrap(),
        ),
    };
    assert!(!is_checked(&context, SOURCE));
    assert!(!is_checked(&context, PROVIDER));
    assert!(context.store().type_node_links(parts.initializer).is_none());
    assert!(context.diagnostics().is_empty());
    context.check_source_file(SOURCE).unwrap();
    assert!(is_checked(&context, SOURCE));
    assert!(!is_checked(&context, PROVIDER));
    let expected = provider_state(&mut context, &library, &provider);
    if let Some(first_result) = first_result {
        assert_eq!(first_result, expected.result);
    }
    assert_import(&context, &source, &parts, &expected);
    if default == 500 {
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
    } else {
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the excluded default must produce one real assignment error")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.node, Some(parts.parameter_name));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            format!("Type '{default}' is not assignable to type 'ContentfulStatusCode'.")
        );
        assert!(diagnostic.related_information.is_empty());
    }
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let checked = checked_state(&context, &parts, members, &expected, default);
    public_queries(&mut context, &parts, &expected, &checked);
    let warm = snapshot(&context);
    for _ in 0..2 {
        context.check_source_file(SOURCE).unwrap();
        public_queries(&mut context, &parts, &expected, &checked);
        context.recheck_source_file(SOURCE).unwrap();
        public_queries(&mut context, &parts, &expected, &checked);
        assert_eq!(provider_state(&mut context, &library, &provider), expected);
        assert_import(&context, &source, &parts, &expected);
        assert_eq!(
            checked_state(
                &context,
                &parts,
                checked.members.clone(),
                &expected,
                default
            ),
            checked
        );
        assert_eq!(snapshot(&context), warm);
    }
}

#[test]
fn imported_hono_status_class_annotations_keep_the_real_conditional_request() {
    for first in [
        FirstQuery::Source,
        FirstQuery::Header,
        FirstQuery::Annotation,
    ] {
        check_source("ContentfulStatusCode", 500, first);
    }
}

#[test]
fn renamed_class_type_imports_keep_the_original_hono_provider() {
    for first in [
        FirstQuery::Source,
        FirstQuery::Header,
        FirstQuery::Annotation,
    ] {
        check_source("Status", 500, first);
    }
}

#[test]
fn imported_conditional_constructor_defaults_reject_every_contentless_status() {
    for default in [101, 204, 205, 304] {
        for first in [FirstQuery::Source, FirstQuery::Header] {
            check_source("ContentfulStatusCode", default, first);
        }
    }
}
