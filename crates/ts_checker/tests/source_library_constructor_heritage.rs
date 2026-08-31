use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalArtifactQueryError, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, ClassMembers,
    IntrinsicBootstrapOptions, SignatureId, SourceCheckError, TypeData, TypeId,
    UnsupportedSourceSyntax, signatures::SignatureFlags,
};
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(260_100);
const STATUS: FileId = FileId::new(260_101);

macro_rules! library_sources {
    ($($name:literal),+ $(,)?) => {
        &[$((
            concat!("\"/lib/lib.", $name, ".d.ts\""),
            include_str!(concat!("../../ts_bundled/libs/lib.", $name, ".d.ts")),
        )),+]
    };
}

// The complete ES2022 default-library closure, in the compiler's library priority order.
const LIBRARIES: &[(&str, &str)] = library_sources![
    "es5",
    "es2015",
    "es2016",
    "es2017",
    "es2018",
    "es2019",
    "es2020",
    "es2021",
    "es2022",
    "dom",
    "dom.iterable",
    "dom.asynciterable",
    "webworker.importscripts",
    "scripthost",
    "es2015.core",
    "es2015.collection",
    "es2015.generator",
    "es2015.iterable",
    "es2015.promise",
    "es2015.proxy",
    "es2015.reflect",
    "es2015.symbol",
    "es2015.symbol.wellknown",
    "es2016.array.include",
    "es2016.intl",
    "es2017.arraybuffer",
    "es2017.date",
    "es2017.object",
    "es2017.sharedmemory",
    "es2017.string",
    "es2017.intl",
    "es2017.typedarrays",
    "es2018.asyncgenerator",
    "es2018.asynciterable",
    "es2018.intl",
    "es2018.promise",
    "es2018.regexp",
    "es2019.array",
    "es2019.object",
    "es2019.string",
    "es2019.symbol",
    "es2019.intl",
    "es2020.bigint",
    "es2020.date",
    "es2020.promise",
    "es2020.sharedmemory",
    "es2020.string",
    "es2020.symbol.wellknown",
    "es2020.intl",
    "es2020.number",
    "es2021.promise",
    "es2021.string",
    "es2021.weakref",
    "es2021.intl",
    "es2022.array",
    "es2022.error",
    "es2022.intl",
    "es2022.object",
    "es2022.string",
    "es2022.regexp",
    "decorators",
    "decorators.legacy",
    "es2022.full",
];

// Complete prepared Hono 06880c4a sources. The last test does not claim body support.
const HONO_EXCEPTION: &str = r#"/**
 * @module
 * This module provides the `HTTPException` class.
 */

import type { ContentfulStatusCode } from './utils/http-status'

/**
 * Options for creating an `HTTPException`.
 * @property res - Optional response object to use.
 * @property message - Optional custom error message.
 * @property cause - Optional cause of the error.
 */
type HTTPExceptionOptions = {
  res?: Response
  message?: string
  cause?: unknown
}

/**
 * `HTTPException` must be used when a fatal error such as authentication failure occurs.
 *
 * @see {@link https://hono.dev/docs/api/exception}
 *
 * @param {StatusCode} status - status code of HTTPException
 * @param {HTTPExceptionOptions} options - options of HTTPException
 * @param {HTTPExceptionOptions["res"]} options.res - response of options of HTTPException
 * @param {HTTPExceptionOptions["message"]} options.message - message of options of HTTPException
 * @param {HTTPExceptionOptions["cause"]} options.cause - cause of options of HTTPException
 *
 * @example
 * ```ts
 * import { HTTPException } from 'hono/http-exception'
 *
 * // ...
 *
 * app.post('/auth', async (c, next) => {
 *   // authentication
 *   if (authorized === false) {
 *     throw new HTTPException(401, { message: 'Custom error message' })
 *   }
 *   await next()
 * })
 * ```
 */
export class HTTPException extends Error {
  readonly res?: Response
  readonly status: ContentfulStatusCode

  /**
   * Creates an instance of `HTTPException`.
   * @param status - HTTP status code for the exception. Defaults to 500.
   * @param options - Additional options for the exception.
   */
  constructor(status: ContentfulStatusCode = 500, options?: HTTPExceptionOptions) {
    super(options?.message, { cause: options?.cause })
    this.res = options?.res
    this.status = status
  }

  /**
   * Returns the response object associated with the exception.
   * If a response object is not provided, a new response is created with the error message and status code.
   * @returns The response object.
   */
  getResponse(): Response {
    if (this.res) {
      const newResponse = new Response(this.res.body, {
        status: this.status,
        headers: this.res.headers,
      })
      return newResponse
    }
    return new Response(this.message, {
      status: this.status,
    })
  }
}
"#;

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

struct Input {
    file: FileId,
    path: &'static str,
    parsed: ParseResult,
    library: bool,
}

fn inputs(source: &str, hono: bool) -> Vec<Input> {
    let mut files = LIBRARIES
        .iter()
        .enumerate()
        .map(|(index, &(path, text))| Input {
            file: FileId::new(260_000 + u32::try_from(index).unwrap()),
            path,
            parsed: parse_source_file(text),
            library: true,
        })
        .collect::<Vec<_>>();
    if hono {
        files.push(Input {
            file: STATUS,
            path: "\"/project/src/utils/http-status.ts\"",
            parsed: parse_source_file(HONO_STATUS),
            library: false,
        });
    }
    files.push(Input {
        file: SOURCE,
        path: if hono {
            "\"/project/src/http-exception.ts\""
        } else {
            "\"/project/constructor-heritage.ts\""
        },
        parsed: parse_source_file(source),
        library: false,
    });
    files
}

fn context(files: &[Input], hono: bool) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    for input in files {
        assert!(
            input.parsed.diagnostics.is_empty(),
            "{:?}",
            input.parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &input.parsed.arena,
                input.parsed.source_file,
                input.file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(input.path),
                    CanonicalSourceLanguage::TypeScript,
                    input.library,
                    input.library,
                    if hono && !input.library {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for input in files {
        binder
            .bind_typescript_declaration_slice(&input.parsed.arena, input.file)
            .unwrap();
    }
    let source = files.iter().find(|input| input.file == SOURCE).unwrap();
    let resolutions = source
        .parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::ImportDeclaration(import) = &record.data else {
                return None;
            };
            assert!(hono);
            let NodeData::StringLiteral(specifier) = &source
                .parsed
                .arena
                .get(import.module_specifier)
                .unwrap()
                .data
            else {
                unreachable!()
            };
            assert_eq!(specifier.text, "./utils/http-status");
            Some(CanonicalModuleResolutionEntry::resolved(
                NodeRef::new(source.parsed.arena.id(), SOURCE, import.module_specifier),
                CanonicalResolvedModuleInput::new(
                    STATUS,
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::Esm,
                ),
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(resolutions.len(), usize::from(hono));
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|input| (input.file, &input.parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_bind_call_apply: true,
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            strict_property_initialization: true,
            use_unknown_in_catch_variables: true,
            no_implicit_any: true,
            no_implicit_this: true,
            no_unused_locals: hono,
            no_unused_parameters: hono,
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

fn reference(context: &CanonicalCheckerContext<'_>, file: FileId, node: NodeId) -> NodeRef {
    NodeRef::new(context.file(file).unwrap().0.id(), file, node)
}

fn named(
    context: &CanonicalCheckerContext<'_>,
    file: FileId,
    kind: SyntaxKind,
    expected: &str,
) -> NodeRef {
    let arena = context.file(file).unwrap().0;
    arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::ClassDeclaration(data) => data.name?,
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::PropertySignatureDeclaration(data) => data.name,
                NodeData::PropertyDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some(reference(context, file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
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

fn global(context: &CanonicalCheckerContext<'_>, name: &str) -> SemanticSymbolId {
    let raw = context
        .store()
        .symbol_table(context.globals())
        .unwrap()
        .get_source(name)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn cached_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .store()
        .source_file_links(context.source_file(file).unwrap())
        .is_some_and(|links| links.type_checked)
}

fn class_nodes(
    context: &CanonicalCheckerContext<'_>,
    class: NodeRef,
) -> (NodeRef, NodeRef, NodeRef) {
    let arena = context.file(class.file).unwrap().0;
    let NodeData::ClassDeclaration(data) = &arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    let clause = data.heritage_clauses.as_ref().unwrap().nodes[0];
    let NodeData::HeritageClause(clause) = &arena.get(clause).unwrap().data else {
        unreachable!()
    };
    let NodeData::ExpressionWithTypeArguments(base) =
        &arena.get(clause.types.nodes[0]).unwrap().data
    else {
        unreachable!()
    };
    let constructor = data
        .members
        .nodes
        .iter()
        .find(|&&member| arena.get(member).unwrap().kind == SyntaxKind::Constructor)
        .copied()
        .unwrap();
    let range = arena.get(constructor).unwrap().range;
    let call = arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            (record.range.start >= range.start
                && record.range.end <= range.end
                && arena.get(call.expression)?.kind == SyntaxKind::SuperKeyword)
                .then_some(node)
        })
        .unwrap();
    (
        reference(context, class.file, base.expression),
        reference(context, class.file, constructor),
        reference(context, class.file, call),
    )
}

fn construct_declarations(
    context: &CanonicalCheckerContext<'_>,
    owner: SemanticSymbolId,
) -> Vec<NodeRef> {
    context
        .store()
        .symbol(owner)
        .unwrap()
        .declarations()
        .unwrap()
        .iter()
        .flat_map(|&declaration| {
            let arena = context.file(declaration.file).unwrap().0;
            let NodeData::InterfaceDeclaration(data) = &arena.get(declaration.node).unwrap().data
            else {
                panic!("the constructor owner must be an actual interface")
            };
            data.members
                .nodes
                .iter()
                .filter_map(|&member| {
                    (arena.get(member).unwrap().kind == SyntaxKind::ConstructSignature)
                        .then_some(reference(context, declaration.file, member))
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

fn assert_constructor_signature(
    context: &CanonicalCheckerContext<'_>,
    declaration: NodeRef,
    result: TypeId,
    optional: bool,
) -> SignatureId {
    let arena = context.file(declaration.file).unwrap().0;
    let NodeData::ConstructSignatureDeclaration(data) = &arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let signature = context
        .store()
        .signature_links(declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
    assert!(record.type_parameters().is_empty());
    assert!(record.this_parameter().is_none());
    assert_eq!(record.resolved_return_type(), Some(result));
    assert_eq!(
        cached_type(
            context,
            reference(context, declaration.file, data.type_.unwrap())
        ),
        result
    );
    assert_eq!(record.parameters().len(), data.parameters.nodes.len());
    assert_eq!(
        record.min_argument_count(),
        if optional {
            0
        } else {
            i32::try_from(record.parameters().len()).unwrap()
        }
    );
    for (&parameter, &source) in record.parameters().iter().zip(&data.parameters.nodes) {
        let source = reference(context, declaration.file, source);
        assert_eq!(symbol(context, source), parameter);
        let NodeData::ParameterDeclaration(data) = &arena.get(source.node).unwrap().data else {
            unreachable!()
        };
        assert_eq!(data.question_token.is_some(), optional);
        let annotation = cached_type(
            context,
            reference(context, source.file, data.type_.unwrap()),
        );
        let intrinsic = context.store().intrinsic_bootstrap().unwrap();
        match arena.get(data.type_.unwrap()).unwrap().kind {
            SyntaxKind::StringKeyword => assert_eq!(annotation, intrinsic.string_type),
            SyntaxKind::NumberKeyword => assert_eq!(annotation, intrinsic.number_type),
            SyntaxKind::TypeReference => assert_eq!(
                context.store().type_payload(annotation).unwrap().symbol(),
                Some(global(context, "ErrorOptions")),
            ),
            _ => panic!("expected the real scalar or ErrorOptions annotation"),
        }
        let value = context
            .store()
            .value_symbol_links(parameter)
            .unwrap()
            .resolved_type
            .unwrap();
        if optional {
            let TypeData::Union(union) = context.store().type_payload(value).unwrap().data() else {
                panic!("an optional constructor parameter keeps its undefined union")
            };
            let mut expected = [
                context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .undefined_type,
                annotation,
            ];
            expected.sort_unstable();
            assert_eq!(union.union.types, expected);
        } else {
            assert_eq!(value, annotation);
        }
    }
    signature
}

fn assert_base_and_super(
    context: &CanonicalCheckerContext<'_>,
    members: &ClassMembers,
    value_owner: SemanticSymbolId,
    constructor_owner: SemanticSymbolId,
    instance_owner: SemanticSymbolId,
    selected_declaration: NodeRef,
) {
    let store = context.store();
    let constructor = store
        .value_symbol_links(value_owner)
        .unwrap()
        .resolved_type
        .unwrap();
    let instance = store
        .declared_type_links(instance_owner)
        .unwrap()
        .declared_type
        .unwrap();
    assert_eq!(
        store
            .declared_type_links(constructor_owner)
            .unwrap()
            .declared_type,
        Some(constructor)
    );
    assert_ne!(constructor, instance);
    assert_eq!(
        store.type_payload(constructor).unwrap().symbol(),
        Some(constructor_owner)
    );
    assert_eq!(
        store.type_payload(instance).unwrap().symbol(),
        Some(instance_owner)
    );
    assert!(
        !store
            .symbol(value_owner)
            .unwrap()
            .flags()
            .contains(SymbolFlags::CLASS)
    );
    let base = members.base().unwrap();
    assert_eq!(base.symbol(), value_owner);
    assert_eq!(base.value_type(), constructor);
    assert_eq!(base.instance_type(), instance);
    let (heritage, own_constructor, call) = class_nodes(context, members.shells().declaration());
    assert_eq!(cached_type(context, heritage), constructor);
    assert_eq!(
        store.symbol_node_links(heritage).unwrap().resolved_symbol,
        Some(value_owner)
    );
    let arena = context.file(call.file).unwrap().0;
    let NodeData::CallExpression(data) = &arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(data.arguments.nodes.len(), 2);
    assert_eq!(
        cached_type(context, reference(context, call.file, data.expression)),
        constructor
    );
    assert_eq!(
        cached_type(context, call),
        store.intrinsic_bootstrap().unwrap().void_type
    );
    let selected = store
        .signature_links(call)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    assert_eq!(
        store.signature(selected).unwrap().declaration(),
        Some(selected_declaration)
    );
    assert_eq!(
        store.signature(selected).unwrap().resolved_return_type(),
        Some(instance)
    );
    let own = store
        .signature(members.default_construct_signature())
        .unwrap();
    assert_eq!(own.declaration(), Some(own_constructor));
    assert_eq!(
        own.resolved_return_type(),
        Some(members.shells().instance_type())
    );
    assert_inherited_message(context, members, instance_owner);
}

fn assert_inherited_message(
    context: &CanonicalCheckerContext<'_>,
    members: &ClassMembers,
    instance_owner: SemanticSymbolId,
) {
    let store = context.store();
    let arena = context.file(SOURCE).unwrap().0;
    let message = store
        .symbol(instance_owner)
        .unwrap()
        .members()
        .and_then(|table| store.symbol_table(table))
        .unwrap()
        .get_source("message")
        .unwrap();
    assert_eq!(store.get_parent_of_symbol(message), Some(instance_owner));
    assert_eq!(
        store
            .symbol_table(members.instance_members().unwrap())
            .unwrap()
            .get_source("message"),
        Some(message)
    );
    assert!(members.instance_properties().contains(&message));
    assert!(!members.declared_instance_properties().contains(&message));
    let string = store.intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(
        store.value_symbol_links(message).unwrap().resolved_type,
        Some(string)
    );
    let accesses = arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &arena.get(access.name)?.data else {
                return None;
            };
            (name.text == "message").then_some(reference(context, SOURCE, node))
        })
        .collect::<Vec<_>>();
    assert_eq!(accesses.len(), 2);
    for access in accesses {
        assert_eq!(cached_type(context, access), string);
        assert_eq!(
            store.symbol_node_links(access).unwrap().resolved_symbol,
            Some(message)
        );
    }
}

fn snapshot(context: &CanonicalCheckerContext<'_>) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.type_predicate_len(),
            store.type_alias_len(),
            store.type_resolution_len(),
        ],
        store.relation_state_snapshot(),
        context.diagnostics().clone(),
        context
            .file_order()
            .iter()
            .map(|&file| {
                (
                    file,
                    store
                        .source_file_links(context.source_file(file).unwrap())
                        .cloned(),
                )
            })
            .collect::<Vec<_>>(),
        context
            .file_order()
            .iter()
            .flat_map(|&file| {
                context.file(file).unwrap().0.iter().map(move |(node, _)| {
                    let node = reference(context, file, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.value_symbol_links(symbol).cloned(),
                    store.declared_type_links(symbol).cloned(),
                    store.type_alias_links(symbol).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .signatures()
            .map(|(id, signature)| {
                (
                    (
                        id,
                        signature.flags(),
                        signature.declaration(),
                        signature.parameters().to_vec(),
                        signature.min_argument_count(),
                        signature.resolved_min_argument_count(),
                        signature.resolved_return_type(),
                    ),
                    (
                        signature.type_parameters().to_vec(),
                        signature.this_parameter(),
                        signature.target(),
                        signature.mapper(),
                        signature.resolved_type_predicate(),
                        signature.isolated_signature_type(),
                        signature.composite().cloned(),
                    ),
                )
            })
            .collect::<Vec<_>>(),
    )
}

fn check_and_members(
    context: &mut CanonicalCheckerContext<'_>,
    name: &str,
    query_first: bool,
) -> ClassMembers {
    let declaration = named(context, SOURCE, SyntaxKind::ClassDeclaration, name);
    let owner = symbol(context, declaration);
    let early = query_first.then(|| context.get_nongeneric_class_members(owner).unwrap());
    assert!(!checked(context, SOURCE));
    let (_, _, call) = class_nodes(context, declaration);
    assert!(context.store().signature_links(call).is_none());
    context.check_source_file(SOURCE).unwrap();
    assert!(checked(context, SOURCE));
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let published = snapshot(context);
    let members = context.get_nongeneric_class_members(owner).unwrap();
    assert_eq!(snapshot(context), published);
    if let Some(early) = early {
        assert_eq!(early, members);
    }
    members
}

fn replay(context: &mut CanonicalCheckerContext<'_>, members: &ClassMembers) {
    let initial = snapshot(context);
    let (heritage, _, call) = class_nodes(context, members.shells().declaration());
    let base = members.base().unwrap();
    let signature = context
        .store()
        .signature_links(call)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    for _ in 0..2 {
        context.recheck_source_file(SOURCE).unwrap();
        assert_eq!(
            context
                .get_nongeneric_class_members(members.shells().symbol())
                .unwrap(),
            *members
        );
        assert_eq!(
            context.get_type_at_location(heritage).unwrap(),
            base.value_type()
        );
        assert_eq!(
            context.get_return_type_of_signature(signature).unwrap(),
            base.instance_type()
        );
        assert_eq!(
            context.get_type_at_location(call).unwrap(),
            context.store().intrinsic_bootstrap().unwrap().void_type
        );
        assert_eq!(snapshot(context), initial);
    }
}

#[test]
fn real_error_heritage_keeps_both_library_constructors_and_inherited_message() {
    let files = inputs(
        concat!(
            "class RequestError extends Error {\n",
            "  constructor(message: string, options: ErrorOptions) { super(message, options); }\n",
            "  read(): string { return this.message; }\n",
            "}\n",
            "declare const options: ErrorOptions;\n",
            "const error = new RequestError('request', options);\n",
            "const message: string = error.message;\n",
        ),
        false,
    );
    for query_first in [false, true] {
        let mut context = context(&files, false);
        let error = global(&context, "Error");
        let constructor = global(&context, "ErrorConstructor");
        assert_ne!(error, constructor);
        let variable = context
            .store()
            .symbol(error)
            .unwrap()
            .value_declaration()
            .unwrap();
        let arena = context.file(variable.file).unwrap().0;
        assert_eq!(
            arena.get(variable.node).unwrap().kind,
            SyntaxKind::VariableDeclaration
        );
        assert_eq!(symbol(&context, variable), error);
        assert!(
            context
                .file(variable.file)
                .unwrap()
                .1
                .source_facts()
                .unwrap()
                .is_default_library()
        );
        let declarations = construct_declarations(&context, constructor);
        assert_eq!(declarations.len(), 2);
        assert_eq!(
            files
                .iter()
                .find(|input| input.file == declarations[0].file)
                .unwrap()
                .path,
            "\"/lib/lib.es5.d.ts\""
        );
        assert_eq!(
            files
                .iter()
                .find(|input| input.file == declarations[1].file)
                .unwrap()
                .path,
            "\"/lib/lib.es2022.error.d.ts\""
        );
        let members = check_and_members(&mut context, "RequestError", query_first);
        let instance = members.base().unwrap().instance_type();
        let signatures = declarations
            .iter()
            .map(|&node| assert_constructor_signature(&context, node, instance, true))
            .collect::<Vec<_>>();
        assert_ne!(signatures[0], signatures[1]);
        assert_eq!(
            context
                .store()
                .signature(signatures[0])
                .unwrap()
                .parameters()
                .len(),
            1
        );
        assert_eq!(
            context
                .store()
                .signature(signatures[1])
                .unwrap()
                .parameters()
                .len(),
            2
        );
        assert_base_and_super(
            &context,
            &members,
            error,
            constructor,
            error,
            declarations[1],
        );
        replay(&mut context, &members);
        for input in files.iter().filter(|input| input.library) {
            assert!(!checked(&context, input.file));
        }
    }
}

#[test]
fn implicit_error_heritage_clones_every_real_constructor_signature() {
    let files = inputs(
        concat!(
            "class InheritedError extends Error {\n",
            "  read(): string { return this.message; }\n",
            "}\n",
            "declare const options: ErrorOptions;\n",
            "const empty = new InheritedError();\n",
            "const caused = new InheritedError('wrapped', options);\n",
        ),
        false,
    );
    let mut context = context(&files, false);
    let declaration = named(
        &context,
        SOURCE,
        SyntaxKind::ClassDeclaration,
        "InheritedError",
    );
    let owner = symbol(&context, declaration);
    assert!(
        !context
            .file(SOURCE)
            .unwrap()
            .0
            .iter()
            .any(|(_, node)| { node.kind == SyntaxKind::Constructor })
    );
    context.check_source_file(SOURCE).unwrap();
    assert!(checked(&context, SOURCE));
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let published = snapshot(&context);
    let members = context.get_nongeneric_class_members(owner).unwrap();
    assert_eq!(snapshot(&context), published);
    let signatures = inherited_constructor_signatures(&context, &members);
    assert_eq!(signatures.len(), 2);
    assert_ne!(signatures[0], signatures[1]);
    assert_eq!(members.default_construct_signature(), signatures[0]);
    let base = members.base().unwrap();
    assert_eq!(base.symbol(), global(&context, "Error"));
    assert_eq!(
        context
            .store()
            .type_payload(base.instance_type())
            .unwrap()
            .symbol(),
        Some(global(&context, "Error"))
    );
    assert_eq!(
        context
            .store()
            .type_payload(base.value_type())
            .unwrap()
            .symbol(),
        Some(global(&context, "ErrorConstructor"))
    );
    assert_ne!(base.instance_type(), members.shells().instance_type());
    let calls = assert_implicit_new_calls(&context, &members, signatures[1]);
    for iteration in 0..3 {
        if iteration != 0 {
            context.recheck_source_file(SOURCE).unwrap();
        }
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
        assert_eq!(
            inherited_constructor_signatures(&context, &members),
            signatures
        );
        for &signature in &signatures {
            assert_eq!(
                context.get_return_type_of_signature(signature).unwrap(),
                members.shells().instance_type()
            );
        }
        for &call in &calls {
            assert_eq!(
                context.get_type_at_location(call).unwrap(),
                members.shells().instance_type()
            );
        }
        assert_eq!(
            assert_implicit_new_calls(&context, &members, signatures[1]),
            calls
        );
        assert_eq!(snapshot(&context), published);
    }
}

fn inherited_constructor_signatures(
    context: &CanonicalCheckerContext<'_>,
    members: &ClassMembers,
) -> Vec<SignatureId> {
    let store = context.store();
    let value = store.type_payload(members.shells().value_type()).unwrap();
    let TypeData::Object(value) = value.data() else {
        panic!("the derived value keeps its actual class object")
    };
    let structured = &value.structured;
    assert_eq!(structured.call_signature_count, 0);
    let signatures = structured.signatures.as_ref().unwrap();
    let declarations = construct_declarations(context, global(context, "ErrorConstructor"));
    assert_eq!(declarations.len(), 2);
    assert_eq!(signatures.len(), declarations.len());
    for (&signature, declaration) in signatures.iter().zip(declarations) {
        let original = assert_constructor_signature(
            context,
            declaration,
            members.base().unwrap().instance_type(),
            true,
        );
        assert_ne!(signature, original);
        let inherited = store.signature(signature).unwrap();
        let original = store.signature(original).unwrap();
        assert_eq!(inherited.declaration(), original.declaration());
        assert_eq!(inherited.parameters(), original.parameters());
        assert_eq!(inherited.flags(), original.flags());
        assert_eq!(
            inherited.min_argument_count(),
            original.min_argument_count()
        );
        assert_eq!(inherited.type_parameters(), original.type_parameters());
        assert_eq!(inherited.this_parameter(), original.this_parameter());
        assert_eq!(
            inherited.resolved_return_type(),
            Some(members.shells().instance_type())
        );
        assert!(inherited.target().is_none());
        assert!(inherited.mapper().is_none());
        assert!(inherited.composite().is_none());
        assert!(inherited.resolved_type_predicate().is_none());
        assert!(inherited.isolated_signature_type().is_none());
    }
    signatures.clone()
}

fn assert_implicit_new_calls(
    context: &CanonicalCheckerContext<'_>,
    members: &ClassMembers,
    selected: SignatureId,
) -> Vec<NodeRef> {
    let store = context.store();
    let arena = context.file(SOURCE).unwrap().0;
    let calls = arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::NewExpression(call) = &record.data else {
                return None;
            };
            Some((reference(context, SOURCE, node), call))
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 2);
    for ((node, call), count) in calls.iter().zip([0, 2]) {
        assert_eq!(
            call.arguments.as_ref().map_or(0, |args| args.nodes.len()),
            count
        );
        assert_eq!(
            cached_type(context, *node),
            members.shells().instance_type()
        );
        assert_eq!(
            cached_type(context, reference(context, SOURCE, call.expression)),
            members.shells().value_type()
        );
        assert_eq!(
            store
                .signature_links(*node)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(selected)
        );
    }
    for name in ["empty", "caused"] {
        let declaration = named(context, SOURCE, SyntaxKind::VariableDeclaration, name);
        assert_eq!(
            store
                .value_symbol_links(symbol(context, declaration))
                .unwrap()
                .resolved_type,
            Some(members.shells().instance_type())
        );
    }
    calls.into_iter().map(|(node, _)| node).collect()
}

#[test]
fn unrelated_constructor_value_uses_its_real_return_interface() {
    let files = inputs(
        concat!(
            "interface Product { message: string; }\n",
            "interface ProductFactory { new(message: string, code: number): Product; readonly prototype: Product; readonly category: string; }\n",
            "declare var BuildProduct: ProductFactory;\n",
            "class CustomProduct extends BuildProduct {\n",
            "  constructor(message: string, code: number) { super(message, code); }\n",
            "  read(): string { return super.message; }\n",
            "  static readCategory(): string { return super.category; }\n",
            "}\n",
            "const product = new CustomProduct('made', 1);\n",
            "const message: string = product.message;\n",
            "const category: string = CustomProduct.category;\n",
        ),
        false,
    );
    for query_first in [false, true] {
        let mut context = context(&files, false);
        let value = global(&context, "BuildProduct");
        let owner = global(&context, "ProductFactory");
        let instance = global(&context, "Product");
        assert_ne!(value, owner);
        assert_ne!(value, instance);
        assert_ne!(owner, instance);
        let declarations = construct_declarations(&context, owner);
        let [declaration] = declarations.as_slice() else {
            unreachable!()
        };
        let members = check_and_members(&mut context, "CustomProduct", query_first);
        assert_constructor_signature(
            &context,
            *declaration,
            members.base().unwrap().instance_type(),
            false,
        );
        assert_base_and_super(&context, &members, value, owner, instance, *declaration);
        assert_raw_instance_super(&context, &members);
        assert_inherited_static_property(&context, &members, owner);
        replay(&mut context, &members);
    }
}

fn assert_raw_instance_super(context: &CanonicalCheckerContext<'_>, members: &ClassMembers) {
    let arena = context.file(SOURCE).unwrap().0;
    let receivers = arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &arena.get(access.name)?.data else {
                return None;
            };
            (name.text == "message"
                && arena.get(access.expression)?.kind == SyntaxKind::SuperKeyword)
                .then_some(reference(context, SOURCE, access.expression))
        })
        .collect::<Vec<_>>();
    let [receiver] = receivers.as_slice() else {
        panic!("expected the real super.message receiver")
    };
    assert_eq!(
        cached_type(context, *receiver),
        members.base().unwrap().instance_type()
    );
}

fn assert_inherited_static_property(
    context: &CanonicalCheckerContext<'_>,
    members: &ClassMembers,
    constructor_owner: SemanticSymbolId,
) {
    let store = context.store();
    let property = store
        .symbol(constructor_owner)
        .unwrap()
        .members()
        .and_then(|table| store.symbol_table(table))
        .unwrap()
        .get_source("category")
        .unwrap();
    assert_eq!(
        store.get_parent_of_symbol(property),
        Some(constructor_owner)
    );
    assert_eq!(
        store
            .symbol_table(members.static_members())
            .unwrap()
            .get_source("category"),
        Some(property)
    );
    assert!(members.static_properties().contains(&property));
    assert!(!members.declared_static_properties().contains(&property));
    assert!(!members.instance_properties().contains(&property));
    let string = store.intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(
        store.value_symbol_links(property).unwrap().resolved_type,
        Some(string)
    );
    let arena = context.file(SOURCE).unwrap().0;
    let accesses = arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &arena.get(access.name)?.data else {
                return None;
            };
            (name.text == "category").then_some(reference(context, SOURCE, node))
        })
        .collect::<Vec<_>>();
    assert_eq!(accesses.len(), 2);
    for access in accesses {
        assert_eq!(cached_type(context, access), string);
        assert_eq!(
            store.symbol_node_links(access).unwrap().resolved_symbol,
            Some(property)
        );
    }
}

#[test]
fn complete_hono_class_keeps_original_inputs_and_an_explicit_unsupported_result() {
    let files = inputs(HONO_EXCEPTION, true);
    let mut context = context(&files, true);
    for file in [SOURCE, STATUS] {
        assert!(
            context
                .file(file)
                .unwrap()
                .1
                .source_facts()
                .unwrap()
                .is_always_strict()
        );
    }
    let class = named(
        &context,
        SOURCE,
        SyntaxKind::ClassDeclaration,
        "HTTPException",
    );
    let (heritage, _, _) = class_nodes(&context, class);
    let error = global(&context, "Error");
    assert_eq!(
        context.get_symbol_at_location(heritage),
        Err(CanonicalArtifactQueryError::SourceCheck(
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(class))
        ))
    );
    let mut resolver = context
        .name_resolver_host(context.options().name_resolution)
        .unwrap();
    assert_eq!(
        resolver
            .resolve_entity_name(heritage, SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE)
            .unwrap(),
        Some(error)
    );
    let variable = context
        .store()
        .symbol(error)
        .unwrap()
        .value_declaration()
        .unwrap();
    let arena = context.file(variable.file).unwrap().0;
    let NodeData::VariableDeclaration(variable) = &arena.get(variable.node).unwrap().data else {
        unreachable!()
    };
    let annotation = NodeRef::new(
        arena.id(),
        context
            .store()
            .symbol(error)
            .unwrap()
            .value_declaration()
            .unwrap()
            .file,
        variable.type_.unwrap(),
    );
    let constructor_type = context.get_type_from_type_node(annotation).unwrap();
    assert_eq!(
        context
            .store()
            .type_payload(constructor_type)
            .unwrap()
            .symbol(),
        Some(global(&context, "ErrorConstructor"))
    );
    let mut first = None;
    for _ in 0..2 {
        assert_eq!(
            context.check_source_file(SOURCE),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Class(class)
            ))
        );
        assert!(!checked(&context, SOURCE));
        assert!(!checked(&context, STATUS));
        assert_hono_body_unchecked(&context, class);
        assert!(context.diagnostics().is_empty());
        let current = snapshot(&context);
        if let Some(first) = &first {
            assert_eq!(&current, first);
        } else {
            first = Some(current);
        }
    }
}

fn assert_hono_body_unchecked(context: &CanonicalCheckerContext<'_>, class: NodeRef) {
    let arena = context.file(SOURCE).unwrap().0;
    let (_, constructor, _) = class_nodes(context, class);
    let NodeData::ConstructorDeclaration(data) = &arena.get(constructor.node).unwrap().data else {
        unreachable!()
    };
    let NodeData::ParameterDeclaration(status) = &arena.get(data.parameters.nodes[0]).unwrap().data
    else {
        unreachable!()
    };
    let default = reference(context, SOURCE, status.initializer.unwrap());
    let NodeData::NumericLiteral(literal) = &arena.get(default.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(literal.text, "500");
    assert!(context.store().type_node_links(default).is_none());
    let calls = arena
        .iter()
        .filter_map(|(node, record)| {
            matches!(
                record.kind,
                SyntaxKind::CallExpression | SyntaxKind::NewExpression
            )
            .then_some(reference(context, SOURCE, node))
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 3);
    for call in calls {
        assert!(context.store().signature_links(call).is_none());
        assert!(context.store().type_node_links(call).is_none());
    }
    let owner = symbol(context, class);
    assert!(
        context
            .store()
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .is_none()
    );
    assert!(
        context
            .store()
            .value_symbol_links(owner)
            .and_then(|links| links.resolved_type)
            .is_none()
    );
}
