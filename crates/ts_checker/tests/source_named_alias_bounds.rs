use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, DeclaredTypeError,
    IntrinsicBootstrapOptions, TypeData, TypeId, TypeNodeUnavailable,
    type_records::{LiteralValue, ObjectTypeData},
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(48_920);
const STATUS: FileId = FileId::new(48_921);
const ES5_FILE: FileId = FileId::new(48_922);
const DECORATORS_FILE: FileId = FileId::new(48_923);
const LEGACY_FILE: FileId = FileId::new(48_924);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const DECORATORS: &str = include_str!("../../ts_bundled/libs/lib.decorators.d.ts");
const LEGACY: &str = include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts");

// These declaration blocks retain the Hono 06880c4a source bytes. The focused
// uses below do not replace the complete project or its compiler options.
const ENV: &str = r"export type Bindings = object
export type Variables = object

export type BlankEnv = {}
export type Env = {
  Bindings?: Bindings
  Variables?: Variables
}
";

const HONO: &str = r#"import type { StatusCode } from './utils/http-status'

export type Bindings = object
export type Variables = object

export type BlankEnv = {}
export type Env = {
  Bindings?: Bindings
  Variables?: Variables
}

export type Input = {
  in?: {}
  out?: {}
  outputFormat?: ResponseFormat
}

export type BlankSchema = {}
export type BlankInput = {}

export type Schema = {
  [Path: string]: {
    [Method: `$${Lowercase<string>}`]: Endpoint
  }
}

export type Endpoint = {
  input: any
  output: any
  outputFormat: ResponseFormat
  status: StatusCode
}

export type KnownResponseFormat = 'json' | 'text' | 'redirect'
export type ResponseFormat = KnownResponseFormat | string

type KeepSchema<S extends Schema = BlankSchema> = S;
type KeepInput<I extends Input | Input['in'] = BlankInput> = I;
type KeepOutput<T extends Input['out'] = BlankInput> = T;
type SelectedSchema = KeepSchema<Schema>;
type DefaultSchema = KeepSchema;
type SelectedInput = KeepInput<Input>;
type DefaultInput = KeepInput;
type DefaultOutput = KeepOutput;
type DirectStatus<T extends StatusCode> = T;
"#;

// This is the complete original src/utils/http-status.ts at the same pin.
const HTTP_STATUS: &str = r#"/**
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

#[derive(Clone, Copy)]
struct Parameter {
    declaration: NodeRef,
    name: NodeRef,
    constraint: Option<NodeRef>,
    default: Option<NodeRef>,
}

struct Alias {
    declaration: NodeRef,
    name: NodeRef,
    body: NodeRef,
    parameters: Vec<Parameter>,
}

#[derive(Clone, Copy)]
struct Property {
    declaration: NodeRef,
    annotation: NodeRef,
    optional: bool,
}

#[derive(Clone, Copy)]
struct Index {
    declaration: NodeRef,
    parameter: NodeRef,
    key: NodeRef,
    value: NodeRef,
}

fn context<'arena>(
    files: &[(FileId, &'arena ParseResult, &str, bool)],
    resolutions: &[(NodeRef, FileId)],
    strict: bool,
    exact_optional: bool,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, library) in files {
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
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|&(file, parsed, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: strict,
                exact_optional_property_types: exact_optional,
            },
            strict_bind_call_apply: strict,
            strict_builtin_iterator_return: strict,
            strict_function_types: strict,
            strict_property_initialization: strict,
            use_unknown_in_catch_variables: strict,
            no_implicit_any: strict,
            no_implicit_this: strict,
            no_unchecked_indexed_access: false,
            no_unused_locals: true,
            no_unused_parameters: true,
            module_kind: ts_options::ModuleKind::Es2020,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ts_options::ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(resolutions.iter().map(
            |&(specifier, target)| {
                CanonicalModuleResolutionEntry::resolved(
                    specifier,
                    CanonicalResolvedModuleInput::new(
                        target,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                )
            },
        )),
    )
    .unwrap()
}

fn local_context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    context(
        &[(SOURCE, parsed, "\"/project/bounds.ts\"", false)],
        &[],
        true,
        false,
    )
}

fn alias(parsed: &ParseResult, file: FileId, expected: &str) -> Alias {
    let node_ref = |node| NodeRef::new(parsed.arena.id(), file, node);
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
            (name.text == expected).then(|| Alias {
                declaration: node_ref(node),
                name: node_ref(alias.name),
                body: node_ref(alias.type_),
                parameters: alias
                    .type_parameters
                    .iter()
                    .flat_map(|list| &list.nodes)
                    .map(|&parameter| {
                        let NodeData::TypeParameterDeclaration(data) =
                            &parsed.arena.get(parameter).unwrap().data
                        else {
                            panic!("the alias owns real type parameters")
                        };
                        Parameter {
                            declaration: node_ref(parameter),
                            name: node_ref(data.name),
                            constraint: data.constraint.map(node_ref),
                            default: data.default_type.map(node_ref),
                        }
                    })
                    .collect(),
            })
        })
        .unwrap_or_else(|| panic!("missing alias {expected}"))
}

fn property(parsed: &ParseResult, literal: NodeRef, expected: &str) -> Property {
    let NodeData::TypeLiteralNode(data) = &parsed.arena.get(literal.node).unwrap().data else {
        panic!("the member belongs to a source type literal")
    };
    data.members
        .nodes
        .iter()
        .find_map(|&node| {
            let (name, annotation, question) = match &parsed.arena.get(node)?.data {
                NodeData::PropertyDeclaration(data) => (data.name, data.type_?, data.postfix_token),
                NodeData::PropertySignatureDeclaration(data) => {
                    (data.name, data.type_, data.postfix_token)
                }
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(Property {
                declaration: NodeRef::new(literal.arena, literal.file, node),
                annotation: NodeRef::new(literal.arena, literal.file, annotation),
                optional: question.is_some(),
            })
        })
        .unwrap_or_else(|| panic!("missing property {expected}"))
}

fn index(parsed: &ParseResult, literal: NodeRef) -> Index {
    let NodeData::TypeLiteralNode(data) = &parsed.arena.get(literal.node).unwrap().data else {
        panic!("the index belongs to a source type literal")
    };
    let [node] = data.members.nodes.as_slice() else {
        panic!("the source literal has one index")
    };
    let NodeData::IndexSignatureDeclaration(data) = &parsed.arena.get(*node).unwrap().data else {
        panic!("the source member is an index signature")
    };
    assert!(data.type_parameters.is_none());
    let [parameter] = data.parameters.nodes.as_slice() else {
        panic!("the index has one value parameter")
    };
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(*parameter).unwrap().data
    else {
        panic!("the key annotation belongs to a real value parameter")
    };
    Index {
        declaration: NodeRef::new(literal.arena, literal.file, *node),
        parameter: NodeRef::new(literal.arena, literal.file, *parameter),
        key: NodeRef::new(literal.arena, literal.file, parameter_data.type_.unwrap()),
        value: NodeRef::new(literal.arena, literal.file, data.type_),
    }
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let bound = checker.file(node.file).unwrap().1;
    checker
        .store()
        .get_merged_symbol(bound.symbol(node).unwrap())
        .unwrap()
}

fn query_alias(checker: &mut CanonicalCheckerContext<'_>, alias: &Alias) -> TypeId {
    let owner = symbol(checker, alias.declaration);
    let resolved = checker.get_declared_type_of_symbol(owner).unwrap();
    assert_eq!(
        checker
            .store()
            .type_alias_links(owner)
            .unwrap()
            .declared_type,
        Some(resolved)
    );
    assert_eq!(checker.get_type_from_type_node(alias.body), Ok(resolved));
    resolved
}

fn assert_parent(parsed: &ParseResult, child: NodeRef, parent: NodeRef) {
    assert_eq!((child.arena, child.file), (parent.arena, parent.file));
    let child = parsed.arena.get(child.node).unwrap();
    let parent_record = parsed.arena.get(parent.node).unwrap();
    assert_eq!(child.parent, Some(parent.node));
    assert!(child.range.start >= parent_record.range.start);
    assert!(child.range.end <= parent_record.range.end);
}

fn text_at<'a>(parsed: &ParseResult, source: &'a str, node: NodeRef) -> &'a str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn assert_checked(checker: &CanonicalCheckerContext<'_>, file: FileId, expected: bool) {
    assert_eq!(
        checker
            .store()
            .source_file_links(checker.source_file(file).unwrap())
            .is_some_and(|links| links.type_checked),
        expected
    );
}

fn assert_unpublished(checker: &CanonicalCheckerContext<'_>, alias: &Alias) {
    let owner = symbol(checker, alias.declaration);
    assert_eq!(
        checker
            .store()
            .type_alias_links(owner)
            .and_then(|links| links.declared_type),
        None
    );
    assert_eq!(
        checker
            .store()
            .type_node_links(alias.body)
            .and_then(|links| links.resolved_type),
        None
    );
    assert!(checker.store().type_alias_links(owner).is_none_or(|links| {
        links
            .instantiations
            .as_ref()
            .is_none_or(std::collections::HashMap::is_empty)
    }));
    assert_checked(checker, alias.declaration.file, false);
}

fn assert_formal(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    alias: &Alias,
    index: usize,
    constraint: Option<TypeId>,
    default: Option<TypeId>,
) -> TypeId {
    let parameter = alias.parameters[index];
    let alias_owner = symbol(checker, alias.declaration);
    let owner = symbol(checker, parameter.declaration);
    let formal = checker
        .store()
        .type_alias_links(alias_owner)
        .unwrap()
        .type_parameters
        .as_ref()
        .unwrap()[index];
    assert_parent(parsed, alias.name, alias.declaration);
    assert_parent(parsed, parameter.declaration, alias.declaration);
    assert_parent(parsed, parameter.name, parameter.declaration);
    let owner_record = checker.store().symbol(owner).unwrap();
    assert!(owner_record.flags().intersects(SymbolFlags::TYPE_PARAMETER));
    assert_eq!(
        owner_record.declarations(),
        Some(&[parameter.declaration][..])
    );
    assert_ne!(owner, alias_owner);
    let record = checker.store().type_payload(formal).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::TypeParameter(data) = record.data() else {
        panic!("an alias formal keeps its original type parameter")
    };
    assert_eq!(data.constraint, constraint);
    assert_eq!(data.target, None);
    assert_eq!(data.mapper, None);
    assert!(!data.is_this_type);
    assert_eq!(data.constrained.resolved_base_constraint, None);
    if let Some(node) = parameter.constraint {
        assert_parent(parsed, node, parameter.declaration);
        assert_eq!(
            checker.get_type_from_type_node(node),
            Ok(constraint.unwrap())
        );
    } else {
        assert_eq!(constraint, None);
    }
    if let Some(node) = parameter.default {
        assert_parent(parsed, node, parameter.declaration);
        assert_eq!(checker.get_type_from_type_node(node), Ok(default.unwrap()));
    } else {
        assert_eq!(default, None);
        let TypeData::TypeParameter(data) = checker.store().type_payload(formal).unwrap().data()
        else {
            unreachable!()
        };
        assert_eq!(data.resolved_default_type, None);
    }
    formal
}

fn object<'a>(checker: &'a CanonicalCheckerContext<'_>, resolved: TypeId) -> &'a ObjectTypeData {
    let TypeData::Object(data) = checker.store().type_payload(resolved).unwrap().data() else {
        panic!("the written type literal has a canonical object result")
    };
    data
}

fn assert_alias_identity(checker: &CanonicalCheckerContext<'_>, alias: &Alias, resolved: TypeId) {
    let record = checker.store().type_payload(resolved).unwrap();
    let identity = checker.store().type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(identity.symbol(), Some(symbol(checker, alias.declaration)));
    assert!(identity.type_arguments().is_none_or(<[TypeId]>::is_empty));
}

fn assert_property(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    literal: NodeRef,
    resolved: TypeId,
    name: &str,
    expected: TypeId,
    optional: bool,
) -> Property {
    let property = property(parsed, literal, name);
    assert_parent(parsed, property.declaration, literal);
    assert_parent(parsed, property.annotation, property.declaration);
    assert_eq!(property.optional, optional);
    let member = symbol(checker, property.declaration);
    let data = object(checker, resolved);
    assert!(
        data.structured
            .properties
            .as_ref()
            .unwrap()
            .contains(&member)
    );
    assert_eq!(
        checker
            .store()
            .symbol_table(data.structured.members.unwrap())
            .unwrap()
            .get(EscapedName::source(name).as_ref()),
        Some(member)
    );
    let record = checker.store().symbol(member).unwrap();
    assert_eq!(record.declarations(), Some(&[property.declaration][..]));
    assert_eq!(record.flags().intersects(SymbolFlags::OPTIONAL), optional);
    assert_eq!(record.parent(), Some(symbol(checker, literal)));
    assert_eq!(
        checker.get_type_from_type_node(property.annotation),
        Ok(expected)
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(member)
            .unwrap()
            .resolved_type,
        Some(expected)
    );
    property
}

fn assert_index(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    literal: NodeRef,
    resolved: TypeId,
    expected_key: TypeId,
    expected_value: TypeId,
    parameter_name: &str,
) -> Index {
    let index = index(parsed, literal);
    assert_parent(parsed, index.declaration, literal);
    assert_parent(parsed, index.parameter, index.declaration);
    assert_parent(parsed, index.key, index.parameter);
    assert_parent(parsed, index.value, index.declaration);
    let data = object(checker, resolved);
    assert_eq!(
        checker.store().type_payload(resolved).unwrap().symbol(),
        Some(symbol(checker, literal))
    );
    assert_eq!(data.target, None);
    assert_eq!(data.mapper, None);
    let [info] = data.structured.index_infos.as_deref().unwrap() else {
        panic!("the object retains its one real index")
    };
    let info = checker.store().index_info(*info).unwrap();
    assert_eq!(info.declaration(), Some(index.declaration));
    assert_eq!(info.key_type(), expected_key);
    assert_eq!(info.value_type(), expected_value);
    assert!(!info.is_readonly());
    assert_eq!(info.index_symbol(), None);
    assert!(info.components().is_empty());
    let members = checker
        .store()
        .symbol_table(data.structured.members.unwrap())
        .unwrap();
    assert_eq!(members.len(), 1);
    assert_eq!(
        members.get(InternalSymbolName::Index.as_ref()),
        Some(symbol(checker, index.declaration))
    );
    let parameter = symbol(checker, index.parameter);
    assert!(
        !checker
            .store()
            .symbol(parameter)
            .unwrap()
            .flags()
            .intersects(SymbolFlags::TYPE_PARAMETER)
    );
    let locals = checker
        .file(index.parameter.file)
        .unwrap()
        .1
        .locals(index.declaration)
        .unwrap();
    assert_eq!(
        checker
            .store()
            .symbol_table(locals)
            .unwrap()
            .get(EscapedName::source(parameter_name).as_ref()),
        Some(parameter)
    );
    assert_eq!(checker.get_type_from_type_node(index.key), Ok(expected_key));
    assert_eq!(
        checker.get_type_from_type_node(index.value),
        Ok(expected_value)
    );
    index
}

// Capture only public semantic state. Factory validation flags are private.
fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    files: &[(FileId, &ParseResult)],
) -> Vec<String> {
    let store = checker.store();
    let mut state = vec![format!(
        "{:?}",
        [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.conditional_root_len(),
            store.symbol_store().symbol_table_len(),
        ]
    )];
    for &(file, parsed) in files {
        state.push(format!(
            "{:?}",
            store.source_file_links(checker.source_file(file).unwrap())
        ));
        state.extend(parsed.arena.iter().map(|(node, _)| {
            let node = NodeRef::new(parsed.arena.id(), file, node);
            format!(
                "{:?}",
                (
                    node,
                    store.node_links(node),
                    store.type_node_links(node),
                    store.symbol_node_links(node),
                    store.signature_links(node),
                )
            )
        }));
    }
    state.extend(store.symbol_store().symbols().map(|(symbol, record)| {
        format!(
            "{:?}",
            (
                symbol,
                record,
                store.value_symbol_links(symbol),
                store.declared_type_links(symbol),
                store.type_alias_links(symbol),
                store.alias_symbol_links(symbol),
                store.members_and_exports_links(symbol),
            )
        )
    }));
    for (_, record) in store.types() {
        state.push(format!("{record:?}"));
        if let Some(alias) = record.alias() {
            state.push(format!("{:?}", store.type_alias(alias)));
        }
        if let TypeData::Object(data) = record.data() {
            state.extend(
                data.structured
                    .index_infos
                    .iter()
                    .flatten()
                    .map(|index| format!("{:?}", store.index_info(*index))),
            );
        }
    }
    state.push(format!("{:?}", checker.diagnostics()));
    state
}

fn assert_diagnostic(
    checker: &CanonicalCheckerContext<'_>,
    index: usize,
    node: NodeRef,
    code: u32,
    arguments: &[&str],
) {
    let diagnostic = &checker.diagnostics().as_slice()[index];
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.diagnostic.arguments, arguments);
    assert!(diagnostic.related_information.is_empty());
}

fn assert_arity_and_argument_diagnostics() {
    let source = format!(
        "{ENV}{}",
        concat!(
            "export type Required<E extends Env> = E;\n",
            "export type Range<E extends Env = BlankEnv, U extends E = E> = U;\n",
            "export type Wrong = Required<string>;\n",
            "export type Missing = Required;\n",
            "export type Excess = Range<Env, BlankEnv, Env>;\n",
        )
    );
    let parsed = parse_source_file(&source);
    let wrong = alias(&parsed, SOURCE, "Wrong");
    let missing = alias(&parsed, SOURCE, "Missing");
    let excess = alias(&parsed, SOURCE, "Excess");
    let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(wrong.body.node).unwrap().data
    else {
        panic!("the invalid argument is a real type-reference argument")
    };
    let [argument] = reference.type_arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("Required has one supplied argument")
    };
    let argument = NodeRef::new(parsed.arena.id(), SOURCE, *argument);
    assert_parent(&parsed, argument, wrong.body);
    assert_eq!(text_at(&parsed, &source, argument), "string");
    let mut checker = local_context(&parsed);
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let error = bootstrap.error_type;
    assert_eq!(query_alias(&mut checker, &wrong), string);
    assert_eq!(query_alias(&mut checker, &missing), error);
    assert_eq!(query_alias(&mut checker, &excess), error);
    assert_eq!(checker.diagnostics().len(), 3);
    assert_diagnostic(&checker, 0, argument, 2344, &["string", "Env"]);
    assert_diagnostic(&checker, 1, missing.body, 2314, &["Required", "1"]);
    assert_diagnostic(&checker, 2, excess.body, 2707, &["Range", "0", "2"]);
    assert_checked(&checker, SOURCE, false);
    let before = snapshot(&checker, &[(SOURCE, &parsed)]);
    for _ in 0..2 {
        assert_eq!(query_alias(&mut checker, &wrong), string);
        assert_eq!(query_alias(&mut checker, &missing), error);
        assert_eq!(query_alias(&mut checker, &excess), error);
        assert_eq!(snapshot(&checker, &[(SOURCE, &parsed)]), before);
    }
}

fn assert_deferred_body_stays_unpublished() {
    let source = format!("type Deferred<E extends Env = BlankEnv> = string | number;\n{ENV}");
    let parsed = parse_source_file(&source);
    let deferred = alias(&parsed, SOURCE, "Deferred");
    let env = alias(&parsed, SOURCE, "Env");
    let blank = alias(&parsed, SOURCE, "BlankEnv");
    let parameter = deferred.parameters[0];
    assert_eq!(text_at(&parsed, &source, deferred.body), "string | number");
    for default_first in [false, true] {
        let mut checker = local_context(&parsed);
        let nodes = if default_first {
            [parameter.default.unwrap(), parameter.constraint.unwrap()]
        } else {
            [parameter.constraint.unwrap(), parameter.default.unwrap()]
        };
        for node in nodes {
            assert_parent(&parsed, node, parameter.declaration);
            checker.get_type_from_type_node(node).unwrap();
            assert_unpublished(&checker, &deferred);
            assert!(checker.diagnostics().is_empty());
        }
        let env_type = query_alias(&mut checker, &env);
        let blank_type = query_alias(&mut checker, &blank);
        assert_eq!(
            checker.get_type_from_type_node(parameter.constraint.unwrap()),
            Ok(env_type)
        );
        assert_eq!(
            checker.get_type_from_type_node(parameter.default.unwrap()),
            Ok(blank_type)
        );
        let owner = symbol(&checker, deferred.declaration);
        let expected = DeclaredTypeError::TypeNodeUnavailable(
            TypeNodeUnavailable::GenericReferenceUnsupported {
                node: deferred.body,
                symbol: owner,
            },
        );
        let before = snapshot(&checker, &[(SOURCE, &parsed)]);
        for _ in 0..2 {
            assert_eq!(checker.get_declared_type_of_symbol(owner), Err(expected));
            assert_unpublished(&checker, &deferred);
            assert_eq!(snapshot(&checker, &[(SOURCE, &parsed)]), before);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the real alias headers, diagnostics and both entry orders together.
fn named_alias_bounds_keep_exact_constraints_defaults_and_diagnostics() {
    let source = format!(
        "{}{ENV}{}",
        concat!(
            "export type Bound<E extends Env = BlankEnv, U extends E = E,> = U;\n",
            "export type Free<T> = T;\n",
            "export type Broken<E extends Env = string> = E;\n",
        ),
        concat!(
            "export type Default = Bound;\n",
            "export type Explicit = Bound<Env>;\n",
            "export type Concrete = Bound<Env, BlankEnv>;\n",
        )
    );
    let parsed = parse_source_file(&source);
    let bound = alias(&parsed, SOURCE, "Bound");
    let free = alias(&parsed, SOURCE, "Free");
    let broken = alias(&parsed, SOURCE, "Broken");
    let env = alias(&parsed, SOURCE, "Env");
    let blank = alias(&parsed, SOURCE, "BlankEnv");
    let applied = ["Default", "Explicit", "Concrete"].map(|name| alias(&parsed, SOURCE, name));
    assert_eq!(bound.parameters.len(), 2);
    assert!(
        parsed.arena.get(bound.declaration.node).unwrap().range.end
            < parsed.arena.get(env.declaration.node).unwrap().range.start
    );
    for operands_first in [false, true] {
        let mut checker = local_context(&parsed);
        if operands_first {
            for parameter in bound.parameters.iter().rev().chain(&broken.parameters) {
                for node in [parameter.default, parameter.constraint]
                    .into_iter()
                    .flatten()
                {
                    checker.get_type_from_type_node(node).unwrap();
                }
            }
            assert_unpublished(&checker, &bound);
            assert_unpublished(&checker, &broken);
            assert!(checker.diagnostics().is_empty());
        }
        checker.check_source_file(SOURCE).unwrap();
        assert_checked(&checker, SOURCE, true);
        let env_type = query_alias(&mut checker, &env);
        let blank_type = query_alias(&mut checker, &blank);
        let result = query_alias(&mut checker, &bound);
        let first = assert_formal(
            &mut checker,
            &parsed,
            &bound,
            0,
            Some(env_type),
            Some(blank_type),
        );
        let second = assert_formal(&mut checker, &parsed, &bound, 1, Some(first), Some(first));
        assert_ne!(first, second);
        assert_eq!(result, second);
        let owner = symbol(&checker, bound.declaration);
        assert_eq!(
            checker
                .store()
                .type_alias_links(owner)
                .unwrap()
                .type_parameters
                .as_deref(),
            Some(&[first, second][..])
        );
        assert_eq!(
            query_alias(&mut checker, &free),
            assert_formal(&mut checker, &parsed, &free, 0, None, None)
        );
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        let broken_result = query_alias(&mut checker, &broken);
        assert_eq!(
            broken_result,
            assert_formal(
                &mut checker,
                &parsed,
                &broken,
                0,
                Some(env_type),
                Some(string)
            )
        );
        assert_ne!(broken_result, first);
        let expected = [blank_type, env_type, blank_type];
        for (alias, expected) in applied.iter().zip(expected) {
            assert_eq!(query_alias(&mut checker, alias), expected);
        }
        let default = broken.parameters[0].default.unwrap();
        assert_eq!(
            checker.diagnostics().len(),
            1,
            "{:?}",
            checker.diagnostics()
        );
        assert_diagnostic(&checker, 0, default, 2344, &["string", "Env"]);
        assert_eq!(text_at(&parsed, &source, default), "string");
        assert_eq!(
            checker.diagnostics().as_slice()[0]
                .diagnostic
                .render()
                .unwrap(),
            "Type 'string' does not satisfy the constraint 'Env'."
        );
        let before = snapshot(&checker, &[(SOURCE, &parsed)]);
        for _ in 0..2 {
            assert_eq!(query_alias(&mut checker, &bound), second);
            for (alias, expected) in applied.iter().zip(expected) {
                assert_eq!(query_alias(&mut checker, alias), expected);
            }
            checker.check_source_file(SOURCE).unwrap();
            checker.recheck_source_file(SOURCE).unwrap();
            assert_eq!(snapshot(&checker, &[(SOURCE, &parsed)]), before);
        }
    }
    assert_arity_and_argument_diagnostics();
    assert_deferred_body_stays_unpublished();
}

fn assert_status_graph(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) -> TypeId {
    let status = alias(parsed, STATUS, "StatusCode");
    let resolved = query_alias(checker, &status);
    assert_alias_identity(checker, &status, resolved);
    let TypeData::Union(data) = checker.store().type_payload(resolved).unwrap().data() else {
        panic!("StatusCode keeps the complete original numeric union")
    };
    let mut actual = data
        .union
        .types
        .iter()
        .map(|type_| {
            let TypeData::Literal(data) = checker.store().type_payload(*type_).unwrap().data()
            else {
                panic!("each status member is a regular numeric literal")
            };
            assert_eq!(data.regular_type, *type_);
            let LiteralValue::Number(number) = data.value else {
                panic!("the original status union has only numbers")
            };
            number.0.to_bits()
        })
        .collect::<Vec<_>>();
    let mut expected = [
        -1, 100, 101, 102, 103, 200, 201, 202, 203, 204, 205, 206, 207, 208, 226, 300, 301, 302,
        303, 304, 305, 306, 307, 308, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
        412, 413, 414, 415, 416, 417, 418, 421, 422, 423, 424, 425, 426, 428, 429, 431, 451, 500,
        501, 502, 503, 504, 505, 506, 507, 508, 510, 511,
    ]
    .map(|value| f64::from(value).to_bits());
    actual.sort_unstable();
    expected.sort_unstable();
    assert_eq!(actual, expected);
    resolved
}

#[allow(clippy::too_many_lines)] // Check both source indexes and their complete value and import graph.
fn assert_schema_graph(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    status: &ParseResult,
    es5: &ParseResult,
) -> TypeId {
    let schema = alias(parsed, SOURCE, "Schema");
    let endpoint = alias(parsed, SOURCE, "Endpoint");
    let format = alias(parsed, SOURCE, "ResponseFormat");
    let known = alias(parsed, SOURCE, "KnownResponseFormat");
    let schema_type = query_alias(checker, &schema);
    let endpoint_type = query_alias(checker, &endpoint);
    assert_alias_identity(checker, &schema, schema_type);
    assert_alias_identity(checker, &endpoint, endpoint_type);
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    let any = checker.store().intrinsic_bootstrap().unwrap().any_type;
    assert_eq!(query_alias(checker, &format), string);
    let known_type = query_alias(checker, &known);
    assert_alias_identity(checker, &known, known_type);
    let TypeData::Union(known_data) = checker.store().type_payload(known_type).unwrap().data()
    else {
        panic!("the three written format literals keep their named union")
    };
    let mut values = known_data
        .union
        .types
        .iter()
        .map(|type_| {
            let TypeData::Literal(data) = checker.store().type_payload(*type_).unwrap().data()
            else {
                panic!("the format constituent is a literal")
            };
            let LiteralValue::String(value) = &data.value else {
                panic!("the format literal is a string")
            };
            value.as_str()
        })
        .collect::<Vec<_>>();
    values.sort_unstable();
    assert_eq!(values, ["json", "redirect", "text"]);
    let outer = index(parsed, schema.body);
    let inner_type = checker.get_type_from_type_node(outer.value).unwrap();
    let inner = index(parsed, outer.value);
    let key_type = checker.get_type_from_type_node(inner.key).unwrap();
    assert_eq!(
        checker.store().type_payload(inner_type).unwrap().alias(),
        None
    );
    assert_index(
        checker,
        parsed,
        schema.body,
        schema_type,
        string,
        inner_type,
        "Path",
    );
    assert_index(
        checker,
        parsed,
        outer.value,
        inner_type,
        key_type,
        endpoint_type,
        "Method",
    );
    let TypeData::TemplateLiteral(template) =
        checker.store().type_payload(key_type).unwrap().data()
    else {
        panic!("the method key retains its original template")
    };
    assert_eq!(template.texts, ["$", ""]);
    let [mapping] = template.types.as_slice() else {
        panic!("the method key has one Lowercase mapping")
    };
    let record = checker.store().type_payload(*mapping).unwrap();
    let TypeData::StringMapping(mapping) = record.data() else {
        panic!("Lowercase<string> remains the real string mapping")
    };
    assert_eq!(mapping.target, string);
    assert_eq!(
        record.symbol(),
        Some(symbol(
            checker,
            alias(es5, ES5_FILE, "Lowercase").declaration
        ))
    );
    let status_type = assert_status_graph(checker, status);
    for (name, expected) in [
        ("input", any),
        ("output", any),
        ("outputFormat", string),
        ("status", status_type),
    ] {
        assert_property(
            checker,
            parsed,
            endpoint.body,
            endpoint_type,
            name,
            expected,
            false,
        );
    }
    let (imported, import_name) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ImportSpecifier(specifier) = &record.data else {
                return None;
            };
            Some((
                NodeRef::new(parsed.arena.id(), SOURCE, node),
                specifier.name,
            ))
        })
        .unwrap();
    assert_eq!(
        text_at(
            parsed,
            HONO,
            NodeRef::new(parsed.arena.id(), SOURCE, import_name)
        ),
        "StatusCode"
    );
    let target = symbol(checker, alias(status, STATUS, "StatusCode").declaration);
    let links = checker
        .store()
        .alias_symbol_links(symbol(checker, imported))
        .unwrap();
    assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    assert_eq!(links.immediate_target, Some(target));
    schema_type
}

fn assert_indexed_read(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    root: NodeRef,
    input: &Alias,
    input_type: TypeId,
    property: (&str, TypeId),
    strict: bool,
) -> TypeId {
    let (property_name, raw) = property;
    let NodeData::IndexedAccessTypeNode(indexed) = &parsed.arena.get(root.node).unwrap().data
    else {
        panic!("the bound contains the original indexed access node")
    };
    let object = NodeRef::new(root.arena, root.file, indexed.object_type);
    let key = NodeRef::new(root.arena, root.file, indexed.index_type);
    assert_parent(parsed, object, root);
    assert_parent(parsed, key, root);
    assert_eq!(text_at(parsed, HONO, object), "Input");
    assert_eq!(text_at(parsed, HONO, key), format!("'{property_name}'"));
    assert_eq!(checker.get_type_from_type_node(object), Ok(input_type));
    let key_type = checker.get_type_from_type_node(key).unwrap();
    let TypeData::Literal(key_data) = checker.store().type_payload(key_type).unwrap().data() else {
        panic!("the source key has a regular literal identity")
    };
    assert_eq!(
        key_data.value,
        LiteralValue::String(property_name.to_owned())
    );
    assert_eq!(key_data.regular_type, key_type);
    let result = checker.get_type_from_type_node(root).unwrap();
    assert_property(
        checker,
        parsed,
        input.body,
        input_type,
        property_name,
        raw,
        true,
    );
    if strict {
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let TypeData::Union(data) = checker.store().type_payload(result).unwrap().data() else {
            panic!("a strict optional source read includes undefined")
        };
        let mut expected = [raw, bootstrap.undefined_type];
        expected.sort_unstable();
        assert_eq!(data.union.types, expected);
        assert!(!data.union.types.contains(&bootstrap.missing_type));
    } else {
        assert_eq!(result, raw);
    }
    result
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the original closed graph and both query orders together.
fn hono_bound_types_keep_schema_and_optional_input_identities() {
    let parsed = parse_source_file(HONO);
    let status = parse_source_file(HTTP_STATUS);
    let es5 = parse_source_file(ES5);
    let decorators = parse_source_file(DECORATORS);
    let legacy = parse_source_file(LEGACY);
    let imports = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::ImportDeclaration(import) = &record.data else {
                return None;
            };
            Some(NodeRef::new(
                parsed.arena.id(),
                SOURCE,
                import.module_specifier,
            ))
        })
        .collect::<Vec<_>>();
    let [specifier] = imports.as_slice() else {
        panic!("the original StatusCode import has one exact manifest entry")
    };
    assert_eq!(text_at(&parsed, HONO, *specifier), "'./utils/http-status'");
    let files = [
        (ES5_FILE, &es5, "\"/lib/lib.es5.d.ts\"", true),
        (
            DECORATORS_FILE,
            &decorators,
            "\"/lib/lib.decorators.d.ts\"",
            true,
        ),
        (
            LEGACY_FILE,
            &legacy,
            "\"/lib/lib.decorators.legacy.d.ts\"",
            true,
        ),
        (SOURCE, &parsed, "\"/project/types.ts\"", false),
        (STATUS, &status, "\"/project/utils/http-status.ts\"", false),
    ];
    let schema_bound = alias(&parsed, SOURCE, "KeepSchema");
    let input_bound = alias(&parsed, SOURCE, "KeepInput");
    let output_bound = alias(&parsed, SOURCE, "KeepOutput");
    let input = alias(&parsed, SOURCE, "Input");
    let bound_nodes = [
        schema_bound.parameters[0].constraint.unwrap(),
        input_bound.parameters[0].constraint.unwrap(),
        output_bound.parameters[0].constraint.unwrap(),
    ];
    let NodeData::UnionTypeNode(input_union) = &parsed.arena.get(bound_nodes[1].node).unwrap().data
    else {
        panic!("the Input bound retains both written children")
    };
    let [input_reference, input_index] = input_union.types.nodes.as_slice() else {
        panic!("the source union has Input and Input['in']")
    };
    let input_reference = NodeRef::new(parsed.arena.id(), SOURCE, *input_reference);
    let input_index = NodeRef::new(parsed.arena.id(), SOURCE, *input_index);
    assert_parent(&parsed, input_reference, bound_nodes[1]);
    assert_parent(&parsed, input_index, bound_nodes[1]);
    for (strict, exact_optional) in [(true, false), (true, true), (false, false)] {
        for operands_first in [false, true] {
            let mut checker = context(&files, &[(*specifier, STATUS)], strict, exact_optional);
            if operands_first {
                for (alias, node) in [&schema_bound, &input_bound, &output_bound]
                    .into_iter()
                    .zip(bound_nodes)
                {
                    assert_parent(&parsed, node, alias.parameters[0].declaration);
                    checker.get_type_from_type_node(node).unwrap();
                    assert_unpublished(&checker, alias);
                }
            }
            let schema_parameter = query_alias(&mut checker, &schema_bound);
            let input_parameter = query_alias(&mut checker, &input_bound);
            let output_parameter = query_alias(&mut checker, &output_bound);
            assert_ne!(schema_parameter, input_parameter);
            assert_ne!(input_parameter, output_parameter);
            let schema_type = assert_schema_graph(&mut checker, &parsed, &status, &es5);
            let input_type = query_alias(&mut checker, &input);
            assert_alias_identity(&checker, &input, input_type);
            let raw_in = checker
                .get_type_from_type_node(property(&parsed, input.body, "in").annotation)
                .unwrap();
            let raw_out = checker
                .get_type_from_type_node(property(&parsed, input.body, "out").annotation)
                .unwrap();
            assert_eq!(raw_in, raw_out);
            assert_eq!(
                raw_in,
                checker
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .empty_type_literal_type
            );
            assert!(
                object(&checker, raw_in)
                    .structured
                    .properties
                    .as_deref()
                    .is_none_or(<[SemanticSymbolId]>::is_empty)
            );
            assert_eq!(checker.store().type_payload(raw_in).unwrap().alias(), None);
            let read_in = assert_indexed_read(
                &mut checker,
                &parsed,
                input_index,
                &input,
                input_type,
                ("in", raw_in),
                strict,
            );
            let read_out = assert_indexed_read(
                &mut checker,
                &parsed,
                bound_nodes[2],
                &input,
                input_type,
                ("out", raw_out),
                strict,
            );
            assert_eq!(read_in, read_out);
            assert_eq!(
                checker.get_type_from_type_node(input_reference),
                Ok(input_type)
            );
            let input_constraint = checker.get_type_from_type_node(bound_nodes[1]).unwrap();
            let TypeData::Union(union) = checker
                .store()
                .type_payload(input_constraint)
                .unwrap()
                .data()
            else {
                panic!("the surrounding Input bound keeps its canonical union")
            };
            let mut expected = vec![input_type, raw_in];
            if strict {
                expected.push(
                    checker
                        .store()
                        .intrinsic_bootstrap()
                        .unwrap()
                        .undefined_type,
                );
            }
            expected.sort_unstable();
            assert_eq!(union.union.types, expected);
            let blank_schema = query_alias(&mut checker, &alias(&parsed, SOURCE, "BlankSchema"));
            let blank_input = query_alias(&mut checker, &alias(&parsed, SOURCE, "BlankInput"));
            assert_eq!(
                assert_formal(
                    &mut checker,
                    &parsed,
                    &schema_bound,
                    0,
                    Some(schema_type),
                    Some(blank_schema)
                ),
                schema_parameter
            );
            assert_eq!(
                assert_formal(
                    &mut checker,
                    &parsed,
                    &input_bound,
                    0,
                    Some(input_constraint),
                    Some(blank_input)
                ),
                input_parameter
            );
            assert_eq!(
                assert_formal(
                    &mut checker,
                    &parsed,
                    &output_bound,
                    0,
                    Some(read_out),
                    Some(blank_input)
                ),
                output_parameter
            );
            let uses = [
                ("SelectedSchema", schema_type),
                ("DefaultSchema", blank_schema),
                ("SelectedInput", input_type),
                ("DefaultInput", blank_input),
                ("DefaultOutput", blank_input),
            ];
            for (name, expected) in uses {
                assert_eq!(
                    query_alias(&mut checker, &alias(&parsed, SOURCE, name)),
                    expected
                );
            }
            assert_checked(&checker, SOURCE, false);
            assert_checked(&checker, STATUS, false);
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            // A property import does not grant a direct imported-bound role.
            let direct = alias(&parsed, SOURCE, "DirectStatus");
            let direct_owner = symbol(&checker, direct.declaration);
            let imported =
                parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        matches!(&record.data, NodeData::ImportSpecifier(_))
                            .then_some(NodeRef::new(parsed.arena.id(), SOURCE, node))
                    })
                    .unwrap();
            let imported_owner = symbol(&checker, imported);
            assert_eq!(
                checker
                    .store()
                    .symbol(imported_owner)
                    .unwrap()
                    .declarations(),
                Some(&[imported][..])
            );
            let rejected = DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::ImportAliasTypeReference {
                    node: direct.parameters[0].constraint.unwrap(),
                    alias: imported_owner,
                },
            );
            let before = snapshot(&checker, &[(SOURCE, &parsed), (STATUS, &status)]);
            for _ in 0..2 {
                assert_eq!(
                    checker.get_declared_type_of_symbol(direct_owner),
                    Err(rejected)
                );
                assert_unpublished(&checker, &direct);
                assert_eq!(query_alias(&mut checker, &schema_bound), schema_parameter);
                assert_eq!(query_alias(&mut checker, &input_bound), input_parameter);
                assert_eq!(query_alias(&mut checker, &output_bound), output_parameter);
                assert_eq!(checker.get_type_from_type_node(input_index), Ok(read_in));
                assert_eq!(
                    checker.get_type_from_type_node(bound_nodes[1]),
                    Ok(input_constraint)
                );
                assert_eq!(
                    checker.get_type_from_type_node(bound_nodes[2]),
                    Ok(read_out)
                );
                for (name, expected) in uses {
                    assert_eq!(
                        query_alias(&mut checker, &alias(&parsed, SOURCE, name)),
                        expected
                    );
                }
                assert_eq!(
                    snapshot(&checker, &[(SOURCE, &parsed), (STATUS, &status)]),
                    before
                );
            }
        }
    }
}

#[test]
fn source_object_union_defaults_keep_their_proof_during_conditional_replay() {
    // The pinned Go checker accepts this source and reports TS2322 for its
    // string annotation. Both requests below omit all type arguments.
    const POSITIVE: &str = concat!(
        "export type Left = { value: number; left: boolean };\n",
        "export type Right = { value: number; right: boolean };\n",
        "export type Defaulted<T = Left | Right> = T;\n",
        "export type Choose<C> = C extends true ? Defaulted : never;\n",
        "export declare const seed: Defaulted;\n",
        "export declare const value: Choose<true>;\n",
        "export const check: number = value.value;\n",
    );
    for negative in [false, true] {
        let source = if negative {
            POSITIVE.replace("check: number", "check: string")
        } else {
            POSITIVE.to_owned()
        };
        let parsed = parse_source_file(&source);
        let mut checker = local_context(&parsed);
        let node_ref = |node| NodeRef::new(parsed.arena.id(), SOURCE, node);
        let variable = |expected: &str| {
            parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(data) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(data.name)?.data else {
                        return None;
                    };
                    (name.text == expected).then(|| {
                        (
                            node_ref(data.name),
                            node_ref(data.type_.unwrap()),
                            data.initializer.map(node_ref),
                        )
                    })
                })
                .unwrap_or_else(|| panic!("missing variable {expected}"))
        };
        let (_, seed_node, _) = variable("seed");
        let (_, value_node, _) = variable("value");
        let (check_name, _, read) = variable("check");
        let read = read.unwrap();
        assert_eq!(text_at(&parsed, &source, read), "value.value");
        assert_eq!(text_at(&parsed, &source, check_name), "check");
        assert_eq!(
            parsed.arena.get(check_name.node).unwrap().range.start.get(),
            306
        );
        let NodeData::TypeReferenceNode(seed) = &parsed.arena.get(seed_node.node).unwrap().data
        else {
            panic!("seed must have a written alias reference");
        };
        assert!(seed.type_arguments.is_none());
        let defaulted = alias(&parsed, SOURCE, "Defaulted");
        let default_node = defaulted.parameters[0].default.unwrap();
        let NodeData::UnionTypeNode(union) = &parsed.arena.get(default_node.node).unwrap().data
        else {
            panic!("the default must retain its written union");
        };
        let [left, right] = union.types.nodes.as_slice() else {
            panic!("the default must reference two source objects");
        };
        let references = [node_ref(*left), node_ref(*right)];
        let objects = [alias(&parsed, SOURCE, "Left"), alias(&parsed, SOURCE, "Right")];
        let children = [objects[0].body, objects[1].body];
        for ((reference, object), name) in references.into_iter().zip(&objects).zip(["Left", "Right"]) {
            assert_parent(&parsed, reference, default_node);
            assert_eq!(text_at(&parsed, &source, reference), name);
            let NodeData::TypeReferenceNode(data) = &parsed.arena.get(reference.node).unwrap().data
            else {
                panic!("the default must contain named references");
            };
            assert!(data.type_arguments.is_none());
            assert_parent(&parsed, object.body, object.declaration);
            assert!(matches!(
                parsed.arena.get(object.body.node).unwrap().data,
                NodeData::TypeLiteralNode(_)
            ));
        }

        assert_eq!(checker.store().source_alias_default_graph_count(), 0);
        let seed_type = checker.get_type_from_type_node(seed_node).unwrap();
        assert_eq!(checker.store().source_alias_default_graph_count(), 1);
        assert_checked(&checker, SOURCE, false);
        let raw_default = checker.get_type_from_type_node(default_node).unwrap();
        let formal = assert_formal(&mut checker, &parsed, &defaulted, 0, None, Some(raw_default));
        assert_eq!(query_alias(&mut checker, &defaulted), formal);
        let TypeData::TypeParameter(parameter) =
            checker.store().type_payload(formal).unwrap().data()
        else {
            panic!("the alias keeps its declared formal");
        };
        assert_eq!(parameter.resolved_default_type, Some(raw_default));
        let TypeData::Union(data) = checker.store().type_payload(raw_default).unwrap().data()
        else {
            panic!("the raw default must remain a union");
        };
        let mut raw_members = data.union.types.clone();
        let object_types = children.map(|node| checker.get_type_from_type_node(node).unwrap());
        for ((reference, object), type_) in references.into_iter().zip(&objects).zip(object_types) {
            assert_eq!(checker.get_type_from_type_node(reference), Ok(type_));
            assert_eq!(query_alias(&mut checker, object), type_);
            assert_alias_identity(&checker, object, type_);
        }
        let mut expected_members = object_types.to_vec();
        raw_members.sort_unstable();
        expected_members.sort_unstable();
        assert_eq!(raw_members, expected_members);
        assert_ne!(object_types[0], object_types[1]);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let boolean = bootstrap.boolean_type;
        for ((node, type_), extra) in children.into_iter().zip(object_types).zip(["left", "right"]) {
            assert_eq!(
                checker.store().type_payload(type_).unwrap().symbol(),
                Some(symbol(&checker, node))
            );
            assert_property(&mut checker, &parsed, node, type_, "value", number, false);
            assert_property(&mut checker, &parsed, node, type_, extra, boolean, false);
        }

        // Alias request keys use the written arguments, not the filled defaults.
        let mut hasher = xxhash_rust::xxh3::Xxh3::new();
        hasher.update(&0_u64.to_le_bytes());
        hasher.update(&[0]);
        let request_key = ts_checker::semantic::CacheHashKey::new(hasher.digest128());
        let owner = symbol(&checker, defaulted.declaration);
        let request = |checker: &CanonicalCheckerContext<'_>| {
            checker
                .store()
                .type_alias_links(owner)
                .unwrap()
                .instantiations
                .as_ref()
                .unwrap()
                .get(&request_key)
                .copied()
        };
        assert_eq!(request(&checker), Some(seed_type));
        assert_eq!(
            checker.store().type_node_links(value_node).and_then(|links| links.resolved_type),
            None
        );
        let value_type = checker.get_type_from_type_node(value_node).unwrap();
        for request_type in [seed_type, value_type] {
            let TypeData::Union(data) = checker.store().type_payload(request_type).unwrap().data()
            else {
                panic!("both alias requests must retain the complete object union");
            };
            let mut members = data.union.types.clone();
            members.sort_unstable();
            assert_eq!(members, expected_members);
        }
        checker.check_source_file(SOURCE).unwrap();
        assert_checked(&checker, SOURCE, true);
        assert_eq!(checker.get_type_at_location(read), Ok(number));
        assert_eq!(checker.diagnostics().as_slice().len(), usize::from(negative));
        if negative {
            assert_diagnostic(&checker, 0, check_name, 2322, &["number", "string"]);
        }
        let warm = snapshot(&checker, &[(SOURCE, &parsed)]);
        let graph_count = checker.store().source_alias_default_graph_count();
        assert_eq!(graph_count, 1);
        for _ in 0..2 {
            assert_eq!(checker.get_type_from_type_node(seed_node), Ok(seed_type));
            assert_eq!(checker.get_type_from_type_node(value_node), Ok(value_type));
            assert_eq!(checker.get_type_at_location(read), Ok(number));
            checker.recheck_source_file(SOURCE).unwrap();
            assert_eq!(request(&checker), Some(seed_type));
            assert_eq!(
                checker.store().source_alias_default_graph_count(),
                graph_count
            );
            assert!(snapshot(&checker, &[(SOURCE, &parsed)]) == warm);
        }
    }
}

#[test]
fn mapped_alias_cache_replays_preserve_properties_and_diagnostics() {
    const ORDINARY: &str = concat!(
        "export type Shape = { value: number; label: string };\n",
        "export type Copy<T> = { [K in keyof T]: T[K] };\n",
        "export declare const seed: Copy<Shape>;\n",
        "export declare const value: Copy<Shape>;\n",
        "export const first: number = seed.value;\n",
        "export const again: number = value.value;\n",
        "export const label: string = value.label;\n",
        "export const check: number = value.value;\n",
    );
    const CONDITIONAL: &str = concat!(
        "export type Shape = { value: number; label: string };\n",
        "export type Copy<T> = { [K in keyof T]: T[K] };\n",
        "export type Choose<C> = C extends true ? Copy<Shape> : never;\n",
        "export declare const seed: Copy<Shape>;\n",
        "export declare const value: Choose<true>;\n",
        "export const first: number = seed.value;\n",
        "export const again: number = value.value;\n",
        "export const label: string = value.label;\n",
        "export const check: number = value.value;\n",
    );
    const DEFAULT: &str = concat!(
        "export type Shape = { value: number; label: string };\n",
        "export type Copy<T = Shape> = { [K in keyof T]: T[K] };\n",
        "export type Choose<C> = C extends true ? Copy : never;\n",
        "export declare const seed: Copy;\n",
        "export declare const value: Choose<true>;\n",
        "export const first: number = seed.value;\n",
        "export const again: number = value.value;\n",
        "export const label: string = value.label;\n",
        "export const check: number = value.value;\n",
    );
    // Pinned Go gives no positive diagnostics and exactly TS2322 on each check.
    for (case, positive, check_start, defaulted) in [
        ("ordinary", ORDINARY, 321, false),
        ("conditional", CONDITIONAL, 384, false),
        ("defaulted", DEFAULT, 378, true),
    ] {
        for negative in [false, true] {
            for source_first in [false, true] {
                let source = if negative {
                    positive.replace("check: number", "check: string")
                } else {
                    positive.to_owned()
                };
                let parsed = parse_source_file(&source);
                let mut checker = local_context(&parsed);
                let node_ref = |node| NodeRef::new(parsed.arena.id(), SOURCE, node);
                let variable = |expected: &str| {
                    parsed
                        .arena
                        .iter()
                        .find_map(|(_, record)| {
                            let NodeData::VariableDeclaration(data) = &record.data else {
                                return None;
                            };
                            let NodeData::Identifier(name) = &parsed.arena.get(data.name)?.data
                            else {
                                return None;
                            };
                            (name.text == expected).then(|| {
                                (
                                    node_ref(data.name),
                                    node_ref(data.type_.unwrap()),
                                    data.initializer.map(node_ref),
                                )
                            })
                        })
                        .unwrap_or_else(|| panic!("missing variable {expected}"))
                };
                let (_, seed_node, _) = variable("seed");
                let (_, value_node, _) = variable("value");
                let (check_name, _, _) = variable("check");
                let reads =
                    ["first", "again", "label", "check"].map(|name| variable(name).2.unwrap());
                for (read, text) in reads.into_iter().zip([
                    "seed.value",
                    "value.value",
                    "value.label",
                    "value.value",
                ]) {
                    assert_eq!(text_at(&parsed, &source, read), text);
                }
                assert_eq!(
                    parsed.arena.get(check_name.node).unwrap().range.start.get(),
                    check_start
                );
                let copy = alias(&parsed, SOURCE, "Copy");
                assert!(matches!(
                    parsed.arena.get(copy.body.node).unwrap().data,
                    NodeData::MappedTypeNode(_)
                ));
                assert_parent(&parsed, copy.body, copy.declaration);
                if defaulted {
                    let choose = alias(&parsed, SOURCE, "Choose");
                    let NodeData::ConditionalTypeNode(data) =
                        &parsed.arena.get(choose.body.node).unwrap().data
                    else {
                        panic!("Choose must retain its conditional");
                    };
                    for reference in [seed_node, node_ref(data.true_type)] {
                        let NodeData::TypeReferenceNode(data) =
                            &parsed.arena.get(reference.node).unwrap().data
                        else {
                            panic!("Copy must remain a written reference");
                        };
                        assert!(data.type_arguments.is_none());
                    }
                }
                if source_first {
                    checker.check_source_file(SOURCE).unwrap();
                }
                let seed_type = checker.get_type_from_type_node(seed_node).unwrap();
                assert_checked(&checker, SOURCE, source_first);
                let owner = symbol(&checker, copy.declaration);
                let copy_links = checker.store().type_alias_links(owner).unwrap().clone();
                let declared = copy_links.declared_type.unwrap();
                let TypeData::Mapped(original) =
                    checker.store().type_payload(declared).unwrap().data()
                else {
                    panic!("Copy must retain its mapped declaration");
                };
                assert_eq!(original.declaration, Some(copy.body));
                let TypeData::Mapped(instance) =
                    checker.store().type_payload(seed_type).unwrap().data()
                else {
                    panic!("Copy<Shape> must be a mapped instance");
                };
                assert_eq!(instance.declaration, Some(copy.body));
                assert_eq!(instance.object.target, Some(declared));
                assert!(instance.object.mapper.is_some());
                assert_ne!(seed_type, declared);
                if defaulted {
                    let default = copy.parameters[0].default.unwrap();
                    let default_type = checker.get_type_from_type_node(default).unwrap();
                    let formal = copy_links.type_parameters.as_ref().unwrap()[0];
                    let TypeData::TypeParameter(data) =
                        checker.store().type_payload(formal).unwrap().data()
                    else {
                        panic!("Copy must retain its declared formal");
                    };
                    assert_eq!(data.resolved_default_type, Some(default_type));
                    let mut hasher = xxhash_rust::xxh3::Xxh3::new();
                    hasher.update(&0_u64.to_le_bytes());
                    hasher.update(&[0]);
                    let key = ts_checker::semantic::CacheHashKey::new(hasher.digest128());
                    assert_eq!(
                        copy_links.instantiations.as_ref().unwrap().get(&key),
                        Some(&seed_type)
                    );
                }
                assert_eq!(
                    checker.get_type_from_type_node(seed_node),
                    Ok(seed_type),
                    "case={case}, negative={negative}, source_first={source_first}"
                );
                if !source_first {
                    assert_eq!(
                        checker
                            .store()
                            .type_node_links(value_node)
                            .and_then(|links| links.resolved_type),
                        None
                    );
                }
                let value_type = checker.get_type_from_type_node(value_node).unwrap();
                assert_eq!(value_type, seed_type);
                assert!(checker.store().type_alias_links(owner) == Some(&copy_links));
                checker.check_source_file(SOURCE).unwrap();
                assert_checked(&checker, SOURCE, true);
                let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
                let expected = [
                    bootstrap.number_type,
                    bootstrap.number_type,
                    bootstrap.string_type,
                    bootstrap.number_type,
                ];
                for (read, type_) in reads.into_iter().zip(expected) {
                    assert_eq!(checker.get_type_at_location(read), Ok(type_));
                }
                assert_eq!(
                    checker.diagnostics().as_slice().len(),
                    usize::from(negative)
                );
                if negative {
                    assert_diagnostic(&checker, 0, check_name, 2322, &["number", "string"]);
                }
                let warm = snapshot(&checker, &[(SOURCE, &parsed)]);
                for _ in 0..2 {
                    assert_eq!(checker.get_type_from_type_node(seed_node), Ok(seed_type));
                    assert_eq!(checker.get_type_from_type_node(value_node), Ok(value_type));
                    for (read, type_) in reads.into_iter().zip(expected) {
                        assert_eq!(checker.get_type_at_location(read), Ok(type_));
                    }
                    checker.recheck_source_file(SOURCE).unwrap();
                    assert!(snapshot(&checker, &[(SOURCE, &parsed)]) == warm);
                }
            }
        }
    }
}
